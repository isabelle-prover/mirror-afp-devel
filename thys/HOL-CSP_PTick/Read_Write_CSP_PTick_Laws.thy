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
theory Read_Write_CSP_PTick_Laws
  imports Step_CSP_PTick_Laws_Extended
begin
  (*>*)

section \<open>Read and Write Laws\<close>

subsection \<open>Sequential Composition\<close>

lemma read_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<^bold>;\<^sub>\<checkmark> Q = c\<^bold>?a\<in>A \<rightarrow> (P a \<^bold>;\<^sub>\<checkmark> Q)\<close>
  by (simp add: read_def Mprefix_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k comp_def)

lemma write0_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>a \<rightarrow> P \<^bold>;\<^sub>\<checkmark> Q = a \<rightarrow> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  by (simp add: write0_def Mprefix_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemma ndet_write_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<^bold>;\<^sub>\<checkmark> Q = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<^bold>;\<^sub>\<checkmark> Q)\<close>
  by (simp add: ndet_write_is_GlobalNdet_write0 Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right write0_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemma write_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>c\<^bold>!a \<rightarrow> P \<^bold>;\<^sub>\<checkmark> Q = c\<^bold>!a \<rightarrow> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  by (simp add: write0_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k write_is_write0)



subsection \<open>Synchronization Product\<close>

subsubsection \<open>General Laws\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin

paragraph \<open> \<^const>\<open>read\<close> \<close>

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read : 
  \<comment> \<open>This is the general case.\<close>
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
   (\<box>x\<in>(c ` A \<inter> d ` B \<inter> S) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d x)))\<close>
  (is \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close>)
  if \<open>c ` A \<inter> S = {} \<or> c ` A \<subseteq> S \<or> inj_on c A\<close>
    \<open>d ` B \<inter> S = {} \<or> d ` B \<subseteq> S \<or> inj_on d B\<close>
    \<comment> \<open>Assumptions may seem strange, but the motivation is that when \<^term>\<open>A - c -` S \<noteq> {}\<close>
     (which is equivalent to \<^term>\<open>\<not> c ` A \<subseteq> S\<close>), we need to ensure that 
     \<^term>\<open>inv_into (A - c -` S) c\<close> is equal to \<^term>\<open>inv_into A c\<close>.
     This requires \<^term>\<open>A - c -` S = A\<close> (which is equivalent to \<^term>\<open>c ` A \<inter> S = {}\<close>)
     or \<^term>\<open>inj_on c A\<close>. We need obviously a similar assumption for \<^term>\<open>B\<close>.\<close>
proof -
  have * : \<open>\<And>e X. e ` (X - e -` S) = e ` X - S\<close> by auto
  have \<open>?lhs = (\<box>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<box>x\<in>d ` B \<rightarrow> Q (inv_into B d x)))) \<box>
               (\<box>b\<in>(d ` B - S) \<rightarrow> ((\<box>x\<in>c ` A \<rightarrow> P (inv_into A c x)) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<box>
               (\<box>x\<in>(c ` A \<inter> d ` B \<inter> S) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d x)))\<close>
    (is \<open>?lhs = ?rhs1' \<box> ?rhs2' \<box> ?rhs3\<close>)
    by (simp add: read_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix comp_def)
  also from that(1) have \<open>?rhs1' = ?rhs1\<close>
  proof (elim disjE)
    assume \<open>c ` A \<inter> S = {}\<close>
    hence \<open>A - c -` S = A \<and> c ` A - S = c ` A\<close> by fast
    thus \<open>?rhs1' = ?rhs1\<close> by (simp add: read_def comp_def)
  next
    assume \<open>c ` A \<subseteq> S\<close>
    hence \<open>A - c -` S = {} \<and> c ` A - S = {}\<close> by fast
    show \<open>?rhs1' = ?rhs1\<close> by (simp add: \<open>?this\<close>)
  next
    assume \<open>inj_on c A\<close>
    hence \<open>inj_on c (A - c -` S)\<close> by (simp add: inj_on_diff)
    with \<open>inj_on c A\<close> show \<open>?rhs1' = ?rhs1\<close>
      by (auto simp add: read_def comp_def "*" intro: mono_Mprefix_eq)
  qed
  also from that(2) have \<open>?rhs2' = ?rhs2\<close>
  proof (elim disjE)
    assume \<open>d ` B \<inter> S = {}\<close>
    hence \<open>B - d -` S = B \<and> d ` B - S = d ` B\<close> by fast
    thus \<open>?rhs2' = ?rhs2\<close> by (simp add: read_def comp_def)
  next
    assume \<open>d ` B \<subseteq> S\<close>
    hence \<open>B - d -` S = {} \<and> d ` B - S = {}\<close> by fast
    show \<open>?rhs2' = ?rhs2\<close> by (simp add: \<open>?this\<close>)
  next
    assume \<open>inj_on d B\<close>
    hence \<open>inj_on d (B - d -` S)\<close> by (simp add: inj_on_diff)
    with \<open>inj_on d B\<close> show \<open>?rhs2' = ?rhs2\<close>
      by (auto simp add: read_def comp_def "*" intro: mono_Mprefix_eq)
  qed
  finally show \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close> .
qed


paragraph \<open>Enforce read\<close>

\<comment> \<open>With stronger assumptions, we can fully rewrite the right hand side with \<^const>\<open>read\<close>.\<close>
\<comment> \<open>Remember that now, channels \<^term>\<open>c\<close> and \<^term>\<open>d\<close> must have the same type.
   This was not the case on the previous lemma.\<close>
lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_left : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
   (c\<^bold>?x\<in>(A \<inter> c -` (d ` B \<inter> S)) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x))\<close>
  (is \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close>)
  if \<open>c ` A \<inter> S = {} \<or> inj_on c A\<close>
    \<open>d ` B \<inter> S = {} \<or> inj_on d B\<close>
    \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> d b \<in> S \<Longrightarrow> a = b\<close>
proof -
  let ?rhs3' = \<open>(\<box>x\<in>(c ` A \<inter> d ` B \<inter> S) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d x)))\<close>
  have  * : \<open>c ` (A \<inter> c -` (d ` B \<inter> S)) = c ` A \<inter> d ` B \<inter> S\<close> by blast
  have ** : \<open>c ` (A \<inter> c -` d ` B) = c ` A \<inter> d ` B\<close> by blast
  from that(1, 2) consider \<open>c ` A \<inter> S = {} \<or> d ` B \<inter> S = {}\<close>
    | \<open>inj_on c A\<close> \<open>inj_on d B\<close> by blast
  hence \<open>?rhs3' = ?rhs3\<close>
  proof cases
    assume \<open>c ` A \<inter> S = {} \<or> d ` B \<inter> S = {}\<close>
    hence \<open>c ` A \<inter> d ` B \<inter> S = {} \<and> A \<inter> c -` (d ` B \<inter> S) = {}\<close> by blast
    thus \<open>?rhs3' = ?rhs3\<close> by simp
  next
    assume \<open>inj_on c A\<close> \<open>inj_on d B\<close>
    show \<open>?rhs3' = ?rhs3\<close>
    proof (unfold read_def "*" comp_def,
        intro mono_Mprefix_eq arg_cong2[where f = \<open>\<lambda>P Q. P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close>])
      fix x assume \<open>x \<in> c ` A \<inter> d ` B \<inter> S\<close>
      moreover from \<open>inj_on c A\<close> inj_on_Int
      have \<open>inj_on c A \<and> inj_on c (A \<inter> c -` (d ` B \<inter> S))\<close> by blast
      ultimately show \<open>P (inv_into A c x) = P (inv_into (A \<inter> c -` (d ` B \<inter> S)) c x)\<close>
        by (simp add: image_iff, elim conjE bexE, simp)
    next
      fix x assume $ : \<open>x \<in> c ` A \<inter> d ` B \<inter> S\<close>
      then obtain a b where $$ : \<open>x = c a\<close> \<open>a \<in> A\<close> \<open>x = d b\<close> \<open>b \<in> B\<close> by blast
      from \<open>inj_on c A\<close> inj_on_Int have $$$ : \<open>inj_on c (A \<inter> c -` (d ` B \<inter> S))\<close> by blast
      have \<open>inv_into B d x = b\<close> by (simp add: "$$"(3, 4) \<open>inj_on d B\<close>)
      also have \<open>b = a\<close> by (metis "$" "$$" Int_iff that(3))
      also have \<open>a = inv_into (A \<inter> c -` (d ` B \<inter> S)) c x\<close>
        by (metis "$" "$$"(1, 2) "$$$" "*" Int_lower1
            \<open>inj_on c A\<close> inj_on_image_mem_iff inv_into_f_eq)
      finally have \<open>inv_into B d x = inv_into (A \<inter> c -` (d ` B \<inter> S)) c x\<close> .
      thus \<open>Q (inv_into B d x) = Q (inv_into (A \<inter> c -` (d ` B \<inter> S)) c x)\<close> by simp
    qed
  qed
  moreover have \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3'\<close>
    using that(1, 2) by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read) auto
  ultimately show \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close> by argo
qed


corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_right:
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
   (d\<^bold>?x\<in>(B \<inter> d -` (c ` A \<inter> S)) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x))\<close>
  (is \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close>)
  if \<open>c ` A \<inter> S = {} \<or> inj_on c A\<close>
    \<open>d ` B \<inter> S = {} \<or> inj_on d B\<close>
    \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> d b \<in> S \<Longrightarrow> a = b\<close>
  unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym
  by (subst Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_left[OF that(2, 1)], metis that(3))
    (auto simp add: Det_commute intro: arg_cong2[where f = \<open>(\<box>)\<close>])



paragraph \<open>Special Cases\<close>

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   \<box>x\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d x))\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  from that have * : \<open>A - c -` S = {}\<close> \<open>B - d -` S = {}\<close> by auto
  from that(1) have ** : \<open>c ` A \<inter> d ` B \<inter> S = c ` A \<inter> d ` B\<close> by blast
  show ?thesis by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read)
      (use that in \<open>simp_all add: "*" "**"\<close>)
qed

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_forced_read_left : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>?x\<in>(A \<inter> c -` d ` B) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<subseteq> S\<close> \<open>inj_on c A\<close> \<open>inj_on d B\<close>
    \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> d b \<in> S \<Longrightarrow> a = b\<close>
proof -
  from that have * : \<open>A - c -` S = {}\<close> \<open>B - d -` S = {}\<close> by auto
  from that(1) have ** : \<open>A \<inter> (c -` d ` B \<inter> c -` S) = A \<inter> c -` d ` B\<close> by blast
  show ?thesis by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_left)
      (use that(3, 4, 5) in \<open>simp_all add: "*" "**"\<close>)
qed

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_forced_read_right : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?x\<in>(B \<inter> d -` c ` A) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<subseteq> S\<close> \<open>inj_on c A\<close> \<open>inj_on d B\<close>
    \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> d b \<in> S \<Longrightarrow> a = b\<close>
proof -
  from that have * : \<open>B - d -` S = {}\<close> \<open>A - c -` S = {}\<close> by auto
  from that(1) have ** : \<open>B \<inter> (d -` c ` A \<inter> d -` S) = B \<inter> d -` c ` A\<close> by blast
  show ?thesis by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_right)
      (use that(3, 4, 5) in \<open>simp_all add: "*" "**"\<close>)
qed


lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_indep : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (d\<^bold>?b\<in>B \<rightarrow> Q b))) \<box> (d\<^bold>?b\<in>B \<rightarrow> ((c\<^bold>?a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))\<close>
  if \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<inter> S = {}\<close>
proof -
  from that have * : \<open>A - c -` S = A\<close> \<open>B - d -` S = B\<close> by auto
  from that(1) have ** : \<open>c ` A \<inter> d ` B \<inter> S = {}\<close> by blast
  show ?thesis by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read) (use that in \<open>simp_all add: "*" "**"\<close>)
qed

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_left : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (d\<^bold>?b\<in>B \<rightarrow> Q b))\<close>
  if \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  from that(1) have * : \<open>A - c -` S = A\<close> \<open>c ` A \<inter> d ` B \<inter> S = {}\<close> by auto
  from that(2) have ** : \<open>B - d -` S = {}\<close> by blast
  show ?thesis by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read)
      (use that in \<open>simp_all add: "*" "**"\<close>)
qed

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_right :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>B \<rightarrow> ((c\<^bold>?a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<inter> S = {}\<close>
proof -
  from that(2) have * : \<open>B - d -` S = B\<close> \<open>c ` A \<inter> d ` B \<inter> S = {}\<close> by auto
  from that(1) have ** : \<open>A - c -` S = {}\<close> by blast
  show ?thesis by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read)
      (use that in \<open>simp_all add: "*" "**"\<close>)
qed


corollary read_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a ||\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   \<box>x\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c x) ||\<^sub>\<checkmark> Q (inv_into B d x))\<close>
  by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset)

corollary read_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_left :
  \<open>\<lbrakk>inj_on c A; inj_on d B; \<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> a = b\<rbrakk> \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a ||\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>?x\<in>(A \<inter> c -` d ` B) \<rightarrow> (P x ||\<^sub>\<checkmark> Q x)\<close>
  by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_left) simp_all

corollary read_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_right :
  \<open>\<lbrakk>inj_on c A; inj_on d B; \<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> a = b\<rbrakk> \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a ||\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?x\<in>(B \<inter> d -` c ` A) \<rightarrow> (P x ||\<^sub>\<checkmark> Q x)\<close>
  by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_right) simp_all


corollary read_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read :
  \<open>\<lbrakk>inj_on c A; inj_on d B; \<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> a = b\<rbrakk> \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a |||\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>A \<rightarrow> (P a |||\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box> (d\<^bold>?b\<in>B \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a |||\<^sub>\<checkmark> Q b))\<close>
  by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read)



paragraph \<open>Same channel\<close>

text \<open>Some results can be rewritten when we have the same channel.\<close>


lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_same_chan : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> c\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> c\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (c\<^bold>?b\<in>(B - c -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
   (c\<^bold>?x\<in>(A \<inter> B \<inter> c -` S) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x))\<close>
  (is \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close>)
  if \<open>c ` A \<inter> S = {} \<or> inj_on c A\<close> \<open>c ` B \<inter> S = {} \<or> inj_on c B\<close>
    \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = c b \<Longrightarrow> c b \<in> S \<Longrightarrow> a = b\<close>
proof -
  \<comment> \<open>Actually, the third assumption is equivalent to the following
     (we of course do not use that(3) in the proof of equivalence).\<close>
  from that(1, 2)
  have \<open>inj_on c ((A \<union> B) \<inter> c -` S) \<longleftrightarrow>
        (\<forall>a b. a \<in> A \<longrightarrow> b \<in> B \<longrightarrow> c a = c b \<longrightarrow> c b \<in> S \<longrightarrow> a = b)\<close>
    by (elim disjE, simp_all add: inj_on_def)
      ((auto)[3], metis Int_iff Un_iff vimageE vimageI)

  from that(3) have * : \<open>A \<inter> (c -` c ` B \<inter> c -` S) = A \<inter> B \<inter> c -` S\<close> by auto blast
  show ?thesis by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_left that "*")
qed

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_same_chan_weaker :
  \<comment> \<open>Easier with a stronger assumption.\<close>
  \<open>inj_on c (A \<union> B) \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> c\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> c\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (c\<^bold>?b\<in>(B - c -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
   (c\<^bold>?x\<in>(A \<inter> B \<inter> c -` S) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x))\<close>
  by (rule read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_forced_read_same_chan)
    (simp_all add: inj_on_Un, metis Un_iff inj_onD inj_on_Un)


lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_forced_read_same_chan :
  \<comment> \<open>In the subset case, the assumption \<^term>\<open>inj_on c (A \<union> B)\<close> is equivalent.
      The result is not weaker anymore.\<close>
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> c\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>?x\<in>(A \<inter> B) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>c ` B \<subseteq> S\<close> \<open>inj_on c (A \<union> B)\<close>
proof -
  from that(3) have \<open>A \<inter> c -` c ` B = A \<inter> B\<close> by (auto simp add: inj_on_def)
  with that(3) show ?thesis
    by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_forced_read_left)
      (simp_all add: that(1, 2) inj_on_Un, meson Un_iff inj_on_contraD that(3))
qed



paragraph \<open>\<^const>\<open>read\<close> and \<^const>\<open>ndet_write\<close>.\<close>

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b
    else \<sqinter>a\<in>c ` A. (if a \<in> S then STOP else a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
                   (\<box>b\<in>(d ` B - S) \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<box>
                   (if a \<in> d ` B \<inter> S then a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d a)) else STOP))\<close>
  by (auto simp add: ndet_write_def read_def Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP
    else \<sqinter>b\<in>d ` B. (if b \<in> S then STOP else b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<box>
                   (\<box>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (if b \<in> c ` A \<inter> S then b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b)) else STOP))\<close>
  by (auto simp add: ndet_write_def read_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])


lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (  if c ` A \<subseteq> d ` B then \<sqinter>a\<in>c ` A \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d a))
    else (\<sqinter>a\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d a))) \<sqinter> STOP)\<close>
  by (simp add: read_def ndet_write_def Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_subset)

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if d ` B \<subseteq> c ` A then \<sqinter>b\<in>d ` B \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))
    else (\<sqinter>b\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<sqinter> STOP)\<close>
  by (simp add: read_def ndet_write_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_subset)


\<comment> \<open>If we have the same injective channel, it's better.\<close>
lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_same_chan:
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> c\<^bold>?b\<in>B \<rightarrow> Q b =
   (if A \<subseteq> B then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a) else (c\<^bold>!\<^bold>!a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)) \<sqinter> STOP)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>c ` B \<subseteq> S\<close> \<open>inj_on c (A \<union> B)\<close>
proof -
  from \<open>inj_on c (A \<union> B)\<close> have  * : \<open>c ` A \<subseteq> c ` B \<longleftrightarrow> A \<subseteq> B\<close>
    by (auto simp add: inj_on_eq_iff)
  from \<open>inj_on c (A \<union> B)\<close> have ** : \<open>c ` A \<inter> c ` B = c ` (A \<inter> B)\<close>
    by (auto simp add: inj_on_Un)
  from \<open>inj_on c (A \<union> B)\<close> show ?thesis
    by (unfold ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset[OF \<open>c ` A \<subseteq> S\<close> \<open>c ` B \<subseteq> S\<close>] "*" "**")
      (auto simp add: ndet_write_def inj_on_Un inj_on_Int
        intro!: mono_Mndetprefix_eq arg_cong2[where f = \<open>(\<sqinter>)\<close>])
qed

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset_same_chan:
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> c\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (if B \<subseteq> A then c\<^bold>!\<^bold>!b\<in>B \<rightarrow> (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b) else (c\<^bold>!\<^bold>!b\<in>(A \<inter> B) \<rightarrow> (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<sqinter> STOP)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>c ` B \<subseteq> S\<close> \<open>inj_on c (A \<union> B)\<close>
  by (subst (1 2 3) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_same_chan
      [OF that(2, 1)] Un_commute Int_commute that(3))


lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (  if A = {} then d\<^bold>?b\<in>B \<rightarrow>  (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
    else \<sqinter>a\<in>c ` A. (a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
                   (d\<^bold>?b\<in>B \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)))\<close>
  by (auto simp add: ndet_write_def read_def Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_indep comp_def
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
    else \<sqinter>b\<in>d ` B. (b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<box>
                   (c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q (inv_into B d b))))\<close>
  by (auto simp add: ndet_write_def read_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_indep comp_def
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])


lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_left :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  from that have \<open>?lhs = (if A = {} then STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b else ?rhs)\<close>
    by (auto simp add: ndet_write_def read_def
        Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_left comp_def
        intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])
  also have \<open>\<dots> = ?rhs\<close>
    by (simp add: read_def ndet_write_def Mprefix_is_STOP_iff
        STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix that(2))
  finally show \<open>?lhs = ?rhs\<close> .
qed

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_left :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  from that have \<open>?lhs = (if B = {} then (c\<^bold>?a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP else ?rhs)\<close>
    by (auto simp add: ndet_write_def read_def
        Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_left comp_def
        intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])
  also have \<open>\<dots> = ?rhs\<close>
    by (simp add: read_def comp_def)
      (use Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_left that(1) in force)
  finally show \<open>?lhs = ?rhs\<close> .
qed


corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_right :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>B \<rightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<inter> S = {}\<close>
  by (subst (1 2) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_left[OF that(2, 1)])

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_right :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<inter> S = {}\<close>
  by (subst (1 2) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_left[OF that(2, 1)])



paragraph \<open>\<^const>\<open>read\<close> and \<^const>\<open>write\<close>.\<close>

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (\<box>b\<in>(d ` B - S) \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<box>
   (if c a \<in> d ` B \<inter> S then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d (c a))) else STOP)\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read[where A = \<open>{a}\<close>, simplified])
    (simp add: write_is_write0 image_iff)

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q =
   (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box>
   (\<box>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)) \<box>
   (if d b \<in> c ` A \<inter> S then d\<^bold>!b \<rightarrow> (P (inv_into A c (d b)) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write[where B = \<open>{b}\<close>, simplified])
    (simp add: write_is_write0 image_iff)


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset :
  \<open>c a \<in> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (if c a \<in> d ` B then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d (c a))) else STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read)
    (metis Det_STOP Det_commute Diff_eq_empty_iff Mprefix_empty)

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d b \<in> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q =
   (if d b \<in> c ` A then d\<^bold>!b \<rightarrow> (P (inv_into A c (d b)) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write)
    (metis Diff_eq_empty_iff Mprefix_empty STOP_Det)


\<comment> \<open>If we have the same injective channel, it's better.\<close>
lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_same_chan:
  \<open>c a \<in> S \<Longrightarrow> c ` B \<subseteq> S \<Longrightarrow> inj_on c (insert a B) \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> c\<^bold>?b\<in>B \<rightarrow> Q b = (if a \<in> B then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a) else STOP)\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_same_chan[where A = \<open>{a}\<close>, simplified]) simp_all

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_subset_same_chan:
  \<open>c ` A \<subseteq> S \<Longrightarrow> c b \<in> S \<Longrightarrow> inj_on c (insert b A) \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> c\<^bold>!b \<rightarrow> Q = (if b \<in> A then c\<^bold>!b \<rightarrow> (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset_same_chan[where B = \<open>{b}\<close>, simplified]) simp_all


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_indep :
  \<open>c a \<notin> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box> (d\<^bold>?b\<in>B \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_indep[where A = \<open>{a}\<close>, simplified])
    (simp_all add: write_is_write0)

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q =
   (d\<^bold>!b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box> (c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q))\<close>
  by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_indep[where B = \<open>{b}\<close>, simplified])
    (simp_all add: write_is_write0)


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_left :
  \<open>c a \<notin> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_left[where A = \<open>{a}\<close>, simplified]) simp_all

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_left :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d b \<in> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)\<close>
  by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_left[where B = \<open>{b}\<close>, simplified]) simp_all


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_right :
  \<open>c a \<in> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>B \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_right[where A = \<open>{a}\<close>, simplified]) simp_all

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = d\<^bold>!b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_right[where B = \<open>{b}\<close>, simplified]) simp_all



paragraph \<open>\<^const>\<open>ndet_write\<close> and \<^const>\<open>ndet_write\<close>\<close>

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if A = {} then   if d ` B \<inter> S = {} then d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
                     else (\<sqinter>x\<in>d ` (B - d -` S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d x))) \<sqinter> STOP
    else   if B = {} then   if c ` A \<inter> S = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
                          else (\<sqinter>x\<in>c ` (A - c -` S) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)) \<sqinter> STOP
         else \<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A.
              (if a \<in> S then STOP else a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q (inv_into B d b))) \<box>
              (if b \<in> S then STOP else b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<box>
              (if a = b \<and> b \<in> S then b \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b)) else STOP))\<close>
proof -
  have \<open>d ` (B - d -` S) = d ` B - S\<close> \<open>c ` (A - c -` S) = c ` A - S\<close> by auto
  thus ?thesis
    by (auto simp add: ndet_write_def Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix comp_def
        intro!: mono_GlobalNdet_eq split: if_split_asm)
qed


lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if \<exists>b. c ` A = {b} \<and> d ` B = {b}
    then (THE b. d ` B = {b}) \<rightarrow> (P (inv_into A c (THE a. c ` A = {a})) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d (THE b. d ` B = {b})))
    else (\<sqinter>x\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d x))) \<sqinter> STOP)\<close>
  by (auto simp add: ndet_write_def Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_subset)


corollary inj_on_ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if \<exists>b. c ` A = {b} \<and> d ` B = {b}
    then d (THE b. B = {b}) \<rightarrow> (P (THE a. A = {a}) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (THE b. B = {b}))
    else (\<sqinter>x\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d x))) \<sqinter> STOP)\<close>
  if \<open>inj_on c A\<close> \<open>inj_on d B\<close> \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  from that(1) have \<open>c ` A = {a'} \<Longrightarrow> \<exists>!a. A = {a} \<and> a' = c a\<close> for a'
    by (fastforce elim!: inj_img_insertE)
  moreover from that(2) have \<open>d ` B = {b'} \<Longrightarrow> \<exists>!b. B = {b} \<and> b' = d b\<close> for b'
    by (fastforce elim!: inj_img_insertE)
  ultimately show ?thesis
    by (auto simp add: ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset[OF that(3, 4)] inv_into_f_eq
        intro: arg_cong2[where f = \<open>(\<rightarrow>)\<close>] arg_cong2[where f = \<open>\<lambda>P Q. P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close>])
qed


lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if A = {} then d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
    else   if B = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
         else \<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A.
              ((a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q (inv_into B d b)))) \<box>
              ((b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b)))))\<close>
  by (auto simp add: ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write disjoint_iff intro!: mono_GlobalNdet_eq)


lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_left :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)\<close>
  by (simp add: ndet_write_def Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_left comp_def)


lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  by (simp add: ndet_write_def Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix_right comp_def)



paragraph \<open>\<^const>\<open>ndet_write\<close> and \<^const>\<open>write\<close>\<close>

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP
    else \<sqinter>b\<in>d ` B. (if b \<in> S then STOP else b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<box>
                   (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (if b = c a \<and> c a \<in> S then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d (c a))) else STOP))\<close>
  by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write[where A = \<open>{a}\<close>, simplified],
      auto simp add: write_def Mprefix_singl split: if_split_asm
      intro!: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>] mono_Mprefix_eq)
    (simp add: insert_Diff_if write0_def)

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q
    else \<sqinter>a\<in>c ` A. (if a \<in> S then STOP else a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)) \<box>
                   (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box>
                   (if a = d b \<and> d b \<in> S then d\<^bold>!b \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP))\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read[where B = \<open>{b}\<close>, simplified],
      auto simp add: write_def Mprefix_singl split: if_split_asm
      intro!: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>] mono_Mprefix_eq)
    (simp add: insert_Diff_if write0_def)


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if c a \<notin> d ` B then STOP else if d ` B = {c a} then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d (c a)))
    else (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d (c a)))) \<sqinter> STOP)\<close> if \<open>c a \<in> S\<close> \<open>d ` B \<subseteq> S\<close>
proof (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset[where A = \<open>{a}\<close>, simplified])
  from \<open>c a \<in> S\<close> show \<open>c a \<in> S\<close> .
next
  from \<open>d ` B \<subseteq> S\<close> show \<open>d ` B \<subseteq> S\<close> .
next
  show \<open>(  if d ` B \<subseteq> {c a} then \<sqinter>b\<in>d ` B \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))
         else (\<sqinter>b\<in>(c ` {a} \<inter> d ` B) \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<sqinter> STOP) =
        (  if c a \<notin> d ` B then STOP else if d ` B = {c a} then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d (c a)))
         else (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d (c a)))) \<sqinter> STOP)\<close>
    (is \<open>?lhs = (if c a \<notin> d ` B then STOP else if d ` B = {c a} then ?rhs else ?rhs \<sqinter> STOP)\<close>)
  proof (split if_split, intro conjI impI)
    show \<open>c a \<notin> d ` B \<Longrightarrow> ?lhs = STOP\<close>
      by (auto simp add: GlobalNdet_is_STOP_iff image_subset_iff image_iff)
  next
    show \<open>\<not> c a \<notin> d ` B \<Longrightarrow> ?lhs = (if d ` B = {c a} then ?rhs else ?rhs \<sqinter> STOP)\<close>
      by (auto simp add: image_subset_iff Ndet_is_STOP_iff write_is_write0)
  qed
qed

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_subset :
  \<open>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (d\<^bold>!b \<rightarrow> Q) =
   (  if d b \<notin> c ` A then STOP else if c ` A = {d b} then d\<^bold>!b \<rightarrow> (P (inv_into A c (d b)) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)
    else (d\<^bold>!b \<rightarrow> (P (inv_into A c (d b)) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<sqinter> STOP)\<close> if \<open>c ` A \<subseteq> S\<close> \<open>d b \<in> S\<close>
  by (subst (1 2 3) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset that)


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_indep :
  \<open>c a \<notin> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
    else \<sqinter>b\<in>d ` B. (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))))\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_indep[where A = \<open>{a}\<close>, simplified])
    (auto simp add: write_is_write0 intro: mono_GlobalNdet_eq)

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q =
   (  if A = {} then d\<^bold>!b \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)
    else \<sqinter>a\<in>c ` A. (a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)) \<box>
                   (d\<^bold>!b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)))\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_indep[where B = \<open>{b}\<close>, simplified])
    (auto simp add: write_is_write0 intro: mono_GlobalNdet_eq)


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_left :
  \<open>c a \<notin> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_left[where A = \<open>{a}\<close>, simplified]) simp_all

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_left :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d b \<in> S \<Longrightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_left[where B = \<open>{b}\<close>, simplified]) simp_all


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_right :
  \<open>c a \<in> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_right[where A = \<open>{a}\<close>, simplified]) simp_all

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d b \<notin> S \<Longrightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = d\<^bold>!b \<rightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  by (subst ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_right[where B = \<open>{b}\<close>, simplified]) simp_all



paragraph \<open>\<^const>\<open>write\<close> and \<^const>\<open>write\<close>\<close>

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q =
   (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box>
   (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)) \<box>
   (if c a = d b \<and> d b \<in> S then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (subst read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read[where A = \<open>{a}\<close> and B = \<open>{b}\<close>, simplified])
    (simp add: write_def insert_Diff_if Det_commute Int_insert_right)

lemma write_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write :
  \<open>c\<^bold>!a \<rightarrow> P |||\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = (c\<^bold>!a \<rightarrow> (P |||\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)) \<box> (d\<^bold>!b \<rightarrow> (c\<^bold>!a \<rightarrow> P |||\<^sub>\<checkmark> Q))\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write Det_commute)

lemma write_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write :
  \<open>c\<^bold>!a \<rightarrow> P ||\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = (if c a = d b then c\<^bold>!a \<rightarrow> (P ||\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write)


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_subset :
  \<open>c a \<in> S \<Longrightarrow> d b \<in> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = (if c a = d b then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write)

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_indep :
  \<open>c a \<notin> S \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)) \<box> (d\<^bold>!b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  by (simp add: Det_commute write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write)


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_left :
  \<open>c a \<notin> S \<Longrightarrow> d b \<in> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)\<close>
  by (auto simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write)


lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_right :
  \<open>c a \<in> S \<Longrightarrow> d b \<notin> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = d\<^bold>!b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  by (auto simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write)




paragraph \<open>\<^const>\<open>read\<close> and \<^const>\<open>write0\<close>.\<close>

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (\<box>b\<in>(d ` B - S) \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<box>
   (if a \<in> d ` B \<inter> S then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d a)) else STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q =
   (if b \<in> S then STOP else b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box>
   (\<box>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)) \<box>
   (if b \<in> c ` A \<inter> S then b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset :
  \<open>a \<in> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (if a \<in> d ` B then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d a)) else STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> b \<in> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q =
   (if b \<in> c ` A then b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_subset[where d = \<open>\<lambda>x. x\<close>, unfolded write_is_write0])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_same_chan:
  \<open>a \<in> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> id\<^bold>?b\<in>B \<rightarrow> Q b = (if a \<in> B then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a) else STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_subset_same_chan
      [where c = id, unfolded write_is_write0, simplified])

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_subset_same_chan:
  \<open>A \<subseteq> S \<Longrightarrow> b \<in> S \<Longrightarrow>
   id\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = (if b \<in> A then b \<rightarrow> (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_subset_same_chan
      [where c = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_indep :
  \<open>a \<notin> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box> (d\<^bold>?b\<in>B \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_indep[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> b \<notin> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q =
   (b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box> (c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q))\<close>
  by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_indep[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_left :
  \<open>a \<notin> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_left[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_left :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> b \<in> S \<Longrightarrow> c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)\<close>
  by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_left[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_right :
  \<open>a \<in> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>B \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read_right[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> b \<notin> S \<Longrightarrow> c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  by (simp add: read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_right[where d = id, unfolded write_is_write0, simplified])



paragraph \<open>\<^const>\<open>ndet_write\<close> and \<^const>\<open>write0\<close>\<close>

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP
    else \<sqinter>b\<in>d ` B. (if b \<in> S then STOP else b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))) \<box>
                   (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (if b = a \<and> a \<in> S then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d a)) else STOP))\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write[where c = \<open>\<lambda>x. x\<close>, unfolded write_is_write0, simplified])

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q
    else \<sqinter>a\<in>c ` A. (if a \<in> S then STOP else a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)) \<box>
                   (if b \<in> S then STOP else b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box>
                   (if a = b \<and> b \<in> S then b \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP))\<close>
  by (simp add: ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write[where d = \<open>\<lambda>x. x\<close>, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset :
  \<open>a \<in> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if a \<notin> d ` B then STOP else if d ` B = {a} then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d a))
    else (a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d a))) \<sqinter> STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_subset[where c = id, unfolded write_is_write0, simplified])

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> b \<in> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q =
   (  if b \<notin> c ` A then STOP else if c ` A = {b} then b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)
    else (b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<sqinter> STOP)\<close>
  by (simp add: ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_subset[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_indep :
  \<open>a \<notin> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
    else \<sqinter>b\<in>d ` B. (a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q (inv_into B d b))))\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_indep[where c = id, unfolded write_is_write0, simplified])

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> b \<notin> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q =
   (  if A = {} then b \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)
    else \<sqinter>a\<in>c ` A. (a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)) \<box>
                   (b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)))\<close>
  by (simp add: ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_indep[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_left :
  \<open>a \<notin> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_left[where c = id, unfolded write_is_write0, simplified])

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_left :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> b \<in> S \<Longrightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)\<close>
  by (simp add: ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_left[where d = id, unfolded write_is_write0, simplified])

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write0_right :
  \<open>a \<in> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write_right[where c = id, unfolded write_is_write0, simplified])

lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> b \<notin> S \<Longrightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = b \<rightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  by (simp add: ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_right[where d = id, unfolded write_is_write0, simplified])



paragraph \<open>\<^const>\<open>write0\<close> and \<^const>\<open>write0\<close>\<close>

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q =
   (if b \<in> S then STOP else b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box>
   (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)) \<box>
   (if a = b \<and> b \<in> S then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write[where c = id and d = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_bis :
  \<open>(a \<rightarrow> P) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> Q) =
   (  if a \<in> S
    then   if b \<in> S
         then   if a = b
              then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)
              else STOP
         else (b \<rightarrow> ((a \<rightarrow> P) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))
    else   if b \<in> S
         then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> Q))
    else (a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> Q))) \<box> (b \<rightarrow> ((a \<rightarrow> P) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)))\<close>
  by (cases \<open>a \<in> S\<close>; cases \<open>b \<in> S\<close>) (auto simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 Det_commute)

lemma write0_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 :
  \<open>a \<rightarrow> P |||\<^sub>\<checkmark> b \<rightarrow> Q = (a \<rightarrow> (P |||\<^sub>\<checkmark> b \<rightarrow> Q)) \<box> (b \<rightarrow> (a \<rightarrow> P |||\<^sub>\<checkmark> Q))\<close>
  by (simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 Det_commute)

lemma write0_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 :
  \<open>a \<rightarrow> P ||\<^sub>\<checkmark> b \<rightarrow> Q = (if a = b then a \<rightarrow> (P ||\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0)



lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_subset :
  \<open>a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = (if a = b then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_subset[where c = id and d = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_indep :
  \<open>a \<notin> S \<Longrightarrow> b \<notin> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = (a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)) \<box> (b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_indep[where c = id and d = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_left :
  \<open>a \<notin> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_left[where c = id and d = id, unfolded write_is_write0, simplified])

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_right :
  \<open>a \<in> S \<Longrightarrow> b \<notin> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_right[where c = id and d = id, unfolded write_is_write0, simplified]) 


paragraph \<open>\<^const>\<open>write\<close> and \<^const>\<open>write0\<close>\<close>

lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q =
   (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box>
   (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)) \<box>
   (if a = d b \<and> d b \<in> S then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 write_is_write0)

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q =
   (if b \<in> S then STOP else b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)) \<box>
   (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)) \<box>
   (if c a = b \<and> b \<in> S then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 write_is_write0)


lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_subset :
  \<open>a \<in> S \<Longrightarrow> d b \<in> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = (if a = d b then a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write)

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_subset :
  \<open>c a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = (if c a = b then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) else STOP)\<close>
  by (simp add: write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0)


lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_indep :
  \<open>a \<notin> S \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = (a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)) \<box> (d\<^bold>!b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  by (simp add: Det_commute write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write)

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_indep :
  \<open>c a \<notin> S \<Longrightarrow> b \<notin> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)) \<box> (b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  by (simp add: Det_commute write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0)


lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_left :
  \<open>a \<notin> S \<Longrightarrow> d b \<in> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q)\<close>
  by (simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_left write_is_write0)

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_left :
  \<open>c a \<notin> S \<Longrightarrow> b \<in> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q)\<close>
  by (simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_left write_is_write0)


lemma write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write_right :
  \<open>a \<in> S \<Longrightarrow> d b \<notin> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = d\<^bold>!b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  by (simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_right write_is_write0)

lemma write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_right :
  \<open>c a \<in> S \<Longrightarrow> b \<notin> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  by (simp add: write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_right write_is_write0)



subsubsection \<open>Synchronization with \<^const>\<open>SKIP\<close> and \<^const>\<open>STOP\<close>\<close>

paragraph \<open>\<^const>\<open>SKIP\<close>\<close>

text \<open>Without injectivity, the result is a trivial corollary of
      @{thm read_def[no_vars]} and @{thm Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP[no_vars]}.\<close>

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r = c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)\<close> if \<open>inj_on c A\<close>
proof -
  have \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
  show \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r = c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)\<close>
    by (auto simp add: read_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP \<open>?this\<close> inj_on_diff \<open>inj_on c A\<close>
        intro: mono_Mprefix_eq)
qed

lemma SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read :
  \<open>SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close> if \<open>inj_on d B\<close>
proof -
  have \<open>d ` (B - d -` S) = d ` B - S\<close> by blast
  show \<open>SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
    by (auto simp add: read_def SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix \<open>?this\<close> inj_on_diff \<open>inj_on d B\<close>
        intro: mono_Mprefix_eq)
qed


corollary write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP s = (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP s))\<close>
  and SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write :
  \<open>SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  by (simp_all add: write_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix Diff_triv)

corollary write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP s = (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP s))\<close>
  and SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 :
  \<open>SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = (if b \<in> S then STOP else b \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  by (simp_all add: write0_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix Diff_triv)


lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r =
   (  if c ` A \<inter> S = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)
    else (c\<^bold>!\<^bold>!a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if _ then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>) if \<open>inj_on c A\<close>
proof (split if_split, intro conjI impI)
  assume \<open>c ` A \<inter> S = {}\<close>
  hence \<open>A - c -` S = A\<close> by blast
  from \<open>c ` A \<inter> S = {}\<close> show \<open>?lhs = ?rhs1\<close>
    by (auto simp add: \<open>?this\<close> ndet_write_is_GlobalNdet_write0 disjoint_iff
        Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP
        intro!: mono_GlobalNdet_eq split: if_split_asm)
next
  show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close> if \<open>c ` A \<inter> S \<noteq> {}\<close>
  proof (cases \<open>c ` A - S = {}\<close>)
    assume \<open>c ` A - S = {}\<close>
    hence \<open>A - c -` S = {}\<close> by blast
    from \<open>c ` A - S = {}\<close> show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close>
      by (auto simp add: ndet_write_is_GlobalNdet_write0 GlobalNdet_is_STOP_iff
          \<open>?this\<close> Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP)
  next
    have \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
    show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close> if \<open>c ` A - S \<noteq> {}\<close>
      by (subst Ndet_commute, unfold ndet_write_is_GlobalNdet_write0 Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right)
        (auto simp add: GlobalNdet_is_STOP_iff write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP
          \<open>?this\<close> \<open>inj_on c A\<close> inj_on_diff
          simp flip: GlobalNdet_factorization_union
          [OF \<open>c ` A \<inter> S \<noteq> {}\<close> \<open>c ` A - S \<noteq> {}\<close>, unfolded Int_Diff_Un]
          intro!: arg_cong2[where f = \<open>(\<sqinter>)\<close>] mono_GlobalNdet_eq)
  qed
qed

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write :
  \<open>inj_on d B \<Longrightarrow> SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if d ` B \<inter> S = {} then d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
    else (d\<^bold>!\<^bold>!b\<in>(B - d -` S) \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<sqinter> STOP)\<close>
  by (subst (1 2 3) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP)




corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP :
  \<open>\<sqinter>a \<in> A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r =
   (if A \<inter> S = {} then \<sqinter>a \<in> A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)
   else (\<sqinter>a \<in> (A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)) \<sqinter> STOP)\<close>  
  using ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP[of id A P S r]
  by (simp add: ndet_write_id_is_Mndetprefix)

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP_Mndetprefix :
  \<open>SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter>b \<in> B \<rightarrow> Q b =
   (  if B \<inter> S = {} then \<sqinter>b \<in> B \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
    else (\<sqinter>b \<in> (B - S) \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<sqinter> STOP)\<close>
  by (subst (1 2 3) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP)



paragraph \<open>\<^const>\<open>STOP\<close>\<close>

text \<open>Without injectivity, the result is a trivial corollary of
      @{thm read_def[no_vars]} and @{thm Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP[no_vars]}.\<close>

lemma read_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP = c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)\<close> if \<open>inj_on c A\<close>
proof -
  have \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
  show \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP = c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)\<close>
    by (auto simp add: \<open>?this\<close> read_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP inj_on_diff \<open>inj_on c A\<close>
        intro: mono_Mprefix_eq)
qed

lemma STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read :
  \<open>STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close> if \<open>inj_on d B\<close>
proof -
  have \<open>d ` (B - d -` S) = d ` B - S\<close> by blast
  show \<open>STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
    by (auto simp add: \<open>?this\<close> read_def STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix inj_on_diff \<open>inj_on d B\<close>
        intro: mono_Mprefix_eq)
qed


corollary write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP = (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP))\<close>
  and STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write :
  \<open>STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!b \<rightarrow> Q = (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  by (simp_all add: write_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix Diff_triv)

corollary write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP = (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP))\<close>
  and STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 :
  \<open>STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> b \<rightarrow> Q = (if b \<in> S then STOP else b \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  by (simp_all add: write0_def Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix Diff_triv)


lemma ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP =
   (  if c ` A \<inter> S = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)
    else (c\<^bold>!\<^bold>!a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if _ then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>) if \<open>inj_on c A\<close>
proof (split if_split, intro conjI impI)
  assume \<open>c ` A \<inter> S = {}\<close>
  hence \<open>A - c -` S = A\<close> by blast
  from \<open>c ` A \<inter> S = {}\<close> show \<open>?lhs = ?rhs1\<close>
    by (auto simp add: \<open>?this\<close> ndet_write_is_GlobalNdet_write0 disjoint_iff
        Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP
        intro!: mono_GlobalNdet_eq split: if_split_asm)
next
  show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close> if \<open>c ` A \<inter> S \<noteq> {}\<close>
  proof (cases \<open>c ` A - S = {}\<close>)
    assume \<open>c ` A - S = {}\<close>
    hence \<open>A - c -` S = {}\<close> by blast
    from \<open>c ` A - S = {}\<close> show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close>
      by (auto simp add: ndet_write_is_GlobalNdet_write0 GlobalNdet_is_STOP_iff
          \<open>?this\<close> Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP)
  next
    have \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
    show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close> if \<open>c ` A - S \<noteq> {}\<close>
      by (subst Ndet_commute, unfold ndet_write_is_GlobalNdet_write0 Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right)
        (auto simp add: GlobalNdet_is_STOP_iff write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP
          \<open>?this\<close> \<open>inj_on c A\<close> inj_on_diff
          simp flip: GlobalNdet_factorization_union
          [OF \<open>c ` A \<inter> S \<noteq> {}\<close> \<open>c ` A - S \<noteq> {}\<close>, unfolded Int_Diff_Un]
          intro!: arg_cong2[where f = \<open>(\<sqinter>)\<close>] mono_GlobalNdet_eq)
  qed
qed

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write :
  \<open>inj_on d B \<Longrightarrow> STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if d ` B \<inter> S = {} then d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)
    else (d\<^bold>!\<^bold>!b\<in>(B - d -` S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<sqinter> STOP)\<close>
  by (subst (1 2 3) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.ndet_write_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP)


end



(*<*)
end
  (*>*)