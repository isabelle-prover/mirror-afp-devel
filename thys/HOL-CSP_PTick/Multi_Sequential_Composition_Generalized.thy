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


chapter \<open>Architectural Versions\<close>

section \<open>Sequential Composition\<close>

(*<*)
theory Multi_Sequential_Composition_Generalized
  imports Synchronization_Product_Generalized_Interpretations
begin
  (*>*)


subsection \<open>Definition\<close>

fun MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>['b list, 'b \<Rightarrow> 'r \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil  : \<open>MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k   []    P = SKIP\<close>
  |     MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons : \<open>MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (l # L) P = (\<lambda>r. P l r \<^bold>;\<^sub>\<checkmark> MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k L P)\<close>


syntax  "_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" ::
  \<open>[pttrn, 'b list, 'b \<Rightarrow> 'r \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3SEQ\<^sub>\<checkmark> _ \<in>@ _./ _)\<close> [78,78,77] 77)
syntax_consts "_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" \<rightleftharpoons> MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
translations  "SEQ\<^sub>\<checkmark> p \<in>@ L. P" \<rightleftharpoons> "CONST MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k L (\<lambda>p. P)"



subsection \<open>First Properties\<close>

\<comment>\<open>Some tests\<close>
lemma \<open>SEQ\<^sub>\<checkmark> p \<in>@ []. P p = SKIP\<close> 
  and \<open>SEQ\<^sub>\<checkmark> p \<in>@ [a]. P p = (\<lambda>r. P a r)\<close> 
  and \<open>SEQ\<^sub>\<checkmark> p \<in>@ [a, b]. P p = (\<lambda>r. P a r \<^bold>;\<^sub>\<checkmark> P b)\<close> 
  and \<open>SEQ\<^sub>\<checkmark> p \<in>@ [a, b, c]. P p = (\<lambda>r. P a r \<^bold>;\<^sub>\<checkmark> P b \<^bold>;\<^sub>\<checkmark> P c)\<close> 
  by (simp_all add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc)

lemma \<open>SEQ\<^sub>\<checkmark> p \<in>@ [1::int .. 3]. P p = (\<lambda>r. P 1 r \<^bold>;\<^sub>\<checkmark> P 2 \<^bold>;\<^sub>\<checkmark> P 3)\<close>
  by (simp add: upto.simps Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc)



lemma \<open>(SEQ\<^sub>\<checkmark> p \<in>@ []. P p) = SKIP\<close> by (fact MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil)

lemma \<open>(SEQ\<^sub>\<checkmark> l \<in>@ (a # L). P l) = (\<lambda>r. P a r \<^bold>;\<^sub>\<checkmark> SEQ\<^sub>\<checkmark> l \<in>@ L. P l)\<close> by (fact MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons)


lemma MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_singl [simp] : \<open>SEQ\<^sub>\<checkmark> l \<in>@ [a]. P l = P a\<close> by simp

lemma MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc : \<open>SEQ\<^sub>\<checkmark> l \<in>@ (L @ [a]). P l = (\<lambda>r. (SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r \<^bold>;\<^sub>\<checkmark> P a)\<close>
  by (induct L) (simp_all add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc)


lemma mono_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq:
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> P l = Q l) \<Longrightarrow> SEQ\<^sub>\<checkmark> l \<in>@ L. P l = SEQ\<^sub>\<checkmark> l \<in>@ L. Q l\<close>
  by (induct L) fastforce+


lemma MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_const [simp] :
  \<open>(SEQ\<^sub>\<checkmark> l \<in>@ L. (\<lambda>r. P l)) =
   (if L = [] then SKIP else (\<lambda>r. SEQ l \<in>@ L. P l))\<close>
  by (induct L rule: rev_induct) (auto simp add: MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc)



subsection \<open>Behaviour with binary version\<close>

lemma MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append:
  \<open>SEQ\<^sub>\<checkmark> l \<in>@ (L1 @ L2). P l = (\<lambda>r. (SEQ\<^sub>\<checkmark> l \<in>@ L1. P l) r \<^bold>;\<^sub>\<checkmark> SEQ\<^sub>\<checkmark> l \<in>@ L2. P l)\<close>
  by (induct L1 rule: list.induct, simp_all, metis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc)



subsection \<open>Other Properties\<close>

lemma MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP_neutral:
  \<open>P a = SKIP \<Longrightarrow> SEQ\<^sub>\<checkmark> l \<in>@ (L1 @ [a] @ L2). P l = SEQ\<^sub>\<checkmark> l \<in>@ (L1 @ L2). P l\<close>
  by (simp add: MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append)

lemma MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_BOT_absorb:
  \<open>P a = \<bottom> \<Longrightarrow> SEQ\<^sub>\<checkmark> l \<in>@ (L1 @ [a] @ L2). P l = (\<lambda>r. (SEQ\<^sub>\<checkmark> l \<in>@ L1. P l) r \<^bold>;\<^sub>\<checkmark> \<bottom>)\<close>
  by (simp add: MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append lambda_strict)

lemma MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP_absorb:
  \<open>P a = (\<lambda>r. STOP) \<Longrightarrow> SEQ\<^sub>\<checkmark> l \<in>@ (L1 @ [a] @ L2). P l =
                        (\<lambda>r. (SEQ\<^sub>\<checkmark> l \<in>@ L1. P l) r \<^bold>; STOP)\<close>
  by (simp add: MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append)

lemma is_ticks_length_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>((SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r)\<close>
  if \<open>L \<noteq> []\<close> and \<open>\<And>r'. r' \<in> \<^bold>\<checkmark>\<^bold>s((SEQ\<^sub>\<checkmark> l \<in>@ (butlast L). P l) r) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P (last L) r')\<close>
proof -
  from that(1) obtain l L' where \<open>L = L' @ [l]\<close>
    by (cases L rule: rev_cases) auto
  with that(2) have \<open>r' \<in> \<^bold>\<checkmark>\<^bold>s((SEQ\<^sub>\<checkmark> l \<in>@ L'. P l) r) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P l r')\<close> for r' by simp
  thus ?thesis
    by (auto simp add: \<open>L = L' @ [l]\<close> MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc intro: is_ticks_length_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed


subsection \<open>Behaviour with injectivity\<close>

lemma inj_on_mapping_over_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>inj_on f (set L) \<Longrightarrow>
   SEQ\<^sub>\<checkmark> l \<in>@ L. P l = SEQ\<^sub>\<checkmark> l \<in>@ map f L. P (inv_into (set L) f l)\<close>
proof (induct L)
  show \<open>inj_on f (set []) \<Longrightarrow> MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [] P =
        SEQ\<^sub>\<checkmark> x\<in>@map f []. P (inv_into (set []) f x)\<close> by simp
next
  case (Cons a L)
  show ?case
  proof (rule ext)
    fix r
    have \<open>(SEQ\<^sub>\<checkmark> l \<in>@ (a # L). P l) r = P a r \<^bold>;\<^sub>\<checkmark> SEQ\<^sub>\<checkmark> l \<in>@ L. P l\<close> by simp
    also have \<open>SEQ\<^sub>\<checkmark> l \<in>@ L. P l = SEQ\<^sub>\<checkmark> l \<in>@ map f L. P (inv_into (set L) f l)\<close>
      using Cons.hyps Cons.prems by auto
    also have \<open>\<dots> = SEQ\<^sub>\<checkmark> l \<in>@ map f L. P (inv_into (set (a # L)) f l)\<close>
      using Cons.prems by (auto intro!: mono_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
    finally show \<open>(SEQ\<^sub>\<checkmark> l \<in>@ (a # L). P l) r =
                  (SEQ\<^sub>\<checkmark> l \<in>@ map f (a # L). P (inv_into (set (a # L)) f l)) r\<close>
      using Cons.prems by auto
  qed
qed



(*<*)
end
  (*>*)