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
theory Multi_Synchronization_Product_Generalized
  imports Synchronization_Product_Generalized_Interpretations
    "HOL-Combinatorics.List_Permutation"
begin
  (*>*)


unbundle no funcset_syntax
  \<comment> \<open>Inherited from \<^theory>\<open>HOL-Combinatorics.List_Permutation\<close>.\<close>


section \<open>Synchronization Product\<close>

subsection \<open>Definition\<close>

text (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale) \<open>
The generalized synchronization product is not
really commutative (see @{thm Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute[no_vars]}).
We therefore define the architectural version on a list.\<close>

fun MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>['a set, 'b list, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k S [] P = STOP\<close>
  |     \<open>MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k S [l] P = RenamingTick (P l) (\<lambda>r. [r])\<close>
  |     \<open>MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k S (l # m # L) P = P l \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k S (m # L) P\<close>


syntax "_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" ::
  \<open>[pttrn, 'a set, 'b list, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3\<^bold>\<lbrakk>_\<^bold>\<rbrakk>\<^sub>\<checkmark> _ \<in>@ _./ _)\<close> [78,78,78,77] 77)
syntax_consts "_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" \<rightleftharpoons> MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
translations "\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P" \<rightleftharpoons> "CONST MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k S L (\<lambda>l. P)"



text \<open>Special case of \<^term>\<open>MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k S P\<close> when \<^term>\<open>S = {}\<close>.\<close>

abbreviation MultiInter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>['b list, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>MultiInter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k L P \<equiv> MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k {} L P\<close> 

syntax "_MultiInter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" ::
  \<open>[pttrn, 'b list, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> _\<in>@_./ _)\<close> [78,78,77] 77)
syntax_consts "_MultiInter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" \<rightleftharpoons> MultiInter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
translations "\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P" \<rightleftharpoons> "CONST MultiInter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k L (\<lambda>l. P)"



text \<open>Special case of \<^term>\<open>MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k S P\<close> when \<^term>\<open>S = UNIV\<close>.\<close>

abbreviation MultiPar\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>['b list, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>MultiPar\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k L P \<equiv> MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k UNIV L P\<close> 

syntax "_MultiPar\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" ::
  \<open>[pttrn, 'b list, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3\<^bold>|\<^bold>|\<^sub>\<checkmark> _\<in>@_./ _)\<close> [78,78,77] 77)
syntax_consts "_MultiPar\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" \<rightleftharpoons> MultiPar\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
translations "\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P" \<rightleftharpoons> "CONST MultiPar\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k L (\<lambda>l. P)"



subsection \<open>First properties\<close>

lemma is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>length L\<^esub>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l)\<close>
  by (induct L rule: induct_list012)
    (simp_all add: is_ticks_length_STOP is_ticks_length_Renaming
      is_ticks_length_Suc_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t)


lemma MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ (l # L). P m =
   (  if L = [] then RenamingTick (P l) (\<lambda>r. [r])
    else P l \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ L. P m)\<close>
  by (cases L) simp_all



lemma mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq :
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> P l = Q l) \<Longrightarrow> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. Q l\<close>
  by (induct L rule: induct_list012) simp_all

lemma mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq2:
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> P (f l) = Q l) \<Longrightarrow> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ map f L. P l = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. Q l\<close>
  by (induct L rule: induct_list012) simp_all



\<comment> \<open>Some tests\<close>
lemma \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ []. P l) = STOP\<close> 
  and \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [a]. P l) = RenamingTick (P a) (\<lambda>r. [r])\<close> 
  and \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [a, b]. P l) = P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t RenamingTick (P b) (\<lambda>r. [r])\<close>  
  and \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ [a, b, c]. P l) = P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (P b \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t RenamingTick (P c) (\<lambda>r. [r]))\<close>    
  by simp_all



subsection \<open>Properties\<close>

lemma MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff:
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l = \<bottom> \<longleftrightarrow> (\<exists>l \<in> set L. P l = \<bottom>)\<close>
  by (induct L rule: induct_list012)
    (simp_all add: Renaming_is_BOT_iff Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff)


lemma MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_BOT_absorb:
  \<open>l \<in> set L \<Longrightarrow> P l = \<bottom> \<Longrightarrow> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l = \<bottom>\<close>
  using MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff by blast


lemma MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP_id :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> r \<in>@ L. SKIP r = (if L = [] then STOP else SKIP L)\<close>
  by (induct L rule: induct_list012) simp_all



subsection \<open>Behaviour with binary version\<close>

lemma MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append :
  \<open>L1 \<noteq> [] \<Longrightarrow> L2 \<noteq> [] \<Longrightarrow>
   \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (L1 @ L2). P l =
   \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L1. P l \<^bsub>length L1\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>length L2\<^esub> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L2. P l\<close>
proof (induct L1 rule: list_nonempty_induct)
  case (single l) thus ?case
    by (simp add: is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons flip: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s)
next
  let ?RT = \<open>\<lambda>P. RenamingTick P (\<lambda>r. [r])\<close>
  case (cons l L1)
  have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ ((l # L1) @ L2). P l = P l \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (L1 @ L2). P l\<close>
    by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons \<open>L1 \<noteq> []\<close>)
  also have \<open>\<dots> = ?RT (P l) \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>length (L1 @ L2)\<^esub> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (L1 @ L2). P l\<close>
    by (intro Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  also have \<open>\<dots> = ?RT (P l) \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>length L1 + length L2\<^esub>
                  (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L1. P l \<^bsub>length L1\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>length L2\<^esub> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L2. P l)\<close>
    using cons.hyps(2) cons.prems by simp
  also have \<open>\<dots> = ?RT (P l) \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>length L1\<^esub> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L1. P l
                  \<^bsub>Suc 0 + length L1\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>length L2\<^esub> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L2. P l\<close>
    by (simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_assoc)
  also have \<open>?RT (P l) \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>length L1\<^esub> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L1. P l =
             P l \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L1. P l\<close>
    by (intro Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s[symmetric] is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  also have \<open>\<dots> = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l # L1). P l\<close>
    by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons \<open>L1 \<noteq> []\<close>)
  finally show ?case by simp
qed



subsection \<open>Behaviour with injectivity\<close>

lemma inj_on_mapping_over_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>inj_on f (set L) \<Longrightarrow> 
   \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ map f L. P (inv_into (set L) f l)\<close>
proof (induct L rule: induct_list012)
  case (3 l' l'' L)
  have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l' # l'' # L). P l =
        P l' \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l'' # L). P l\<close> by simp
  also have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (l'' # L). P l =
             \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ map f (l'' # L). P (inv_into (set (l'' # L)) f l)\<close>
    by (metis "3.hyps"(2) "3.prems" inj_on_insert list.simps(15))
  also have \<open>\<dots> = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ map f (l'' # L). P (inv_into (set (l' # l'' # L)) f l)\<close>
    using "3.prems" by (auto intro!: mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
  also have \<open>P l' = P (inv_into (set (l' # l'' # L)) f (f l'))\<close>
    using "3.prems" by auto
  finally show ?case by simp
qed simp_all



subsection \<open>Permuting the Sequence\<close>

subsubsection \<open>A particular Case\<close>

lemma MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ (L @ [l]). P m =
   (  if L = [] then RenamingTick (P l) (\<lambda>r. [r])
    else \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ L. P m \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l)\<close>
  by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append)
    (metis (lifting) ext Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)


text \<open>
At the beginning, we wanted to prove the following property.
\<close>

theorem MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (rev L). P l = RenamingTick (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) rev\<close>
proof (induct L)
  case Nil show ?case by simp
next
  let ?RT = \<open>RenamingTick\<close>
  case (Cons l L)
  show ?case
  proof (cases \<open>L = []\<close>)
    show \<open>L = [] \<Longrightarrow> ?case\<close> by (simp add: comp_def flip: Renaming_comp id_def)
  next
    assume \<open>L \<noteq> []\<close>
    have \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ (rev (l # L)). P m = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ (rev L). P m \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l\<close>
      by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc \<open>L \<noteq> []\<close>)
    also have \<open>\<dots> = ?RT (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ L. P m) rev \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l\<close>
      by (simp only: Cons.hyps)
    also have \<open>\<dots> = ?RT (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ L. P m) rev \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?RT (P l) id\<close> by simp
    also have \<open>\<dots> = Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. Some (rev r @ [s]))
                    (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ L. P m) S (P l)\<close>
      by (subst Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.inj_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_RenamingTick)
        simp_all
    also have \<open>\<dots> = ?RT (P l \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ L. P m) rev\<close>
    proof (subst Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      show \<open>inj_on rev Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.range_tick_join\<close> by simp
    next
      show \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. Some (rev r @ [s])) (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ L. P m) S (P l) =
            Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
            (\<lambda>r s. case Some (r # s) of None \<Rightarrow> None | Some r_s \<Rightarrow> Some (rev r_s))
            (P l) S (MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k S L P)\<close>
        by (subst Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym, simp_all)
          (unfold_locales, blast)
    qed
    also have \<open>P l \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ L. P m = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> m \<in>@ (l # L). P m\<close>
      by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons \<open>L \<noteq> []\<close>)
    finally show ?case .
  qed
qed


text \<open>
This has just been established for \<^term>\<open>rev L\<close>,
which is a particular permutation of the list \<^term>\<open>L\<close>.
It turns out that it actually holds for any permutation.
The rest of this file constitutes the proof.
\<close>


subsubsection \<open>Arbitrary Permutation\<close>

paragraph \<open>Some preliminary results\<close>

lemma permute_list_transpose_eq_list_update :
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
   permute_list (Transposition.transpose i j) xs = xs[i := xs!j, j := xs!i]\<close>
  by (auto simp add: permute_list_def transpose_def intro: nth_equalityI)

lemma inj_on_permute_list_transpose :
  \<open>i < n \<Longrightarrow> j < n \<Longrightarrow> inj_on (permute_list (Transposition.transpose i j)) {xs. n \<le> length xs}\<close>
  by (auto intro!: inj_onI simp add: permute_list_transpose_eq_list_update)
    (metis length_list_update nth_equalityI nth_list_update_eq nth_list_update_neq order_less_le_trans)

lemma rev_permute_list_transpose :
  \<open>i < length L \<Longrightarrow> j < length L \<Longrightarrow>
   rev (permute_list (Transposition.transpose i j) L) =
   permute_list (Transposition.transpose (length L - Suc i) (length L - Suc j)) (rev L)\<close>
  by (simp add: permute_list_transpose_eq_list_update rev_nth rev_update)

lemma permute_list_transpose_rev :
  \<open>i < length L \<Longrightarrow> j < length L \<Longrightarrow>
   permute_list (Transposition.transpose i j) (rev L) =
   rev (permute_list (Transposition.transpose (length L - Suc i) (length L - Suc j)) L)\<close>
  by (simp add: permute_list_transpose_eq_list_update rev_nth rev_update)


lemma tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq :
  \<open>tF t \<Longrightarrow> map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g) t = t\<close>
  and tickFree_mem_T_RenamingTick_iff_mem_T :
  \<open>tF t \<Longrightarrow> t \<in> \<T> (RenamingTick P g) \<longleftrightarrow> t \<in> \<T> P\<close>
  and tickFree_mem_D_RenamingTick_iff_mem_D :
  \<open>tF t \<Longrightarrow> t \<in> \<D> (RenamingTick P g) \<longleftrightarrow> t \<in> \<D> P\<close>
  for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and g :: \<open>'r \<Rightarrow> 'r\<close>
    \<comment> \<open>Necessarily here, antecedents and images for \<^term>\<open>g\<close> share the same type.\<close>
proof -
  show * : \<open>tF t \<Longrightarrow> map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g) t = t\<close> for t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct t) (auto simp add: is_ev_def)
  show \<open>tF t \<Longrightarrow> t \<in> \<T> (RenamingTick P g) \<longleftrightarrow> t \<in> \<T> P\<close>
    by (auto simp add: T_Renaming "*" map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree D_T is_processT7)
  show \<open>tF t \<Longrightarrow> t \<in> \<D> (RenamingTick P g) \<longleftrightarrow> t \<in> \<D> P\<close>
    by (auto simp add: D_Renaming "*" is_processT7)
      (metis "*" front_tickFree_Nil self_append_conv)
qed



paragraph \<open>The proof\<close>

text \<open>
We start by proving that the \<^const>\<open>RenamingTick\<close> of the right-hand side
process \<^term>\<open>Q\<close> by a transposition can be ``taken to the outside''
of the synchronization \<^term>\<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q\<close>.
\<close>

lemma Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_RenamingTick_permute_list_transpose :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t RenamingTick Q (permute_list (Transposition.transpose i j)) =
   RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q) (permute_list (Transposition.transpose (Suc i) (Suc j)))\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>i < n\<close> \<open>j < n\<close> \<open>\<And>rs. rs \<in> \<^bold>\<checkmark>\<^bold>s(Q) \<Longrightarrow> n \<le> length rs\<close>
proof -
  let ?\<tau> = Transposition.transpose
  let ?pl_\<tau> = \<open>\<lambda>i j. permute_list (?\<tau> i j)\<close>
  let ?fun_evt = \<open>\<lambda>i j. map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id (?pl_\<tau> i j)\<close>
  let ?map_evt = \<open>\<lambda>i j. map (?fun_evt i j)\<close>
  let ?RT = \<open>\<lambda>i j P. RenamingTick P (?pl_\<tau> i j)\<close>
  let ?tj = \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close>
  note map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_iffs [simp] =
    ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff
    map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff
  have length_ge_eq_pl_\<tau>_imp_eq : \<open>r = r'\<close>
    if \<open>n \<le> length r\<close> and \<open>?pl_\<tau> i j r = ?pl_\<tau> i j r'\<close> for r r' :: \<open>'r list\<close>
  proof -
    from \<open>n \<le> length r\<close> have \<open>n \<le> length (?pl_\<tau> i j r)\<close> by simp
    with \<open>?pl_\<tau> i j r = ?pl_\<tau> i j r'\<close> have \<open>n \<le> length r'\<close> by simp
    have \<open>inj_on (?pl_\<tau> i j) {r. n \<le> length r}\<close>
      by (simp add: \<open>i < n\<close> \<open>j < n\<close> inj_on_permute_list_transpose)
    with \<open>n \<le> length r\<close> \<open>n \<le> length r'\<close> \<open>?pl_\<tau> i j r = ?pl_\<tau> i j r'\<close>
    show \<open>r = r'\<close> by (auto dest: inj_onD)
  qed
  have pl_\<tau>_pl_\<tau> : \<open>n \<le> length r \<Longrightarrow> ?pl_\<tau> i j (?pl_\<tau> i j r) = r\<close> for r :: \<open>'r list\<close>
    by (subst permute_list_compose[symmetric])
      (metis lessThan_iff order_less_le_trans permutes_swap_id \<open>i < n\<close> \<open>j < n\<close>, simp)
  have fun_evt_fun_evt :
    \<open>(case e of ev a \<Rightarrow> True | \<checkmark>(r) \<Rightarrow> n \<le> length r) \<Longrightarrow> ?fun_evt i j (?fun_evt i j e) = e\<close>
    for e :: \<open>('a, 'r list) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (cases e) (simp_all add: pl_\<tau>_pl_\<tau>)
  have map_evt_map_evt :
    \<open>(\<And>e. e \<in> set t \<Longrightarrow> case e of ev a \<Rightarrow> True | \<checkmark>(r) \<Rightarrow> n \<le> length r)
     \<Longrightarrow> ?map_evt i j (?map_evt i j t) = t\<close> for t :: \<open>('a, 'r list) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct t) (simp_all add: fun_evt_fun_evt)
  from \<open>i < n\<close> \<open>j < n\<close> have pl_\<tau>_Cons :
    \<open>n \<le> length s \<Longrightarrow> ?pl_\<tau> (Suc i) (Suc j) (r # s) = r # ?pl_\<tau> i j s\<close> for r and s :: \<open>'r list\<close>
    by (simp add: list_update_append1 nth_append_left permute_list_transpose_eq_list_update)
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain u v t_P t_Q where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> (?RT i j Q) \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> (?RT i j Q)\<close>
      unfolding Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[THEN iffD1, OF "*"(4, 2)] have \<open>tF t_Q\<close> ..
    with "*"(5) have \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      by (simp add: tickFree_mem_T_RenamingTick_iff_mem_T tickFree_mem_D_RenamingTick_iff_mem_D)
    with "*"(1-4) have \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
      by (auto simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    thus \<open>t \<in> \<D> ?rhs\<close>
      by (meson D_imp_front_tickFree div_butlast_when_non_tickFree_iff
          front_tickFree_iff_tickFree_butlast tickFree_mem_D_RenamingTick_iff_mem_D)
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain t1 t2
      where * : \<open>t = ?map_evt (Suc i) (Suc j) t1 @ t2\<close> \<open>tF t1\<close> \<open>ftF t2\<close> \<open>t1 \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
      by (auto simp add: D_Renaming)
    from "*"(1, 2) have \<open>t = t1 @ t2\<close>
      by (simp add: tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
    from "*"(4) obtain u1 u2 t_P t_Q where ** : \<open>t1 = u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close>
      \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[THEN iffD1, OF "**"(4, 2)] have \<open>tF t_Q\<close> ..
    with "**"(5) have \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> (?RT i j Q) \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> (?RT i j Q)\<close>
      by (simp_all add: tickFree_mem_T_RenamingTick_iff_mem_T tickFree_mem_D_RenamingTick_iff_mem_D)
    with "**"(1-4) "*"(2, 3) \<open>t = t1 @ t2\<close> show \<open>t \<in> \<D> ?lhs\<close>
      by (auto simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro: front_tickFree_append)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain t' where * : \<open>t = ?map_evt (Suc i) (Suc j) t'\<close>
      \<open>(t', ?fun_evt (Suc i) (Suc j) -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
      unfolding Renaming_projs by blast
    from "*"(2) \<open>t \<notin> \<D> ?rhs\<close> have \<open>t' \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
      by (metis (no_types, lifting) "*"(1) D_imp_front_tickFree div_butlast_when_non_tickFree_iff
          front_tickFree_iff_tickFree_butlast map_butlast map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree
          tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq tickFree_mem_D_RenamingTick_iff_mem_D)
    with "*"(2) obtain t_P t_Q X_P X_Q
      where ** : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close>
        \<open>?fun_evt (Suc i) (Suc j) -` X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj X_P S X_Q\<close>
      unfolding Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by force
    from "*"(2) consider \<open>tF t'\<close> | t'' rs where \<open>tF t''\<close> \<open>t' = t'' @ [\<checkmark>(rs)]\<close>
      by (metis (lifting) F_T F_imp_front_tickFree T_nonTickFree_imp_decomp
          butlast_snoc front_tickFree_iff_tickFree_butlast)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>tF t'\<close>
      have \<open>?map_evt (Suc i) (Suc j) t' = t'\<close>
        by (simp add: \<open>tF t'\<close> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
      have \<open>?map_evt i j t_Q = t_Q\<close>
        using "**"(3) \<open>tF t'\<close> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff by blast
      define X_Q' where \<open>X_Q' \<equiv> X_Q \<inter> (range ev \<union> {\<checkmark>(r) |r. n \<le> length r})\<close>
      define X' where \<open>X' \<equiv> X \<inter> (range ev \<union> {\<checkmark>(rs) |rs. Suc n \<le> length rs})\<close>
      have \<open>X_Q' \<subseteq> X_Q\<close> unfolding X_Q'_def by blast
      with "**"(2) is_processT4 have \<open>(t_Q, X_Q') \<in> \<F> Q\<close> by blast
      moreover have \<open>?fun_evt i j -` (?fun_evt i j ` X_Q') = X_Q'\<close>
        by (auto simp add: X_Q'_def)
          (use length_ge_eq_pl_\<tau>_imp_eq in blast)+
      moreover have \<open>?map_evt i j t_Q = t_Q\<close> by fact
      ultimately have \<open>(t_Q, ?fun_evt i j ` X_Q') \<in> \<F> (?RT i j Q)\<close>
        by (auto simp add: F_Renaming)
      moreover have \<open>e \<in> X' \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj X_P S (?fun_evt i j ` X_Q')\<close> for e
        using "**"(4)[THEN set_mp, of \<open>?fun_evt (Suc i) (Suc j) e\<close>]
        unfolding X'_def X_Q'_def super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
        by (auto simp add: image_iff pl_\<tau>_Cons) (use pl_\<tau>_pl_\<tau> in force)
      ultimately have \<open>(t, X') \<in> \<F> ?lhs\<close>
        by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          (metis "*"(1) "**"(1, 3) \<open>?map_evt (Suc i) (Suc j) t' = t'\<close> subsetI)
      moreover have \<open>Suc n \<le> length (rs)\<close> if \<open>t @ [\<checkmark>(rs)] \<in> \<T> ?lhs\<close> for rs
      proof -
        from \<open>t \<notin> \<D> ?lhs\<close> have \<open>t @ [\<checkmark>(rs)] \<notin> \<D> ?lhs\<close>
          by (meson is_processT9)
        with \<open>t @ [\<checkmark>(rs)] \<in> \<T> ?lhs\<close>
        obtain t_P'' t_Q'' where "\<pounds>" : \<open>t_P'' \<in> \<T> P\<close> \<open>t_Q'' \<in> \<T> (?RT i j Q)\<close>
          \<open>t @ [\<checkmark>(rs)] setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. \<lfloor>r # s\<rfloor>\<^esub> ((t_P'', t_Q''), S)\<close>
          unfolding Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
        from "\<pounds>" obtain t_P''' t_Q''' r s
          where "\<pounds>\<pounds>" : \<open>rs = r # s\<close> \<open>t_P'' = t_P''' @ [\<checkmark>(r)]\<close> \<open>t_Q'' = t_Q''' @ [\<checkmark>(s)]\<close>
            \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. \<lfloor>r # s\<rfloor>\<^esub> ((t_P''', t_Q'''), S)\<close>
          by (auto elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
        have \<open>tF t_Q'''\<close> using "\<pounds>"(2) "\<pounds>\<pounds>"(3) append_T_imp_tickFree by blast
        from \<open>t \<notin> \<D> ?lhs\<close> "\<pounds>"(1) "\<pounds>\<pounds>"(2, 4) have \<open>t_Q''' \<notin> \<D> (?RT i j Q)\<close>
          by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
            (use front_tickFree_Nil is_processT3_TR_append in blast)
        with "\<pounds>"(2) obtain t_Q''''
          where \<open>?map_evt i j t_Q'''' = t_Q''' @ [\<checkmark>(s)]\<close> \<open>t_Q'''' \<in> \<T> Q\<close>
          by (simp add: Renaming_projs)
            (metis "\<pounds>\<pounds>"(3) \<open>t_Q''' \<notin> \<D> (?RT i j Q)\<close> is_processT7 is_processT9
              tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq tickFree_mem_D_RenamingTick_iff_mem_D)
        then obtain s' where "\<pounds>\<pounds>\<pounds>" : \<open>s = ?pl_\<tau> i j s'\<close> \<open>t_Q''' @ [\<checkmark>(s')] \<in> \<T> Q\<close>
          by (auto simp add: map_eq_append_conv Cons_eq_map_conv
              append_T_imp_tickFree tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
        have \<open>s' \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
          by (meson "\<pounds>\<pounds>\<pounds>"(2) \<open>tF t_Q'''\<close> \<open>t_Q''' \<notin> \<D> (?RT i j Q)\<close> is_processT9
              strict_ticks_of_memI tickFree_mem_D_RenamingTick_iff_mem_D)
        with \<open>\<And>rs. rs \<in> \<^bold>\<checkmark>\<^bold>s(Q) \<Longrightarrow> n \<le> length rs\<close> have \<open>n \<le> length s'\<close> .
        with \<open>s = ?pl_\<tau> i j s'\<close> have \<open>n \<le> length s\<close> by simp
        with \<open>rs = r # s\<close> show \<open>Suc n \<le> length rs\<close> by simp
      qed
      ultimately have \<open>(t, X' \<union> (X \<inter> {\<checkmark>(rs) |rs. \<not> Suc n \<le> length rs})) \<in> \<F> ?lhs\<close>
        using is_processT5_S7' by blast
      also have \<open>X' \<union> (X \<inter> {\<checkmark>(rs) |rs. \<not> Suc n \<le> length rs}) = X\<close>
        by (simp add: set_eq_iff X'_def image_iff) (meson event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      finally show \<open>(t, X) \<in> \<F> ?lhs\<close> .
    next
      fix t'' rs assume \<open>tF t''\<close> \<open>t' = t'' @ [\<checkmark>(rs)]\<close>
      from "**"(3) obtain t_P' t_Q' r s
        where *** : \<open>r # s = rs\<close>
          \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P', t_Q'), S)\<close>
          \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
        by (auto elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE
            simp add: \<open>t' = t'' @ [\<checkmark>(rs)]\<close> split: if_split_asm)
      have \<open>n \<le> length s\<close>
      proof -
        from "**"(1)[THEN F_T] "**"(3) \<open>t' \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close> have \<open>t_Q \<notin> \<D> Q\<close>
          by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs')
            (use front_tickFree_Nil in blast)
        with \<open>(t_Q, X_Q) \<in> \<F> Q\<close>[THEN F_T] have \<open>s \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
          by (simp add: "***"(4) strict_ticks_of_memI)
        with \<open>\<And>rs. rs \<in> \<^bold>\<checkmark>\<^bold>s(Q) \<Longrightarrow> n \<le> length rs\<close> show \<open>n \<le> length s\<close> .
      qed
      from \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P', t_Q'), S)\<close>
      have \<open>?map_evt (Suc i) (Suc j) t'' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P', ?map_evt i j t_Q'), S)\<close>
        by (metis (no_types, lifting) \<open>tF t''\<close> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq
            tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick
        [OF this, of r \<open>?pl_\<tau> i j s\<close> \<open>?pl_\<tau> (Suc i) (Suc j) rs\<close>] \<open>n \<le> length s\<close>
      have \<open>?map_evt (Suc i) (Suc j) t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, ?map_evt i j t_Q), S)\<close>
        by (simp add: "***"(1, 3, 4) \<open>t' = t'' @ [\<checkmark>(rs)]\<close>) (metis "***"(1) pl_\<tau>_Cons)
      moreover from "**"(2)[THEN F_T] have \<open>(?map_evt i j t_Q, UNIV) \<in> \<F> (?RT i j Q)\<close>
        by (simp add: "***"(4), intro tick_T_F) (auto simp add: T_Renaming)
      moreover have \<open>(t_P, UNIV) \<in> \<F> P\<close>
        by (metis "**"(1) "***"(3) F_T tick_T_F)
      moreover have \<open>e \<in> X \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj UNIV S UNIV\<close> for e
        using "**"(4)[THEN set_mp, of \<open>?fun_evt (Suc i) (Suc j) e\<close>]
        by (cases e) (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
      ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
        using "*"(1) by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    qed
  next    
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> (?RT i j Q)\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj X_P S X_Q\<close>
      unfolding Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by force
    from "*"(1, 3) \<open>t \<notin> \<D> ?lhs\<close> F_T front_tickFree_Nil
    have \<open>t_Q \<notin> \<D> (?RT i j Q)\<close> unfolding Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' by blast
    with "*"(2) obtain t_Q' where ** : \<open>t_Q = ?map_evt i j t_Q'\<close> \<open>(t_Q', ?fun_evt i j -` X_Q) \<in> \<F> Q\<close>
      unfolding Renaming_projs by blast
    define X_Q' where \<open>X_Q' \<equiv> X_Q \<inter> (range ev \<union> {\<checkmark>(rs) |rs. n \<le> length rs})\<close>
    define X' where \<open>X' \<equiv> X \<inter> (range ev \<union> {\<checkmark>(rs) |rs. Suc n \<le> length rs})\<close>

    from \<open>(t, X) \<in> \<F> ?lhs\<close>[THEN F_T] consider \<open>tF t\<close> | t' rs where \<open>tF t'\<close> \<open>t = t' @ [\<checkmark>(rs)]\<close>
      using T_nonTickFree_imp_decomp append_T_imp_tickFree by blast
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      assume \<open>tF t\<close>
      hence \<open>?map_evt (Suc i) (Suc j) t = t\<close>
        by (simp add: tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
      have \<open>?map_evt i j t_Q' = t_Q'\<close>
        using "*"(3) "**"(1) \<open>tF t\<close> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq
          tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff by blast
      have \<open>(t_Q, ?fun_evt i j -` X_Q) \<in> \<F> Q\<close>
        by (simp add: "**"(1, 2) \<open>?map_evt i j t_Q' = t_Q'\<close>)
      hence \<open>(t_Q, ?fun_evt i j -` X_Q') \<in> \<F> Q\<close>
        by (simp add: X_Q'_def is_processT4)
      moreover have \<open>(t_P, X_P) \<in> \<F> P\<close> by (fact "*"(1))
      moreover have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close> by (fact "*"(3))
      moreover have \<open>e \<in> ?fun_evt (Suc i) (Suc j) -` X' \<Longrightarrow>
                     e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj X_P S (?fun_evt i j -` X_Q)\<close> for e
        using set_mp[OF "*"(4), of \<open>?fun_evt (Suc i) (Suc j) e\<close>]
        by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def X'_def pl_\<tau>_Cons)
      ultimately have \<open>(t, ?fun_evt (Suc i) (Suc j) -` X') \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
        by (unfold Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, clarify)
          (metis "**"(1, 2) \<open>?map_evt i j t_Q' = t_Q'\<close> subsetI)
      moreover have \<open>Suc n \<le> length (rs)\<close> if \<open>t @ [\<checkmark>(rs)] \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close> for rs
      proof -
        from \<open>t \<notin> \<D> ?lhs\<close> have \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
          by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            (metis tickFree_mem_D_RenamingTick_iff_mem_D
              tickFree_mem_T_RenamingTick_iff_mem_T tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
        hence \<open>t @ [\<checkmark>(rs)] \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
          by (meson is_processT9)
        with \<open>t @ [\<checkmark>(rs)] \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
        obtain t_P'' t_Q'' where "\<pounds>" : \<open>t_P'' \<in> \<T> P\<close> \<open>t_Q'' \<in> \<T> Q\<close>
          \<open>t @ [\<checkmark>(rs)] setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. \<lfloor>r # s\<rfloor>\<^esub> ((t_P'', t_Q''), S)\<close>
          unfolding Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
        from "\<pounds>" obtain t_P''' t_Q''' r s
          where "\<pounds>\<pounds>" : \<open>rs = r # s\<close> \<open>t_P'' = t_P''' @ [\<checkmark>(r)]\<close> \<open>t_Q'' = t_Q''' @ [\<checkmark>(s)]\<close>
            \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. \<lfloor>r # s\<rfloor>\<^esub> ((t_P''', t_Q'''), S)\<close>
          by (auto elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
        from \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close> have \<open>t_Q'' \<notin> \<D> Q\<close>
          by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
            (metis "\<pounds>"(1) "\<pounds>\<pounds>"(2-4) append.right_neutral
              front_tickFree_Nil is_processT3_TR_append is_processT9)
        have \<open>s \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
          by (metis "\<pounds>"(2) "\<pounds>\<pounds>"(3) \<open>t_Q'' \<notin> \<D> Q\<close> strict_ticks_of_memI)
        with \<open>\<And>rs. rs \<in> \<^bold>\<checkmark>\<^bold>s(Q) \<Longrightarrow> n \<le> length rs\<close> have \<open>n \<le> length s\<close> .
        thus \<open>Suc n \<le> length rs\<close> by (simp add: \<open>rs = r # s\<close>)
      qed
      ultimately have \<open>(t, ?fun_evt (Suc i) (Suc j) -` X' \<union>
                           ?fun_evt (Suc i) (Suc j) -`
                           (X \<inter> {\<checkmark>(rs) |rs. \<not> Suc n \<le> length rs})) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
        using is_processT5_S7' by force
      also have \<open>?fun_evt (Suc i) (Suc j) -` X' \<union>
                 ?fun_evt (Suc i) (Suc j) -` (X \<inter> {\<checkmark>(rs) |rs. \<not> Suc n \<le> length rs}) =
                 ?fun_evt (Suc i) (Suc j) -` X\<close>
        by (auto simp add: X'_def image_iff) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      finally show \<open>(t, X) \<in> \<F> ?rhs\<close>
        using \<open>?map_evt (Suc i) (Suc j) t = t\<close> by (auto simp add: F_Renaming)
    next
      fix t' rs assume \<open>tF t'\<close> \<open>t = t' @ [\<checkmark>(rs)]\<close>
      from "*"(3) obtain t_P'' t_Q'' r s
        where *** : \<open>rs = r # s\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P'', t_Q''), S)\<close>
          \<open>t_P = t_P'' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q'' @ [\<checkmark>(s)]\<close>
          \<open>tF t_P''\<close> \<open>tF t_Q''\<close>
        by (auto elim!: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE
            simp add: \<open>t = t' @ [\<checkmark>(rs)]\<close> split: if_split_asm)
          (metis \<open>tF t'\<close> tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      have \<open>t_Q'' \<notin> \<D> Q\<close>
        by (metis "*"(2) "***"(4) F_imp_front_tickFree \<open>t_Q \<notin> \<D> (?RT i j Q)\<close>
            front_tickFree_append_iff is_processT7 non_tickFree_tick
            tickFree_Nil tickFree_mem_D_RenamingTick_iff_mem_D)
      from "**"(1) "***"(4) obtain s' where \<open>s = ?pl_\<tau> i j s'\<close>
        by (auto simp add: "**"(2) append_eq_map_conv Cons_eq_map_conv)
      with "**"(1) "**"(2)[THEN F_T] "***"(4) have \<open>t_Q'' @ [\<checkmark>(s')] \<in> \<T> Q\<close>
        by (simp add: "***"(4) append_eq_map_conv Cons_eq_map_conv)
          (metis "***"(6) \<open>t_Q'' \<notin> \<D> Q\<close> is_processT9 length_permute_list map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree
            pl_\<tau>_pl_\<tau> strict_ticks_of_memI that(3) tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
      with \<open>t_Q'' \<notin> \<D> Q\<close> have \<open>s' \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
        by (metis is_processT9 strict_ticks_of_memI)
      with \<open>\<And>rs. rs \<in> \<^bold>\<checkmark>\<^bold>s(Q) \<Longrightarrow> n \<le> length rs\<close> have \<open>n \<le> length s'\<close> .
      with \<open>s = ?pl_\<tau> i j s'\<close> have \<open>n \<le> length s\<close> by simp
      hence \<open>Suc n \<le> length rs\<close> by (simp add: \<open>rs = r # s\<close>)

      have \<open>?map_evt (Suc i) (Suc j) t setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, ?map_evt i j t_Q), S)\<close>
        by (simp add: "***"(1-3, 4, 6) \<open>t = t' @ [\<checkmark>(rs)]\<close> \<open>n \<le> length s\<close> \<open>tF t'\<close> pl_\<tau>_Cons
            setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
      moreover have \<open>t_P \<in> \<T> P\<close> using "*"(1) F_T by blast
      moreover from "*"(2)[THEN F_T] \<open>n \<le> length s\<close> have \<open>?map_evt i j t_Q \<in> \<T> Q\<close>
        by (auto simp add: T_Renaming "***"(4, 6) append_eq_map_conv Cons_eq_map_conv
            tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq pl_\<tau>_pl_\<tau>)
          (metis append_T_imp_tickFree not_Cons_self2 tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq,
            metis \<open>t_Q'' \<notin> \<D> Q\<close> is_processT7 is_processT9)
      ultimately have \<open>?map_evt (Suc i) (Suc j) t \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
        by (auto simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      with \<open>n \<le> length s\<close> have \<open>t \<in> \<T> ?rhs\<close>
        by (auto simp add: T_Renaming \<open>t = t' @ [\<checkmark>(rs)]\<close> append_eq_map_conv Cons_eq_map_conv)
          (metis "***"(1) \<open>tF t'\<close> length_permute_list pl_\<tau>_Cons pl_\<tau>_pl_\<tau> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (simp add: \<open>t = t' @ [\<checkmark>(rs)]\<close> tick_T_F)
    qed
  qed
qed



lemma RenamingTick_permute_list_transpose_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L :
  \<open>RenamingTick P (permute_list (Transposition.transpose i j)) \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q =
   RenamingTick (P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q) (permute_list (Transposition.transpose i j))\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>i < n\<close> \<open>j < n\<close> for P :: \<open>('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  let ?pl = \<open>permute_list (Transposition.transpose i j)\<close>
  let ?fun_evt = \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id (permute_list (Transposition.transpose i j))\<close>
  let ?map_evt = \<open>map ?fun_evt\<close>
    and ?RT = \<open>\<lambda>P. RenamingTick P (permute_list (Transposition.transpose i j))\<close>
    and ?tj = \<open>\<lambda>r s. if length r = n then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  note map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_iffs [simp] =
    ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff
  have length_eq_pl_imp : \<open>r = r'\<close> if \<open>n \<le> length r\<close> and \<open>?pl r = ?pl r'\<close> for r r' :: \<open>'r list\<close>
  proof -
    from \<open>n \<le> length r\<close> have \<open>n \<le> length (?pl r)\<close> by simp
    with \<open>?pl r = ?pl r'\<close> have \<open>n \<le> length r'\<close> by simp
    have \<open>inj_on ?pl {r. n \<le> length r}\<close>
      by (simp add: \<open>i < n\<close> \<open>j < n\<close> inj_on_permute_list_transpose)
    with \<open>n \<le> length r\<close> \<open>n \<le> length r'\<close> \<open>?pl r = ?pl r'\<close>
    show \<open>r = r'\<close> by (auto dest: inj_onD)
  qed
  have pl_pl : \<open>n \<le> length r \<Longrightarrow> ?pl (?pl r) = r\<close> for r :: \<open>'r list\<close>
    by (subst permute_list_compose[symmetric])
      (metis lessThan_iff order_less_le_trans permutes_swap_id \<open>i < n\<close> \<open>j < n\<close>, simp)
  have fun_evt_fun_evt :
    \<open>(case e of ev a \<Rightarrow> True | \<checkmark>(r) \<Rightarrow> n \<le> length r) \<Longrightarrow> ?fun_evt (?fun_evt e) = e\<close>
    for e :: \<open>('a, 'r list) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (cases e) (simp_all add: pl_pl)
  have map_evt_map_evt :
    \<open>(\<And>e. e \<in> set t \<Longrightarrow> case e of ev a \<Rightarrow> True | \<checkmark>(r) \<Rightarrow> n \<le> length r)
     \<Longrightarrow> ?map_evt (?map_evt t) = t\<close> for t :: \<open>('a, 'r list) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct t) (simp_all add: fun_evt_fun_evt)
  from \<open>i < n\<close> \<open>j < n\<close> have pl_append :
    \<open>n \<le> length r \<Longrightarrow> ?pl (r @ r') = ?pl r @ r'\<close> for r r' :: \<open>'r list\<close>
    by (simp add: list_update_append1 nth_append_left permute_list_transpose_eq_list_update)

  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain u v t_P t_Q where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D> (?RT P) \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> (?RT P) \<and> t_Q \<in> \<D> Q\<close>
      unfolding Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[THEN iffD1, OF "*"(4, 2)] have \<open>tF t_P\<close> ..
    with "*"(5) have \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      by (simp_all add: tickFree_mem_T_RenamingTick_iff_mem_T tickFree_mem_D_RenamingTick_iff_mem_D)
    with "*"(1-4) have \<open>t \<in> \<D> (P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q)\<close>
      by (auto simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    thus \<open>t \<in> \<D> ?rhs\<close>
      by (meson D_imp_front_tickFree div_butlast_when_non_tickFree_iff
          front_tickFree_iff_tickFree_butlast tickFree_mem_D_RenamingTick_iff_mem_D)
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain t1 t2
      where * : \<open>t = ?map_evt t1 @ t2\<close> \<open>tF t1\<close> \<open>ftF t2\<close> \<open>t1 \<in> \<D> (P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q)\<close>
      by (auto simp add: D_Renaming)
    from "*"(1, 2) have \<open>t = t1 @ t2\<close>
      by (simp add: tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
    from "*"(4) obtain u1 u2 t_P t_Q where ** : \<open>t1 = u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close>
      \<open>u1 setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff[THEN iffD1, OF "**"(4, 2)] have \<open>tF t_P\<close> ..
    with "**"(5) have \<open>t_P \<in> \<D> (?RT P) \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> (?RT P) \<and> t_Q \<in> \<D> Q\<close>
      by (simp_all add: tickFree_mem_T_RenamingTick_iff_mem_T tickFree_mem_D_RenamingTick_iff_mem_D)
    with "**"(1-4) "*"(2, 3) \<open>t = t1 @ t2\<close> show \<open>t \<in> \<D> ?lhs\<close>
      by (auto simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro: front_tickFree_append)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> (?RT P)\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj X_P S X_Q\<close>
      unfolding Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by force
    from "*"(2, 3) \<open>t \<notin> \<D> ?lhs\<close> F_T front_tickFree_Nil
    have \<open>t_P \<notin> \<D> (?RT P)\<close> unfolding Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' by blast
    with "*"(1) obtain t_P' where ** : \<open>t_P = ?map_evt t_P'\<close> \<open>(t_P', ?fun_evt -` X_P) \<in> \<F> P\<close>
      unfolding Renaming_projs by blast
    from \<open>(t, X) \<in> \<F> ?lhs\<close>[THEN F_T] consider \<open>tF t\<close> | t' rs where \<open>tF t'\<close> \<open>t = t' @ [\<checkmark>(rs)]\<close>
      using T_nonTickFree_imp_decomp append_T_imp_tickFree by blast
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      assume \<open>tF t\<close>
      hence \<open>?map_evt t = t\<close>
        by (simp add: tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
      have \<open>?map_evt t_P' = t_P'\<close>
        using "*"(3) "**"(1) \<open>tF t\<close> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq
          tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff by blast
      have \<open>(t_P, ?fun_evt -` X_P) \<in> \<F> P\<close>
        by (simp add: "**"(1,2) \<open>?map_evt t_P' = t_P'\<close>)
      moreover have \<open>(t_Q, X_Q) \<in> \<F> Q\<close> by (fact "*"(2))
      moreover have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close> by (fact "*"(3))
      moreover have \<open>e \<in> ?fun_evt -` X \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj (?fun_evt -` X_P) S X_Q\<close> for e
        using "*"(4)[THEN set_mp, of \<open>?fun_evt e\<close>]
        by (cases e, auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def split: if_split_asm)
          (metis append_eq_append_conv dual_order.refl length_permute_list pl_append,
            metis append_eq_append_conv dual_order.refl length_permute_list pl_append,
            metis dual_order.refl length_permute_list pl_append)
      ultimately have \<open>(t, ?fun_evt -` X) \<in> \<F> (P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q)\<close>
        by (simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
      with \<open>?map_evt t = t\<close> show \<open>(t, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Renaming)
    next
      fix t' rs assume \<open>tF t'\<close> \<open>t = t' @ [\<checkmark>(rs)]\<close>
      from "*"(3) obtain t_P'' t_Q'' r s
        where *** : \<open>length r = n\<close> \<open>r @ s = rs\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P'', t_Q''), S)\<close>
          \<open>t_P = t_P'' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q'' @ [\<checkmark>(s)]\<close>
        by (auto elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE
            simp add: \<open>t = t' @ [\<checkmark>(rs)]\<close> split: if_split_asm)
      have \<open>?pl r @ s = ?pl rs\<close> using "***"(1, 2) pl_append by force
      from \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P'', t_Q''), S)\<close>
      have \<open>?map_evt t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((?map_evt t_P'', t_Q''), S)\<close>
        by (metis (no_types, lifting) \<open>tF t'\<close> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq
            tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      have \<open>case e of ev a \<Rightarrow> True | \<checkmark>(r) \<Rightarrow> n \<le> length r\<close> if \<open>e \<in> set t_P'\<close> for e
      proof -
        have \<open>tF t_P''\<close>
          using "***"(3) \<open>tF t'\<close> tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff by blast
        hence \<open>e \<in> set t_P'' \<Longrightarrow> is_ev e\<close> for e
          by (metis in_set_conv_decomp tickFree_Cons_iff tickFree_append_iff)
        moreover from \<open>e \<in> set t_P'\<close> have \<open>?fun_evt e \<in> set t_P\<close>
          by (simp add: "**"(1))
        ultimately show \<open>case e of ev a \<Rightarrow> True | \<checkmark>(r) \<Rightarrow> n \<le> length r\<close>
          using "***"(1) by (cases e, auto simp add: "***"(4)) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2))
      qed
      with arg_cong[OF "**"(1), where f = ?map_evt] map_evt_map_evt
      have \<open>?map_evt t_P = t_P'\<close> by presburger
      with "**" have \<open>?map_evt t_P \<in> \<T> P\<close> by (simp add: F_T)
      moreover have \<open>t_Q \<in> \<T> Q\<close> using "*"(2) F_T by blast
      moreover from \<open>?map_evt t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((?map_evt t_P'', t_Q''), S)\<close>
      have \<open>?map_evt t setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((?map_evt t_P, t_Q), S)\<close>
        by (simp add: \<open>t = t' @ [\<checkmark>(rs)]\<close> "***"(1, 4, 5)
            \<open>?pl r @ s = ?pl rs\<close> setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick)
      ultimately have \<open>?map_evt t \<in> \<T> (P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q)\<close>
        unfolding Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      hence \<open>?map_evt (?map_evt t) \<in> \<T> ?rhs\<close>
        by (auto simp add: T_Renaming)
      also have \<open>?map_evt (?map_evt t) = t\<close>
        by (simp add: \<open>t = t' @ [\<checkmark>(rs)]\<close> )
          (metis "***"(1, 2) \<open>tF t'\<close> dual_order.refl length_permute_list
            list.map_comp pl_append pl_pl tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
      finally show \<open>(t, X) \<in> \<F> ?rhs\<close> by (simp add: \<open>t = t' @ [\<checkmark>(rs)]\<close> tick_T_F)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain t' where * : \<open>t = ?map_evt t'\<close>
      \<open>(t', ?fun_evt -` X) \<in> \<F> (P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q)\<close>
      unfolding Renaming_projs by blast
    from "*"(2) \<open>t \<notin> \<D> ?rhs\<close> have \<open>t' \<notin> \<D> (P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q)\<close>
      by (metis (no_types, lifting) "*"(1) D_imp_front_tickFree div_butlast_when_non_tickFree_iff
          front_tickFree_iff_tickFree_butlast map_butlast map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree
          tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq tickFree_mem_D_RenamingTick_iff_mem_D)
    with "*"(2) obtain t_P t_Q X_P X_Q
      where ** : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P, t_Q), S)\<close>
        \<open>?fun_evt -` X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj X_P S X_Q\<close>
      unfolding Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by force
    from "*"(2) consider \<open>tF t'\<close> | t'' rs where \<open>tF t''\<close> \<open>t' = t'' @ [\<checkmark>(rs)]\<close>
      by (metis (lifting) F_T F_imp_front_tickFree T_nonTickFree_imp_decomp
          butlast_snoc front_tickFree_iff_tickFree_butlast)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>tF t'\<close>
      have \<open>?map_evt t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((?map_evt t_P, t_Q), S)\<close>
        by (metis (lifting) "**"(3) \<open>tF t'\<close> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq
            tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)

      define X_P' where \<open>X_P' \<equiv> X_P \<inter> (range ev \<union> {\<checkmark>(r) |r. length r = n})\<close>
      define X' where \<open>X' \<equiv> X \<inter> (range ev \<union> {\<checkmark>(rs) |rs. n \<le> length rs})\<close>
      have \<open>X_P' \<subseteq> X_P\<close> unfolding X_P'_def by blast
      with "**"(1) is_processT4 have \<open>(t_P, X_P') \<in> \<F> P\<close> by blast
      moreover have \<open>?fun_evt -` (?fun_evt ` X_P') = X_P'\<close>
        by (auto simp add: X_P'_def) (use length_eq_pl_imp in blast)+
      moreover have \<open>?map_evt t_P = t_P\<close>
        using "**"(3) \<open>tF t'\<close> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff by blast
      ultimately have \<open>(t_P, ?fun_evt ` X_P') \<in> \<F> (?RT P)\<close>
        by (auto simp add: F_Renaming)
      moreover have \<open>e \<in> X' \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj (?fun_evt ` X_P') S X_Q\<close> if \<open>e \<in> X'\<close> for e
        using "**"(4)[THEN set_mp, of \<open>?fun_evt e\<close>] fun_evt_fun_evt[of e]
        unfolding X'_def X_P'_def super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
        by (auto simp add: image_iff pl_append split: if_split_asm)
          (metis (mono_tags, lifting) Int_iff Un_iff length_permute_list mem_Collect_eq,
            blast, metis length_permute_list)
      ultimately have \<open>(t, X') \<in> \<F> ?lhs\<close>
        by (simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          (metis (lifting) "*"(1) "**"(2, 3) \<open>tF t'\<close> subsetI tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq)
      moreover from \<open>t \<notin> \<D> ?lhs\<close> have \<open>t @ [\<checkmark>(rs)] \<in> \<T> ?lhs \<Longrightarrow> n \<le> length (rs)\<close> for rs
        by (auto simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
            elim!: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE split: if_split_asm)
          (metis (no_types, lifting) append.assoc butlast_snoc front_tickFree_charn 
            non_tickFree_tick tickFree_Nil tickFree_append_iff tickFree_imp_front_tickFree)+
      ultimately have \<open>(t, X' \<union> (X \<inter> {\<checkmark>(rs) |rs. \<not> n \<le> length rs})) \<in> \<F> ?lhs\<close>
        using is_processT5_S7' by fastforce
      also have \<open>X' \<union> (X \<inter> {\<checkmark>(rs) |rs. \<not> n \<le> length rs}) = X\<close>
        by (simp add: set_eq_iff X'_def image_iff) (meson event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      finally show \<open>(t, X) \<in> \<F> ?lhs\<close> .
    next
      fix t'' rs assume \<open>tF t''\<close> \<open>t' = t'' @ [\<checkmark>(rs)]\<close>
      from "**"(3) obtain t_P' t_Q' r s
        where *** : \<open>length r = n\<close> \<open>r @ s = rs\<close>
          \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P', t_Q'), S)\<close>
          \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
        by (auto elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE
            simp add: \<open>t' = t'' @ [\<checkmark>(rs)]\<close> split: if_split_asm)
      have \<open>?pl r @ s = ?pl rs\<close>
        using "***"(1, 2) pl_append by force
      from \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((t_P', t_Q'), S)\<close>
      have \<open>?map_evt t'' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((?map_evt t_P', t_Q'), S)\<close>
        by (metis (no_types, lifting) \<open>tF t''\<close> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_id_eq
            tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick[OF this, of \<open>?pl r\<close> s \<open>?pl rs\<close>]
      have \<open>?map_evt t' setinterleaves\<^sub>\<checkmark>\<^bsub>?tj\<^esub> ((?map_evt t_P, t_Q), S)\<close>
        by (simp add: "***"(1, 4, 5) \<open>t' = t'' @ [\<checkmark>(rs)]\<close> \<open>?pl r @ s = ?pl rs\<close>)
      moreover from "**"(1)[THEN F_T] have \<open>(?map_evt t_P, UNIV) \<in> \<F> (?RT P)\<close>
        by (simp add: "***"(4), intro tick_T_F) (auto simp add: T_Renaming)
      moreover have \<open>(t_Q, UNIV) \<in> \<F> Q\<close>
        by (metis "**"(2) "***"(5) F_T tick_T_F)
      moreover have \<open>e \<in> X \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj UNIV S UNIV\<close> for e
        using "**"(4)[THEN set_mp, of \<open>?fun_evt e\<close>]
        by (cases e) (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
      ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
        using "*"(1) by (simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    qed
  qed
qed




text \<open>Then, we establish the result when the permutation is only a transposition.\<close>

lemma MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_permute_list_transpose :
  \<open>i < length L \<Longrightarrow> j < length L \<Longrightarrow>
   \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ permute_list (Transposition.transpose i j) L. P l =
   RenamingTick (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) (permute_list (Transposition.transpose i j))\<close>
  for L :: \<open>'b list\<close>
proof -
  let ?RT = RenamingTick and ?MS = \<open>\<lambda>L. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l\<close>
  let ?RS = \<open>\<lambda>L. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l\<close>
  let ?\<tau> = \<open>Transposition.transpose\<close>
  let ?pl_\<tau> = \<open>\<lambda>i j. permute_list (?\<tau> i j)\<close>
  have custom_nat_induct [case_names 0 1 2 Suc] :
    \<open>thesis 0 \<Longrightarrow> thesis 1 \<Longrightarrow> thesis 2 \<Longrightarrow>
     (\<And>n. 2 \<le> n \<Longrightarrow> (\<And>k. k \<le> n \<Longrightarrow> thesis k) \<Longrightarrow> thesis (Suc n)) \<Longrightarrow> thesis n\<close> for thesis n
    by (metis One_nat_def Suc_1 less_2_cases linorder_not_le strong_nat_induct)
  have * : \<open>i \<le> j \<Longrightarrow> i < length L \<Longrightarrow> j < length L \<Longrightarrow>
            ?RS (?pl_\<tau> i j L) = ?RT (?RS L) (?pl_\<tau> i j)\<close> for i j
  proof (induct \<open>length L\<close> arbitrary: i j L rule: custom_nat_induct)
    case 0 thus ?case by simp
  next
    case 1 thus ?case by (cases L) simp_all
  next
    case 2
    from "2.hyps" "2.prems"(1, 3) consider \<open>i = j\<close> | \<open>i = 0\<close> \<open>j = 1\<close> by linarith
    thus ?case
    proof cases
      show \<open>i = j \<Longrightarrow> ?case\<close> by simp
    next
      let ?g = \<open>\<lambda>rs. if rs = [] then [] else last rs # butlast rs\<close>
      assume \<open>i = 0\<close> \<open>j = 1\<close>
      moreover obtain l1 l2 where \<open>L = [l1, l2]\<close>
        by (metis "2.hyps" One_nat_def Suc_1 diff_Suc_1' length_tl lessI
            list.exhaust_sel nat_less_le order.refl take0 take_all_iff)
      ultimately have \<open>?MS (?pl_\<tau> i j L) = P l2 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?RT (P l1) (\<lambda>r. [r])\<close>
        by (simp add: permute_list_transpose_eq_list_update)
      also have \<open>\<dots> = ?RT (?RT (P l1) (\<lambda>r. [r]) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l2) ?g\<close>
        by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)
      also have \<open>... = ?RT (?MS L) ?g\<close>
        by (simp add: \<open>L = [l1, l2]\<close> MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc[of _ \<open>[l1]\<close>, simplified])
      also have \<open>\<dots> = ?RT (?MS L) (?pl_\<tau> i j)\<close>
      proof (rule RenamingTick_is_restrictable_on_strict_ticks_of)
        fix rs assume \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(?MS L)\<close>
        from is_ticks_lengthD is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k this
        have \<open>length rs = length L\<close> .
        thus \<open>?g rs = ?pl_\<tau> i j rs\<close>
          by (cases rs; cases \<open>tl rs\<close>)
            (simp_all add: \<open>L = [l1, l2]\<close> \<open>i = 0\<close> \<open>j = 1\<close>
              permute_list_transpose_eq_list_update)
      qed
      finally show ?case .
    qed
  next
    case (Suc n)
    show ?case
    proof (cases \<open>i = j\<close>)
      show \<open>i = j \<Longrightarrow> ?case\<close>
        by simp (metis RenamingTick_id eq_id_iff permute_list_id)
    next
      assume \<open>i \<noteq> j\<close> hence \<open>i < j\<close>
        by (simp add: Suc.prems(1) nat_less_le)

      { fix i j L l0 l1 and L' :: \<open>'b list\<close>
        assume \<open>i \<noteq> 0\<close> \<open>i < j\<close> \<open>i < length L\<close> \<open>j < length L\<close> \<open>Suc n = length L\<close> \<open>L = l0 # l1 # L'\<close>
        with \<open>i < length L\<close> \<open>j < length L\<close> \<open>i < j\<close> \<open>i \<noteq> 0\<close>
        have * : \<open>i - 1 < j - 1\<close> \<open>i - 1 < length (l1 # L')\<close>
          \<open>j - 1 < length (l1 # L')\<close> by auto
        have \<open>?pl_\<tau> i j L = l0 # ?pl_\<tau> (i - 1) (j - 1) (l1 # L')\<close>
        proof (subst (1 2) permute_list_transpose_eq_list_update)
          show \<open>i - 1 < length (l1 # L')\<close> \<open>j - 1 < length (l1 # L')\<close>
            \<open>i < length L\<close> \<open>j < length L\<close>
            by (fact "*"(2, 3) \<open>i < length L\<close> \<open>j < length L\<close>)+
        next
          from "*" \<open>i \<noteq> 0\<close>
          show \<open>L[i := L ! j, j := L ! i] =
                l0 # (l1 # L')[i - 1 := (l1 # L') ! (j - 1), j - 1 := (l1 # L') ! (i - 1)]\<close>
            by (cases i; cases j) (simp_all add: \<open>L = l0 # l1 # L'\<close> nat.case_eq_if)
        qed
        hence \<open>?MS (?pl_\<tau> i j L) = P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?MS (?pl_\<tau> (i - 1) (j - 1) (l1 # L'))\<close>
          by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons)
            (metis Zero_not_Suc length_Cons length_permute_list list.size(3))
        also have \<open>?MS (?pl_\<tau> (i - 1) (j - 1) (l1 # L')) =
                   ?RT (?MS (l1 # L')) (?pl_\<tau> (i - 1) (j - 1))\<close>
          by (subst "Suc.hyps") 
            (use "*" \<open>Suc n = length L\<close> \<open>L = l0 # l1 # L'\<close> in simp_all)
        also have \<open>P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?RT (?MS (l1 # L')) (?pl_\<tau> (i - 1) (j - 1)) =
                 ?RT (P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?MS (l1 # L')) (?pl_\<tau> (Suc (i - 1)) (Suc (j - 1)))\<close>
          by (rule Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_RenamingTick_permute_list_transpose[OF "*"(2, 3)])
            (metis is_ticks_lengthD is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k order_le_less)
        also have \<open>(Suc (i - 1)) = i\<close> using \<open>i \<noteq> 0\<close> by simp
        also have \<open>(Suc (j - 1)) = j\<close> using "*"(1) by linarith
        also have \<open>P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?MS (l1 # L') = ?MS L\<close>
          by (simp add: \<open>L = l0 # l1 # L'\<close>)
        finally have \<open>?MS (?pl_\<tau> i j L) = ?RT (?MS L) (?pl_\<tau> i j)\<close> .
      } note \<pounds> = this

      consider \<open>i \<noteq> 0\<close> | \<open>j \<noteq> n\<close> | \<open>i = 0\<close> \<open>j = n\<close> by argo
      thus ?case
      proof cases
        assume \<open>i \<noteq> 0\<close>
        from Suc.hyps(1, 3) obtain l0 l1 L' where \<open>L = l0 # l1 # L'\<close>
          by (cases L; cases \<open>tl L\<close>) simp_all
        from "\<pounds>" \<open>i \<noteq> 0\<close> \<open>i < j\<close> Suc.prems(2, 3) Suc.hyps(3) this show ?case .
      next
        assume \<open>j \<noteq> n\<close>
        from Suc.hyps(1, 3) obtain l0 l1 L' where \<open>L = L' @ [l1] @ [l0]\<close>
          by (cases L rule: rev_cases; cases \<open>butlast L\<close> rule: rev_cases) simp_all
        hence \<open>rev L = l0 # l1 # rev L'\<close> by simp
        have \<open>Suc n = length (rev L)\<close> by (simp add: Suc.hyps(3))

        have \<open>?MS (?pl_\<tau> i j L) = ?MS (rev (?pl_\<tau> (length L - Suc i) (length L - Suc j) (rev L)))\<close>
          by (subst rev_rev_ident[of L, symmetric], subst permute_list_transpose_rev)
            (simp_all add: Suc.prems(2, 3))
        also have \<open>\<dots> = ?RT (?MS (?pl_\<tau> (length L - Suc i) (length L - Suc j) (rev L))) rev\<close>
          by (fact MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev)
        also have \<open>?pl_\<tau> (length L - Suc i) (length L - Suc j) =
                   ?pl_\<tau> (length L - Suc j) (length L - Suc i)\<close>
          by (simp add: transpose_commute)
        also have \<open>?MS (?pl_\<tau> (length L - Suc j) (length L - Suc i) (rev L)) =
                   ?RT (?MS (rev L)) (?pl_\<tau> (length L - Suc j) (length L - Suc i))\<close>
          by (rule "\<pounds>") (use Suc.hyps(3) Suc.prems(3) \<open>j \<noteq> n\<close> \<open>i < j\<close>
              \<open>rev L = l0 # l1 # rev L'\<close> in auto)
        also have \<open>?MS (rev L) = ?RT (?MS L) rev\<close>
          by (fact MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev)
        also have \<open>?RT (?RT (?RT (?MS L) rev) (?pl_\<tau> (length L - Suc j) (length L - Suc i))) rev =
                   ?RT (?MS L) (rev \<circ> (?pl_\<tau> (length L - Suc j) (length L - Suc i)) \<circ> rev)\<close>
          by (simp add: RenamingTick_comp)
        also have \<open>\<dots> = ?RT (?MS L) (?pl_\<tau> j i)\<close>
        proof (rule RenamingTick_is_restrictable_on_strict_ticks_of)
          fix rs assume \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(?MS L)\<close>
          hence \<open>length rs = length L\<close>
            using is_ticks_lengthD is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
          thus \<open>(rev \<circ> (?pl_\<tau> (length L - Suc j) (length L - Suc i)) \<circ> rev) rs = ?pl_\<tau> j i rs\<close>
            by (unfold comp_def, subst rev_permute_list_transpose)
              (use Suc.prems(2, 3) in auto)
        qed
        also have \<open>\<dots> = ?RT (?MS L) (?pl_\<tau> i j)\<close>
          by (simp add: transpose_commute)
        finally show ?case .
      next
        let ?g1 = \<open>\<lambda>rs. if rs = [] then [] else last rs # butlast rs\<close>
        let ?g2 = \<open>\<lambda>rs. drop (Suc (Suc 0)) rs @ take (Suc (Suc 0)) rs\<close>
        let ?g3 = \<open>\<lambda>rs. case rs of r # s \<Rightarrow> r # (if s = [] then [] else last s # butlast s)\<close>
        let ?tj = \<open>\<lambda>r s. \<lfloor>id r # (if s = [] then [] else last s # butlast s)\<rfloor>\<close>
        assume \<open>i = 0\<close> \<open>j = n\<close>
        from Suc.hyps(1, 3) obtain l0 l1 L'
          where \<open>L = l0 # L' @ [l1]\<close> \<open>L' \<noteq> []\<close>
          by (cases L; cases \<open>tl L\<close> rule: rev_cases; force)
        have \<open>?pl_\<tau> i j L = l1 # L' @ [l0]\<close>
          by (subst permute_list_transpose_eq_list_update)
            (use Suc.prems(3) Suc.hyps(3) \<open>L = l0 # L' @ [l1]\<close>
              in \<open>auto simp add: \<open>i = 0\<close> \<open>j = n\<close>\<close>)
        hence \<open>?MS (?pl_\<tau> i j L) = P l1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (?MS L' \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l0)\<close>
          by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc \<open>L' \<noteq> []\<close>)
        also have \<open>\<dots> = ?RT (?MS L' \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1) ?g1\<close>
          by (simp only: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)
        also have \<open>?MS L' \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1 =
                   (?MS L' \<^bsub>Suc (Suc 0)\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R (P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1))\<close>
          by (simp only: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_assoc)
        also have \<open>\<dots> = ?RT (P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1 \<^bsub>Suc (Suc 0)\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L ?MS L') ?g2\<close>
          by (simp only: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)
        also have \<open>P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1 \<^bsub>Suc (Suc 0)\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L ?MS L' =
                   P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (P l1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?MS L')\<close>
          by (simp only: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_assoc)
        also have \<open>\<dots> = P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?RT (?MS L' \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1) ?g1\<close>
          by (simp only: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)
        also have \<open>\<dots> = ?RT (P l0) id \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?RT (?MS L' \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1) ?g1\<close> by simp
        also have \<open>\<dots> = Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj (P l0) S (?MS L' \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1)\<close>
        proof (rule Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.inj_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_RenamingTick)
          show \<open>inj id\<close> \<open>inj (\<lambda>rs. if rs = [] then [] else last rs # butlast rs)\<close>
            by (auto intro!: injI split: if_split_asm)
              (metis append_butlast_last_id)
        qed
        also have \<open>\<dots> = ?RT (P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (?MS L' \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1)) ?g3\<close>
          by (subst Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            (auto intro!: inj_onI split: if_split_asm, metis append_butlast_last_id)
        also have \<open>P l0 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (?MS L' \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P l1) = ?MS L\<close>
          by (simp add: \<open>L = l0 # L' @ [l1]\<close> MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc \<open>L' \<noteq> []\<close>)
        also have \<open>?RT (?RT (?RT (?MS L) ?g3) ?g2) ?g1 = ?RT (?MS L) (?g1 \<circ> ?g2 \<circ> ?g3)\<close>
          by (simp only: RenamingTick_comp)
        also have \<open>\<dots> = ?RT (?MS L) (?pl_\<tau> i j)\<close>
        proof (rule RenamingTick_is_restrictable_on_strict_ticks_of)
          fix rs assume \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(?MS L)\<close>
          hence \<open>length rs = length L\<close>
            using is_ticks_lengthD is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
          obtain n' where \<open>n = Suc (Suc n')\<close>
            by (metis One_nat_def Suc.hyps(1) Suc_1 Suc_n_not_le_n \<open>i = 0\<close> \<open>i \<noteq> j\<close> \<open>j = n\<close> nat.exhaust_sel)
          with Suc.hyps(1, 3) \<open>length rs = length L\<close>
          obtain r0 r1 r2 rs' where \<open>rs = r0 # r1 # r2 # rs'\<close> \<open>n' = length rs'\<close>
            by (cases rs; cases \<open>tl rs\<close>; cases \<open>tl (tl rs)\<close>) simp_all
          show \<open>(?g1 \<circ> ?g2 \<circ> ?g3) rs = ?pl_\<tau> i j rs\<close>
          proof (subst permute_list_transpose_eq_list_update)
            show \<open>i < length rs\<close> \<open>j < length rs\<close>
              by (simp_all add: Suc.prems(2, 3) \<open>length rs = length L\<close>)
          next
            show \<open>(?g1 \<circ> ?g2 \<circ> ?g3) rs = rs[i := rs ! j, j := rs ! i]\<close>
              by (simp add: \<open>i = 0\<close> \<open>j = n\<close> \<open>rs = r0 # r1 # r2 # rs'\<close> \<open>n' = length rs'\<close>
                  \<open>n = Suc (Suc n')\<close> butlast_append nat.case_eq_if)
                (metis One_nat_def append_butlast_last_id diff_Suc_1' last_conv_nth
                  length_0_conv length_butlast list_update_length nat.collapse)
          qed
        qed
        finally show ?case .
      qed
    qed
  qed

  consider \<open>i \<le> j\<close> | \<open>j \<le> i\<close> by linarith
  thus \<open>?RS (?pl_\<tau> i j L) = ?RT (?RS L) (?pl_\<tau> i j)\<close> if \<open>i < length L\<close> \<open>j < length L\<close>
  proof cases
    from that show \<open>i \<le> j \<Longrightarrow> ?RS (?pl_\<tau> i j L) = ?RT (?RS L) (?pl_\<tau> i j)\<close> by (fact "*")
  next
    from that show \<open>j \<le> i \<Longrightarrow> ?RS (?pl_\<tau> i j L) = ?RT (?RS L) (?pl_\<tau> i j)\<close>
      by (subst (1 2) transpose_commute) (rule "*")
  qed
qed


text \<open>
Finally, the proof of the general version relies on the fact that
a permutation can be written as finite product of transpositions.
\<close>


theorem MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_permute_list :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ permute_list f L. P l =
   RenamingTick (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) (permute_list f)\<close>
  if f_permutes : \<open>f permutes {..<length L}\<close>
  using finite_lessThan f_permutes
proof (induct f rule: permutes_rev_induct)
  case id show ?case by (simp flip: id_def)
next
  let ?RT = RenamingTick and ?pl = permute_list and ?\<tau> = Transposition.transpose
  case (swap i j f)  
  have \<open>?\<tau> i j permutes {..<length L}\<close>
    by (meson permutes_swap_id swap.hyps(1, 2))
  hence \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ ?pl (f \<circ> ?\<tau> i j) L. P l =
         \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (?pl (?\<tau> i j) (?pl f L)). P l\<close>
    by (simp add: permute_list_compose)

  also have \<open>\<dots> = ?RT (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ (?pl f L). P l) (?pl (?\<tau> i j))\<close>
    by (metis MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_permute_list_transpose atLeast0LessThan
        atLeastLessThan_iff length_permute_list swap.hyps(1,2))
  also have \<open>\<dots> = ?RT (?RT (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) (?pl f)) (?pl (?\<tau> i j))\<close>
    unfolding swap.hyps(4) ..
  also have \<open>\<dots> = ?RT (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) (?pl (?\<tau> i j) \<circ> ?pl f)\<close>
    by (simp flip: Renaming_comp)
  also have \<open>\<dots> = ?RT (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l) (?pl (f \<circ> (?\<tau> i j)))\<close>
  proof (rule RenamingTick_is_restrictable_on_strict_ticks_of)
    fix rs assume \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l)\<close>
    from is_ticks_lengthD is_ticks_length_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k this
    have \<open>length rs = length L\<close> .
    with \<open>?\<tau> i j permutes {..<length L}\<close>
    show \<open>(?pl (?\<tau> i j) \<circ> ?pl f) rs = ?pl (f \<circ> ?\<tau> i j) rs\<close>
      by (simp add: permute_list_compose)
  qed
  finally show ?case .
qed



(*<*)
end
  (*>*)