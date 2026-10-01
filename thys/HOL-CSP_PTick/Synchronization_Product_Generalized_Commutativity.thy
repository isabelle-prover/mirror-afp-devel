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


chapter \<open>Commutativity and Associativity of Synchronization\<close>

section \<open>Commutativity\<close>

(*<*)
theory Synchronization_Product_Generalized_Commutativity
  imports CSP_PTick_Renaming
begin
  (*>*)

subsection \<open>Motivation\<close>

text (in Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<open>
The classical synchronization product is commutative: @{thm Sync_commute[of P A Q]}
but in our generalization such a law cannot be obtained in all generality.
Imagine for example that the \<^term>\<open>tj\<close> parameter is actually \<^term>\<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close>:
we easily figure out that in this case the corresponding law should
be something like \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q = TickSwap (Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P)\<close>.
More generally, in the \<^theory_text>\<open>locale\<close>, when writing \<^term>\<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q\<close>,
\<^term>\<open>P\<close> is of type \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> while \<^term>\<open>Q\<close> is of type \<^typ>\<open>('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
so we want to find an abstract setup in which we can establish a quasi-commutativity.
This is done in the next subsection.
\<close>


subsection \<open>Formalization\<close>

locale Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm =
  Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>(\<otimes>\<checkmark>)\<close> for tj :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close> (infixl \<open>\<otimes>\<checkmark>\<close> 100) +
fixes tj_dual      :: \<open>'s \<Rightarrow> 'r \<Rightarrow> 'u option\<close> (infixl \<open>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<close> 100)
  and tj_conv      :: \<open>'t \<Rightarrow> 'u\<close> (\<open>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<close>)
  and tj_dual_conv :: \<open>'u \<Rightarrow> 't\<close> (\<open>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark>\<close>)
assumes tj_None_iff :
  \<open>r \<otimes>\<checkmark> s = \<diamond> \<longleftrightarrow> s \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r = \<diamond>\<close>
  and tj_Some_imp :
  \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<Longrightarrow> s \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r = \<lfloor>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r_s\<rfloor>\<close>
  and tj_dual_Some_imp :
  \<open>s \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r = \<lfloor>s_r\<rfloor> \<Longrightarrow> r \<otimes>\<checkmark> s = \<lfloor>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark> s_r\<rfloor>\<close>
begin


text \<open>There is an obvious symmetry over the variables.\<close>

sublocale Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual :
  Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm \<open>(\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l)\<close> \<open>(\<otimes>\<checkmark>)\<close> \<open>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark>\<close> \<open>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<close>
proof unfold_locales
  show \<open>s \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r = \<lfloor>s_r\<rfloor> \<Longrightarrow> s' \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r' = \<lfloor>s_r\<rfloor>
        \<Longrightarrow> s' = s \<and> r' = r\<close> for s r s_r s' r'
    using inj_tj tj_dual_Some_imp by blast
next
  show \<open>s \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r = \<diamond> \<longleftrightarrow> r \<otimes>\<checkmark> s = \<diamond>\<close> for s r
    by (simp add: tj_None_iff)
next
  show \<open>s \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r = \<lfloor>s_r\<rfloor> \<Longrightarrow> r \<otimes>\<checkmark> s = \<lfloor>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark> s_r\<rfloor>\<close> for s r s_r
    by (simp add: tj_dual_Some_imp)
next
  show \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<Longrightarrow> s \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r = \<lfloor>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r_s\<rfloor>\<close> for r s r_s
    by (simp add: tj_Some_imp)
qed


notation Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l _)\<close> [70, 0, 71] 70)
notation Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ |||\<^sub>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l _)\<close> [72, 73] 72)
notation Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ ||\<^sub>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l _)\<close> [74, 75] 74)



subsection \<open>First Properties\<close>

lemma tj_conv_image_range_tj :
  \<open>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l ` range_tj = Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.range_tj\<close>
  by (simp add: set_eq_iff flip: setcompr_eq_image)
    (metis option.inject tj_Some_imp tj_dual_Some_imp)

lemma tj_dual_conv_comp_tj_conv [simp] :
  \<open>r_s \<in> range_tj \<Longrightarrow> \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark> (\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r_s) = r_s\<close>
  using tj_Some_imp tj_dual_Some_imp by fastforce

lemma inj_on_tj_conv : \<open>inj_on \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l range_tj\<close>
  by (rule inj_onI, simp)
    (metis option.inject tj_Some_imp tj_dual_Some_imp)

lemma bij_betw_tj_conv :
  \<open>bij_betw \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l range_tj Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.range_tj\<close>
proof (rule bij_betw_imageI)
  show \<open>inj_on \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l range_tj\<close>
    by (fact inj_on_tj_conv)
next
  show \<open>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l ` range_tj = Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.range_tj\<close>
    using tj_conv_image_range_tj by blast
qed



lemma map_tj_dual_conv_map_tj_conv :
  \<open>{r_s. \<checkmark>(r_s) \<in> set t} \<subseteq> range_tj \<Longrightarrow>
   map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark>) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l) t) = t\<close>
proof (induct t)
  case Nil show ?case by simp
next
  let ?f1 = \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<close>
  let ?f2 = \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark>\<close>
  case (Cons e t)
  have \<open>map ?f2 (map ?f1 (e # t)) = ?f2 (?f1 e) # map ?f2 (map ?f1 t)\<close> by simp
  also have \<open>?f2 (?f1 e) = e\<close>
  proof (cases e)
    show \<open>e = ev a \<Longrightarrow> ?f2 (?f1 e) = e\<close> for a by simp
  next
    fix r_s assume \<open>e = \<checkmark>(r_s)\<close>
    with Cons.prems have \<open>r_s \<in> range_tj\<close> by auto
    with \<open>e = \<checkmark>(r_s)\<close> inj_on_tj_conv
    show \<open>?f2 (?f1 e) = e\<close> by simp
  qed
  also have \<open>map ?f2 (map ?f1 t) = t\<close>
    by (rule Cons.hyps) (use Cons.prems in auto)
  finally show \<open>map ?f2 (map ?f1 (e # t)) = e # t\<close> .
qed

end



subsection \<open>Commutativity\<close>

context Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm begin

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v), A) \<Longrightarrow>
   map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l) t
   setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l)\<^esub> ((v, u), A)\<close>
  \<comment> \<open>Finally not used, and probably obtainable as a corollary of
      @{thm inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_tj_conv, of t u A v]}\<close>
proof (induct \<open>((\<otimes>\<checkmark>), u, A, v)\<close> arbitrary: t u v)
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems
  obtain r_s t'
    where * : \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v), A)\<close>
    by (auto split: option.split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF "*"(1), OF "*"(3)]
  have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l) t'
        setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l)\<^esub> ((v, u), A)\<close> .
  moreover from tj_Some_imp[OF "*"(1)]
  have \<open>s \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r = \<lfloor>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r_s\<rfloor>\<close> .
  ultimately show \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l) t
                   setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l)\<^esub> ((\<checkmark>(s) # v, \<checkmark>(r) # u), A)\<close>
    by (simp add: "*"(1, 2))
qed auto

lemma vimage_tj_dual_conv_subset_super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff :
  \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark> -` X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l) X_Q A X_P
   \<longleftrightarrow> X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q\<close>
  (is \<open>?lhs1 \<subseteq> ?lhs2 \<longleftrightarrow> X \<subseteq> ?rhs\<close>)
  \<comment> \<open>Same: finally not used, and probably obtainable as a corollary of
      @{thm Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.vimage_inj_on_subset_super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff
            [OF Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.inj_on_tj_conv]}.\<close>
proof -
  have * : \<open>(\<lambda>r s. case r \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark> r_s\<rfloor>) =
            (\<lambda>s r. r \<otimes>\<checkmark> s)\<close>
    by (intro ext, simp split: option.split)
      (metis tj_None_iff tj_dual_Some_imp)
  show ?thesis
  proof (subst Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.vimage_inj_on_subset_super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    show \<open>inj_on \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark> Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.range_tj\<close>
      by (fact Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.inj_on_tj_conv)
  next
    show \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
               (\<lambda>r s. case r \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l\<Rightarrow>\<otimes>\<checkmark> r_s\<rfloor>) X_Q A X_P
          \<longleftrightarrow> X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q\<close>
      using super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual by (simp add: "*") blast
  qed
qed



text \<open>
In the end, the proof is quite simple: mainly a corollary
of @{thm inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[no_vars]}.
\<close>

theorem Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute :
  \<open>RenamingTick (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l = Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l P\<close>
proof -
  from inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_tj_conv]
  have \<open>RenamingTick (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l =
        Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        (\<lambda>r s. case r \<otimes>\<checkmark> s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r_s\<rfloor>) P A Q\<close>
    (is \<open>_ = Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tj' P A Q\<close>) .
  also have \<open>?tj' = (\<lambda>r s. s \<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l r)\<close>
    by (intro ext)
      (simp add: Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.tj_dual_Some_imp
        tj_None_iff split: option.split)
  finally show \<open>RenamingTick (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l = Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>d\<^sub>u\<^sub>a\<^sub>l P\<close>
    by (metis Synchro\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_dual.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_dual)
qed


end


(*<*)
end
  (*>*)