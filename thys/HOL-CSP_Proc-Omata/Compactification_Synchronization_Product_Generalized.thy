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


chapter \<open>Compactification of Synchronization Product Generalized\<close>

(*<*)
theory Compactification_Synchronization_Product_Generalized
  imports Compactification_Synchronization_Product
    Combining_Synchronization_Product_Generalized
begin
  (*>*)


section \<open>Iterated Combine\<close>

subsection \<open>Definitions\<close>

fun iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>'e set \<Rightarrow> ('\<sigma>, 'e, 'r) A\<^sub>d list \<Rightarrow> ('\<sigma> list, 'e, 'r list) A\<^sub>d\<close> (\<open>\<llangle>\<^sub>d\<Otimes>\<lbrakk>_\<rbrakk>\<^sub>\<checkmark> _\<rrangle>\<close> [0, 0])
  where \<open>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> []\<rrangle> = \<lparr>\<tau> = \<lambda>\<sigma>s a. \<diamond>, \<omega> = \<lambda>\<sigma>s. \<diamond>\<rparr>\<close>
  |     \<open>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> [A\<^sub>0]\<rrangle> = \<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<close>
  |     \<open>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A\<^sub>0 # A\<^sub>1 # As\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle>\<rrangle>\<close>

fun iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>'e set \<Rightarrow> ('\<sigma>, 'e, 'r) A\<^sub>n\<^sub>d list \<Rightarrow> ('\<sigma> list, 'e, 'r list) A\<^sub>n\<^sub>d\<close> (\<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>_\<rbrakk>\<^sub>\<checkmark> _\<rrangle>\<close> [0, 0])
  where \<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> []\<rrangle> = \<lparr>\<tau> = \<lambda>\<sigma>s a. {}, \<omega> = \<lambda>\<sigma>s. {}\<rparr>\<close>
  |     \<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> [A\<^sub>0]\<rrangle> = \<^sub>n\<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<close>
  |     \<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A\<^sub>0 # A\<^sub>1 # As\<rrangle> = \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle>\<rrangle>\<close>


lemma iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps_bis: \<open>As \<noteq> [] \<Longrightarrow> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A\<^sub>0 # As\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<close>
  and iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps_bis: \<open>Bs \<noteq> [] \<Longrightarrow> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> B\<^sub>0 # Bs\<rrangle> = \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> Bs\<rrangle>\<rrangle>\<close>
  by (induct As, simp_all) (induct Bs, simp_all)



subsection \<open>First Results\<close>

lemma \<tau>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle> = \<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<close> \<open>\<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> Bs\<rrangle> = \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> Bs\<rrangle>\<close>
  by (intro ext, induct rule: induct_list012;
      simp add: \<sigma>_\<sigma>s_conv_defs singl_list_conv_defs
      combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<epsilon>_simps)+

corollary \<epsilon>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle> \<sigma>s = \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> Bs\<rrangle> \<sigma>s = \<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> Bs\<rrangle> \<sigma>s\<close>
  by (simp_all add: \<epsilon>_simps \<tau>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

corollary \<R>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle> = \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<close> \<open>\<R>\<^sub>n\<^sub>d \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> Bs\<rrangle> = \<R>\<^sub>n\<^sub>d \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> Bs\<rrangle>\<close>
  by (intro ext same_\<tau>_implies_same_\<R>\<^sub>d same_\<tau>_implies_same_\<R>\<^sub>n\<^sub>d,
      simp add: \<tau>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)+


lemma combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq:
  \<open>\<epsilon> \<llangle>\<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^sub>d\<otimes>\<lbrakk>1, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> \<sigma>s = \<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> \<sigma>s\<close>
  \<open>\<tau> \<llangle>\<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^sub>d\<otimes>\<lbrakk>1, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e = \<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e\<close>
  \<open>\<epsilon> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<^sub>0\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^sub>n\<^sub>d\<otimes>\<lbrakk>1, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> \<sigma>s = \<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> \<sigma>s\<close>
  \<open>\<tau> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<^sub>0\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^sub>n\<^sub>d\<otimes>\<lbrakk>1, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e = \<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e\<close>
  by (simp_all add: \<epsilon>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k drop_Suc combine_Sync_\<epsilon>_def,
      auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs singl_list_conv_defs \<epsilon>_simps) 
    (metis append_Cons append_Nil)



lemma combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_and_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq:
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] = \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> [A\<^sub>0, A\<^sub>1]\<rrangle> [s\<^sub>0, s\<^sub>1]\<close>
  \<open>\<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] e = \<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> [A\<^sub>0, A\<^sub>1]\<rrangle> [s\<^sub>0, s\<^sub>1] e\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] = \<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> [B\<^sub>0, B\<^sub>1]\<rrangle> [s\<^sub>0, s\<^sub>1]\<close>
  \<open>\<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] e = \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> [B\<^sub>0, B\<^sub>1]\<rrangle> [s\<^sub>0, s\<^sub>1] e\<close>
  by (simp_all add: \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs singl_list_conv_defs 
      option.case_eq_if \<epsilon>_simps combine_Sync_\<epsilon>_def)



lemmas combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_and_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq =
  combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_and_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq[simplified]



subsection \<open>Transmission of Properties\<close>

lemma finite_trans_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>(\<And>A. A \<in> set As \<Longrightarrow> finite_trans A) \<Longrightarrow> finite_trans \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<close>
  by (induct As rule: induct_list012) 
    (auto simp add: singl_list_conv_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs finite_trans_def finite_image_set2)

lemma \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>(\<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A) \<Longrightarrow> \<rho>_disjoint_\<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<close>
  by (induct As rule: induct_list012)
    (simp_all add: \<rho>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<rho>_disjoint_\<epsilon>_def combine_Sync_\<epsilon>_def)

lemma \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<forall>B \<in> set Bs. \<rho>_disjoint_\<epsilon> B \<Longrightarrow> \<rho>_disjoint_\<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> Bs\<rrangle>\<close>
  by (induct Bs rule: induct_list012)
    (simp_all add: \<rho>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<rho>_disjoint_\<epsilon>_def combine_Sync_\<epsilon>_def)


lemma same_length_indep_transmission_to_iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>indep_enabl A\<^sub>0 s\<^sub>0 E \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle> \<sigma>s\<close>
  if \<open>length \<sigma>s = length As\<close>
    \<open>\<And>i j. \<lbrakk>i \<le> length As; j \<le> length As; i \<noteq> j\<rbrakk> \<Longrightarrow> 
            indep_enabl ((A\<^sub>0 # As) ! i) ((s\<^sub>0 # \<sigma>s) ! i) E ((A\<^sub>0 # As) ! j) ((s\<^sub>0 # \<sigma>s) ! j)\<close>
  using same_length_indep_transmission_to_iterated_combine\<^sub>d_Sync[OF that]
  by (simp add: indep_enabl_def \<epsilon>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      \<tau>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<R>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k that(1))


lemma \<omega>_iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>length \<sigma>s = length As \<Longrightarrow>
   \<omega> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle> \<sigma>s = (if As = [] then \<diamond> else those (map2 \<omega> As \<sigma>s))\<close>
  by (induct \<sigma>s As rule: induct_2_lists012)
    (simp_all add: singl_list_conv_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs split: option.split)


lemma \<omega>_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>length \<sigma>s = length As \<Longrightarrow>
   \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle> \<sigma>s =
   (if As = [] then {} else {rs. length rs = length As \<and> (\<forall>i < length As. rs ! i \<in> \<omega> (As ! i) (\<sigma>s ! i))})\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by simp
next
  case (single \<sigma>1 A1)
  from length_Suc_conv show ?case
    by (auto simp add: singl_list_conv_defs)
next
  case (Cons \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As)
  show ?case (is \<open>_ = ?rhs \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As\<close>)
  proof (intro subset_antisym subsetI)
    fix rs assume \<open>rs \<in> \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A1 # A2 # As\<rrangle> (\<sigma>1 # \<sigma>2 # \<sigma>s)\<close>
    then obtain r1 rs' where \<open>rs = r1 # rs'\<close> \<open>r1 \<in> \<omega> A1 \<sigma>1\<close>
      \<open>rs' \<in> \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A2 # As\<rrangle> (\<sigma>2 # \<sigma>s)\<close>
      by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
    from this(3) Cons.hyps(3) obtain r2 rs''
      where \<open>rs' = r2 # rs''\<close> \<open>length rs'' = length As\<close>
        \<open>\<forall>i<Suc (length As). (r2 # rs'') ! i \<in> \<omega> ((A2 # As) ! i) ((\<sigma>2 # \<sigma>s) ! i)\<close>
      by simp (metis (no_types, lifting) length_Suc_conv)
    with \<open>r1 \<in> \<omega> A1 \<sigma>1\<close> show \<open>rs \<in> ?rhs \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As\<close>
      by (auto simp add: \<open>rs = r1 # rs'\<close> less_Suc_eq_0_disj)
  next
    from Cons.hyps(3)
    show \<open>rs \<in> ?rhs \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As \<Longrightarrow>
          rs \<in> \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A1 # A2 # As\<rrangle> (\<sigma>1 # \<sigma>2 # \<sigma>s)\<close> for rs
      by (cases rs; cases \<open>tl rs\<close>, simp_all add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs) auto
  qed
qed


subsection \<open>Normalization\<close>

lemma \<omega>_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_det_ndet_conv:
  \<open>length \<sigma>s = length As \<Longrightarrow>
   \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s = \<omega> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil
  show ?case by (simp add: base_trans_det_ndet_conv(1))
next
  case (single \<sigma>1 A1)
  show ?case by (simp add: from_det_to_ndet_singl_list_conv_commute)
next
  case (Cons \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As)
  thus ?case
    by (auto simp add: det_ndet_conv_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs split: option.split)
qed

lemma \<tau>_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>length \<sigma>s = length As \<Longrightarrow>
   (\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk>
    \<Longrightarrow> indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)) \<Longrightarrow> 
   \<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s e = \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s e\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil
  show ?case by simp
next
  case (single \<sigma>1 A1)
  show ?case by (simp add: from_det_to_ndet_singl_list_conv_commute(1))
next
  case (Cons \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As)
  have * : \<open>\<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A2 # As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (\<sigma>2 # \<sigma>s) e =
            \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) (A2 # As)\<rrangle> (\<sigma>2 # \<sigma>s) e\<close>
  proof (rule Cons.hyps(3))
    show \<open>\<lbrakk>i < length (A2 # As); j < length (A2 # As); i \<noteq> j\<rbrakk>
          \<Longrightarrow> indep_enabl ((A2 # As) ! i) ((\<sigma>2 # \<sigma>s) ! i) E
                              ((A2 # As) ! j) ((\<sigma>2 # \<sigma>s) ! j)\<close> for i j
      using Cons.prems[of \<open>Suc i\<close> \<open>Suc j\<close>] by simp
  qed
  have \<open>\<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A1 # A2 # As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (\<sigma>1 # \<sigma>2 # \<sigma>s) e =
        \<tau> \<llangle>\<llangle>A1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A2 # As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (\<sigma>1 # \<sigma>2 # \<sigma>s) e\<close>
  proof (subst iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(3), rule \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep)
    show \<open>\<epsilon> A1 \<sigma>1 \<inter> \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A2 # As\<rrangle> (\<sigma>2 # \<sigma>s) \<subseteq> E\<close>
    proof (rule indep_enablD[OF _ \<R>\<^sub>d.init \<R>\<^sub>d.init])
      show \<open>indep_enabl A1 \<sigma>1 E \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A2 # As\<rrangle> (\<sigma>2 # \<sigma>s)\<close>
        by (simp add: Cons.hyps(1) Cons.prems order_le_less_trans
            same_length_indep_transmission_to_iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    qed
  qed
  also have \<open>\<dots> = \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) (A1 # A2 # As)\<rrangle> (\<sigma>1 # \<sigma>2 # \<sigma>s) e\<close>
    by (use "*" in \<open>simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<epsilon>_simps\<close>)
      (metis empty_from_det_to_ndet_is_None_trans option.exhaust)
  finally show ?case .
qed



lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  assumes same_length: \<open>length \<sigma>s = length As\<close>
    and indep: \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
                      indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
  shows \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d, rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id)
  show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow>
        \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s' e = \<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s' e\<close> for \<sigma>s' e
  proof (rule \<tau>_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep[symmetric])
    show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow> length \<sigma>s' = length As\<close>
      by (metis \<R>\<^sub>n\<^sub>d_from_det_to_ndet \<R>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(1) same_length
          same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description)
  next
    show \<open>\<lbrakk>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s; i < length As; j < length As; i \<noteq> j\<rbrakk>
          \<Longrightarrow> indep_enabl (As ! i) (\<sigma>s' ! i) E (As ! j) (\<sigma>s' ! j)\<close> for i j
      by (unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet \<R>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k,
          drule same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description[OF same_length])
        (meson \<R>\<^sub>d_trans indep_enabl_def indep)
  qed
next
  show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow>
        \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s' = \<omega> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s'\<close> for \<sigma>s'
    by (metis \<R>\<^sub>n\<^sub>d_from_det_to_ndet \<R>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(1)
        \<omega>_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_det_ndet_conv same_length
        same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description)
qed


lemma P_d_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  assumes same_length: \<open>length \<sigma>s = length As\<close>
    and indep: \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
                      indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
  shows \<open>P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (fold P_nd_from_det_to_ndet_is_P_d, rule P_nd_eqI_strong_id)
  show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow>
        \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s' e = \<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s' e\<close> for \<sigma>s' e
  proof (rule \<tau>_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep[symmetric])
    show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow> length \<sigma>s' = length As\<close>
      by (metis \<R>\<^sub>n\<^sub>d_from_det_to_ndet \<R>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(1) same_length
          same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description)
  next
    show \<open>\<lbrakk>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s; i < length As; j < length As; i \<noteq> j\<rbrakk>
          \<Longrightarrow> indep_enabl (As ! i) (\<sigma>s' ! i) E (As ! j) (\<sigma>s' ! j)\<close> for i j
      by (unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet \<R>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k,
          drule same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description[OF same_length])
        (meson \<R>\<^sub>d_trans indep_enabl_def indep)
  qed
qed



section \<open>Compactification Theorems\<close>

subsection \<open>Binary\<close>

subsubsection \<open>Pair\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  fixes E :: \<open>'a set\<close>
  assumes \<rho>_disjoint_\<epsilon> : \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close>
  defines A_def: \<open>A \<equiv> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<close>      
  defines P_def: \<open>P \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d\<close> and Q_def: \<open>Q \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d\<close> and S_def: \<open>S \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  shows \<open>P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1 = S (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
proof -
  let ?f = \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) (\<lambda>\<sigma>'. case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>\<^sub>1) \<Rightarrow> P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1)\<close>
  note cartprod_rwrt = GlobalNdet_cartprod[of _ _ \<open>\<lambda>x y. _ (x, y)\<close>, simplified]
  note Ndet_and_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r = Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left
    Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right
  note Mprefix_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_constant =
    Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP
    Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP
  note P_rec = restriction_fix_eq[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis[of A\<^sub>0], folded P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def P_def, THEN fun_cong]
  note Q_rec = restriction_fix_eq[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis[of A\<^sub>1], folded P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def Q_def, THEN fun_cong]
  have \<omega>_A : \<open>\<omega> A (\<sigma>\<^sub>0', \<sigma>\<^sub>1') = \<omega> A\<^sub>0 \<sigma>\<^sub>0' \<times> \<omega> A\<^sub>1 \<sigma>\<^sub>1'\<close> for \<sigma>\<^sub>0' \<sigma>\<^sub>1'
    by (auto simp add: A_def combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  have \<epsilon>_A : \<open>\<epsilon> A (\<sigma>\<^sub>0', \<sigma>\<^sub>1') = combine_sets_Sync (\<epsilon> A\<^sub>0 \<sigma>\<^sub>0') E (\<epsilon> A\<^sub>1 \<sigma>\<^sub>1')\<close> for \<sigma>\<^sub>0' \<sigma>\<^sub>1'
    by (simp add: A_def \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k combine_Sync_\<epsilon>_def)
  show \<open>P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1 = S (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
  proof (rule fun_cong[of \<open>\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1\<close> _ \<open>(\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>, simplified])
    show \<open>(\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1) = S\<close>
    proof (rule restriction_fix_unique[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis[of A],
          symmetric, folded P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def S_def])
      show \<open>?f = (\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1)\<close>
      proof (rule ext, clarify)
        have \<rho>_disjoint_\<epsilon>_bis : \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {} \<Longrightarrow> \<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close>
          \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {} \<Longrightarrow> \<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close> for \<sigma>\<^sub>0 \<sigma>\<^sub>1
          by (simp_all add: \<rho>_simps \<rho>_disjoint_\<epsilon>D \<rho>_disjoint_\<epsilon>)
        show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1\<close> for \<sigma>\<^sub>0 \<sigma>\<^sub>1
        proof (cases \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close>; cases \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>)
          assume \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
          hence P_rec' : \<open>P \<sigma>\<^sub>0 = P_nd_step (\<epsilon> A\<^sub>0) (\<tau> A\<^sub>0) P \<sigma>\<^sub>0\<close>
            and Q_rec' : \<open>Q \<sigma>\<^sub>1 = P_nd_step (\<epsilon> A\<^sub>1) (\<tau> A\<^sub>1) Q \<sigma>\<^sub>1\<close>
            and S_rec' : \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) (\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1) (\<sigma>\<^sub>0, \<sigma>\<^sub>1) =
                        P_nd_step (\<epsilon> A) (\<tau> A) (\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1) (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
            by (simp_all add: P_rec[of \<sigma>\<^sub>0] Q_rec[of \<sigma>\<^sub>1] \<omega>_A)
          show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1\<close>
            unfolding P_rec' Q_rec' S_rec' Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_for_procomata
            unfolding \<epsilon>_A Mprefix_Un_distrib
            by (intro arg_cong2[where f = \<open>(\<box>)\<close>] mono_Mprefix_eq, fold P_rec' Q_rec',
                auto simp add: A_def Ndet_and_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r cartprod_rwrt
                combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<epsilon>_simps GlobalNdet_sets_commute[of \<open>\<tau> A\<^sub>1 _ _\<close>]
                simp flip: GlobalNdet_factorization_union
                intro!: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<sqinter>)\<close>])
        next
          assume \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
          from \<rho>_disjoint_\<epsilon>(1) \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close> have \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close>
            by (simp add: \<rho>_disjoint_\<epsilon>_def \<rho>_simps)
          have \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = \<box>b\<in>(\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 - E) \<rightarrow> (\<sqinter>\<sigma>\<^sub>1'\<in>\<tau> A\<^sub>1 \<sigma>\<^sub>1 b. (SKIPS (\<omega> A\<^sub>0 \<sigma>\<^sub>0) \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1'))\<close>
            by (auto simp add: \<omega>_A \<epsilon>_A \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close> \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> intro!: mono_Mprefix_eq,
                auto simp add: A_def combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close>
                \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> cartprod_rwrt P_rec[of \<sigma>\<^sub>0] intro!: mono_GlobalNdet_eq)
          also have \<open>\<dots> = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1\<close>
            by (unfold P_rec[of \<sigma>\<^sub>0] Q_rec[of \<sigma>\<^sub>1])
              (auto simp add: SKIPS_def Ndet_and_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r Mprefix_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_constant \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close>
                GlobalNdet_Mprefix_distr GlobalNdet_sets_commute[of \<open>\<tau> A\<^sub>1 _ _\<close>] \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
                intro!: mono_Mprefix_eq mono_GlobalNdet_eq)
          finally show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = \<dots>\<close> .
        next
          assume \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close>
          from \<rho>_disjoint_\<epsilon>(2) \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close> have \<open>\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
            by (simp add: \<rho>_disjoint_\<epsilon>_def \<rho>_simps)
          have \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = \<box>a\<in>(\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 - E) \<rightarrow> (\<sqinter>\<sigma>\<^sub>0'\<in>\<tau> A\<^sub>0 \<sigma>\<^sub>0 a. (P \<sigma>\<^sub>0' \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r SKIPS (\<omega> A\<^sub>1 \<sigma>\<^sub>1)))\<close>
            by (auto simp add: \<omega>_A \<epsilon>_A \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> \<open>\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close> intro!: mono_Mprefix_eq,
                auto simp add: A_def combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close>
                \<open>\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close> cartprod_rwrt Q_rec[of \<sigma>\<^sub>1] intro!: mono_GlobalNdet_eq)
          also have \<open>\<dots> = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1\<close>
            by (unfold P_rec[of \<sigma>\<^sub>0] Q_rec[of \<sigma>\<^sub>1])
              (auto simp add: SKIPS_def Ndet_and_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r Mprefix_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_constant \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close>
                GlobalNdet_Mprefix_distr GlobalNdet_sets_commute[of \<open>\<tau> A\<^sub>0 _ _\<close>] \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close>
                intro!: mono_Mprefix_eq mono_GlobalNdet_eq)
          finally show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = \<dots>\<close> .
        next
          assume \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close>
          with \<rho>_disjoint_\<epsilon> have \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> \<open>\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
            by (simp_all add: \<rho>_disjoint_\<epsilon>_def \<rho>_simps)
          show \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {} \<Longrightarrow> \<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {} \<Longrightarrow> ?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1\<close>
            by (simp add: \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close> \<omega>_A P_rec[of \<sigma>\<^sub>0] Q_rec[of \<sigma>\<^sub>1] SKIPS_def
                Ndet_and_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r cartprod_rwrt GlobalNdet_sets_commute[of \<open>\<omega> A\<^sub>0 _\<close>])
        qed
      qed
    qed
  qed
qed

corollary P_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) simp_all
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<close>
    by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
  if \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> and \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> and \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp flip: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (metis \<rho>_disjoint_\<epsilon>_def det_ndet_conv_\<epsilon>(1) det_ndet_conv_\<rho>(1) \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close>,
        metis \<rho>_disjoint_\<epsilon>_def det_ndet_conv_\<epsilon>(1) det_ndet_conv_\<rho>(1) \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>)
  finally show ?thesis .
qed

corollary P_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, simp_all add: \<rho>_simps \<rho>_disjoint_\<epsilon>_def)
      (rule indep_enablI,
        use \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>[THEN indep_enablD] in \<open>simp add: \<epsilon>_simps\<close>)
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<close>
    by (simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  finally show ?thesis .
qed



subsubsection \<open>Pairlist\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  fixes E :: \<open>'a set\<close>
  assumes \<rho>_disjoint_\<epsilon> : \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close>
  shows \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
proof -
  let ?A = \<open>\<lparr>\<tau> = \<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>, \<omega> = \<lambda>\<sigma>. (\<lambda>(r, s). [r, s]) ` \<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>\<rparr>\<close>
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 =
        RenamingTick (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1) (\<lambda>(r, s). [r, s])\<close>
    by (simp only: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t)
  also have \<open>\<dots> = RenamingTick (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)) (\<lambda>(r, s). [r, s])\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<rho>_disjoint_\<epsilon>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>?A\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (simp only: RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (auto intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of \<open>\<lambda>(r, s). [r, s]\<close> _ \<open>(\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>, simplified] inj_onI)
      (auto simp add: combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs split: if_split_asm)
  finally show ?thesis .
qed

corollary P_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) simp_all
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<close>
    by (simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
  if \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> and \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> and \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp flip: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (metis \<rho>_disjoint_\<epsilon>_def det_ndet_conv_\<epsilon>(1) det_ndet_conv_\<rho>(1) \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close>,
        metis \<rho>_disjoint_\<epsilon>_def det_ndet_conv_\<epsilon>(1) det_ndet_conv_\<rho>(1) \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>)
  finally show ?thesis .
qed

corollary P_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
  if \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, simp_all)
      (rule indep_enablI,
        use \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>[THEN indep_enablD] in simp)
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<close>
    by (simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  finally show ?thesis .
qed



subsection \<open>Rlist\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  fixes E :: \<open>'a set\<close>
  assumes \<rho>_disjoint_\<epsilon> : \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close>
  defines A_def: \<open>A \<equiv> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<close>      
  defines P_def: \<open>P \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d\<close> and Q_def: \<open>Q \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d\<close> and S_def: \<open>S \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  shows \<open>P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q \<sigma>s = S (\<sigma>\<^sub>0 # \<sigma>s)\<close>
proof -
  let ?A' = \<open>\<lparr>\<tau> = \<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>, \<omega> = \<lambda>\<sigma>. (\<lambda>(x, y). x # y) ` \<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>\<rparr>\<close>
  from P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<rho>_disjoint_\<epsilon>]
  have \<open>P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>s)\<close> by (simp add: P_def Q_def)
  hence \<open>RenamingTick (P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>s) (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 # \<sigma>s) =
         RenamingTick (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>s)) (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 # \<sigma>s)\<close> by simp
  also have \<open>RenamingTick (P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>s) (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 # \<sigma>s) = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q \<sigma>s\<close>
    by (auto intro: inj_onI Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        [of \<open>\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 # \<sigma>s\<close>, simplified])
  also have \<open>RenamingTick (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>s)) (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 # \<sigma>s) = S (\<sigma>\<^sub>0 # \<sigma>s)\<close>
  proof (unfold RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd S_def,
      rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of \<open>\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 # \<sigma>s\<close> ?A' \<open>(\<sigma>\<^sub>0, \<sigma>s)\<close>, simplified])
    show \<open>inj_on (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 # \<sigma>s) (\<R>\<^sub>n\<^sub>d ?A' (\<sigma>\<^sub>0, \<sigma>s))\<close> by (auto intro: inj_onI)
  next
    show \<open>\<tau> A (case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>s) \<Rightarrow> \<sigma>\<^sub>0 # \<sigma>s) e =
          (\<lambda>\<sigma>''. case \<sigma>'' of (\<sigma>\<^sub>0, \<sigma>s) \<Rightarrow> \<sigma>\<^sub>0 # \<sigma>s) ` \<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>' e\<close> for \<sigma>' e
      by (cases \<sigma>') (auto simp add: A_def combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  next
    show \<open>\<omega> A (case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>s) \<Rightarrow> \<sigma>\<^sub>0 # \<sigma>s) =
          (\<lambda>\<sigma>''. case \<sigma>'' of (\<sigma>\<^sub>0, \<sigma>s) \<Rightarrow> \<sigma>\<^sub>0 # \<sigma>s) ` \<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>'\<close> for \<sigma>'
      by (cases \<sigma>') (auto simp add: A_def combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  qed
  finally show \<open>P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q \<sigma>s = S (\<sigma>\<^sub>0 # \<sigma>s)\<close> .
qed

corollary P_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>s = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>s =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (simp_all add: \<rho>_simps \<rho>_disjoint_\<epsilon>_def)
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<close>
    by (simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs, intro ext, simp add: \<epsilon>_simps)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
  if \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> and \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> and \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>s\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
    by (simp flip: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (metis \<rho>_disjoint_\<epsilon>_def det_ndet_conv_\<epsilon>(1) det_ndet_conv_\<rho>(1) \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close>,
        metis \<rho>_disjoint_\<epsilon>_def det_ndet_conv_\<epsilon>(1) det_ndet_conv_\<rho>(1) \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>s\<close>)
  finally show ?thesis .
qed

corollary P_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>s = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
  if \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>s\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>s =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>s\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, simp_all add: \<rho>_simps \<rho>_disjoint_\<epsilon>_def)
      (rule indep_enablI,
        use \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>s\<close>[THEN indep_enablD] in \<open>simp add: \<epsilon>_simps\<close>)
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<close>
    by (simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs, intro ext, simp add: \<epsilon>_simps)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  finally show ?thesis .
qed



subsection \<open>ListslenL\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  fixes E :: \<open>'a set\<close>
  assumes same_length_reach0 : \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> length \<sigma>\<^sub>0' = len\<^sub>0\<close>
    and same_length_term0 : \<open>\<And>\<sigma>\<^sub>0' rs. \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> rs \<in> \<omega> A\<^sub>0 \<sigma>\<^sub>0' \<Longrightarrow> length rs = len\<^sub>0\<close>
    and \<rho>_disjoint_\<epsilon> : \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close>
  defines A_def: \<open>A \<equiv> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<close>      
  defines P_def: \<open>P \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d\<close> and Q_def: \<open>Q \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d\<close> and S_def: \<open>S \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  shows \<open>P \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q \<sigma>\<^sub>1 = S (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
proof -
  let ?A' = \<open>\<lparr>\<tau> = \<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>, \<omega> = \<lambda>\<sigma>. (\<lambda>(x, y). x @ y) ` \<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>\<rparr>\<close>
  let ?RT = RenamingTick
  have * : \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d ?A' (\<sigma>\<^sub>0, \<sigma>\<^sub>1) \<Longrightarrow> length (fst \<sigma>') = len\<^sub>0\<close> for \<sigma>'
    by (metis (no_types, lifting) \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset mem_Sigma_iff prod.collapse
        same_\<tau>_implies_same_\<R>\<^sub>n\<^sub>d same_length_reach0 select_convs(1) subset_iff)

  from P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<rho>_disjoint_\<epsilon>]
  have \<open>P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (simp add: P_def Q_def)

  hence \<open>?RT (P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1) (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 @ \<sigma>s) =
         ?RT (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)) (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 @ \<sigma>s)\<close> by simp
  also have \<open>?RT (P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<sigma>\<^sub>1) (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 @ \<sigma>s) = P \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q \<sigma>\<^sub>1\<close>
    by (rule Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L[OF is_ticks_length_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd[of A\<^sub>0, folded P_def]])
      (fact same_length_term0)
  also have \<open>?RT (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)) (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 @ \<sigma>s) = S (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (auto simp add: RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd S_def dest!: "*"
        intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of \<open>\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 @ \<sigma>s\<close> ?A' \<open>(\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>, simplified] inj_onI)
      (force simp add: image_iff A_def combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs split: if_split_asm)+
  finally show ?thesis .
qed

corollary P_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
  if same_length_reach0 : \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> length \<sigma>\<^sub>0' = len\<^sub>0\<close>
proof -
  have * : \<open>\<sigma>s \<in> \<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>0. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>1. {}\<rparr>\<rrangle> (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1) \<Longrightarrow> len\<^sub>0 \<le> length \<sigma>s\<close> for \<sigma>s
    by (auto dest: set_rev_mp[OF _ \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]
        simp add: same_length_reach0)
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>0. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>1. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>0. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>1. {}\<rparr>\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (auto intro: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k simp add: same_length_reach0)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>1. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (auto intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id dest!: "*")
      (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs split: if_split_asm)
  also have \<open>\<dots> = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  assumes same_length_reach0 : \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> length \<sigma>\<^sub>0' = len\<^sub>0\<close>
    and same_length_term0 : \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> \<omega> A\<^sub>0 \<sigma>\<^sub>0' \<noteq> \<diamond> \<Longrightarrow> length \<lceil>\<omega> A\<^sub>0 \<sigma>\<^sub>0'\<rceil> = len\<^sub>0\<close>
    and \<rho>_disjoint_\<epsilon> : \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close>
    and indep_enabl : \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
  shows \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
         P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
proof -
  have * : \<open>\<sigma>s \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1) \<Longrightarrow>
            \<exists>\<sigma>\<^sub>0' \<sigma>\<^sub>1'. \<sigma>s = \<sigma>\<^sub>0' @ \<sigma>\<^sub>1' \<and> \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<and> \<sigma>\<^sub>1' \<in> \<R>\<^sub>d A\<^sub>1 \<sigma>\<^sub>1\<close> for \<sigma>s
    by (auto dest!: set_rev_mp[OF _ \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]
        simp add: \<R>\<^sub>n\<^sub>d_from_det_to_ndet same_length_reach0)+
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also from same_length_term0 have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (auto intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k split: option.split_asm
        simp add: \<rho>_disjoint_\<epsilon> \<R>\<^sub>n\<^sub>d_from_det_to_ndet same_length_reach0 \<omega>_from_det_to_ndet)
      (metis option.sel)
  also from indep_enabl have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (auto intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id
        \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep \<omega>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour
        simp add: same_length_reach0 dest!: "*" indep_enablD)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  finally show ?thesis .
qed

corollary P_d_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  assumes same_length_reach0 : \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> length \<sigma>\<^sub>0' = len\<^sub>0\<close>
    and indep_enabl : \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
  shows \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
         P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
proof -
  have * : \<open>\<sigma>s \<in> \<R>\<^sub>d \<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>0. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>1. \<diamond>\<rparr>\<rrangle> (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1) \<Longrightarrow> len\<^sub>0 \<le> length \<sigma>s\<close> for \<sigma>s
    by (auto dest: set_rev_mp[OF _ \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]
        simp add: same_length_reach0)
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>0. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bsub>len\<^sub>0\<^esub>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>1. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  also from indep_enabl
  have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>0. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>1. \<diamond>\<rparr>\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (auto intro: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k simp add: same_length_reach0)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>\<^sub>0. \<diamond>\<rparr>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (auto intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI_strong_id dest!: "*")
      (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs split: if_split_asm)
  also have \<open>\<dots> = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  finally show ?thesis .
qed



subsection \<open>Multiple\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>length \<sigma>s = length As \<Longrightarrow> (\<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A) \<Longrightarrow>
   \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip \<sigma>s As. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp, subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec, simp)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case
    by (auto simp add: RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd singl_list_conv_defs
        intro!: inj_onI P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  have \<rho>_disjoint_\<epsilon> : \<open>A \<in> set (A\<^sub>1 # As) \<Longrightarrow> \<rho>_disjoint_\<epsilon> A\<close> for A
    by (simp add: Cons.prems)
  show ?case
    by (simp add: Cons.hyps(3)[OF \<rho>_disjoint_\<epsilon>, simplified] Cons.prems
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed

corollary P_nd_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>length \<sigma>s = length As \<Longrightarrow> \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip \<sigma>s As. P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp, subst P_nd_rec, simp)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case
    by (simp, subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
      (auto simp add: RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd singl_list_conv_defs
        intro!: inj_onI P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  show ?case
    by (simp add: Cons.hyps(3)[simplified] Cons.prems
        P_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<lbrakk>length \<sigma>s = length As; \<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A;
    \<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
          indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<rbrakk> \<Longrightarrow>
   \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip \<sigma>s As. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp, subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec, simp)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case
    by (auto simp add: RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d singl_list_conv_defs
        intro!: inj_onI P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI_strong split: option.split)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  have \<rho>_disjoint_\<epsilon> : \<open>A \<in> set (A\<^sub>1 # As) \<Longrightarrow> \<rho>_disjoint_\<epsilon> A\<close> for A
    by (simp add: Cons.prems(1))
  have indep_enabl :
    \<open>\<lbrakk>i < length (A\<^sub>1 # As); j < length (A\<^sub>1 # As); i \<noteq> j\<rbrakk> \<Longrightarrow>
     indep_enabl ((A\<^sub>1 # As) ! i) ((\<sigma>\<^sub>1 # \<sigma>s) ! i) E ((A\<^sub>1 # As) ! j) ((\<sigma>\<^sub>1 # \<sigma>s) ! j)\<close> for i j
    by (metis Cons.prems(2) Suc_less_eq length_Cons nat.inject nth_Cons_Suc)
  have \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> by (simp add: Cons.prems(1))
  moreover have \<open>\<rho>_disjoint_\<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle>\<close>
    by (meson \<rho>_disjoint_\<epsilon> \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  moreover have \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (metis Cons.hyps(1) Cons.prems(2) length_Cons less_Suc_eq_le
        same_length_indep_transmission_to_iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  ultimately show ?case 
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        Cons.hyps(3)[OF \<rho>_disjoint_\<epsilon> indep_enabl, simplified])
qed

corollary P_d_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<lbrakk>length \<sigma>s = length As;
    \<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
          indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<rbrakk> \<Longrightarrow>
   \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip \<sigma>s As. P\<llangle>A\<rrangle>\<^sub>d \<sigma> = P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp, subst P_d_rec, simp)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case
    by (simp, subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
      (auto simp add: RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d singl_list_conv_defs
        intro!: inj_onI P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI_strong split: option.split)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  have indep_enabl :
    \<open>\<lbrakk>i < length (A\<^sub>1 # As); j < length (A\<^sub>1 # As); i \<noteq> j\<rbrakk> \<Longrightarrow>
     indep_enabl ((A\<^sub>1 # As) ! i) ((\<sigma>\<^sub>1 # \<sigma>s) ! i) E ((A\<^sub>1 # As) ! j) ((\<sigma>\<^sub>1 # \<sigma>s) ! j)\<close> for i j
    by (metis Cons.prems Suc_less_eq length_Cons nat.inject nth_Cons_Suc)
  have \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (metis Cons.hyps(1) Cons.prems length_Cons less_Suc_eq_le
        same_length_indep_transmission_to_iterated_combine\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  thus ?case 
    by (simp add: P_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        Cons.hyps(3)[OF indep_enabl, simplified])
qed



(* 

corollary P_nd_compactification_Sync_order_is_arbitrary:
  \<open>P\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<^sub>n\<^sub>d \<sigma>s = P\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As'\<rrangle>\<^sub>n\<^sub>d \<sigma>s'\<close>
  if \<open>mset (zip \<sigma>s As) = mset (zip \<sigma>s' As')\<close> and \<open>length \<sigma>s = length As\<close> and \<open>length \<sigma>s' = length As'\<close>
    and \<open>\<forall>A \<in> set As. finite_trans A\<close> and \<open>\<forall>A \<in> set As. \<rho>_disjoint_\<epsilon> A\<close>
proof -
  have \<open>P\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<^sub>n\<^sub>d \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> (map (\<lambda>A. A\<lparr>\<S>\<^sub>F := {}\<rparr>) As)\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
    apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_empty_\<S>\<^sub>F_bis, simp add: finite_trans_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k that(4))
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_ndI_strong_id)
      (simp_all add: finite_trans_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k that(4) prem_old_compact)
  moreover have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> (map (\<lambda>A. A\<lparr>\<S>\<^sub>F := {}\<rparr>) As')\<rrangle>\<^sub>n\<^sub>d \<sigma>s'\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync_order_is_arbitrary) (simp_all add: that zip_map2)
  moreover have \<open>\<dots> = P\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As'\<rrangle>\<^sub>n\<^sub>d \<sigma>s'\<close>
    apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_empty_\<S>\<^sub>F_bis, metis in_set_impl_in_set_zip2 set_mset_mset set_zip_rightD
        finite_trans_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k that(1, 3, 4))
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_ndI_strong_id, simp_all add: prem_old_compact)
      (metis in_set_impl_in_set_zip2 set_mset_mset set_zip_rightD
        finite_trans_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k that(1, 3, 4))+
  ultimately show \<open>P\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<^sub>n\<^sub>d \<sigma>s = P\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As'\<rrangle>\<^sub>n\<^sub>d \<sigma>s'\<close> by presburger
qed


corollary P_d_compactification_Sync_order_is_arbitrary:
  \<open>P\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<^sub>d \<sigma>s = P\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As'\<rrangle>\<^sub>d \<sigma>s'\<close>
  if \<open>mset (zip \<sigma>s As) = mset (zip \<sigma>s' As')\<close> and \<open>length \<sigma>s = length As\<close> and \<open>length \<sigma>s' = length As'\<close>
    and \<open>\<forall>i<length As. \<forall>j<length As. i \<noteq> j \<longrightarrow> indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
    and \<open>\<forall>A \<in> set As. \<rho>_disjoint_\<epsilon> A\<close>
proof -
  have \<open>P\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<^sub>d \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> (map (\<lambda>A. A\<lparr>\<S>\<^sub>F := {}\<rparr>) As)\<rrangle>\<^sub>d \<sigma>s\<close>
    apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_empty_\<S>\<^sub>F_bis)
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_dI_strong_id) (simp_all add: prem_old_compact option.map_id)
  moreover have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> (map (\<lambda>A. A\<lparr>\<S>\<^sub>F := {}\<rparr>) As')\<rrangle>\<^sub>d \<sigma>s'\<close>
    using that(4) by (intro P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync_order_is_arbitrary)
      (simp_all add: that zip_map2 \<R>\<^sub>d_\<S>\<^sub>F_useless \<epsilon>_simps)
  moreover have \<open>\<dots> = P\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As'\<rrangle>\<^sub>d \<sigma>s'\<close>
    apply (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_empty_\<S>\<^sub>F_bis)
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_dI_strong_id) (simp_all add: prem_old_compact option.map_id)
  ultimately show \<open>P\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As\<rrangle>\<^sub>d \<sigma>s = P\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> As'\<rrangle>\<^sub>d \<sigma>s'\<close> by presburger
qed






 *)



section \<open>Derived Versions\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_upt_version:
  \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> P \<in>@ map Q [0..<n]. P = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map A [0..<n]\<rrangle>\<rrangle>\<^sub>n\<^sub>d (replicate n 0)\<close>
  if \<open>\<And>i. i < n \<Longrightarrow> \<rho>_disjoint_\<epsilon> (A i)\<close>
    \<open>\<And>i. i < n \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 = Q i\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> P \<in>@ map Q [0..<n]. P = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i \<in>@ [0..<n]. Q i\<close>
    by (auto intro: mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq2)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i \<in>@ [0..<n]. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0\<close>
    by (auto simp add: that(2) intro: mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (replicate n 0) (map A [0..<n]). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
  proof (induct n rule: nat_induct_012)
    case (Suc k)
    have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i\<in>@ [0..<Suc k]. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 =
          \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i\<in>@ [0..<k]. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A k\<rrangle>\<^sub>n\<^sub>d 0\<close>
      using Suc.hyps(1) by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc)
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (replicate k 0) (map A [0..<k]). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A k\<rrangle>\<^sub>n\<^sub>d 0\<close>
      by (simp only: Suc.hyps(2))
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (replicate (Suc k) 0) (map A [0..<Suc k]). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
      using Suc.hyps(1) by (simp flip: replicate_append_same add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc)
    finally show ?case .
  qed simp_all
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map A [0..<n]\<rrangle>\<rrangle>\<^sub>n\<^sub>d (replicate n 0)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (auto simp add: that(1))
  finally show ?thesis .
qed

lemma P_nd_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_upt_version:
  \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> P \<in>@ map Q [0..<n]. P = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map A [0..<n]\<rrangle>\<rrangle>\<^sub>n\<^sub>d (replicate n 0)\<close>
  if \<open>\<And>i. i < n \<Longrightarrow> P\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 = Q i\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> P \<in>@ map Q [0..<n]. P = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i \<in>@ [0..<n]. Q i\<close>
    by (auto intro: mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq2)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i \<in>@ [0..<n]. P\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0\<close>
    by (auto simp add: that intro: mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (replicate n 0) (map A [0..<n]). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
  proof (induct n rule: nat_induct_012)
    case (Suc k)
    have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i\<in>@ [0..<Suc k]. P\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 =
          \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i\<in>@ [0..<k]. P\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A k\<rrangle>\<^sub>n\<^sub>d 0\<close>
      using Suc.hyps(1) by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc)
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (replicate k 0) (map A [0..<k]). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A k\<rrangle>\<^sub>n\<^sub>d 0\<close>
      by (simp only: Suc.hyps(2))
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (replicate (Suc k) 0) (map A [0..<Suc k]). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
      using Suc.hyps(1) by (simp flip: replicate_append_same add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc)
    finally show ?case .
  qed simp_all
  also have \<open>\<dots> = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map A [0..<n]\<rrangle>\<rrangle>\<^sub>n\<^sub>d (replicate n 0)\<close>
    by (rule P_nd_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) simp
  finally show ?thesis .
qed

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_upt_version:
  \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> P \<in>@ map Q [0..<n]. P = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map A [0..<n]\<rrangle>\<rrangle>\<^sub>d (replicate n 0)\<close>
  if \<open>\<And>i. i < n \<Longrightarrow> \<rho>_disjoint_\<epsilon> (A i)\<close>
    \<open>\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> indep_enabl (A i) 0 E (A j) 0\<close>
    \<open>\<And>i. i < n \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>d 0 = Q i\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> P \<in>@ map Q [0..<n]. P = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i \<in>@ [0..<n]. Q i\<close>
    by (auto intro: mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq2)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i \<in>@ [0..<n]. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>d 0\<close>
    by (auto simp add: that(3) intro: mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (replicate n 0) (map A [0..<n]). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
  proof (induct n rule: nat_induct_012)
    case (Suc k)
    have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i\<in>@ [0..<Suc k]. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>d 0 =
          \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i\<in>@ [0..<k]. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>d 0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A k\<rrangle>\<^sub>d 0\<close>
      using Suc.hyps(1) by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc)
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (replicate k 0) (map A [0..<k]). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A k\<rrangle>\<^sub>d 0\<close>
      by (simp only: Suc.hyps(2))
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (replicate (Suc k) 0) (map A [0..<Suc k]). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
      using Suc.hyps(1) by (simp flip: replicate_append_same add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc)
    finally show ?case .
  qed simp_all
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map A [0..<n]\<rrangle>\<rrangle>\<^sub>d (replicate n 0)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (auto simp add: that(1, 2))
  finally show ?thesis .
qed

lemma P_d_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_upt_version:
  \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> P \<in>@ map Q [0..<n]. P = P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map A [0..<n]\<rrangle>\<rrangle>\<^sub>d (replicate n 0)\<close>
  if \<open>\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> indep_enabl (A i) 0 E (A j) 0\<close>
    \<open>\<And>i. i < n \<Longrightarrow> P\<llangle>A i\<rrangle>\<^sub>d 0 = Q i\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> P \<in>@ map Q [0..<n]. P = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i \<in>@ [0..<n]. Q i\<close>
    by (auto intro: mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq2)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i \<in>@ [0..<n]. P\<llangle>A i\<rrangle>\<^sub>d 0\<close>
    by (auto simp add: that intro: mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A)\<in>@ (zip (replicate n 0) (map A [0..<n])). P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
  proof (induct n rule: nat_induct_012)
    case (Suc k)
    have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i\<in>@ [0..<Suc k]. P\<llangle>A i\<rrangle>\<^sub>d 0 =
          \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> i\<in>@ [0..<k]. P\<llangle>A i\<rrangle>\<^sub>d 0 \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A k\<rrangle>\<^sub>d 0\<close>
      using Suc.hyps(1) by (simp add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc)
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A)\<in>@ zip (replicate k 0) (map A [0..<k]). P\<llangle>A\<rrangle>\<^sub>d \<sigma> \<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t P\<llangle>A k\<rrangle>\<^sub>d 0\<close>
      by (simp only: Suc.hyps(2))
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk>\<^sub>\<checkmark> (\<sigma>, A)\<in>@ zip (replicate (Suc k) 0) (map A [0..<Suc k]). P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
      using Suc.hyps(1) by (simp flip: replicate_append_same add: MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc)
    finally show ?case .
  qed simp_all
  also have \<open>\<dots> = P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark> map A [0..<n]\<rrangle>\<rrangle>\<^sub>d (replicate n 0)\<close>
    by (rule P_d_compactification_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (auto simp add: that(1))
  finally show ?thesis .
qed



section \<open>More on Iterated Combine and Events\<close>

text \<open>
Through @{thm [source] \<tau>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<epsilon>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<R>_iterated_combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k},
we immediately recover the results proven in
\<^theory>\<open>HOL-CSP_Proc-Omata.Compactification_Synchronization_Product\<close>.
\<close>


(*<*)
end
  (*>*)
