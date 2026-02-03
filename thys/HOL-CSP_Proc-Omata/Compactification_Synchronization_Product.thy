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


chapter \<open>Compactification of Synchronization Product\<close>

(*<*)
theory Compactification_Synchronization_Product
  imports Combining_Synchronization_Product Process_Normalization_Properties
begin
  (*>*)


section \<open>Iterated Combine\<close>

subsection \<open>Definitions\<close>

fun iterated_combine\<^sub>d_Sync :: \<open>'e set \<Rightarrow> ('\<sigma>, 'e, 'r) A\<^sub>d list \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>d\<close> (\<open>\<llangle>\<^sub>d\<Otimes>\<lbrakk>_\<rbrakk> _\<rrangle>\<close> [0, 0])
  where \<open>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> []\<rrangle> = \<lparr>\<tau> = \<lambda>\<sigma>s a. \<diamond>, \<omega> = \<lambda>\<sigma>s. \<diamond>\<rparr>\<close>
  |     \<open>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> [A\<^sub>0]\<rrangle> = \<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>
  |     \<open>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>0 # A\<^sub>1 # As\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle>\<rrangle>\<close>

fun iterated_combine\<^sub>n\<^sub>d_Sync :: \<open>'e set \<Rightarrow> ('\<sigma>, 'e, 'r) A\<^sub>n\<^sub>d list \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>n\<^sub>d\<close> (\<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>_\<rbrakk> _\<rrangle>\<close> [0, 0])
  where \<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> []\<rrangle> = \<lparr>\<tau> = \<lambda>\<sigma>s a. {}, \<omega> = \<lambda>\<sigma>s. {}\<rparr>\<close>
  |     \<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> [A\<^sub>0]\<rrangle> = \<^sub>n\<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>
  |     \<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>0 # A\<^sub>1 # As\<rrangle> = \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle>\<rrangle>\<close>


lemma iterated_combine\<^sub>d_Sync_simps_bis: \<open>As \<noteq> [] \<Longrightarrow> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>0 # As\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<close>
  and iterated_combine\<^sub>n\<^sub>d_Sync_simps_bis: \<open>Bs \<noteq> [] \<Longrightarrow> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> B\<^sub>0 # Bs\<rrangle> = \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> Bs\<rrangle>\<rrangle>\<close>
  by (induct As, simp_all) (induct Bs, simp_all)


fun iterated_combine\<^sub>d_Sync_\<epsilon> :: \<open>('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>d_scheme list \<Rightarrow> 'e set \<Rightarrow> '\<sigma> list \<Rightarrow> 'e set\<close>
  where \<open>iterated_combine\<^sub>d_Sync_\<epsilon> [] E \<sigma>s = {}\<close> 
  |     \<open>iterated_combine\<^sub>d_Sync_\<epsilon> [A\<^sub>0] E \<sigma>s = \<epsilon> A\<^sub>0 (hd \<sigma>s)\<close>
  |     \<open>iterated_combine\<^sub>d_Sync_\<epsilon> (A\<^sub>0 # A\<^sub>1 # As) E \<sigma>s = 
         combine_sets_Sync (\<epsilon> A\<^sub>0 (hd \<sigma>s)) E (iterated_combine\<^sub>d_Sync_\<epsilon> (A\<^sub>1 # As) E (tl \<sigma>s))\<close>

fun iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon> :: \<open>('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme list \<Rightarrow> 'e set \<Rightarrow> '\<sigma> list \<Rightarrow> 'e set\<close>
  where \<open>iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon> [] E \<sigma>s = {}\<close> 
  |     \<open>iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon> [A\<^sub>0] E \<sigma>s = \<epsilon> A\<^sub>0 (hd \<sigma>s)\<close>
  |     \<open>iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon> (A\<^sub>0 # A\<^sub>1 # As) E \<sigma>s = 
         combine_sets_Sync (\<epsilon> A\<^sub>0 (hd \<sigma>s)) E (iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon> (A\<^sub>1 # As) E (tl \<sigma>s))\<close>


lemma iterated_combine\<^sub>d_Sync_\<epsilon>_simps_bis:
  \<open>As \<noteq> [] \<Longrightarrow> iterated_combine\<^sub>d_Sync_\<epsilon> (A\<^sub>0 # As) E \<sigma>s = 
                combine_sets_Sync (\<epsilon> A\<^sub>0 (hd \<sigma>s)) E (iterated_combine\<^sub>d_Sync_\<epsilon> As E (tl \<sigma>s))\<close>
  and iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon>_simps_bis: 
  \<open>Bs \<noteq> [] \<Longrightarrow> iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon> (B\<^sub>0 # Bs) E \<sigma>s = 
                 combine_sets_Sync (\<epsilon> B\<^sub>0 (hd \<sigma>s)) E (iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon> Bs E (tl \<sigma>s))\<close>
  by (induct As, simp_all) (induct Bs, simp_all)



subsection \<open>First Results\<close>

lemma \<epsilon>_iterated_combine\<^sub>d_Sync:
  \<open>length \<sigma>s = length As \<Longrightarrow> \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s = iterated_combine\<^sub>d_Sync_\<epsilon> As E \<sigma>s\<close>
  by (induct \<sigma>s As rule: induct_2_lists012)
    (simp_all add: \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync combine_Sync_\<epsilon>_def)

lemma \<epsilon>_iterated_combine\<^sub>n\<^sub>d_Sync:
  \<open>length \<sigma>s = length Bs \<Longrightarrow> \<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> Bs\<rrangle> \<sigma>s = iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon> Bs E \<sigma>s\<close>
  by (induct \<sigma>s Bs rule: induct_2_lists012)
    (simp_all add: \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync combine_Sync_\<epsilon>_def)


lemma combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_eq:
  \<open>\<epsilon> \<llangle>\<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<^sub>d\<otimes>\<lbrakk>1, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> \<sigma>s = \<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> \<sigma>s\<close>
  \<open>\<tau> \<llangle>\<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<^sub>d\<otimes>\<lbrakk>1, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e = \<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e\<close>
  \<open>\<epsilon> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<^sub>n\<^sub>d\<otimes>\<lbrakk>1, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> \<sigma>s = \<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> \<sigma>s\<close>
  \<open>\<tau> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<^sub>n\<^sub>d\<otimes>\<lbrakk>1, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e = \<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e\<close>
  by (simp_all add: \<epsilon>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync drop_Suc combine_Sync_\<epsilon>_def,
      auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs \<sigma>_\<sigma>s_conv_defs \<epsilon>_simps) 
    (metis append_Cons append_Nil)



lemma combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_and_iterated_combine\<^sub>n\<^sub>d_Sync_eq:
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] = \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> [A\<^sub>0, A\<^sub>1]\<rrangle> [s\<^sub>0, s\<^sub>1]\<close>
  \<open>\<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] e = \<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> [A\<^sub>0, A\<^sub>1]\<rrangle> [s\<^sub>0, s\<^sub>1] e\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] = \<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> [B\<^sub>0, B\<^sub>1]\<rrangle> [s\<^sub>0, s\<^sub>1]\<close>
  \<open>\<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] e = \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> [B\<^sub>0, B\<^sub>1]\<rrangle> [s\<^sub>0, s\<^sub>1] e\<close>
  by (simp_all add: \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync)
    (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs \<sigma>_\<sigma>s_conv_defs 
      option.case_eq_if \<epsilon>_simps combine_Sync_\<epsilon>_def)



lemmas combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_and_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_eq =
  combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_and_iterated_combine\<^sub>n\<^sub>d_Sync_eq[simplified]



subsection \<open>Reachability\<close>

lemma same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description:
  \<open>length \<sigma>s = length As \<Longrightarrow> \<sigma>s' \<in> \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s \<Longrightarrow>
   length \<sigma>s' = length As \<and> (\<forall>i < length As. \<sigma>s' ! i \<in> \<R>\<^sub>d (As ! i) (\<sigma>s ! i))\<close>
proof (induct \<sigma>s As arbitrary: \<sigma>s' rule: induct_2_lists012)
  case Nil thus ?case by simp
next
  case (single \<sigma>1 A1)
  thus ?case by (auto simp add: \<R>\<^sub>d_from_\<sigma>_to_\<sigma>s_description)
next
  case (Cons \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As)
  from set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset, OF Cons.prems[simplified]]
  obtain \<sigma>1' \<sigma>s'' where \<open>\<sigma>s' = \<sigma>1' # \<sigma>s''\<close> \<open>\<sigma>1' \<in> \<R>\<^sub>d A1 \<sigma>1\<close>
    \<open>\<sigma>s'' \<in> \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A2 # As\<rrangle> (\<sigma>2 # \<sigma>s)\<close> by blast
  from Cons.hyps(3)[OF this(3)] this(1, 2)
  show ?case using less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc by simp auto
qed


lemma same_length_\<R>\<^sub>n\<^sub>d_iterated_combine\<^sub>n\<^sub>d_Sync_description:
  \<open>length \<sigma>s = length Bs \<Longrightarrow> \<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> Bs\<rrangle> \<sigma>s \<Longrightarrow>
   length \<sigma>s' = length Bs \<and> (\<forall>i < length Bs. \<sigma>s' ! i \<in> \<R>\<^sub>n\<^sub>d (Bs ! i) (\<sigma>s ! i))\<close>
proof (induct \<sigma>s Bs arbitrary: \<sigma>s' rule: induct_2_lists012)
  case Nil thus ?case by simp
next
  case (single \<sigma>1 B1)
  thus ?case by (auto simp add: \<R>\<^sub>n\<^sub>d_from_\<sigma>_to_\<sigma>s_description)
next
  case (Cons \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As)
  from set_mp[OF \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset, OF Cons.prems[simplified]]
  obtain \<sigma>1' \<sigma>s'' where \<open>\<sigma>s' = \<sigma>1' # \<sigma>s''\<close> \<open>\<sigma>1' \<in> \<R>\<^sub>n\<^sub>d A1 \<sigma>1\<close>
    \<open>\<sigma>s'' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A2 # As\<rrangle> (\<sigma>2 # \<sigma>s)\<close> by blast
  from Cons.hyps(3)[OF this(3)] this(1, 2)
  show ?case using less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc by simp auto
qed



subsection \<open>Transmission of Properties\<close>

lemma finite_trans_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync:
  \<open>(\<And>A. A \<in> set As \<Longrightarrow> finite_trans A) \<Longrightarrow> finite_trans \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<close>
  by (induct As rule: induct_list012) 
    (auto simp add: \<sigma>_\<sigma>s_conv_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs finite_trans_def finite_image_set2)

lemma \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>d_Sync:
  \<open>(\<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A) \<Longrightarrow> \<rho>_disjoint_\<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<close>
  by (induct As rule: induct_list012)
    (simp_all add: \<rho>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync \<rho>_disjoint_\<epsilon>_def combine_Sync_\<epsilon>_def)

lemma \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync:
  \<open>(\<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A) \<Longrightarrow> \<rho>_disjoint_\<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<close>
  by (induct As rule: induct_list012)
    (simp_all add: \<rho>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync \<rho>_disjoint_\<epsilon>_def combine_Sync_\<epsilon>_def)

lemma at_most_1_elem_term_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync:
  \<open>(\<And>A. A \<in> set As \<Longrightarrow> at_most_1_elem_term A) \<Longrightarrow> at_most_1_elem_term \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<close>
  by (induct As rule: induct_list012,
      simp_all add: at_most_1_elem_term_def \<sigma>_\<sigma>s_conv_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs)
    fastforce


lemma same_length_indep_transmission_to_iterated_combine\<^sub>d_Sync:
  \<open>length \<sigma>s = length As \<Longrightarrow>
   (\<And>i j. i \<le> length As \<Longrightarrow> j \<le> length As \<Longrightarrow> i \<noteq> j \<Longrightarrow> 
   indep_enabl ((A\<^sub>0 # As) ! i) ((s\<^sub>0 # \<sigma>s) ! i) E ((A\<^sub>0 # As) ! j) ((s\<^sub>0 # \<sigma>s) ! j)) \<Longrightarrow>
   indep_enabl A\<^sub>0 s\<^sub>0 E \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil
  then show ?case by (simp add: indep_enablI)
next
  case (single \<sigma>\<^sub>1 A\<^sub>1)
  from single.prems[of 0 1] show ?case
    by (auto simp add: \<R>\<^sub>d_from_\<sigma>_to_\<sigma>s_description
        intro!: indep_enablI dest!: indep_enablD)
next
  case (Cons \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>s A\<^sub>1 A\<^sub>2 As)
  show ?case
  proof (rule indep_enablI)
    fix t\<^sub>0 ts assume assms : \<open>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0\<close> \<open>ts \<in> \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # A\<^sub>2 # As\<rrangle> (\<sigma>\<^sub>1 # \<sigma>\<^sub>2 # \<sigma>s)\<close>
    from assms(2) obtain t\<^sub>1 ts' where \<open>ts = t\<^sub>1 # ts'\<close>
      by (metis Cons.hyps(1) Zero_not_Suc length_Cons list.exhaust_sel list.size(3)
          same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description)
    with assms(2)[simplified, THEN set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset]]
    have \<open>ts' \<in> \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>2 # As\<rrangle> (\<sigma>\<^sub>2 # \<sigma>s)\<close> by simp

    have \<open>indep_enabl A\<^sub>0 s\<^sub>0 E \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>2 # As\<rrangle> (\<sigma>\<^sub>2 # \<sigma>s)\<close>
    proof (rule Cons.hyps(3))
      show \<open>i \<le> length (A\<^sub>2 # As) \<Longrightarrow> j \<le> length (A\<^sub>2 # As) \<Longrightarrow> i \<noteq> j \<Longrightarrow>
            indep_enabl ((A\<^sub>0 # A\<^sub>2 # As) ! i) ((s\<^sub>0 # \<sigma>\<^sub>2 # \<sigma>s) ! i) E
                            ((A\<^sub>0 # A\<^sub>2 # As) ! j) ((s\<^sub>0 # \<sigma>\<^sub>2 # \<sigma>s) ! j)\<close> for i j
        using Cons.prems[of \<open>if i = 0 then 0 else Suc i\<close> \<open>if j = 0 then 0 else Suc j\<close>]
        by (cases i; cases j) simp_all
    qed
    from this[THEN indep_enablD, OF assms(1) \<open>ts' \<in> \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>2 # As\<rrangle> (\<sigma>\<^sub>2 # \<sigma>s)\<close>]
    have \<open>\<epsilon> A\<^sub>0 t\<^sub>0 \<inter> \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>2 # As\<rrangle> ts' \<subseteq> E\<close> .
    moreover from Cons.prems[THEN indep_enablD, of 0 \<open>Suc 0\<close> t\<^sub>0 t\<^sub>1]
      assms(2)[simplified, THEN set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset]] assms(1)
    have \<open>\<epsilon> A\<^sub>0 t\<^sub>0 \<inter> \<epsilon> A\<^sub>1 t\<^sub>1 \<subseteq> E\<close> by (simp add: \<open>ts = t\<^sub>1 # ts'\<close>)
    ultimately show \<open>\<epsilon> A\<^sub>0 t\<^sub>0 \<inter> \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # A\<^sub>2 # As\<rrangle> ts \<subseteq> E\<close>
      by (auto simp add: \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync \<open>ts = t\<^sub>1 # ts'\<close> combine_Sync_\<epsilon>_def)
  qed
qed


lemma \<omega>_iterated_combine\<^sub>d_Sync :
  \<open>length \<sigma>s = length As \<Longrightarrow>
   \<omega> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s = (case those (map2 \<omega> As \<sigma>s) of \<diamond> \<Rightarrow> \<diamond>
    | \<lfloor>terms\<rfloor> \<Rightarrow> if card (set terms) = Suc 0 then \<lfloor>THE r. set terms = {r}\<rfloor> else \<diamond>)\<close>
  by (induct \<sigma>s As rule: induct_2_lists012)
    (auto simp add: \<sigma>_\<sigma>s_conv_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs card_1_singleton_iff the_equality split: option.split)

lemma \<omega>_iterated_combine\<^sub>n\<^sub>d_Sync :
  \<open>length \<sigma>s = length As \<Longrightarrow>
   \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s = (if As = [] then {} else {r. \<forall>i < length As. r \<in> \<omega> (As ! i) (\<sigma>s ! i)})\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by simp
next
  case (single \<sigma>1 A1)
  from length_Suc_conv show ?case
    by (auto simp add: \<sigma>_\<sigma>s_conv_defs)
next
  case (Cons \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As)
  show ?case (is \<open>_ = ?rhs \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As\<close>)
  proof (intro subset_antisym subsetI)
    fix r assume \<open>r \<in> \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A1 # A2 # As\<rrangle> (\<sigma>1 # \<sigma>2 # \<sigma>s)\<close>
    hence \<open>r \<in> \<omega> A1 \<sigma>1\<close> \<open>r \<in> \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A2 # As\<rrangle> (\<sigma>2 # \<sigma>s)\<close>
      by (simp_all add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs split: if_split_asm)
    from this(2) have \<open>\<forall>i<Suc (length As). r \<in> \<omega> ((A2 # As) ! i) ((\<sigma>2 # \<sigma>s) ! i)\<close>
      by (simp add: Cons.hyps(3))
    with \<open>r \<in> \<omega> A1 \<sigma>1\<close> show \<open>r \<in> ?rhs \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As\<close>
      by (auto simp add: less_Suc_eq_0_disj)
  next
    from Cons.hyps(3)
    show \<open>r \<in> ?rhs \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As \<Longrightarrow>
          r \<in> \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A1 # A2 # As\<rrangle> (\<sigma>1 # \<sigma>2 # \<sigma>s)\<close> for r
      by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs)
  qed
qed


subsection \<open>Normalization\<close>

lemma \<omega>_iterated_combine\<^sub>n\<^sub>d_Sync_det_ndet_conv:
  \<open>length \<sigma>s = length As \<Longrightarrow>
   \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s = \<omega> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil
  show ?case by (simp add: base_trans_det_ndet_conv(1))
next
  case (single \<sigma>1 A1)
  show ?case by (simp add: from_det_to_ndet_\<sigma>_\<sigma>s_conv_commute)
next
  case (Cons \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As)
  thus ?case
    by (auto simp add: det_ndet_conv_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs split: option.split)
qed

lemma \<tau>_iterated_combine\<^sub>n\<^sub>d_Sync_behaviour_when_indep:
  \<open>length \<sigma>s = length As \<Longrightarrow>
   (\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk>
    \<Longrightarrow> indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)) \<Longrightarrow> 
   \<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s e = \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s e\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil
  show ?case by simp
next
  case (single \<sigma>1 A1)
  show ?case by (simp add: from_det_to_ndet_\<sigma>_\<sigma>s_conv_commute(1))
next
  case (Cons \<sigma>1 \<sigma>2 \<sigma>s A1 A2 As)
  have * : \<open>\<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A2 # As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (\<sigma>2 # \<sigma>s) e =
            \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) (A2 # As)\<rrangle> (\<sigma>2 # \<sigma>s) e\<close>
  proof (rule Cons.hyps(3))
    show \<open>\<lbrakk>i < length (A2 # As); j < length (A2 # As); i \<noteq> j\<rbrakk>
          \<Longrightarrow> indep_enabl ((A2 # As) ! i) ((\<sigma>2 # \<sigma>s) ! i) E
                              ((A2 # As) ! j) ((\<sigma>2 # \<sigma>s) ! j)\<close> for i j
      using Cons.prems[of \<open>Suc i\<close> \<open>Suc j\<close>] by simp
  qed
  have \<open>\<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A1 # A2 # As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (\<sigma>1 # \<sigma>2 # \<sigma>s) e =
        \<tau> \<llangle>\<llangle>A1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A2 # As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (\<sigma>1 # \<sigma>2 # \<sigma>s) e\<close>
  proof (subst iterated_combine\<^sub>d_Sync.simps(3), rule \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep)
    show \<open>\<epsilon> A1 \<sigma>1 \<inter> \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A2 # As\<rrangle> (\<sigma>2 # \<sigma>s) \<subseteq> E\<close>
    proof (rule indep_enablD[OF _ \<R>\<^sub>d.init \<R>\<^sub>d.init])
      show \<open>indep_enabl A1 \<sigma>1 E \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A2 # As\<rrangle> (\<sigma>2 # \<sigma>s)\<close>
        by (simp add: Cons.hyps(1) Cons.prems order_le_less_trans
            same_length_indep_transmission_to_iterated_combine\<^sub>d_Sync)
    qed
  qed
  also have \<open>\<dots> = \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) (A1 # A2 # As)\<rrangle> (\<sigma>1 # \<sigma>2 # \<sigma>s) e\<close>
    by (use "*" in \<open>simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs \<epsilon>_simps\<close>)
      (metis empty_from_det_to_ndet_is_None_trans option.exhaust)
  finally show ?case .
qed



lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterated_combine\<^sub>n\<^sub>d_Sync_behaviour_when_indep:
  assumes same_length: \<open>length \<sigma>s = length As\<close>
    and indep: \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
                      indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
  shows \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d, rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id)
  show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow>
        \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s' e = \<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s' e\<close> for \<sigma>s' e
  proof (rule \<tau>_iterated_combine\<^sub>n\<^sub>d_Sync_behaviour_when_indep[symmetric])
    show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow> length \<sigma>s' = length As\<close>
      by (metis \<R>\<^sub>n\<^sub>d_from_det_to_ndet same_length same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description)
  next
    show \<open>\<lbrakk>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s; i < length As; j < length As; i \<noteq> j\<rbrakk>
          \<Longrightarrow> indep_enabl (As ! i) (\<sigma>s' ! i) E (As ! j) (\<sigma>s' ! j)\<close> for i j
      by (subst (asm) \<R>\<^sub>n\<^sub>d_from_det_to_ndet,
          drule same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description[OF same_length])
        (meson \<R>\<^sub>d_trans indep_enabl_def indep)
  qed
next
  show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow>
        \<omega> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s' = \<omega> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s'\<close> for \<sigma>s'
    by (metis \<R>\<^sub>n\<^sub>d_from_det_to_ndet \<omega>_iterated_combine\<^sub>n\<^sub>d_Sync_det_ndet_conv same_length
        same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description)
qed


lemma P_d_iterated_combine\<^sub>n\<^sub>d_Sync_behaviour_when_indep:
  assumes same_length: \<open>length \<sigma>s = length As\<close>
    and indep: \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
                      indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
  shows \<open>P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (fold P_nd_from_det_to_ndet_is_P_d, rule P_nd_eqI_strong_id)
  show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow>
        \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> \<sigma>s' e = \<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s' e\<close> for \<sigma>s' e
  proof (rule \<tau>_iterated_combine\<^sub>n\<^sub>d_Sync_behaviour_when_indep[symmetric])
    show \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow> length \<sigma>s' = length As\<close>
      by (metis \<R>\<^sub>n\<^sub>d_from_det_to_ndet same_length same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description)
  next
    show \<open>\<lbrakk>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s; i < length As; j < length As; i \<noteq> j\<rbrakk>
          \<Longrightarrow> indep_enabl (As ! i) (\<sigma>s' ! i) E (As ! j) (\<sigma>s' ! j)\<close> for i j
      by (subst (asm) \<R>\<^sub>n\<^sub>d_from_det_to_ndet,
          drule same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description[OF same_length])
        (meson \<R>\<^sub>d_trans indep_enabl_def indep)
  qed
qed



section \<open>Compactification Theorems\<close>

subsection \<open>Binary\<close>

subsubsection \<open>Pair\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync :
  fixes E :: \<open>'a set\<close> and A\<^sub>0 :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close>
  assumes \<rho>_disjoint_\<epsilon> : \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close>
    and at_most_1_elem_term : \<open>at_most_1_elem_term A\<^sub>0\<close> \<open>at_most_1_elem_term A\<^sub>1\<close>
  defines A_def: \<open>A \<equiv> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<close>      
  defines P_def: \<open>P \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d\<close> and Q_def: \<open>Q \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d\<close> and S_def: \<open>S \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  shows \<open>P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1 = S (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
proof -
  let ?f = \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) (\<lambda>\<sigma>'. case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>\<^sub>1) \<Rightarrow> P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1)\<close>
  note cartprod_rwrt = GlobalNdet_cartprod[of _ _ \<open>\<lambda>x y. _ (x, y)\<close>, simplified]
  note Ndet_and_Sync = Sync_distrib_GlobalNdet_left
    Sync_distrib_GlobalNdet_right
  note Mprefix_Sync_constant =
    SKIP_Sync_Mprefix Mprefix_Sync_SKIP
    STOP_Sync_Mprefix Mprefix_Sync_STOP
  note P_rec = restriction_fix_eq[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis[of A\<^sub>0], folded P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def P_def, THEN fun_cong]
  note Q_rec = restriction_fix_eq[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis[of A\<^sub>1], folded P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def Q_def, THEN fun_cong]
  have \<omega>_A : \<open>\<omega> A (\<sigma>\<^sub>0', \<sigma>\<^sub>1') = \<omega> A\<^sub>0 \<sigma>\<^sub>0' \<inter> \<omega> A\<^sub>1 \<sigma>\<^sub>1'\<close> for \<sigma>\<^sub>0' \<sigma>\<^sub>1'
    by (auto simp add: A_def combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs)
  have \<epsilon>_A : \<open>\<epsilon> A (\<sigma>\<^sub>0', \<sigma>\<^sub>1') = combine_sets_Sync (\<epsilon> A\<^sub>0 \<sigma>\<^sub>0') E (\<epsilon> A\<^sub>1 \<sigma>\<^sub>1')\<close> for \<sigma>\<^sub>0' \<sigma>\<^sub>1'
    by (simp add: A_def \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync combine_Sync_\<epsilon>_def)
  have Mprefix_Sync_Mprefix_for_procomata :
    \<open>\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b =
     (\<box>a\<in>(A - E - B) \<rightarrow> (P a \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b))                            \<box>
     (\<box>b\<in>(B - E - A) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> Q b))                            \<box>
     (\<box>x\<in>(A \<inter> B - E) \<rightarrow> (P x \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b) \<sqinter> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> Q x)) \<box>
     (\<box>x\<in>(A \<inter> B \<inter> E) \<rightarrow> (P x \<lbrakk>E\<rbrakk> Q x))\<close> (is ?eq) for A B and P Q :: \<open>'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof -
    have  * : \<open>\<box>a\<in>(A - E) \<rightarrow> (P a \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b) =
              (\<box>a\<in>(A - E - B) \<rightarrow> (P a \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b)) \<box>
              (\<box>a\<in>(A \<inter> B - E) \<rightarrow> (P a \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b))\<close>
      by (metis Diff_Int2 Diff_Int_distrib2 Mprefix_Un_distrib Un_Diff_Int)
    have ** : \<open>\<box>b\<in>(B - E) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> Q b) =
               (\<box>b\<in>(B - E - A) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> Q b)) \<box>
               (\<box>b\<in>(A \<inter> B - E) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> Q b))\<close>
      by (metis (no_types) Int_Diff Int_commute Mprefix_Un_distrib Un_Diff_Int)
    have \<open>\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b =
          (\<box>a\<in>(A - E - B) \<rightarrow> (P a \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b))    \<box>
          (\<box>b\<in>(B - E - A) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> Q b))    \<box>
          ((\<box>a\<in>(A \<inter> B - E) \<rightarrow> (P a \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b))   \<box>
           (\<box>b\<in>(A \<inter> B - E) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> Q b)))  \<box>
          (\<box>x\<in>(A \<inter> B \<inter> E) \<rightarrow> (P x \<lbrakk>E\<rbrakk> Q x))\<close>
      unfolding Mprefix_Sync_Mprefix
      by (auto simp add: "**" Det_assoc intro!: arg_cong[where f = \<open>\<lambda>P. P \<box> _\<close>])
        (subst (3) Det_commute, subst Det_assoc,
          auto simp add: "*" Det_commute intro: arg_cong[where f = \<open>\<lambda>P. P \<box> _\<close>])
    also have \<open>(\<box>a\<in>(A \<inter> B - E) \<rightarrow> (P a \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b)) \<box>
                (\<box>b\<in>(A \<inter> B - E) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> Q b)) =
                \<box>x\<in>(A \<inter> B - E) \<rightarrow> ((P x \<lbrakk>E\<rbrakk> \<box>b\<in>B \<rightarrow> Q b)) \<sqinter> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>E\<rbrakk> Q x)\<close>
      by (simp add: Mprefix_Det_Mprefix, rule mono_Mprefix_eq, simp)
    finally show ?thesis .
  qed
  show \<open>P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1 = S (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
  proof (rule fun_cong[of \<open>\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1\<close> _ \<open>(\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>, simplified])
    show \<open>(\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1) = S\<close>
    proof (rule restriction_fix_unique[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis[of A],
          symmetric, folded P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def S_def])
      show \<open>?f = (\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1)\<close>
      proof (rule ext, clarify)
        have \<rho>_disjoint_\<epsilon>_bis : \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {} \<Longrightarrow> \<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close>
          \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {} \<Longrightarrow> \<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close> for \<sigma>\<^sub>0 \<sigma>\<^sub>1
          by (simp_all add: \<rho>_simps \<rho>_disjoint_\<epsilon>D \<rho>_disjoint_\<epsilon>)
        show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1\<close> for \<sigma>\<^sub>0 \<sigma>\<^sub>1
        proof (cases \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close>; cases \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>)
          assume \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
          hence P_rec' : \<open>P \<sigma>\<^sub>0 = P_nd_step (\<epsilon> A\<^sub>0) (\<tau> A\<^sub>0) P \<sigma>\<^sub>0\<close>
            and Q_rec' : \<open>Q \<sigma>\<^sub>1 = P_nd_step (\<epsilon> A\<^sub>1) (\<tau> A\<^sub>1) Q \<sigma>\<^sub>1\<close>
            and S_rec' : \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) (\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1) (\<sigma>\<^sub>0, \<sigma>\<^sub>1) =
                        P_nd_step (\<epsilon> A) (\<tau> A) (\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1) (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
            by (simp_all add: P_rec[of \<sigma>\<^sub>0] Q_rec[of \<sigma>\<^sub>1] \<omega>_A)
          show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1\<close>
            unfolding P_rec' Q_rec' S_rec' Mprefix_Sync_Mprefix_for_procomata
            unfolding \<epsilon>_A Mprefix_Un_distrib
            by (intro arg_cong2[where f = \<open>(\<box>)\<close>] mono_Mprefix_eq, fold P_rec' Q_rec',
                auto simp add: A_def Ndet_and_Sync cartprod_rwrt
                combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs \<epsilon>_simps GlobalNdet_sets_commute[of \<open>\<tau> A\<^sub>1 _ _\<close>]
                simp flip: GlobalNdet_factorization_union
                intro!: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<sqinter>)\<close>])
        next
          assume \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
          from \<rho>_disjoint_\<epsilon>(1) \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close> have \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close>
            by (simp add: \<rho>_disjoint_\<epsilon>_def \<rho>_simps)
          have \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = \<box>b\<in>(\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 - E) \<rightarrow> (\<sqinter>\<sigma>\<^sub>1'\<in>\<tau> A\<^sub>1 \<sigma>\<^sub>1 b. (SKIPS (\<omega> A\<^sub>0 \<sigma>\<^sub>0) \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1'))\<close>
            by (auto simp add: \<omega>_A \<epsilon>_A \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close> \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> intro!: mono_Mprefix_eq,
                auto simp add: A_def combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close>
                \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> cartprod_rwrt P_rec[of \<sigma>\<^sub>0] intro!: mono_GlobalNdet_eq)
          also have \<open>\<dots> = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1\<close>
            by (unfold P_rec[of \<sigma>\<^sub>0] Q_rec[of \<sigma>\<^sub>1])
              (auto simp add: SKIPS_def Ndet_and_Sync Mprefix_Sync_constant \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close>
                GlobalNdet_Mprefix_distr GlobalNdet_sets_commute[of \<open>\<tau> A\<^sub>1 _ _\<close>] \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
                intro!: mono_Mprefix_eq mono_GlobalNdet_eq)
          finally show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = \<dots>\<close> .
        next
          assume \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close>
          from \<rho>_disjoint_\<epsilon>(2) \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close> have \<open>\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
            by (simp add: \<rho>_disjoint_\<epsilon>_def \<rho>_simps)
          have \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = \<box>a\<in>(\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 - E) \<rightarrow> (\<sqinter>\<sigma>\<^sub>0'\<in>\<tau> A\<^sub>0 \<sigma>\<^sub>0 a. (P \<sigma>\<^sub>0' \<lbrakk>E\<rbrakk> SKIPS (\<omega> A\<^sub>1 \<sigma>\<^sub>1)))\<close>
            by (auto simp add: \<omega>_A \<epsilon>_A \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> \<open>\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close> intro!: mono_Mprefix_eq,
                auto simp add: A_def combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close>
                \<open>\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close> cartprod_rwrt Q_rec[of \<sigma>\<^sub>1] intro!: mono_GlobalNdet_eq)
          also have \<open>\<dots> = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1\<close>
            by (unfold P_rec[of \<sigma>\<^sub>0] Q_rec[of \<sigma>\<^sub>1])
              (auto simp add: SKIPS_def Ndet_and_Sync Mprefix_Sync_constant \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close>
                GlobalNdet_Mprefix_distr GlobalNdet_sets_commute[of \<open>\<tau> A\<^sub>0 _ _\<close>] \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close>
                intro!: mono_Mprefix_eq mono_GlobalNdet_eq)
          finally show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = \<dots>\<close> .
        next
          assume \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close>
          with \<rho>_disjoint_\<epsilon> have \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> \<open>\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close>
            by (simp_all add: \<rho>_disjoint_\<epsilon>_def \<rho>_simps)
          from at_most_1_elem_term
          show \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {} \<Longrightarrow> \<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {} \<Longrightarrow> ?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> Q \<sigma>\<^sub>1\<close>
            by (auto simp add: \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close> \<open>\<omega> A\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}\<close> \<omega>_A P_rec[of \<sigma>\<^sub>0] Q_rec[of \<sigma>\<^sub>1]
                SKIPS_def Ndet_and_Sync cartprod_rwrt GlobalNdet_sets_commute[of \<open>\<omega> A\<^sub>0 _\<close>]
                \<epsilon>_A \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0 = {}\<close> \<open>\<epsilon> A\<^sub>1 \<sigma>\<^sub>1 = {}\<close> elim!: at_most_1_elem_termE)
        qed
      qed
    qed
  qed
qed

corollary P_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync) simp_all
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<close>
    by (simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
  if \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> and \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> and \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp flip: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also from that(1, 2) have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (auto intro: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_behaviour_when_indep \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>)
  finally show ?thesis .
qed

corollary P_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync:
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync, simp_all add: \<rho>_simps \<rho>_disjoint_\<epsilon>_def)
      (rule indep_enablI,
        use \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>[THEN indep_enablD] in \<open>simp add: \<epsilon>_simps\<close>)
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<close>
    by (simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  finally show ?thesis .
qed



subsubsection \<open>Pairlist\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
  if \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> \<open>at_most_1_elem_term A\<^sub>0\<close> \<open>at_most_1_elem_term A\<^sub>1\<close>
proof -
  from P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync that
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close> .
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (auto intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of \<open>\<lambda>(r, s). [r, s]\<close> _ \<open>(\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>, simplified] inj_onI)
      (auto simp add: combine_Sync_defs split: if_split_asm)
  finally show ?thesis .
qed

corollary P_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync) simp_all
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<close>
    by (simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
  if \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> and \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> and \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp flip: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also from that(1, 2) have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (auto intro: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>)
  finally show ?thesis .
qed

corollary P_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
  if \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync, simp_all)
      (rule indep_enablI,
        use \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>[THEN indep_enablD] in simp)
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<close>
    by (simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  finally show ?thesis .
qed



subsection \<open>Rlist\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1)\<close>
  if \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> \<open>at_most_1_elem_term A\<^sub>0\<close> \<open>at_most_1_elem_term A\<^sub>1\<close>
proof -
  from P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync that
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close> .
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1)\<close>
    by (auto intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of \<open>\<lambda>(r, s). r # s\<close> _ \<open>(\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>, simplified] inj_onI)
      (auto simp add: combine_Sync_defs split: if_split_asm)
  finally show ?thesis .
qed

corollary P_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1)\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync) simp_all
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<close>
    by (simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1)\<close>
  if \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> and \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> and \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp flip: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also from that(1, 2) have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1)\<close>
    by (auto intro: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>)
  finally show ?thesis .
qed

corollary P_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1)\<close>
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync, simp_all)
      (rule indep_enablI,
        use \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>[THEN indep_enablD] in simp)
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<close>
    by (simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  finally show ?thesis .
qed



subsection \<open>ListslenL\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync :
  assumes same_length_reach0 : \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> length \<sigma>\<^sub>0' = len\<^sub>0\<close>
    and \<rho>_disjoint_\<epsilon> : \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> \<open>at_most_1_elem_term A\<^sub>0\<close> \<open>at_most_1_elem_term A\<^sub>1\<close>
  shows \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
proof -
  from set_mp[OF \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_subset]
  have * : \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (\<sigma>\<^sub>0, \<sigma>\<^sub>1) \<Longrightarrow>
            \<exists>\<sigma>\<^sub>0' \<sigma>\<^sub>1'. \<sigma>' = (\<sigma>\<^sub>0', \<sigma>\<^sub>1') \<and> \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<and> \<sigma>\<^sub>1' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>1 \<sigma>\<^sub>1\<close> for \<sigma>' by fast
  from P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync assms(2-5)
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close> .
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by  (auto intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of \<open>\<lambda>(r, s). r @ s\<close> _ \<open>(\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>, simplified] inj_onI
        dest!: "*" same_length_reach0 simp add: same_length_reach0 image_iff)
      (auto simp add: combine_Sync_defs \<epsilon>_simps split: if_split_asm,
        (metis SigmaI UnCI case_prod_conv insertI1)+)
  finally show ?thesis .
qed

corollary P_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
  if \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> length \<sigma>\<^sub>0' = len\<^sub>0\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync) (simp_all add: that)
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<close>
    by (simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
  if \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> length \<sigma>\<^sub>0' = len\<^sub>0\<close>
    \<open>\<rho>_disjoint_\<epsilon> A\<^sub>0\<close> \<open>\<rho>_disjoint_\<epsilon> A\<^sub>1\<close> \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp flip: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also from that(1-3) have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (auto simp add: \<R>\<^sub>n\<^sub>d_from_det_to_ndet intro!: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_behaviour_when_indep that(1, 4))
  finally show ?thesis .
qed

corollary P_d_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync :
  \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
  if \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> length \<sigma>\<^sub>0' = len\<^sub>0\<close> \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
proof -
  have \<open>P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<llangle>A\<^sub>1\<rrangle>\<^sub>d \<sigma>\<^sub>1 =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d \<sigma>\<^sub>1\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 @ \<sigma>\<^sub>1)\<close>
    by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync) (simp_all add: that)
  also have \<open>\<llangle>A\<^sub>0\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr> \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle> = \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<close>
    by (simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs, intro ext, simp)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d = P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
  finally show ?thesis .
qed



subsection \<open>Multiple\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync:
  \<open>\<lbrakk>length \<sigma>s = length As; \<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A;
    \<And>A. A \<in> set As \<Longrightarrow> at_most_1_elem_term A\<rbrakk>
   \<Longrightarrow> \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp, subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec, simp)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case
    by (auto simp add: \<sigma>_\<sigma>s_conv_defs intro!: inj_onI P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>0 # A\<^sub>1 # As)). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip (\<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>1 # As)). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close> by simp
  also have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip (\<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>1 # As)). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> =
             P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (rule Cons.hyps(3)) (simp_all add: Cons.prems)
  also have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<lbrakk>E\<rbrakk> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>1 # \<sigma>s) =
             P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle>\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync
        [OF _ \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync
          _ at_most_1_elem_term_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync])
      (simp_all add: Cons.prems)
  also have \<open>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle>\<rrangle> = \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>0 # A\<^sub>1 # As\<rrangle>\<close> by simp
  finally show ?case .
qed

lemma P_nd_compactification_Sync:
  \<open>length \<sigma>s = length As \<Longrightarrow>
   \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp, subst P_nd_rec, simp)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case
    by (simp add: P_nd_from_\<sigma>_to_\<sigma>s_is_P_nd)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As) thus ?case
    by (simp add: P_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync)
qed

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync:
  \<open>\<lbrakk>length \<sigma>s = length As; \<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A;
    \<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
          indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<rbrakk> \<Longrightarrow>
   \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp, subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec, simp)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case
    by (auto simp add: RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d \<sigma>_\<sigma>s_conv_defs
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
  moreover have \<open>\<rho>_disjoint_\<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle>\<close>
    by (meson \<rho>_disjoint_\<epsilon> \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>d_Sync)
  moreover have \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (metis Cons.hyps(1) Cons.prems(2) length_Cons less_Suc_eq_le
        same_length_indep_transmission_to_iterated_combine\<^sub>d_Sync)
  ultimately show ?case 
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync
        Cons.hyps(3)[OF \<rho>_disjoint_\<epsilon> indep_enabl, simplified])
qed

lemma P_d_compactification_Sync:
  \<open>\<lbrakk>length \<sigma>s = length As;
    \<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
          indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<rbrakk> \<Longrightarrow>
   \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<llangle>A\<rrangle>\<^sub>d \<sigma> = P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp, subst P_d_rec, simp)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case
    by (simp, subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>)
      (auto simp add: RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d \<sigma>_\<sigma>s_conv_defs
        intro!: inj_onI P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI_strong split: option.split)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  have indep_enabl :
    \<open>\<lbrakk>i < length (A\<^sub>1 # As); j < length (A\<^sub>1 # As); i \<noteq> j\<rbrakk> \<Longrightarrow>
     indep_enabl ((A\<^sub>1 # As) ! i) ((\<sigma>\<^sub>1 # \<sigma>s) ! i) E ((A\<^sub>1 # As) ! j) ((\<sigma>\<^sub>1 # \<sigma>s) ! j)\<close> for i j
    by (metis Cons.prems Suc_less_eq length_Cons nat.inject nth_Cons_Suc)
  have \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (metis Cons.hyps(1) Cons.prems length_Cons less_Suc_eq_le
        same_length_indep_transmission_to_iterated_combine\<^sub>d_Sync)
  thus ?case 
    by (simp add: P_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync
        Cons.hyps(3)[OF indep_enabl, simplified])
qed




corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync_order_is_arbitrary:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As'\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s'\<close>
  if \<open>length \<sigma>s = length As\<close> \<open>length \<sigma>s' = length As'\<close>
    \<open>mset (zip \<sigma>s As) = mset (zip \<sigma>s' As')\<close> 
    \<open>\<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A\<close>
    \<open>\<And>A. A \<in> set As \<Longrightarrow> at_most_1_elem_term A\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip \<sigma>s As). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync[OF that(1, 4, 5), symmetric])
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip \<sigma>s' As'). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
    by (simp only: that(3))
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As'\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s'\<close>
  proof (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync[OF that(2)])
    show \<open>A \<in> set As' \<Longrightarrow> \<rho>_disjoint_\<epsilon> A\<close> for A
      by (metis in_set_impl_in_set_zip2 set_mset_mset set_zip_rightD that(2-4))
  next
    show \<open>A \<in> set As' \<Longrightarrow> at_most_1_elem_term A\<close> for A
      by (metis in_set_impl_in_set_zip2 set_mset_mset set_zip_rightD that(2, 3, 5))
  qed
  finally show ?thesis .
qed

corollary P_nd_compactification_Sync_order_is_arbitrary:
  \<open>P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As'\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s'\<close>
  if \<open>length \<sigma>s = length As\<close> \<open>length \<sigma>s' = length As'\<close>
    \<open>mset (zip \<sigma>s As) = mset (zip \<sigma>s' As')\<close> 
proof -
  have \<open>P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip \<sigma>s As). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
    by (fact P_nd_compactification_Sync[OF that(1), symmetric])
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip \<sigma>s' As'). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
    by (simp only: that(3))
  also have \<open>\<dots> = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As'\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s'\<close>
    by (fact P_nd_compactification_Sync[OF that(2)])
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync_order_is_arbitrary:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As'\<rrangle>\<rrangle>\<^sub>d \<sigma>s'\<close>
  if \<open>length \<sigma>s = length As\<close> \<open>length \<sigma>s' = length As'\<close>
    \<open>mset (zip \<sigma>s As) = mset (zip \<sigma>s' As')\<close> 
    \<open>\<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A\<close>
    \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
            indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip \<sigma>s As). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync[OF that(1, 4, 5), symmetric])
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip \<sigma>s' As'). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
    by (simp only: that(3))
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As'\<rrangle>\<rrangle>\<^sub>d \<sigma>s'\<close>
  proof (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync[OF that(2)])
    show \<open>A \<in> set As' \<Longrightarrow> \<rho>_disjoint_\<epsilon> A\<close> for A
      by (metis in_set_impl_in_set_zip2 set_mset_mset set_zip_rightD that(2-4))
  next
    from \<open>length \<sigma>s = length As\<close> \<open>length \<sigma>s' = length As'\<close> \<open>mset (zip \<sigma>s As) = mset (zip \<sigma>s' As')\<close>
    obtain n where * : \<open>length \<sigma>s = n\<close> \<open>length \<sigma>s' = n\<close> \<open>length As = n\<close> \<open>length As' = n\<close>
      by (metis length_zip min_less_iff_conj nat_neq_iff size_mset)
    from that(3)[symmetric, THEN permutation_Ex_bij] obtain f
      where ** : \<open>bij_betw f {..<n} {..<n}\<close>
        \<open>i < n \<Longrightarrow> zip \<sigma>s' As' ! i = zip \<sigma>s As ! f i\<close> for i by (auto simp add: "*")
    { fix i assume \<open>i < n\<close>
      hence \<open>f i < n\<close> using "**"(1) bij_betwE by blast
      from \<open>i < n\<close> have \<open>zip \<sigma>s' As' ! i = (\<sigma>s' ! i, As' ! i)\<close> by (simp add: "*"(2, 4))
      moreover from \<open>f i < n\<close> have \<open>zip \<sigma>s As ! f i = (\<sigma>s ! f i, As ! f i)\<close>
        by (simp add: "*"(1, 3))
      ultimately have \<open>\<sigma>s' ! i = \<sigma>s ! f i\<close> \<open>As' ! i = As ! f i\<close>
        using "**"(2)[OF \<open>i < n\<close>] by simp_all
    } note *** = this
    fix i j assume \<open>i < length As'\<close> \<open>j < length As'\<close> \<open>i \<noteq> j\<close>
    hence \<open>i < n\<close> \<open>j < n\<close> by (simp_all add: "*"(2, 4))
    with bij_betw_imp_surj_on[OF "**"(1)] bij_betw_imp_inj_on[OF "**"(1)] \<open>i \<noteq> j\<close>
    have \<open>f i < length As\<close> \<open>f j < length As\<close> \<open>f i \<noteq> f j\<close>
      by (auto simp add: "*" dest: inj_onD)
    from that(5)[OF this]
    show \<open>indep_enabl (As' ! i) (\<sigma>s' ! i) E (As' ! j) (\<sigma>s' ! j)\<close>
      by (simp add: "***"(1, 2) \<open>i < n\<close> \<open>j < n\<close>)
  qed
  finally show ?thesis .
qed

corollary P_d_compactification_Sync_order_is_arbitrary:
  \<open>P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s = P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As'\<rrangle>\<rrangle>\<^sub>d \<sigma>s'\<close>
  if \<open>length \<sigma>s = length As\<close> \<open>length \<sigma>s' = length As'\<close>
    \<open>mset (zip \<sigma>s As) = mset (zip \<sigma>s' As')\<close> 
    \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
            indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
proof -
  have \<open>P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip \<sigma>s As). P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
    by (rule P_d_compactification_Sync[OF that(1, 4), symmetric])
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip \<sigma>s' As'). P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
    by (simp only: that(3))
  also have \<open>\<dots> = P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As'\<rrangle>\<rrangle>\<^sub>d \<sigma>s'\<close>
  proof (rule P_d_compactification_Sync[OF that(2)])
    from \<open>length \<sigma>s = length As\<close> \<open>length \<sigma>s' = length As'\<close> \<open>mset (zip \<sigma>s As) = mset (zip \<sigma>s' As')\<close>
    obtain n where * : \<open>length \<sigma>s = n\<close> \<open>length \<sigma>s' = n\<close> \<open>length As = n\<close> \<open>length As' = n\<close>
      by (metis length_zip min_less_iff_conj nat_neq_iff size_mset)
    from that(3)[symmetric, THEN permutation_Ex_bij] obtain f
      where ** : \<open>bij_betw f {..<n} {..<n}\<close>
        \<open>i < n \<Longrightarrow> zip \<sigma>s' As' ! i = zip \<sigma>s As ! f i\<close> for i by (auto simp add: "*")
    { fix i assume \<open>i < n\<close>
      hence \<open>f i < n\<close> using "**"(1) bij_betwE by blast
      from \<open>i < n\<close> have \<open>zip \<sigma>s' As' ! i = (\<sigma>s' ! i, As' ! i)\<close> by (simp add: "*"(2, 4))
      moreover from \<open>f i < n\<close> have \<open>zip \<sigma>s As ! f i = (\<sigma>s ! f i, As ! f i)\<close>
        by (simp add: "*"(1, 3))
      ultimately have \<open>\<sigma>s' ! i = \<sigma>s ! f i\<close> \<open>As' ! i = As ! f i\<close>
        using "**"(2)[OF \<open>i < n\<close>] by simp_all
    } note *** = this
    fix i j assume \<open>i < length As'\<close> \<open>j < length As'\<close> \<open>i \<noteq> j\<close>
    hence \<open>i < n\<close> \<open>j < n\<close> by (simp_all add: "*"(2, 4))
    with bij_betw_imp_surj_on[OF "**"(1)] bij_betw_imp_inj_on[OF "**"(1)] \<open>i \<noteq> j\<close>
    have \<open>f i < length As\<close> \<open>f j < length As\<close> \<open>f i \<noteq> f j\<close>
      by (auto simp add: "*" dest: inj_onD)
    from that(4)[OF this]
    show \<open>indep_enabl (As' ! i) (\<sigma>s' ! i) E (As' ! j) (\<sigma>s' ! j)\<close>
      by (simp add: "***"(1, 2) \<open>i < n\<close> \<open>j < n\<close>)
  qed
  finally show ?thesis .
qed



section \<open>Derived Versions\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync_upt_version:
  \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> P \<in># mset (map Q [0..<n]). P = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map A [0..<n]\<rrangle>\<rrangle>\<^sub>n\<^sub>d (replicate n 0)\<close>
  if \<open>\<And>i. i < n \<Longrightarrow> \<rho>_disjoint_\<epsilon> (A i)\<close>
    \<open>\<And>i. i < n \<Longrightarrow> at_most_1_elem_term (A i)\<close>
    \<open>\<And>i. i < n \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 = Q i\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> P \<in># mset (map Q [0..<n]). P = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i \<in># (mset_set {0..<n}). Q i\<close>
    by (auto intro: mono_MultiSync_eq2)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i \<in># (mset_set {0..<n}). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0\<close>
    by (auto simp add: that(3) intro: mono_MultiSync_eq)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate n 0) (map A [0..<n])). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
  proof (induct n rule: nat_induct_012)
    case (Suc k)
    have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> i\<in>#mset_set {0..<Suc k}. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 =
          P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A k\<rrangle>\<^sub>n\<^sub>d 0 \<lbrakk>E\<rbrakk> \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i\<in>#mset_set {0..<k}. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0\<close>
      by (subst atLeastLessThanSuc, simp, rule MultiSync_add)
        (metis Suc.hyps(1) atLeastLessThan_empty_iff2 finite_lessThan
          gr0_conv_Suc lessThan_atLeast0 mset_set_empty_iff order_less_le_trans)
    also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A k\<rrangle>\<^sub>n\<^sub>d 0 \<lbrakk>E\<rbrakk>
                    \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate k 0) (map A [0..<k])). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
      by (simp only: Suc.hyps(2))
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate (Suc k) 0) (map A [0..<Suc k])). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
      by (simp flip: replicate_append_same, subst MultiSync_add)
        (use Suc.hyps(1) in auto)
    finally show ?case .
  qed (simp_all add: atLeastLessThanSuc Sync_commute)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map A [0..<n]\<rrangle>\<rrangle>\<^sub>n\<^sub>d (replicate n 0)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync)
      (auto simp add: that(1, 2))
  finally show ?thesis .
qed

lemma P_nd_compactification_Sync_upt_version:
  \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> P \<in># mset (map Q [0..<n]). P = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map A [0..<n]\<rrangle>\<rrangle>\<^sub>n\<^sub>d (replicate n 0)\<close>
  if \<open>\<And>i. i < n \<Longrightarrow> P\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 = Q i\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> P \<in># mset (map Q [0..<n]). P = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i \<in># (mset_set {0..<n}). Q i\<close>
    by (auto intro: mono_MultiSync_eq2)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i \<in># (mset_set {0..<n}). P\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0\<close>
    by (auto simp add: that(1) intro: mono_MultiSync_eq)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate n 0) (map A [0..<n])). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
  proof (induct n rule: nat_induct_012)
    case (Suc k)
    have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> i\<in>#mset_set {0..<Suc k}. P\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0 =
          P\<llangle>A k\<rrangle>\<^sub>n\<^sub>d 0 \<lbrakk>E\<rbrakk> \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i\<in>#mset_set {0..<k}. P\<llangle>A i\<rrangle>\<^sub>n\<^sub>d 0\<close>
      by (subst atLeastLessThanSuc, simp, rule MultiSync_add)
        (metis Suc.hyps(1) atLeastLessThan_empty_iff2 finite_lessThan
          gr0_conv_Suc lessThan_atLeast0 mset_set_empty_iff order_less_le_trans)
    also have \<open>\<dots> = P\<llangle>A k\<rrangle>\<^sub>n\<^sub>d 0 \<lbrakk>E\<rbrakk> \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate k 0) (map A [0..<k])). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
      by (simp only: Suc.hyps(2))
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate (Suc k) 0) (map A [0..<Suc k])). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
      by (simp flip: replicate_append_same, subst MultiSync_add)
        (use Suc.hyps(1) in auto)
    finally show ?case .
  qed (simp_all add: atLeastLessThanSuc Sync_commute)
  also have \<open>\<dots> = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map A [0..<n]\<rrangle>\<rrangle>\<^sub>n\<^sub>d (replicate n 0)\<close>
    by (auto intro: P_nd_compactification_Sync)
  finally show ?thesis .
qed

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync_upt_version:
  \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> P \<in># mset (map Q [0..<n]). P = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map A [0..<n]\<rrangle>\<rrangle>\<^sub>d (replicate n 0)\<close>
  if \<open>\<And>i. i < n \<Longrightarrow> \<rho>_disjoint_\<epsilon> (A i)\<close>
    \<open>\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> indep_enabl (A i) 0 E (A j) 0\<close>
    \<open>\<And>i. i < n \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>d 0 = Q i\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> P \<in># mset (map Q [0..<n]). P = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i \<in># (mset_set {0..<n}). Q i\<close>
    by (auto intro: mono_MultiSync_eq2)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i \<in># (mset_set {0..<n}). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>d 0\<close>
    by (auto simp add: that(3) intro: mono_MultiSync_eq)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate n 0) (map A [0..<n])). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
  proof (induct n rule: nat_induct_012)
    case (Suc k)
    have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> i\<in>#mset_set {0..<Suc k}. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>d 0 =
          P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A k\<rrangle>\<^sub>d 0 \<lbrakk>E\<rbrakk> \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i\<in>#mset_set {0..<k}. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A i\<rrangle>\<^sub>d 0\<close>
      by (subst atLeastLessThanSuc, simp, rule MultiSync_add)
        (metis Suc.hyps(1) atLeastLessThan_empty_iff2 finite_lessThan
          gr0_conv_Suc lessThan_atLeast0 mset_set_empty_iff order_less_le_trans)
    also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A k\<rrangle>\<^sub>d 0 \<lbrakk>E\<rbrakk>
                    \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate k 0) (map A [0..<k])). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
      by (simp only: Suc.hyps(2))
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate (Suc k) 0) (map A [0..<Suc k])). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
      by (simp flip: replicate_append_same, subst MultiSync_add)
        (use Suc.hyps(1) in auto)
    finally show ?case .
  qed (simp_all add: atLeastLessThanSuc Sync_commute)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map A [0..<n]\<rrangle>\<rrangle>\<^sub>d (replicate n 0)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync)
      (auto simp add: that(1, 2))
  finally show ?thesis .
qed

lemma P_d_compactification_Sync_upt_version:
  \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> P \<in># mset (map Q [0..<n]). P = P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map A [0..<n]\<rrangle>\<rrangle>\<^sub>d (replicate n 0)\<close>
  if \<open>\<And>i. i < n \<Longrightarrow> P\<llangle>A i\<rrangle>\<^sub>d 0 = Q i\<close>
    \<open>\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> indep_enabl (A i) 0 E (A j) 0\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> P \<in># mset (map Q [0..<n]). P = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i \<in># (mset_set {0..<n}). Q i\<close>
    by (auto intro: mono_MultiSync_eq2)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i \<in># (mset_set {0..<n}). P\<llangle>A i\<rrangle>\<^sub>d 0\<close>
    by (auto simp add: that(1) intro: mono_MultiSync_eq)
  also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate n 0) (map A [0..<n])). P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
  proof (induct n rule: nat_induct_012)
    case (Suc k)
    have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> i\<in>#mset_set {0..<Suc k}. P\<llangle>A i\<rrangle>\<^sub>d 0 =
          P\<llangle>A k\<rrangle>\<^sub>d 0 \<lbrakk>E\<rbrakk> \<^bold>\<lbrakk>E\<^bold>\<rbrakk> i\<in>#mset_set {0..<k}. P\<llangle>A i\<rrangle>\<^sub>d 0\<close>
      by (subst atLeastLessThanSuc, simp, rule MultiSync_add)
        (metis Suc.hyps(1) atLeastLessThan_empty_iff2 finite_lessThan
          gr0_conv_Suc lessThan_atLeast0 mset_set_empty_iff order_less_le_trans)
    also have \<open>\<dots> = P\<llangle>A k\<rrangle>\<^sub>d 0 \<lbrakk>E\<rbrakk> \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate k 0) (map A [0..<k])). P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
      by (simp only: Suc.hyps(2))
    also have \<open>\<dots> = \<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A)\<in>#mset (zip (replicate (Suc k) 0) (map A [0..<Suc k])). P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
      by (simp flip: replicate_append_same, subst MultiSync_add)
        (use Suc.hyps(1) in auto)
    finally show ?case .
  qed (simp_all add: atLeastLessThanSuc Sync_commute)
  also have \<open>\<dots> = P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> map A [0..<n]\<rrangle>\<rrangle>\<^sub>d (replicate n 0)\<close>
    by (rule P_d_compactification_Sync) (simp_all add: that(2))
  finally show ?thesis .
qed



section \<open>More on Iterated Combine\<close>

lemma \<epsilon>_iterated_combine\<^sub>n\<^sub>d_Sync_general_form:
  \<open>length \<sigma>s = length As \<Longrightarrow> \<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s =
   (if As = [] then {}
    else (\<Union>i < length As. \<epsilon> (As ! i) (\<sigma>s ! i)) - E \<union> (\<Inter>i < length As. \<epsilon> (As ! i) (\<sigma>s ! i)))\<close>
  for As :: \<open>('\<sigma>, 'e, 'r) A\<^sub>n\<^sub>d list\<close>
proof (subst \<epsilon>_iterated_combine\<^sub>n\<^sub>d_Sync, assumption, induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by simp
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case by auto
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  define U and I
    where U_def : \<open>U As \<sigma>s \<equiv> \<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
      and I_def : \<open>I As \<sigma>s \<equiv> \<Inter>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
    for As :: \<open>('\<sigma>, 'e, 'r) A\<^sub>n\<^sub>d list\<close> and \<sigma>s
  have * : \<open>U (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) = \<epsilon> A\<^sub>0 \<sigma>\<^sub>0 \<union> U (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (auto simp add: U_def nth_Cons split: nat.split_asm)
  have ** : \<open>I (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) = \<epsilon> A\<^sub>0 \<sigma>\<^sub>0 \<inter> I (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (auto simp add: I_def nth_Cons split: nat.splits)
  have \<open>iterated_combine\<^sub>n\<^sub>d_Sync_\<epsilon> (A\<^sub>0 # A\<^sub>1 # As) E (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) =
        combine_sets_Sync (\<epsilon> A\<^sub>0 \<sigma>\<^sub>0) E (U (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s) - E \<union> (I (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s)))\<close>
    by (simp add: U_def I_def Cons.hyps(3))
  also have \<open>\<dots> = U (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) - E \<union> I (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s)\<close>
    unfolding "*" "**" by (auto simp add: U_def I_def)
  finally show ?case by (simp add: U_def I_def)
qed

lemma \<epsilon>_iterated_combine\<^sub>d_Sync_general_form:
  \<open>length \<sigma>s = length As \<Longrightarrow> \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s =
   (if As = [] then {}
    else (\<Union>i < length As. \<epsilon> (As ! i) (\<sigma>s ! i)) - E \<union> (\<Inter>i < length As. \<epsilon> (As ! i) (\<sigma>s ! i)))\<close>
  for As :: \<open>('\<sigma>, 'e, 'r) A\<^sub>d list\<close>
proof (subst \<epsilon>_iterated_combine\<^sub>d_Sync, assumption, induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by simp
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case by auto
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  define U and I
    where U_def : \<open>U As \<sigma>s \<equiv> \<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
      and I_def : \<open>I As \<sigma>s \<equiv> \<Inter>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
    for As :: \<open>('\<sigma>, 'e, 'r) A\<^sub>d list\<close> and \<sigma>s
  have * : \<open>U (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) = \<epsilon> A\<^sub>0 \<sigma>\<^sub>0 \<union> U (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (auto simp add: U_def nth_Cons split: nat.split_asm)
  have ** : \<open>I (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) = \<epsilon> A\<^sub>0 \<sigma>\<^sub>0 \<inter> I (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s)\<close>
    by (auto simp add: I_def nth_Cons split: nat.splits)
  have \<open>iterated_combine\<^sub>d_Sync_\<epsilon> (A\<^sub>0 # A\<^sub>1 # As) E (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) =
        combine_sets_Sync (\<epsilon> A\<^sub>0 \<sigma>\<^sub>0) E (U (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s) - E \<union> (I (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s)))\<close>
    by (simp add: U_def I_def Cons.hyps(3))
  also have \<open>\<dots> = U (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) - E \<union> I (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s)\<close>
    unfolding "*" "**" by (auto simp add: U_def I_def)
  finally show ?case by (simp add: U_def I_def)
qed


lemma \<tau>_iterated_combine\<^sub>n\<^sub>d_Sync_general_form:
  \<open>\<lbrakk>length \<sigma>s = length As; \<sigma>s' \<in> \<tau> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s a; i < length As\<rbrakk> \<Longrightarrow>
   \<sigma>s' ! i \<in> insert (\<sigma>s ! i) (\<tau> (As ! i) (\<sigma>s ! i) a)\<close>
proof (induct \<sigma>s As arbitrary: \<sigma>s' i rule: induct_2_lists012)
  case Nil thus ?case by simp
next
  case (single \<sigma>\<^sub>0 A\<^sub>0)
  from single.prems show ?case by (auto simp add: behaviour_\<sigma>_\<sigma>s_conv)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  from \<open>length \<sigma>s = length As\<close> have \<open>length (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) = length (A\<^sub>0 # A\<^sub>1 # As)\<close> by simp
  from same_length_\<R>\<^sub>n\<^sub>d_iterated_combine\<^sub>n\<^sub>d_Sync_description[OF this]
  have \<open>length \<sigma>s' = length (A\<^sub>0 # A\<^sub>1 # As)\<close>
    by (metis Cons.prems(1) \<R>\<^sub>n\<^sub>d.init \<R>\<^sub>n\<^sub>d.step)
  then obtain \<sigma>\<^sub>0' \<sigma>\<^sub>1' \<sigma>s'' where \<open>\<sigma>s' = \<sigma>\<^sub>0' # \<sigma>\<^sub>1' # \<sigma>s''\<close> by (metis length_Suc_conv)
  with Cons.prems Cons.hyps(3)[of \<open>\<sigma>\<^sub>1' # \<sigma>s''\<close> \<open>nat.pred i\<close>] show ?case
    by (auto simp add: combine_Sync_defs nth_Cons split: if_split_asm nat.splits)
qed


lemma \<tau>_iterated_combine\<^sub>d_Sync_general_form:
  \<open>length \<sigma>s = length As \<Longrightarrow>
   \<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s a =
   (if As = [] then \<diamond> else
    if a \<in> (\<Union>i < length As. \<epsilon> (As ! i) (\<sigma>s ! i)) - E \<union> (\<Inter>i < length As. \<epsilon> (As ! i) (\<sigma>s ! i))
    then \<lfloor>map2 (\<lambda>\<sigma> A. if a \<in> \<epsilon> A \<sigma> then \<lceil>\<tau> A \<sigma> a\<rceil> else \<sigma>) \<sigma>s As\<rfloor> else \<diamond>)\<close>
  for As :: \<open>('\<sigma>, 'e, 'r) A\<^sub>d list\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by simp
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case by (auto simp add: behaviour_\<sigma>_\<sigma>s_conv \<epsilon>_simps)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  let ?U = \<open>\<lambda>As \<sigma>s. \<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
  let ?I = \<open>\<lambda>As \<sigma>s. \<Inter>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
  show ?case
  proof (split if_split, split if_split, intro conjI impI)
    show \<open>A\<^sub>0 # A\<^sub>1 # As = [] \<Longrightarrow> \<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>0 # A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) a = \<diamond>\<close>
      and \<open>A\<^sub>0 # A\<^sub>1 # As = [] \<Longrightarrow> \<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>0 # A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) a = \<diamond>\<close> by simp_all
  next
    assume \<open>a \<notin> ?U (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) - E \<union> ?I (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s)\<close>
    hence \<open>a \<notin> \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>0 # A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s)\<close>
      by (subst \<epsilon>_iterated_combine\<^sub>d_Sync_general_form)
        (simp_all add: Cons.hyps(1))
    thus \<open>\<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>0 # A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) a = \<diamond>\<close>
      by (simp add: \<epsilon>_simps)
  next
    assume * : \<open>a \<in> ?U (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) - E \<union> ?I (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s)\<close>
    have ** : \<open>?U (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) = \<epsilon> A\<^sub>0 \<sigma>\<^sub>0 \<union> ?U (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s)\<close>
      by (auto simp add: nth_Cons split: nat.split_asm)
    have *** : \<open>?I (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) = \<epsilon> A\<^sub>0 \<sigma>\<^sub>0 \<inter> ?I (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s)\<close>
      by (auto simp add: nth_Cons split: nat.splits)
    have **** : \<open>?U (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) - E \<union> ?I (A\<^sub>0 # A\<^sub>1 # As) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) =
                 combine_sets_Sync (\<epsilon> A\<^sub>0 \<sigma>\<^sub>0) E (?U (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s) - E \<union> ?I (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s))\<close>
      unfolding "**" "***" by auto
    have $ : \<open>?U (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s) - E \<union> ?I (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s) = \<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>1 # \<sigma>s)\<close>
      by (subst \<epsilon>_iterated_combine\<^sub>d_Sync_general_form)
        (simp_all add: Cons.hyps(1))

    from Cons.hyps(1) have \<open>a \<notin> ?U As \<sigma>s \<Longrightarrow>
            map2 (\<lambda>\<sigma> A. if a \<in> \<epsilon> A \<sigma> then \<lceil>\<tau> A \<sigma> a\<rceil> else \<sigma>) \<sigma>s As = \<sigma>s\<close>
      by (induct \<sigma>s As rule: induct_2_lists012)
        (auto simp add: \<epsilon>_simps lessThan_def, fastforce)
    moreover have \<open>?U As \<sigma>s \<subseteq> ?U (A\<^sub>1 # As) (\<sigma>\<^sub>1 # \<sigma>s)\<close> by force
    ultimately show \<open>\<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> A\<^sub>0 # A\<^sub>1 # As\<rrangle> (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) a =
                  \<lfloor>map2 (\<lambda>x y. if a \<in> \<epsilon> y x then \<lceil>\<tau> y x a\<rceil> else x) (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>0 # A\<^sub>1 # As)\<rfloor>\<close>
      using "*" unfolding "****" "$"
      by (simp add: \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync combine_Sync_\<epsilon>_def, safe,
          auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs \<epsilon>_simps Cons.hyps(3) lessThan_def subset_iff
          split: option.splits if_splits)
        (metis (no_types, lifting) not_less_eq nth_Cons_Suc)
  qed
qed


lemma indep_implies_only_one_enabled':
  \<open>\<exists>!i. i < length As \<and> a \<in> \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
  if \<open>length \<sigma>s = length As\<close>
    and \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
            \<epsilon> (As ! i) (\<sigma>s ! i) \<inter> \<epsilon> (As ! j) (\<sigma>s ! j) \<subseteq> E\<close>
    and \<open>a \<in> (\<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i)) - E\<close>
proof (rule ex_ex1I)
  from that(3) show \<open>\<exists>i<length As. a \<in> \<epsilon> (As ! i) (\<sigma>s ! i)\<close> by auto
next
  fix i j assume \<open>i < length As \<and> a \<in> \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
    \<open>j < length As \<and> a \<in> \<epsilon> (As ! j) (\<sigma>s ! j)\<close>
  moreover from that(3) have \<open>a \<notin> E\<close> by blast
  ultimately show \<open>i = j\<close> using that(2)[of i j] by auto
qed

lemma indep_implies_only_one_enabled:
  \<open>\<lbrakk>length \<sigma>s = length As;
    \<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
           indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j);
    a \<in> (\<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i)) - E\<rbrakk> \<Longrightarrow>
    \<exists>!i. i < length As \<and> a \<in> \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
  by (erule indep_implies_only_one_enabled'[where E = E])
    (simp_all add: indep_enabl_def subset_iff, meson IntI \<R>\<^sub>d.init)


lemma \<tau>_iterated_combine\<^sub>d_Sync_general_form_when_indep:
  \<open>\<tau> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s a =
   (if As = [] then \<diamond>
    else   if a \<in> (\<Inter>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i))
         then \<lfloor>map2 (\<lambda>\<sigma> A. \<lceil>\<tau> A \<sigma> a\<rceil>) \<sigma>s As\<rfloor>
         else   if a \<in> (\<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s ! i)) - E
              then let i = THE i. i < length As \<and>  a \<in> \<epsilon> (As ! i) (\<sigma>s ! i)
                    in \<lfloor>\<sigma>s[i := \<lceil>\<tau> (As ! i) (\<sigma>s ! i) a\<rceil>]\<rfloor>
              else \<diamond>)\<close>
  (is \<open>_ = (if As = [] then \<diamond> else 
            if a \<in> ?I As \<sigma>s then \<lfloor>map2 (\<lambda>\<sigma> A. \<lceil>\<tau> A \<sigma> a\<rceil>) \<sigma>s As\<rfloor> else
            if a \<in> ?U As \<sigma>s - E then ?upd As \<sigma>s else \<diamond>)\<close>)
    if \<open>length \<sigma>s = length As\<close>
      \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
            indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
proof (subst \<tau>_iterated_combine\<^sub>d_Sync_general_form[OF that(1)], rule if_cong)
  show \<open>(if a \<in> ?U As \<sigma>s - E \<union> ?I As \<sigma>s
         then \<lfloor>map2 (\<lambda>x y. if a \<in> \<epsilon> y x then \<lceil>\<tau> y x a\<rceil> else x) \<sigma>s As\<rfloor> else \<diamond>) =
        (if a \<in> ?I As \<sigma>s then \<lfloor>map2 (\<lambda>x y. \<lceil>\<tau> y x a\<rceil>) \<sigma>s As\<rfloor> else
         if a \<in> ?U As \<sigma>s - E then ?upd As \<sigma>s else \<diamond>)\<close>
  proof (split if_split, intro conjI impI)
    assume * : \<open>a \<in> ?I As \<sigma>s\<close>
    with that(1) have \<open>(\<sigma>, A) \<in> set (zip \<sigma>s As) \<Longrightarrow> a \<in> \<epsilon> A \<sigma>\<close> for \<sigma> A
      by (induct \<sigma>s As rule: list_induct2) (use lessThan_Suc_eq_insert_0 in auto)
    with "*" show \<open>(if a \<in> ?U As \<sigma>s - E \<union> ?I As \<sigma>s
                    then \<lfloor>map2 (\<lambda>x y. if a \<in> \<epsilon> y x then \<lceil>\<tau> y x a\<rceil> else x) \<sigma>s As\<rfloor> else \<diamond>) =
                   \<lfloor>map2 (\<lambda>x y. \<lceil>\<tau> y x a\<rceil>) \<sigma>s As\<rfloor>\<close> by auto
  next
    assume * : \<open>a \<notin> ?I As \<sigma>s\<close>
    show \<open>(if a \<in> ?U As \<sigma>s - E \<union> ?I As \<sigma>s
           then \<lfloor>map2 (\<lambda>x y. if a \<in> \<epsilon> y x then \<lceil>\<tau> y x a\<rceil> else x) \<sigma>s As\<rfloor> else \<diamond>) =
          (if a \<in> ?U As \<sigma>s - E then ?upd As \<sigma>s else \<diamond>)\<close>
    proof (rule if_cong)
      assume \<open>a \<in> ?U As \<sigma>s - E\<close>
      from indep_implies_only_one_enabled[OF that this]
      obtain i where $ : \<open>i < length As\<close>  \<open>a \<in> \<epsilon> (As ! i) (\<sigma>s ! i)\<close>
        \<open>j < length As \<Longrightarrow> j \<noteq> i \<Longrightarrow> a \<notin> \<epsilon> (As ! j) (\<sigma>s ! j)\<close> for j by blast
      have $$ : \<open>(THE i. i < length As \<and> a \<in> \<epsilon> (As ! i) (\<sigma>s ! i)) = i\<close>
        using "$" by blast
      have \<open>\<lfloor>map2 (\<lambda>x y. if a \<in> \<epsilon> y x then \<lceil>\<tau> y x a\<rceil> else x) \<sigma>s As\<rfloor> =
            \<lfloor>\<sigma>s[i := \<lceil>\<tau> (As ! i) (\<sigma>s ! i) a\<rceil>]\<rfloor>\<close>
        by (auto intro!: nth_equalityI simp add: that(1))
          (use that(1) "$"(3) in fastforce, metis "$"(2) nth_list_update_neq)
      also have \<open>\<dots> = ?upd As \<sigma>s\<close>
        using "$$" by auto
      finally show \<open>\<lfloor>map2 (\<lambda>x y. if a \<in> \<epsilon> y x then \<lceil>\<tau> y x a\<rceil> else x) \<sigma>s As\<rfloor> = ?upd As \<sigma>s\<close> .
    qed (use "*" in auto)
  qed
qed simp_all



section \<open>More on Events\<close>

lemma events_of_MultiSync_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd : 
  \<open>\<alpha>(\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) =
   (if As = [] then {} else
    \<Union> \<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s. (\<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s' ! i)) - E \<union>
                                 (\<Inter>i<length As. \<epsilon> (As ! i) (\<sigma>s' ! i)))\<close>
  (is \<open>_ = ?rhs\<close>) if \<open>length \<sigma>s = length As\<close>
  \<open>\<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A\<close> \<open>\<And>A. A \<in> set As \<Longrightarrow> at_most_1_elem_term A\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
    by (simp only: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Sync[OF that])
  also have \<open>\<alpha>(\<dots>) = \<Union> (\<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> ` \<R>\<^sub>n\<^sub>d \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s)\<close> 
  proof (rule events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)
    show \<open>\<rho>_disjoint_\<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<close>
      by (simp only: \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>n\<^sub>d_Sync that(2))
  qed
  also from same_length_\<R>\<^sub>n\<^sub>d_iterated_combine\<^sub>n\<^sub>d_Sync_description[OF that(1)]
  have \<open>\<dots> = ?rhs\<close> by (auto simp add: \<epsilon>_iterated_combine\<^sub>n\<^sub>d_Sync_general_form)
  finally show ?thesis .
qed


lemma events_of_MultiSync_P_nd : 
  \<open>\<alpha>(\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) =
   (if As = [] then {} else
    \<Union> \<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s. (\<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s' ! i)) - E \<union>
                                 (\<Inter>i<length As. \<epsilon> (As ! i) (\<sigma>s' ! i)))\<close>
  (is \<open>_ = ?rhs\<close>) if \<open>length \<sigma>s = length As\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
    by (fact P_nd_compactification_Sync[OF that])
  also have \<open>\<alpha>(\<dots>) = \<Union> (\<epsilon> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> ` \<R>\<^sub>n\<^sub>d \<llangle>\<^sub>n\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s)\<close> by (fact events_of_P_nd)
  also from same_length_\<R>\<^sub>n\<^sub>d_iterated_combine\<^sub>n\<^sub>d_Sync_description[OF that(1)]
  have \<open>\<dots> = ?rhs\<close> by (auto simp add: \<epsilon>_iterated_combine\<^sub>n\<^sub>d_Sync_general_form)
  finally show ?thesis .
qed



lemma events_of_MultiSync_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d : 
  \<open>\<alpha>(\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) =
   (if As = [] then {} else
    \<Union> \<sigma>s' \<in> \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s. (\<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s' ! i) - E \<union>
                               (\<Inter>i<length As. \<epsilon> (As ! i) (\<sigma>s' ! i))))\<close>
  (is \<open>_ = ?rhs\<close>) if \<open>length \<sigma>s = length As\<close> \<open>\<And>A. A \<in> set As \<Longrightarrow> \<rho>_disjoint_\<epsilon> A\<close>
  \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
          indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Sync[OF that])
  also have \<open>\<alpha>(\<dots>) = \<Union> (\<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> ` \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s)\<close> 
  proof (rule events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
    show \<open>\<rho>_disjoint_\<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<close>
      by (simp only: \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine\<^sub>d_Sync that(2))
  qed
  also from same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description[OF that(1)]
  have \<open>\<dots> = ?rhs\<close> by (auto simp add: \<epsilon>_iterated_combine\<^sub>d_Sync_general_form)
  finally show ?thesis .
qed


lemma events_of_MultiSync_P_d : 
  \<open>\<alpha>(\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<llangle>A\<rrangle>\<^sub>d \<sigma>) =
   (if As = [] then {} else
    \<Union> \<sigma>s' \<in> \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s. (\<Union>i<length As. \<epsilon> (As ! i) (\<sigma>s' ! i) - E \<union>
                                (\<Inter>i<length As. \<epsilon> (As ! i) (\<sigma>s' ! i))))\<close>
  (is \<open>_ = ?rhs\<close>) if \<open>length \<sigma>s = length As\<close>
  and \<open>\<And>i j. \<lbrakk>i < length As; j < length As; i \<noteq> j\<rbrakk> \<Longrightarrow>
             indep_enabl (As ! i) (\<sigma>s ! i) E (As ! j) (\<sigma>s ! j)\<close>
proof -
  have \<open>\<^bold>\<lbrakk>E\<^bold>\<rbrakk> (\<sigma>, A) \<in># mset (zip \<sigma>s As). P\<llangle>A\<rrangle>\<^sub>d \<sigma> = P\<llangle>\<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle>\<rrangle>\<^sub>d \<sigma>s\<close>
    by (simp add: P_d_compactification_Sync[OF that])
  also have \<open>\<alpha>(\<dots>) = \<Union> (\<epsilon> \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> ` \<R>\<^sub>d \<llangle>\<^sub>d\<Otimes>\<lbrakk>E\<rbrakk> As\<rrangle> \<sigma>s)\<close> by (fact events_of_P_d)
  also from same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description[OF that(1)]
  have \<open>\<dots> = ?rhs\<close> by (auto simp add: \<epsilon>_iterated_combine\<^sub>d_Sync_general_form)
  finally show ?thesis .
qed



(*<*)
end
  (*>*)