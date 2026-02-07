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


chapter \<open>Combining Automata for Generalized Synchronization Product\<close>

(*<*)
theory Combining_Synchronization_Product_Generalized
  imports Combining_Synchronization_Product
begin
  (*>*)


section \<open>Definitions\<close>

subsection \<open>Specializations\<close>

definition combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, 'e set, ('\<sigma>, 'e, 'r, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r list) A\<^sub>d\<close>
  where \<open>combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 E A\<^sub>1 \<equiv>
         combine\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 hd (\<lambda>\<sigma>s. hd (tl \<sigma>s)) (\<lambda>s t. [s, t]) (\<lambda>s t. \<lfloor>[s, t]\<rfloor>)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, 'e set, ('\<sigma>, 'e, 'r, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r list) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 E A\<^sub>1 \<equiv> combine\<^sub>n\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 hd (\<lambda>\<sigma>s. hd (tl \<sigma>s)) (\<lambda>s t. [s, t]) (\<lambda>s t. \<lfloor>[s, t]\<rfloor>)\<close>

definition combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r\<^sub>0, '\<alpha>) A\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r\<^sub>1, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma>\<^sub>0 \<times> '\<sigma>\<^sub>1, 'e, 'r\<^sub>0 \<times> 'r\<^sub>1) A\<^sub>d\<close>
  where \<open>combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 E A\<^sub>1 \<equiv> combine\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 fst snd Pair (\<lambda>s r. \<lfloor>(s, r)\<rfloor>)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r\<^sub>0, '\<alpha>) A\<^sub>n\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r\<^sub>1, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma>\<^sub>0 \<times> '\<sigma>\<^sub>1, 'e, 'r\<^sub>0 \<times> 'r\<^sub>1) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 E A\<^sub>1 \<equiv> combine\<^sub>n\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 fst snd Pair (\<lambda>s r. \<lfloor>(s, r)\<rfloor>)\<close>

definition combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma> list, 'e, 'r list, '\<alpha>) A\<^sub>d_scheme, nat, 'e set, ('\<sigma> list, 'e, 'r list, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r list) A\<^sub>d\<close>
  where \<open>combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 len\<^sub>0 E A\<^sub>1 \<equiv> combine\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) (@) (\<lambda>s r. \<lfloor>s @ r\<rfloor>)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma> list, 'e, 'r list, '\<alpha>) A\<^sub>n\<^sub>d_scheme, nat, 'e set, ('\<sigma> list, 'e, 'r list, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r list) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 len\<^sub>0 E A\<^sub>1 \<equiv> combine\<^sub>n\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) (@) (\<lambda>s r. \<lfloor>s @ r\<rfloor>)\<close>

definition combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, 'e set, ('\<sigma> list, 'e, 'r list, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r list) A\<^sub>d\<close>
  where \<open>combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 E A\<^sub>1 \<equiv> combine\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 hd tl (#) (\<lambda>s r. \<lfloor>s # r\<rfloor>)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, 'e set, ('\<sigma> list, 'e, 'r list, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r list) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 E A\<^sub>1 \<equiv> combine\<^sub>n\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 hd tl (#) (\<lambda>s r. \<lfloor>s # r\<rfloor>)\<close>

lemmas combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs = combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
  and combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs = combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
  and combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs = combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
  and combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs = combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def

lemmas combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs =
  combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs


bundle combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_syntax begin

notation combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>d\<otimes>\<lbrakk>_, _\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L _\<rrangle>\<close> [0, 0, 0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<lbrakk>_, _\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L _\<rrangle>\<close> [0, 0, 0, 0])
notation combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0, 0])

end

unbundle combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_syntax



section \<open>First Properties\<close>

lemma finite_trans_combine\<^sub>n\<^sub>d_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps [simp] : 
  \<open>finite_trans A\<^sub>0 \<Longrightarrow> finite_trans A\<^sub>1 \<Longrightarrow> finite_trans \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<close>
  \<open>finite_trans B\<^sub>0 \<Longrightarrow> finite_trans B\<^sub>1 \<Longrightarrow> finite_trans \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle>\<close>
  \<open>finite_trans C\<^sub>0 \<Longrightarrow> finite_trans C\<^sub>1 \<Longrightarrow> finite_trans \<llangle>C\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L C\<^sub>1\<rrangle>\<close>
  \<open>finite_trans D\<^sub>0 \<Longrightarrow> finite_trans D\<^sub>1 \<Longrightarrow> finite_trans \<llangle>D\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t D\<^sub>1\<rrangle>\<close>
  unfolding combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def 
  by (simp_all add: finite_trans_def finite_image_set2)

lemma \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 hd (hd \<circ> tl) \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> B\<^sub>0 E B\<^sub>1 hd (hd \<circ> tl) \<sigma>s\<close>
  by (auto simp add: combine_Sync_\<epsilon>_def_bis combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<epsilon>_simps)

lemma \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 fst snd \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> B\<^sub>0 E B\<^sub>1 fst snd \<sigma>s\<close>
  by (auto simp add: combine_Sync_\<epsilon>_def_bis combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<epsilon>_simps)

lemma \<epsilon>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: 
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> B\<^sub>0 E B\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) \<sigma>s\<close>
  by (auto simp add: combine_Sync_\<epsilon>_def_bis combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<epsilon>_simps)

lemma \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 hd tl \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> B\<^sub>0 E B\<^sub>1 hd tl \<sigma>s\<close>
  by (auto simp add: combine_Sync_\<epsilon>_def_bis combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<epsilon>_simps)


lemma \<rho>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<rho> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> = {\<sigma>s. hd \<sigma>s \<in> \<rho> A\<^sub>0 \<and> hd (tl \<sigma>s) \<in> \<rho> A\<^sub>1}\<close>
  \<open>\<rho> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> = {\<sigma>s. hd \<sigma>s \<in> \<rho> B\<^sub>0 \<and> hd (tl \<sigma>s) \<in> \<rho> B\<^sub>1}\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<rho>_simps split: option.split)

lemma \<rho>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<rho> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> = {(\<sigma>\<^sub>0, \<sigma>\<^sub>1). \<sigma>\<^sub>0 \<in> \<rho> A\<^sub>0 \<and> \<sigma>\<^sub>1 \<in> \<rho> A\<^sub>1}\<close>
  \<open>\<rho> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle> = {(\<sigma>\<^sub>0, \<sigma>\<^sub>1). \<sigma>\<^sub>0 \<in> \<rho> B\<^sub>0 \<and> \<sigma>\<^sub>1 \<in> \<rho> B\<^sub>1}\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<rho>_simps split: option.split)

lemma \<rho>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: 
  \<open>\<rho> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> = {\<sigma>s. take len\<^sub>0 \<sigma>s \<in> \<rho> A\<^sub>0 \<and> drop len\<^sub>0 \<sigma>s \<in> \<rho> A\<^sub>1}\<close>
  \<open>\<rho> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> = {\<sigma>s. take len\<^sub>0 \<sigma>s \<in> \<rho> B\<^sub>0 \<and> drop len\<^sub>0 \<sigma>s \<in> \<rho> B\<^sub>1}\<close>
  by (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<rho>_simps split: option.split)

lemma \<rho>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<rho> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> = {\<sigma>s. hd \<sigma>s \<in> \<rho> A\<^sub>0 \<and> tl \<sigma>s \<in> \<rho> A\<^sub>1}\<close>
  \<open>\<rho> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> = {\<sigma>s. hd \<sigma>s \<in> \<rho> B\<^sub>0 \<and> tl \<sigma>s \<in> \<rho> B\<^sub>1}\<close>
  by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<rho>_simps split: option.split)



section \<open>Transitions are unchanged in the Generalization\<close>

text \<open>
In the generalization, only the \<^const>\<open>\<omega>\<close> function is modified.
\<close>

lemma \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> = \<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<close>
  \<open>\<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> = \<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle>\<close>
  by (simp_all add: combine_Sync_defs combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)

lemma \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> = \<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<close>
  \<open>\<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle> = \<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle>\<close>
  by (simp_all add: combine_Sync_defs combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)

lemma \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> = \<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<close>
  \<open>\<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> = \<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle>\<close>
  by (simp_all add: combine_Sync_defs combine_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)

text \<open>
\<^term>\<open>\<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<close> and \<^term>\<open>\<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle>\<close>
cannot be obtained that easily because of the types of terminations.\<close>



section \<open>Reachability\<close>

lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (s\<^sub>0 @ s\<^sub>1) \<subseteq> {t\<^sub>0 @ t\<^sub>1| t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  if \<open>\<And>t\<^sub>0. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<Longrightarrow> length t\<^sub>0 = len\<^sub>0\<close>
  by (subst same_\<tau>_implies_same_\<R>\<^sub>d[of _ _ \<open>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<close>])
    (simp_all add: \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_subset that)

lemma \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> (s\<^sub>0 @ s\<^sub>1) \<subseteq> {t\<^sub>0 @ t\<^sub>1| t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1}\<close> (is \<open>?S\<^sub>B \<subseteq> _\<close>)
  if \<open>\<And>t\<^sub>0. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<Longrightarrow> length t\<^sub>0 = len\<^sub>0\<close>
  by (subst same_\<tau>_implies_same_\<R>\<^sub>n\<^sub>d[of _ _ \<open>\<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle>\<close>])
    (simp_all add: \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_subset that)


lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset:
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] \<subseteq> {[t\<^sub>0, t\<^sub>1]| t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  and \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset:
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] \<subseteq> {[t\<^sub>0, t\<^sub>1]| t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1}\<close> (is \<open>?S\<^sub>B \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = [t\<^sub>0, t\<^sub>1] \<and> t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1\<close> for t
    by (\<R>\<^sub>d_subset_method defs: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  show \<open>t \<in> ?S\<^sub>B \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = [t\<^sub>0, t\<^sub>1] \<and> t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1\<close> for t
    by (\<R>\<^sub>n\<^sub>d_subset_method defs: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
qed

lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset:
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (s\<^sub>0, s\<^sub>1) \<subseteq> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<times> \<R>\<^sub>d A\<^sub>1 s\<^sub>1\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  and \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset:
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle> (s\<^sub>0, s\<^sub>1) \<subseteq> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<times> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1\<close> (is \<open>?S\<^sub>B \<subseteq> _\<close>)
proof -
  have \<open>t \<in> ?S\<^sub>A \<Longrightarrow> fst t \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> snd t \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1\<close> for t 
    by (\<R>\<^sub>d_subset_method defs: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  thus \<open>?S\<^sub>A \<subseteq> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<times> \<R>\<^sub>d A\<^sub>1 s\<^sub>1\<close> by force
next
  have \<open>t \<in> ?S\<^sub>B \<Longrightarrow> fst t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> snd t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1\<close> for t
    by (\<R>\<^sub>n\<^sub>d_subset_method defs: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  thus \<open>?S\<^sub>B \<subseteq> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<times> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1\<close> by force
qed


lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset:
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) \<subseteq> {t\<^sub>0 # \<sigma>t| t\<^sub>0 \<sigma>t. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> \<sigma>t \<in> \<R>\<^sub>d A\<^sub>1 \<sigma>s}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  and \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) \<subseteq> {t\<^sub>0 # \<sigma>t| t\<^sub>0 \<sigma>t. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> \<sigma>t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 \<sigma>s}\<close> (is \<open>?S\<^sub>B \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 \<sigma>t. t = t\<^sub>0 # \<sigma>t \<and> t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> \<sigma>t \<in> \<R>\<^sub>d A\<^sub>1 \<sigma>s\<close> for t
    by (\<R>\<^sub>d_subset_method defs: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
next
  show \<open>t \<in> ?S\<^sub>B \<Longrightarrow> \<exists>t\<^sub>0 \<sigma>t. t = t\<^sub>0 # \<sigma>t \<and> t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> \<sigma>t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 \<sigma>s\<close> for t
    by (\<R>\<^sub>n\<^sub>d_subset_method defs: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
qed



section \<open>Normalization\<close> 


lemma \<omega>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>\<omega> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1] = \<omega> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> [s\<^sub>0, s\<^sub>1]\<close>
  by (simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if)

lemma \<omega>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>\<omega> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1) = \<omega> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (s\<^sub>0, s\<^sub>1)\<close>
  by (simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if)

lemma \<omega>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>\<omega> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) = \<omega> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
  by (simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if)

lemma \<omega>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>\<omega> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1) = \<omega> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (s\<^sub>0 # \<sigma>s\<^sub>1)\<close>
  by (simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if)


lemma \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>\<epsilon> A\<^sub>0 s\<^sub>0 \<inter> \<epsilon> A\<^sub>1 s\<^sub>1 \<subseteq> E \<Longrightarrow>
   \<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1] e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> [s\<^sub>0, s\<^sub>1] e\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)

lemma \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>\<epsilon> A\<^sub>0 s\<^sub>0 \<inter> \<epsilon> A\<^sub>1 s\<^sub>1 \<subseteq> E \<Longrightarrow> 
   \<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1) e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (s\<^sub>0, s\<^sub>1) e\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)

lemma \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>\<epsilon> A\<^sub>0 \<sigma>s\<^sub>0 \<inter> \<epsilon> A\<^sub>1 \<sigma>s\<^sub>1 \<subseteq> E \<Longrightarrow> length \<sigma>s\<^sub>0 = len\<^sub>0 \<Longrightarrow> 
   \<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) e\<close>
  by (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)

lemma \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>\<epsilon> A\<^sub>0 s\<^sub>0 \<inter> \<epsilon> A\<^sub>1 \<sigma>s\<^sub>1 \<subseteq> E \<Longrightarrow>
   \<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1) e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (s\<^sub>0 # \<sigma>s\<^sub>1) e\<close>
  by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)



lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [s\<^sub>0, s\<^sub>1] = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1]\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 s\<^sub>1\<close>
  by (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset, simp_all)
    (metis \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep indep_enablD that,
      metis \<omega>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour)

lemma P_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [s\<^sub>0, s\<^sub>1] = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1]\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 s\<^sub>1\<close>
  by (P_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset, simp_all)
    (metis \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep indep_enablD that)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0, s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 s\<^sub>1\<close>
  by (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset, all \<open>elim SigmaE\<close>)
    (metis \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep indep_enablD that,
      auto simp add: \<omega>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour option.case_eq_if)

lemma P_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0, s\<^sub>1) = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 s\<^sub>1\<close>
  by (P_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset, elim SigmaE)
    (metis \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep indep_enablD that)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close> 
  if \<open>indep_enabl A\<^sub>0 \<sigma>s\<^sub>0 E A\<^sub>1 \<sigma>s\<^sub>1\<close> and \<open>\<And>\<sigma>t\<^sub>0. \<sigma>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0 \<Longrightarrow> length \<sigma>t\<^sub>0 = len\<^sub>0\<close>
  by (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset, simp_all add: that(2))
    (metis \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep indep_enablD that,
      metis \<omega>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour)

lemma P_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 \<sigma>s\<^sub>0 E A\<^sub>1 \<sigma>s\<^sub>1\<close> and \<open>\<And>\<sigma>t\<^sub>0. \<sigma>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0 \<Longrightarrow> length \<sigma>t\<^sub>0 = len\<^sub>0\<close>
  by (P_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset, simp_all add: that(2))
    (metis \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep indep_enablD that)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 \<sigma>s\<^sub>1\<close>
  by (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset, simp_all)
    (metis \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep indep_enablD that,
      metis \<omega>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour)

lemma P_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1) = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 \<sigma>s\<^sub>1\<close>
  by (P_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset, simp)
    (metis \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour_when_indep indep_enablD that)


(*<*)
end
  (*>*)