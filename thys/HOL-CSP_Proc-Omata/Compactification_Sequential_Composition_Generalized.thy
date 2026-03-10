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


chapter \<open>Compactification of Sequential Composition Generalized \<close>

(*<*)
theory Compactification_Sequential_Composition_Generalized
  imports Combining_Sequential_Composition_Generalized
begin
  (*>*)


section \<open>Iterated Combine\<close>

subsection \<open>Definitions\<close>

fun iterated_combine\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>[('r \<Rightarrow> ('\<sigma>, 'e, 'r) A\<^sub>d) list, 'r] \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>d\<close> (\<open>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> _\<rrangle>\<close> [0])
  where \<open>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> []\<rrangle> r = \<lparr>\<tau> = \<lambda>\<sigma>s a. \<diamond>, \<omega> = \<lambda>\<sigma>s. \<lfloor>r\<rfloor>\<rparr>\<close>
  |     \<open>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [A\<^sub>0]\<rrangle> r = \<^sub>d\<llangle>A\<^sub>0 r\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>
  |     \<open>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>0 # A\<^sub>1 # As\<rrangle> r = \<llangle>A\<^sub>0 r \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle>\<rrangle>\<close>

fun iterated_combine\<^sub>n\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>[('r \<Rightarrow> ('\<sigma>, 'e, 'r) A\<^sub>n\<^sub>d) list, 'r] \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>n\<^sub>d\<close> (\<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> _\<rrangle>\<close> [0])
  where \<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> []\<rrangle> r = \<lparr>\<tau> = \<lambda>\<sigma>s a. {}, \<omega> = \<lambda>\<sigma>s. {r}\<rparr>\<close>
  |     \<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [A\<^sub>0]\<rrangle> r = \<^sub>n\<^sub>d\<llangle>A\<^sub>0 r\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>
  |     \<open>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>0 # A\<^sub>1 # As\<rrangle> r = \<llangle>A\<^sub>0 r \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle>\<rrangle>\<close>


lemma iterated_combine\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps_bis: \<open>As \<noteq> [] \<Longrightarrow> \<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>0 # As\<rrangle> r = \<llangle>A\<^sub>0 r \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle>\<rrangle>\<close>
  and iterated_combine\<^sub>n\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps_bis: \<open>Bs \<noteq> [] \<Longrightarrow> \<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> B\<^sub>0 # Bs\<rrangle> r = \<llangle>B\<^sub>0 r \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> Bs\<rrangle>\<rrangle>\<close>
  by (induct As, simp_all) (induct Bs, simp_all)



subsection \<open>First Results\<close>

lemma combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq:
  \<open>\<epsilon> \<llangle>\<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<^sub>d\<otimes>1\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) = \<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s)\<close>
  \<open>\<tau> \<llangle>\<^sub>d\<llangle>A\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<^sub>d\<otimes>1\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e = \<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e\<close>
  \<open>\<epsilon> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<^sub>n\<^sub>d\<otimes>1\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) = \<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s)\<close>
  \<open>\<tau> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<^sub>0\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<^sub>n\<^sub>d\<otimes>1\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e = \<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) e\<close>
  by (simp_all add: \<epsilon>_simps \<rho>_simps combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<sigma>_\<sigma>s_conv_defs)
    (safe, auto simp add: map_option_case split: option.splits)


lemma combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_and_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq:
  \<open>\<epsilon> \<llangle>A\<^sub>0 r \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] = \<epsilon> (\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [A\<^sub>0, A\<^sub>1]\<rrangle> r) [s\<^sub>0, s\<^sub>1]\<close>
  \<open>\<tau> \<llangle>A\<^sub>0 r \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] e = \<tau> (\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [A\<^sub>0, A\<^sub>1]\<rrangle> r) [s\<^sub>0, s\<^sub>1] e\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 r \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] = \<epsilon> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [B\<^sub>0, B\<^sub>1]\<rrangle> r) [s\<^sub>0, s\<^sub>1]\<close>
  \<open>\<tau> \<llangle>B\<^sub>0 r \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] e = \<tau> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [B\<^sub>0, B\<^sub>1]\<rrangle> r) [s\<^sub>0, s\<^sub>1] e\<close>
  by (simp_all add: \<epsilon>_simps \<rho>_simps combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<sigma>_\<sigma>s_conv_defs)
    (safe, auto simp add: map_option_case split: option.splits)


lemma combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_and_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq :
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] = \<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [A\<^sub>1]\<rrangle>\<rrangle> [s\<^sub>0, s\<^sub>1]\<close>
  \<open>\<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] e = \<tau> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [A\<^sub>1]\<rrangle>\<rrangle> [s\<^sub>0, s\<^sub>1] e\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] = \<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [B\<^sub>1]\<rrangle>\<rrangle> [s\<^sub>0, s\<^sub>1]\<close>
  \<open>\<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] e = \<tau> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> [B\<^sub>1]\<rrangle>\<rrangle> [s\<^sub>0, s\<^sub>1] e\<close>
  by (simp_all add: \<epsilon>_simps \<rho>_simps combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<sigma>_\<sigma>s_conv_defs)
    (safe, auto simp add: map_option_case split: option.splits)



subsection \<open>Reachability\<close>

lemma same_length_\<tau>_iterated_combine\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>length \<sigma>s = length As \<Longrightarrow> \<lfloor>\<sigma>t\<rfloor> = \<tau> (\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r) \<sigma>s a \<Longrightarrow> length \<sigma>t = length As\<close>
proof (induct arbitrary: \<sigma>t r rule: induct_2_lists012)
  case Nil thus ?case by simp
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) thus ?case
    by simp (metis length_1_trans\<^sub>dE length_1_trans_from_\<sigma>_to_\<sigma>s(1) length_Cons list.size(3))
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  from Cons.prems Cons.hyps(1, 3) show ?case
    by (simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs map_option_case \<rho>_simps
        split: if_split_asm option.split_asm) metis
qed

lemma same_length_\<tau>_iterated_combine\<^sub>n\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>length \<sigma>s = length As \<Longrightarrow> \<sigma>t \<in> \<tau> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r) \<sigma>s a \<Longrightarrow> length \<sigma>t = length As\<close>
proof (induct arbitrary: \<sigma>t r rule: induct_2_lists012)
  case Nil thus ?case by simp
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) thus ?case
    by simp (meson length_1_trans\<^sub>n\<^sub>d_def length_1_trans_from_\<sigma>_to_\<sigma>s(2))
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  from Cons.prems Cons.hyps(1, 3) show ?case
    by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs map_option_case \<rho>_simps
        split: if_split_asm)
qed



lemma same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<sigma>t \<in> \<R>\<^sub>d (\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r) \<sigma>s \<Longrightarrow> length \<sigma>s = length As \<Longrightarrow> length \<sigma>t = length As\<close>
  by (induct rule: \<R>\<^sub>d.induct, simp) (meson same_length_\<tau>_iterated_combine\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemma same_length_\<R>\<^sub>n\<^sub>d_iterated_combine\<^sub>n\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<sigma>t \<in> \<R>\<^sub>n\<^sub>d (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r) \<sigma>s \<Longrightarrow> length \<sigma>s = length As \<Longrightarrow> length \<sigma>t = length As\<close>
  by (induct rule: \<R>\<^sub>n\<^sub>d.induct, simp) (meson same_length_\<tau>_iterated_combine\<^sub>n\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)



subsection \<open>Transmission of Properties\<close>

lemma \<rho>_disjoint_\<epsilon>_transmission_to_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>As \<noteq> [] \<Longrightarrow> \<rho>_disjoint_\<epsilon> ((last As) r) \<Longrightarrow> \<rho>_disjoint_\<epsilon> (\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r)\<close>
  \<open>Bs \<noteq> [] \<Longrightarrow> \<rho>_disjoint_\<epsilon> ((last Bs) r) \<Longrightarrow> \<rho>_disjoint_\<epsilon> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> Bs\<rrangle> r)\<close>
  by (induct rule: induct_list012;
      auto simp add: \<rho>_disjoint_\<epsilon>_def combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<epsilon>_simps \<rho>_simps \<sigma>_\<sigma>s_conv_defs)+



subsection \<open>Normalization\<close>

lemma \<omega>_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_det_ndet_conv:
  \<open>\<omega> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> map (\<lambda>A r. \<llangle>A r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> r) \<sigma>s = \<omega> \<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s\<close>
  by (induct As arbitrary: \<sigma>s r rule: induct_list012[case_names Nil singl Cons])
    (simp_all add: from_det_to_ndet_\<sigma>_\<sigma>s_conv_commute combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs
      \<omega>_from_det_to_ndet split: option.split)

lemma \<rho>_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_det_ndet_conv :
  \<open>\<rho> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> map (\<lambda>A r. \<llangle>A r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> r) = \<rho> \<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>
  by (simp add: \<rho>_simps \<omega>_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_det_ndet_conv)


lemma \<tau>_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>length \<sigma>s = length As \<Longrightarrow>
   \<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s e = \<tau> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> map (\<lambda>A r. \<llangle>A r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> r) \<sigma>s e\<close>
proof (induct \<sigma>s As arbitrary: r rule: induct_2_lists012)
  case Nil show ?case by simp
next
  case (single \<sigma>\<^sub>0 A\<^sub>0)
  show ?case by (simp add: from_det_to_ndet_\<sigma>_\<sigma>s_conv_commute(1))
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  show ?case
    by (simp add: \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour split: option.split,
        simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<rho>_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_det_ndet_conv
        \<omega>_from_det_to_ndet split: option.split)
      (metis Cons.hyps(3) \<rho>_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_det_ndet_conv det_ndet_conv_\<rho>(1) list.simps(9))
qed



lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  assumes same_length: \<open>length \<sigma>s = length As\<close>
  shows \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d \<sigma>s = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> map (\<lambda>A r. \<llangle>A r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> r\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d, rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id)
  show \<open>\<sigma>t \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow>
        \<tau> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> map (\<lambda>A r. \<llangle>A r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> r) \<sigma>t a = \<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>t a\<close> for \<sigma>t a
    by (simp add: \<R>\<^sub>n\<^sub>d_from_det_to_ndet \<tau>_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour
        same_length same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  show \<open>\<omega> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> map (\<lambda>A r. \<llangle>A r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> r) \<sigma>t = \<omega> \<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>t\<close> for \<sigma>t
    by (simp add: \<omega>_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_det_ndet_conv)
qed

lemma P_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  assumes same_length: \<open>length \<sigma>s = length As\<close>
  shows \<open>P\<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d \<sigma>s = P\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> map (\<lambda>A r. \<llangle>A r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> r\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<close>
proof (fold P_nd_from_det_to_ndet_is_P_d, rule P_nd_eqI_strong_id)
  show \<open>\<sigma>t \<in> \<R>\<^sub>n\<^sub>d \<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>s \<Longrightarrow>
       \<tau> (\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> map (\<lambda>A r. \<llangle>A r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) As\<rrangle> r) \<sigma>t a = \<tau> \<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>t a\<close> for \<sigma>t a
    by (simp add: \<R>\<^sub>n\<^sub>d_from_det_to_ndet \<tau>_iterated_combine_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour
        same_length same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed



section \<open>Compactification Theorems\<close>

subsection \<open>Binary\<close>

subsubsection \<open>Pair\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  fixes A\<^sub>0 A\<^sub>1
  assumes at_most_1_elem_term : \<open>at_most_1_elem_term A\<^sub>0\<close>
    \<comment> \<open>This assumption is necessary in the new setup,
        otherwise the result is not always a Procomaton
        (for example if \<^term>\<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = UNIV\<close>,
         we have \<^term>\<open>P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1 = \<sqinter>r\<in>UNIV. Q \<sigma>\<^sub>1 r\<close>).\<close>
    (* TODO: weaken this to reachable terminations ? *)
  defines A_def: \<open>A \<equiv> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<close> 
  defines P_def: \<open>P \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d\<close>
    and Q_def: \<open>Q \<equiv> \<lambda>\<sigma>\<^sub>1 r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1\<close>
    and S_def: \<open>S \<equiv> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  shows \<open>P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1 = S (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
proof -
  let ?f = \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) (\<lambda>\<sigma>'. case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>\<^sub>1) \<Rightarrow> P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1)\<close>
  note cartprod_rwrt = GlobalNdet_cartprod[of _ _ \<open>\<lambda>x y. _ (x, y)\<close>, simplified]
  note Ndet_and_Seq = Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right
  have P_rec : \<open>P \<sigma>\<^sub>0 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A\<^sub>0) (\<tau> A\<^sub>0) (\<omega> A\<^sub>0) P \<sigma>\<^sub>0\<close> for \<sigma>\<^sub>0
    by (fact restriction_fix_eq[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis[of A\<^sub>0],
          folded P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def P_def, THEN fun_cong])
  have Q_rec : \<open>Q \<sigma>\<^sub>1 = (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> (A\<^sub>1 r)) (\<tau> (A\<^sub>1 r)) (\<omega> (A\<^sub>1 r)) (\<lambda>\<sigma>\<^sub>1. Q \<sigma>\<^sub>1 r) \<sigma>\<^sub>1)\<close> for \<sigma>\<^sub>1
    by (rule ext, simp add: Q_def P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
  show \<open>P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1 = S (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
  proof (rule fun_cong[of \<open>\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1).P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1\<close> _ \<open>(\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>, simplified])
    show \<open>(\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1) = S\<close>
    proof (rule restriction_fix_unique[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis[of A],
          symmetric, folded P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def S_def])
      show \<open>?f = (\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1)\<close>
      proof (rule ext, clarify)
        show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1\<close> for \<sigma>\<^sub>0 \<sigma>\<^sub>1
        proof (cases \<open>\<sigma>\<^sub>0 \<in> \<rho> A\<^sub>0\<close>)
          show \<open>\<sigma>\<^sub>0 \<notin> \<rho> A\<^sub>0 \<Longrightarrow> ?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1\<close>
            by (subst (2) P_rec)
              (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<epsilon>_simps A_def \<rho>_simps
                Mprefix_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k cartprod_rwrt Ndet_and_Seq intro!: mono_Mprefix_eq)
        next
          assume \<open>\<sigma>\<^sub>0 \<in> \<rho> A\<^sub>0\<close>
          hence \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 \<noteq> {}\<close> by (simp add: \<rho>_simps)
          then obtain r where \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {r}\<close>
            by (meson at_most_1_elem_term at_most_1_elem_termE)
          from \<open>\<sigma>\<^sub>0 \<in> \<rho> A\<^sub>0\<close> have P_rec' : \<open>P \<sigma>\<^sub>0 = SKIPS (\<omega> A\<^sub>0 \<sigma>\<^sub>0)\<close> by (simp add: P_rec \<rho>_simps)
          have \<epsilon>_A : \<open>\<epsilon> A (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = (if \<sigma>\<^sub>1 \<in> \<rho> (A\<^sub>1 r) then {} else \<epsilon> (A\<^sub>1 r) \<sigma>\<^sub>1)\<close>
            by (simp add: A_def \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k combine_Seq_\<epsilon>_defs \<open>\<sigma>\<^sub>0 \<in> \<rho> A\<^sub>0\<close> \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {r}\<close>)
          from \<open>\<sigma>\<^sub>0 \<in> \<rho> A\<^sub>0\<close> have \<omega>_A : \<open>\<omega> A (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = \<omega> (A\<^sub>1 r) \<sigma>\<^sub>1\<close>
            by (simp add: A_def combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {r}\<close>)
          show \<open>?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1\<close>
          proof (cases \<open>\<sigma>\<^sub>1 \<in> \<rho> (A\<^sub>1 r)\<close>)
            show \<open>\<sigma>\<^sub>1 \<in> \<rho> (A\<^sub>1 r) \<Longrightarrow> ?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1\<close>
              by (subst (2) Q_rec)
                (simp add: P_rec' \<epsilon>_A \<omega>_A SKIPS_def Ndet_and_Seq \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {r}\<close> \<rho>_simps)
          next
            show \<open>\<sigma>\<^sub>1 \<notin> \<rho> (A\<^sub>1 r) \<Longrightarrow> ?f (\<sigma>\<^sub>0, \<sigma>\<^sub>1) = P \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> Q \<sigma>\<^sub>1\<close>
              by (subst (2) Q_rec, unfold \<epsilon>_A \<omega>_A SKIPS_def)
                (auto simp add: A_def P_rec' Ndet_and_Seq \<open>\<omega> A\<^sub>0 \<sigma>\<^sub>0 = {r}\<close>
                  \<rho>_simps cartprod_rwrt combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs intro!: mono_Mprefix_eq)
          qed
        qed
      qed
    qed
  qed
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d \<sigma>\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d \<sigma>\<^sub>1) =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (metis P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k at_most_1_elem_from_det_to_ndet
        at_most_1_elem_imp_at_most_1_elem_term)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour)
  finally show ?thesis .
qed



subsubsection \<open>Pairlist\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
  if \<open>at_most_1_elem_term A\<^sub>0\<close>
proof -
  from P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>at_most_1_elem_term A\<^sub>0\<close>]
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1) =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close> .
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
  proof (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of \<open>\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close> _ \<open>(\<sigma>\<^sub>0, \<sigma>\<^sub>1)\<close>, simplified])
    show \<open>inj_on (\<lambda>(\<sigma>\<^sub>0, \<sigma>\<^sub>1). [\<sigma>\<^sub>0, \<sigma>\<^sub>1]) (\<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (\<sigma>\<^sub>0, \<sigma>\<^sub>1))\<close>
      by (auto intro: inj_onI)
  next
    show \<open>\<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>\<^sub>1) \<Rightarrow> [\<sigma>\<^sub>0, \<sigma>\<^sub>1]) a =
          (\<lambda>\<sigma>'. case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>\<^sub>1) \<Rightarrow> [\<sigma>\<^sub>0, \<sigma>\<^sub>1]) ` \<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>' a\<close> for \<sigma>' a
      by (cases \<sigma>') (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  next
    show \<open>\<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>\<^sub>1) \<Rightarrow> [\<sigma>\<^sub>0, \<sigma>\<^sub>1]) = \<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>'\<close> for \<sigma>'
      by (cases \<sigma>') (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  qed
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d \<sigma>\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d \<sigma>\<^sub>1) =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>1)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (metis P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k at_most_1_elem_from_det_to_ndet
        at_most_1_elem_imp_at_most_1_elem_term)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [\<sigma>\<^sub>0, \<sigma>\<^sub>1]\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour)
  finally show ?thesis .
qed



subsubsection \<open>Rlist\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>n\<^sub>d \<sigma>s) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
  if \<open>at_most_1_elem_term A\<^sub>0\<close>
proof -
  from P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>at_most_1_elem_term A\<^sub>0\<close>]
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>n\<^sub>d \<sigma>s) =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0, \<sigma>s)\<close> .
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
  proof (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of \<open>\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 # \<sigma>s\<close> _ \<open>(\<sigma>\<^sub>0, \<sigma>s)\<close>, simplified])
    show \<open>inj_on (\<lambda>(\<sigma>\<^sub>0, \<sigma>s). \<sigma>\<^sub>0 # \<sigma>s) (\<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (\<sigma>\<^sub>0, \<sigma>s))\<close>
      by (auto intro: inj_onI)
  next
    show \<open>\<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>s) \<Rightarrow> \<sigma>\<^sub>0 # \<sigma>s) a =
         (\<lambda>\<sigma>'. case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>s) \<Rightarrow> \<sigma>\<^sub>0 # \<sigma>s) ` \<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>' a\<close> for \<sigma>' a
      by (cases \<sigma>') (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  next
    show \<open>\<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (case \<sigma>' of (\<sigma>\<^sub>0, \<sigma>s) \<Rightarrow> \<sigma>\<^sub>0 # \<sigma>s) = \<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>'\<close> for \<sigma>'
      by (cases \<sigma>') (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs)
  qed
  finally show ?thesis .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d \<sigma>s) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d \<sigma>s) =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>s)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
    by (metis P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k at_most_1_elem_from_det_to_ndet
        at_most_1_elem_imp_at_most_1_elem_term)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>s)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour)
  finally show ?thesis .
qed



subsection \<open>ListslenL\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
  if same_length_reach : \<open>\<And>\<sigma>s\<^sub>0'. \<sigma>s\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0 \<Longrightarrow> length \<sigma>s\<^sub>0' = len\<^sub>0\<close>
    and \<open>at_most_1_elem_term A\<^sub>0\<close>
proof -
  from P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>at_most_1_elem_term A\<^sub>0\<close>]
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<^sub>1) =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0, \<sigma>s\<^sub>1)\<close> .
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
  proof (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of \<open>\<lambda>(\<sigma>s\<^sub>0, \<sigma>s\<^sub>1). \<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1\<close> _ \<open>(\<sigma>s\<^sub>0, \<sigma>s\<^sub>1)\<close>, simplified])
    show \<open>inj_on (\<lambda>(\<sigma>s\<^sub>0, \<sigma>s\<^sub>1). \<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) (\<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (\<sigma>s\<^sub>0, \<sigma>s\<^sub>1))\<close>
    proof (rule inj_onI, clarify)
      fix \<sigma>s\<^sub>0' \<sigma>s\<^sub>1' \<sigma>s\<^sub>0'' \<sigma>s\<^sub>1''
      assume assms : \<open>(\<sigma>s\<^sub>0', \<sigma>s\<^sub>1') \<in> \<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (\<sigma>s\<^sub>0, \<sigma>s\<^sub>1)\<close>
        \<open>(\<sigma>s\<^sub>0'', \<sigma>s\<^sub>1'') \<in> \<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (\<sigma>s\<^sub>0, \<sigma>s\<^sub>1)\<close>
        \<open>\<sigma>s\<^sub>0' @ \<sigma>s\<^sub>1' = \<sigma>s\<^sub>0'' @ \<sigma>s\<^sub>1''\<close>
      from \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset assms(1, 2)
      have \<open>\<sigma>s\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0\<close> \<open>\<sigma>s\<^sub>0'' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0\<close> by fast+
      with same_length_reach have \<open>length \<sigma>s\<^sub>0' = length \<sigma>s\<^sub>0''\<close> by blast
      with assms(3) show \<open>\<sigma>s\<^sub>0' = \<sigma>s\<^sub>0'' \<and> \<sigma>s\<^sub>1' = \<sigma>s\<^sub>1''\<close> by simp
    qed
  next
    fix \<sigma>s' a
    assume \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (\<sigma>s\<^sub>0, \<sigma>s\<^sub>1)\<close>
    with \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset
    obtain \<sigma>s\<^sub>0' \<sigma>s\<^sub>1' where \<open>\<sigma>s' = (\<sigma>s\<^sub>0', \<sigma>s\<^sub>1')\<close> \<open>\<sigma>s\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0\<close> by fast
    from \<open>\<sigma>s\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0\<close> same_length_reach have \<open>length \<sigma>s\<^sub>0' = len\<^sub>0\<close> by blast
    show \<open>\<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (case \<sigma>s' of (\<sigma>s\<^sub>0, \<sigma>s\<^sub>1) \<Rightarrow> \<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) a =
          (\<lambda>\<sigma>s'. case \<sigma>s' of (\<sigma>s\<^sub>0, \<sigma>s\<^sub>1) \<Rightarrow> \<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) ` \<tau> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>s' a\<close>
      by (auto simp add: \<open>\<sigma>s' = (\<sigma>s\<^sub>0', \<sigma>s\<^sub>1')\<close> \<open>length \<sigma>s\<^sub>0' = len\<^sub>0\<close>
          combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    fix \<sigma>s' a
    assume \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (\<sigma>s\<^sub>0, \<sigma>s\<^sub>1)\<close>
    with \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset
    obtain \<sigma>s\<^sub>0' \<sigma>s\<^sub>1' where \<open>\<sigma>s' = (\<sigma>s\<^sub>0', \<sigma>s\<^sub>1')\<close> \<open>\<sigma>s\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0\<close> by fast
    from \<open>\<sigma>s\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0\<close> same_length_reach have \<open>length \<sigma>s\<^sub>0' = len\<^sub>0\<close> by blast
    show \<open>\<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (case \<sigma>s' of (\<sigma>s\<^sub>0, \<sigma>s\<^sub>1) \<Rightarrow> \<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) = \<omega> \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>s'\<close>
      by (auto simp add: \<open>\<sigma>s' = (\<sigma>s\<^sub>0', \<sigma>s\<^sub>1')\<close> \<open>length \<sigma>s\<^sub>0' = len\<^sub>0\<close>
          combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  qed
  finally show ?thesis .
qed


corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>s\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d \<sigma>s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
  if same_length_reach : \<open>\<And>\<sigma>s\<^sub>0'. \<sigma>s\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0 \<Longrightarrow> length \<sigma>s\<^sub>0' = len\<^sub>0\<close>
proof -
  have \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>s\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d \<sigma>s\<^sub>1) =
        P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d \<sigma>s\<^sub>1)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
    by (rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF same_length_reach])
      (simp_all add: \<R>\<^sub>n\<^sub>d_from_det_to_ndet at_most_1_elem_imp_at_most_1_elem_term)
  also have \<open>\<dots> = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour same_length_reach)
  finally show ?thesis .
qed



subsection \<open>Multiple\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_compactification_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<lbrakk>length \<sigma>s = length As; \<And>A r. A \<in> set (butlast As) \<Longrightarrow> at_most_1_elem_term (A r)\<rbrakk> \<Longrightarrow>
   SEQ\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip \<sigma>s As. (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A r\<rrangle>\<^sub>n\<^sub>d \<sigma>) = (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>n\<^sub>d \<sigma>s)\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_\<sigma>_to_\<sigma>s_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  have \<open>SEQ\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>0 # A\<^sub>1 # As). (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A r\<rrangle>\<^sub>n\<^sub>d \<sigma>) =
        (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0 r\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> SEQ\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (\<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>1 # As). (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A r\<rrangle>\<^sub>n\<^sub>d \<sigma>))\<close> by simp
  also have \<open>SEQ\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (\<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>1 # As). (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A r\<rrangle>\<^sub>n\<^sub>d \<sigma>) =
             (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle> r\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>1 # \<sigma>s))\<close>
    by (rule Cons.hyps(3)) (simp add: Cons.prems)
  also have \<open>(\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0 r\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>1 # As \<rrangle> r\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>1 # \<sigma>s))) =
             (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 r \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle>\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s))\<close>
    by (intro ext P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (simp add: Cons.prems)
  also have \<open>\<dots> = (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>n\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>0 # A\<^sub>1 # As\<rrangle> r\<rrangle>\<^sub>n\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s))\<close> by simp
  finally show ?case .
qed

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_compactification_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>length \<sigma>s = length As \<Longrightarrow>
   SEQ\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip \<sigma>s As. (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A r\<rrangle>\<^sub>d \<sigma>) = (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> As\<rrangle> r\<rrangle>\<^sub>d \<sigma>s)\<close>
proof (induct \<sigma>s As rule: induct_2_lists012)
  case Nil show ?case by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec)
next
  case (single \<sigma>\<^sub>0 A\<^sub>0) show ?case by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_from_\<sigma>_to_\<sigma>s_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
next
  case (Cons \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>s A\<^sub>0 A\<^sub>1 As)
  have \<open>SEQ\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>0 # A\<^sub>1 # As). (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A r\<rrangle>\<^sub>d \<sigma>) =
        (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0 r\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> SEQ\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (\<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>1 # As). (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A r\<rrangle>\<^sub>d \<sigma>))\<close> by simp
  also have \<open>SEQ\<^sub>\<checkmark> (\<sigma>, A) \<in>@ zip (\<sigma>\<^sub>1 # \<sigma>s) (A\<^sub>1 # As). (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A r\<rrangle>\<^sub>d \<sigma>) =
             (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle> r\<rrangle>\<^sub>d (\<sigma>\<^sub>1 # \<sigma>s))\<close>
    by (fact Cons.hyps(3))
  also have \<open>(\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0 r\<rrangle>\<^sub>d \<sigma>\<^sub>0 \<^bold>;\<^sub>\<checkmark> (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle> r\<rrangle>\<^sub>d (\<sigma>\<^sub>1 # \<sigma>s))) =
             (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 r \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>1 # As\<rrangle>\<rrangle>\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s))\<close>
    by (intro ext P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  also have \<open>\<dots> = (\<lambda>r. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<^sub>d\<Otimes>\<^bold>;\<^sub>\<checkmark> A\<^sub>0 # A\<^sub>1 # As\<rrangle> r\<rrangle>\<^sub>d (\<sigma>\<^sub>0 # \<sigma>\<^sub>1 # \<sigma>s))\<close> by simp
  finally show ?case .
qed



(*<*)
end
  (*>*)