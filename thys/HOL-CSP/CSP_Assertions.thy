(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Reference processes and properties
 *
 * Copyright (c) 2009 Université Paris-Sud, France
 * Copyright (c) 2025 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter\<open>CSP Assertions\<close>

(*<*)
theory CSP_Assertions
  imports Basic_CSP_Laws CSP_Monotonies Events_Ticks_CSP_Laws
begin
  (*>*)


section \<open>Reference Processes\<close>

definition DF :: \<open>'a set \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where   \<open>DF A \<equiv> \<mu> X. \<sqinter>a\<in>A \<rightarrow> X\<close>

lemma DF_unfold : \<open>DF A = \<sqinter>a\<in>A \<rightarrow> DF A\<close>
  by (simp add: DF_def, rule trans, rule fix_eq, simp)


definition DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :: \<open>'a set \<Rightarrow> 'r set \<Rightarrow> ('a,'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<equiv> \<mu> X. (\<sqinter>a \<in> A \<rightarrow> X) \<sqinter> SKIPS R\<close>

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold : \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R = (\<sqinter>a \<in> A \<rightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) \<sqinter> SKIPS R\<close>
  by (simp add: DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, rule trans, rule fix_eq, simp)


definition RUN :: \<open>'a set \<Rightarrow> ('a,'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>RUN A \<equiv> \<mu> X. \<box>x\<in>A \<rightarrow> X\<close>

lemma RUN_unfold : \<open>RUN A = \<box>a\<in>A \<rightarrow> RUN A\<close>
  by (simp add: RUN_def, rule trans, rule fix_eq, simp)


definition CHAOS :: \<open>'a set \<Rightarrow> ('a,'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> 
  where \<open>CHAOS A \<equiv> \<mu> X. STOP \<sqinter> (\<box>a \<in> A \<rightarrow> X)\<close>

lemma CHAOS_unfold : \<open>CHAOS A = STOP \<sqinter> (\<box>a\<in>A \<rightarrow> CHAOS A)\<close>
  by (simp add: CHAOS_def, rule trans, rule fix_eq, simp)


definition CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :: \<open>'a set \<Rightarrow> 'r set \<Rightarrow> ('a,'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<equiv> \<mu> X. SKIPS R \<sqinter> STOP \<sqinter> (\<box>a\<in>A \<rightarrow> X)\<close>

lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold: \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R = SKIPS R \<sqinter> STOP \<sqinter> (\<box>a \<in> A \<rightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
  by (simp add: CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, rule trans, rule fix_eq, simp)



section \<open>Assertions\<close>

definition deadlock_free :: \<open>('a,'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  where \<open>deadlock_free P \<equiv> DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D P\<close>


definition deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  where \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<equiv> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>F P\<close>


definition lifelock_free :: \<open>('a,'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  where \<open>lifelock_free P \<equiv> CHAOS UNIV \<sqsubseteq>\<^sub>F\<^sub>D P\<close>


definition lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :: \<open>('a,'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  where \<open>lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<equiv> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>F\<^sub>D P\<close>


definition non_terminating :: \<open>('a,'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  where \<open>non_terminating P \<equiv> RUN UNIV \<sqsubseteq>\<^sub>T P\<close>



section \<open>Properties\<close>

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF : \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close>
proof (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D DF A)\<close> by simp
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close> by simp
next
  show \<open>X \<sqsubseteq>\<^sub>F\<^sub>D DF A \<Longrightarrow> (\<Lambda> X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> SKIPS R)\<cdot>X \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close> for X
    by (subst DF_unfold, simp)
      (meson Ndet_FD_self_left mono_Mndetprefix_FD trans_FD)
qed



lemma SKIPS_FD_SKIPS_iff :
  \<open>SKIPS S \<sqsubseteq>\<^sub>F\<^sub>D SKIPS R \<longleftrightarrow> (if R = {} then S = {} else R \<subseteq> S)\<close>
  by (auto simp add: failure_divergence_refine_def failure_refine_def
      divergence_refine_def F_SKIPS D_SKIPS)

lemma SKIPS_F_SKIPS_iff :
  \<open>SKIPS S \<sqsubseteq>\<^sub>F SKIPS R \<longleftrightarrow> (if R = {} then S = {} else R \<subseteq> S)\<close>
  by (auto simp add: failure_refine_def F_SKIPS)

lemma SKIPS_T_SKIPS_iff : \<open>SKIPS S \<sqsubseteq>\<^sub>T SKIPS R \<longleftrightarrow> (R \<subseteq> S)\<close>
  by (auto simp add: trace_refine_def T_SKIPS subset_iff)



lemma DF_subset : \<open>DF B \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close> if \<open>A \<noteq> {}\<close> \<open>A \<subseteq> B\<close> for A B :: \<open>'a set\<close>
proof (subst DF_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D DF A)\<close> by simp
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close> by simp
next
  show \<open>X \<sqsubseteq>\<^sub>F\<^sub>D DF A \<Longrightarrow> (\<Lambda> X. \<sqinter>b\<in>B \<rightarrow> X)\<cdot>X \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close> for X :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (subst DF_unfold, simp)
      (meson \<open>A \<noteq> {}\<close> \<open>A \<subseteq> B\<close>  Mndetprefix_FD_subset mono_Mndetprefix_FD trans_FD)
qed

lemma DF_Univ_freeness : \<open>A \<noteq> {} \<Longrightarrow> DF A \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> deadlock_free P\<close>
  by (meson DF_subset deadlock_free_def subset_UNIV trans_FD)

lemma deadlock_free_Ndet_iff :
  \<open>deadlock_free (P \<sqinter> Q) \<longleftrightarrow> deadlock_free P \<and> deadlock_free Q\<close>
  by (auto simp add: F_Ndet D_Ndet deadlock_free_def refine_defs)


lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_subset : \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S B S \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close>
  if \<open>A \<noteq> {}\<close> \<open>A \<subseteq> B\<close> \<open>R \<noteq> {}\<close> \<open>R \<subseteq> S\<close>
proof (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> by simp
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close> by simp
next
  show \<open>(\<Lambda> X. (\<sqinter>b\<in>B \<rightarrow> X) \<sqinter> SKIPS S)\<cdot>X \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close> if \<open>X \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close> for X
  proof (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold, subst beta_cfun)
    show \<open>cont (\<lambda>X. (\<sqinter>b\<in>B \<rightarrow>  X) \<sqinter> SKIPS S)\<close> by simp
  next
    show \<open>(\<sqinter>b\<in>B \<rightarrow>  X) \<sqinter> SKIPS S \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter>a\<in>A \<rightarrow>  DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) \<sqinter> SKIPS R\<close>
    proof (rule mono_Ndet_FD)
      show \<open>\<sqinter>b\<in>B \<rightarrow>  X \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>A \<rightarrow>  DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close>
        by (meson Mndetprefix_FD_subset \<open>A \<noteq> {}\<close> \<open>A \<subseteq> B\<close>
            mono_Mndetprefix_FD \<open>X \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close> trans_FD)
    next
      show \<open>SKIPS S \<sqsubseteq>\<^sub>F\<^sub>D SKIPS R\<close>
        by (simp add: SKIPS_FD_SKIPS_iff \<open>R \<noteq> {}\<close> \<open>R \<subseteq> S\<close>)
    qed
  qed
qed


lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Univ_freeness : \<open>\<lbrakk>A \<noteq> {}; R \<noteq> {}; DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D P\<rbrakk> \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  by (meson DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_subset deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def leFD_imp_leF subset_UNIV trans_F)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Ndet_iff :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<sqinter> Q) \<longleftrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<and> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q\<close>
  by (simp add: F_Ndet deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def)


lemma div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: \<open>\<D> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = {}\<close>
proof (rule equals0I)
  show \<open>s \<in> \<D> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) \<Longrightarrow> False\<close> for s
    by (induct s; subst (asm) DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: D_Ndet D_SKIPS D_Mndetprefix write0_def D_Mprefix split: if_split_asm)
qed


lemma div_free_DF: \<open>\<D> (DF A) = {}\<close>
  by (metis DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S empty_subsetI subset_antisym le_ref1)


lemma deadlock_free_implies_div_free: \<open>deadlock_free P \<Longrightarrow> \<D> P = {}\<close>
  by (simp add: deadlock_free_def div_free_DF refine_defs)



section \<open>Events and Ticks of Reference Processes\<close>

lemma events_of_SKIPS : \<open>\<alpha>(SKIPS R) = {}\<close>
  and  ticks_of_SKIPS : \<open>\<checkmark>s(SKIPS R) = R\<close>
  by (auto simp add: events_of_def ticks_of_def T_SKIPS)


lemma no_ticks_imp_tickFree_T : \<open>\<checkmark>s(P) = {} \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> tF s\<close>
  by (simp add: ticks_of_def tickFree_def disjoint_iff image_iff)
    (metis T_nonTickFree_imp_decomp event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) split_list tickFree_Cons_iff tickFree_append_iff)


lemma events_of_DF : \<open>\<alpha>(DF A) = A\<close>
proof (intro subset_antisym subsetI)
  fix a assume \<open>a \<in> A\<close>
  hence \<open>[ev a] \<in> \<T> (DF A)\<close>
    by (subst DF_unfold) (auto simp add: T_Mndetprefix write0_def T_Mprefix)
  thus \<open>a \<in> \<alpha>(DF A)\<close> by (force simp add: events_of_def)
next
  fix a assume \<open>a \<in> \<alpha>((DF A) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
  then obtain t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> (DF A)\<close>
    by (auto simp add: events_of_def)
  thus \<open>a \<in> A\<close>
    by (induct t, simp, subst (asm) DF_unfold)
      (auto simp add: T_Mndetprefix write0_def T_Mprefix split: if_split_asm)
qed

lemma ticks_DF : \<open>\<checkmark>s(DF A) = {}\<close>
proof (rule equals0I)
  fix r :: 'r assume \<open>r \<in> \<checkmark>s(DF A)\<close>
  then obtain s where \<open>s @ [\<checkmark>(r)] \<in> \<T> (DF A)\<close> unfolding ticks_of_def by blast
  thus False
    by (induct s; subst (asm) DF_unfold)
      (simp_all add: T_Mndetprefix write0_def T_Mprefix split: if_split_asm)
qed


lemma events_of_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>\<alpha>(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = A\<close>
proof (intro subset_antisym subsetI)
  fix a assume \<open>a \<in> A\<close>
  hence \<open>[ev a] \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
    by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold) (auto simp add: T_Ndet T_Mndetprefix write0_def T_Mprefix)
  thus \<open>a \<in> \<alpha>(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> by (force simp add: events_of_def)
next
  fix a assume \<open>a \<in> \<alpha>(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
  then obtain t where \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
    by (auto simp add: events_of_def)
  thus \<open>a \<in> A\<close>
    by (induct t, simp, subst (asm) DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: T_Ndet T_SKIPS T_Mndetprefix write0_def T_Mprefix split: if_split_asm)
qed

lemma ticks_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>\<checkmark>s(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = R\<close>
proof (intro subset_antisym subsetI)
  fix r assume \<open>r \<in> R\<close>
  hence \<open>[\<checkmark>(r)] \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold) (simp add: T_Ndet T_SKIPS)
  thus \<open>r \<in> \<checkmark>s(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
    unfolding ticks_of_def by (metis (no_types, lifting) CollectI append_self_conv2)
next
  fix r assume \<open>r \<in> \<checkmark>s(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
  then obtain s where \<open>s @ [\<checkmark>(r)] \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> unfolding ticks_of_def by blast
  thus \<open>r \<in> R\<close>
    by (induct s; subst (asm) DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (simp_all add: T_Ndet T_SKIPS T_Mndetprefix write0_def T_Mprefix split: if_split_asm)
qed



lemma events_of_RUN : \<open>\<alpha>(RUN A) = A\<close>
proof (intro subset_antisym subsetI)
  fix a assume \<open>a \<in> A\<close>
  hence \<open>[ev a] \<in> \<T> (RUN A)\<close>
    by (subst RUN_unfold) (auto simp add: T_Mprefix)
  thus \<open>a \<in> \<alpha>(RUN A)\<close> by (force simp add: events_of_def)
next
  fix a assume \<open>a \<in> \<alpha>((RUN A) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
  then obtain t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> (RUN A)\<close>
    by (auto simp add: events_of_def)
  thus \<open>a \<in> A\<close>
    by (induct t, simp, subst (asm) RUN_unfold) (auto simp add: T_Mprefix)
qed

lemma ticks_RUN : \<open>\<checkmark>s(RUN A) = {}\<close>
proof (rule equals0I)
  fix r :: 'r assume \<open>r \<in> \<checkmark>s(RUN A)\<close>
  then obtain s where \<open>s @ [\<checkmark>(r)] \<in> \<T> (RUN A)\<close> unfolding ticks_of_def by blast
  thus False
    by (induct s; subst (asm) RUN_unfold)
      (auto simp add: T_Mprefix split: if_split_asm)
qed




lemma events_of_CHAOS : \<open>\<alpha>(CHAOS A) = A\<close>
proof (intro subset_antisym subsetI)
  fix a assume \<open>a \<in> A\<close>
  hence \<open>[ev a] \<in> \<T> (CHAOS A)\<close>
    by (subst CHAOS_unfold) (auto simp add: T_Ndet T_Mprefix)
  thus \<open>a \<in> \<alpha>(CHAOS A)\<close> by (force simp add: events_of_def)
next
  fix a assume \<open>a \<in> \<alpha>((CHAOS A) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
  then obtain t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> (CHAOS A)\<close>
    by (auto simp add: events_of_def)
  thus \<open>a \<in> A\<close>
    by (induct t, simp, subst (asm) CHAOS_unfold) (auto simp add: T_Ndet T_STOP T_Mprefix)
qed

lemma ticks_CHAOS : \<open>\<checkmark>s(CHAOS A) = {}\<close>
proof (rule equals0I)
  fix r :: 'r assume \<open>r \<in> \<checkmark>s(CHAOS A)\<close>
  then obtain s where \<open>s @ [\<checkmark>(r)] \<in> \<T> (CHAOS A)\<close> unfolding ticks_of_def by blast
  thus False
    by (induct s; subst (asm) CHAOS_unfold)
      (auto simp add: T_Ndet T_STOP T_Mprefix split: if_split_asm)
qed


lemma events_of_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>\<alpha>(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = A\<close>
proof (intro subset_antisym subsetI)
  fix a assume \<open>a \<in> A\<close>
  hence \<open>[ev a] \<in> \<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
    by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold) (auto simp add: T_Ndet T_Mprefix)
  thus \<open>a \<in> \<alpha>(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> by (force simp add: events_of_def)
next
  fix a assume \<open>a \<in> \<alpha>(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
  then obtain t where \<open>ev a \<in> set t\<close> \<open>t \<in> \<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
    by (auto simp add: events_of_def)
  thus \<open>a \<in> A\<close>
    by (induct t, simp, subst (asm) CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: T_Ndet T_STOP T_SKIPS T_Mprefix)
qed

lemma ticks_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>\<checkmark>s(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = R\<close>
proof (intro subset_antisym subsetI)
  fix r assume \<open>r \<in> R\<close>
  hence \<open>[\<checkmark>(r)] \<in> \<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold) (simp add: T_Ndet T_SKIPS)
  thus \<open>r \<in> \<checkmark>s(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> by (metis append_Nil ticks_of_memI)
next
  fix r assume \<open>r \<in> \<checkmark>s(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
  then obtain s where \<open>s @ [\<checkmark>(r)] \<in> \<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> unfolding ticks_of_def by blast
  thus \<open>r \<in> R\<close>
    by (induct s; subst (asm) CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: T_Ndet T_STOP T_SKIPS T_Mprefix)
qed


lemma RUN_subset_DT: \<open>RUN B \<sqsubseteq>\<^sub>D\<^sub>T RUN A\<close>
  if \<open>A \<subseteq> B\<close> for A B :: \<open>'a set\<close>
proof (subst RUN_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>D\<^sub>T RUN A)\<close> by simp
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>D\<^sub>T RUN A\<close> by simp
next
  show \<open>X \<sqsubseteq>\<^sub>D\<^sub>T RUN A \<Longrightarrow> (\<Lambda> X. \<box>b\<in>B \<rightarrow> X)\<cdot>X \<sqsubseteq>\<^sub>D\<^sub>T RUN A\<close> for X :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (subst RUN_unfold, simp)
      (meson Mprefix_DT_subset mono_Mprefix_DT \<open>A \<subseteq> B\<close> trans_DT)
qed


lemma CHAOS_subset_FD : \<open>CHAOS B \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A\<close>
  if \<open>A \<subseteq> B\<close> for A B :: \<open>'a set\<close>
proof (subst CHAOS_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A)\<close> by simp
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A\<close> by simp
next
  from \<open>A \<subseteq> B\<close> show \<open>X \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A \<Longrightarrow> (\<Lambda> X. STOP \<sqinter> (\<box>b\<in>B \<rightarrow> X))\<cdot>X \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A\<close>
    for X :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (subst CHAOS_unfold)
      (auto simp add: refine_defs Mprefix_projs Ndet_projs F_STOP D_STOP)
qed


lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_subset_FD : \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S B S \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close>
  if \<open>A \<subseteq> B\<close> \<open>R \<noteq> {}\<close> \<open>R \<subseteq> S\<close>
proof (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> by simp
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close> by simp
next
  from \<open>A \<subseteq> B\<close> \<open>R \<noteq> {}\<close> \<open>R \<subseteq> S\<close>
  show \<open>X \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<Longrightarrow> (\<Lambda> X. SKIPS S \<sqinter> STOP \<sqinter> (\<box>a\<in>B \<rightarrow> X))\<cdot>X \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close> for X
    by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: refine_defs Mprefix_projs Ndet_projs F_STOP D_STOP F_SKIPS D_SKIPS)
qed



section \<open>Relations between refinements on reference processes\<close>

lemma CHAOS_has_all_tickFree_failures : 
  \<open>tF s \<Longrightarrow> {a. ev a \<in> set s} \<subseteq> A \<Longrightarrow> (s, X) \<in> \<F> (CHAOS A)\<close>
proof (induct s)
  show \<open>([], X) \<in> \<F> (CHAOS A)\<close>
    by (subst CHAOS_unfold) (simp add: F_Ndet F_STOP)
next
  fix e s
  assume   hyp : \<open>tF s \<Longrightarrow> {a. ev a \<in> set s} \<subseteq> A \<Longrightarrow> (s, X) \<in> \<F> (CHAOS A)\<close>
  assume prems : \<open>tF (e # s)\<close> \<open>{a. ev a \<in> set (e # s)} \<subseteq> A\<close>
  from prems have \<open>tF s\<close> \<open>{a. ev a \<in> set s} \<subseteq> A\<close> by auto
  hence \<open>(s, X) \<in> \<F> (CHAOS A)\<close> by (fact hyp)
  with prems show \<open>(e # s, X) \<in> \<F> (CHAOS A)\<close>
    by (subst CHAOS_unfold, cases e) (auto simp add: F_Ndet F_Mprefix)
qed



lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_superset_events_of_ticks_of_leF : 
  \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F P\<close> if \<open>\<alpha>(P) \<subseteq> A\<close> and \<open>\<checkmark>s(P) \<subseteq> R\<close>
proof (unfold failure_refine_def)
  have \<open>ftF s \<Longrightarrow> set s \<subseteq> (\<Union>t\<in>\<T> P. set t) \<Longrightarrow> (s, X) \<in> \<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> for s X
  proof (induct s)
    show \<open>([], X) \<in> \<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
      by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold) (simp add: F_Ndet F_STOP)
  next
    fix e s
    assume prems : \<open>ftF (e # s)\<close> \<open>set (e # s) \<subseteq> \<Union> (set ` \<T> P)\<close>
    assume   hyp : \<open>ftF s \<Longrightarrow> set s \<subseteq> \<Union> (set ` \<T> P) \<Longrightarrow> (s, X) \<in> \<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
    show \<open>(e # s, X) \<in> \<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
    proof (cases e)
      fix a assume \<open>e = ev a\<close>
      with prems(2) have \<open>a \<in> \<alpha>(P)\<close> by (auto simp add: events_of_def)
      with \<open>\<alpha>(P) \<subseteq> A\<close> have \<open>a \<in> A\<close> by fast
      from prems have \<open>ftF s\<close> \<open>set s \<subseteq> \<Union> (set ` \<T> P)\<close>
        by auto (metis front_tickFree_Cons_iff front_tickFree_Nil)
      hence \<open>(s, X) \<in> \<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> by (fact hyp)
      thus \<open>(e # s, X) \<in> \<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
        by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold) (simp add: F_Ndet F_Mprefix \<open>e = ev a\<close> \<open>a \<in> A\<close>)
    next
      fix r assume \<open>e = \<checkmark>(r)\<close>
      with prems(2) have \<open>r \<in> \<checkmark>s(P)\<close>
        by (simp add: ticks_of_def)
          (metis T_imp_front_tickFree front_tickFree_Cons_iff front_tickFree_append_iff
            in_set_conv_decomp non_tickFree_tick tickFree_Cons_iff tickFree_Nil)
      with \<open>\<checkmark>s(P) \<subseteq> R\<close> have \<open>r \<in> R\<close> by fast
      moreover from \<open>e = \<checkmark>(r)\<close> prems(1) have \<open>s = []\<close> by (simp add: front_tickFree_Cons_iff)
      ultimately show \<open>(e # s, X) \<in> \<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
        by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold) (auto simp add: F_Ndet F_SKIPS \<open>e = \<checkmark>(r)\<close>)
    qed
  qed
  thus \<open>\<F> P \<subseteq> \<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close> by (meson F_T F_imp_front_tickFree SUP_upper subrelI)
qed


corollary CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_events_of_ticks_of_leF: \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F P\<close> 
  and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_UNIV_UNIV_leF: \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>F P\<close>
  by (simp_all add: CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_superset_events_of_ticks_of_leF)


lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_DF : \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F DF A\<close>
  by (simp add: DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF leFD_imp_leF)

lemma DF_F_RUN : \<open>DF A \<sqsubseteq>\<^sub>F RUN A\<close> for A :: \<open>'a set\<close>
proof (unfold DF_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F RUN A)\<close> by simp
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F RUN A\<close> by simp
next
  show \<open>X \<sqsubseteq>\<^sub>F RUN A \<Longrightarrow> (\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>X \<sqsubseteq>\<^sub>F RUN A\<close> for X :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (subst RUN_unfold, simp)    
      (meson Mndetprefix_F_Mprefix mono_Mprefix_F trans_F)
qed

lemma CHAOS_F_DF : \<open>CHAOS A \<sqsubseteq>\<^sub>F DF A\<close>
proof (unfold failure_refine_def, safe, rule CHAOS_has_all_tickFree_failures)
  show \<open>(s, X) \<in> \<F> (DF A) \<Longrightarrow> tF s\<close> for s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and X
    by (metis F_T no_ticks_imp_tickFree_T ticks_DF)
next
  show \<open>(s, X) \<in> \<F> (DF A) \<Longrightarrow> {a. ev a \<in> set s} \<subseteq> A\<close> for s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and X
    by (drule F_T) (use events_of_DF[of A] in \<open>auto simp add: events_of_def\<close>)
qed

corollary CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_CHAOS : \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F CHAOS A\<close>
  and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close>
  by (rule CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_superset_events_of_ticks_of_leF;
      simp add: events_of_CHAOS ticks_CHAOS events_of_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ticks_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)+




lemma div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: \<open>\<D> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = {}\<close>
proof (rule equals0I)
  show \<open>s \<in> \<D> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) \<Longrightarrow> False\<close> for s
    by (induct s; subst (asm) CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: D_Ndet D_STOP D_SKIPS D_Mprefix)
qed


lemma div_free_CHAOS: \<open>\<D> (CHAOS A) = {}\<close>
proof (rule equals0I)
  show \<open>s \<in> \<D> (CHAOS A) \<Longrightarrow> False\<close> for s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct s; subst (asm) CHAOS_unfold)
      (auto simp add: D_Ndet D_STOP D_Mprefix)
qed


lemma div_free_RUN: \<open>\<D> (RUN A) = {}\<close>
proof (rule equals0I)
  show \<open>s \<in> \<D> (RUN A) \<Longrightarrow> False\<close> for s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct s; subst (asm) RUN_unfold) (auto simp add: D_Mprefix)
qed

(* DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF : "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D DF A" *)

corollary DF_FD_RUN : \<open>DF A  \<sqsubseteq>\<^sub>F\<^sub>D RUN A\<close>
  and CHAOS_FD_DF : \<open>CHAOS A  \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close>
  and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_CHAOS : \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A\<close>
  and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close>
  by (simp_all add: DF_F_RUN div_free_RUN CHAOS_F_DF div_free_DF CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_CHAOS div_free_CHAOS
      CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S divergence_refine_def leF_leD_imp_leFD)



lemma traces_CHAOS_subset : \<open>\<T> (CHAOS A) \<subseteq> {s. set s \<subseteq> ev ` A}\<close>
proof (rule subsetI)
  show \<open>s \<in> \<T> (CHAOS A) \<Longrightarrow> s \<in> {s. set s \<subseteq> ev ` A}\<close> for s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct s; subst (asm) CHAOS_unfold) (auto simp add: T_Ndet T_STOP T_Mprefix)
qed

lemma traces_RUN_superset : \<open>{s. set s \<subseteq> ev ` A} \<subseteq> \<T> (RUN A)\<close>
proof (rule subsetI)
  show \<open>s \<in> {s. set s \<subseteq> ev ` A} \<Longrightarrow> s \<in> \<T> (RUN A)\<close> for s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct s, simp) (subst RUN_unfold, auto simp add: T_Mprefix)
qed

corollary RUN_all_tickfree_traces1   : \<open>\<T> (RUN   A) = {s. set s \<subseteq> ev ` A}\<close> 
  and     DF_all_tickfree_traces1    : \<open>\<T> (DF    A) = {s. set s \<subseteq> ev ` A}\<close>
  and     CHAOS_all_tickfree_traces1 : \<open>\<T> (CHAOS A) = {s. set s \<subseteq> ev ` A}\<close>
  using DF_F_RUN[THEN leF_imp_leT, simplified trace_refine_def]
    CHAOS_F_DF[THEN leF_imp_leT,simplified trace_refine_def] 
    traces_CHAOS_subset traces_RUN_superset by blast+

corollary RUN_all_tickfree_traces2  : \<open>s \<in> \<T> (RUN   UNIV)\<close> 
  and     DF_all_tickfree_traces2   : \<open>s \<in> \<T> (DF    UNIV)\<close> 
  and     CHAOS_all_tickfree_trace2 : \<open>s \<in> \<T> (CHAOS UNIV)\<close> if \<open>tF s\<close>
  using \<open>tF s\<close>
  by (simp add: tickFree_def RUN_all_tickfree_traces1 DF_all_tickfree_traces1
      CHAOS_all_tickfree_traces1 disjoint_iff image_iff subset_iff; metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)+


lemma traces_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_subset :
  \<open>\<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) \<subseteq> {s. ftF s \<and> set s \<subseteq> ev ` A \<union> tick ` R}\<close>
proof (rule subsetI)
  show \<open>s \<in> \<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) \<Longrightarrow> s \<in> {s. ftF s \<and> set s \<subseteq> ev ` A \<union> tick ` R}\<close> for s
    by (induct s; subst (asm) CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: T_Ndet T_STOP T_SKIPS T_Mprefix front_tickFree_Cons_iff)
qed


lemma traces_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_superset : 
  \<open>{s. ftF s \<and> set s \<subseteq> ev ` A \<union> tick ` R} \<subseteq> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
proof (rule subsetI)
  show \<open>s \<in> {s. ftF s \<and> set s \<subseteq> ev ` A \<union> tick ` R} \<Longrightarrow> s \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) \<close> for s
    by (induct s; subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: T_Ndet T_SKIPS T_Mndetprefix write0_def T_Mprefix front_tickFree_Cons_iff)
qed



corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces1: 
  \<open>\<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = {s. ftF s \<and> set s \<subseteq> ev ` A \<union> tick ` R}\<close>
  and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces1: 
  \<open>\<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = {s. ftF s \<and> set s \<subseteq> ev ` A \<union> tick ` R}\<close>
  using CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S[THEN leF_imp_leT, simplified trace_refine_def]
    traces_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_subset traces_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_superset by blast+


corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces2   : \<open>s \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close>
  and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces2: \<open>s \<in> \<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close>
  if \<open>ftF s\<close>
  using \<open>ftF s\<close>
  by (simp add: tickFree_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces1 CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces1;
      metis UnCI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust rangeI subsetI)+


corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_UNIV_UNIV_leT :    \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>T P\<close>
  and  CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_UNIV_UNIV_leT : \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>T P\<close>
  by (simp add:trace_refine_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces2 is_processT2_TR subsetI) 
    (simp add:trace_refine_def CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces2 is_processT2_TR subsetI)

lemma deadlock_free_implies_lifelock_free: \<open>deadlock_free P \<Longrightarrow> lifelock_free P\<close>
  unfolding deadlock_free_def lifelock_free_def
  using CHAOS_FD_DF trans_FD by blast

lemma deadlock_free_implies_non_terminating:
  \<open>tF s\<close> if \<open>deadlock_free P\<close> \<open>s \<in> \<T> P\<close>
proof -
  from \<open>deadlock_free P\<close> have \<open>\<T> P \<subseteq> \<T> (DF UNIV)\<close>
    by (simp add: deadlock_free_def le_ref2T)
  with \<open>s \<in> \<T> P\<close> show \<open>tF s\<close>
    by (meson no_ticks_imp_tickFree_T subsetD ticks_DF)
qed



lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right: 
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<longleftrightarrow>
   (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (s, UNIV :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set) \<notin> \<F> P)\<close>
proof (intro iffI ballI impI)
  have \<open>tF s \<Longrightarrow> (s, UNIV) \<notin> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close> for s :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list\<close>
    by (induct s; subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: F_Ndet F_SKIPS F_Mndetprefix write0_def F_Mprefix)
  thus \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> tF s \<Longrightarrow> (s, UNIV) \<notin> \<F> P\<close> for s
    using deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def by blast
next
  assume as1 : \<open>\<forall>s\<in>\<T> P. tF s \<longrightarrow> (s, UNIV) \<notin> \<F> P\<close>
  have as2 : \<open>ftF s \<Longrightarrow> (\<exists>a \<in> UNIV. ev a \<notin> X) \<Longrightarrow>
              (s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close> for s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and X
  proof(induct s)
    case Nil
    then show ?case
      by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold, auto simp add:F_Mndetprefix write0_def F_Mprefix F_Ndet F_SKIP)
  next
    case (Cons hds tls)
    then show ?case 
    proof (simp add: DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def fix_def)
      define Y where "Y \<equiv> \<lambda>i. iterate i\<cdot>(\<Lambda> x. (\<sqinter>xa\<in>(UNIV :: 'a set) \<rightarrow>  x) \<sqinter> SKIPS (UNIV :: 'r set))\<cdot>\<bottom>"
      assume a:"ftF (hds # tls)" and b:"ftF tls \<Longrightarrow> (tls, X) \<in> \<F> (\<Squnion>i. Y i)"
        and c:"\<exists>a. ev a \<notin> X"
      from Y_def have cc:"chain Y" by simp
      from b have d:"ftF tls \<Longrightarrow> \<exists>a\<in>UNIV. ev a \<notin> X \<Longrightarrow>(tls, X) \<in> \<F> (Y i)" for i 
        using F_LUB[OF cc] limproc_is_thelub[OF cc] by simp
      from Y_def have e:"\<F>(Mndetprefix UNIV (\<lambda>x. Y i) \<sqinter> SKIPS UNIV) \<subseteq> \<F> (Y (Suc i))" for i by(simp)
      from a have f:"tls \<noteq> [] \<Longrightarrow> hds \<notin> range tick" "ftF tls"
        by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_Cons_iff imageE)
          (metis a front_tickFree_Cons_iff front_tickFree_Nil)
      have g:"(hds#tls, X) \<in> \<F> (Y (Suc i))" for i
        using f c e[of i] d[of i] 
        by (auto simp: F_Mndetprefix write0_def F_Mprefix Y_def F_Ndet F_SKIPS image_iff)
          (meson event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)+
      have h:"(hds#tls, X) \<in> \<F> (Y 0)"
        using D_F cc g po_class.chainE proc_ord2a by blast
      from a b c show "(hds#tls, X) \<in> \<F> (\<Squnion>i. Y i)"
        using F_LUB[OF cc] is_ub_thelub[OF cc] 
        by (metis D_LUB_2 cc g limproc_is_thelub po_class.chainE proc_ord2a process_charn) 
    qed   
  qed
  show "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P"
  proof(unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def, safe)
    fix s X
    assume as3:"(s, X) \<in> \<F> P"
    hence a1:"s \<in> \<T> P" "ftF s" 
      using F_T as3 is_processT2 by blast+
    show "(s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)" 
    proof(cases "tF s")
      case FT_True:True
      hence a2:"(s, UNIV) \<notin> \<F> P"
        using a1 as1 by blast
      then show ?thesis 
        by (metis DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces2 FT_True UNIV_I UNIV_eq_I a1(2) as2 as3
            event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust is_processT6_TR_notin tickFree_imp_front_tickFree_snoc)
    next
      case FT_False: False                                                                 
      then show ?thesis 
        by (metis DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_all_front_tickfree_traces2 a1(2) front_tickFree_append_iff
            is_processT2_TR is_processT5_S7 list.distinct(1))
    qed 
  qed
qed 

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> \<D> P = {}\<close>
  by (metis D_T D_imp_front_tickFree T_nonTickFree_imp_decomp all_not_in_conv butlast_snoc
      deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right front_tickFree_iff_tickFree_butlast is_processT8 is_processT9)

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free
      less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def order_refl refine_defs(3))

lemma all_events_ticks_refusal: 
  \<open>(s, tick ` \<checkmark>s(P) \<union> ev ` \<alpha>(P)) \<in> \<F> P \<Longrightarrow> (s, UNIV) \<in> \<F> P\<close>
proof (rule ccontr)
  assume \<open>(s, tick ` \<checkmark>s(P) \<union> ev ` \<alpha>(P)) \<in> \<F> P\<close> and \<open>(s, UNIV) \<notin> \<F> P\<close>
  then obtain c where \<open>c \<notin> tick ` \<checkmark>s(P) \<union> ev ` \<alpha>(P) \<and> s @ [c] \<in> \<T> P\<close>
    using is_processT5[of s \<open>tick ` \<checkmark>s(P) \<union> ev ` \<alpha>(P)\<close> P 
        \<open>UNIV - (tick ` \<checkmark>s(P) \<union> ev ` \<alpha>(P))\<close>, simplified] F_T by blast
  thus False by (simp add: events_of_def ticks_of_def, cases c) fastforce+
qed

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right_wrt_events:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> 
   (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (s, tick ` \<checkmark>s(P) \<union> ev ` \<alpha>(P)) \<notin> \<F> P)\<close>
  unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right using all_events_ticks_refusal is_processT4 by blast


lemma deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: \<open>deadlock_free P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  using DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD deadlock_free_def trans_FD by blast




section \<open>\<^const>\<open>deadlock_free\<close> and \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close> with \<^const>\<open>SKIP\<close> and \<^const>\<open>STOP\<close>\<close>

lemma non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_STOP: \<open>\<not> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S STOP\<close>
  by (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold, unfold failure_refine_def)
    (auto simp add: F_Ndet F_STOP F_SKIPS F_Mndetprefix write0_def F_Mprefix)

lemma non_deadlock_free_STOP: \<open>\<not> deadlock_free STOP\<close>
  using deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_STOP by blast


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIPS : \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (SKIPS R) \<longleftrightarrow> R \<noteq> {}\<close>
proof (rule iffI)
  show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (SKIPS R) \<Longrightarrow> R \<noteq> {}\<close>
    by (rule ccontr, simp add: SKIPS_def)
      (use non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_STOP in blast)
next
  show \<open>R \<noteq> {} \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (SKIPS R)\<close>
    by (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold, unfold failure_refine_def)
      (auto simp add: F_Ndet F_STOP F_SKIPS F_Mndetprefix write0_def F_Mprefix subset_iff)
qed


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIP: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (SKIP r)\<close>
  by (metis SKIPS_singl_is_SKIP deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIPS empty_not_insert)

lemma non_deadlock_free_SKIPS : \<open>\<not> deadlock_free (SKIPS R)\<close>
proof (cases \<open>R = {}\<close>)
  show \<open>R = {} \<Longrightarrow> \<not> deadlock_free (SKIPS R)\<close>
    by (simp add: non_deadlock_free_STOP)
next
  assume \<open>R \<noteq> {}\<close>
  then obtain r where \<open>r \<in> R\<close> by blast
  hence \<open>[\<checkmark>(r)] \<in> \<T> (SKIPS R)\<close> by (simp add: T_SKIPS)
  moreover have \<open>\<not> tF ([\<checkmark>(r)])\<close> by simp
  ultimately show \<open>\<not> deadlock_free (SKIPS R)\<close>
    using deadlock_free_implies_non_terminating by blast
qed


lemma non_deadlock_free_SKIP: \<open>\<not> deadlock_free (SKIP r)\<close>
  by (metis SKIPS_singl_is_SKIP non_deadlock_free_SKIPS)




corollary non_terminating_refine_DF : \<open>non_terminating P \<longleftrightarrow> DF UNIV \<sqsubseteq>\<^sub>T P\<close> 
  and non_terminating_refine_CHAOS : \<open>non_terminating P \<longleftrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>T P\<close>
  by (simp_all add: DF_all_tickfree_traces1 RUN_all_tickfree_traces1 CHAOS_all_tickfree_traces1 
      non_terminating_def trace_refine_def)

lemma non_terminating_is_right : \<open>non_terminating P \<longleftrightarrow> (\<forall>s\<in>\<T> P. tF s)\<close>
  by (meson RUN_all_tickfree_traces2 no_ticks_imp_tickFree_T
      non_terminating_def subset_iff ticks_RUN trace_refine_def)

lemma nonterminating_implies_div_free : \<open>non_terminating P \<Longrightarrow> \<D> P = {}\<close>
  by (metis D_T ex_in_conv front_tickFree_single is_processT7
      non_terminating_is_right non_tickFree_tick tickFree_append_iff)

lemma non_terminating_implies_F : \<open>non_terminating P \<Longrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>F P\<close>
  by (meson CHAOS_has_all_tickFree_failures F_T failure_refine_def in_mono no_ticks_imp_tickFree_T
      non_terminating_refine_CHAOS subrelI ticks_CHAOS top_greatest trace_refine_def)

corollary non_terminating_F : \<open>non_terminating P \<longleftrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>F P\<close>
  by (auto simp add:non_terminating_implies_F non_terminating_refine_CHAOS leF_imp_leT)

corollary non_terminating_FD : \<open>non_terminating P \<longleftrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis failure_refine_def less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def non_terminating_F
      nonterminating_implies_div_free order_refl)



corollary lifelock_free_is_non_terminating: \<open>lifelock_free P = non_terminating P\<close>
  unfolding lifelock_free_def non_terminating_FD by (fact refl)

lemma divergence_refine_div_free :
  \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>D P \<longleftrightarrow> \<D> P = {}\<close>
  \<open>CHAOS UNIV \<sqsubseteq>\<^sub>D P         \<longleftrightarrow> \<D> P = {}\<close>
  \<open>RUN UNIV \<sqsubseteq>\<^sub>D P           \<longleftrightarrow> \<D> P = {}\<close> 
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>D P   \<longleftrightarrow> \<D> P = {}\<close>
  \<open>DF UNIV \<sqsubseteq>\<^sub>D P            \<longleftrightarrow> \<D> P = {}\<close>
  by (simp_all add: div_free_CHAOS div_free_RUN div_free_DF div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S
      div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S divergence_refine_def)



lemma lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_div_free : \<open>lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> \<D> P = {}\<close>
  by (simp add: CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_UNIV_UNIV_leF divergence_refine_div_free(1)
      failure_divergence_refine_def lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def)

lemma lifelock_free_imp_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>lifelock_free P \<Longrightarrow> lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  by (simp add: lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_div_free lifelock_free_is_non_terminating
      nonterminating_implies_div_free)

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_imp_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_div_free)



lemma non_terminating_Seq : \<open>P \<^bold>; Q = P\<close> if \<open>non_terminating P\<close>
proof -
  from \<open>non_terminating P\<close> have * : \<open>s \<in> \<T> P \<Longrightarrow> tF s\<close> for s
    unfolding non_terminating_is_right ..
  show \<open>P \<^bold>; Q = P\<close>
  proof (subst Process_eq_spec_optimized, safe)
    from "*" show \<open>s \<in> \<D> (P \<^bold>; Q) \<Longrightarrow> s \<in> \<D> P\<close> for s by (force simp add: D_Seq)
  next
    show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> (P \<^bold>; Q)\<close> for s by (simp add: D_Seq)
  next
    show \<open>(s, X) \<in> \<F> (P \<^bold>; Q) \<Longrightarrow> (s, X) \<in> \<F> P\<close> for s X
      by (simp add: F_Seq)
        (meson "*" is_processT4 is_processT8 non_tickFree_tick sup_ge1 tickFree_append_iff)
  next
    show \<open>(s, X) \<in> \<F> P \<Longrightarrow> (s, X) \<in> \<F> (P \<^bold>; Q)\<close> for s X
      by (simp add: F_Seq)
        (metis (mono_tags, lifting) "*" F_T f_inv_into_f is_processT5_S7'
          non_tickFree_tick tickFree_append_iff)
  qed
qed


lemma non_terminating_Sync :
  \<open>non_terminating P \<Longrightarrow> lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q \<Longrightarrow> non_terminating (P \<lbrakk>A\<rbrakk> Q)\<close>
  by (simp add: lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_div_free T_Sync
      non_terminating_is_right nonterminating_implies_div_free)
    (metis SyncWithTick_imp_NTF T_imp_front_tickFree ftf_Sync
      nonTickFree_n_frontTickFree non_tickFree_tick tickFree_append_iff)


lemmas non_terminating_Par = non_terminating_Sync[where A = \<open>UNIV\<close>]
  and non_terminating_Inter = non_terminating_Sync[where A = \<open>{}\<close>]



(*<*)
end
  (*>*)
