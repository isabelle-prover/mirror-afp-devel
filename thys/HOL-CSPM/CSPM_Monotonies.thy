(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : CSPM monotonies
 *
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

section\<open> Monotonies \<close>

(*<*)
theory CSPM_Monotonies                                            
  imports Global_Deterministic_Choice Multi_Synchronization_Product
    Multi_Sequential_Composition Interrupt Throw
begin 
  (*>*)


subsection \<open>The Throw Operator\<close>

lemma mono_Throw_F_right :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> a \<in> \<alpha>(P) \<Longrightarrow> Q a \<sqsubseteq>\<^sub>F Q' a) \<Longrightarrow> P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>F P \<Theta> a \<in> A. Q' a\<close>
  unfolding failure_refine_def by (simp add: F_Throw subset_iff disjoint_iff)
    (metis events_of_memI in_set_conv_decomp)

lemma mono_Throw_T_right : 
  \<open>(\<And>a. a \<in> A \<Longrightarrow> a \<in> \<alpha>(P) \<Longrightarrow> Q a \<sqsubseteq>\<^sub>T Q' a) \<Longrightarrow> P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>T P \<Theta> a \<in> A. Q' a\<close>
  unfolding trace_refine_def by (simp add: T_Throw subset_iff disjoint_iff)
    (metis events_of_memI in_set_conv_decomp)

lemma mono_Throw_D_right : 
  \<open>(\<And>a. a \<in> A \<Longrightarrow> a \<in> \<alpha>(P) \<Longrightarrow> Q a \<sqsubseteq>\<^sub>D Q' a) \<Longrightarrow> P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>D P \<Theta> a \<in> A. Q' a\<close>
  unfolding divergence_refine_def by (simp add: D_Throw subset_iff disjoint_iff)
    (metis events_of_memI in_set_conv_decomp)

lemma mono_Throw_FD : \<open>P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>F\<^sub>D P' \<Theta> a \<in> A. Q' a\<close>
  if \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P'\<close> and \<open>\<And>a. a \<in> A \<Longrightarrow> a \<in> \<alpha>(P) \<Longrightarrow> Q a \<sqsubseteq>\<^sub>F\<^sub>D Q' a\<close>
proof (rule trans_FD)
  from \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P'\<close> show \<open>P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>F\<^sub>D P' \<Theta> a \<in> A. Q a\<close>
    by (simp add: refine_defs Throw_projs subset_iff, safe, simp_all flip: T_F_spec, blast)
next
  show \<open>P' \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>F\<^sub>D P' \<Theta> a \<in> A. Q' a\<close>
    by (meson anti_mono_events_of_FD failure_divergence_refine_def
        mono_Throw_D_right mono_Throw_F_right subsetD that)
qed


lemma mono_Throw_DT : \<open>P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>D\<^sub>T P' \<Theta> a \<in> A. Q' a\<close>
  if \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P'\<close> and \<open>\<And>a. a \<in> A \<Longrightarrow> a \<in> \<alpha>(P) \<Longrightarrow> Q a \<sqsubseteq>\<^sub>D\<^sub>T Q' a\<close>
proof (rule trans_DT)
  from \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P'\<close> show \<open>P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>D\<^sub>T P' \<Theta> a \<in> A. Q a\<close>
    by (simp add: refine_defs Throw_projs subset_iff, safe, auto)
next
  show \<open>P' \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>D\<^sub>T P' \<Theta> a \<in> A. Q' a\<close>
    by (meson anti_mono_events_of_DT leDT_imp_leD leDT_imp_leT leD_leT_imp_leDT
        mono_Throw_D_right mono_Throw_T_right subsetD that)
qed


lemmas monos_Throw = mono_Throw mono_Throw_FD mono_Throw_DT
  mono_Throw_F_right mono_Throw_D_right mono_Throw_T_right



subsection \<open>The Interrupt Operator\<close>

lemma mono_Interrupt_T: \<open>P \<sqsubseteq>\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>T Q' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>T P' \<triangle> Q'\<close>
  unfolding trace_refine_def by (auto simp add: T_Interrupt)

lemma mono_Interrupt_D_right : \<open>Q \<sqsubseteq>\<^sub>D Q' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>D P \<triangle> Q'\<close>
  unfolding divergence_refine_def by (auto simp add: D_Interrupt) 

\<comment>\<open>We have no monotony, even partial, with \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>.\<close>

lemma mono_Interrupt_FD:
  \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<triangle> Q'\<close>
  unfolding failure_divergence_refine_def failure_refine_def divergence_refine_def
  by (simp add: D_Interrupt F_Interrupt, safe;
      metis [[metis_verbose = false]] F_subset_imp_T_subset subsetD)

lemma mono_Interrupt_DT:
  \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<triangle> Q'\<close>
  unfolding trace_divergence_refine_def trace_refine_def divergence_refine_def
  by (auto simp add: T_Interrupt D_Interrupt subset_iff)


lemmas monos_Interrupt = mono_Interrupt mono_Interrupt_FD mono_Interrupt_DT
  mono_Interrupt_D_right mono_Interrupt_T



subsection \<open>Global Deterministic Choice\<close>

lemma mono_GlobalDet_DT : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q a) \<Longrightarrow> (\<box>a \<in> A. P a) \<sqsubseteq>\<^sub>D\<^sub>T (\<box>a \<in> A. Q a)\<close>
  and mono_GlobalDet_T  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>T Q a) \<Longrightarrow> (\<box>a \<in> A. P a) \<sqsubseteq>\<^sub>T (\<box>a \<in> A. Q a)\<close>
  and mono_GlobalDet_D  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D Q a) \<Longrightarrow> (\<box>a \<in> A. P a) \<sqsubseteq>\<^sub>D (\<box>a \<in> A. Q a)\<close>
  by (auto simp add: refine_defs GlobalDet_projs)

lemma mono_GlobalDet_FD : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (\<box>a \<in> A. P a) \<sqsubseteq>\<^sub>F\<^sub>D (\<box>a \<in> A. Q a)\<close>
  by (simp add: refine_defs GlobalDet_projs subset_iff) (meson F_T T_F in_mono)

lemmas monos_GlobalDet = mono_GlobalDet mono_GlobalDet_FD mono_GlobalDet_DT
  mono_GlobalDet_T mono_GlobalDet_D

lemma GlobalNdet_FD_GlobalDet : \<open>(\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>F\<^sub>D (\<box>a \<in> A. P a)\<close>
  and GlobalNdet_DT_GlobalDet : \<open>(\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>D\<^sub>T (\<box>a \<in> A. P a)\<close>
  and GlobalNdet_F_GlobalDet  : \<open>(\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>F (\<box>a \<in> A. P a)\<close>
  and GlobalNdet_T_GlobalDet  : \<open>(\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>T (\<box>a \<in> A. P a)\<close>
  and GlobalNdet_D_GlobalDet  : \<open>(\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>D (\<box>a \<in> A. P a)\<close>
  by (simp_all add: refine_defs GlobalDet_projs GlobalNdet_projs subset_iff, safe)
    (blast, blast intro: is_processT8, metis append_Nil is_processT6_TR_notin)+

lemmas GlobalNdet_le_GlobalDet = GlobalNdet_FD_GlobalDet GlobalNdet_DT_GlobalDet
  GlobalNdet_F_GlobalDet GlobalNdet_T_GlobalDet GlobalNdet_D_GlobalDet



subsection \<open>Multiple Synchronization Product\<close>

lemma mono_MultiSync_FD :
  \<open>(\<And>m. m \<in># M \<Longrightarrow> P m \<sqsubseteq>\<^sub>F\<^sub>D Q m) \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m) \<sqsubseteq>\<^sub>F\<^sub>D (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. Q m)\<close>
  and mono_MultiSync_DT :
  \<open>(\<And>m. m \<in># M \<Longrightarrow> P m \<sqsubseteq>\<^sub>D\<^sub>T Q m) \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m) \<sqsubseteq>\<^sub>D\<^sub>T (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. Q m)\<close>
  by (cases \<open>M = {#}\<close>, simp, erule mset_induct_nonempty, simp_all add: monos_Sync)+

lemmas mono_MultiInter_FD = mono_MultiSync_FD[where S = \<open>{}\<close>]
  and mono_MultiInter_DT = mono_MultiSync_DT[where S = \<open>{}\<close>]
  and   mono_MultiPar_FD = mono_MultiSync_FD[where S = \<open>UNIV\<close>]
  and   mono_MultiPar_DT = mono_MultiSync_DT[where S = \<open>UNIV\<close>]

lemmas monos_MultiSync = mono_MultiSync mono_MultiSync_FD mono_MultiSync_DT
  and monos_MultiPar = mono_MultiPar mono_MultiPar_FD mono_MultiPar_DT
  and monos_MultiInter = mono_MultiInter mono_MultiInter_FD mono_MultiInter_DT

text \<open>Monotony doesn't hold for \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>, \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close> and \<^term>\<open>(\<sqsubseteq>\<^sub>D)\<close>.\<close>



subsection \<open>Multiple Sequential Composition\<close>

lemma mono_MultiSeq_FD :
  \<open>(\<And>x. x \<in> set L \<Longrightarrow> P x \<sqsubseteq>\<^sub>F\<^sub>D Q x) \<Longrightarrow> SEQ l \<in>@ L. P l \<sqsubseteq>\<^sub>F\<^sub>D SEQ l \<in>@ L. Q l\<close>
  and mono_MultiSeq_DT :
  \<open>(\<And>x. x \<in> set L \<Longrightarrow> P x \<sqsubseteq>\<^sub>D\<^sub>T Q x) \<Longrightarrow> SEQ l \<in>@ L. P l \<sqsubseteq>\<^sub>D\<^sub>T SEQ l \<in>@ L. Q l\<close>
  by (induct L rule: rev_induct, simp_all add: monos_Seq)

lemmas monos_MultiSeq = mono_MultiSeq mono_MultiSeq_FD  mono_MultiSeq_FD



(*<*)
end
  (*>*)