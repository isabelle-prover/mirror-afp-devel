(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : CSP monotonies
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

section \<open> Monotonies \<close>

(*<*)
theory CSP_Monotonies 
  imports Constant_Processes Deterministic_Choice Non_Deterministic_Choice
    Global_Non_Deterministic_Choice Sliding_Choice
    Multi_Deterministic_Prefix_Choice Multi_Non_Deterministic_Prefix_Choice
    Sequential_Composition Synchronization_Product Hiding Renaming CSP_Refinements
begin
  (*>*)

subsection \<open>Straight Monotony\<close>

subsubsection \<open> Non Deterministic Choice \<close>

lemma mono_Ndet_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P \<sqinter> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<sqinter> Q'\<close>
  and mono_Ndet_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> P \<sqinter> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<sqinter> Q'\<close>
  and mono_Ndet_F  : \<open>P \<sqsubseteq>\<^sub>F P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F Q' \<Longrightarrow> P \<sqinter> Q \<sqsubseteq>\<^sub>F P' \<sqinter> Q'\<close>
  and mono_Ndet_D  : \<open>P \<sqsubseteq>\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D Q' \<Longrightarrow> P \<sqinter> Q \<sqsubseteq>\<^sub>D P' \<sqinter> Q'\<close>
  and mono_Ndet_T  : \<open>P \<sqsubseteq>\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>T Q' \<Longrightarrow> P \<sqinter> Q \<sqsubseteq>\<^sub>T P' \<sqinter> Q'\<close>
  by (auto simp add: refine_defs Ndet_projs)

lemmas monos_Ndet = mono_Ndet mono_Ndet_FD mono_Ndet_DT
  mono_Ndet_F mono_Ndet_D mono_Ndet_T



subsubsection \<open> Global Non Deterministic Choice \<close>

lemma mono_GlobalNdet_FD : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a \<in> A. Q a\<close>
  and mono_GlobalNdet_DT : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q a) \<Longrightarrow> (\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>D\<^sub>T \<sqinter>a \<in> A. Q a\<close>
  and mono_GlobalNdet_F  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F Q a) \<Longrightarrow> (\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>F \<sqinter>a \<in> A. Q a\<close>
  and mono_GlobalNdet_D  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D Q a) \<Longrightarrow> (\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>D \<sqinter>a \<in> A. Q a\<close>
  and mono_GlobalNdet_T  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>T Q a) \<Longrightarrow> (\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>T \<sqinter>a \<in> A. Q a\<close>
  by (auto simp add: refine_defs GlobalNdet_projs)

lemmas monos_GlobalNdet = mono_GlobalNdet mono_GlobalNdet_FD mono_GlobalNdet_DT
  mono_GlobalNdet_F mono_GlobalNdet_D mono_GlobalNdet_T


lemma GlobalNdet_FD_subset : \<open>A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<sqinter>a \<in> B. P a) \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter>a \<in> A. P a)\<close>
  and GlobalNdet_DT_subset : \<open>A \<subseteq> B \<Longrightarrow> (\<sqinter>a \<in> B. P a) \<sqsubseteq>\<^sub>D\<^sub>T (\<sqinter>a \<in> A. P a)\<close>
  and GlobalNdet_F_subset  : \<open>A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<sqinter>a \<in> B. P a) \<sqsubseteq>\<^sub>F (\<sqinter>a \<in> A. P a)\<close>  
  and GlobalNdet_T_subset  : \<open>A \<subseteq> B \<Longrightarrow> (\<sqinter>a \<in> B. P a) \<sqsubseteq>\<^sub>T (\<sqinter>a \<in> A. P a)\<close>
  and GlobalNdet_D_subset  : \<open>A \<subseteq> B \<Longrightarrow> (\<sqinter>a \<in> B. P a) \<sqsubseteq>\<^sub>D (\<sqinter>a \<in> A. P a)\<close>
  by (auto simp add: refine_defs GlobalNdet_projs)

lemmas GlobalNdet_le_subset =
  GlobalNdet_FD_subset GlobalNdet_DT_subset
  GlobalNdet_F_subset GlobalNdet_T_subset GlobalNdet_D_subset



subsubsection \<open> Deterministic Choice \<close>

lemma mono_Det_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P \<box> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<box> Q'\<close>
proof (rule trans_FD)
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> P \<box> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<box> Q\<close>
    unfolding refine_defs F_Det D_Det using F_T T_F by blast
next
  show \<open>Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P' \<box> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<box> Q'\<close>
    unfolding refine_defs F_Det D_Det using F_T T_F by blast
qed

lemma mono_Det_D : \<open>P \<sqsubseteq>\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D Q' \<Longrightarrow> P \<box> Q \<sqsubseteq>\<^sub>D P' \<box> Q'\<close>
  by (metis D_Det Un_mono divergence_refine_def)

lemma mono_Det_T : \<open>P \<sqsubseteq>\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>T Q' \<Longrightarrow> P \<box> Q \<sqsubseteq>\<^sub>T P' \<box> Q'\<close>
  by (metis T_Det Un_mono trace_refine_def)

corollary mono_Det_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> P \<box> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<box> Q'\<close>
  by (simp_all add: trace_divergence_refine_def mono_Det_D mono_Det_T)

text \<open>Deterministic choice monotony doesn't hold for \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>.\<close>

lemmas monos_Det = mono_Det mono_Det_FD mono_Det_DT
  mono_Det_D mono_Det_T



subsubsection \<open>Sliding choice\<close>

lemma mono_Sliding_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<rhd> Q'\<close>
  and mono_Sliding_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<rhd> Q'\<close>
  and mono_Sliding_D  : \<open>P \<sqsubseteq>\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>D P' \<rhd> Q'\<close>
  and mono_Sliding_T  : \<open>P \<sqsubseteq>\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>T Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>T P' \<rhd> Q'\<close>
  unfolding Sliding_def by (simp_all add: monos_Det monos_Ndet)

text \<open>Sliding choice monotony doesn't hold for \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>.\<close>

lemma mono_Sliding_F_right : \<open>Q \<sqsubseteq>\<^sub>F Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>F P \<rhd> Q'\<close>
  by (auto simp add: failure_refine_def F_Sliding)

lemmas monos_Sliding = mono_Sliding mono_Sliding_FD mono_Sliding_DT
  mono_Sliding_D mono_Sliding_T mono_Sliding_F_right



subsubsection \<open>Synchronization\<close>

lemma mono_Sync_FD : \<open>\<lbrakk>P \<sqsubseteq>\<^sub>F\<^sub>D P'; Q \<sqsubseteq>\<^sub>F\<^sub>D Q'\<rbrakk> \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<lbrakk>S\<rbrakk> Q'\<close>
  for P P' Q Q' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule trans_FD[of _ \<open>P' \<lbrakk>S\<rbrakk> Q\<close>])
  show \<open>P \<lbrakk>S\<rbrakk> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<lbrakk>S\<rbrakk> Q\<close> if \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P'\<close> for P P' Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (rule failure_divergence_refine_optimizedI)
    from le_ref1 le_ref2T \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P'\<close>
    show \<open>s \<in> \<D> (P' \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> for s
      unfolding D_Sync by blast
  next
    assume subset_div : \<open>\<D> (P' \<lbrakk>S\<rbrakk> Q) \<subseteq> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    fix s Z assume \<open>(s, Z) \<in> \<F> (P' \<lbrakk>S\<rbrakk> Q)\<close>
    then consider \<open>s \<in> \<D> (P' \<lbrakk>S\<rbrakk> Q)\<close>
      | (F) t u X Y where \<open>(t, X) \<in> \<F> P'\<close> \<open>(u, Y) \<in> \<F> Q\<close>
        \<open>s setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
        \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
      unfolding F_Sync D_Sync by blast
    thus \<open>(s, Z) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof cases
      from subset_div D_F show \<open>s \<in> \<D> (P' \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> (s, Z) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> by blast
    next
      case F
      with le_ref2[OF \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P'\<close>] show \<open>(s, Z) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> unfolding F_Sync by blast
    qed
  qed
  thus \<open>Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P' \<lbrakk>S\<rbrakk> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<lbrakk>S\<rbrakk> Q'\<close> by (metis Sync_commute)
qed

lemma mono_Sync_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<lbrakk>S\<rbrakk> Q'\<close>
  by (simp add: refine_defs T_Sync D_Sync) blast


lemmas mono_Par = mono_Sync[where A = UNIV]
  and mono_Par_FD = mono_Sync_FD[where S = UNIV]
  and mono_Par_DT = mono_Sync_DT[where S = UNIV]
  and mono_Inter = mono_Sync[where A = \<open>{}\<close>]
  and mono_Inter_FD = mono_Sync_FD[where S = \<open>{}\<close>]
  and mono_Inter_DT = mono_Sync_DT[where S = \<open>{}\<close>]


lemmas monos_Sync = mono_Sync mono_Sync_FD mono_Sync_DT
  and monos_Par = mono_Par mono_Par_FD mono_Par_DT
  and monos_Inter = mono_Inter mono_Inter_FD mono_Inter_DT



subsubsection \<open>Sequential composition\<close>

lemma mono_Seq_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P \<^bold>; Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<^bold>; Q'\<close>
  by (simp add: refine_defs Seq_projs subset_iff) (metis T_F_spec)

lemma mono_Seq_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> P \<^bold>; Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<^bold>; Q'\<close>
  by (simp add: refine_defs Seq_projs subset_iff) blast

lemma mono_Seq_F_right : \<open>Q \<sqsubseteq>\<^sub>F Q' \<Longrightarrow> P \<^bold>; Q \<sqsubseteq>\<^sub>F P \<^bold>; Q'\<close>
  by (simp add: failure_refine_def F_Seq) blast

lemma mono_Seq_D_right : \<open>Q \<sqsubseteq>\<^sub>D Q' \<Longrightarrow> P \<^bold>; Q \<sqsubseteq>\<^sub>D P \<^bold>; Q'\<close>
  by (simp add: divergence_refine_def D_Seq) blast

lemma mono_Seq_T_right : \<open>Q \<sqsubseteq>\<^sub>T Q' \<Longrightarrow> P \<^bold>; Q \<sqsubseteq>\<^sub>T P \<^bold>; Q'\<close>
  by (simp add: trace_refine_def T_Seq) blast

text \<open>Left Sequence monotony doesn't hold for \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>, \<^term>\<open>(\<sqsubseteq>\<^sub>D)\<close> and \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>.\<close>

lemmas monos_Seq = mono_Seq mono_Seq_FD mono_Seq_DT
  mono_Seq_F_right mono_Seq_D_right mono_Seq_T_right



subsubsection \<open>Renaming\<close>

lemma mono_Renaming_D : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> Renaming P f g \<sqsubseteq>\<^sub>D Renaming Q f g\<close>
  unfolding divergence_refine_def D_Renaming by blast

lemma mono_Renaming_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Renaming P f g \<sqsubseteq>\<^sub>F\<^sub>D Renaming Q f g\<close>
  using mono_Renaming_D unfolding refine_defs F_Renaming D_Renaming by blast

lemma mono_Renaming_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Renaming P f g \<sqsubseteq>\<^sub>D\<^sub>T Renaming Q f g\<close>
  using mono_Renaming_D unfolding refine_defs T_Renaming D_Renaming by blast

lemmas monos_Renaming = mono_Renaming mono_Renaming_FD mono_Renaming_DT mono_Renaming_D



subsubsection \<open>Hiding\<close>

lemma mono_Hiding_leT_imp_leD : \<open>P \ A \<sqsubseteq>\<^sub>D Q \ A\<close> if \<open>A \<noteq> {}\<close> and \<open>P \<sqsubseteq>\<^sub>T Q\<close>
proof (unfold divergence_refine_def, rule subsetI)
  fix s assume \<open>s \<in> \<D> (Q \ A)\<close>
  then obtain t u
    where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close>
      \<open>s = trace_hide t (ev ` A) @ u\<close>
      \<open>t \<in> \<D> Q \<or> (\<exists>x. isInfHidden_seqRun x Q A t)\<close>
    unfolding D_Hiding_seqRun by blast
  from "*"(4) have \<open>\<exists>x. isInfHidden_seqRun x P A t\<close>
  proof (elim disjE exE)
    assume \<open>t \<in> \<D> Q\<close>
    from \<open>A \<noteq> {}\<close> obtain a where \<open>a \<in> A\<close> by blast
    have \<open>isInfHidden_seqRun (\<lambda>i. ev a) P A t\<close>
    proof (intro allI conjI)
      have \<open>seqRun t (\<lambda>i. ev a) i \<in> \<D> Q\<close> for i
        by (induct i) (simp_all add: \<open>t \<in> \<D> Q\<close> is_processT7 tickFree_seqRun_iff "*"(2))
      thus \<open>seqRun t (\<lambda>i. ev a) i \<in> \<T> P\<close> for i
        by (meson D_T \<open>P \<sqsubseteq>\<^sub>T Q\<close> trace_refine_def subset_iff)
    next
      from \<open>a \<in> A\<close> show \<open>ev a \<in> ev ` A\<close> by simp
    qed
    thus \<open>\<exists>x. isInfHidden_seqRun x P A t\<close> by blast
  next
    show \<open>isInfHidden_seqRun x Q A t \<Longrightarrow> \<exists>x. isInfHidden_seqRun x P A t\<close> for x
      by (meson \<open>P \<sqsubseteq>\<^sub>T Q\<close> trace_refine_def subset_iff)
  qed
  with "*"(1, 2, 3) show \<open>s \<in> \<D> (P \ A)\<close> unfolding D_Hiding_seqRun by blast
qed


lemma mono_Hiding_F : \<open>P \ A \<sqsubseteq>\<^sub>F Q \ A\<close> if \<open>P \<sqsubseteq>\<^sub>F Q\<close>
proof (cases \<open>A = {}\<close>)
  from \<open>P \<sqsubseteq>\<^sub>F Q\<close> show \<open>A = {} \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>F Q \ A\<close>
    by (auto simp add: failure_refine_def F_Hiding_seqRun subset_iff
        intro: is_processT7 is_processT8)
next
  show \<open>P \ A \<sqsubseteq>\<^sub>F Q \ A\<close> if \<open>A \<noteq> {}\<close>
  proof (unfold failure_refine_def, safe)
    fix s X assume \<open>(s, X) \<in> \<F> (Q \ A)\<close>
    then consider \<open>s \<in> \<D> (Q \ A)\<close>
      | t where \<open>s = trace_hide t (ev ` A)\<close> \<open>(t, X \<union> ev ` A) \<in> \<F> Q\<close>
      unfolding F_Hiding_seqRun D_Hiding_seqRun by blast
    thus \<open>(s, X) \<in> \<F> (P \ A)\<close>
    proof cases
      fix t assume \<open>s = trace_hide t (ev ` A)\<close> \<open>(t, X \<union> ev ` A) \<in> \<F> Q\<close>
      from \<open>P \<sqsubseteq>\<^sub>F Q\<close> \<open>(t, X \<union> ev ` A) \<in> \<F> Q\<close> have \<open>(t, X \<union> ev ` A) \<in> \<F> P\<close>
        unfolding failure_refine_def by blast
      with \<open>s = trace_hide t (ev ` A)\<close> show \<open>(s, X) \<in> \<F> (P \ A)\<close>
        unfolding F_Hiding by blast
    next
      from mono_Hiding_leT_imp_leD[OF \<open>A \<noteq> {}\<close> \<open>P \<sqsubseteq>\<^sub>F Q\<close>[THEN leF_imp_leT]]
      show \<open>s \<in> \<D> (Q \ A) \<Longrightarrow> (s, X) \<in> \<F> (P \ A)\<close>
        by (simp add: divergence_refine_def in_mono is_processT8)
    qed
  qed
qed

lemma mono_Hiding_T : \<open>P \ A \<sqsubseteq>\<^sub>T Q \ A\<close> if \<open>P \<sqsubseteq>\<^sub>T Q\<close>
proof (cases \<open>A = {}\<close>)
  from \<open>P \<sqsubseteq>\<^sub>T Q\<close> show \<open>A = {} \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>T Q \ A\<close>
    by (auto simp add: trace_refine_def T_Hiding_seqRun
        subset_iff F_T T_F D_T is_processT7)
next
  show \<open>P \ A \<sqsubseteq>\<^sub>T Q \ A\<close> if \<open>A \<noteq> {}\<close>
  proof (unfold trace_refine_def, rule subsetI)
    fix s assume \<open>s \<in> \<T> (Q \ A)\<close>
    then consider \<open>s \<in> \<D> (Q \ A)\<close>
      | t where \<open>s = trace_hide t (ev ` A)\<close> \<open>(t, ev ` A) \<in> \<F> Q\<close>
      unfolding T_Hiding_seqRun D_Hiding_seqRun by blast
    thus \<open>s \<in> \<T> (P \ A)\<close>
    proof cases
      fix t assume \<open>s = trace_hide t (ev ` A)\<close> \<open>(t, ev ` A) \<in> \<F> Q\<close>
      from \<open>(t, ev ` A) \<in> \<F> Q\<close> have \<open>t \<in> \<T> P\<close>
        by (meson F_T \<open>P \<sqsubseteq>\<^sub>T Q\<close> in_mono trace_refine_def)
      with inf_hidden consider 
        t' where \<open>trace_hide t' (ev ` A) = trace_hide t (ev ` A)\<close> \<open>(t', ev ` A) \<in> \<F> P\<close>
      | f where \<open>isInfHiddenRun f P A \<and> t \<in> range f\<close> by blast
      thus \<open>s \<in> \<T> (P \ A)\<close>
      proof cases
        show \<open>trace_hide t' (ev ` A) = trace_hide t (ev ` A) \<Longrightarrow>
              (t', ev ` A) \<in> \<F> P \<Longrightarrow> s \<in> \<T> (P \ A)\<close> for t'
          by (simp add: T_Hiding_seqRun) (metis \<open>s = trace_hide t (ev ` A)\<close>)
      next
        show \<open>isInfHiddenRun f P A \<and> t \<in> range f \<Longrightarrow> s \<in> \<T> (P \ A)\<close> for f
          by (simp add: T_Hiding)
            (metis T_nonTickFree_imp_decomp \<open>s = trace_hide t (ev ` A)\<close>
              \<open>t \<in> \<T> P\<close> append_self_conv front_tickFree_Nil tick_T_F)
      qed
    next
      from mono_Hiding_leT_imp_leD[OF \<open>A \<noteq> {}\<close> \<open>P \<sqsubseteq>\<^sub>T Q\<close>]
      show \<open>s \<in> \<D> (Q \ A) \<Longrightarrow> s \<in> \<T> (P \ A)\<close>
        by (simp add: divergence_refine_def in_mono D_T)
    qed
  qed
qed

lemma mono_Hiding_FD : \<open>P \ A \<sqsubseteq>\<^sub>F\<^sub>D Q \ A\<close> if \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
proof (cases \<open>A = {}\<close>)
  from \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> show \<open>A = {} \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>F\<^sub>D Q \ A\<close>
    by (simp add: refine_defs F_Hiding_seqRun D_Hiding_seqRun) blast
next
  show \<open>A \<noteq> {} \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>F\<^sub>D Q \ A\<close>
    by (unfold failure_divergence_refine_def)
      (simp add: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> leFD_imp_leF mono_Hiding_F leF_imp_leT mono_Hiding_leT_imp_leD)
qed

lemma mono_Hiding_DT : \<open>P \ A \<sqsubseteq>\<^sub>D\<^sub>T Q \ A\<close> if \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
proof (cases \<open>A = {}\<close>)
  from \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close> show \<open>A = {} \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>D\<^sub>TQ \ A\<close>
    by (auto simp add: refine_defs T_Hiding_seqRun D_Hiding_seqRun F_T T_F in_mono)
next
  show \<open>A \<noteq> {} \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>D\<^sub>T Q \ A\<close>
    by (unfold trace_divergence_refine_def)
      (simp add: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close> leDT_imp_leT mono_Hiding_T mono_Hiding_leT_imp_leD)
qed

text \<open>Obviously, Hide monotony doesn't hold for \<^term>\<open>(\<sqsubseteq>\<^sub>D)\<close>.\<close>


lemmas monos_Hiding = mono_Hiding mono_Hiding_FD mono_Hiding_DT
  mono_Hiding_F mono_Hiding_T



subsubsection \<open>Prefixes\<close>

lemma mono_Mprefix_FD : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>F\<^sub>D Mprefix A Q\<close>
  and mono_Mprefix_DT : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q a) \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>D\<^sub>T Mprefix A Q\<close>
  and mono_Mprefix_F  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F Q a) \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>F Mprefix A Q\<close>
  and mono_Mprefix_T  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>T Q a) \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>T Mprefix A Q\<close>
  and mono_Mprefix_D  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D Q a) \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>D Mprefix A Q\<close>
  by (simp add: refine_defs Mprefix_projs, blast)+

lemmas monos_Mprefix = mono_Mprefix mono_Mprefix_FD mono_Mprefix_DT
  mono_Mprefix_F mono_Mprefix_T mono_Mprefix_D

corollary mono_write0_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> (a \<rightarrow> P) \<sqsubseteq>\<^sub>F\<^sub>D (a \<rightarrow> Q)\<close>
  and     mono_write0_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> (a \<rightarrow> P) \<sqsubseteq>\<^sub>D\<^sub>T (a \<rightarrow> Q)\<close>
  and     mono_write0_F  : \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> (a \<rightarrow> P) \<sqsubseteq>\<^sub>F (a \<rightarrow> Q)\<close>
  and     mono_write0_T  : \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> (a \<rightarrow> P) \<sqsubseteq>\<^sub>T (a \<rightarrow> Q)\<close>
  and     mono_write0_D  : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> (a \<rightarrow> P) \<sqsubseteq>\<^sub>D (a \<rightarrow> Q)\<close>
  unfolding write0_def by (simp_all add: monos_Mprefix)

lemmas monos_write0 = mono_write0 mono_write0_FD mono_write0_DT
  mono_write0_F mono_write0_T mono_write0_D


corollary mono_write_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> (c\<^bold>!a \<rightarrow> P) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>!a \<rightarrow> Q)\<close>
  and     mono_write_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> (c\<^bold>!a \<rightarrow> P) \<sqsubseteq>\<^sub>D\<^sub>T (c\<^bold>!a \<rightarrow> Q)\<close>
  and     mono_write_F  : \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> (c\<^bold>!a \<rightarrow> P) \<sqsubseteq>\<^sub>F (c\<^bold>!a \<rightarrow> Q)\<close>
  and     mono_write_T  : \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> (c\<^bold>!a \<rightarrow> P) \<sqsubseteq>\<^sub>T (c\<^bold>!a \<rightarrow> Q)\<close>
  and     mono_write_D  : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> (c\<^bold>!a \<rightarrow> P) \<sqsubseteq>\<^sub>D (c\<^bold>!a \<rightarrow> Q)\<close>
  by (simp_all add: write_is_write0 monos_write0)

lemmas monos_write = mono_write mono_write_FD mono_write_DT
  mono_write_F mono_write_T mono_write_D


corollary mono_read_FD : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>?a\<in>A \<rightarrow> Q a)\<close>
  and     mono_read_DT : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q a) \<Longrightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>D\<^sub>T (c\<^bold>?a\<in>A \<rightarrow> Q a)\<close>
  and     mono_read_F  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F Q a) \<Longrightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>F (c\<^bold>?a\<in>A \<rightarrow> Q a)\<close>
  and     mono_read_T  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>T Q a) \<Longrightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>T (c\<^bold>?a\<in>A \<rightarrow> Q a)\<close>
  and     mono_read_D  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D Q a) \<Longrightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>D (c\<^bold>?a\<in>A \<rightarrow> Q a)\<close>
  unfolding read_def by (simp_all add: monos_Mprefix inv_into_into)

lemmas monos_read = mono_read mono_read_FD mono_read_DT
  mono_read_F mono_read_T mono_read_D


lemma mono_Mndetprefix_FD : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>F\<^sub>D Mndetprefix A Q\<close>
  and mono_Mndetprefix_DT : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q a) \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>D\<^sub>T Mndetprefix A Q\<close>
  and mono_Mndetprefix_F  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F Q a) \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>F Mndetprefix A Q\<close>
  and mono_Mndetprefix_T  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>T Q a) \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>T Mndetprefix A Q\<close>
  and mono_Mndetprefix_D  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D Q a) \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>D Mndetprefix A Q\<close>
  by (simp add: refine_defs Mndetprefix_projs, blast)+

lemmas monos_Mndetprefix = mono_Mndetprefix mono_Mndetprefix_FD mono_Mndetprefix_DT
  mono_Mndetprefix_F mono_Mndetprefix_T mono_Mndetprefix_D


corollary mono_ndet_write_FD : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a)\<close>
  and     mono_ndet_write_DT : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q a) \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>D\<^sub>T (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a)\<close>
  and     mono_ndet_write_F  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>F Q a) \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>F (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a)\<close>
  and     mono_ndet_write_T  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>T Q a) \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>T (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a)\<close>
  and     mono_ndet_write_D  : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq>\<^sub>D Q a) \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<sqsubseteq>\<^sub>D (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a)\<close>
  unfolding ndet_write_def by (simp_all add: monos_Mndetprefix inv_into_into)

lemmas monos_ndet_write = mono_ndet_write mono_ndet_write_FD mono_ndet_write_DT
  mono_ndet_write_F mono_ndet_write_T mono_ndet_write_D


lemma Mndetprefix_FD_Mprefix : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>F\<^sub>D Mprefix A P\<close>
  and Mndetprefix_DT_Mprefix : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>D\<^sub>T Mprefix A P\<close>
  and Mndetprefix_F_Mprefix  : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>F Mprefix A P\<close>
  and Mndetprefix_T_Mprefix  : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>T Mprefix A P\<close>
  and Mndetprefix_D_Mprefix  : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>D Mprefix A P\<close>
  by (simp_all add: refine_defs Mprefix_projs Mndetprefix_projs) blast+

lemmas Mndetprefix_le_Mprefix =
  Mndetprefix_FD_Mprefix Mndetprefix_DT_Mprefix
  Mndetprefix_F_Mprefix Mndetprefix_T_Mprefix Mndetprefix_D_Mprefix


corollary ndet_write_FD_read : \<open>ndet_write c A P \<sqsubseteq>\<^sub>F\<^sub>D read c A P\<close>
  and     ndet_write_DT_read : \<open>ndet_write c A P \<sqsubseteq>\<^sub>D\<^sub>T read c A P\<close>
  and     ndet_write_F_read  : \<open>ndet_write c A P \<sqsubseteq>\<^sub>F read c A P\<close>
  and     ndet_write_T_read  : \<open>ndet_write c A P \<sqsubseteq>\<^sub>T read c A P\<close>
  and     ndet_write_D_read  : \<open>ndet_write c A P \<sqsubseteq>\<^sub>D read c A P\<close>
  by (simp_all add: read_def ndet_write_def Mndetprefix_le_Mprefix)

lemmas ndet_write_le_read =
  ndet_write_FD_read ndet_write_DT_read
  ndet_write_F_read ndet_write_T_read ndet_write_D_read


lemma Mndetprefix_FD_subset : \<open>A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Mndetprefix B P \<sqsubseteq>\<^sub>F\<^sub>D Mndetprefix A P\<close>
  and Mndetprefix_DT_subset : \<open>A \<subseteq> B \<Longrightarrow> Mndetprefix B P \<sqsubseteq>\<^sub>D\<^sub>T Mndetprefix A P\<close>
  and Mndetprefix_F_subset  : \<open>A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Mndetprefix B P \<sqsubseteq>\<^sub>F Mndetprefix A P\<close>  
  and Mndetprefix_T_subset  : \<open>A \<subseteq> B \<Longrightarrow> Mndetprefix B P \<sqsubseteq>\<^sub>T Mndetprefix A P\<close>
  and Mndetprefix_D_subset  : \<open>A \<subseteq> B \<Longrightarrow> Mndetprefix B P \<sqsubseteq>\<^sub>D Mndetprefix A P\<close>
  by (auto simp add: refine_defs Mndetprefix_projs)

lemmas Mndetprefix_le_subset =
  Mndetprefix_FD_subset Mndetprefix_DT_subset
  Mndetprefix_F_subset Mndetprefix_T_subset Mndetprefix_D_subset


lemma ndet_write_FD_subset : \<open>A \<noteq> {} \<Longrightarrow> (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
  and ndet_write_DT_subset : \<open>(c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>D\<^sub>T (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
  and ndet_write_F_subset  : \<open>A \<noteq> {} \<Longrightarrow> (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>F (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
  and ndet_write_T_subset  : \<open>(c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>T (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
  and ndet_write_D_subset  : \<open>(c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>D (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
  if \<open>inj_on c B\<close> and \<open>A \<subseteq> B\<close>
proof -
  have * : \<open>(P \<circ> inv_into B c) x = (P \<circ> inv_into A c) x\<close> if \<open>x \<in> c ` A\<close> for x
  proof -
    from \<open>x \<in> c ` A\<close> obtain a where \<open>a \<in> A\<close> \<open>x = c a\<close> by blast
    from \<open>a \<in> A\<close> \<open>A \<subseteq> B\<close> have \<open>a \<in> B\<close> by blast
    from \<open>A \<subseteq> B\<close> \<open>inj_on c B\<close> inj_on_subset have \<open>inj_on c A\<close> by blast
    from \<open>a \<in> A\<close> \<open>x = c a\<close> \<open>inj_on c A\<close> have \<open>(inv_into A c) x = a\<close> by simp
    moreover from \<open>a \<in> B\<close> \<open>x = c a\<close> \<open>inj_on c B\<close> have \<open>(inv_into B c) x = a\<close> by simp
    ultimately show \<open>(P \<circ> inv_into B c) x = (P \<circ> inv_into A c) x\<close> by simp
  qed
  show \<open>A \<noteq> {} \<Longrightarrow> (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
    by (metis \<open>A \<subseteq> B\<close> "*" Mndetprefix_FD_subset empty_is_image
        image_mono mono_Mndetprefix_eq ndet_write_def)
  show \<open>(c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>D\<^sub>T (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
    by (metis \<open>A \<subseteq> B\<close> "*" Mndetprefix_DT_subset
        image_mono mono_Mndetprefix_eq ndet_write_def)
  show \<open>A \<noteq> {} \<Longrightarrow> (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>F (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
    by (metis \<open>A \<subseteq> B\<close> "*" Mndetprefix_F_subset empty_is_image
        image_mono mono_Mndetprefix_eq ndet_write_def)
  show \<open>(c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>T (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
    by (metis \<open>A \<subseteq> B\<close> "*" Mndetprefix_T_subset
        image_mono mono_Mndetprefix_eq ndet_write_def)
  show \<open>(c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>D (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<close>
    by (metis \<open>A \<subseteq> B\<close> "*" Mndetprefix_D_subset
        image_mono mono_Mndetprefix_eq ndet_write_def)
qed

lemmas ndet_write_le_subset =
  ndet_write_FD_subset ndet_write_DT_subset
  ndet_write_F_subset ndet_write_T_subset ndet_write_D_subset


lemma Mndetprefix_FD_write0 : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>F\<^sub>D (a \<rightarrow> P a)\<close>
  and Mndetprefix_DT_write0 : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>D\<^sub>T (a \<rightarrow> P a)\<close>
  and Mndetprefix_F_write0  : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>F (a \<rightarrow> P a)\<close>
  and Mndetprefix_T_write0  : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>T (a \<rightarrow> P a)\<close>
  and Mndetprefix_D_write0  : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>D (a \<rightarrow> P a)\<close> if \<open>a \<in> A\<close>
  by (rule Mndetprefix_le_subset[of \<open>{a}\<close>, simplified, OF \<open>a \<in> A\<close>])+

lemmas Mndetprefix_le_write0 =
  Mndetprefix_FD_write0 Mndetprefix_DT_write0
  Mndetprefix_F_write0 Mndetprefix_T_write0 Mndetprefix_D_write0


lemma Mprefix_DT_subset : \<open>A \<subseteq> B \<Longrightarrow> Mprefix B P \<sqsubseteq>\<^sub>D\<^sub>T Mprefix A P\<close>
  and Mprefix_T_subset  : \<open>A \<subseteq> B \<Longrightarrow> Mprefix B P \<sqsubseteq>\<^sub>T Mprefix A P\<close>
  and Mprefix_D_subset  : \<open>A \<subseteq> B \<Longrightarrow> Mprefix B P \<sqsubseteq>\<^sub>D Mprefix A P\<close>
  by (auto simp add: refine_defs Mprefix_projs)

lemmas Mprefix_le_subset = Mprefix_DT_subset Mprefix_T_subset Mprefix_D_subset

text \<open>Mprefix set monotony doesn't hold for \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> and \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>
      where it holds for deterministic choice.\<close>


lemma read_DT_subset : \<open>(c\<^bold>?b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>D\<^sub>T (c\<^bold>?a\<in>A \<rightarrow> P a)\<close>
  and read_T_subset  : \<open>(c\<^bold>?b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>T (c\<^bold>?a\<in>A \<rightarrow> P a)\<close>
  and read_D_subset  : \<open>(c\<^bold>?b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>D (c\<^bold>?a\<in>A \<rightarrow> P a)\<close>
  if \<open>inj_on c B\<close> and \<open>A \<subseteq> B\<close>
proof -
  have * : \<open>(P \<circ> inv_into B c) x = (P \<circ> inv_into A c) x\<close> if \<open>x \<in> c ` A\<close> for x
  proof -
    from \<open>x \<in> c ` A\<close> obtain a where \<open>a \<in> A\<close> \<open>x = c a\<close> by blast
    from \<open>a \<in> A\<close> \<open>A \<subseteq> B\<close> have \<open>a \<in> B\<close> by blast
    from \<open>A \<subseteq> B\<close> \<open>inj_on c B\<close> inj_on_subset have \<open>inj_on c A\<close> by blast
    from \<open>a \<in> A\<close> \<open>x = c a\<close> \<open>inj_on c A\<close> have \<open>(inv_into A c) x = a\<close> by simp
    moreover from \<open>a \<in> B\<close> \<open>x = c a\<close> \<open>inj_on c B\<close> have \<open>(inv_into B c) x = a\<close> by simp
    ultimately show \<open>(P \<circ> inv_into B c) x = (P \<circ> inv_into A c) x\<close> by simp
  qed
  show \<open>(c\<^bold>?b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>D\<^sub>T (c\<^bold>?a\<in>A \<rightarrow> P a)\<close>
    by (metis \<open>A \<subseteq> B\<close> "*" Mprefix_DT_subset image_mono mono_Mprefix_eq read_def)
  show \<open>(c\<^bold>?b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>T (c\<^bold>?a\<in>A \<rightarrow> P a)\<close>
    by (metis \<open>A \<subseteq> B\<close> "*" Mprefix_T_subset image_mono mono_Mprefix_eq read_def)
  show \<open>(c\<^bold>?b\<in>B \<rightarrow> P b) \<sqsubseteq>\<^sub>D (c\<^bold>?a\<in>A \<rightarrow> P a)\<close>
    by (metis \<open>A \<subseteq> B\<close> "*" Mprefix_D_subset image_mono mono_Mprefix_eq read_def)
qed



subsection \<open>Monotony Properties\<close>

subsubsection \<open> Non Deterministic Choice Operator Laws \<close>

lemma Ndet_FD_self_left   : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  and Ndet_DT_self_left   : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>D\<^sub>T P\<close>
  and Ndet_F_self_left    : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F P\<close>
  and Ndet_T_self_left    : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>T P\<close>
  and Ndet_D_self_left    : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>D P\<close>
  and Ndet_FD_self_right  : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  and Ndet_DT_self_right  : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  and Ndet_F_self_right   : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F Q\<close>
  and Ndet_T_self_right   : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>T Q\<close>
  and Ndet_D_self_right   : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>D Q\<close>
  by (simp_all add: refine_defs Ndet_projs)

lemmas Ndet_le_self_left  = Ndet_FD_self_left Ndet_DT_self_left
  Ndet_F_self_left Ndet_T_self_left Ndet_D_self_left
  and Ndet_le_self_right = Ndet_FD_self_right Ndet_DT_self_right
  Ndet_F_self_right Ndet_T_self_right Ndet_D_self_right

lemma Ndet_FD_Det : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F\<^sub>D P \<box> Q\<close>
  and Ndet_DT_Det : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>D\<^sub>T P \<box> Q\<close>
  and Ndet_F_Det  : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F P \<box> Q\<close>
  and Ndet_T_Det  : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>T P \<box> Q\<close>
  and Ndet_D_Det  : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>D P \<box> Q\<close>
  by (auto simp add: refine_defs Det_projs Ndet_projs
      intro: is_processT8 is_processT6_TR_notin)

lemmas Ndet_le_Det = Ndet_FD_Det Ndet_DT_Det Ndet_F_Det Ndet_T_Det Ndet_D_Det

lemma Ndet_FD_Sliding : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F\<^sub>D P \<rhd> Q\<close>
  and Ndet_DT_Sliding : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>D\<^sub>T P \<rhd> Q\<close>
  and Ndet_F_Sliding  : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F P \<rhd> Q\<close>
  and Ndet_T_Sliding  : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>T P \<rhd> Q\<close>
  and Ndet_D_Sliding  : \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>D P \<rhd> Q\<close>
  by (auto simp add: refine_defs Ndet_projs Sliding_projs
      intro: is_processT8 is_processT6_TR_notin)

lemmas Ndet_le_Sliding = Ndet_FD_Sliding Ndet_DT_Sliding
  Ndet_F_Sliding Ndet_T_Sliding Ndet_D_Sliding



lemma GlobalNdet_refine_FD : \<open>a \<in> A \<Longrightarrow> \<sqinter>a \<in> A. P a \<sqsubseteq>\<^sub>F\<^sub>D P a\<close>
  using GlobalNdet_FD_subset[of \<open>{a}\<close> A] by simp

lemma GlobalNdet_refine_DT : \<open>a \<in> A \<Longrightarrow> \<sqinter>a \<in> A. P a \<sqsubseteq>\<^sub>D\<^sub>T P a\<close>
  using GlobalNdet_DT_subset[of \<open>{a}\<close> A] by simp

lemma GlobalNdet_refine_F : \<open>a \<in> A \<Longrightarrow> \<sqinter>a \<in> A. P a \<sqsubseteq>\<^sub>F P a\<close>
  by (simp add: GlobalNdet_refine_FD leFD_imp_leF)

lemma GlobalNdet_refine_D : \<open>a \<in> A \<Longrightarrow> \<sqinter>a \<in> A. P a \<sqsubseteq>\<^sub>D P a\<close>
  by (simp add: GlobalNdet_refine_DT leDT_imp_leD)

lemma GlobalNdet_refine_T : \<open>a \<in> A \<Longrightarrow> \<sqinter>a \<in> A. P a \<sqsubseteq>\<^sub>T P a\<close>
  by (simp add: GlobalNdet_refine_DT leDT_imp_leT)

lemmas GlobalNdet_refine_le = GlobalNdet_refine_FD GlobalNdet_refine_DT
  GlobalNdet_refine_F GlobalNdet_refine_D GlobalNdet_refine_T 


lemma mono_GlobalNdet_FD_const:
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a \<in> A. Q a\<close>
  by (metis GlobalNdet_id mono_GlobalNdet_FD)

lemma mono_GlobalNdet_DT_const:
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q a) \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T \<sqinter>a \<in> A. Q a\<close>
  by (metis GlobalNdet_id mono_GlobalNdet_DT)

lemma mono_GlobalNdet_F_const:
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q a) \<Longrightarrow> P \<sqsubseteq>\<^sub>F \<sqinter>a \<in> A. Q a\<close>
  by (metis GlobalNdet_id mono_GlobalNdet_F)

lemma mono_GlobalNdet_D_const:
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q a) \<Longrightarrow> P \<sqsubseteq>\<^sub>D \<sqinter>a \<in> A. Q a\<close>
  by (metis GlobalNdet_id mono_GlobalNdet_D)

lemma mono_GlobalNdet_T_const:
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q a) \<Longrightarrow> P \<sqsubseteq>\<^sub>T \<sqinter>a \<in> A. Q a\<close>
  by (metis GlobalNdet_id mono_GlobalNdet_T)

lemmas mono_GlobalNdet_le_const = mono_GlobalNdet_FD_const mono_GlobalNdet_DT_const
  mono_GlobalNdet_F_const mono_GlobalNdet_D_const mono_GlobalNdet_T_const



subsubsection \<open> Refinements and Constant Processes \<close>

lemma STOP_T_iff: \<open>STOP \<sqsubseteq>\<^sub>T P \<longleftrightarrow> P = STOP\<close>
  by (metis STOP_iff_T insert_absorb is_processT1_TR subset_singleton_iff trace_refine_def)

lemma STOP_F_iff: \<open>STOP \<sqsubseteq>\<^sub>F P \<longleftrightarrow> P = STOP\<close>
  using STOP_T_iff idem_F leF_imp_leT by blast

lemma STOP_FD_iff: \<open>STOP \<sqsubseteq>\<^sub>F\<^sub>D P \<longleftrightarrow> P = STOP\<close>
  using STOP_F_iff leFD_imp_leF by blast

lemma STOP_DT_iff: \<open>STOP \<sqsubseteq>\<^sub>D\<^sub>T P \<longleftrightarrow> P = STOP\<close>
  using STOP_T_iff idem_DT leDT_imp_leT by blast


lemma SKIP_FD_iff: \<open>SKIP r \<sqsubseteq>\<^sub>F\<^sub>D P \<longleftrightarrow> P = SKIP r\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule iffI)
  show \<open>P = SKIP r \<Longrightarrow> SKIP r \<sqsubseteq>\<^sub>F\<^sub>D P\<close> by simp
next
  show \<open>P = SKIP r\<close> if \<open>SKIP r \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  proof (rule FD_antisym[OF _ \<open>SKIP r \<sqsubseteq>\<^sub>F\<^sub>D P\<close>])
    show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r\<close>
    proof (rule failure_divergence_refineI)
      from \<open>SKIP r \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>s \<in> \<D> (SKIP r) \<Longrightarrow> s \<in> \<D> P\<close> for s
        by (simp add: refine_defs D_SKIP)
    next
      fix s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and X assume \<open>(s, X) \<in> \<F> (SKIP r)\<close>
      then consider \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> | \<open>s = [\<checkmark>(r)]\<close> unfolding F_SKIP by blast
      thus \<open>(s, X) \<in> \<F> P\<close>
      proof cases
        from \<open>SKIP r \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>s = [] \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> P\<close>
          by (simp add: refine_defs F_SKIP D_SKIP subset_iff)
            (metis T_F append_Nil is_processT1_TR is_processT5_S7 is_processT6_TR_notin not_Cons_self2)
      next
        from \<open>SKIP r \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>s = [\<checkmark>(r)] \<Longrightarrow> (s, X) \<in> \<F> P\<close>
          by (simp add: refine_defs F_SKIP D_SKIP subset_iff)
            (metis (no_types) Int_insert_right_if0 is_processT1 list.simps(15) non_tickFree_tick
              tickFree_Nil tickFree_def tick_T_F trace_tick_continuation_or_all_tick_failuresE)
      qed
    qed
  qed
qed


lemma SKIP_F_iff: \<open>SKIP r \<sqsubseteq>\<^sub>F P \<longleftrightarrow> P = SKIP r\<close>
proof (rule iffI)
  show \<open>P = SKIP r \<Longrightarrow> SKIP r \<sqsubseteq>\<^sub>F P\<close> by simp
next
  assume \<open>SKIP r \<sqsubseteq>\<^sub>F P\<close>
  hence \<open>SKIP r \<sqsubseteq>\<^sub>D P\<close>
    by (simp add: failure_refine_def divergence_refine_def subset_iff F_SKIP D_SKIP)
      (metis append_Nil equals0I insertI1 is_processT8 is_processT9 list.distinct(1))
  with \<open>SKIP r \<sqsubseteq>\<^sub>F P\<close> have \<open>SKIP r \<sqsubseteq>\<^sub>F\<^sub>D P\<close> by (unfold failure_divergence_refine_def) simp
  thus \<open>P = SKIP r\<close> by (fact SKIP_FD_iff[THEN iffD1])
qed




(* TODO: prove a new version of this result, should be something like
  and move it
  \<open>P \<^bold>; Q = SKIP r \<longleftrightarrow> \<exists>S. (P = \<sqinter>s \<in> S. SKIP s) \<and> (\<forall>s \<in> S. Q s = SKIP r)\<close> 

lemma Seq_is_SKIP_iff: \<open>P \<^bold>; Q = SKIP r \<longleftrightarrow> (\<exists>s. P = SKIP s \<and> Q s = SKIP r)\<close>
proof (intro iffI)
  show \<open>\<exists>s. P = SKIP s \<and> Q s = SKIP r \<Longrightarrow> P \<^bold>; Q = SKIP r\<close>
    by (elim exE) (simp add: SKIP_Seq)
next
  assume \<open>P \<^bold>; Q = SKIP r\<close>

  obtain s where \<open>\<exists>t \<in> \<T> P. tick s \<in> t\<close>
  { fix t X assume \<open>(t, X) \<in> \<F> P\<close>
    hence \<open>\<exists>s. (t, X) \<in> \<F> (SKIP s)\<close>
      sorry
  }
  then obtain s where \<open>SKIP s \<sqsubseteq>\<^sub>F P\<close> unfolding failure_refine_def sledgehammer
  { fix t X assume \<open>(t, X) \<in> \<F> (Q\<close>
    hence \<open>\<exists>s. (t, X) \<in> \<F> (SKIP r)\<close>
      sorry
  }
  hence \<open>\<exists>s. \<close>
  thus \<open>\<exists>s. P = SKIP s \<and> Q s = SKIP r\<close>
    
    apply (simp add: Process_eq_spec F_Seq F_SKIP D_Seq D_SKIP, safe; simp)

  { fix s X
    assume \<open>(s, X) \<in> \<F> P\<close>
  hence \<open>\<F> (P \<^bold>; Q) = \<F> (SKIP r)\<close> by simp
  thm this[simplified F_SKIP, simplified]
  thm this[simplified Process_eq_spec, simplified F_Seq D_Seq F_SKIP D_SKIP, simplified, simplified]
  apply (intro iffI, simp_all add: Seq_SKIP)
  apply (simp add: SKIP_F_iff[symmetric])
  unfolding failure_refine_def
proof (auto simp add: F_Seq F_SKIP D_Seq D_SKIP subset_iff intro: T_F, goal_cases)
  case (1 s X)
  thus ?case
    apply (cases \<open>tickFree s\<close>) 
     apply (erule_tac x = s in allE, 
            metis F_T append.right_neutral is_processT4_empty is_processT5_S4 process_charn)
    by (erule_tac x = \<open>butlast s\<close> in allE,
        metis F_T append.right_neutral append_butlast_last_id append_single_T_imp_tickFree
        last_snoc nonTickFree_n_frontTickFree non_tickFree_tick process_charn self_append_conv2)
next
  case (2 s X)
  thus ?case
    by (metis F_T append_Nil2 append_self_conv2 butlast_snoc front_tickFree_iff_tickFree_butlast
        insert_Diff insert_Diff_single nonTickFree_n_frontTickFree non_tickFree_tick process_charn)
qed (metis F_T append.left_neutral insertI1 insert_absorb2 is_processT5_S6 tickFree_Nil)+

 *)



(*<*)
end
  (*>*)