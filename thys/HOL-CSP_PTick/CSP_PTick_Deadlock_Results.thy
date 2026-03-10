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


chapter \<open>Deadlock Results\<close>

(*<*)
theory CSP_PTick_Deadlock_Results
  imports "HOL-CSP_RS" Read_Write_CSP_PTick_Laws CSP_PTick_Monotonicities
    "HOL-CSP_OpSem" Events_Ticks_CSP_PTick_Laws
begin                                                                      
  (*>*)


section \<open>First Results\<close>

subsection \<open>Non Terminating\<close>

text \<open>Keep in mind @{thm lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_div_free[no_vars]}.\<close>

subsubsection \<open>Sequential Composition\<close>

lemma \<open>non_terminating P \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q = RenamingTick P g\<close>
  \<comment> \<open>Already proven earlier.\<close>
  by (fact non_terminating_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)



subsubsection \<open>Synchronization Product\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) non_terminating_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>non_terminating P \<Longrightarrow> lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q \<Longrightarrow> non_terminating (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  \<open>lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> non_terminating Q \<Longrightarrow> non_terminating (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  by (simp add: lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_div_free T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      non_terminating_is_right nonterminating_implies_div_free,
      use setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp in blast)+



subsection \<open>Deadlock Free\<close>

subsubsection \<open>Sequential Composition\<close>

lemma \<open>deadlock_free P \<Longrightarrow> deadlock_free (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  by (metis deadlock_free_imp_deadlock_free_Renaming deadlock_free_implies_lifelock_free
            lifelock_free_is_non_terminating non_terminating_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)


text \<open>The next lemma is of course more interesting.\<close>

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  if df_assms : \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> \<open>\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Q r)\<close>
proof (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right, intro ballI impI)
  show \<open>t \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> for t
  proof (induct t rule: rev_induct)
    from df_assms show \<open>([], UNIV) \<notin> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_UNIV)
        (metis F_T append_Nil deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free
               deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right empty_iff strict_ticks_of_memI tickFree_Nil)
  next
    from df_assms(1) have \<open>\<D> P = {}\<close>
      by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free)
    fix t e assume hyp : \<open>t \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
    assume \<open>t @ [e] \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>tF (t @ [e])\<close>
    then consider u v where \<open>t @ [e] = map (ev \<circ> of_ev) u\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close>
      | u r v where \<open>t @ [e] = map (ev \<circ> of_ev) u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF u\<close> \<open>v \<in> \<T> (Q r)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs \<open>\<D> P = {}\<close>)
    thus \<open>(t @ [e], UNIV) \<notin> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (cases; simp_all add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_UNIV)
        (metis (no_types) F_T \<open>\<D> P = {}\<close> \<open>tF (t @ [e])\<close> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right
                          empty_iff strict_ticks_of_memI that tickFree_append_iff)+
  qed
qed


corollary deadlock_free_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<lbrakk>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P; \<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> deadlock_free (Q r)\<rbrakk>
   \<Longrightarrow> deadlock_free (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  by (simp add: AfterExt.deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ticks_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    (meson deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free)



subsubsection \<open>Synchronization Product\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin

lemma deadlock_free_Det_bis :
  \<open>P = STOP \<and> Q \<noteq> STOP \<or> deadlock_free P \<Longrightarrow>
   Q = STOP \<and> P \<noteq> STOP \<or> deadlock_free Q \<Longrightarrow> deadlock_free (P \<box> Q)\<close>
  using deadlock_free_Det by auto

lemma deadlock_free_Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix :
  assumes not_all_empty: \<open>\<not> A \<subseteq> S \<or> \<not> B \<subseteq> S \<or> A \<inter> B \<inter> S \<noteq> {}\<close>
    and \<open>\<And>a. a \<in> A - S \<Longrightarrow> deadlock_free (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)\<close>
    and \<open>\<And>b. b \<in> B - S \<Longrightarrow> deadlock_free (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
    and \<open>\<And>x. x \<in> A \<inter> B \<inter> S \<Longrightarrow> deadlock_free (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close> 
  shows \<open>deadlock_free (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b \<in> B \<rightarrow> Q b)\<close>
  unfolding Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix using not_all_empty
  by (auto intro!: deadlock_free_Det_bis
      simp add: Mprefix_is_STOP_iff Det_is_STOP_iff deadlock_free_Mprefix_iff assms(2-4))


lemma deadlock_free_Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_subset :
  \<open>\<lbrakk>A \<subseteq> S; B \<subseteq> S; A \<inter> B \<noteq> {};
    \<And>x. x \<in> A \<inter> B \<inter> S \<Longrightarrow> deadlock_free (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<rbrakk>
   \<Longrightarrow> deadlock_free (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)\<close>
  and deadlock_free_Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_indep :
  \<open>\<lbrakk>A \<inter> S = {}; B \<inter> S = {}; A \<noteq> {} \<or> B \<noteq> {};
    \<And>a. a \<in> A - S \<Longrightarrow> deadlock_free (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b);
    \<And>b. b \<in> B - S \<Longrightarrow> deadlock_free (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<rbrakk>
   \<Longrightarrow> deadlock_free (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)\<close>
  and deadlock_free_Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_right :
  \<open>\<lbrakk>A \<subseteq> S; B \<inter> S = {}; B \<noteq> {};
    \<And>b. b \<in> B - S \<Longrightarrow> deadlock_free (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<rbrakk>
   \<Longrightarrow> deadlock_free (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)\<close>
  and deadlock_free_Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_left :
  \<open>\<lbrakk>A \<inter> S = {}; B \<subseteq> S; A \<noteq> {};
    \<And>a. a \<in> A - S \<Longrightarrow> deadlock_free (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)\<rbrakk>
   \<Longrightarrow> deadlock_free (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)\<close>
  by (auto intro!: deadlock_free_Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix)


end



section \<open>Renaming and reference Processes\<close>

\<comment> \<open>Should have been declared simp earlier.\<close>
lemma DF_empty        [simp] : \<open>DF {} = STOP\<close>
  and DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_empty    [simp] : \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S {} {} = STOP\<close>
  and RUN_empty       [simp] : \<open>RUN {} = STOP\<close>
  and CHAOS_empty     [simp] : \<open>CHAOS {} = STOP\<close>
  and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_empty [simp] : \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S {} {} = STOP\<close>
  by (subst DF_unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold RUN_unfold CHAOS_unfold CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold, simp)+



subsection \<open>Alternative Definitions with restriction fixed-point Operator\<close>

text \<open>
For now, we have lemmas such as @{thm DF_FD_Renaming_DF[no_vars]}, but the other refinement is
requiring \<^const>\<open>finitary\<close> assumptions (@{thm Renaming_DF_FD_DF[no_vars]}).
\<close>

lemma DF_restriction_fix_def : \<open>DF A = (\<upsilon> X. \<sqinter>a \<in> A \<rightarrow> X)\<close>
  unfolding DF_def by (rule restriction_fix_is_fix[symmetric]) simp_all

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_restriction_fix_def : \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R = (\<upsilon> X. (\<sqinter>a \<in> A \<rightarrow> X) \<sqinter> SKIPS R)\<close>
  unfolding DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def by (rule restriction_fix_is_fix[symmetric]) simp_all

lemma RUN_restriction_fix_def : \<open>RUN A = (\<upsilon> X. \<box>a \<in> A \<rightarrow> X)\<close>
  unfolding RUN_def by (rule restriction_fix_is_fix[symmetric]) simp_all

lemma CHAOS_restriction_fix_def : \<open>CHAOS A = (\<upsilon> X. STOP \<sqinter> (\<box>a \<in> A \<rightarrow> X))\<close>
  unfolding CHAOS_def by (rule restriction_fix_is_fix[symmetric]) simp_all

lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_restriction_fix_def : \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R = (\<upsilon> X. SKIPS R \<sqinter> STOP \<sqinter> (\<box>a \<in> A \<rightarrow> X))\<close>
  unfolding CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def by (rule restriction_fix_is_fix[symmetric]) simp_all



subsection \<open>Stronger Results\<close>

text \<open>With \<^const>\<open>restriction_fix\<close> induction, removing these assumptions is trivial.\<close>

lemma Renaming_DF : \<open>Renaming (DF A) f g = DF (f ` A)\<close>
proof (unfold DF_restriction_fix_def, induct rule: parallel_restriction_fix_ind)
  show \<open>Renaming STOP f g = STOP\<close> by simp
qed (auto simp add: Renaming_Mndetprefix intro!: mono_Mndetprefix_eq)

lemma Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g = DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close>
proof (unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_restriction_fix_def, induct rule: parallel_restriction_fix_ind)
  show \<open>Renaming STOP f g = STOP\<close> by simp
qed (auto simp add: Renaming_Mndetprefix Renaming_Ndet
    intro!: mono_Mndetprefix_eq arg_cong2[where f = \<open>(\<sqinter>)\<close>])

lemma Renaming_RUN : \<open>Renaming (RUN A) f g = RUN (f ` A)\<close>
proof (unfold RUN_restriction_fix_def, induct rule: parallel_restriction_fix_ind)
  show \<open>Renaming STOP f g = STOP\<close> by simp
qed (auto simp add: Renaming_Mprefix intro!: mono_Mprefix_eq)

lemma Renaming_CHAOS : \<open>Renaming (CHAOS A) f g = CHAOS (f ` A)\<close>
proof (unfold CHAOS_restriction_fix_def, induct rule: parallel_restriction_fix_ind)
  show \<open>Renaming STOP f g = STOP\<close> by simp
qed (auto simp add: Renaming_Mprefix Renaming_Ndet
    intro!: mono_Mprefix_eq arg_cong2[where f = \<open>(\<sqinter>)\<close>])

lemma Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g = CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close>
proof (unfold CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_restriction_fix_def, induct rule: parallel_restriction_fix_ind)
  show \<open>Renaming STOP f g = STOP\<close> by simp
qed (auto simp add: Renaming_Mprefix Renaming_Ndet
    intro!: mono_Mprefix_eq arg_cong2[where f = \<open>(\<sqinter>)\<close>])



section \<open>Data Independence\<close>

text (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) \<open>
When working with the new interleaving \<^term>\<open>P |||\<^sub>\<checkmark> Q\<close>, we intuitively expect it to be
\<^const>\<open>deadlock_free\<close> when both \<^term>\<open>P\<close> and \<^term>\<open>Q\<close> are.
The purpose of this section is to prove it.
\<close>

subsection \<open>An interesting equivalence\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) deadlock_free_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF:
  \<open>(\<forall>P Q. deadlock_free P \<longrightarrow> deadlock_free Q \<longrightarrow> deadlock_free (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))
   \<longleftrightarrow> DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D (DF UNIV \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF UNIV)\<close> (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
proof (rule iffI)
  assume ?lhs
  show ?rhs by (fold deadlock_free_def, rule \<open>?lhs\<close>[rule_format])
      (simp_all add: deadlock_free_def)
next
  assume ?rhs
  show ?lhs unfolding deadlock_free_def
    by (intro allI impI trans_FD[OF \<open>?rhs\<close>]) (rule mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)
qed



subsection \<open>\<^const>\<open>STOP\<close> and \<^const>\<open>SKIP\<close> synchronized with \<^term>\<open>DF A\<close>\<close>

text \<open>The two results below form a stronger (and generalized)
      version of @{thm DF_FD_DF_Sync_SKIP_iff[of r s A S]}.\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS_imp_disjoint :
  \<open>A \<inter> S = {}\<close> if \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIPS R\<close>
proof (rule ccontr)
  assume \<open>A \<inter> S \<noteq> {}\<close>
  then obtain a where \<open>a \<in> A\<close> and \<open>a \<in> S\<close> by blast
  have \<open>DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIPS R \<sqsubseteq>\<^sub>F\<^sub>D DF {a} \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIPS R\<close>
    by (intro mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD[OF _ idem_FD]) (simp add: DF_subset \<open>a \<in> A\<close>)
  also have \<open>\<dots> = STOP\<close>
    by (subst DF_unfold)
      (simp add: \<open>a \<in> S\<close> SKIPS_def Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left
        write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP)
  finally show False
    by (metis that \<open>a \<in> A\<close> DF_Univ_freeness empty_iff non_deadlock_free_STOP trans_FD)
qed


lemma disjoint_imp_DF_eq_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS :
  \<open>DF A = DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIPS R\<close> if \<open>A \<inter> S = {}\<close>
proof (subst DF_restriction_fix_def, induct rule: restriction_fix_ind)
  show \<open>X = DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIPS R \<Longrightarrow> \<sqinter>a\<in>A \<rightarrow> X = DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIPS R\<close> for X
    by (subst DF_unfold)
      (auto simp add: SKIPS_def Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left
        Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP
        \<open>A \<inter> S = {}\<close> Mndetprefix_distrib_GlobalNdet)
qed simp_all


corollary DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP_imp_disjoint :
  \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP \<Longrightarrow> A \<inter> S = {}\<close>
  and DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP_imp_disjoint :
  \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r \<Longrightarrow> A \<inter> S = {}\<close>
  and disjoint_imp_DF_eq_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP :
  \<open>A \<inter> S = {} \<Longrightarrow> DF A = DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP\<close>
  and disjoint_imp_DF_eq_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP :
  \<open>A \<inter> S = {} \<Longrightarrow> DF A = DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r\<close>
  by (fact DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS_imp_disjoint[where R = \<open>{}\<close>, simplified]
      DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS_imp_disjoint[where R = \<open>{r}\<close>, simplified]
      disjoint_imp_DF_eq_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS[where R = \<open>{}\<close>, simplified]
      disjoint_imp_DF_eq_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS[where R = \<open>{r}\<close>, simplified])+


end

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) DF_FD_SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_imp_disjoint :
  \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D SKIPS R \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF A \<Longrightarrow> A \<inter> S = {}\<close>
  by (metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS_imp_disjoint Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) disjoint_imp_DF_eq_SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF :
  \<open>A \<inter> S = {} \<Longrightarrow> DF A = SKIPS R \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF A\<close>
  by (metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.disjoint_imp_DF_eq_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)


corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) DF_FD_STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_imp_disjoint :
  \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF A \<Longrightarrow> A \<inter> S = {}\<close>
  and DF_FD_SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_imp_disjoint :
  \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF A \<Longrightarrow> A \<inter> S = {}\<close>
  and disjoint_imp_DF_eq_STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF :
  \<open>A \<inter> S = {} \<Longrightarrow> DF A = STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF A\<close>
  and disjoint_imp_DF_eq_SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF :
  \<open>A \<inter> S = {} \<Longrightarrow> DF A = SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF A\<close>
  by (fact DF_FD_SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_imp_disjoint[where R = \<open>{}\<close>, simplified]
      DF_FD_SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_imp_disjoint[where R = \<open>{r}\<close>, simplified]
      disjoint_imp_DF_eq_SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF[where R = \<open>{}\<close>, simplified]
      disjoint_imp_DF_eq_SKIPS_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF[where R = \<open>{r}\<close>, simplified])+




subsection \<open>Finally, \<^term>\<open>deadlock_free (P ||| Q)\<close>\<close>

theorem (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) DF_F_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_weak : \<open>DF (A \<union> B) \<sqsubseteq>\<^sub>F DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF B\<close>
  if nonempty: \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close>
    and intersect_hyp: \<open>B \<inter> S = {} \<or> (\<exists>y. B \<inter> S = {y} \<and> A \<inter> S \<subseteq> {y})\<close>
proof -
  have \<open>\<lbrakk>(u, X) \<in> \<F> (DF A); (v, Y) \<in> \<F> (DF B); t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v), S)\<rbrakk>
        \<Longrightarrow> (t, super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X S Y) \<in> \<F> (DF (A \<union> B))\<close> for v t u X Y
  proof (induct t arbitrary: u v)
    case Nil
    from Nil.prems(3) have \<open>u = []\<close> \<open>v = []\<close> by (simp_all add: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    from Nil.prems(1) obtain a where \<open>a \<in> A\<close> \<open>ev a \<notin> X\<close>
      by (subst (asm) F_DF) (auto simp add: nonempty \<open>u = []\<close>)
    moreover from Nil.prems(2) obtain b where \<open>b \<in> B\<close> \<open>ev b \<notin> Y\<close>
      by (subst (asm) F_DF) (auto simp add: nonempty \<open>v = []\<close>)
    ultimately show ?case
      using intersect_hyp
      by (subst F_DF, simp add: nonempty super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff)
        (metis Int_iff empty_iff insert_iff)
  next
    case (Cons e t)
    from Cons.prems(3) consider (mv_left) a u' where \<open>a \<notin> S\<close> \<open>e = ev a\<close> \<open>u = ev a # u'\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u', v), S)\<close>
    | (mv_right) b v' where \<open>b \<notin> S\<close> \<open>e = ev b\<close> \<open>v = ev b # v'\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v'), S)\<close>
    | (mv_both_ev) a u' v' where \<open>a \<in> S\<close> \<open>e = ev a\<close> \<open>u = ev a # u'\<close> \<open>v = ev a # v'\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u', v'), S)\<close>
    | (mv_both_tick) r s r_s u' v' where \<open>r \<otimes>\<checkmark> s = Some r_s\<close> \<open>e = \<checkmark>(r_s)\<close>
      \<open>u = \<checkmark>(r) # u'\<close> \<open>v = \<checkmark>(s) # v'\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u', v'), S)\<close>
      by (cases e) (auto elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    thus ?case
    proof cases
      case mv_left
      from Cons.prems(1) have \<open>a \<in> A\<close>
        by (subst (asm) F_DF) (simp add: mv_left(3) split: if_split_asm)
      from Cons.prems(1)[unfolded mv_left(3), THEN Cons_F_DF] have \<open>(u', X) \<in> \<F> (DF A)\<close> .
      from Cons.hyps[OF this Cons.prems(2) mv_left(4)] show ?thesis
        by (subst F_DF) (simp add: nonempty \<open>e = ev a\<close> \<open>a \<in> A\<close>)
    next
      case mv_right
      from Cons.prems(2) have \<open>b \<in> B\<close>
        by (subst (asm) F_DF) (simp add: mv_right(3) split: if_split_asm)
      from Cons.prems(2)[unfolded mv_right(3), THEN Cons_F_DF] have \<open>(v', Y) \<in> \<F> (DF B)\<close> .
      from Cons.hyps[OF Cons.prems(1) this mv_right(4)] show ?thesis
        by (subst F_DF) (simp add: nonempty \<open>e = ev b\<close> \<open>b \<in> B\<close>)
    next
      case mv_both_ev
      from Cons.prems(1) have \<open>a \<in> A\<close>
        by (subst (asm) F_DF) (simp add: mv_both_ev(3) split: if_split_asm)
      from Cons.prems(1)[unfolded mv_both_ev(3), THEN Cons_F_DF]
        Cons.prems(2)[unfolded mv_both_ev(4), THEN Cons_F_DF]
      have \<open>(u', X) \<in> \<F> (DF A)\<close> \<open>(v', Y) \<in> \<F> (DF B)\<close> .
      from Cons.hyps[OF this mv_both_ev(5)] show ?thesis
        by (subst F_DF) (simp add: nonempty \<open>e = ev a\<close> \<open>a \<in> A\<close>)
    next
      case mv_both_tick
      from Cons.prems(1) have False
        by (subst (asm) F_DF) (simp add: mv_both_tick(3) split: if_split_asm)
      thus ?thesis ..
    qed
  qed
  thus \<open>DF (A \<union> B) \<sqsubseteq>\<^sub>F DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF B\<close>
    by (simp add: failure_refine_def F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k div_free_DF)
      (use is_processT4 in blast)
qed


theorem (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) DF_F_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF :
  \<open>DF (A \<union> B) \<sqsubseteq>\<^sub>F DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF B\<close> if \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close>
  and \<open>A \<inter> S = {} \<or> (\<exists>a. A \<inter> S = {a} \<and> B \<inter> S \<subseteq> {a}) \<or>
       B \<inter> S = {} \<or> (\<exists>b. B \<inter> S = {b} \<and> A \<inter> S \<subseteq> {b})\<close>
proof -
  from that(3) consider \<open>A \<inter> S = {} \<or> (\<exists>a. A \<inter> S = {a} \<and> B \<inter> S \<subseteq> {a})\<close>
    | \<open>B \<inter> S = {} \<or> (\<exists>b. B \<inter> S = {b} \<and> A \<inter> S \<subseteq> {b})\<close> by metis
  thus \<open>DF (A \<union> B) \<sqsubseteq>\<^sub>F DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF B\<close>
  proof cases
    from that(1, 2) show \<open>B \<inter> S = {} \<or> (\<exists>b. B \<inter> S = {b} \<and> A \<inter> S \<subseteq> {b}) \<Longrightarrow>
                          DF (A \<union> B) \<sqsubseteq>\<^sub>F DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF B\<close>
      by (rule DF_F_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_weak)
  next
    from that(1, 2) show \<open>A \<inter> S = {} \<or> (\<exists>a. A \<inter> S = {a} \<and> B \<inter> S \<subseteq> {a}) \<Longrightarrow>
                          DF (A \<union> B) \<sqsubseteq>\<^sub>F DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF B\<close>
      by (fold Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym, subst Un_commute)
        (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.DF_F_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_weak)
  qed
qed


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF :
  \<open>DF (A \<union> B) \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF B\<close> if \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close>
  and \<open>A \<inter> S = {} \<or> (\<exists>a. A \<inter> S = {a} \<and> B \<inter> S \<subseteq> {a}) \<or>
       B \<inter> S = {} \<or> (\<exists>b. B \<inter> S = {b} \<and> A \<inter> S \<subseteq> {b})\<close>
  using DF_F_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF[OF that]
  by (simp add: refine_defs div_free_DF D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)


theorem (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_iff:
  \<open>DF (A \<union> B) \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF B \<longleftrightarrow> 
   (     if A = {} then B \<inter> S = {}
    else if B = {} then A \<inter> S = {}
    else A \<inter> S = {} \<or> (\<exists>a. A \<inter> S = {a} \<and> B \<inter> S \<subseteq> {a}) \<or>
         B \<inter> S = {} \<or> (\<exists>b. B \<inter> S = {b} \<and> A \<inter> S \<subseteq> {b}))\<close>
  (is \<open>?FD_ref \<longleftrightarrow> (     if A = {} then B \<inter> S = {}
                    else if B = {} then A \<inter> S = {} 
                    else ?cases)\<close>)
proof -
  { assume \<open>A \<noteq> {}\<close> and \<open>B \<noteq> {}\<close> and ?FD_ref and \<open>\<not> ?cases\<close>
    from \<open>\<not> ?cases\<close>[simplified] 
    obtain a and b where \<open>a \<in> A\<close> \<open>a \<in> S\<close> \<open>b \<in> B\<close> \<open>b \<in> S\<close> \<open>a \<noteq> b\<close> by blast
    have \<open>DF A \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> DF B \<sqsubseteq>\<^sub>F\<^sub>D (a \<rightarrow> DF A) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (b \<rightarrow> DF B)\<close>
      by (intro mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD; subst DF_unfold, meson Mndetprefix_FD_write0 \<open>a \<in> A\<close> \<open>b \<in> B\<close>)
    also have \<open>\<dots> = STOP\<close> by (simp add: \<open>a \<in> S\<close> \<open>a \<noteq> b\<close> \<open>b \<in> S\<close> write0_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0_subset)
    finally have False
      by (metis DF_Univ_freeness Un_empty \<open>A \<noteq> {}\<close>
          trans_FD[OF \<open>?FD_ref\<close>] non_deadlock_free_STOP)
  } note * = this
  show ?thesis
  proof (cases \<open>A = {}\<close>; cases \<open>B = {}\<close>)
    show \<open>A = {} \<Longrightarrow> B = {} \<Longrightarrow> ?thesis\<close> by simp
  next
    show \<open>A = {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> ?thesis\<close>
      by simp (metis DF_FD_STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_imp_disjoint
          disjoint_imp_DF_eq_STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF order_refl)
  next
    show \<open>A \<noteq> {} \<Longrightarrow> B = {} \<Longrightarrow> ?thesis\<close>
      by simp (metis DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP_imp_disjoint
          disjoint_imp_DF_eq_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP order_refl)
  next
    show \<open>A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> ?thesis\<close>
      by simp (metis "*" DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF)
  qed
qed



lemma DF_FD_DF_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF :
  \<open>\<lbrakk>\<And>l. l \<in> set L \<Longrightarrow> X l \<noteq> {}; \<exists>s. (\<Union> l \<in> set L. X l) \<inter> S \<subseteq> {s}\<rbrakk>
   \<Longrightarrow> DF (\<Union> l \<in> set L. X l) \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. (DF (X l) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
proof (induct L rule: induct_list012)
  case 1 show ?case by simp
next
  case (2 l0) show ?case by (simp add: Renaming_DF)
next
  case (3 l0 l1 L)
  have \<open>(DF (\<Union> l \<in> set (l0 # l1 # L). X l) :: ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) =
        DF (X l0 \<union> (\<Union> l \<in> set (l1 # L). X l))\<close> by simp
  also have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D DF (X l0) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t DF (\<Union> l \<in> set (l1 # L). X l)\<close>
    by (rule Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_iff[THEN iffD2])
      (use "3.prems"(2) in \<open>simp add: "3.prems"(1) subset_singleton_iff
                                      Int_Un_distrib2 Un_singleton_iff, safe, simp_all\<close>)
  also have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D DF (X l0) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l\<in>@(l1 # L). (DF (X l))\<close>
    by (intro Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD[OF idem_FD] "3.hyps"(2))
      (use "3.prems" in auto)
  also have \<open>\<dots> = \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l\<in>@(l0 # l1 # L). DF (X l)\<close> by simp
  finally show ?case .
qed





lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) \<open>DF {a} = DF {a} \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP \<longleftrightarrow> a \<notin> S\<close>
  by (metis DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP_imp_disjoint boolean_algebra.conj_zero_left
      disjoint_imp_DF_eq_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP insert_disjoint(1) order_refl)

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) \<open>DF {a} \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP = STOP \<longleftrightarrow> a \<in> S\<close>
  by (metis DF_unfold Diff_eq_empty_iff Diff_triv Int_empty_left Int_insert_left
      Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_right Mndetprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP
      Mndetprefix_is_STOP_iff Mprefix_empty empty_not_insert insert_Diff1)


corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) DF_FD_DF_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF : \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A |||\<^sub>\<checkmark> DF A\<close>
  by (metis DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_iff inf_bot_right sup.idem)

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) DF_UNIV_FD_DF_UNIV_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF_UNIV:
  \<open>DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D DF UNIV |||\<^sub>\<checkmark> DF UNIV\<close>
  by (fact DF_FD_DF_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF)

corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_deadlock_free :
  \<open>deadlock_free P \<Longrightarrow> deadlock_free Q \<Longrightarrow> deadlock_free (P |||\<^sub>\<checkmark> Q)\<close>
  using DF_FD_DF_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF deadlock_free_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_DF_FD_DF_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF by blast


theorem MultiInter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_deadlock_free :
  \<open>\<lbrakk>L \<noteq> []; \<And>l. l \<in> set L \<Longrightarrow> deadlock_free (P l)\<rbrakk> \<Longrightarrow>
   deadlock_free (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ L. P l)\<close>
proof (induct L rule: induct_list012)
  case 1
  from "1.prems"(1) have False by simp
  thus ?case ..
next
  case (2 l0)
  from "2.prems"(2) show ?case
    by (simp add: deadlock_free_imp_deadlock_free_Renaming)
next
  case (3 l0 l1 L)
  have \<open>\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l0 # l1 # L). P l = P l0 |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l\<close> by simp
  moreover have \<open>deadlock_free (P l0)\<close> by (simp add: "3.prems"(2))
  moreover have \<open>deadlock_free (\<^bold>|\<^bold>|\<^bold>|\<^sub>\<checkmark> l \<in>@ (l1 # L). P l)\<close>
    by (rule "3.hyps"(2)) (simp_all add: "3.prems"(2))
  ultimately show ?case
    by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_deadlock_free)
qed



(*<*)
end
  (*>*)