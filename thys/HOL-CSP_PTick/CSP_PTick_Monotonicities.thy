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


chapter \<open>Monotonicity Properties\<close>

(*<*)
theory CSP_PTick_Monotonicities
  imports Sequential_Composition_Generalized_Cont
    Synchronization_Product_Generalized_Cont
begin
  (*>*)


subsection \<open>Sequential Composition\<close>

lemma mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> (\<And>r. Q r \<sqsubseteq>\<^sub>F\<^sub>D Q' r) \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<^bold>;\<^sub>\<checkmark> Q'\<close>
proof (rule trans_FD[of _ \<open>P' \<^bold>;\<^sub>\<checkmark> Q\<close>])
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> (\<And>r. Q r \<sqsubseteq>\<^sub>F\<^sub>D Q' r) \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<^bold>;\<^sub>\<checkmark> Q\<close>
    unfolding refine_defs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
    by (auto simp add: subset_iff T_F_spec[symmetric])
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> (\<And>r. Q r \<sqsubseteq>\<^sub>F\<^sub>D Q' r) \<Longrightarrow> P' \<^bold>;\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<^bold>;\<^sub>\<checkmark> Q'\<close>
    unfolding less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
    by (simp add: subset_iff T_F_spec[symmetric]) metis
qed

lemma mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> (\<And>r. Q r \<sqsubseteq>\<^sub>D\<^sub>T Q' r) \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<^bold>;\<^sub>\<checkmark> Q'\<close>
proof (rule trans_DT[of _ \<open>P' \<^bold>;\<^sub>\<checkmark> Q\<close>])
  show \<open>P \<^bold>;\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<^bold>;\<^sub>\<checkmark> Q\<close> if \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P'\<close>
  proof (rule trace_divergence_refine_optimizedI)
    from \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P'\<close> show \<open>s \<in> \<D> (P' \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> s \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> for s
      by (auto simp add: refine_defs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
  next
    from \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P'\<close> show \<open>s \<in> \<T> (P' \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> s \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> for s
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs refine_defs)
  qed
next
  show \<open>(\<And>r. Q r \<sqsubseteq>\<^sub>D\<^sub>T Q' r) \<Longrightarrow> P' \<^bold>;\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<^bold>;\<^sub>\<checkmark> Q'\<close>
    by (simp add: refine_defs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) blast
qed


lemma mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_F_right : \<open>(\<And>r. Q r \<sqsubseteq>\<^sub>F Q' r) \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>F P \<^bold>;\<^sub>\<checkmark> Q'\<close>
  by (auto simp add: failure_refine_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) blast

lemma mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_D_right : \<open>(\<And>r. Q r \<sqsubseteq>\<^sub>D Q' r) \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>D P \<^bold>;\<^sub>\<checkmark> Q'\<close>
  by (simp add: divergence_refine_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) blast

lemma  mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_right : \<open>(\<And>r. Q r \<sqsubseteq>\<^sub>T Q' r) \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>T P \<^bold>;\<^sub>\<checkmark> Q'\<close>
  by (simp add: trace_refine_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) blast

text \<open>Left Sequence monotonicity doesn't hold for \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>, \<^term>\<open>(\<sqsubseteq>\<^sub>D)\<close> and \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>.\<close>

lemmas monos_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT
  mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_F_right mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_D_right mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_right



subsection \<open>Multiple Sequential Composition\<close>

lemma mono_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>(\<And>x r. x \<in> set L \<Longrightarrow> P x r \<sqsubseteq> Q x r) \<Longrightarrow>
   (SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r \<sqsubseteq> (SEQ\<^sub>\<checkmark> l \<in>@ L. Q l) r\<close>
  by (induct L arbitrary: r, simp_all add: fun_belowI mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemma mono_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD :
  \<open>(\<And>x r. x \<in> set L \<Longrightarrow> P x r \<sqsubseteq>\<^sub>F\<^sub>D Q x r) \<Longrightarrow>
   (SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r \<sqsubseteq>\<^sub>F\<^sub>D (SEQ\<^sub>\<checkmark> l \<in>@ L. Q l) r\<close>
  and mono_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT :
  \<open>(\<And>x r. x \<in> set L \<Longrightarrow> P x r \<sqsubseteq>\<^sub>D\<^sub>T Q x r) \<Longrightarrow>
   (SEQ\<^sub>\<checkmark> l \<in>@ L. P l) r \<sqsubseteq>\<^sub>D\<^sub>T (SEQ\<^sub>\<checkmark> l \<in>@ L. Q l) r\<close>
  by (induct L arbitrary: r, simp_all add: monos_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemmas monos_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k =
  mono_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k mono_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD mono_MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD



subsection \<open>Synchronization Product\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin

lemma mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT :
  \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q'\<close>
  by (simp add: refine_defs T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast

lemma mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD : \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q'\<close>
  if \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P'\<close> and \<open>Q \<sqsubseteq>\<^sub>F\<^sub>D Q'\<close>
proof -
  from \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P'\<close> \<open>Q \<sqsubseteq>\<^sub>F\<^sub>D Q'\<close> have \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P'\<close> \<open>Q \<sqsubseteq>\<^sub>D\<^sub>T Q'\<close>
    by (simp_all add: le_ref2T refine_defs)
  with mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT have \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q'\<close> by blast
  hence * : \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>D P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q'\<close> by (simp add: leDT_imp_leD)
  show \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q'\<close>
  proof (rule leF_leD_imp_leFD[OF _ "*"],
      unfold failure_refine_def, safe)
    fix t X assume \<open>(t, X) \<in> \<F> (P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q')\<close>
    then consider \<open>t \<in> \<D> (P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q')\<close>
      | (fail) t_P t_Q X_P X_Q
      where \<open>(t_P, X_P) \<in> \<F> P'\<close> \<open>(t_Q, X_Q) \<in> \<F> Q'\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), A)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P A X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    thus \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    proof cases
      show \<open>t \<in> \<D> (P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q') \<Longrightarrow> (t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        using "*" D_F unfolding divergence_refine_def by blast
    next
      case fail
      from fail(1, 2) \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P'\<close> \<open>Q \<sqsubseteq>\<^sub>F\<^sub>D Q'\<close>
      have \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        unfolding refine_defs by auto
      with fail(3, 4) show \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    qed
  qed
qed




lemmas monos_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT


end


subsection \<open>Multiple Synchronization Product\<close>

lemma mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> P l \<sqsubseteq> Q l) \<Longrightarrow> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \<sqsubseteq> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. Q l\<close>
  by (induct L rule: induct_list012)
    (simp_all add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k mono_Renaming)

lemma mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD :
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> P l \<sqsubseteq>\<^sub>F\<^sub>D Q l) \<Longrightarrow> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. Q l\<close>
  by (induct L rule: induct_list012)
    (simp_all add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD mono_Renaming_FD)


lemma mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT :
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> P l \<sqsubseteq>\<^sub>D\<^sub>T Q l) \<Longrightarrow> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l \<sqsubseteq>\<^sub>D\<^sub>T \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. Q l\<close>
  by (induct L rule: induct_list012)
    (simp_all add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT mono_Renaming_DT)


lemmas monos_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k =
  mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD mono_MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT




(*<*)
end
  (*>*)