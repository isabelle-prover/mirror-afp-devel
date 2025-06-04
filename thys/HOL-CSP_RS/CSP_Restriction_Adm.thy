(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
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

section \<open>Admissibility\<close>

(*<*)
theory CSP_Restriction_Adm
  imports Process_Restriction_Space After_Operator_Non_Too_Destructive
    "HOL-CSP_OpSem.Operational_Semantics_Laws"
begin 
  (*>*)


named_theorems restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset

subsection \<open>Belonging\<close>

lemma restriction_adm_in_D [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. t \<in> \<D> (f x))\<close>
  and restriction_adm_notin_D [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. t \<notin> \<D> (f x))\<close>
  and restriction_adm_in_F [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. (t, X) \<in> \<F> (f x))\<close>
  and restriction_adm_notin_F [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. (t, X) \<notin> \<F> (f x))\<close> if \<open>cont\<^sub>\<down> f\<close>
for f :: \<open>'b :: restriction \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (all \<open>rule restriction_adm_subst[OF \<open>cont\<^sub>\<down> f\<close>]\<close>)
  have * : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<exists>n0. \<forall>n \<ge> n0. \<sigma> n \<down> Suc (length t) = \<Sigma> \<down> Suc (length t)\<close>
    for \<sigma> and \<Sigma> :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (metis restriction_tendstoD)

  show \<open>adm\<^sub>\<down> (\<lambda>x. t \<in> \<D> x)\<close> \<open>adm\<^sub>\<down> (\<lambda>x. t \<notin> \<D> x)\<close>
    by (rule restriction_admI,
        metis (no_types) "*" D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_D dual_order.refl)+

  show \<open>adm\<^sub>\<down> (\<lambda>x. (t, X) \<in> \<F> x)\<close> \<open>adm\<^sub>\<down> (\<lambda>x. (t, X) \<notin> \<F> x)\<close>
    by (rule restriction_admI,
        metis (no_types) "*" F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_F dual_order.refl)+
qed


corollary restriction_adm_in_T [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. t \<in> \<T> (f x))\<close>
  and restriction_adm_notin_T [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. t \<notin> \<T> (f x))\<close>
  by (fact restriction_adm_in_F[of f t \<open>{}\<close>, simplified T_F_spec])
    (fact restriction_adm_notin_F[of f t \<open>{}\<close>, simplified T_F_spec])


corollary restriction_adm_in_initials [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. e \<in> (f x)\<^sup>0)\<close>
  and restriction_adm_notin_initials [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. e \<notin> (f x)\<^sup>0)\<close>
  by (simp_all add: initials_def restriction_adm_in_T restriction_adm_notin_T)



subsection \<open>Refining\<close>

corollary restriction_adm_leF [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> g \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. f x \<sqsubseteq>\<^sub>F g x)\<close>
  by (simp add: failure_refine_def subset_iff restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset)

corollary restriction_adm_leD [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> g \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. f x \<sqsubseteq>\<^sub>D g x)\<close> 
  by (simp add: divergence_refine_def subset_iff restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset)

corollary restriction_adm_leT [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> g \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. f x \<sqsubseteq>\<^sub>T g x)\<close>
  by (simp add: trace_refine_def subset_iff restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset)

corollary restriction_adm_leFD [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> g \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. f x \<sqsubseteq>\<^sub>F\<^sub>D g x)\<close>
  by (simp add: failure_divergence_refine_def restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset)

corollary restriction_adm_leDT [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> g \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. f x \<sqsubseteq>\<^sub>D\<^sub>T g x)\<close> 
  by (simp add: trace_divergence_refine_def restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset)




subsubsection \<open>Transitions\<close>

lemma (in After) restriction_cont_After [restriction_adm_simpset] :
  \<open>cont\<^sub>\<down> (\<lambda>x. f x after a)\<close> if \<open>cont\<^sub>\<down> f\<close> and \<open>cont\<^sub>\<down> \<Psi>\<close>
  \<comment> \<open>We could imagine more precise assumptions, but is it useful?\<close>
proof (rule restriction_cont_comp[OF _ \<open>cont\<^sub>\<down> f\<close>])
  show \<open>cont\<^sub>\<down> (\<lambda>P. P after a)\<close>
  proof (rule restriction_contI)
    show \<open>(\<lambda>n. \<sigma> n after a) \<midarrow>\<down>\<rightarrow> \<Sigma> after a\<close> if \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> for \<sigma> \<Sigma>
    proof (rule restriction_tendstoI)
      fix n
      from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> obtain n0
        where * : \<open>\<forall>k\<ge>n0. \<Sigma> \<down> Suc n = \<sigma> k \<down> Suc n\<close>
        by (blast dest: restriction_tendstoD)
      consider \<open>ev a \<in> \<Sigma>\<^sup>0\<close> \<open>\<forall>n\<ge>Suc n0. ev a \<in> (\<sigma> n)\<^sup>0\<close>
        | \<open>ev a \<notin> \<Sigma>\<^sup>0\<close> \<open>\<forall>n\<ge>Suc n0. ev a \<notin> (\<sigma> n)\<^sup>0\<close>
        by (metis "*" Suc_leD initials_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k nat.distinct(1))
      thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> after a \<down> n = \<sigma> k after a \<down> n\<close>
      proof cases
        assume \<open>ev a \<in> \<Sigma>\<^sup>0\<close> \<open>\<forall>n\<ge>Suc n0. ev a \<in> (\<sigma> n)\<^sup>0\<close>
        hence \<open>\<forall>k\<ge>Suc n0. \<Sigma> after a \<down> n = \<sigma> k after a \<down> n\<close>
          by (metis "*" Suc_leD restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After)
        thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> after a \<down> n = \<sigma> k after a \<down> n\<close> ..
      next
        assume \<open>ev a \<notin> \<Sigma>\<^sup>0\<close> \<open>\<forall>n\<ge>Suc n0. ev a \<notin> (\<sigma> n)\<^sup>0\<close>
        hence \<open>\<Sigma> after a = \<Psi> \<Sigma> a\<close> \<open>\<forall>k\<ge>Suc n0. \<sigma> k after a = \<Psi> (\<sigma> k) a\<close>
          by (simp_all add: not_initial_After)
        moreover from \<open>cont\<^sub>\<down> \<Psi>\<close>[THEN restriction_contD]
        obtain n1 where \<open>\<forall>k\<ge>n1. \<Psi> \<Sigma> \<down> n = \<Psi> (\<sigma> k) \<down> n\<close>
          by (blast intro: \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> dest: restriction_tendstoD)
        ultimately have \<open>\<forall>k\<ge>max n1 (Suc n0). \<Sigma> after a \<down> n = \<sigma> k after a \<down> n\<close>
          by simp (metis restriction_fun_def)
        thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> after a \<down> n = \<sigma> k after a \<down> n\<close> ..
      qed
    qed
  qed
qed

lemma (in AfterExt) restriction_cont_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_adm_simpset] :
  \<open>cont\<^sub>\<down> (\<lambda>x. f x after\<^sub>\<checkmark> e)\<close> if \<open>cont\<^sub>\<down> f\<close> and \<open>cont\<^sub>\<down> \<Psi>\<close> and \<open>cont\<^sub>\<down> \<Omega>\<close>
  \<comment> \<open>We could imagine more precise assumptions, but is it useful?\<close>
proof (cases e)
  show \<open>e = ev a \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. f x after\<^sub>\<checkmark> e)\<close> for a
    by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def restriction_cont_After \<open>cont\<^sub>\<down> f\<close> \<open>cont\<^sub>\<down> \<Psi>\<close>)
next
  fix r assume \<open>e = \<checkmark>(r)\<close>
  hence \<open>(\<lambda>x. f x after\<^sub>\<checkmark> e) = (\<lambda>x. \<Omega> (f x) r)\<close> by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
  thus \<open>cont\<^sub>\<down> (\<lambda>x. f x after\<^sub>\<checkmark> e)\<close>
    by (metis restriction_cont_comp restriction_cont_fun_imp that(1,3))
qed

lemma (in AfterExt) restriction_cont_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e [restriction_adm_simpset] :
  \<open>cont\<^sub>\<down> (\<lambda>x. f x after\<^sub>\<T> t)\<close> if \<open>cont\<^sub>\<down> f\<close> and \<open>cont\<^sub>\<down> \<Psi>\<close> and \<open>cont\<^sub>\<down> \<Omega>\<close>
  \<comment> \<open>We could imagine more precise assumptions, but is it useful?\<close>
proof (rule restriction_cont_comp[OF _ \<open>cont\<^sub>\<down> f\<close>])
  show \<open>cont\<^sub>\<down> (\<lambda>P. P after\<^sub>\<T> t)\<close>
  proof (induct t)
    show \<open>cont\<^sub>\<down> (\<lambda>P. P after\<^sub>\<T> [])\<close> by simp
  next
    fix e t assume \<open>cont\<^sub>\<down> (\<lambda>P. P after\<^sub>\<T> t)\<close>
    show \<open>cont\<^sub>\<down> (\<lambda>P. P after\<^sub>\<T> (e # t))\<close>
      by (simp, rule restriction_cont_comp[OF \<open>cont\<^sub>\<down> (\<lambda>P. P after\<^sub>\<T> t)\<close>])
        (simp add: restriction_cont_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>cont\<^sub>\<down> \<Psi>\<close> \<open>cont\<^sub>\<down> \<Omega>\<close>)
  qed
qed


lemma (in OpSemTransitions) restriction_adm_weak_ev_trans [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset]:
  \<comment> \<open>Could be weakened to a continuity assumption on \<^term>\<open>\<Psi>\<close>.\<close>
  fixes f g :: \<open>'b :: restriction \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes \<tau>_trans_restriction_adm:
    \<open>\<And>f g :: 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> g \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. f x \<leadsto>\<^sub>\<tau> g x)\<close>
    and \<open>cont\<^sub>\<down> f\<close> and \<open>cont\<^sub>\<down> g\<close> and \<open>cont\<^sub>\<down> \<Psi>\<close> and \<open>cont\<^sub>\<down> \<Omega>\<close>
  shows \<open>adm\<^sub>\<down> (\<lambda>x. f x \<leadsto>\<^bsub>e\<^esub> g x)\<close>
proof (intro restriction_adm_conj)
  show \<open>adm\<^sub>\<down> (\<lambda>x. ev e \<in> (f x)\<^sup>0)\<close>
    by (simp add: \<open>cont\<^sub>\<down> f\<close> restriction_adm_in_initials)
next
  show \<open>adm\<^sub>\<down> (\<lambda>x. f x after\<^sub>\<checkmark> ev e \<leadsto>\<^sub>\<tau> g x)\<close>
  proof (rule \<tau>_trans_restriction_adm[OF _ \<open>cont\<^sub>\<down> g\<close>],
      rule restriction_cont_comp[OF _ \<open>cont\<^sub>\<down> f\<close>])
    show \<open>cont\<^sub>\<down> (\<lambda>x. x after\<^sub>\<checkmark> ev e)\<close>
      by (simp add: \<open>cont\<^sub>\<down> \<Psi>\<close> \<open>cont\<^sub>\<down> \<Omega>\<close> restriction_cont_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  qed
qed

lemma (in OpSemTransitions) restriction_adm_weak_tick_trans [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset]:
  fixes f g :: \<open>'b :: restriction \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes \<tau>_trans_restriction_adm:
    \<open>\<And>f g :: 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> g \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. f x \<leadsto>\<^sub>\<tau> g x)\<close>
    and \<open>cont\<^sub>\<down> f\<close> and \<open>cont\<^sub>\<down> g\<close> and \<open>cont\<^sub>\<down> \<Psi>\<close> and \<open>cont\<^sub>\<down> \<Omega>\<close>
  shows \<open>adm\<^sub>\<down> (\<lambda>x. f x \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> (g x))\<close>
proof (intro restriction_adm_conj)
  show \<open>adm\<^sub>\<down> (\<lambda>x. \<checkmark>(r) \<in> (f x)\<^sup>0)\<close>
    by (simp add: \<open>cont\<^sub>\<down> f\<close> restriction_adm_in_initials)
next
  show \<open>adm\<^sub>\<down> (\<lambda>x. f x after\<^sub>\<checkmark> \<checkmark>(r) \<leadsto>\<^sub>\<tau> g x)\<close>
  proof (rule \<tau>_trans_restriction_adm[OF _ \<open>cont\<^sub>\<down> g\<close>],
      rule restriction_cont_comp[OF _ \<open>cont\<^sub>\<down> f\<close>])
    show \<open>cont\<^sub>\<down> (\<lambda>x. x after\<^sub>\<checkmark> \<checkmark>(r))\<close>
      by (simp add: \<open>cont\<^sub>\<down> \<Psi>\<close> \<open>cont\<^sub>\<down> \<Omega>\<close> restriction_cont_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  qed
qed

lemma (in OpSemTransitions) restriction_adm_weak_trace_trans [restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset]:
  fixes f g :: \<open>'b :: restriction \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes \<tau>_trans_restriction_adm:
    \<open>\<And>f g :: 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> g \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. f x \<leadsto>\<^sub>\<tau> g x)\<close>
    and \<open>cont\<^sub>\<down> f\<close> and \<open>cont\<^sub>\<down> g\<close> and \<open>cont\<^sub>\<down> \<Psi>\<close> and \<open>cont\<^sub>\<down> \<Omega>\<close>
  shows \<open>adm\<^sub>\<down> (\<lambda>x. f x \<leadsto>\<^sup>* t (g x))\<close>
proof (subst trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans, intro restriction_adm_conj)
  show \<open>adm\<^sub>\<down> (\<lambda>x. t \<in> \<T> (f x))\<close> by (simp add: \<open>cont\<^sub>\<down> f\<close> restriction_adm_in_T)
next
  show \<open>adm\<^sub>\<down> (\<lambda>x. f x after\<^sub>\<T> t \<leadsto>\<^sub>\<tau> g x)\<close>
  proof (rule \<tau>_trans_restriction_adm[OF _ \<open>cont\<^sub>\<down> g\<close>])
    show \<open>cont\<^sub>\<down> (\<lambda>x. f x after\<^sub>\<T> t)\<close>
      by (simp add: \<open>cont\<^sub>\<down> f\<close> \<open>cont\<^sub>\<down> \<Psi>\<close> \<open>cont\<^sub>\<down> \<Omega>\<close> restriction_cont_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e)
  qed
qed



declare restriction_adm_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset [simp]


(*<*)
end
  (*>*)