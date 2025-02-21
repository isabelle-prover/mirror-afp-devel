(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : CSP refinements
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


chapter \<open> The CSP Refinements \<close>

section \<open>Definitions and first Properties\<close>

(*<*)
theory CSP_Refinements
  imports Process Constant_Processes
begin
  (*>*)

subsection \<open>Definitions\<close>

definition trace_refine :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>              (infix \<open>\<sqsubseteq>\<^sub>T\<close> 50)
  where \<open>P \<sqsubseteq>\<^sub>T Q \<equiv> \<T> Q \<subseteq> \<T> P\<close>

definition failure_refine :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>            (infix \<open>\<sqsubseteq>\<^sub>F\<close> 50)
  where \<open>P \<sqsubseteq>\<^sub>F Q \<equiv> \<F> Q \<subseteq> \<F> P\<close>

definition divergence_refine :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>         (infix \<open>\<sqsubseteq>\<^sub>D\<close> 50)
  where \<open>P \<sqsubseteq>\<^sub>D Q \<equiv> \<D> Q \<subseteq> \<D> P\<close>

abbreviation failure_divergence_refine :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>F\<^sub>D\<close> 50)
  where \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<equiv> P \<le> Q\<close>


definition trace_divergence_refine :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>   (infix \<open>\<sqsubseteq>\<^sub>D\<^sub>T\<close> 50)
  (* an experimental order considered also in our theories*)
  where \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<equiv> P \<sqsubseteq>\<^sub>T Q \<and> P \<sqsubseteq>\<^sub>D Q\<close>


lemma failure_divergence_refine_def : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>F Q \<and> P \<sqsubseteq>\<^sub>D Q\<close>
  unfolding less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def failure_refine_def divergence_refine_def by argo

lemmas refine_defs = failure_divergence_refine_def trace_divergence_refine_def
  failure_refine_def divergence_refine_def trace_refine_def


lemma failure_divergence_refineI :
  \<open>\<lbrakk>\<And>s. s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> P; \<And>s X. (s, X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> P\<rbrakk> \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (auto simp add: refine_defs)

lemma failure_divergence_refine_optimizedI :
  \<open>\<lbrakk>\<And>s. s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> P; \<And>s X. (s, X) \<in> \<F> Q \<Longrightarrow> \<D> Q \<subseteq> \<D> P \<Longrightarrow> (s, X) \<in> \<F> P\<rbrakk> \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (simp add: failure_divergence_refineI subsetI)

lemma trace_divergence_refineI :
  \<open>\<lbrakk>\<And>s. s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> P; \<And>s. s \<in> \<T> Q \<Longrightarrow> s \<in> \<T> P\<rbrakk> \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (auto simp add: refine_defs)

lemma trace_divergence_refine_optimizedI :
  \<open>\<lbrakk>\<And>s. s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> P; \<And>s. s \<in> \<T> Q \<Longrightarrow> \<D> Q \<subseteq> \<D> P \<Longrightarrow> s \<in> \<T> P\<rbrakk> \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (simp add: trace_divergence_refineI subsetI)



subsection \<open>Idempotency\<close>

(* TODO: rename in ..._refl ? *)

lemma  idem_F[simp] : \<open>P \<sqsubseteq>\<^sub>F P\<close>
  and  idem_D[simp] : \<open>P \<sqsubseteq>\<^sub>D P\<close>
  and  idem_T[simp] : \<open>P \<sqsubseteq>\<^sub>T P\<close>
  and idem_FD[simp] : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  and idem_DT[simp] : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P\<close>
  by (simp_all add: refine_defs) 


subsection \<open>Some obvious refinements\<close>

lemma BOT_leF [simp] : \<open>\<bottom> \<sqsubseteq>\<^sub>F Q\<close>
  and BOT_leD [simp] : \<open>\<bottom> \<sqsubseteq>\<^sub>D Q\<close>
  and BOT_leT [simp] : \<open>\<bottom> \<sqsubseteq>\<^sub>T Q\<close>
  and BOT_leFD[simp] : \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  and BOT_leDT[simp] : \<open>\<bottom> \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (simp_all add: refine_defs le_approx_lemma_F
      le_approx_lemma_T le_approx1)



subsection \<open>Antisymmetry\<close>

lemma FD_antisym: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> P = Q\<close> by simp

lemma DT_antisym: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T P \<Longrightarrow> P = Q\<close>
  apply (simp add: trace_divergence_refine_def)
  oops (* obviously false *)



  subsection \<open>Transitivity\<close>

lemma  trans_F : \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F S \<Longrightarrow> P \<sqsubseteq>\<^sub>F S\<close>
  and  trans_D : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D S \<Longrightarrow> P \<sqsubseteq>\<^sub>D S\<close>
  and  trans_T : \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>T S \<Longrightarrow> P \<sqsubseteq>\<^sub>T S\<close>
  and trans_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D S \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D S\<close>
  and trans_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T S \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T S\<close>
  by (auto simp add: failure_refine_def divergence_refine_def
      trace_refine_def trace_divergence_refine_def)



subsection \<open>Relations between refinements\<close>

lemma      leF_imp_leT : \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close>
  and     leFD_imp_leF : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q\<close>
  and     leFD_imp_leD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q\<close>
  and     leDT_imp_leD : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q\<close>
  and     leDT_imp_leT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close>
  and leF_leD_imp_leFD : \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  and leD_leT_imp_leDT : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (simp_all add: failure_refine_def trace_refine_def divergence_refine_def
      trace_divergence_refine_def less_eq_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    (use T_F_spec in blast)



subsection \<open>More obvious refinements\<close>

lemma  leD_STOP[simp] : \<open>P \<sqsubseteq>\<^sub>D STOP\<close>
  and  leT_STOP[simp] : \<open>P \<sqsubseteq>\<^sub>T STOP\<close>
  and leDT_STOP[simp] : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T STOP\<close>
  by (simp_all add: refine_defs T_STOP D_STOP)



subsection \<open>Admissibility\<close>

lemma le_F_adm [simp] : \<open>adm (\<lambda>x. u x \<sqsubseteq>\<^sub>F v x)\<close> if \<open>cont u\<close> and \<open>monofun v\<close>
proof (unfold adm_def failure_refine_def, safe)
  fix Y s X assume * : \<open>chain Y\<close> \<open>\<forall>i. \<F> (v (Y i)) \<subseteq> \<F> (u (Y i))\<close> \<open>(s, X) \<in> \<F> (v (Lub Y))\<close>
  have \<open>v (Y i) \<sqsubseteq> v (\<Squnion>i. Y i)\<close> for i by (simp add: "*"(1) is_ub_thelub monofunE \<open>monofun v\<close>)
  with "*"(2) le_approx_lemma_F have \<open>\<F> (v (\<Squnion>i. Y i)) \<subseteq> \<F> (u (Y i))\<close> for i by blast
  with "*"(3) show \<open>(s, X) \<in> \<F> (u (Lub Y))\<close>
    by (auto simp add: ch2ch_cont \<open>cont u\<close> \<open>chain Y\<close> F_LUB limproc_is_thelub cont2contlubE)
qed


lemma le_T_adm [simp] : \<open>adm (\<lambda>x. u x \<sqsubseteq>\<^sub>T v x)\<close> if \<open>cont u\<close> and \<open>monofun v\<close>
proof (unfold adm_def trace_refine_def, intro allI impI subsetI)
  fix Y s assume * : \<open>chain Y\<close> \<open>\<forall>i. \<T> (v (Y i)) \<subseteq> \<T> (u (Y i))\<close> \<open>s \<in> \<T> (v (Lub Y))\<close>
  have \<open>v (Y i) \<sqsubseteq> v (\<Squnion>i. Y i)\<close> for i by (simp add: "*"(1) is_ub_thelub monofunE \<open>monofun v\<close>)
  with "*"(2) le_approx_lemma_T have \<open>\<T> (v (\<Squnion>i. Y i)) \<subseteq> \<T> (u (Y i))\<close> for i by blast
  with "*"(3) show \<open>s \<in> \<T> (u (Lub Y))\<close>
    by (auto simp add: ch2ch_cont \<open>cont u\<close> \<open>chain Y\<close> T_LUB limproc_is_thelub cont2contlubE)
qed


lemma le_D_adm [simp] : \<open>adm (\<lambda>x. u x \<sqsubseteq>\<^sub>D v x)\<close> if \<open>cont u\<close> and \<open>monofun v\<close>
proof (unfold adm_def divergence_refine_def, intro allI impI subsetI)
  fix Y s assume * : \<open>chain Y\<close> \<open>\<forall>i. \<D> (v (Y i)) \<subseteq> \<D> (u (Y i))\<close> \<open>s \<in> \<D> (v (Lub Y))\<close>
  have \<open>v (Y i) \<sqsubseteq> v (\<Squnion>i. Y i)\<close> for i by (simp add: "*"(1) is_ub_thelub monofunE \<open>monofun v\<close>)
  with "*"(2) le_approx1 have \<open>\<D> (v (\<Squnion>i. Y i)) \<subseteq> \<D> (u (Y i))\<close> for i by blast
  with "*"(3) show \<open>s \<in> \<D> (u (Lub Y))\<close>
    by (auto simp add: ch2ch_cont \<open>cont u\<close> \<open>chain Y\<close> D_LUB limproc_is_thelub cont2contlubE)
qed

declare le_FD_adm [simp]

thm le_FD_adm le_FD_adm_cont (* already proven *)


lemma le_DT_adm [simp] : \<open>cont (u::('b::cpo) \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>D\<^sub>T v x)\<close>
  using adm_conj[OF le_T_adm[of u v] le_D_adm[of u v]] by (simp add: trace_divergence_refine_def)


lemmas le_F_adm_cont[simp] =  le_F_adm[OF _ cont2mono]
  and  le_T_adm_cont[simp] =  le_T_adm[OF _ cont2mono]
  and  le_D_adm_cont[simp] =  le_D_adm[OF _ cont2mono]
  and le_DT_adm_cont[simp] = le_DT_adm[OF _ cont2mono]

(*<*)
end
  (*>*)