(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Sliding choice
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


section \<open> Sliding Choice \<close>

(*<*)
theory  Sliding_Choice
  imports Deterministic_Choice Non_Deterministic_Choice
begin
  (*>*)

subsection \<open>Definition\<close>

definition Sliding :: \<open>('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>\<rhd>\<close> 80)
  where \<open>P \<rhd> Q \<equiv> (P \<box> Q) \<sqinter> Q\<close>



subsection \<open>Projections\<close>

lemma F_Sliding:
  \<open>\<F> (P \<rhd> Q) = \<F> Q \<union> {(s, X). s \<noteq> [] \<and> (s, X) \<in> \<F> P \<or> 
                               s = [] \<and> (\<exists>r. s \<in> \<D> P \<or> tick r \<notin> X \<and> [tick r] \<in> \<T> P)}\<close>
  by (auto simp add: Sliding_def F_Ndet F_Det intro: is_processT8 is_processT6_TR_notin)

lemma D_Sliding: \<open>\<D> (P \<rhd> Q) = \<D> P \<union> \<D> Q\<close>
  by (simp add: Sliding_def D_Ndet D_Det)

lemma T_Sliding: \<open>\<T> (P \<rhd> Q) = \<T> P \<union> \<T> Q\<close>
  by (simp add: Sliding_def T_Ndet T_Det)

lemmas Sliding_projs = F_Sliding D_Sliding T_Sliding



subsection \<open>Properties\<close>

lemma Sliding_id: \<open>P \<rhd> P = P\<close>
  by (simp add: Sliding_def)

(* 
text \<open>Of course, \<^term>\<open>P \<rhd> STOP \<noteq> STOP\<close> and \<^term>\<open>P \<rhd> STOP \<noteq> P\<close> in general.\<close>
lemma \<open>\<exists>P. P \<rhd> STOP \<noteq> STOP \<and> P \<rhd> STOP \<noteq> P\<close>
proof (intro exI)
  show \<open>SKIP undefined \<rhd> STOP \<noteq> STOP \<and> SKIP undefined \<rhd> STOP \<noteq> SKIP undefined\<close>
    by (metis Det_STOP Ndet_commute SKIP_F_iff SKIP_Neq_STOP
            STOP_F_iff Sliding_def mono_Ndet_F_left)
qed
   *)




subsection \<open>Continuity\<close>

text \<open>From the definition, monotony and continuity is obvious.\<close>

lemma mono_Sliding : \<open>P \<sqsubseteq> P' \<Longrightarrow> Q \<sqsubseteq> Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq> P' \<rhd> Q'\<close>
  unfolding Sliding_def by (simp add: mono_Det mono_Ndet)

lemma Sliding_cont[simp] : \<open>cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. f x \<rhd> g x)\<close>
  by (simp add: Sliding_def)

(*<*)
end
  (*>*)
