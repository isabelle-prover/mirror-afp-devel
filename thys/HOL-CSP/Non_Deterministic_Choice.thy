(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Non deterministic choice
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

section\<open> Non Deterministic Choice \<close>

(*<*)
theory  Non_Deterministic_Choice 
  imports Process
begin
  (*>*)

subsection\<open>The Ndet Operator Definition\<close>

lift_definition Ndet :: \<open>[('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>|-|\<close> 83)
  is \<open>\<lambda>P Q. (\<F> P \<union> \<F> Q , \<D> P \<union> \<D> Q)\<close>
proof -
  show \<open>is_process (\<F> P \<union> \<F> Q , \<D> P \<union> \<D> Q)\<close> for P Q :: \<open>('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (unfold is_process_def DIVERGENCES_def FAILURES_def fst_conv snd_conv, intro conjI allI impI)
    show \<open>([], {}) \<in> \<F> P \<union> \<F> Q\<close>
      by (simp add: is_processT1)
  next
    show \<open>(s, X) \<in> \<F> P \<union> \<F> Q \<Longrightarrow> front_tickFree s\<close> for s X
      by (auto intro: is_processT2)
  next
    show \<open>(s @ t, {}) \<in> \<F> P \<union> \<F> Q \<Longrightarrow> (s, {}) \<in> \<F> P \<union> \<F> Q\<close> for s t
      by (auto intro: is_processT3)
  next
    show \<open>(s, Y) \<in> \<F> P \<union> \<F> Q \<and> X \<subseteq> Y  \<Longrightarrow>  (s, X) \<in> \<F> P \<union> \<F> Q\<close> for s X Y
      by (auto intro: is_processT4)
  next
    show \<open>(s, X) \<in> \<F> P \<union> \<F> Q \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> \<F> P \<union> \<F> Q)
          \<Longrightarrow> (s, X \<union> Y) \<in> \<F> P \<union> \<F> Q\<close> for s X Y by (auto intro: is_processT5)
  next
    show \<open>(s @ [\<checkmark>(r)], {}) \<in> \<F> P \<union> \<F> Q \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> \<F> P \<union> \<F> Q\<close> for s r X
      by (auto intro: is_processT6)
  next
    show \<open>s \<in> \<D> P \<union> \<D> Q \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> \<D> P \<union> \<D> Q\<close> for s t
      by (auto intro: is_processT7)
  next
    show \<open>s \<in> \<D> P \<union> \<D> Q \<Longrightarrow> (s, X) \<in> \<F> P \<union> \<F> Q\<close> for s X
      by (auto intro: is_processT8) 
  next
    show \<open>s @ [\<checkmark>(r)] \<in> \<D> P \<union> \<D> Q \<Longrightarrow> s \<in> \<D> P \<union> \<D> Q\<close> for s r
      by (auto intro: is_processT9)
  qed
qed


notation Ndet (infixl \<open>\<sqinter>\<close> 83)


subsection \<open>The Projections\<close>

lemma F_Ndet : \<open>\<F> (P \<sqinter> Q) = \<F> P \<union> \<F> Q\<close>
  by (simp add: FAILURES_def Failures.rep_eq Ndet.rep_eq)

lemma D_Ndet : \<open>\<D> (P \<sqinter> Q) = \<D> P \<union> \<D> Q\<close>
  by (simp add: DIVERGENCES_def Divergences.rep_eq Ndet.rep_eq)

lemma T_Ndet : \<open>\<T> (P \<sqinter> Q) = \<T> P \<union> \<T> Q\<close>
  by (subst Traces.rep_eq)
    (use T_F_spec in \<open>auto simp: TRACES_def Failures.rep_eq[symmetric] F_Ndet F_T\<close>)

lemmas Ndet_projs = F_Ndet D_Ndet T_Ndet



subsection\<open>Basic Laws\<close>

text \<open>The commutativity of the operator helps to simplify the subsequent
      continuity proof and is therefore developed here: \<close>

lemma Ndet_commute: \<open>P \<sqinter> Q = Q \<sqinter> P\<close>
  by (auto simp: Process_eq_spec F_Ndet D_Ndet)

lemma Ndet_id [simp] : \<open>P \<sqinter> P = P\<close> by (simp add: Process_eq_spec F_Ndet D_Ndet)


subsection\<open>The Continuity Rule\<close>

lemma mono_Ndet : \<open>P \<sqinter> Q \<sqsubseteq> P' \<sqinter> Q'\<close> if \<open>P \<sqsubseteq> P'\<close> and \<open>Q \<sqsubseteq> Q'\<close>
proof (unfold le_approx_def, intro conjI allI impI)
  show \<open>\<D> (P' \<sqinter> Q') \<subseteq> \<D> (P \<sqinter> Q)\<close> by (metis D_Ndet Un_mono le_approx1 that)
next
  show \<open>s \<notin> \<D> (P \<sqinter> Q) \<Longrightarrow> \<R>\<^sub>a (P \<sqinter> Q) s = \<R>\<^sub>a (P' \<sqinter> Q') s\<close> for s
    using that[THEN le_approx2] by (simp add: D_Ndet Refusals_after_def F_Ndet)
next
  show \<open>min_elems (\<D> (P \<sqinter> Q)) \<subseteq> \<T> (P' \<sqinter> Q')\<close>
    using that[THEN le_approx3] by (auto simp add: min_elems_def D_Ndet T_Ndet)
qed


lemma cont_Ndet_prem : \<open>(\<Squnion> i. Y i) \<sqinter> S = (\<Squnion> i. Y i \<sqinter> S)\<close> if \<open>chain Y\<close>
proof -
  have \<open>chain (\<lambda>i. Y i \<sqinter> S)\<close>
    by (rule chainI) (simp add: \<open>chain Y\<close> chainE mono_Ndet)
  with \<open>chain Y\<close> show ?thesis
    by (simp add: limproc_is_thelub Process_eq_spec D_Ndet F_Ndet F_LUB D_LUB)
qed


lemma Ndet_cont[simp]: \<open>cont (\<lambda>x. f x \<sqinter> g x)\<close> if \<open>cont f\<close> and \<open>cont g\<close>
proof (rule cont_apply[where f = \<open>\<lambda>x g. f x \<sqinter> g\<close>])
  show \<open>cont g\<close> by (fact \<open>cont g\<close>)
next
  show \<open>cont ((\<sqinter>) (f x))\<close> for x
    by (rule contI2, simp add: monofun_def mono_Ndet)
      (subst (1 2) Ndet_commute, simp add: cont_Ndet_prem)
next
  show \<open>cont (\<lambda>x. f x \<sqinter> y)\<close> for y
    by (rule contI2, simp add: monofun_def mono_Ndet cont2monofunE \<open>cont f\<close>)
      (simp add: ch2ch_cont cont2contlubE cont_Ndet_prem \<open>cont f\<close>)
qed


(*<*)
end
  (*>*)