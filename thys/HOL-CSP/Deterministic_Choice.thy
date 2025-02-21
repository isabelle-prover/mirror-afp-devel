(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Deterministic choice
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

chapter \<open>The Binary Choice Operators\<close>

section\<open> Deterministic Choice \<close>

(*<*)
theory  Deterministic_Choice 
  imports Process
begin
  (*>*)

subsection\<open>The Det Operator Definition\<close>

lift_definition Det :: \<open>[('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>[+]\<close> 82)
  is \<open>\<lambda>P Q. ({(s, X). s = [] \<and> (s, X) \<in> \<F> P \<inter> \<F> Q} \<union>
             {(s, X). s \<noteq> [] \<and> (s, X) \<in> \<F> P \<union> \<F> Q} \<union>
             {(s, X). s = [] \<and> s \<in> \<D> P \<union> \<D> Q} \<union>
             {(s, X). \<exists>r. s = [] \<and> \<checkmark>(r) \<notin> X \<and> [\<checkmark>(r)] \<in> \<T> P \<union> \<T> Q},
             \<D> P \<union> \<D> Q)\<close>
proof -
  show \<open>?thesis P Q\<close> (is \<open>is_process (?f, \<D> P \<union> \<D> Q)\<close>) for P Q :: \<open>('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (unfold is_process_def DIVERGENCES_def FAILURES_def fst_conv snd_conv, intro conjI allI impI)
    show \<open>([], {}) \<in> ?f\<close>
      by (simp add: is_processT1)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
      by (auto simp: is_processT2)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
      by (auto simp: is_processT1 dest!: is_processT3[rule_format])
  next
    show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y  \<Longrightarrow>  (s, X) \<in> ?f\<close> for s X Y
      by (cases s; use is_processT4 in blast)
  next
    show \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for s X Y
      by (cases s) (auto simp: is_processT5 T_F)
  next
    show \<open>(s @ [\<checkmark>(r)], {}) \<in> ?f \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> ?f\<close> for s r X
      apply (cases s; simp add: T_F_spec)
      by blast (metis T_F_spec append_Cons is_processT6)
  next
    show \<open>s \<in> \<D> P \<union> \<D> Q \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> \<D> P \<union> \<D> Q\<close> for s t
      by (auto simp: is_processT7)
  next
    show \<open>s \<in> \<D> P \<union> \<D> Q \<Longrightarrow> (s, X) \<in> ?f\<close> for s X
      by (auto simp: is_processT8) 
  next
    show \<open>s @ [\<checkmark>(r)] \<in> \<D> P \<union> \<D> Q \<Longrightarrow> s \<in> \<D> P \<union> \<D> Q\<close> for s r
      by (meson UnCI UnE is_processT9)
  qed
qed

notation Det (infixl \<open>\<box>\<close> 82)


subsection\<open>The Projections\<close>

lemma F_Det :
  \<open>\<F> (P \<box> Q) = {(s, X). s = [] \<and> (s, X) \<in> \<F> P \<inter> \<F> Q} \<union>
                {(s, X). s \<noteq> [] \<and> (s, X) \<in> \<F> P \<union> \<F> Q} \<union>
                {(s, X). s = [] \<and> s \<in> \<D> P \<union> \<D> Q} \<union>
                {(s, X). \<exists>r. s = [] \<and> \<checkmark>(r) \<notin> X \<and> [\<checkmark>(r)] \<in> \<T> P \<union> \<T> Q}\<close>
  by (subst Failures.rep_eq, simp add: Det.rep_eq FAILURES_def)

lemma D_Det : \<open>\<D> (P \<box> Q) = \<D> P \<union> \<D> Q\<close>
  by (subst Divergences.rep_eq, simp add: Det.rep_eq DIVERGENCES_def)

lemma T_Det : \<open>\<T> (P \<box> Q) = \<T> P \<union> \<T> Q\<close>
  by (unfold Traces.rep_eq TRACES_def F_Det Failures.rep_eq[symmetric])
    (simp add: T_F F_T set_eq_iff, metis F_T T_F is_processT1)

lemmas Det_projs = F_Det D_Det T_Det



subsection\<open>Basic Laws\<close>

text\<open>The following theorem of Commutativity helps to simplify the subsequent
continuity proof by symmetry breaking. It is therefore already developed here:\<close>

lemma Det_commute : \<open>P \<box> Q = Q \<box> P\<close>
  by(auto simp: Process_eq_spec F_Det D_Det)

lemma Det_id [simp] : \<open>P \<box> P = P\<close>
  by (auto simp add: Process_eq_spec F_Det D_Det
      intro: is_processT8 is_processT6_TR_notin)



subsection\<open>The Continuity-Rule\<close>

lemma mono_Det : \<open>(P :: ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<sqsubseteq> P' \<Longrightarrow> Q \<sqsubseteq> Q' \<Longrightarrow> P \<box> Q \<sqsubseteq> P' \<box> Q'\<close>
proof -
  have \<open>(P :: ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<box> S \<sqsubseteq> Q \<box> S\<close> if \<open>P \<sqsubseteq> Q\<close> for P S Q
  proof (unfold le_approx_def, intro conjI impI allI subsetI)
    show \<open>s \<in> \<D> (Q \<box> S) \<Longrightarrow> s \<in> \<D> (P \<box> S)\<close> for s
      apply (simp add: D_Det)
      using le_approx_imp_le_ref le_ref1 that by blast
  next
    show \<open>s \<notin> \<D> (P \<box> S) \<Longrightarrow> \<R>\<^sub>a (P \<box> S) s = \<R>\<^sub>a (Q \<box> S) s\<close> for s
      apply (cases s; simp add: D_Det Refusals_after_def F_Det set_eq_iff)
       apply (meson front_tickFree_Nil in_mono is_processT9_tick le_approx1 le_approx2T proc_ord2a that)
      using le_approx2 that by auto[1]
  next
    show \<open>s \<in> min_elems (\<D> (P \<box> S)) \<Longrightarrow> s \<in> \<T> (Q \<box> S)\<close> for s
      by (simp add: min_elems_def D_Det T_Det)
        (metis D_T UnCI elem_min_elems in_mono le_approx3 min_elems5 order_neq_le_trans that)
  qed

  thus \<open>P \<sqsubseteq> P' \<Longrightarrow> Q \<sqsubseteq> Q' \<Longrightarrow> P \<box> Q \<sqsubseteq> P' \<box> Q'\<close>
    by (metis Det_commute below_trans)
qed


lemma chain_Det : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<box> S)\<close>
  by (simp add: po_class.chain_def mono_Det)

lemma cont_Det_prem : \<open>((\<Squnion> i. Y i) \<box> S) = (\<Squnion> i. (Y i \<box> S))\<close> if \<open>chain Y\<close>
proof (subst Process_eq_spec, safe)
  show \<open>(s, X) \<in> \<F> (Lub Y \<box> S) \<Longrightarrow> (s, X) \<in> \<F> (\<Squnion>i. Y i \<box> S)\<close> for s X
    by (auto simp add: limproc_is_thelub F_Det D_LUB F_LUB T_LUB chain_Det \<open>chain Y\<close>)
next
  show \<open>(s, X) \<in> \<F> (\<Squnion>i. Y i \<box> S) \<Longrightarrow> (s, X) \<in> \<F> (Lub Y \<box> S)\<close> for s X
    using le_approx2T[OF is_ub_thelub[OF \<open>chain Y\<close>]]
    apply (cases s; simp add: limproc_is_thelub F_Det D_LUB F_LUB T_LUB chain_Det \<open>chain Y\<close>)
    by (metis append_Nil is_processT8 is_processT9)
next
  show \<open>s \<in> \<D> (Lub Y \<box> S) \<Longrightarrow> s \<in> \<D> (\<Squnion>i. Y i \<box> S)\<close>
    and \<open>s \<in> \<D> (\<Squnion>i. Y i \<box> S) \<Longrightarrow> s \<in> \<D> (Lub Y \<box> S)\<close> for s
    by (simp_all add: limproc_is_thelub D_Det D_LUB chain_Det \<open>chain Y\<close>)
qed


lemma Det_cont[simp]: \<open>cont (\<lambda>x. f x \<box> g x)\<close> if \<open>cont f\<close> and \<open>cont g\<close>
proof (rule cont_apply[where f = \<open>\<lambda>x g. f x \<box> g\<close>])
  show \<open>cont g\<close> by (fact \<open>cont g\<close>)
next
  show \<open>cont ((\<box>) (f x))\<close> for x
    by (rule contI2, simp add: monofun_def mono_Det)
      (subst (1 2) Det_commute, simp add: cont_Det_prem)
next
  show \<open>cont (\<lambda>x. f x \<box> y)\<close> for y
    by (rule contI2, simp add: monofun_def mono_Det cont2monofunE \<open>cont f\<close>)
      (simp add: ch2ch_cont cont2contlubE cont_Det_prem \<open>cont f\<close>)
qed


(*<*)
end
  (*>*)