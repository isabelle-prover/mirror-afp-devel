(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff, Safouan Taha.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : A Combined CSP Theory
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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

section\<open> Nondeterministic Choice Operator Definition \<close>

theory  Ndet 
imports Process
begin


subsection\<open>The Ndet Operator Definition\<close>
lift_definition
        Ndet     :: "['\<alpha> process,'\<alpha> process] \<Rightarrow> '\<alpha> process"   (infixl \<open>|-|\<close> 80)
is   "\<lambda>P Q. (\<F> P \<union> \<F> Q , \<D> P \<union> \<D> Q)"
proof(simp only: fst_conv snd_conv Rep_process is_process_def DIVERGENCES_def FAILURES_def,
      intro conjI)
    show "\<And>P Q. ([], {}) \<in> (\<F> P \<union> \<F> Q)"
         by(simp add: is_processT1)
next
    show "\<And>P Q. \<forall>s X. (s, X) \<in> (\<F> P \<union> \<F> Q) \<longrightarrow> front_tickFree s"
         by(auto simp: is_processT2)
next
    show "\<And>P Q. \<forall>s t.   (s @ t, {}) \<in>(\<F> P \<union> \<F> Q) \<longrightarrow> (s, {}) \<in> (\<F> P \<union> \<F> Q)"
         by (auto simp: is_processT1 dest!: is_processT3[rule_format])
next
    show "\<And>P Q. \<forall>s X Y. (s, Y) \<in> (\<F> P \<union> \<F> Q) \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> (\<F> P \<union> \<F> Q)"
         by(auto dest: is_processT4[rule_format,OF conj_commute[THEN iffD1], OF conjI])
next
    show "\<And>P Q. \<forall>sa X Y. (sa, X) \<in> (\<F> P \<union> \<F> Q) \<and> (\<forall>c. c \<in> Y \<longrightarrow> (sa @ [c], {}) \<notin> (\<F> P \<union> \<F> Q))
          \<longrightarrow> (sa, X \<union> Y) \<in> (\<F> P \<union> \<F> Q)"
         by(auto simp: is_processT5 T_F)
next
    show "\<And>P Q. \<forall>s X. (s @ [tick], {}) \<in> (\<F> P \<union> \<F> Q) \<longrightarrow> (s, X - {tick}) \<in> (\<F> P \<union> \<F> Q)"
         apply((rule allI)+, rule impI)
         apply(rename_tac s X, case_tac "s=[]", simp_all add: is_processT6[rule_format] T_F_spec)
         apply(erule disjE,simp_all add: is_processT6[rule_format] T_F_spec)
         apply(erule disjE,simp_all add: is_processT6[rule_format] T_F_spec)
         done
next
    show "\<And>P Q. \<forall>s t. s \<in> \<D> P \<union> \<D> Q \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s @ t \<in> \<D> P \<union> \<D> Q"
         by(auto simp: is_processT7)
next
    show "\<And>P Q. \<forall>s X. s \<in> \<D> P \<union> \<D> Q \<longrightarrow> (s, X) \<in> (\<F> P \<union> \<F> Q)"
         by(auto simp: is_processT8[rule_format])
next
    show "\<And>P Q. \<forall>s. s @ [tick] \<in> \<D> P \<union> \<D> Q \<longrightarrow> s \<in> \<D> P \<union> \<D> Q"
         by(auto intro!:is_processT9[rule_format])
     qed

notation
  Ndet (infixl \<open>\<sqinter>\<close> 80)


subsection \<open>The Projections\<close>

lemma F_Ndet : "\<F> (P \<sqinter> Q) = \<F> P \<union> \<F> Q"
  by (simp add: FAILURES_def Failures.rep_eq Ndet.rep_eq)
 
lemma D_Ndet : "\<D> (P \<sqinter> Q) = \<D> P \<union> \<D> Q"
  by (simp add: DIVERGENCES_def Divergences.rep_eq Ndet.rep_eq)

lemma T_Ndet : "\<T> (P \<sqinter> Q) = \<T> P \<union> \<T> Q"
  apply (subst Traces.rep_eq, simp add: TRACES_def Failures.rep_eq[symmetric] F_Ndet)
  apply(auto simp: T_F F_T is_processT1 Nil_elem_T)
  by(rule_tac x="{}" in exI, simp add: T_F F_T is_processT1 Nil_elem_T)+


subsection\<open>Basic Laws\<close>
text \<open>The commutativity of the operator helps to simplify the subsequent
      continuity proof and is therefore developed here: \<close>

lemma Ndet_commute: "(P \<sqinter> Q) = (Q \<sqinter> P)"
  by(auto simp: Process_eq_spec F_Ndet D_Ndet)


subsection\<open>The Continuity Rule\<close>
lemma  mono_Ndet1: "P \<sqsubseteq> Q \<Longrightarrow> \<D> (Q \<sqinter> S) \<subseteq> \<D> (P \<sqinter> S)"
apply(drule le_approx1)
by (auto simp: Process_eq_spec F_Ndet D_Ndet)

lemma mono_Ndet2: "P \<sqsubseteq> Q \<Longrightarrow> (\<forall> s. s \<notin> \<D> (P \<sqinter> S) \<longrightarrow> Ra (P \<sqinter> S) s = Ra (Q \<sqinter> S) s)"
apply(subst (asm) le_approx_def)
by (auto simp: Process_eq_spec F_Ndet D_Ndet Ra_def)

lemma mono_Ndet3: "P \<sqsubseteq> Q \<Longrightarrow> min_elems (\<D> (P \<sqinter> S)) \<subseteq> \<T> (Q \<sqinter> S)"
apply(auto dest!:le_approx3 simp: min_elems_def subset_iff F_Ndet D_Ndet T_Ndet)
apply(erule_tac x="t" in allE, auto)
by (erule_tac x="[]" in allE, auto simp: less_list_def Nil_elem_T D_T)

lemma mono_Ndet[simp] : "P \<sqsubseteq> Q \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq> (Q \<sqinter> S)"
by(auto simp:le_approx_def mono_Ndet1 mono_Ndet2 mono_Ndet3)

lemma mono_Ndet_sym[simp] : "P \<sqsubseteq> Q \<Longrightarrow> (S \<sqinter> P) \<sqsubseteq> (S \<sqinter> Q)"
by (auto simp: Ndet_commute)


lemma cont_Ndet1: 
assumes chain:"chain Y"
shows  "((\<Squnion> i. Y i) \<sqinter> S) = (\<Squnion> i. (Y i \<sqinter> S))"
proof -
   have A : "chain (\<lambda>i. Y i \<sqinter> S)"
        apply(insert chain,rule chainI)
        apply(frule_tac i="i" in chainE)
        by(simp)
   show ?thesis using chain
        by(auto simp add: limproc_is_thelub Process_eq_spec D_Ndet F_Ndet F_LUB D_LUB A)
qed


lemma Ndet_cont[simp]: 
assumes f: "cont f"
and     g: "cont g"
shows      "cont (\<lambda>x. f x \<sqinter> g x)"
proof -
   have A:"\<And>x. cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>X. (f x)\<sqinter> X)"
          apply(rule contI2, rule monofunI)
          apply(auto)
          apply(subst Ndet_commute, subst cont_Ndet1)
          by   (auto simp:Ndet_commute)
   have B:"\<And>y. cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. f x \<sqinter> y)"
          apply(rule_tac c="(\<lambda> g. g \<sqinter> y)" in cont_compose)
          apply(rule contI2,rule monofunI)
          by   (simp_all add: cont_Ndet1)
   show ?thesis using f g
   by (rule_tac f="(\<lambda> x. (\<lambda> g. f x \<sqinter> g))" in cont_apply, auto simp: A B)
qed


end
