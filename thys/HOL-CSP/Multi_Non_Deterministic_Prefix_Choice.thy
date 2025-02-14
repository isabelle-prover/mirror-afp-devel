(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Multi non deterministic prefix choice
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

section\<open> Multiple non Deterministic Prefix Choice \<close>

(*<*)
theory Multi_Non_Deterministic_Prefix_Choice
  imports Constant_Processes Multi_Deterministic_Prefix_Choice Non_Deterministic_Choice
begin
  (*>*)

section\<open>Multiple non deterministic prefix operator\<close>

lift_definition Mndetprefix :: \<open>['a set, 'a \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda>A P.   if A = {} then process\<^sub>0_of_process STOP
            else (\<Union>a\<in>A. \<F> (a \<rightarrow> P a), \<Union>a\<in>A. \<D> (a \<rightarrow> P a))\<close>
proof (split if_split, intro conjI impI)
  show \<open>is_process (process\<^sub>0_of_process STOP)\<close>
    by (metis STOP.rep_eq STOP.rsp eq_onp_def)
next
  show \<open>is_process (\<Union>a\<in>A. \<F> (a \<rightarrow> P a), \<Union>a\<in>A. \<D> (a \<rightarrow> P a))\<close> (is \<open>is_process (?f, ?d)\<close>)
    if \<open>A \<noteq> {}\<close> for A and P :: \<open>'a \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (unfold is_process_def DIVERGENCES_def FAILURES_def fst_conv snd_conv, intro conjI allI impI)
    show \<open>([], {}) \<in> ?f\<close> by (simp add: ex_in_conv is_processT1 \<open>A \<noteq> {}\<close>)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
      by (blast intro: is_processT2)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
      by (blast intro: is_processT3)
  next
    show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
      by (blast intro: is_processT4)
  next
    show \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<Longrightarrow>
          (s, X \<union> Y) \<in> ?f\<close> for s X Y by (blast intro!: is_processT5)
  next
    show \<open>(s @ [\<checkmark>(r)], {}) \<in> ?f \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> ?f\<close> for s r X
      by (blast intro: is_processT6)
  next
    show \<open>s \<in> ?d \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> ?d\<close> for s t
      by (blast intro: is_processT7)
  next
    show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X
      by (blast intro!: is_processT8)
  next
    show \<open>s @ [\<checkmark>(r)] \<in> ?d \<Longrightarrow> s \<in> ?d\<close> for s r
      by (blast intro!: is_processT9)
  qed
qed


syntax "_Mndetprefix" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" 
  (\<open>(3\<sqinter>((_)/\<in>(_))/ \<rightarrow> (_))\<close> [78,78,77] 77)
syntax_consts "_Mndetprefix" \<rightleftharpoons> Mndetprefix
  (* "_writeS"  :: "['b \<Rightarrow> 'a, pttrn, 'b set, ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] => ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" 
                          ("(4(_\<^bold>!_\<^bold>|_) /\<rightarrow> _)" [0,0,50,78] 50) *)

translations "\<sqinter>a \<in> A \<rightarrow> P" \<rightleftharpoons> "CONST Mndetprefix A (\<lambda>a. P)"
  (* "_writeS c p b P"  => "CONST Mndetprefix (c ` {p. b}) (\<lambda>_. P)" *)



lemma F_Mndetprefix:
  \<open>\<F> (\<sqinter>a \<in> A \<rightarrow> P a) = (if A = {} then {(s, X). s = []} else \<Union>x\<in>A. \<F> (x \<rightarrow> P x))\<close>
  by (simp add: Failures.rep_eq FAILURES_def STOP.rep_eq Mndetprefix.rep_eq)

lemma D_Mndetprefix : \<open>\<D> (\<sqinter>a \<in> A \<rightarrow> P a) = (if A = {} then {} else \<Union>x\<in>A. \<D> (x \<rightarrow> P x))\<close>
  by (simp add: Divergences.rep_eq DIVERGENCES_def STOP.rep_eq Mndetprefix.rep_eq)

lemma T_Mndetprefix: \<open>\<T> (\<sqinter>a \<in> A \<rightarrow> P a) = (if A = {} then {[]} else \<Union>x\<in>A. \<T> (x \<rightarrow> P x))\<close>
  by (auto simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_Mndetprefix)

lemma mono_Mndetprefix_eq: \<open>(\<And>a. a \<in> A \<Longrightarrow> P a = Q a) \<Longrightarrow> \<sqinter>a \<in> A \<rightarrow> P a = \<sqinter>a \<in> A \<rightarrow> Q a\<close>
  by (cases \<open>A = {}\<close>, simp; subst Process_eq_spec, auto simp add: F_Mndetprefix D_Mndetprefix)


lemma F_Mndetprefix' :
  \<open>\<F> (\<sqinter>a \<in> A \<rightarrow> P a) =
   (  if A = {} then {(s, X). s = []}
    else {([], X)| X. \<exists>a \<in> A. ev a \<notin> X} \<union> {(ev a # s, X) |a s X. a \<in> A \<and> (s, X) \<in> \<F> (P a)})\<close>
  by (simp add: F_Mndetprefix write0_def F_Mprefix) blast

lemma D_Mndetprefix' : \<open>\<D> (\<sqinter>a \<in> A \<rightarrow> P a) = {ev a # s |a s. a \<in> A \<and> s \<in> \<D> (P a)}\<close>
  by (auto simp add: D_Mndetprefix write0_def D_Mprefix)

lemma T_Mndetprefix' : \<open>\<T> (\<sqinter>a \<in> A \<rightarrow> P a) = insert [] {ev a # s |a s. a \<in> A \<and> s \<in> \<T> (P a)}\<close>
  by (auto simp add: T_Mndetprefix write0_def T_Mprefix)

lemmas Mndetprefix_projs = F_Mndetprefix' D_Mndetprefix' T_Mndetprefix'


text\<open> Thus we know now, that Mndetprefix yields processes. Direct consequences are the following
  distributivities: \<close>

lemma Mndetprefix_singl [simp] : \<open>\<sqinter> a \<in> {a} \<rightarrow> P a = a \<rightarrow> P a\<close> 
  by (auto simp add: Process_eq_spec F_Mndetprefix D_Mndetprefix)

lemma Mndetprefix_Un_distrib :
  \<open>A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> \<sqinter>x \<in> (A \<union> B) \<rightarrow> P x = (\<sqinter>a \<in> A \<rightarrow> P a) \<sqinter> (\<sqinter>b \<in> B \<rightarrow> P b)\<close>
  by(auto simp : Process.Process_eq_spec F_Ndet D_Ndet F_Mndetprefix D_Mndetprefix)

text\<open> The two lemmas @{thm Mndetprefix_singl} and @{thm Mndetprefix_Un_distrib} together give us that @{const Mndetprefix} 
      can be represented by a fold in the finite case. \<close>                                         

lemma Mndetprefix_distrib_unit :
  \<open>A - {a} \<noteq> {} \<Longrightarrow> \<sqinter> x \<in> insert a A \<rightarrow> P x = (a \<rightarrow> P a) \<sqinter> (\<sqinter>x \<in> (A - {a}) \<rightarrow> P x)\<close>
  by (metis Un_Diff_cancel insert_is_Un insert_not_empty Mndetprefix_Un_distrib Mndetprefix_singl)

text\<open> This also implies that \<^const>\<open>Mndetprefix\<close> is continuous when \<^term>\<open>finite A\<close>,
      but this is not really useful since we have the general case. \<close>


subsection\<open>General case Continuity\<close>

lemma mono_Mndetprefix : \<open>\<sqinter>a \<in> A \<rightarrow> P a \<sqsubseteq> \<sqinter>a \<in> A \<rightarrow> Q a\<close>
  (is \<open>?P \<sqsubseteq> ?Q\<close>) if \<open>\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq> Q a\<close>
proof (unfold le_approx_def, intro conjI impI allI subsetI)
  from that[THEN le_approx1] show \<open>s \<in> \<D> ?Q \<Longrightarrow> s \<in> \<D> ?P\<close> for s
    by (auto simp add: D_Mndetprefix')
next
  from that[THEN le_approx2] show \<open>s \<notin> \<D> ?P \<Longrightarrow> \<R>\<^sub>a ?P s = \<R>\<^sub>a ?Q s\<close> for s
    by (auto simp add: Refusals_after_def D_Mndetprefix' F_Mndetprefix')
next
  from that[THEN le_approx3] show \<open>s \<in> min_elems (\<D> ?P) \<Longrightarrow> s \<in> \<T> ?Q\<close> for s
    by (simp add: min_elems_def D_Mndetprefix' T_Mndetprefix' subset_iff) (metis less_cons)
qed


lemma chain_Mndetprefix : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. \<sqinter>a\<in>A \<rightarrow> Y i a)\<close>
  by (simp add: fun_belowD mono_Mndetprefix chain_def)


lemma cont_Mndetprefix_prem : \<open>\<sqinter>a \<in> A \<rightarrow> (\<Squnion>i. Y i a) = (\<Squnion>i. \<sqinter>a \<in> A \<rightarrow> Y i a)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>chain Y\<close>
proof (subst Process_eq_spec, safe)
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (auto simp add: F_Mndetprefix' limproc_is_thelub \<open>chain Y\<close> F_LUB
        ch2ch_fun chain_Mndetprefix split: if_split_asm)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (simp add: F_Mndetprefix' limproc_is_thelub \<open>chain Y\<close> F_LUB ch2ch_fun
        chain_Mndetprefix split: if_split_asm) blast
next
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: D_Mndetprefix' limproc_is_thelub \<open>chain Y\<close> D_LUB ch2ch_fun chain_Mndetprefix)
next
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (simp add: D_Mndetprefix' limproc_is_thelub \<open>chain Y\<close> D_LUB ch2ch_fun chain_Mndetprefix) blast
qed


lemma Mndetprefix_cont [simp] : \<open>cont (\<lambda>b. \<sqinter>a \<in> A \<rightarrow> f a b)\<close> if * : \<open>\<And>a. a \<in> A \<Longrightarrow> cont (f a)\<close>
proof -
  define g where \<open>g a b \<equiv> if a \<in> A then f a b else undefined\<close> for a b
  have \<open>(\<lambda>b. \<sqinter>a \<in> A \<rightarrow> f a b) = (\<lambda>b. \<sqinter>a \<in> A \<rightarrow> g a b)\<close>
    by (intro ext mono_Mndetprefix_eq) (simp add: g_def)
  moreover have \<open>cont (\<lambda>b. \<sqinter>a \<in> A \<rightarrow> g a b)\<close>
  proof (rule cont_compose[where c = \<open>Mndetprefix A\<close>])
    show \<open>cont (Mndetprefix A)\<close>
    proof (rule contI2)
      show \<open>monofun (Mndetprefix A)\<close> by (simp add: fun_belowD mono_Mndetprefix monofunI)
    next
      show \<open>chain Y \<Longrightarrow> Mndetprefix A (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. Mndetprefix A (Y i))\<close>
        for Y :: \<open>nat \<Rightarrow> 'a \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
        by (simp add: cont_Mndetprefix_prem lub_fun)
    qed
  next
    show \<open>cont (\<lambda>b a. g a b)\<close> 
      by (rule cont2cont_lambda, rule contI2)
        (simp_all add: cont2monofunE cont2contlubE g_def monofunI "*")
  qed
  ultimately show \<open>cont (\<lambda>b. \<sqinter>a\<in>A \<rightarrow> f a b)\<close> by simp
qed


(* TODO: redo the formatting with subsections, sections, etc. *)

subsection\<open> High-level Syntax for Write \<close>

text \<open>A version with a non deterministic choice is also introduced.\<close>

definition ndet_write :: \<open>['a \<Rightarrow> 'b, 'a set, 'a \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>ndet_write c A P \<equiv> Mndetprefix (c ` A) (P o (inv_into A c))\<close>

definition "write" :: \<open>['a \<Rightarrow> 'b, 'a, ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>write c a P \<equiv> Mprefix {c a} (\<lambda>x. P)\<close>

syntax
  "_ndet_write"   :: \<open>['a \<Rightarrow> 'b, pttrn, ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3((_)\<^bold>!\<^bold>!(_)) /\<rightarrow> _)\<close> [78,78,77] 77)
  "_ndet_writeX"  :: \<open>['a \<Rightarrow> 'b, pttrn, bool,('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3((_)\<^bold>!\<^bold>!(_))\<^bold>|_ /\<rightarrow> _)\<close> [78,78,78,77] 77)
  "_ndet_writeS"  :: \<open>['a \<Rightarrow> 'b, pttrn, 'b set,('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3((_)\<^bold>!\<^bold>!(_))\<in>_ /\<rightarrow> _)\<close> [78,78,78,77] 77)
  "_write" ::  \<open>['a \<Rightarrow> 'b, 'a, ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(3(_)\<^bold>!(_) /\<rightarrow> _)\<close> [78,78,77] 77)


syntax_consts "_ndet_write"  \<rightleftharpoons> ndet_write
  and         "_ndet_writeX" \<rightleftharpoons> ndet_write
  and         "_ndet_writeS" \<rightleftharpoons> ndet_write
  and         "_write"       \<rightleftharpoons> ndet_write


translations
  "_ndet_write c p P"      \<rightleftharpoons> "CONST ndet_write c CONST UNIV (\<lambda>p. P)"
  "_ndet_writeX c p b P"   => "CONST ndet_write c {p. b} (\<lambda>p. P)"
  "_ndet_writeS c p A P"   => "CONST ndet_write c A (\<lambda>p. P)"
  "_write c a P"           \<rightleftharpoons> "CONST write c a P"

text \<open>Syntax checks.\<close>

term \<open>c\<^bold>!\<^bold>!x \<rightarrow> P x\<close>
term \<open>c\<^bold>!\<^bold>!x\<in>A \<rightarrow> P x\<close>
term \<open>c\<^bold>!\<^bold>!x\<^bold>|(0<x) \<rightarrow> P x\<close>

term \<open>(c \<circ> c')\<^bold>!\<^bold>!a\<in>A \<rightarrow> d\<^bold>?b\<in>B \<rightarrow> event \<rightarrow> e\<^bold>!a' \<rightarrow> P a b\<close>

term \<open>c\<^bold>!x \<rightarrow> P\<close>


lemma mono_ndet_write: \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq> Q a) \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<sqsubseteq> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a)\<close>
  unfolding ndet_write_def by (simp add: inv_into_into mono_Mndetprefix)

lemma ndet_write_cont[simp]:
  \<open>(\<And>a. a \<in> A \<Longrightarrow> cont (\<lambda>b. P b a)) \<Longrightarrow> cont (\<lambda>y. c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P y a)\<close>
  unfolding ndet_write_def o_def by (rule Mndetprefix_cont) (simp add: inv_into_into)


lemma mono_write: \<open>P \<sqsubseteq> Q \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<sqsubseteq> c\<^bold>!a \<rightarrow> Q\<close>
  unfolding write_def by (simp add: mono_Mprefix)

lemma write_cont[simp]: \<open>cont P \<Longrightarrow> cont (\<lambda>x. c\<^bold>!a \<rightarrow> P x)\<close>
  unfolding write_def by simp


lemma read_singl[simp] : \<open>c\<^bold>?a\<in>{x} \<rightarrow> P a = c\<^bold>!x \<rightarrow> P x\<close>
  by (simp add: read_def Mprefix_singl write_def)

lemma ndet_write_singl[simp] : \<open>c\<^bold>!\<^bold>!a\<in>{x} \<rightarrow> P a = c\<^bold>!x \<rightarrow> P x\<close>
  by (simp add: ndet_write_def Mprefix_singl write_def)

lemma write_is_write0 : \<open>c\<^bold>!x \<rightarrow> P = c x \<rightarrow> P\<close>
  by (simp add: write0_def write_def)

(*<*)
end
  (*>*)