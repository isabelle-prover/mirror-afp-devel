(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Multi deterministic prefix choice
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

chapter \<open> The Prefix Choice Operators \<close>

section\<open> Multiple Deterministic Prefix Choice \<close>

(*<*)
theory  Multi_Deterministic_Prefix_Choice 
  imports Process 
begin 
  (*>*)

subsection\<open> The Definition and some Consequences \<close>

lift_definition Mprefix :: \<open>['a set, 'a \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda>A P. ({(tr, ref). tr = [] \<and> ref \<inter> ev ` A = {}} \<union>
             {(tr, ref). tr \<noteq> [] \<and> hd tr \<in> ev ` A \<and> (\<exists>a. ev a = hd tr \<and> (tl tr, ref) \<in> \<F> (P a))},
             {d. d \<noteq> [] \<and> hd d \<in> ev ` A \<and> (\<exists>a. ev a = hd d \<and> tl d \<in> \<D> (P a))})\<close>
proof -
  show \<open>?thesis A P\<close> (is \<open>is_process(?f, ?d)\<close>) for P and A
  proof (unfold is_process_def DIVERGENCES_def FAILURES_def fst_conv snd_conv, intro conjI allI impI)
    show \<open>([], {}) \<in> ?f\<close>
      by (simp add: is_processT1)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
      apply (cases s; simp add: image_iff)
      by (meson F_imp_front_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) front_tickFree_Cons_iff)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
      by (auto intro: is_processT3)
  next
    show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y  \<Longrightarrow>  (s, X) \<in> ?f\<close> for s X Y
      by (auto intro: is_processT4)
  next
    show \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for s X Y
      apply (cases s; simp add: disjoint_iff image_iff)
      using is_processT1 apply blast
      by (metis is_processT5)
  next
    show \<open>(s @ [\<checkmark>(r)], {}) \<in> ?f \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> ?f\<close> for s r X
      by (cases s) (auto intro: is_processT6)
  next
    show \<open>s \<in> ?d \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> ?d\<close> for s t
      by (cases s) (auto intro: is_processT7)
  next
    show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X
      by (auto intro: is_processT8) 
  next
    show \<open>s @ [\<checkmark>(r)] \<in> ?d \<Longrightarrow> s \<in> ?d\<close> for s r
      by (cases s) (auto intro: is_processT9)
  qed
qed


syntax "_Mprefix" :: \<open>[pttrn, 'a set, ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>	
  (\<open>(3\<box>((_)/\<in>(_))/ \<rightarrow> (_))\<close> [78,78,77] 77)
syntax_consts "_Mprefix" \<rightleftharpoons> Mprefix
translations "\<box>a\<in>A \<rightarrow> P" \<rightleftharpoons> "CONST Mprefix A (\<lambda>a. P)"

text\<open>Syntax Check:\<close>
term \<open>\<box>x\<in>A \<rightarrow> \<box>y\<in>A \<rightarrow> \<box>z\<in>A \<rightarrow> P z x y = Q\<close>


subsection \<open> Projections in Prefix \<close>

lemma F_Mprefix : 
  "\<F> (\<box>a \<in> A \<rightarrow> P a) = {([], X)| X. X \<inter> ev ` A = {}} \<union>
                         {(ev a # s, X)| a s X. a \<in> A \<and> (s, X) \<in> \<F> (P a)}"
  by (subst Failures.rep_eq, auto simp add: Mprefix.rep_eq FAILURES_def)
    (metis list.collapse)

lemma D_Mprefix: \<open>\<D> (\<box>a \<in> A \<rightarrow> P a) = {ev a # s| a s. a \<in> A \<and> s \<in> \<D> (P a)}\<close>
  by (subst Divergences.rep_eq, auto simp add: Mprefix.rep_eq DIVERGENCES_def)
    (metis list.collapse)

lemma T_Mprefix: \<open>\<T> (\<box>a \<in> A \<rightarrow> P a) = insert [] {ev a # s| a s. a \<in> A \<and> s \<in> \<T> (P a)}\<close>
  by (subst Traces.rep_eq, auto simp add: TRACES_def Failures.rep_eq[symmetric] F_Mprefix)
    (use F_T T_F in blast)+

lemmas Mprefix_projs = F_Mprefix D_Mprefix T_Mprefix


lemma mono_Mprefix_eq: \<open>(\<And>a. a \<in> A \<Longrightarrow> P a = Q a) \<Longrightarrow> Mprefix A P = Mprefix A Q\<close>
  by (subst Process_eq_spec) (auto simp add: F_Mprefix D_Mprefix)


subsection \<open> Basic Properties \<close>

lemma tick_notin_T_Mprefix [simp]: \<open>[\<checkmark>(r)] \<notin> \<T> (\<box>x \<in> A \<rightarrow> P x)\<close>
  by (simp add: T_Mprefix)


lemma Nil_notin_D_Mprefix [simp]: \<open>[] \<notin> \<D> (\<box>x \<in> A \<rightarrow> P x)\<close>
  by (simp add: D_Mprefix)

subsection\<open> Proof of Continuity Rule \<close>

subsubsection\<open> Backpatch Isabelle 2009-1\<close>

\<comment>\<open>re-introduced from Isabelle/HOLCF 2009-1; clearly
   a derived concept, but still a useful shortcut\<close>

(* TODO really useful ? *)

definition
  contlub :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool" 
  where
    "contlub f = (\<forall>Y. chain Y \<longrightarrow> f (\<Squnion> i. Y i) = (\<Squnion> i. f (Y i)))"

lemma contlubE:
  "\<lbrakk>contlub f; chain Y\<rbrakk> \<Longrightarrow> f (\<Squnion> i. Y i) = (\<Squnion> i. f (Y i))"
  by (simp add: contlub_def)


lemma monocontlub2cont: "\<lbrakk>monofun f; contlub f\<rbrakk> \<Longrightarrow> cont f"
  apply (rule contI)
  apply (rule thelubE)
   apply (erule (1) ch2ch_monofun)
  apply (erule (1) contlubE [symmetric])
  done

lemma contlubI:
  "(\<And>Y. chain Y \<Longrightarrow> f (\<Squnion> i. Y i) = (\<Squnion> i. f (Y i))) \<Longrightarrow> contlub f"
  by (simp add: contlub_def)


lemma cont2contlub: "cont f \<Longrightarrow> contlub f"
  apply (rule contlubI)
  apply (rule po_class.lub_eqI [symmetric])
  apply (erule (1) contE)
  done


subsubsection\<open> Core of Proof  \<close>

lemma mono_Mprefix : \<open>\<box>a \<in> A \<rightarrow> P a \<sqsubseteq> \<box>a \<in> A \<rightarrow> Q a\<close> (is \<open>?P \<sqsubseteq> ?Q\<close>)
  if \<open>\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq> Q a\<close>
proof (unfold le_approx_def, intro conjI impI allI subsetI)
  from that[THEN le_approx1] show \<open>s \<in> \<D> ?Q \<Longrightarrow> s \<in> \<D> ?P\<close> for s
    by (auto simp add: D_Mprefix)
next
  from that[THEN le_approx2] show \<open>s \<notin> \<D> ?P \<Longrightarrow> \<R>\<^sub>a ?P s = \<R>\<^sub>a ?Q s\<close> for s
    by (auto simp add: Refusals_after_def D_Mprefix F_Mprefix)
next
  from that[THEN le_approx3] show \<open>s \<in> min_elems (\<D> ?P) \<Longrightarrow> s \<in> \<T> ?Q\<close> for s
    by (simp add: min_elems_def D_Mprefix T_Mprefix subset_iff) (metis less_cons)
qed


lemma chain_Mprefix : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. \<box>a\<in>A \<rightarrow> Y i a)\<close>
  by (simp add: fun_belowD mono_Mprefix chain_def)


lemma cont_Mprefix_prem : \<open>\<box>a \<in> A \<rightarrow> (\<Squnion>i. Y i a) = (\<Squnion>i. \<box>a \<in> A \<rightarrow> Y i a)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>chain Y\<close>
proof (subst Process_eq_spec, safe)
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (auto simp add: F_Mprefix limproc_is_thelub \<open>chain Y\<close> F_LUB ch2ch_fun chain_Mprefix)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (simp add: F_Mprefix limproc_is_thelub \<open>chain Y\<close> F_LUB ch2ch_fun chain_Mprefix) blast
next
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: D_Mprefix limproc_is_thelub \<open>chain Y\<close> D_LUB ch2ch_fun chain_Mprefix)
next
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (simp add: D_Mprefix limproc_is_thelub \<open>chain Y\<close> D_LUB ch2ch_fun chain_Mprefix) blast
qed


lemma Mprefix_cont [simp] : \<open>cont (\<lambda>b. \<box>a \<in> A \<rightarrow> f a b)\<close> if * : \<open>\<And>a. a \<in> A \<Longrightarrow> cont (f a)\<close>
proof -
  define g where \<open>g a b \<equiv> if a \<in> A then f a b else undefined\<close> for a b
  have \<open>(\<lambda>b. \<box>a \<in> A \<rightarrow> f a b) = (\<lambda>b. \<box>a \<in> A \<rightarrow> g a b)\<close>
    by (intro ext mono_Mprefix_eq) (simp add: g_def)
  moreover have \<open>cont (\<lambda>b. \<box>a \<in> A \<rightarrow> g a b)\<close>
  proof (rule cont_compose[where c = \<open>Mprefix A\<close>])
    show \<open>cont (Mprefix A)\<close>
    proof (rule contI2)
      show \<open>monofun (Mprefix A)\<close> by (simp add: fun_belowD mono_Mprefix monofunI)
    next
      show \<open>chain Y \<Longrightarrow> Mprefix A (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. Mprefix A (Y i))\<close>
        for Y :: \<open>nat \<Rightarrow> 'a \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
        by (simp add: cont_Mprefix_prem lub_fun)
    qed
  next
    show \<open>cont (\<lambda>b a. g a b)\<close> 
      by (rule cont2cont_lambda, rule contI2)
        (simp_all add: cont2monofunE cont2contlubE g_def monofunI "*")
  qed
  ultimately show \<open>cont (\<lambda>b. \<box>a\<in>A \<rightarrow> f a b)\<close> by simp
qed



subsection\<open> High-level Syntax for Read and Write0\<close>

text\<open> The following syntax introduces the usual channel notation for CSP.
Slightly deviating from conventional wisdom, we view a channel not as a tag in
a pair, rather than as a function of type @{typ "'a\<Rightarrow>'b"}. This paves the way
for \emph{typed} channels over a common universe of events. \<close>

definition read :: \<open>['a \<Rightarrow> 'b, 'a set, 'a \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>read c A P  \<equiv> Mprefix (c ` A) (P \<circ> (inv_into A c))\<close>

definition write0 :: \<open>['a, ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixr \<open>\<rightarrow>\<close> 77)
  where \<open>write0 a P \<equiv> Mprefix {a} (\<lambda>x. P)\<close>


subsection\<open>CSP$_M$-Style Syntax for Communication Primitives\<close>

syntax
  "_read" :: \<open>['a \<Rightarrow> 'b, pttrn, ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3((_)\<^bold>?(_)) /\<rightarrow> _)\<close> [78,78,77] 77)
  "_readX"  :: \<open>['a \<Rightarrow> 'b, pttrn, bool, ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3((_)\<^bold>?(_))\<^bold>|_ /\<rightarrow> _)\<close> [78,78,78,77] 77)
  "_readS"  :: \<open>['a \<Rightarrow> 'b, pttrn, 'a set, ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('b, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3((_)\<^bold>?(_))\<in>_ /\<rightarrow> _)\<close> [78,78,78,77] 77)
  (* "_write0" :: \<open>['a, ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] => ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>  *)

translations
  "_read c p P"      \<rightleftharpoons> "CONST read c CONST UNIV (\<lambda>p. P)"
  "_readX c p b P"   => "CONST read c {p. b} (\<lambda>p. P)"
  (* "_write0 a P"      \<rightleftharpoons> "CONST write0 a P" *)
  "_readS c p A P"   => "CONST read c A (\<lambda>p. P)"

syntax_consts "_read"  \<rightleftharpoons> read
  and         "_readX" \<rightleftharpoons> read
  and         "_readS" \<rightleftharpoons> read




text\<open>Syntax Check:\<close>

term \<open>a \<rightarrow> P\<close>

term \<open>c\<^bold>?x \<rightarrow> d\<^bold>?y \<rightarrow> P a y\<close>
term \<open>c\<^bold>?x\<in>X \<rightarrow> P x\<close>
term \<open>c\<^bold>?x\<^bold>|(x<0) \<rightarrow> P x\<close>

term \<open>c\<^bold>?x \<rightarrow> d\<^bold>?y\<in>B \<rightarrow> e \<rightarrow> u\<^bold>?t\<^bold>|(t \<ge> 1) \<rightarrow> P a y\<close>

term \<open>(c \<circ> d)\<^bold>?a \<rightarrow> P a\<close>



lemma mono_write0 : \<open>P \<sqsubseteq> Q \<Longrightarrow> a \<rightarrow> P \<sqsubseteq> a \<rightarrow> Q\<close>
  unfolding write0_def by (simp add: mono_Mprefix)

lemma mono_read : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq> Q a) \<Longrightarrow> c\<^bold>?a\<in>A \<rightarrow> P a \<sqsubseteq> c\<^bold>?a\<in>A \<rightarrow> Q a\<close>
  unfolding read_def by (simp add: inv_into_into mono_Mprefix)


lemma read_cont[simp]:
  \<open>(\<And>a. a \<in> A \<Longrightarrow> cont (\<lambda>b. P b a)) \<Longrightarrow> cont (\<lambda>y. read c A (P y))\<close>
  unfolding read_def o_def by (rule Mprefix_cont) (simp add: inv_into_into)

lemma read_cont'[simp]: \<open>cont P \<Longrightarrow> cont (\<lambda>y. read c A (P y))\<close>
  unfolding read_def o_def by (rule Mprefix_cont, rule cont2cont_fun)



lemma read_cont''[simp]: \<open>(\<And>a. cont (f a)) \<Longrightarrow> cont (\<lambda>y. c\<^bold>?x \<rightarrow> f x y)\<close> by simp


lemma write0_cont[simp]: \<open>cont (P::('b::cpo \<Rightarrow> ('a, 'r)process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)) \<Longrightarrow> cont(\<lambda>x. a \<rightarrow> P x)\<close>
  by (simp add: write0_def)


lemma Mprefix_singl : \<open>\<box>x \<in> {a} \<rightarrow> P x = a \<rightarrow> P a\<close> 
  by (auto simp add: Process_eq_spec write0_def Mprefix_projs)

(*<*)
end
  (*>*)
