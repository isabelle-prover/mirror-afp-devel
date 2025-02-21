(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
 *
 * This file       : Extension of the AfterExt operator with a locale
 *
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

section\<open> The After trace Operator \<close>

(*<*)
theory  After_Trace_Operator
  imports After_Ext_Operator
begin
  (*>*)


context AfterExt
begin


subsection \<open>Definition\<close>

text \<open>We just defined \<^term>\<open>P after\<^sub>\<checkmark> e\<close> for @{term [show_types] \<open>P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>}
      and @{term [show_types] \<open>e :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>}.
      Since a trace of a \<^term>\<open>P\<close> is just an \<^typ>\<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list\<close>, the following 
      inductive definition is natural.\<close>

fun After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>after\<^sub>\<T>\<close> 86)
  where \<open>P after\<^sub>\<T> [] = P\<close>
  |     \<open>P after\<^sub>\<T> (e # t) = P after\<^sub>\<checkmark> e after\<^sub>\<T> t\<close>



text \<open>We can also induct backward.\<close>

lemma After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_append: \<open>P after\<^sub>\<T> (t @ u) = P after\<^sub>\<T> t after\<^sub>\<T> u\<close>
  apply (induct u rule: rev_induct, solves \<open>simp\<close>)
  apply (induct t rule: rev_induct, solves \<open>simp\<close>)
  by (metis After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps append.assoc append.right_neutral append_Cons append_Nil)

lemma After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc : \<open>P after\<^sub>\<T> (t @ [e]) = P after\<^sub>\<T> t after\<^sub>\<checkmark> e\<close>
  by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_append)



subsection \<open>Projections\<close>

lemma F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e:
  \<open>tF t \<Longrightarrow> (t @ u, X) \<in> \<F> P \<Longrightarrow> (u, X) \<in> \<F> (P after\<^sub>\<T> t)\<close>
proof (induct t arbitrary: u rule: rev_induct)
  show \<open>([] @ u, X) \<in> \<F> P \<Longrightarrow> (u, X) \<in> \<F> (P after\<^sub>\<T> [])\<close> for u by simp
next
  fix e t u
  assume   hyp : \<open>tF t \<Longrightarrow> (t @ u, X) \<in> \<F> P \<Longrightarrow> (u, X) \<in> \<F> (P after\<^sub>\<T> t)\<close> for u
  assume prems : \<open>tF (t @ [e])\<close> \<open>((t @ [e]) @ u, X) \<in> \<F> P\<close>
  have * : \<open>(e # u, X) \<in> \<F> (P after\<^sub>\<T> t)\<close> by (rule hyp; use prems in simp)
  thus \<open>(u, X) \<in> \<F> (P after\<^sub>\<T> (t @ [e]))\<close>
    by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc F_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      (metis initials_memI F_T non_tickFree_tick prems(1) tickFree_append_iff)
qed


lemma D_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e:
  \<open>tF t \<Longrightarrow> t @ u \<in> \<D> P \<Longrightarrow> u \<in> \<D> (P after\<^sub>\<T> t)\<close>
proof (induct t arbitrary: u rule: rev_induct)
  show \<open>[] @ u \<in> \<D> P \<Longrightarrow> u \<in> \<D> (P after\<^sub>\<T> [])\<close> for u by simp
next
  fix e t u
  assume   hyp : \<open>tF t \<Longrightarrow> t @ u \<in> \<D> P \<Longrightarrow> u \<in> \<D> (P after\<^sub>\<T> t)\<close> for u
  assume prems : \<open>tF ((t @ [e]))\<close> \<open>(t @ [e]) @ u \<in> \<D> P\<close>
  have * : \<open>e # u \<in> \<D> (P after\<^sub>\<T> t)\<close> by (rule hyp; use prems in simp)
  thus \<open>u \<in> \<D> (P after\<^sub>\<T> (t @ [e]))\<close>
    by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc D_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      (metis initials_memI D_T non_tickFree_tick prems(1) tickFree_append_iff)
qed


lemma T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e : \<open>t @ u \<in> \<T> P \<Longrightarrow> u \<in> \<T> (P after\<^sub>\<T> t)\<close>
proof (induct t arbitrary: u rule: rev_induct)
  show \<open>[] @ u \<in> \<T> P \<Longrightarrow> u \<in> \<T> (P after\<^sub>\<T> [])\<close> for u by simp
next
  fix e t u
  assume  hyp : \<open>t @ u \<in> \<T> P \<Longrightarrow> u \<in> \<T> (P after\<^sub>\<T> t)\<close> for u
  assume prem : \<open>(t @ [e]) @ u \<in> \<T> P\<close>
  have * : \<open>e # u \<in> \<T> (P after\<^sub>\<T> t)\<close> by (rule hyp, use prem in simp)
  thus \<open>u \<in> \<T> (P after\<^sub>\<T> (t @ [e]))\<close>
    by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc T_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      (metis initials_memI append_T_imp_tickFree
        is_processT1_TR non_tickFree_tick prem tickFree_append_iff)
qed


corollary initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e :
  \<open>t @ e # u \<in> \<T> P \<Longrightarrow> e \<in> (P after\<^sub>\<T> t)\<^sup>0\<close>
  by (metis initials_memI T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e)

corollary F_imp_R_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e: \<open>tF t \<Longrightarrow> (t, X) \<in> \<F> P \<Longrightarrow> X \<in> \<R> (P after\<^sub>\<T> t)\<close>
  by (simp add: F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e Refusals_iff)

corollary D_imp_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_is_BOT: \<open>tF t \<Longrightarrow> t \<in> \<D> P \<Longrightarrow> P after\<^sub>\<T> t = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e)


lemma F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq:
  \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> \<F> (P after\<^sub>\<T> t) = {(u, X). (t @ u, X) \<in> \<F> P}\<close>
proof safe
  show \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> (u, X) \<in> \<F> (P after\<^sub>\<T> t) \<Longrightarrow> (t @ u, X) \<in> \<F> P\<close> for u X
  proof (induct t arbitrary: u rule: rev_induct)
    show \<open>(u, X) \<in> \<F> (P after\<^sub>\<T> []) \<Longrightarrow> ([] @ u, X) \<in> \<F> P\<close> for u by simp
  next
    case (snoc e t)
    from initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e snoc.prems(1) have * : \<open>e \<in> (P after\<^sub>\<T> t)\<^sup>0\<close> by blast
    obtain a where \<open>e = ev a\<close> 
      by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust non_tickFree_tick snoc.prems(2) tickFree_append_iff)
    show ?case
      apply (simp, rule snoc.hyps)
        apply (metis prefixI is_processT3_TR snoc.prems(1))
       apply (use snoc.prems(2) tickFree_append_iff in blast)
      using snoc.prems(3) "*" by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc F_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>e = ev a\<close>)
  qed
next
  show \<open>tF t \<Longrightarrow> (t @ u, X) \<in> \<F> P \<Longrightarrow> (u, X) \<in> \<F> (P after\<^sub>\<T> t)\<close> for u X
    by (fact F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e)
qed


lemma D_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq:
  \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> \<D> (P after\<^sub>\<T> t) = {u. t @ u \<in> \<D> P}\<close>
proof safe
  show \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> u \<in> \<D> (P after\<^sub>\<T> t) \<Longrightarrow> t @ u \<in> \<D> P\<close> for u
  proof (induct t arbitrary: u rule: rev_induct)
    show \<open>u \<in> \<D> (P after\<^sub>\<T> []) \<Longrightarrow> [] @ u \<in> \<D> P\<close> for u by simp
  next
    case (snoc e t)
    from initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e snoc.prems(1) have * : \<open>e \<in> (P after\<^sub>\<T> t)\<^sup>0\<close> by blast
    obtain a where \<open>e = ev a\<close> 
      by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust non_tickFree_tick snoc.prems(2) tickFree_append_iff)
    show ?case
      apply (simp, rule snoc.hyps)
        apply (metis prefixI is_processT3_TR snoc.prems(1))
      using "*" After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc D_After \<open>e = ev a\<close> snoc.prems(2, 3) by auto
  qed
next
  show \<open>tF t \<Longrightarrow> t @ u \<in> \<D> P \<Longrightarrow> u \<in> \<D> (P after\<^sub>\<T> t)\<close> for u by (fact D_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e)
qed


lemma T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq:
  \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> \<T> (P after\<^sub>\<T> t) = {u. t @ u \<in> \<T> P}\<close>
proof safe
  show \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> u \<in> \<T> (P after\<^sub>\<T> t) \<Longrightarrow> t @ u \<in> \<T> P\<close> for u
  proof (induct t arbitrary: u rule: rev_induct)
    show \<open>u \<in> \<T> (P after\<^sub>\<T> []) \<Longrightarrow> [] @ u \<in> \<T> P\<close> for u by simp
  next
    case (snoc e t)
    from initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e snoc.prems(1) have * : \<open>e \<in> (P after\<^sub>\<T> t)\<^sup>0\<close> by blast
    obtain a where \<open>e = ev a\<close> 
      by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust non_tickFree_tick snoc.prems(2) tickFree_append_iff)
    show ?case
      apply (simp, rule snoc.hyps)
        apply (meson prefixI is_processT3_TR snoc.prems(1))
      using "*" After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc T_After \<open>e = ev a\<close> snoc.prems(2, 3) by auto
  qed
next
  show \<open>t @ u \<in> \<T> P \<Longrightarrow> u \<in> \<T> (P after\<^sub>\<T> t)\<close> for u by (fact T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e)
qed



subsection \<open>Monotony\<close>

(* lemma mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_T  :
  \<open>(\<And>P Q. P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> \<Omega> P \<sqsubseteq>\<^sub>T \<Omega> Q)  \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q  \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>T Q after\<^sub>\<T> s\<close>
  and mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_F  :
  \<open>(\<And>P Q. P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> \<Omega> P \<sqsubseteq>\<^sub>F \<Omega> Q)  \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q  \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>F Q after\<^sub>\<T> s\<close>
  and mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_D  :
  \<open>(\<And>P Q. P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> \<Omega> P \<sqsubseteq>\<^sub>D \<Omega> Q)  \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q  \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>D Q after\<^sub>\<T> s\<close>
  and mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_FD :
  \<open>(\<And>P Q. P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> \<Omega> P \<sqsubseteq>\<^sub>F\<^sub>D \<Omega> Q) \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>F\<^sub>D Q after\<^sub>\<T> s\<close>
  and mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_DT :
  \<open>(\<And>P Q. P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> \<Omega> P \<sqsubseteq>\<^sub>D\<^sub>T \<Omega> Q) \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>D\<^sub>T Q after\<^sub>\<T> s\<close>
  if \<open>s \<in> \<T> Q\<close> and \<open>tF s\<close>
  using that apply (all \<open>induct s arbitrary: P Q rule: rev_induct; simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc\<close>)

  oops
      *)

(* lemma mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e : \<open>P \<sqsubseteq> Q \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq> Q after\<^sub>\<T> s\<close>
  by (induct s rule: rev_induct) (simp_all add: mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc)

lemma mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_T : 
  \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> tF s \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>T Q after\<^sub>\<T> s\<close>
  by (induct s rule: rev_induct; simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc)
     (rule mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T; use is_processT3_ST in blast)

lemma mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_F : 
  \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> tF s \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>F Q after\<^sub>\<T> s\<close>
  by (induct s rule: rev_induct; simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc)
     (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust is_processT3_ST mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_F initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e)

lemma mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_D : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>D Q after\<^sub>\<T> s\<close>
  by (induct s rule: rev_induct) (simp_all add: mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_D After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc)

lemma mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_FD :
  \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>F\<^sub>D Q after\<^sub>\<T> s\<close>
  by (induct s rule: rev_induct; simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc)
     (meson initials_memI T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e is_processT3_ST mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)

lemma mono_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_DT :
  \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P after\<^sub>\<T> s \<sqsubseteq>\<^sub>D\<^sub>T Q after\<^sub>\<T> s\<close>
  by (induct s rule: rev_induct; simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT)

 *)




subsection \<open>Four inductive Constructions with @{const [source] After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e}\<close>

subsubsection \<open>Reachable Processes\<close>

inductive_set reachable_processes :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>\<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c\<close>)
  for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where reachable_self : \<open>P \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
  |     reachable_after: \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> Q after e \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>


lemma reachable_processes_is: \<open>\<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P = {Q. \<exists>t \<in> \<T> P. tF t \<and> Q = P after\<^sub>\<T> t}\<close>
proof safe
  show \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> \<exists>t \<in> \<T> P. tF t \<and> Q = P after\<^sub>\<T> t\<close> for Q
  proof (induct rule: reachable_processes.induct)
    show \<open>\<exists>t \<in> \<T> P. tF t \<and> P = P after\<^sub>\<T> t\<close>
    proof (intro bexI)
      show \<open>tF [] \<and> P = P after\<^sub>\<T> []\<close> by simp
    next
      show \<open>[] \<in> \<T> P\<close> by simp
    qed
  next
    fix Q e
    assume assms : \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> \<open>\<exists>t \<in> \<T> P. tF t \<and> Q = P after\<^sub>\<T> t\<close> \<open>ev e \<in> Q\<^sup>0\<close>
    from assms(2) obtain t where * : \<open>tF t\<close> \<open>t \<in> \<T> P\<close> \<open>Q = P after\<^sub>\<T> t\<close> by blast
    show \<open>\<exists>t\<in>\<T> P. tF t \<and> Q after e = P after\<^sub>\<T> t\<close>
    proof (intro bexI)
      show \<open>tF (t @ [ev e]) \<and> Q after e = P after\<^sub>\<T> (t @ [ev e])\<close>
        by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def "*"(1, 3))
    next
      from "*" T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq assms(3) initials_def
      show \<open>t @ [ev e] \<in> \<T> P\<close> by fastforce
    qed
  qed
next
  show \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> P after\<^sub>\<T> t \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> for t
  proof (induct t rule: rev_induct)
    show \<open>P after\<^sub>\<T> [] \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> by (simp add: reachable_self)
  next
    fix t e
    assume   hyp : \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> P after\<^sub>\<T> t \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
      and prems : \<open>t @ [e] \<in> \<T> P\<close> \<open>tF (t @ [e])\<close>
    from prems T_F_spec is_processT3 tickFree_append_iff
    have * : \<open>t \<in> \<T> P\<close> \<open>tF t\<close> by blast+
    obtain a where \<open>e = ev a\<close> 
      by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust non_tickFree_tick prems(2) tickFree_append_iff)
    thus \<open>P after\<^sub>\<T> (t @ [e]) \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
      by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        (use initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e prems(1) in
          \<open>blast intro: initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e prems(1) reachable_after[OF hyp[OF "*"]]\<close>)
  qed
qed

lemma reachable_processes_trans: \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> R \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c Q \<Longrightarrow> R \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
  apply (simp add: reachable_processes_is, elim bexE)
  apply (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_append[symmetric] T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq)
  using tickFree_append_iff by blast



subsubsection \<open>Antecedent Processes\<close>

inductive_set antecedent_processes :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>\<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c\<close>)
  for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where antecedent_self : \<open>P \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
  |     antecedent_after: \<open>Q after e \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>


lemma antecedent_processes_is: \<open>\<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P = {Q. \<exists>t \<in> \<T> Q. tF t \<and> P = Q after\<^sub>\<T> t}\<close>
proof safe
  have \<open>Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> P \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c Q\<close> for Q
  proof (induct rule: antecedent_processes.induct)
    show \<open>P \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> by (fact reachable_self)
  next
    show \<open>Q after e \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> P \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c (Q after e) \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> P \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c Q\<close> for Q e
      by (meson reachable_after reachable_self reachable_processes_trans)
  qed
  thus \<open>Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> \<exists>t \<in> \<T> Q. tF t \<and> P = Q after\<^sub>\<T> t\<close> for Q 
    by (simp add: reachable_processes_is)
next
  show \<open>t \<in> \<T> Q \<Longrightarrow> tF t \<Longrightarrow> Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c (Q after\<^sub>\<T> t)\<close> for t Q
  proof (induct t arbitrary: Q)
    show \<open>Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c (Q after\<^sub>\<T> [])\<close> for Q by (simp add: antecedent_self)
  next
    fix e t Q
    assume   hyp : \<open>\<And>Q. t \<in> \<T> Q \<Longrightarrow> tF t \<Longrightarrow> Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c (Q after\<^sub>\<T> t)\<close>
      and prems : \<open>e # t \<in> \<T> Q\<close> \<open>tF (e # t)\<close>
    from prems obtain a where \<open>e = ev a\<close> \<open>ev a \<in> Q\<^sup>0\<close>
      by (metis initials_memI is_ev_def tickFree_Cons_iff)
    with prems have \<open>t \<in> \<T> (Q after a)\<close> \<open>tF t\<close> by (simp_all add: T_After)
    from hyp[OF this] have \<open>Q after a \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c (Q after\<^sub>\<T> (e # t))\<close>
      by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def \<open>e = ev a\<close>)
    from this \<open>ev a \<in> Q\<^sup>0\<close> show \<open>Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c (Q after\<^sub>\<T> (e # t))\<close>
      by (fact antecedent_after)
  qed
qed

lemma antecedent_processes_trans: \<open>Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> R \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c Q \<Longrightarrow> R \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
  apply (simp add: antecedent_processes_is, elim bexE)
  apply (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_append[symmetric] T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq)
  using tickFree_append_iff by blast


corollary antecedent_processes_iff_rev_reachable_processes: \<open>P \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c Q \<longleftrightarrow> Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
  by (simp add: antecedent_processes_is reachable_processes_is)


subsection \<open>Nth initials Events\<close>

primrec nth_initials :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>_\<^bsup>_\<^esup>\<close> [1000, 3] 999)
  where \<open>P\<^bsup>0\<^esup>     = P\<^sup>0\<close>
  |     \<open>P\<^bsup>Suc n\<^esup> = \<Union> {(P after e)\<^bsup>n\<^esup> |e. ev e \<in> P\<^sup>0}\<close>


lemma \<open>P\<^bsup>0\<^esup> = P\<^sup>0\<close> by simp

lemma  first_initials_is : \<open>P\<^bsup>1\<^esup> = \<Union> {(P after e)\<^sup>0 |e. ev e \<in> P\<^sup>0}\<close> by simp

lemma second_initials_is :
  \<open>P\<^bsup>2\<^esup> = \<Union> {(P after e after f)\<^sup>0 |e f. ev e \<in> P\<^sup>0 \<and> ev f \<in> (P after e)\<^sup>0}\<close> 
  by (auto simp add: numeral_eq_Suc)

lemma third_initials_is :
  \<open>P\<^bsup>3\<^esup> = \<Union> {(P after e after f after g)\<^sup>0 |e f g. 
              ev e \<in> P\<^sup>0 \<and> ev f \<in> (P after e)\<^sup>0 \<and> ev g \<in> (P after e after f)\<^sup>0}\<close> 
  by (auto simp add: numeral_eq_Suc)


text \<open>More generally, we have the following result.\<close>

lemma nth_initials_is: \<open>P\<^bsup>n\<^esup> = \<Union> {(P after\<^sub>\<T> t)\<^sup>0 | t. t \<in> \<T> P \<and> tF t \<and> length t = n}\<close>
proof (induct n arbitrary: P)
  show \<open>P\<^bsup>0\<^esup> = \<Union> {(P after\<^sub>\<T> t)\<^sup>0 |t. t \<in> \<T> P \<and> tF t \<and> length t = 0}\<close> for P  by simp
next
  fix n P
  assume hyp : \<open>P\<^bsup>n\<^esup> = \<Union> {(P after\<^sub>\<T> t)\<^sup>0 |t. t \<in> \<T> P \<and> tF t \<and> length t = n}\<close> for P
  show \<open>P\<^bsup>Suc n\<^esup> = \<Union> {(P after\<^sub>\<T> t)\<^sup>0 |t. t \<in> \<T> P \<and> tF t \<and> length t = Suc n}\<close>
  proof safe
    show \<open>e \<in> P\<^bsup>Suc n\<^esup> \<Longrightarrow> e \<in> \<Union> {(P after\<^sub>\<T> t)\<^sup>0 |t. t \<in> \<T> P \<and> tF t \<and> length t = Suc n}\<close> for e
      by (auto simp add: hyp T_After)
        (metis (no_types, lifting) AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def AfterExt.After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps(2)
          event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(5) is_ev_def length_Cons tickFree_Cons_iff)
  next
    fix e t
    assume assms : \<open>e \<in> (P after\<^sub>\<T> t)\<^sup>0\<close> \<open>t \<in> \<T> P\<close> \<open>tF t\<close> \<open>length t = Suc n\<close>
    from assms(1-3) have * : \<open>t @ [e] \<in> \<T> P\<close>
      unfolding initials_def by (simp add: T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq)
    from assms(3, 4)obtain a t' where ** : \<open>t = ev a # t'\<close> \<open>tF t'\<close> \<open>length t' = n\<close>
      by (metis Suc_length_conv event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) tickFree_Cons_iff)
    with initials_memI assms(2) have \<open>ev a \<in> P\<^sup>0\<close> by blast
    show \<open>e \<in> P\<^bsup>Suc n\<^esup>\<close>
    proof (unfold nth_initials.simps(2), rule UnionI)
      from \<open>ev a \<in> P\<^sup>0\<close> show \<open>(P after a)\<^bsup>n\<^esup> \<in> {(P after e)\<^bsup>n\<^esup> |e. ev e \<in> P\<^sup>0}\<close> by blast
    next
      from assms(1, 2) "**"(1-3) \<open>ev a \<in> P\<^sup>0\<close>
      show \<open>e \<in> (P after a)\<^bsup>n\<^esup>\<close> by (auto simp add: hyp "**"(1) After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def T_After)
    qed
  qed
qed


lemma nth_initials_DF: \<open>(DF A)\<^bsup>n\<^esup> = ev ` A\<close>
  by (induct n) (auto simp add: initials_DF After_DF)

lemma nth_initials_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<^bsup>n\<^esup> = (if A = {} then if n = 0 then tick ` R else {} else ev ` A \<union> tick ` R)\<close>
  by (induct n) (auto simp add: initials_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S After_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)

lemma nth_initials_RUN: \<open>(RUN A)\<^bsup>n\<^esup> = ev ` A\<close>
  by (induct n) (auto simp add: initials_RUN After_RUN)

lemma nth_initials_CHAOS: \<open>(CHAOS A)\<^bsup>n\<^esup> = ev ` A\<close>
  by (induct n) (auto simp add: initials_CHAOS After_CHAOS)

lemma nth_initials_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<^bsup>n\<^esup> = (if A = {} then if n = 0 then tick ` R else {} else ev ` A \<union> tick ` R)\<close>
  by (induct n) (auto simp add: initials_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S After_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)



subsubsection \<open>Reachable Ev\<close>

inductive reachable_ev :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where initial_ev_reachable:
    \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> reachable_ev P a\<close>
  |     reachable_ev_after_reachable:
    \<open>ev b \<in> P\<^sup>0 \<Longrightarrow> reachable_ev (P after b) a \<Longrightarrow> reachable_ev P a\<close>

definition reachable_ev_set :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a set\<close> (\<open>\<R>\<^sub>e\<^sub>v\<close>)
  where \<open>\<R>\<^sub>e\<^sub>v P \<equiv> \<Union>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. {a. ev a \<in> Q\<^sup>0}\<close>


lemma reachable_ev_BOT : \<open>reachable_ev \<bottom> a\<close>
  and not_reachable_ev_STOP : \<open>\<not> reachable_ev STOP a\<close>
  and not_reachable_ev_SKIP : \<open>\<not> reachable_ev (SKIP r) a\<close>
  by (subst reachable_ev.simps, simp)+


lemma events_of_iff_reachable_ev: \<open>a \<in> \<alpha>(P) \<longleftrightarrow> reachable_ev P a\<close>
proof (intro iffI)
  show \<open>reachable_ev P a \<Longrightarrow> a \<in> \<alpha>(P)\<close>
    apply (induct rule: reachable_ev.induct;
        simp add: T_After events_of_def initials_def split: if_split_asm)
    by (meson list.set_intros(1)) (meson list.set_intros(2))
next
  assume \<open>a \<in> \<alpha>(P)\<close>
  then obtain t where * : \<open>t \<in> \<T> P\<close> \<open>ev a \<in> set t\<close> by (meson events_of_memD)
  thus \<open>reachable_ev P a\<close>
  proof (induct t arbitrary: P)
    show \<open>\<And>P a. ev a \<in> set [] \<Longrightarrow> reachable_ev P a\<close> by simp
  next
    case (Cons e t)
    from Cons.prems(1) initials_memI
    have * : \<open>e \<in> P\<^sup>0\<close> unfolding initials_def by blast
    from Cons.prems(2) consider \<open>e = ev a\<close> | \<open>ev a \<in> set t\<close> by auto
    thus \<open>reachable_ev P a\<close>
    proof cases
      assume \<open>e = ev a\<close>
      from "*"[simplified this]
      show \<open>reachable_ev P a\<close> by (fact reachable_ev.intros(1))
    next
      show \<open>reachable_ev P a\<close> if \<open>ev a \<in> set t\<close>
      proof (cases e)
        fix b
        assume \<open>e = ev b\<close>
        with * Cons.prems(1) have \<open>t \<in> \<T> (P after b)\<close> by (force simp add: T_After)
        show \<open>reachable_ev P a\<close>
        proof (rule reachable_ev.intros(2))
          from "*" \<open>e = ev b\<close> show \<open>ev b \<in> P\<^sup>0\<close> by blast
        next
          show \<open>reachable_ev (P after b) a\<close>
            by (fact Cons.hyps[OF \<open>t \<in> \<T> (P after b)\<close> \<open>ev a \<in> set t\<close>])
        qed
      next
        from Cons.prems(1) have \<open>e = \<checkmark>(r) \<Longrightarrow> t = []\<close> for r
          by simp (meson T_imp_front_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_Cons_iff)
        with \<open>ev a \<in> set t\<close> show \<open>e = \<checkmark>(r) \<Longrightarrow> reachable_ev P a\<close> for r by simp
      qed
    qed
  qed
qed


lemma reachable_ev_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T:
  \<open>reachable_ev P a \<longleftrightarrow> (\<exists>t \<in> \<T> P. tF t \<and> ev a \<in> (P after\<^sub>\<T> t)\<^sup>0)\<close>
proof (intro iffI)                                          
  show \<open>reachable_ev P a \<Longrightarrow> \<exists>t\<in>\<T> P. tF t \<and> ev a \<in> (P after\<^sub>\<T> t)\<^sup>0\<close>
  proof (induct rule: reachable_ev.induct)
    show \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> \<exists>t\<in>\<T> P. tF t \<and> ev a \<in> (P after\<^sub>\<T> t)\<^sup>0\<close> for a P
    proof (intro bexI)
      show \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> tF [] \<and> ev a \<in> (P after\<^sub>\<T> [])\<^sup>0\<close> by simp
    next
      show \<open>[] \<in> \<T> P\<close> by (fact Nil_elem_T)
    qed
  next
    fix b a P
    assume prems : \<open>ev b \<in> P\<^sup>0\<close> \<open>reachable_ev (P after b) a\<close>
      and   hyp : \<open>\<exists>t \<in> \<T> (P after b). tF t \<and> ev a \<in> (P after b after\<^sub>\<T> t)\<^sup>0\<close>
    from hyp obtain t
      where * : \<open>tF t\<close> \<open>t \<in> \<T> (P after b)\<close>
        \<open>ev a \<in> (P after b after\<^sub>\<T> t)\<^sup>0\<close> by blast
    show \<open>\<exists>t \<in> \<T> P. tF t \<and> ev a \<in> (P after\<^sub>\<T> t)\<^sup>0\<close>
    proof (intro bexI)
      show \<open>tF (ev b # t) \<and> ev a \<in> (P after\<^sub>\<T> (ev b # t))\<^sup>0\<close>
        by (simp add: "*"(1, 3) After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)        
    next
      from "*"(2) show \<open>ev b # t \<in> \<T> P\<close> by (simp add: T_After prems(1))
    qed
  qed
next
  show \<open>\<exists>t \<in> \<T> P. tF t \<and> ev a \<in> (P after\<^sub>\<T> t)\<^sup>0 \<Longrightarrow> reachable_ev P a\<close>
  proof (elim bexE conjE)
    show \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> ev a \<in> (P after\<^sub>\<T> t)\<^sup>0 \<Longrightarrow> reachable_ev P a\<close> for t
    proof (induct t arbitrary: P)
      show \<open>ev a \<in> (P after\<^sub>\<T> [])\<^sup>0 \<Longrightarrow> reachable_ev P a\<close> for P
        by (simp add: reachable_ev.intros(1))
    next
      fix e t P
      assume   hyp : \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> ev a \<in> (P after\<^sub>\<T> t)\<^sup>0 \<Longrightarrow>
                      reachable_ev P a\<close> for P
      assume prems : \<open>tF (e # t)\<close> \<open>e # t \<in> \<T> P\<close> \<open>ev a \<in> (P after\<^sub>\<T> (e # t))\<^sup>0\<close>
      from prems(1) obtain b where \<open>e = ev b\<close> by (cases e; simp)
      with prems(2) have initial : \<open>ev b \<in> P\<^sup>0\<close> by (simp add: initials_memI)
      from reachable_ev_after_reachable[OF initial[simplified \<open>e = ev b\<close>]]
        After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def T_After \<open>e = ev b\<close> hyp prems initial
      show \<open>reachable_ev P a\<close> by auto
    qed
  qed
qed



subsubsection \<open>Properties\<close>

corollary reachable_ev_set_is_mem_Collect_reachable_ev:
  \<open>\<R>\<^sub>e\<^sub>v P = {a. reachable_ev P a}\<close>
  by (auto simp add: reachable_ev_set_def reachable_processes_is
      reachable_ev_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T)  

corollary events_of_is_reachable_ev_set: \<open>\<alpha>(P) = \<R>\<^sub>e\<^sub>v P\<close>
  by (simp add: reachable_ev_set_is_mem_Collect_reachable_ev
      set_eq_iff events_of_iff_reachable_ev)

lemma events_of_reachable_processes_subset: \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> \<alpha>(Q) \<subseteq> \<alpha>(P)\<close>
  by (induct rule: reachable_processes.induct)
    (simp_all add: subset_iff events_of_iff_reachable_ev reachable_ev_after_reachable)


corollary events_of_antecedent_processes_superset: \<open>Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> \<alpha>(P) \<subseteq> \<alpha>(Q)\<close>
  by (simp add: antecedent_processes_iff_rev_reachable_processes
      events_of_reachable_processes_subset)

lemma events_of_is_Union_nth_initials: \<open>\<alpha>(P) = (\<Union>n. {a. ev a \<in> P\<^bsup>n\<^esup>})\<close>
  by (auto simp add: nth_initials_is events_of_iff_reachable_ev
      reachable_ev_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T)+


subsubsection \<open>Reachable Tick\<close>

inductive reachable_tick :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'r \<Rightarrow> bool\<close>
  where initial_tick_reachable:
    \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> reachable_tick P r\<close>
  |     reachable_tick_after_reachable:
    \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> reachable_tick (P after a) r \<Longrightarrow> reachable_tick P r\<close>

definition reachable_tick_set :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'r set\<close> (\<open>\<R>\<^sub>\<checkmark>\<close>)
  where \<open>\<R>\<^sub>\<checkmark> P \<equiv> \<Union>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. {r. \<checkmark>(r) \<in> Q\<^sup>0}\<close>


lemma reachable_tick_BOT : \<open>reachable_tick \<bottom> r\<close>
  and not_reachable_tick_STOP : \<open>\<not> reachable_tick STOP s\<close>
  and reachable_tick_SKIP_iff : \<open>reachable_tick (SKIP r) s \<longleftrightarrow> s = r\<close>
  by (subst reachable_tick.simps, simp)+


lemma ticks_of_iff_reachable_tick : \<open>r \<in> \<checkmark>s(P) \<longleftrightarrow> reachable_tick P r\<close>
proof (intro iffI)
  show \<open>reachable_tick P r \<Longrightarrow> r \<in> \<checkmark>s(P)\<close>
    apply (induct rule: reachable_tick.induct;
        simp add: T_After ticks_of_def initials_def split: if_split_asm)
    by (metis append_Nil, metis append_Cons)
next
  assume \<open>r \<in> \<checkmark>s(P)\<close>
  then obtain t where * : \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> by (meson ticks_of_memD)
  thus \<open>reachable_tick P r\<close>
  proof (induct t arbitrary: P)
    show \<open>[] @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> reachable_tick P r\<close> for P
      by (simp add: initial_tick_reachable initials_memI)
  next
    case (Cons e t)
    obtain a where \<open>e = ev a\<close>
      by (meson Cons.prems append_T_imp_tickFree is_ev_def not_Cons_self2 tickFree_Cons_iff)
    moreover from Cons.prems have \<open>e \<in> P\<^sup>0\<close> by (auto intro: initials_memI)
    ultimately have \<open>t @ [\<checkmark>(r)] \<in> \<T> (P after a)\<close>
      using Cons.prems by (simp add: T_After \<open>e = ev a\<close>)
    with Cons.hyps have \<open>reachable_tick (P after a) r\<close> by blast
    with \<open>e = ev a\<close> \<open>e \<in> P\<^sup>0\<close> reachable_tick_after_reachable
    show \<open>reachable_tick P r\<close> by blast
  qed
qed


lemma reachable_tick_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T:
  \<open>reachable_tick P r \<longleftrightarrow> (\<exists>t \<in> \<T> P. tF t \<and> \<checkmark>(r) \<in> (P after\<^sub>\<T> t)\<^sup>0)\<close>
proof (intro iffI)                                      
  show \<open>reachable_tick P r \<Longrightarrow> \<exists>t\<in>\<T> P. tF t \<and> \<checkmark>(r) \<in> (P after\<^sub>\<T> t)\<^sup>0\<close>
  proof (induct rule: reachable_tick.induct)
    show \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> \<exists>t\<in>\<T> P. tF t \<and> \<checkmark>(r) \<in> (P after\<^sub>\<T> t)\<^sup>0\<close> for r P
    proof (intro bexI)
      show \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> tF [] \<and> \<checkmark>(r) \<in> (P after\<^sub>\<T> [])\<^sup>0\<close> by simp
    next
      show \<open>[] \<in> \<T> P\<close> by (fact Nil_elem_T)
    qed
  next
    fix a P r
    assume prems : \<open>ev a \<in> P\<^sup>0\<close> \<open>reachable_tick (P after a) r\<close>
      and   hyp : \<open>\<exists>t\<in>\<T> (P after a). tF t \<and> \<checkmark>(r) \<in> (P after a after\<^sub>\<T> t)\<^sup>0\<close>
    from hyp obtain t
      where * : \<open>tF t\<close> \<open>t \<in> \<T> (P after a)\<close>
        \<open>\<checkmark>(r) \<in> (P after a after\<^sub>\<T> t)\<^sup>0\<close> by blast
    show \<open>\<exists>t\<in>\<T> P. tF t \<and> \<checkmark>(r) \<in> (P after\<^sub>\<T> t)\<^sup>0\<close>
    proof (intro bexI)
      show \<open>tF (ev a # t) \<and> \<checkmark>(r) \<in> (P after\<^sub>\<T> (ev a # t))\<^sup>0\<close>
        by (simp add: "*"(1, 3) After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)        
    next
      from "*"(2) show \<open>ev a # t \<in> \<T> P\<close> by (simp add: T_After prems(1))
    qed
  qed
next
  show \<open> \<exists>t\<in>\<T> P. tF t \<and> \<checkmark>(r) \<in> (P after\<^sub>\<T> t)\<^sup>0 \<Longrightarrow> reachable_tick P r\<close>
  proof (elim bexE conjE)
    show \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> \<checkmark>(r) \<in> (P after\<^sub>\<T> t)\<^sup>0 \<Longrightarrow> reachable_tick P r\<close> for t
    proof (induct t arbitrary: P)
      show \<open>\<checkmark>(r) \<in> (P after\<^sub>\<T> [])\<^sup>0 \<Longrightarrow> reachable_tick P r\<close> for P
        by (simp add: initial_tick_reachable)
    next
      fix e t P
      assume   hyp : \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> \<checkmark>(r) \<in> (P after\<^sub>\<T> t)\<^sup>0 \<Longrightarrow> reachable_tick P r\<close> for P
      assume prems : \<open>tF (e # t)\<close> \<open>e # t \<in> \<T> P\<close> \<open>\<checkmark>(r) \<in> (P after\<^sub>\<T> (e # t))\<^sup>0\<close>
      from prems(1) obtain a where \<open>e = ev a\<close> by (cases e; simp)
      with prems(2) have initial : \<open>ev a \<in> P\<^sup>0\<close> by (simp add: initials_memI)
      from reachable_tick_after_reachable[OF initial[simplified \<open>e = ev a\<close>]]
        After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def T_After \<open>e = ev a\<close> hyp prems initial
      show \<open>reachable_tick P r\<close> by auto
    qed
  qed
qed



subsubsection \<open>Properties\<close>

corollary reachable_tick_set_is_mem_Collect_reachable_tick :
  \<open>\<R>\<^sub>\<checkmark> P = {a. reachable_tick P a}\<close>
  by (auto simp add: reachable_tick_set_def reachable_processes_is
      reachable_tick_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T)  

corollary ticks_of_is_reachable_tick_set : \<open>\<checkmark>s(P) = \<R>\<^sub>\<checkmark> P\<close>
  by (simp add: reachable_tick_set_is_mem_Collect_reachable_tick
      set_eq_iff ticks_of_iff_reachable_tick)

lemma ticks_of_reachable_processes_subset : \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> \<checkmark>s(Q) \<subseteq> \<checkmark>s(P)\<close>
  by (induct rule: reachable_processes.induct)
    (simp_all add: subset_iff ticks_of_iff_reachable_tick reachable_tick_after_reachable)

corollary ticks_of_antecedent_processes_superset : \<open>Q \<in> \<A>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> \<checkmark>s(P) \<subseteq> \<checkmark>s(Q)\<close>
  by (simp add: antecedent_processes_iff_rev_reachable_processes
      ticks_of_reachable_processes_subset)

lemma ticks_of_is_Union_nth_initials: \<open>\<checkmark>s(P) = (\<Union>n. {r. \<checkmark>(r) \<in> P\<^bsup>n\<^esup>})\<close>
  by (auto simp add: nth_initials_is ticks_of_iff_reachable_tick
      reachable_tick_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T)+






subsection \<open>Characterizations for Deadlock Freeness\<close> 

text \<open>Remember that we have characterized \<^term>\<open>deadlock_free P\<close> with an equality involving
      \<^const>\<open>After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>: @{thm [show_question_marks=false] deadlock_free_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_characterization}.
      This can of course be derived in a characterization involving \<^const>\<open>After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e\<close>.\<close>

lemma deadlock_free_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_characterization:
  \<open>deadlock_free P \<longleftrightarrow> (\<forall>t \<in> \<T> P. range ev \<notin> \<R>\<^sub>a P t \<and> (t \<noteq> [] \<longrightarrow> deadlock_free (P after\<^sub>\<T> t)))\<close>
proof (intro iffI)
  show \<open>deadlock_free P \<Longrightarrow> \<forall>t\<in>\<T> P. range ev \<notin> \<R>\<^sub>a P t \<and> (t \<noteq> [] \<longrightarrow> deadlock_free (P after\<^sub>\<T> t))\<close>
  proof (intro ballI)
    show \<open>deadlock_free P \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> range ev \<notin> \<R>\<^sub>a P t \<and> (t \<noteq> [] \<longrightarrow> deadlock_free (P after\<^sub>\<T> t))\<close> for t
    proof (induct t rule: rev_induct)
      case Nil
      thus ?case
        by (subst (asm) deadlock_free_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_characterization)
          (simp add: Refusals_after_def Nil.prems(1) Refusals_iff)
    next
      case (snoc e t)
      thus ?case
        by (simp add: Refusals_after_def After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc)
          (metis After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps(1) After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc DF_FD_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_imp_R_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e T_F_spec
            deadlock_free_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_characterization deadlock_free_def 
            deadlock_free_implies_non_terminating initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e is_processT3)
    qed
  qed
  show \<open>\<forall>t\<in>\<T> P. range ev \<notin> \<R>\<^sub>a P t \<and> (t \<noteq> [] \<longrightarrow> deadlock_free (P after\<^sub>\<T> t)) \<Longrightarrow> deadlock_free P\<close>
    by (subst deadlock_free_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_characterization)
      (metis After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps Nil_elem_T Refusals_after_def
        Refusals_iff list.distinct(1) mem_Collect_eq initials_def)
qed   


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_characterization: 
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow>
   (\<forall>t \<in> \<T> P. tF t \<longrightarrow> UNIV \<notin> \<R>\<^sub>a P t \<and> (t \<noteq> [] \<longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P after\<^sub>\<T> t)))\<close>
  by (auto simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq Refusals_after_def)


text \<open>Actually, with @{const [source] After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e}, we can obtain much more powerful results.
      This will be developed later.\<close>



subsection \<open>Continuity\<close>

lemma After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_cont :
  \<open>\<lbrakk>\<forall>a. ev a \<in> set t \<longrightarrow> cont (\<lambda>P. \<Psi> P a);
    \<forall>r. \<checkmark>(r) \<in> set t \<longrightarrow> cont (\<lambda>P. \<Omega> P r); cont f\<rbrakk> \<Longrightarrow>
   cont (\<lambda>x. f x after\<^sub>\<T> t)\<close>
proof (induct t arbitrary: f)
  case Nil thus ?case by simp
next
  case (Cons e s)
  show ?case by (cases e; simp, rule Cons.hyps) (simp_all add: Cons.prems)
qed



end

(*<*)
end
  (*>*)