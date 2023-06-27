(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
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

theory Assertions
  imports CSP Process_Order
begin




section\<open>CSP Assertions\<close>

definition DF :: "'a set \<Rightarrow> 'a process"
  where   "DF A \<equiv> \<mu> X. \<sqinter> x \<in> A \<rightarrow> X"

lemma DF_unfold : "DF A = (\<sqinter> z \<in> A \<rightarrow> DF A)"
 by(simp add: DF_def, rule trans, rule fix_eq, simp)

definition deadlock_free :: "'a process \<Rightarrow> bool"
  where   "deadlock_free P \<equiv> DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"

definition DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P :: "'a set \<Rightarrow> 'a process"
  where   "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> \<mu> X. ((\<sqinter> x \<in> A \<rightarrow> X) \<sqinter> SKIP)"

(* TO DO: rename this in deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P *)
definition deadlock_free_v2 :: "'a process \<Rightarrow> bool"
  where   "deadlock_free_v2 P \<equiv> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F P"


section\<open>Some deadlock freeness laws\<close>

lemma DF_subset: "A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> DF B \<sqsubseteq>\<^sub>F\<^sub>D DF A" 
  apply(subst DF_def, rule fix_ind) 
  apply(rule le_FD_adm, simp_all add: monofunI, subst DF_unfold)
  by (meson mono_Mndetprefix_FD mono_Mndetprefix_FD_set trans_FD)

lemma DF_Univ_freeness: "A \<noteq> {} \<Longrightarrow> (DF A) \<sqsubseteq>\<^sub>F\<^sub>D P  \<Longrightarrow> deadlock_free P"
  by (meson deadlock_free_def DF_subset failure_divergence_refine_def order.trans subset_UNIV)

lemma deadlock_free_Ndet: "deadlock_free P \<Longrightarrow> deadlock_free Q \<Longrightarrow> deadlock_free (P \<sqinter> Q)"
  by (simp add: D_Ndet F_Ndet deadlock_free_def failure_divergence_refine_def le_ref_def)



section \<open>Preliminaries\<close>

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold : "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A = ((\<sqinter> z \<in> A \<rightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<sqinter> SKIP)"
  by(simp add: DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule trans, rule fix_eq, simp)


section \<open>Deadlock Free\<close>

lemma div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "\<D>(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = {}"
proof(simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def fix_def) 
  define Y where "Y \<equiv> \<lambda>i. iterate i\<cdot>(\<Lambda> x. (\<sqinter>xa\<in>A \<rightarrow>  x) \<sqinter> SKIP)\<cdot>\<bottom>"
  hence a:"chain Y" by simp
  have "\<D> (Y (Suc i)) = {d. d \<noteq> [] \<and> hd d  \<in> (ev ` A) \<and> tl d \<in> \<D>(Y i)}" for i
    by (cases "A={}", auto simp add:Y_def D_STOP D_SKIP D_Mndetprefix write0_def D_Mprefix D_Ndet) 
  hence b:"d \<in> \<D>(Y i) \<Longrightarrow> length d \<ge> i" for d i
    by (induct i arbitrary:d, simp_all add: Nitpick.size_list_simp(2))
  { fix x
    assume c:"\<forall> i. x \<in> \<D> (Y i)"
    from b have "x \<notin> \<D> (Y (Suc (length x)))" using Suc_n_not_le_n by blast
    with c have False by simp
  }
  with a show "\<D> (\<Squnion>i. Y i) = {}"
  using D_LUB[OF a] limproc_is_thelub[OF a] by auto
qed

lemma div_free_DF: "\<D>(DF A) = {}"
proof - 
  have "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>D DF A"
    apply (simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def)
    by(rule fix_ind, simp_all add: monofunI, subst DF_unfold, simp)
  then show ?thesis using divergence_refine_def div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P by blast 
qed

lemma deadlock_free_implies_div_free: "deadlock_free P \<Longrightarrow> \<D> P = {}"
  by (simp add: deadlock_free_def div_free_DF failure_divergence_refine_def le_ref_def)




section \<open>Run\<close>

definition RUN :: "'a set \<Rightarrow> 'a process"
  where   "RUN A \<equiv> \<mu> X. \<box> x \<in> A \<rightarrow> X"

definition CHAOS :: "'a set \<Rightarrow> 'a process" 
  where   "CHAOS A \<equiv> \<mu> X. (STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))"

definition lifelock_free :: "'a process \<Rightarrow> bool"
  where   "lifelock_free P \<equiv> CHAOS UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"




section \<open>Reference processes and their unfolding rules\<close>


definition CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P :: "'a set \<Rightarrow> 'a process" 
  where   "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> \<mu> X. (SKIP \<sqinter> STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))"


lemma RUN_unfold : "RUN A = (\<box> z \<in> A \<rightarrow> RUN A)"
  by(simp add: RUN_def, rule trans, rule fix_eq, simp)

lemma CHAOS_unfold : "CHAOS A = (STOP \<sqinter> (\<box> z \<in> A \<rightarrow> CHAOS A))"
  by(simp add: CHAOS_def, rule trans, rule fix_eq, simp)
                                              
lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> SKIP \<sqinter> STOP \<sqinter> (\<box> x \<in> A \<rightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)"
  unfolding CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def using fix_eq[of "\<Lambda> X. (SKIP \<sqinter> STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))"] by simp

section \<open>Process events and reference processes events\<close>

definition events_of where "events_of P \<equiv> (\<Union>t\<in>\<T> P. {a. ev a \<in> set t})"

lemma events_DF: "events_of (DF A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> \<T> (DF A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> \<T> (\<sqinter>z\<in>A \<rightarrow>  DF A)" using DF_unfold by metis
    then obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> \<T> (DF A)" 
      by (cases "A={}", auto simp add: T_Mndetprefix write0_def T_Mprefix T_STOP)
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa\<in>\<T> (DF A). ev x \<in> set xa"
    apply(subst DF_unfold, cases "A={}", auto simp add:T_Mndetprefix write0_def T_Mprefix)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "events_of (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> \<T> ((\<sqinter>z\<in>A \<rightarrow>  DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<sqinter> SKIP)" using DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold by metis
    with Cons obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)" 
      by (cases "A={}", auto simp add:T_Mndetprefix write0_def T_Mprefix T_STOP T_SKIP T_Ndet)  
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa\<in>\<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A). ev x \<in> set xa"
    apply(subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, cases "A={}")
     apply(auto simp add:T_Mndetprefix write0_def T_Mprefix T_SKIP T_Ndet)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_RUN: "events_of (RUN A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> \<T> (RUN A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> \<T> (\<box>z\<in>A \<rightarrow>  RUN A)" using RUN_unfold by metis
    then obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> \<T> (RUN A)" by (auto simp add:T_Mprefix)
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa \<in> \<T>(RUN A). ev x \<in> set xa"
    apply(subst RUN_unfold, simp add: T_Mprefix)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_CHAOS: "events_of (CHAOS A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> \<T> (CHAOS A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> \<T> (STOP \<sqinter> (\<box> z \<in> A \<rightarrow> CHAOS A))" using CHAOS_unfold by metis
    then obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> \<T> (CHAOS A)" 
      by (auto simp add:T_Ndet T_Mprefix T_STOP)
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa\<in>\<T> (CHAOS A). ev x \<in> set xa"
    apply(subst CHAOS_unfold, simp add:T_Ndet T_Mprefix T_STOP)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "events_of (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> \<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> \<T> (SKIP \<sqinter> STOP \<sqinter> (\<box> z \<in> A \<rightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A))" 
      using CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold by metis
    with Cons obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> \<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)" 
      by (auto simp add:T_Ndet T_Mprefix T_STOP T_SKIP)
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa\<in>\<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A). ev x \<in> set xa"
    apply(subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:T_Ndet T_Mprefix T_STOP T_SKIP)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_div: "\<D>(P) \<noteq> {} \<Longrightarrow>  events_of (P) = UNIV"
proof(auto simp add:events_of_def)
  fix x xa
  assume 1: "x \<in> \<D> P"
  show "\<exists>x\<in>\<T> P. ev xa \<in> set x"
  proof(cases "tickFree x")
    case True  
    hence "x@[ev xa] \<in> \<T> P"
      using 1 NT_ND front_tickFree_single is_processT7 by blast   
    then show ?thesis by force 
  next
    case False
    hence "(butlast x)@[ev xa] \<in> \<T> P"
      by (metis "1" D_T D_imp_front_tickFree append_single_T_imp_tickFree butlast_snoc 
                front_tickFree_single nonTickFree_n_frontTickFree process_charn) 
    then show ?thesis by force
  qed
qed



lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_subset_FD: "A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P B \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  apply(subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind, rule le_FD_adm, simp_all add:monofunI, subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
  by (rule mono_Ndet_FD, simp_all) (meson mono_Mndetprefix_FD mono_Mndetprefix_FD_set trans_FD) 

lemma RUN_subset_DT: "A \<subseteq> B \<Longrightarrow> RUN B \<sqsubseteq>\<^sub>D\<^sub>T RUN A"
  apply(subst RUN_def, rule fix_ind, rule le_DT_adm, simp_all add:monofunI, subst RUN_unfold)
  by (meson mono_Mprefix_DT mono_Mprefix_DT_set trans_DT)

lemma CHAOS_subset_FD: "A \<subseteq> B \<Longrightarrow> CHAOS B \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A"
  apply(subst CHAOS_def, rule fix_ind, rule le_FD_adm, simp_all add:monofunI, subst CHAOS_unfold)
  by (auto simp add: failure_divergence_refine_def le_ref_def 
                     D_Mprefix D_Ndet F_STOP F_Mprefix F_Ndet) 

lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_subset_FD: "A \<subseteq> B \<Longrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P B \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  apply(subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind, rule le_FD_adm) 
     apply(simp_all add:monofunI, subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
  by (auto simp add: failure_divergence_refine_def le_ref_def 
                     D_Mprefix D_Ndet F_STOP F_Mprefix F_Ndet)

section \<open>Relations between refinements on reference processes\<close>

lemma CHAOS_has_all_tickFree_failures: 
      "tickFree a \<Longrightarrow> {x. ev x \<in> set a} \<subseteq> A \<Longrightarrow> (a,b) \<in> \<F> (CHAOS A)"
proof(induct a)
  case Nil
  then show ?case 
    by (subst CHAOS_unfold, simp add:F_Ndet F_STOP)
next
  case (Cons a0 al)
  hence "tickFree al"
    by (metis append.left_neutral append_Cons front_tickFree_charn front_tickFree_mono)
  with Cons show ?case 
    apply (subst CHAOS_unfold, simp add:F_Ndet F_STOP F_Mprefix events_of_def)
    using event_set by blast
qed

lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures: 
  assumes as:"(events_of P) \<subseteq> A" 
  shows "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>F P"
proof -
  have "front_tickFree a \<Longrightarrow> set a \<subseteq> (\<Union>t\<in>\<T> P. set t) \<Longrightarrow> (a,b) \<in> \<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)" for a b
  proof(induct a)
    case Nil
    then show ?case 
      by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:F_Ndet F_STOP)
  next
    case (Cons a0 al)
    hence "front_tickFree al"
      by (metis append.left_neutral append_Cons front_tickFree_charn front_tickFree_mono)
    with Cons show ?case 
      apply (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:F_Ndet F_STOP F_SKIP F_Mprefix events_of_def as)
      apply(cases "a0=tick")
       apply (metis append.simps(2) front_tickFree_charn 
                    front_tickFree_mono list.distinct(1) tickFree_Cons)
      using event_set image_iff as[simplified events_of_def] by fastforce
  qed
  thus ?thesis 
    by (simp add: F_T SUP_upper failure_refine_def process_charn subrelI) 
qed

corollary CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures_ev: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P (events_of P) \<sqsubseteq>\<^sub>F P" 
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures_Un: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F P"
  by (simp_all add: CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures)


lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF_refine_F: "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F DF A"
  by (simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind, simp_all add: monofunI, subst DF_unfold, simp) 

lemma DF_RUN_refine_F: "DF A  \<sqsubseteq>\<^sub>F RUN A"
  apply (simp add:DF_def, rule fix_ind, simp_all add: monofunI, subst RUN_unfold)
  by (meson Mprefix_refines_Mndetprefix_F mono_Mndetprefix_F trans_F)

lemma CHAOS_DF_refine_F: "CHAOS A  \<sqsubseteq>\<^sub>F DF A"
  apply (simp add:CHAOS_def DF_def, rule parallel_fix_ind, simp_all add: monofunI)
   apply (rule le_F_adm, simp_all add: monofun_snd)
  by (cases "A={}", auto simp add:adm_def failure_refine_def F_Mndetprefix 
                                  F_Mprefix write0_def F_Ndet F_STOP)

corollary CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_CHAOS_refine_F: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F CHAOS A"
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_refine_F: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  by (simp_all add: CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures events_CHAOS events_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P 
                    trans_F[OF CHAOS_DF_refine_F DF_RUN_refine_F])




lemma div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "\<D> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = {}"
proof -
  have "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  proof (simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind, simp_all add: monofunI, subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
    fix x
    assume 1:"x \<sqsubseteq>\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
    have a:"((\<sqinter>xa\<in>A \<rightarrow>  x) \<sqinter> SKIP) = (SKIP \<sqinter> SKIP \<sqinter> (\<sqinter>xa\<in>A \<rightarrow>  x))" 
      by (simp add: Ndet_commute Ndet_id)
    from 1 have b:"(SKIP \<sqinter> SKIP \<sqinter> (\<sqinter>xa\<in>A \<rightarrow>  x)) \<sqsubseteq>\<^sub>D (SKIP \<sqinter> STOP \<sqinter> (\<box>xa\<in>A \<rightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A))"
      by (meson Mprefix_refines_Mndetprefix_D idem_D leD_STOP mono_Mprefix_D mono_Ndet_D trans_D)
    from a b show "((\<sqinter>xa\<in>A \<rightarrow>  x) |-| SKIP) \<sqsubseteq>\<^sub>D (SKIP |-| STOP |-| Mprefix A (\<lambda>x. CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A))" 
      by simp
  qed
  then show ?thesis using divergence_refine_def div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P by blast 
qed

lemma div_free_CHAOS: "\<D>(CHAOS A) = {}"
proof - 
  have "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>D CHAOS A"
    apply (simp add:CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind)
    by (simp_all add: monofunI, subst CHAOS_unfold, simp) 
  then show ?thesis using divergence_refine_def div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P by blast 
qed

lemma div_free_RUN: "\<D>(RUN A) = {}"
proof - 
  have "CHAOS A  \<sqsubseteq>\<^sub>D RUN A"
    by (simp add:CHAOS_def, rule fix_ind, simp_all add: monofunI, subst RUN_unfold, simp) 
  then show ?thesis using divergence_refine_def div_free_CHAOS by blast 
qed

corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF_refine_FD: "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F\<^sub>D DF A"
      and DF_RUN_refine_FD: "DF A  \<sqsubseteq>\<^sub>F\<^sub>D RUN A"
      and CHAOS_DF_refine_FD: "CHAOS A  \<sqsubseteq>\<^sub>F\<^sub>D DF A"
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_CHAOS_refine_FD: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A"
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_refine_FD: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  using div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P[of A] div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P[of A] div_free_DF[of A] div_free_RUN[of A] 
        div_free_CHAOS[of A] 
        leF_leD_imp_leFD[OF DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF_refine_F, of A] leF_leD_imp_leFD[OF DF_RUN_refine_F, of A] 
        leF_leD_imp_leFD[OF CHAOS_DF_refine_F, of A] leF_leD_imp_leFD[OF CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_CHAOS_refine_F, of A] 
        leF_leD_imp_leFD[OF CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_refine_F, of A]
  by (auto simp add:divergence_refine_def) 


lemma traces_CHAOS_sub: "\<T>(CHAOS A) \<subseteq> {s. set s \<subseteq> ev ` A}"
proof(auto)
  fix s sa
  assume "s \<in> \<T> (CHAOS A)" and "sa \<in> set s"
  then show "sa \<in> ev ` A"
    apply (induct s, simp) 
    by (subst (asm) (2) CHAOS_unfold, cases "A={}", auto simp add:T_Ndet T_STOP T_Mprefix)  
qed

lemma traces_RUN_sub: "{s. set s \<subseteq> ev ` A} \<subseteq> \<T>(RUN A)"
proof(auto)
  fix s
  assume "set s \<subseteq> ev ` A"
  then show "s \<in> \<T> (RUN A)"
    by (induct s, simp add: Nil_elem_T) (subst RUN_unfold, auto simp add:T_Mprefix)
qed

corollary RUN_all_tickfree_traces1: "\<T>(RUN A) = {s. set s \<subseteq> ev ` A}" 
      and DF_all_tickfree_traces1: "\<T>(DF A) = {s. set s \<subseteq> ev ` A}" 
      and CHAOS_all_tickfree_traces1: "\<T>(CHAOS A) = {s. set s \<subseteq> ev ` A}"
  using DF_RUN_refine_F[THEN leF_imp_leT, simplified trace_refine_def]
        CHAOS_DF_refine_F[THEN leF_imp_leT,simplified trace_refine_def] 
        traces_CHAOS_sub traces_RUN_sub by blast+

corollary RUN_all_tickfree_traces2: "tickFree s \<Longrightarrow> s \<in> \<T>(RUN UNIV)" 
      and DF_all_tickfree_traces2: "tickFree s \<Longrightarrow> s \<in> \<T>(DF UNIV)" 
      and CHAOS_all_tickfree_trace2: "tickFree s \<Longrightarrow> s \<in> \<T>(CHAOS UNIV)"
    apply(simp_all add:tickFree_def RUN_all_tickfree_traces1 
                       DF_all_tickfree_traces1 CHAOS_all_tickfree_traces1)
  by (metis event_set insertE subsetI)+

lemma traces_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_sub: "\<T>(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<subseteq> {s. front_tickFree s \<and> set s \<subseteq> (ev ` A \<union> {tick})}"
proof(auto simp add:is_processT2_TR)
  fix s sa
  assume "s \<in> \<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)" and "sa \<in> set s" and "sa \<notin> ev ` A"
  then show "sa = tick"
    apply (induct s, simp) 
    by (subst (asm) (2) CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, cases "A={}", auto simp add:T_Ndet T_STOP T_SKIP T_Mprefix)  
qed

lemma traces_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_sub: 
  "{s. front_tickFree s \<and> set s \<subseteq> (ev ` A \<union> {tick})} \<subseteq> \<T>(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A::'a process)"
proof(auto)
  fix s
  assume a:"front_tickFree s" and b:"set s \<subseteq> insert tick (ev ` A)"
  have c:"front_tickFree ((tick::'a event) # s) \<Longrightarrow> s = []" for s
    by (metis butlast.simps(2) butlast_snoc front_tickFree_charn list.distinct(1) tickFree_Cons) 
  with a b show "s \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)"
    apply (induct s, simp add: Nil_elem_T, subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, cases "A={}") 
     apply (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, cases "A={}")
      apply(auto simp add:T_Mprefix T_Mndetprefix write0_def T_SKIP T_Ndet T_STOP)
    apply (metis append_Cons append_Nil front_tickFree_charn front_tickFree_mono)
    by (metis append_Cons append_Nil front_tickFree_mono)
  qed

corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces1: 
                              "\<T>(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = {s. front_tickFree s \<and> set s \<subseteq> (ev ` A \<union> {tick})}" 
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces1: 
                              "\<T>(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = {s. front_tickFree s \<and> set s \<subseteq> (ev ` A \<union> {tick})}"
  using CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_refine_F[THEN leF_imp_leT, simplified trace_refine_def]
        traces_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_sub traces_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_sub by blast+

corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces2: "front_tickFree s \<Longrightarrow> s \<in> \<T>(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)" 
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces2: "front_tickFree s \<Longrightarrow> s \<in> \<T>(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)"
   apply(simp_all add:tickFree_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces1 
                      CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces1)
  by (metis event_set subsetI)+

corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_traces: "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>T P"
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_traces: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>T P"
  apply (simp add:trace_refine_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces2 is_processT2_TR subsetI) 
  by (simp add:trace_refine_def CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces2 is_processT2_TR subsetI) 



lemma deadlock_free_implies_non_terminating: 
  "deadlock_free (P::'a process) \<Longrightarrow> \<forall>s\<in>\<T> P. tickFree s"
  unfolding deadlock_free_def apply(drule leFD_imp_leF, drule leF_imp_leT) unfolding trace_refine_def 
  using DF_all_tickfree_traces1[of "(UNIV::'a set)"] tickFree_def by fastforce 

lemma deadlock_free_v2_is_right: 
  "deadlock_free_v2 (P::'a process) \<longleftrightarrow> (\<forall>s\<in>\<T> P. tickFree s \<longrightarrow> (s, UNIV::'a event set) \<notin> \<F> P)"
proof
  assume a:"deadlock_free_v2 P"
  have "tickFree s \<longrightarrow> (s, UNIV) \<notin> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)" for s::"'a event list"
  proof(induct s)
    case Nil
    then show ?case by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:F_Mndetprefix write0_def F_Mprefix F_Ndet F_SKIP)
  next
    case (Cons a s)
    then show ?case 
      by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:F_Mndetprefix write0_def F_Mprefix F_Ndet F_SKIP)
  qed
  with a show "\<forall>s\<in>\<T> P. tickFree s \<longrightarrow> (s, UNIV) \<notin> \<F> P"
    using deadlock_free_v2_def failure_refine_def by blast
next 
  assume as1:"\<forall>s\<in>\<T> P. tickFree s \<longrightarrow> (s, UNIV) \<notin> \<F> P"
  have as2:"front_tickFree s \<Longrightarrow> (\<exists>aa \<in> UNIV. ev aa \<notin> b) \<Longrightarrow> (s, b) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P (UNIV::'a set))" 
       for s b
  proof(induct s)
    case Nil
    then show ?case
      by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, auto simp add:F_Mndetprefix write0_def F_Mprefix F_Ndet F_SKIP)
  next
    case (Cons hda tla)
    then show ?case 
    proof(simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def fix_def)
      define Y where "Y \<equiv> \<lambda>i. iterate i\<cdot>(\<Lambda> x. (\<sqinter>xa\<in>(UNIV::'a set) \<rightarrow>  x) \<sqinter> SKIP)\<cdot>\<bottom>"
      assume a:"front_tickFree (hda # tla)" and b:"front_tickFree tla \<Longrightarrow> (tla, b) \<in> \<F> (\<Squnion>i. Y i)"
             and c:"\<exists>aa. ev aa \<notin> b"
      from Y_def have cc:"chain Y" by simp
      from b have d:"front_tickFree tla \<Longrightarrow> \<exists>aa\<in>UNIV. ev aa \<notin> b \<Longrightarrow>(tla, b) \<in> \<F> (Y i)" for i 
        using F_LUB[OF cc] limproc_is_thelub[OF cc] by simp
      from Y_def have e:"\<F>(Mndetprefix UNIV (\<lambda>x. Y i) \<sqinter> SKIP) \<subseteq> \<F> (Y (Suc i))" for i by(simp)
      from a have f:"tla \<noteq> [] \<Longrightarrow> hda \<noteq> tick" "front_tickFree tla"
        apply (metis butlast.simps(2) butlast_snoc front_tickFree_charn 
                      list.distinct(1) tickFree_Cons)
        by (metis a append_Cons append_Nil front_tickFree_Nil front_tickFree_mono) 
      have g:"(hda#tla, b) \<in> \<F> (Y (Suc i))" for i
        using f c e[of i] d[of i] 
        by (auto simp: F_Mndetprefix write0_def F_Mprefix Y_def F_Ndet F_SKIP) (metis event.exhaust)+ 
      have h:"(hda#tla, b) \<in> \<F> (Y 0)"
        using NF_ND cc g po_class.chainE proc_ord2a by blast
      from a b c show "(hda#tla, b) \<in> \<F> (\<Squnion>i. Y i)"
        using F_LUB[OF cc] is_ub_thelub[OF cc] 
        by (metis D_LUB_2 cc g limproc_is_thelub po_class.chainE proc_ord2a process_charn) 
    qed   
  qed
  show "deadlock_free_v2 P"
  proof(auto simp add:deadlock_free_v2_def failure_refine_def)
    fix s b
    assume as3:"(s, b) \<in> \<F> P"
    hence a1:"s \<in> \<T> P" "front_tickFree s" 
       using F_T apply blast
      using as3 is_processT2 by blast
    show "(s, b) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)" 
    proof(cases "tickFree s")
      case FT_True:True
      hence a2:"(s, UNIV) \<notin> \<F> P"
        using a1 as1 by blast
      then show ?thesis 
        by (metis FT_True UNIV_I UNIV_eq_I a1(2) as2 as3 emptyE event.exhaust 
                  is_processT6_S1 tickFree_implies_front_tickFree_single) 
    next
      case FT_False: False                                                                 
      then show ?thesis 
        by (meson T_F_spec UNIV_witness a1(2) append_single_T_imp_tickFree 
                  as2 emptyE is_processT5_S7)
    qed 
  qed
qed  

lemma deadlock_free_v2_implies_div_free: "deadlock_free_v2 P \<Longrightarrow> \<D> P = {}"
  by (metis F_T append_single_T_imp_tickFree deadlock_free_v2_is_right ex_in_conv 
            nonTickFree_n_frontTickFree process_charn)

corollary deadlock_free_v2_FD: "deadlock_free_v2 P = DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"
  unfolding deadlock_free_v2_def 
  using deadlock_free_v2_implies_div_free leFD_imp_leF leF_leD_imp_leFD 
        deadlock_free_v2_def divergence_refine_def 
  by fastforce 

lemma all_events_refusal: 
   "(s, {tick} \<union> ev ` (events_of P)) \<in> \<F> P \<Longrightarrow> (s, UNIV::'a event set) \<in> \<F> P"
proof -
  assume a1:"(s, {tick} \<union> ev ` events_of P) \<in> \<F> P"
  { assume "(s, UNIV) \<notin> \<F> P"
    then obtain c where "c \<notin> {tick} \<union> ev ` events_of P \<and> s @ [c] \<in> \<T> P"
      using is_processT5_S1[of s "{tick} \<union> ev ` events_of P" P 
            "UNIV - ({tick} \<union> ev ` events_of P)", simplified] F_T a1 by auto
    hence False by (simp add:events_of_def, cases c) fastforce+
  }  
  with a1 show "(s, UNIV) \<in> \<F> P" by blast 
qed

corollary deadlock_free_v2_is_right_wrt_events:
  "deadlock_free_v2 (P::'a process) \<longleftrightarrow> 
      (\<forall>s\<in>\<T> P. tickFree s \<longrightarrow> (s, {tick} \<union> ev ` (events_of P)) \<notin> \<F> P)"
  unfolding deadlock_free_v2_is_right using all_events_refusal apply auto 
  using is_processT4 by blast 

lemma deadlock_free_is_deadlock_free_v2:
  "deadlock_free P \<Longrightarrow> deadlock_free_v2 P"
  using DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF_refine_FD deadlock_free_def deadlock_free_v2_FD trans_FD by blast 



section \<open>\<^const>\<open>deadlock_free\<close> and \<^const>\<open>deadlock_free_v2\<close> with \<^const>\<open>SKIP\<close> and \<^const>\<open>STOP\<close>\<close>

lemma deadlock_free_v2_SKIP: "deadlock_free_v2 SKIP"
  unfolding deadlock_free_v2_FD by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold) simp
 
lemma non_deadlock_free_SKIP: \<open>\<not> deadlock_free SKIP\<close> 
  by (metis T_SKIP deadlock_free_implies_non_terminating insertCI non_tickFree_tick)

lemma non_deadlock_free_v2_STOP: \<open>\<not> deadlock_free_v2 STOP\<close>
  by (simp add: F_STOP Nil_elem_T deadlock_free_v2_is_right)

lemma non_deadlock_free_STOP: \<open>\<not> deadlock_free STOP\<close>
  using deadlock_free_is_deadlock_free_v2 non_deadlock_free_v2_STOP by blast




end