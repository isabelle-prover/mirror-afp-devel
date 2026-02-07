(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
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


(*<*)
theory Operational_Semantics_CSP_PTick_Laws
  imports After_CSP_PTick_Laws
    Non_Deterministic_CSP_PTick_Distributivity
    "HOL-CSP_OpSem"
begin
  (*>*)


section \<open>Small Steps Transitions\<close>

subsection \<open>Extension of the After Operator\<close>

subsection \<open>Sequential Composition\<close>

locale AfterExtDuplicated_same_events = AfterExtDuplicated \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>\<beta> :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> 


sublocale AfterExtDuplicated_same_events \<subseteq> AfterDuplicated_same_events .
    \<comment>\<open>Recovering @{thm [source] AfterDuplicated_same_events.After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k}\<close>


context AfterExtDuplicated_same_events
begin 

notation After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<alpha>.After (infixl \<open>after\<^sub>\<alpha>\<close> 86)
notation After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<beta>.After (infixl \<open>after\<^sub>\<beta>\<close> 86)
notation After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<alpha>.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k (infixl \<open>after\<^sub>\<checkmark>\<^sub>\<alpha>\<close> 86)
notation After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<beta>.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k (infixl \<open>after\<^sub>\<checkmark>\<^sub>\<beta>\<close> 86)


lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : 
  \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<checkmark>\<^sub>\<beta> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) r
            | ev a \<Rightarrow>
      if \<forall>r. \<checkmark>(r) \<in> P\<^sup>0 \<longrightarrow> ev a \<notin> (Q r)\<^sup>0
    then   if ev a \<in> P\<^sup>0
         then P after\<^sub>\<checkmark>\<^sub>\<alpha> ev a \<^bold>;\<^sub>\<checkmark> Q else \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a
         else   if ev a \<in> P\<^sup>0
              then (P after\<^sub>\<checkmark>\<^sub>\<alpha> ev a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter>
                   (\<sqinter>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0 \<and> ev a \<in> (Q r)\<^sup>0}. Q r after\<^sub>\<checkmark>\<^sub>\<beta> ev a)
              else \<sqinter>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0 \<and> ev a \<in> (Q r)\<^sup>0}. Q r after\<^sub>\<checkmark>\<^sub>\<beta> ev a)\<close>
  by (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<beta>.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<alpha>.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

end



subsubsection \<open>Synchronization Product\<close>

locale AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale = Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale tick_join +
  AfterExt\<^sub>l\<^sub>h\<^sub>s : AfterExt \<Psi>\<^sub>l\<^sub>h\<^sub>s \<Omega>\<^sub>l\<^sub>h\<^sub>s +
  AfterExt\<^sub>r\<^sub>h\<^sub>s : AfterExt \<Psi>\<^sub>r\<^sub>h\<^sub>s \<Omega>\<^sub>r\<^sub>h\<^sub>s +
  AfterExt\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : AfterExt \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  for tick_join :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close>
    and \<Psi>\<^sub>l\<^sub>h\<^sub>s :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>l\<^sub>h\<^sub>s :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>r\<^sub>h\<^sub>s :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>r\<^sub>h\<^sub>s :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>[('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>[('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 't] \<Rightarrow> ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
begin

sublocale After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale tick_join \<Psi>\<^sub>l\<^sub>h\<^sub>s \<Psi>\<^sub>r\<^sub>h\<^sub>s \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by unfold_locales

sublocale AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym :
  AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>s r. tick_join r s\<close> \<Psi>\<^sub>r\<^sub>h\<^sub>s \<Omega>\<^sub>r\<^sub>h\<^sub>s \<Psi>\<^sub>l\<^sub>h\<^sub>s \<Omega>\<^sub>l\<^sub>h\<^sub>s \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  by unfold_locales

(*
notation AfterExt\<^sub>l\<^sub>h\<^sub>s.After (infixl \<open>after\<^sub>l\<^sub>h\<^sub>s\<close> 86)
notation AfterExt\<^sub>r\<^sub>h\<^sub>s.After (infixl \<open>after\<^sub>r\<^sub>h\<^sub>s\<close> 86)
notation AfterExt\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After (infixl \<open>after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> 86)
*)
notation AfterExt\<^sub>l\<^sub>h\<^sub>s.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k (infixl \<open>after\<^sub>\<checkmark>\<^sub>l\<^sub>h\<^sub>s\<close> 86)
notation AfterExt\<^sub>r\<^sub>h\<^sub>s.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k (infixl \<open>after\<^sub>\<checkmark>\<^sub>r\<^sub>h\<^sub>s\<close> 86)
notation AfterExt\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k (infixl \<open>after\<^sub>\<checkmark>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> 86)
  (* 
definition \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v :: \<open>('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 't \<Rightarrow> ('a, 's \<times> 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>\<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v P s_r \<equiv> TickSwap (\<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (TickSwap P) (case s_r of (s, r) \<Rightarrow> (r, s)))\<close>

sublocale AfterExt\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v : AfterExt \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v .

notation AfterExt\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k (infixl \<open>after\<^sub>\<checkmark>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v\<close> 86)

sublocale AfterExt\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kDuplicated : AfterExtDuplicated \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v .



lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_TickSwap :
  \<open>TickSwap P after\<^sub>\<checkmark>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v e =
   (case e of \<checkmark>(s_r) \<Rightarrow> \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v (TickSwap P) s_r
              | ev a \<Rightarrow>  if P = \<bottom> then \<bottom>
                       else   if ev a \<in> P\<^sup>0
                            then TickSwap (P after\<^sub>\<checkmark>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ev a)
                            else \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v (TickSwap P) a)\<close>
  by (simp add: AfterExt\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def AfterExt\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
      After.After_BOT split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      (simp add: After_TickSwap)


lemma TickSwap_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k [simp] :
  \<open>TickSwap (P after\<^sub>\<checkmark>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k e) = TickSwap P after\<^sub>\<checkmark>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v tick_swap e\<close>
  by (cases e) (auto simp add: AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v_def)

lemma TickSwap_is_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff [simp] :
  \<open>TickSwap P = (Q after\<^sub>\<checkmark>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k e) \<longleftrightarrow> P = TickSwap Q after\<^sub>\<checkmark>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>r\<^sub>e\<^sub>v tick_swap e\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)
 *)

theorem After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: 
  \<open>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>\<checkmark>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k e =
   (case e of \<checkmark>(r_s) \<Rightarrow> \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) r_s
            |  ev a \<Rightarrow> 
     if P = \<bottom> \<or> Q = \<bottom> then \<bottom>
    else   if ev a \<in> P\<^sup>0 \<and> ev a \<in> Q\<^sup>0
         then   if a \<in> S then P after\<^sub>\<checkmark>\<^sub>l\<^sub>h\<^sub>s ev a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q after\<^sub>\<checkmark>\<^sub>r\<^sub>h\<^sub>s ev a
              else (P after\<^sub>\<checkmark>\<^sub>l\<^sub>h\<^sub>s ev a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<sqinter> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q after\<^sub>\<checkmark>\<^sub>r\<^sub>h\<^sub>s ev a)
         else   if ev a \<in> P\<^sup>0 \<and> a \<notin> S then P after\<^sub>\<checkmark>\<^sub>l\<^sub>h\<^sub>s ev a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q
              else   if ev a \<in> Q\<^sup>0 \<and> a \<notin> S then P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q after\<^sub>\<checkmark>\<^sub>r\<^sub>h\<^sub>s ev a
                   else \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) a)\<close>
  by (cases e) (simp_all add: AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

end



subsection \<open>Generic Operational Semantics as Locales\<close>

subsubsection \<open>Sequential Composition\<close>

locale OpSemTransitionsDuplicated_same_events =
  OpSemTransitionsDuplicated \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> \<tau>_trans\<^sub>\<alpha> \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta> \<tau>_trans\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<alpha>\<leadsto>\<^sub>\<tau>\<close> 50)
    and \<Psi>\<^sub>\<beta> :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<beta> :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<beta>\<leadsto>\<^sub>\<tau>\<close> 50)

sublocale OpSemTransitionsDuplicated_same_events \<subseteq> AfterExtDuplicated_same_events
  by unfold_locales 

context OpSemTransitionsDuplicated_same_events begin

notation OpSemTransitions\<^sub>\<alpha>.ev_trans   (\<open>_ \<^sub>\<alpha>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>\<alpha>.tick_trans (\<open>_ \<^sub>\<alpha>\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>\<beta>.ev_trans   (\<open>_ \<^sub>\<beta>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>\<beta>.tick_trans (\<open>_ \<^sub>\<beta>\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)

lemma \<tau>_trans_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR: \<open>P \<^bold>;\<^sub>\<checkmark> Q \<^sub>\<beta>\<leadsto>\<^sub>\<tau> Q'\<close> if \<open>P \<^sub>\<alpha>\<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P'\<close> and \<open>Q r \<^sub>\<beta>\<leadsto>\<^sub>\<tau> Q'\<close>
proof -
  from that(1) have \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r\<close> 
    by (meson OpSemTransitions\<^sub>\<alpha>.exists_tick_trans_is_initial_tick initial_tick_iff_FD_SKIP)
  with FD_iff_eq_Ndet have \<open>P = P \<sqinter> SKIP r\<close> ..
  hence \<open>P \<^bold>;\<^sub>\<checkmark> Q = (P \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> (SKIP r \<^bold>;\<^sub>\<checkmark> Q)\<close> 
    by (metis Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_right)
  also have \<open>\<dots> = (P \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> Q r\<close> by simp
  also have \<open>\<dots> \<^sub>\<beta>\<leadsto>\<^sub>\<tau> Q r\<close> by (simp add: OpSemTransitions\<^sub>\<beta>.\<tau>_trans_NdetR)
  finally show \<open>P \<^bold>;\<^sub>\<checkmark> Q \<^sub>\<beta>\<leadsto>\<^sub>\<tau> Q'\<close> by (rule OpSemTransitions\<^sub>\<beta>.\<tau>_trans_transitivity) (fact that(2))
qed

lemma \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> Q r \<^sub>\<beta>\<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q \<^sub>\<beta>\<leadsto>\<^bsub>e\<^esub> Q'\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  by (meson OpSemTransitions\<^sub>\<beta>.\<tau>_trans_eq OpSemTransitions\<^sub>\<beta>.\<tau>_trans_ev_trans
            \<tau>_trans_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR OpSemTransitions\<^sub>\<alpha>.exists_tick_trans_is_initial_tick)


end



locale OpSemTransitionsSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k =
  OpSemTransitionsDuplicated_same_events \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> \<tau>_trans\<^sub>\<alpha> \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta> \<tau>_trans\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<alpha>\<leadsto>\<^sub>\<tau>\<close> 50)
    and \<Psi>\<^sub>\<beta> :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<beta> :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<beta>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL : \<open>P \<^sub>\<alpha>\<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q \<^sub>\<beta>\<leadsto>\<^sub>\<tau> P' \<^bold>;\<^sub>\<checkmark> Q\<close>
begin

lemma ev_trans_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL: \<open>P \<^sub>\<alpha>\<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q \<^sub>\<beta>\<leadsto>\<^bsub>e\<^esub> P' \<^bold>;\<^sub>\<checkmark> Q\<close>
  by (cases \<open>P = \<bottom>\<close>, solves \<open>simp add: OpSemTransitions\<^sub>\<beta>.BOT_ev_trans_anything\<close>)
    (auto simp add: OpSemTransitions\<^sub>\<beta>.ev_trans_def After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
                    OpSemTransitions\<^sub>\<alpha>.ev_trans_def
             intro: OpSemTransitions\<^sub>\<beta>.\<tau>_trans_NdetL OpSemTransitions\<^sub>\<beta>.\<tau>_trans_transitivity \<tau>_trans_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL)

lemmas Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules = \<tau>_trans_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL ev_trans_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL \<tau>_trans_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR


end


subsubsection \<open>Synchronization Product\<close>

locale OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale = Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>(\<otimes>\<checkmark>)\<close> +
  OpSemTransitions\<^sub>l\<^sub>h\<^sub>s  : OpSemTransitions \<Psi>\<^sub>l\<^sub>h\<^sub>s   \<Omega>\<^sub>l\<^sub>h\<^sub>s   \<open>(\<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau>)\<close>  +
  OpSemTransitions\<^sub>r\<^sub>h\<^sub>s  : OpSemTransitions \<Psi>\<^sub>r\<^sub>h\<^sub>s   \<Omega>\<^sub>r\<^sub>h\<^sub>s   \<open>(\<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau>)\<close>  +
  OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : OpSemTransitions \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>(\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau>)\<close>
  for tick_join :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close> (infixl \<open>\<otimes>\<checkmark>\<close> 100)
    and \<Psi>\<^sub>l\<^sub>h\<^sub>s :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>l\<^sub>h\<^sub>s :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>l\<^sub>h\<^sub>s :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau>\<close> 50)
    and \<Psi>\<^sub>r\<^sub>h\<^sub>s :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>r\<^sub>h\<^sub>s :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>r\<^sub>h\<^sub>s :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau>\<close> 50)
    and \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>[('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>[('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 't] \<Rightarrow> ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>[('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL : \<open>P \<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q\<close>
    and \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR : \<open>Q \<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau> Q' \<Longrightarrow> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q'\<close>
begin

sublocale AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale by unfold_locales


sublocale OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym :
  OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale
  \<open>\<lambda>s r. r \<otimes>\<checkmark> s\<close> \<Psi>\<^sub>r\<^sub>h\<^sub>s \<Omega>\<^sub>r\<^sub>h\<^sub>s \<open>(\<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau>)\<close> \<Psi>\<^sub>l\<^sub>h\<^sub>s \<Omega>\<^sub>l\<^sub>h\<^sub>s \<open>(\<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau>)\<close> \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>(\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau>)\<close>
proof unfold_locales
  show \<open>P \<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m Q\<close> for P P' A Q
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR)
next
  show \<open>Q \<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^sub>\<tau> Q' \<Longrightarrow> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m Q'\<close> for Q Q' A P
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL)
qed


notation OpSemTransitions\<^sub>l\<^sub>h\<^sub>s.ev_trans (\<open>_ \<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>l\<^sub>h\<^sub>s.tick_trans (\<open>_ \<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>r\<^sub>h\<^sub>s.ev_trans (\<open>_ \<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>r\<^sub>h\<^sub>s.tick_trans (\<open>_ \<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.ev_trans (\<open>_ \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.tick_trans (\<open>_ \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)


text \<open>
We do not need the assumptions @{thm [source] \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR}
for the three following lemmas.
\<close>

lemma \<tau>_trans_SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL :
  \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q\<close> if \<open>P \<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P'\<close>
proof -
  from that have \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r\<close>
    by (simp add: OpSemTransitions\<^sub>l\<^sub>h\<^sub>s.tick_trans_def initial_tick_iff_FD_SKIP)
  with FD_iff_eq_Ndet have \<open>P = P \<sqinter> SKIP r\<close> ..
  hence \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q = (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<sqinter> (SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_right)
  also have \<open>\<dots> \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q\<close>
    by (fact OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.\<tau>_trans_NdetR)
  finally show \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q\<close> .
qed

lemma \<tau>_trans_SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR :
  \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s\<close> if \<open>Q \<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^sub>\<checkmark>\<^bsub>s\<^esub> Q'\<close>
proof -
  from that have \<open>Q \<sqsubseteq>\<^sub>F\<^sub>D SKIP s\<close>
    by (simp add: OpSemTransitions\<^sub>r\<^sub>h\<^sub>s.tick_trans_def initial_tick_iff_FD_SKIP)
  with FD_iff_eq_Ndet have \<open>Q = Q \<sqinter> SKIP s\<close> ..
  hence \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q = (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<sqinter> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s)\<close>
    by (metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_left)
  also have \<open>\<dots> \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s\<close>
    by (fact OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.\<tau>_trans_NdetR)
  finally show \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<tau> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s\<close> .
qed


lemma tick_trans_SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP:
  \<open>r \<otimes>\<checkmark> s = Some r_s \<Longrightarrow> SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^sub>\<checkmark>\<^bsub>r_s\<^esub> \<Omega>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (SKIP r_s) r_s\<close>
  by (simp add: OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.SKIP_trans_tick_\<Omega>_SKIP)


lemma ev_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL :
  \<open>a \<notin> A \<Longrightarrow> P \<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^bsub>a\<^esub> P' \<Longrightarrow> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^bsub>a\<^esub> P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q\<close>
  by (auto simp add: OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.ev_trans_def After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
                     initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k OpSemTransitions\<^sub>l\<^sub>h\<^sub>s.ev_trans_def
              intro: OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.BOT_\<tau>_trans_anything OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.\<tau>_trans_NdetL
                     OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.\<tau>_trans_transitivity \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL)


lemma ev_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR :
  \<open>a \<notin> A \<Longrightarrow> Q \<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^bsub>a\<^esub> Q' \<Longrightarrow> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^bsub>a\<^esub> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q'\<close>
  by (auto simp add: OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.ev_trans_def After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
                     initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k OpSemTransitions\<^sub>r\<^sub>h\<^sub>s.ev_trans_def
              intro: OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.BOT_\<tau>_trans_anything OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.\<tau>_trans_NdetR
                     OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.\<tau>_trans_transitivity \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR)

lemma ev_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kLR :
  \<open>a \<in> A \<Longrightarrow> P \<^sub>l\<^sub>h\<^sub>s\<leadsto>\<^bsub>a\<^esub> P' \<Longrightarrow> Q \<^sub>r\<^sub>h\<^sub>s\<leadsto>\<^bsub>a\<^esub> Q' \<Longrightarrow> P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<leadsto>\<^bsub>a\<^esub> P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q'\<close>
  by (auto simp add: OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.ev_trans_def OpSemTransitions\<^sub>l\<^sub>h\<^sub>s.ev_trans_def
                     OpSemTransitions\<^sub>r\<^sub>h\<^sub>s.ev_trans_def After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
              intro: OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.BOT_\<tau>_trans_anything
                     OpSemTransitions\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.\<tau>_trans_transitivity
                     \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR)


lemmas Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules = \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL \<tau>_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR
  ev_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL ev_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR
  ev_trans_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kLR
  \<tau>_trans_SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kL \<tau>_trans_SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kR
  tick_trans_SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP

end



(*<*)
end
  (*>*)
