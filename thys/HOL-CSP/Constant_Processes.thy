(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Constant processes
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

chapter\<open> Constant Processes \<close>

(*<*)
theory     Constant_Processes
  imports    Process
begin 
  (*>*)

section\<open>The Undefined Process: \<^term>\<open>\<bottom>\<close>\<close>

text\<open> This is the key result: @{term "\<bottom>"} --- which we know to exist 
from the process instantiation --- can be explicitly written with its projections.
\<close>

lemma F_BOT : \<open>\<F> \<bottom> = {(s :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, X). ftF s}\<close>
  and D_BOT : \<open>\<D> \<bottom> = {d :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. ftF d}\<close>
  and T_BOT : \<open>\<T> \<bottom> = {s :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. ftF s}\<close>
proof -
  define bot\<^sub>0 :: \<open>('a, 'r) process\<^sub>0\<close> where \<open>bot\<^sub>0 \<equiv> ({(s, X). ftF s}, {d. ftF d})\<close>
  define bot :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>bot \<equiv> process_of_process\<^sub>0 bot\<^sub>0\<close>

  have \<open>is_process bot\<^sub>0\<close>
    unfolding is_process_def bot\<^sub>0_def
    by (simp add: FAILURES_def DIVERGENCES_def)
      (meson front_tickFree_append_iff front_tickFree_dw_closed)
  have F_bot : \<open>\<F> bot = {(s, X). ftF s}\<close>
    by (metis CollectI FAILURES_def Failures.rep_eq \<open>is_process bot\<^sub>0\<close> 
        bot\<^sub>0_def bot_def fst_eqD process_of_process\<^sub>0_inverse)
  have D_bot : \<open>\<D> bot = {d. ftF d}\<close>
    by (metis CollectI DIVERGENCES_def Divergences.rep_eq \<open>is_process bot\<^sub>0\<close>
        bot\<^sub>0_def bot_def process_of_process\<^sub>0_inverse prod.sel(2))
  hence T_bot : \<open>\<T> bot = {s. ftF s}\<close>
    by (metis D_T T_imp_front_tickFree mem_Collect_eq subsetI subset_Un_eq sup.orderE)
  have \<open>bot = \<bottom>\<close>
    by (simp add: eq_bottom_iff le_approx_def Refusals_after_def F_bot D_bot
        min_elems_Collect_ftF_is_Nil)
      (metis D_front_tickFree_subset process_charn)
  with F_bot D_bot T_bot
  show \<open>\<F> \<bottom> = {(s :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, X). ftF s}\<close>
    \<open>\<D> \<bottom> = {d :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. ftF d}\<close>
    \<open>\<T> \<bottom> = {s :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. ftF s}\<close> by simp_all
qed

lemmas BOT_projs = F_BOT D_BOT T_BOT


lemma BOT_iff_Nil_D : \<open>P = \<bottom> \<longleftrightarrow> [] \<in> \<D> P\<close>
proof (rule iffI)
  show \<open>P = \<bottom> \<Longrightarrow> [] \<in> \<D> P\<close> by (simp add: D_BOT)
next
  show \<open>P = \<bottom>\<close> if \<open>[] \<in> \<D> P\<close>
  proof (subst Process_eq_spec_optimized, safe)
    show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> \<bottom>\<close> for s by (simp add: D_BOT D_imp_front_tickFree)
  next
    show \<open>s \<in> \<D> \<bottom> \<Longrightarrow> s \<in> \<D> P\<close> for s
      by (metis \<open>[] \<in> \<D> P\<close> append_Nil process_charn tickFree_Nil)
  next
    show \<open>(s, X) \<in> \<F> P \<Longrightarrow> (s, X) \<in> \<F> \<bottom>\<close> for s X
      using le_approx_lemma_F by blast
  next
    show \<open>\<D> P = \<D> \<bottom> \<Longrightarrow> (s, X) \<in> \<F> \<bottom> \<Longrightarrow> (s, X) \<in> \<F> P\<close> for s X
      using D_BOT F_T T_BOT is_processT8 by blast
  qed
qed

lemma BOT_iff_tick_D : \<open>P = \<bottom> \<longleftrightarrow> (\<exists>r. [\<checkmark>(r)] \<in> \<D> P)\<close>
  by (metis BOT_iff_Nil_D D_BOT front_tickFree_single is_processT9_tick mem_Collect_eq)



section\<open>The SKIP Process\<close>

text \<open>In this new parameterized version, the SKIP process is of course also parameterized.\<close>

lift_definition SKIP :: \<open>'r \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda>r. ({([], X)| X. \<checkmark>(r) \<notin> X} \<union> {(s, X). s = [\<checkmark>(r)]}, {})\<close>
  unfolding is_process_def FAILURES_def DIVERGENCES_def
  by (auto simp add: append_eq_Cons_conv)

abbreviation SKIP_unit :: \<open>'a process\<close> (\<open>Skip\<close>) where \<open>Skip \<equiv> SKIP ()\<close>


lemma F_SKIP :
  \<open>\<F> (SKIP r) = {([], X)| X. \<checkmark>(r) \<notin> X} \<union> {(s, X). s = [\<checkmark>(r)]}\<close>
  by (simp add: FAILURES_def Failures.rep_eq SKIP.rep_eq)

lemma D_SKIP : \<open>\<D> (SKIP r) = {}\<close>
  by (simp add: DIVERGENCES_def Divergences.rep_eq SKIP.rep_eq)

lemma T_SKIP : \<open>\<T> (SKIP r) = {[], [\<checkmark>(r)]}\<close>
  by (auto simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_SKIP)

lemmas SKIP_projs = F_SKIP D_SKIP T_SKIP


lemma inj_SKIP : \<open>inj SKIP\<close>
  by (rule injI, simp add: Process_eq_spec F_SKIP) blast



section\<open> The STOP Process \<close>

lift_definition STOP :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>({(s, X). s = []}, {})\<close>
  unfolding is_process_def FAILURES_def DIVERGENCES_def by simp


lemma F_STOP : \<open>\<F> STOP = {(s, X). s = []}\<close>
  by (simp add: FAILURES_def Failures.rep_eq STOP.rep_eq)

lemma D_STOP : \<open>\<D> STOP = {}\<close>
  by (simp add: DIVERGENCES_def Divergences.rep_eq STOP.rep_eq)

lemma T_STOP : \<open>\<T> STOP = {[]}\<close>
  by (simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_STOP)

lemmas STOP_projs = F_STOP D_STOP T_STOP


lemma STOP_iff_T : \<open>P = STOP \<longleftrightarrow> \<T> P = {[]}\<close>
proof (rule iffI)
  show \<open>P = STOP \<Longrightarrow> \<T> P = {[]}\<close> by (simp add: T_STOP)
next
  assume \<open>\<T> P = {[]}\<close>
  show \<open>P = STOP\<close>
  proof (subst Process_eq_spec, safe)
    show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> STOP\<close> for s
      by (metis D_T \<open>\<T> P = {[]}\<close> front_tickFree_single not_Cons_self
          process_charn self_append_conv2 singletonD tickFree_Nil)
  next
    show \<open>s \<in> \<D> STOP \<Longrightarrow> s \<in> \<D> P\<close> for s by (simp add: D_STOP)
  next
    show \<open>(s, X) \<in> \<F> P \<Longrightarrow> (s, X) \<in> \<F> STOP\<close> for s X
      using F_STOP F_T \<open>\<T> P = {[]}\<close> by blast
  next
    show \<open>(s, X) \<in> \<F> STOP \<Longrightarrow> (s, X) \<in> \<F> P\<close> for s X
      by (metis F_T T_STOP \<open>\<T> P = {[]}\<close> is_processT5_S7 singletonD snoc_eq_iff_butlast)
  qed
qed

(*<*)
end
  (*>*)