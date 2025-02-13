(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Deadlock Results
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

section\<open> Deadlock Results \<close>

(*<*)
theory  OpSem_Deadlock_Results
  imports After_Trace_Operator
begin
(*>*)


lemma initial_ev_imp_in_events_of: \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> a \<in> \<alpha>(P)\<close>
  by (meson AfterExt.events_of_iff_reachable_ev AfterExt.initial_ev_reachable)

lemma initial_tick_imp_in_ticks_of: \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> r \<in> \<checkmark>s(P)\<close>
  by (meson AfterExt.initial_tick_reachable AfterExt.ticks_of_iff_reachable_tick)

lemma \<open>UNIV \<in> \<R> P \<longleftrightarrow> P \<sqsubseteq>\<^sub>F STOP\<close>
  unfolding failure_refine_def
  apply (simp add: D_STOP F_STOP Refusals_iff)
  using is_processT4 by blast

lemma no_events_of_if_at_most_initial_tick: \<open>P\<^sup>0 \<subseteq> range tick \<Longrightarrow> \<alpha>(P) = {}\<close>
  using empty_ev_initials_iff_empty_events_of by fast

lemma deadlock_free_initial_evE:
  \<open>deadlock_free P \<Longrightarrow> (\<And>a. ev a \<in> P\<^sup>0 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  using empty_ev_initials_iff_empty_events_of
        nonempty_events_of_if_deadlock_free by fastforce


context AfterExt
begin

text \<open>As we said earlier, @{const [source] After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e} allows us to obtain some 
      very powerful results about \<^const>\<open>deadlock_free\<close> and \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>.\<close>

subsection \<open>Preliminaries and induction Rules\<close>

context fixes P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> begin

lemma initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_subset_events_of:
  \<open>(P after\<^sub>\<T> t)\<^sup>0 \<subseteq> ev ` \<alpha>(P)\<close> if \<open>non_terminating P\<close> \<open>t \<in> \<T> P\<close>
proof -
  have \<open>tF t \<Longrightarrow> ev a \<in> (P after\<^sub>\<T> t)\<^sup>0 \<Longrightarrow> reachable_ev P a\<close> for a
    using reachable_ev_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T that(2) by blast
  also have \<open>tF t \<and> range tick \<inter> (P after\<^sub>\<T> t)\<^sup>0 = {}\<close>
    by (simp add: disjoint_iff image_iff)
       (metis T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq initials_def mem_Collect_eq non_terminating_is_right
              non_tickFree_tick that(1) that(2) tickFree_append_iff)
  ultimately show \<open>(P after\<^sub>\<T> t)\<^sup>0 \<subseteq> ev ` \<alpha>(P)\<close>
    by (simp add: subset_iff image_iff disjoint_iff)
       (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust events_of_iff_reachable_ev)
qed

end



text \<open>With the next result, the general idea appears: instead of doing an induction only
      on the process \<^term>\<open>P\<close> we are interested in, we include a quantification over all
      the processes than can be reached from \<^term>\<open>P\<close> after some trace of \<^term>\<open>P\<close>.\<close>

theorem After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_fix_ind [consumes 2, case_names cont step]:
    fixes ref :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f\<close> 60)
  assumes adm_ref : \<open>\<And>u v. cont (u :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow> monofun v
                            \<Longrightarrow> adm (\<lambda>x. u x \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f v x)\<close>
      and BOT_le_ref : \<open>\<And>Q. \<bottom> \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f Q\<close>
      and cont_f : \<open>cont f\<close>
      and hyp : \<open>\<And>s x. \<forall>Q \<in> {Q. \<exists>s \<in> \<T> P. g s Q \<and> Q = P after\<^sub>\<T> s}. x \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f Q \<Longrightarrow>
                       s \<in> \<T> P \<Longrightarrow> g s (P after\<^sub>\<T> s) \<Longrightarrow> f x \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f P after\<^sub>\<T> s\<close>
  shows \<open>\<forall>Q \<in> {Q. \<exists>s \<in> \<T> P. g s Q \<and> Q = P after\<^sub>\<T> s}. (\<mu> X. f X) \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f Q\<close>
  apply (induct rule: fix_ind)
    apply (solves \<open>simp add: adm_ref monofunI\<close>)
   apply (solves \<open>simp add: BOT_le_ref\<close>)
  using hyp cont_f by auto


lemma After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_fix_ind_F [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}; cont f;
    \<And>t x. \<lbrakk>\<forall>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}. x \<sqsubseteq>\<^sub>F Q;
           t \<in> \<T> P; g t (P after\<^sub>\<T> t)\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^sub>F P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>F Q\<close>
  and After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_fix_ind_D [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}; cont f;
    \<And>t x. \<lbrakk>\<forall>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}. x \<sqsubseteq>\<^sub>D Q;
           t \<in> \<T> P; g t (P after\<^sub>\<T> t)\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^sub>D P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>D Q\<close>
  and After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_fix_ind_T [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}; cont f;
    \<And>t x. \<lbrakk>\<forall>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}. x \<sqsubseteq>\<^sub>T Q;
           t \<in> \<T> P; g t (P after\<^sub>\<T> t)\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^sub>T P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>T Q\<close>
  and After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_fix_ind_FD [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}; cont f;
    \<And>t x. \<lbrakk>\<forall>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}. x \<sqsubseteq>\<^sub>F\<^sub>D Q;
           t \<in> \<T> P; g t (P after\<^sub>\<T> t)\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^sub>F\<^sub>D P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  and After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_fix_ind_DT [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}; cont f;
    \<And>t x. \<lbrakk>\<forall>Q \<in> {Q. \<exists>t \<in> \<T> P. g t Q \<and> Q = P after\<^sub>\<T> t}. x \<sqsubseteq>\<^sub>D\<^sub>T Q;
           t \<in> \<T> P; g t (P after\<^sub>\<T> t)\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^sub>D\<^sub>T P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (all \<open>rule After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_fix_ind[rule_format]\<close>) simp_all


corollary reachable_processes_fix_ind [consumes 3, case_names cont step]: 
  \<open>\<lbrakk>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P; 
    \<And>u v. \<lbrakk>cont (u :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k); monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. ref (u x) (v x));
    \<And>Q. ref \<bottom> Q;
    cont f;
    \<And>t x. \<lbrakk>\<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. ref x Q; t \<in> \<T> P; tickFree t\<rbrakk> \<Longrightarrow> ref (f x) (P after\<^sub>\<T> t)\<rbrakk> \<Longrightarrow>
    ref (\<mu> x. f x) Q\<close>
  by (simp add: reachable_processes_is,
      rule After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_fix_ind[where g = \<open>\<lambda>s Q. tickFree s\<close>, simplified, rule_format]; simp)

corollary reachable_processes_fix_ind_F [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P; cont f; 
    \<And>t x. \<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>F Q \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> tickFree t \<Longrightarrow> f x \<sqsubseteq>\<^sub>F P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>F Q\<close>
  and reachable_processes_fix_ind_D [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P; cont f; 
    \<And>t x. \<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>D Q \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> tickFree t \<Longrightarrow> f x \<sqsubseteq>\<^sub>D P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>D Q\<close>
  and reachable_processes_fix_ind_T [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P; cont f; 
    \<And>t x. \<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>T Q \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> tickFree t \<Longrightarrow> f x \<sqsubseteq>\<^sub>T P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>T Q\<close>
  and reachable_processes_fix_ind_FD [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P; cont f; 
    \<And>t x. \<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> tickFree t \<Longrightarrow> f x \<sqsubseteq>\<^sub>F\<^sub>D P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  and reachable_processes_fix_ind_DT [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P; cont f; 
    \<And>t x. \<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> tickFree t \<Longrightarrow> f x \<sqsubseteq>\<^sub>D\<^sub>T P after\<^sub>\<T> t\<rbrakk> \<Longrightarrow>
    (\<mu> X. f X) \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (all \<open>rule reachable_processes_fix_ind\<close>) simp_all



subsection \<open>New idea: \<^const>\<open>After\<close> induct instead of \<^const>\<open>After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e\<close>\<close>

\<comment>\<open>TODO: find something\<close>



subsection \<open>New results on \<^term>\<open>\<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c\<close>\<close>

lemma reachable_processes_FD_refinement_propagation_induct [consumes 1, case_names cont base step]:
  \<comment>\<open>May be generalized or duplicated to other refinements.\<close>
  assumes reachable : \<open>(Q :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
      and cont_f : \<open>cont f\<close>
      and base : \<open>(\<mu> x. f x) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
      and step : \<open>\<And>a. a \<in> \<alpha>(P) \<Longrightarrow> f (\<mu> x. f x) after a = (\<mu> x. f x)\<close>
    shows \<open>(\<mu> x. f x) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
proof (use reachable in \<open>induct rule: reachable_processes.induct\<close>)
  case reachable_self
  show \<open>(\<mu> x. f x) \<sqsubseteq>\<^sub>F\<^sub>D P\<close> by (fact base)
next
  case (reachable_after Q a)
  from reachable_after.hyps(2) have \<open>f (\<mu> x. f x) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
    by (subst (asm) cont_process_rec[OF refl cont_f])
  hence  * : \<open>f (\<mu> x. f x) after a \<sqsubseteq>\<^sub>F\<^sub>D Q after a\<close>
    by (simp add: mono_After_FD reachable_after.hyps(3))
  from reachable_after.hyps(1, 3) have \<open>a \<in> \<alpha>(P)\<close>
    using events_of_reachable_processes_subset initial_ev_imp_in_events_of by (metis in_mono)
  hence ** : \<open>f (\<mu> x. f x) after a = (\<mu> x. f x)\<close> by (fact local.step)
  from "*"[unfolded "**"] show \<open>(\<mu> x. f x) \<sqsubseteq>\<^sub>F\<^sub>D Q after a\<close> .
qed


theorem \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c_fix_ind [consumes 3, case_names cont step]:
    fixes ref :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f\<close> 60)
  assumes reachable : \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
      and adm_ref : \<open>\<And>u v. cont (u :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow> monofun v
                            \<Longrightarrow> adm (\<lambda>x. u x \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f v x)\<close>
      and BOT_le_ref : \<open>\<And>Q. \<bottom> \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f Q\<close>
      and cont_f : \<open>cont f\<close>
      and hyp : \<open>\<And>x. \<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f Q \<Longrightarrow> \<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. f x \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f Q\<close>
    shows \<open>(\<mu> X. f X) \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f Q\<close>
proof -
  have \<open>\<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. (\<mu> X. f X) \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f Q\<close>
    apply (induct rule: fix_ind)
      apply (solves \<open>simp add: adm_ref monofunI\<close>)
     apply (solves \<open>simp add: BOT_le_ref\<close>)
    using hyp cont_f by auto
  with reachable show \<open>(\<mu> X. f X) \<sqsubseteq>\<^sub>r\<^sub>e\<^sub>f Q\<close> by blast
qed

lemma \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c_fix_ind_FD [consumes 1, case_names cont step]:
  \<open>\<lbrakk>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P; cont f; \<And>x Q. \<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> f x \<sqsubseteq>\<^sub>F\<^sub>D Q\<rbrakk>
   \<Longrightarrow> (\<mu> X. f X) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (rule \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c_fix_ind) auto
    
 

\<comment>\<open>See what else we can add.\<close>


subsection \<open>Induction Proofs\<close>


subsubsection \<open>Generalizations\<close>

\<comment>\<open>Again, new approach\<close>

\<comment>\<open>TODO: reorganize this file\<close>


(* put this somewhere else, maybe useful *)

lemma \<open>Mprefix A P = Mprefix B Q \<Longrightarrow> A = B\<close>
  by (drule arg_cong[where f = initials]) (auto simp add: initials_Mprefix)    

lemma \<open>Mndetprefix A P = Mprefix B Q \<Longrightarrow> A = B\<close>
  by (drule arg_cong[where f = initials]) (auto simp add: initials_Mprefix initials_Mndetprefix)

lemma \<open>Mndetprefix A P = Mndetprefix B Q \<Longrightarrow> A = B\<close>
  by (drule arg_cong[where f = initials]) (auto simp add: initials_Mndetprefix)

(* end of block to move *)


print_context

lemma superset_initials_restriction_Mndetprefix_FD:
  \<open>\<sqinter>a \<in> B \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  if \<open>\<sqinter>a \<in> A \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> and \<open>{e. ev e \<in> Q\<^sup>0} \<subseteq> B\<close> and \<open>A \<noteq> {} \<or> B = {}\<close>
  supply that' = that(1)[unfolded failure_divergence_refine_def failure_refine_def divergence_refine_def]
proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, safe)
  from that'[THEN conjunct2] that(2)
  show \<open>s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> (Mndetprefix B P)\<close> for s
    by (simp add: D_Mndetprefix write0_def D_Mprefix subset_iff split: if_split_asm)
       (metis initials_memI D_T empty_iff)
next
  from that have that'' : \<open>Q\<^sup>0 \<subseteq> ev ` A\<close>
    using anti_mono_initials_FD initials_Mndetprefix by blast
  fix s X
  assume * : \<open>(s, X) \<in> \<F> Q\<close>
  with set_mp[OF that'[THEN conjunct1] this]
  consider \<open>s = []\<close> | e s' where \<open>s = ev e # s'\<close> \<open>ev e \<in> Q\<^sup>0\<close>
    by (simp add: F_Mndetprefix write0_def F_Mprefix split: if_split_asm)
       (metis initials_memI F_T)
  thus \<open>(s, X) \<in> \<F> (Mndetprefix B P)\<close>
  proof cases
    assume \<open>s = []\<close>
    hence \<open>([], X \<union> (- Q\<^sup>0)) \<in> \<F> Q\<close>
      by (metis "*" ComplD initials_memI is_processT5_S7' self_append_conv2)
    from set_mp[OF that'[THEN conjunct1] this] that'' that(2, 3)
    show \<open>(s, X) \<in> \<F> (Mndetprefix B P)\<close>
      by (simp add: \<open>s = []\<close> F_Mndetprefix write0_def F_Mprefix split: if_split_asm) blast
  next
    fix e s' assume \<open>s = ev e # s'\<close> \<open>ev e \<in> Q\<^sup>0\<close>
    with set_mp[OF that'[THEN conjunct1] "*"] that(2)
    show \<open>(s, X) \<in> \<F> (Mndetprefix B P)\<close>
      by (simp add: F_Mndetprefix write0_def F_Mprefix subset_iff split: if_split_asm) blast
  qed
qed

corollary initials_restriction_Mndetprefix_FD:
  \<open>\<sqinter>a \<in> A \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> \<sqinter>a \<in> {e. ev e \<in> Q\<^sup>0} \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (cases \<open>A = {}\<close>, simp add: STOP_FD_iff)
     (simp add: superset_initials_restriction_Mndetprefix_FD)

corollary events_of_restriction_Mndetprefix_FD:
  \<open>\<sqinter>a \<in> A \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D (Q :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow> \<sqinter>a \<in> \<alpha>(Q) \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (cases \<open>A = {}\<close>, simp add: STOP_FD_iff)
     (erule superset_initials_restriction_Mndetprefix_FD,
      simp_all add: subset_iff initial_ev_imp_in_events_of)



lemma superset_initials_restriction_Mprefix_FD:
  \<open>\<box>a \<in> B \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
   if \<open>\<box>a \<in> A \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> and \<open>{e. ev e \<in> Q\<^sup>0} \<subseteq> B\<close>
  and \<open>B \<subseteq> A\<close> \<comment>\<open>Stronger assumption than with \<^const>\<open>Mndetprefix\<close>.\<close>
  supply that' = that(1)[unfolded failure_divergence_refine_def failure_refine_def divergence_refine_def]
proof (unfold failure_divergence_refine_def failure_refine_def divergence_refine_def, safe)
  from that'[THEN conjunct2] that(2)
  show \<open>s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> (Mprefix B P)\<close> for s
    by (simp add: D_Mprefix subset_iff image_iff)
       (metis initials_memI D_T)
next
  from that have that'' : \<open>Q\<^sup>0 \<subseteq> ev ` A\<close>
    using anti_mono_initials_FD initials_Mprefix by blast
  fix s X
  assume * : \<open>(s, X) \<in> \<F> Q\<close>
  with set_mp[OF that'[THEN conjunct1] this]
  consider \<open>s = []\<close> | \<open>\<exists>e s'. s = ev e # s' \<and> ev e \<in> Q\<^sup>0\<close>
    by (simp add: F_Mprefix) (metis initials_memI F_T)
  thus \<open>(s, X) \<in> \<F> (Mprefix B P)\<close>
  proof cases
    assume \<open>s = []\<close>
    hence \<open>([], X \<union> (- Q\<^sup>0)) \<in> \<F> Q\<close>
      by (metis "*" ComplD initials_memI is_processT5_S7' self_append_conv2)
    from set_mp[OF that'[THEN conjunct1] this] that'' that(2, 3)
    show \<open>(s, X) \<in> \<F> (Mprefix B P)\<close> by (simp add: \<open>s = []\<close> F_Mprefix) blast
  next
    assume \<open>\<exists>e s'. s = ev e # s' \<and> ev e \<in> Q\<^sup>0\<close>
    with set_mp[OF that'[THEN conjunct1] "*"] that(2)
    show \<open>(s, X) \<in> \<F> (Mprefix B P)\<close> by (auto simp add: F_Mprefix image_iff)
  qed
qed

corollary initials_restriction_Mprefix_FD:
  \<open>{e. ev e \<in> Q\<^sup>0} \<subseteq> A \<Longrightarrow> \<box>a \<in> A \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow>
   \<box>a \<in> {e. ev e \<in> Q\<^sup>0} \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (erule superset_initials_restriction_Mprefix_FD; simp)
 
corollary events_of_restriction_Mprefix_FD:
  \<open>\<alpha>(Q) \<subseteq> A \<Longrightarrow> \<box>a \<in> A \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D (Q :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow>
   \<box>a \<in> \<alpha>(Q) \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (erule superset_initials_restriction_Mprefix_FD,
      simp add: subset_iff initial_ev_imp_in_events_of)



\<comment>\<open>This is much better with \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close> refinement.\<close>
lemma superset_initials_restriction_Mprefix_DT:
  \<open>\<box>a \<in> B \<rightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q\<close> if \<open>\<box>a \<in> A \<rightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q\<close> and \<open>{e. ev e \<in> Q\<^sup>0} \<subseteq> B\<close>
  supply that' = that(1)[unfolded trace_divergence_refine_def
                                  trace_refine_def divergence_refine_def]
proof (unfold trace_divergence_refine_def trace_divergence_refine_def
              trace_refine_def divergence_refine_def, safe)
  from that'[THEN conjunct2] that(2)
  show \<open>s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> (Mprefix B P)\<close> for s
    by (simp add: D_Mprefix subset_iff image_iff)
       (metis initials_memI D_T)
next
  from that have that'' : \<open>Q\<^sup>0 \<subseteq> ev ` A\<close>
    using anti_mono_initials_DT initials_Mprefix by blast
  fix s
  assume * : \<open>s \<in> \<T> Q\<close>
  with set_mp[OF that'[THEN conjunct1] this]
  consider \<open>s = []\<close> | \<open>\<exists>e s'. s = ev e # s' \<and> ev e \<in> Q\<^sup>0\<close>
    by (simp add: T_Mprefix) (metis initials_memI)
  thus \<open>s \<in> \<T> (Mprefix B P)\<close>
  proof cases
    show \<open>s = [] \<Longrightarrow> s \<in> \<T> (Mprefix B P)\<close> by simp
  next
    assume \<open>\<exists>e s'. s = ev e # s' \<and> ev e \<in> Q\<^sup>0\<close>
    with set_mp[OF that'[THEN conjunct1] "*"] that(2)
    show \<open>s \<in> \<T> (Mprefix B P)\<close> by (auto simp add: T_Mprefix)
  qed
qed

corollary initials_restriction_Mprefix_DT:
  \<open>\<box>a \<in> A \<rightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> \<box>a \<in> {e. ev e \<in> Q\<^sup>0} \<rightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (erule superset_initials_restriction_Mprefix_DT) simp
 
corollary events_restriction_Mprefix_DT:
  \<open>\<box>a \<in> A \<rightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T (Q :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow> \<box>a \<in> \<alpha>(Q) \<rightarrow> P a \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (erule superset_initials_restriction_Mprefix_DT)
     (simp add: subset_iff initial_ev_imp_in_events_of)





paragraph \<open>Admissibility\<close>

(* lemma not_le_F_adm[simp]: 
  \<open>adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>F v x)\<close> if \<open>cont (u::('a::cpo) \<Rightarrow> 'b process)\<close> and \<open>monofun v\<close>
proof (unfold adm_def, intro allI impI)
  fix Y
  assume chain : \<open>chain Y\<close> and hyp : \<open>\<forall>i. \<not> u (Y i) \<sqsubseteq>\<^sub>F v (Y i)\<close>
  have \<open>v (Y i) \<sqsubseteq> v (\<Squnion>i. Y i)\<close> for i by (simp add: chain is_ub_thelub monofunE that(2))
  from le_approx_lemma_F[OF this] have \<open>\<not> v (\<Squnion>i. Y i) \<sqsubseteq>\<^sub>F u (Y i)\<close> for i 
    using hyp[rule_format, of i, unfolded failure_refine_def]

  have \<open>(s, X) \<in> \<F> (v (\<Squnion>x. Y x)) \<longleftrightarrow> (\<forall>i. (s, X) \<in> \<F> (v (Y i)))\<close> for s X
    apply (simp add: lub_def)
  (* from hyp[unfolded failure_refine_def] have \<open>\<close> *)
    thm hyp[unfolded failure_refine_def subset_iff, simplified]
  
    thm limproc_is_thelub
  { fix s X
    assume \<open>(s, X) \<in> \<F> (v (\<Squnion>x. Y x)) \<Longrightarrow> (s, X) \<in> \<F> (u (\<Squnion>x. Y x))\<close>
    hence False 
      using hyp[unfolded failure_refine_def subset_iff, simplified]
      apply (simp add: cont2contlubE limproc_is_thelub ch2ch_cont that(1) chain F_LUB)
      apply (auto simp add:   lub_def is_lub_def is_ub_def)
      
      find_theorems \<open>(<<|)\<close> name: def
      find_theorems monofun
      
      sorry }
  thus \<open>\<not> u (Lub Y) \<sqsubseteq>\<^sub>F v (Lub Y)\<close> 
    oops
    unfolding failure_refine_def apply simp by (auto simp add: subset_iff) *)
\<comment>\<open>See if we can do this kind of version with \<^const>\<open>monofun\<close>, not easy.\<close>



\<comment>\<open>Less powerful versions\<close>
lemma not_le_F_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>F P)\<close>
  by (simp add: adm_def cont2contlubE ch2ch_cont failure_refine_def
                limproc_is_thelub F_LUB subset_iff) blast

lemma not_le_T_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>T P)\<close>
  by (simp add: adm_def cont2contlubE ch2ch_cont trace_refine_def
                limproc_is_thelub T_LUB subset_iff) blast

lemma not_le_D_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>D P)\<close>
  by (simp add: adm_def cont2contlubE ch2ch_cont divergence_refine_def
                limproc_is_thelub D_LUB subset_iff) blast

lemma not_le_FD_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>F\<^sub>D P)\<close>
  by (simp add: adm_def cont2contlubE ch2ch_cont failure_divergence_refine_def 
                failure_refine_def divergence_refine_def limproc_is_thelub F_LUB D_LUB subset_iff) blast

lemma not_le_DT_adm[simp]: \<open>cont u \<Longrightarrow> adm (\<lambda>x. \<not> u x \<sqsubseteq>\<^sub>D\<^sub>T P)\<close>
  by (simp add: adm_def cont2contlubE ch2ch_cont trace_divergence_refine_def trace_refine_def
                divergence_refine_def limproc_is_thelub D_LUB T_LUB subset_iff) blast





lemma initials_refusal: 
   \<open>(t, UNIV) \<in> \<F> P\<close> if assms: \<open>t \<in> \<T> P\<close> \<open>tF t\<close> \<open>(t, (P after\<^sub>\<T> t)\<^sup>0) \<in> \<F> P\<close>
proof (rule ccontr)
  assume \<open>(t, UNIV) \<notin> \<F> P\<close>
  from is_processT5_S7'[OF assms(3), of UNIV, simplified, OF this]
  obtain e where \<open>e \<notin> (P after\<^sub>\<T> t)\<^sup>0 \<and> t @ [e] \<in> \<T> P\<close> ..
  thus False by (simp add: initials_def T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq assms(1, 2))
qed




lemma leF_ev_initialE' :
  assumes \<open>STOP \<sqinter> (\<sqinter>a \<in> UNIV \<rightarrow> P a) \<sqsubseteq>\<^sub>F Q\<close> \<open>Q \<noteq> STOP\<close> obtains a where \<open>ev a \<in> Q\<^sup>0\<close>
proof -
  from \<open>Q \<noteq> STOP\<close> initials_empty_iff_STOP obtain e where \<open>e \<in> Q\<^sup>0\<close> by blast
  with \<open>STOP \<sqinter> (\<sqinter>a \<in> UNIV \<rightarrow> P a) \<sqsubseteq>\<^sub>F Q\<close> obtain a where \<open>e = ev a\<close>
    by (auto simp add: failure_refine_def F_Ndet F_STOP F_Mndetprefix'
                intro: T_F dest!: initials_memD)
  with \<open>e \<in> Q\<^sup>0\<close> that show thesis by blast
qed

corollary leF_ev_initialE :
  assumes \<open>\<sqinter>a \<in> UNIV \<rightarrow> P a \<sqsubseteq>\<^sub>F Q\<close> obtains a where \<open>ev a \<in> Q\<^sup>0\<close>
proof -
  from \<open>\<sqinter>a \<in> UNIV \<rightarrow> P a \<sqsubseteq>\<^sub>F Q\<close> Ndet_F_self_right trans_F
  have \<open>STOP \<sqinter> (\<sqinter>a \<in> UNIV \<rightarrow> P a) \<sqsubseteq>\<^sub>F Q\<close> by blast
  moreover from \<open>\<sqinter>a \<in> UNIV \<rightarrow> P a \<sqsubseteq>\<^sub>F Q\<close> have \<open>Q \<noteq> STOP\<close>
    by (auto simp add: Process_eq_spec failure_refine_def F_Mndetprefix' F_STOP)
  ultimately obtain a where \<open>ev a \<in> Q\<^sup>0\<close> by (rule leF_ev_initialE')
  with that show thesis by blast
qed
  

lemma leFD_ev_initialE' :
  \<open>STOP \<sqinter> (\<sqinter>a \<in> UNIV \<rightarrow> P a) \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Q \<noteq> STOP \<Longrightarrow> (\<And>a. ev a \<in> Q\<^sup>0 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (meson leFD_imp_leF leF_ev_initialE')

lemma leFD_ev_initialE : 
  \<open>\<sqinter>a \<in> UNIV \<rightarrow> P a \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> (\<And>a. ev a \<in> Q\<^sup>0 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (meson leFD_imp_leF leF_ev_initialE)
    
 
(* TODO: useful ? *)
method prove_propagation uses simp base =
       induct rule: reachable_processes_FD_refinement_propagation_induct,
       solves simp, solves \<open>use base in \<open>simp add: simp\<close>\<close>, solves \<open>simp add: simp\<close>




text \<open>The three following results illustrate how powerful are our new rules of induction.\<close>

text \<open>Really ? The second version with @{thm cont_parallel_fix_ind} seems easier...\<close>

lemma (* deadlock_free_imp_DF_F_prem: *)
  \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> DF \<alpha>(P) \<sqsubseteq>\<^sub>F Q\<close> if df_P: \<open>deadlock_free P\<close>
proof (unfold DF_def, induct rule: reachable_processes_fix_ind_F)
  show \<open>cont (\<lambda>x. \<sqinter> a \<in> events_of P \<rightarrow> x)\<close> by simp
next
  fix x
  assume hyp : \<open>\<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>F Q\<close>
  show \<open>s \<in> \<T> P \<Longrightarrow> tickFree s \<Longrightarrow> \<sqinter>a \<in> events_of P \<rightarrow> x \<sqsubseteq>\<^sub>F P after\<^sub>\<T> s\<close> for s
  proof (unfold failure_refine_def, safe)
    show \<open>s \<in> \<T> P \<Longrightarrow> tickFree s \<Longrightarrow> (t, X) \<in> \<F> (P after\<^sub>\<T> s) \<Longrightarrow> 
          (t, X) \<in> \<F> (\<sqinter>a \<in> events_of P \<rightarrow> x)\<close> for t X
    proof (induct t arbitrary: s)
      case Nil
      have * : \<open>deadlock_free (P after\<^sub>\<T> s)\<close>
        by (metis After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps(1) \<open>s \<in> \<T> P\<close> deadlock_free_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_characterization df_P)
      have \<open>([], X \<union> (- initials (P after\<^sub>\<T> s))) \<in> \<F> (P after\<^sub>\<T> s)\<close>
        by (metis ComplD Nil.prems T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq is_processT5_S7' 
                  mem_Collect_eq initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e self_append_conv2)
      from this[THEN set_rev_mp, OF "*"[unfolded deadlock_free_F failure_refine_def]]
      show \<open>([], X) \<in> \<F> (\<sqinter>a \<in> events_of P \<rightarrow> x)\<close>
        apply (subst (asm) F_DF, simp add: F_Mndetprefix write0_def F_Mprefix image_iff)
        using Nil.prems(1) deadlock_free_implies_non_terminating events_of_iff_reachable_ev 
              reachable_ev_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T that by blast
    next
      case (Cons e t)
      from Cons.prems(1, 2) have * : \<open>P after\<^sub>\<T> s \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
        by (auto simp add: reachable_processes_is)
      obtain e' where ** : \<open>e = ev e'\<close> \<open>e' \<in> events_of P\<close>
        by (meson Cons.prems(1, 3) initials_memI F_T set_mp
                  deadlock_free_implies_non_terminating df_P imageE 
                  non_terminating_is_right initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_subset_events_of)
      from Cons.prems F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq "**"(1)
      have \<open>(t, X) \<in> \<F> (P after\<^sub>\<T> (s @ [e]))\<close> by (simp add: F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e)
      also have \<open>\<dots> \<subseteq> \<F> x\<close>
        apply (rule hyp[rule_format, unfolded failure_refine_def,
                        of \<open>P after\<^sub>\<T> (s @ [e])\<close>, simplified])
        apply (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc "**"(1) After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        apply (rule reachable_after[OF "*" ])
        using Cons.prems(3) initials_memI F_T "**"(1) by blast
      finally have \<open>(t, X) \<in> \<F> x\<close> .
      with "**" show ?case by (auto simp add: F_Mndetprefix write0_def F_Mprefix)
    qed
  qed
qed


lemma (* deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_imp_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_prem: *)
  \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) UNIV \<sqsubseteq>\<^sub>F Q\<close> if df\<^sub>S\<^sub>K\<^sub>I\<^sub>P_P: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
proof (unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct rule: reachable_processes_fix_ind_F)
  show \<open>cont (\<lambda>x. (\<sqinter>a \<in> events_of P \<rightarrow> x) \<sqinter> SKIPS UNIV)\<close> by simp
next
  fix x
  assume hyp : \<open>\<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>F Q\<close>
  show \<open>s \<in> \<T> P \<Longrightarrow> tickFree s \<Longrightarrow> (\<sqinter>a \<in> events_of P \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F P after\<^sub>\<T> s\<close> for s
  proof (unfold failure_refine_def, safe)
    show \<open>s \<in> \<T> P \<Longrightarrow> tickFree s \<Longrightarrow> (t, X) \<in> \<F> (P after\<^sub>\<T> s) \<Longrightarrow>
          (t, X) \<in> \<F> ((\<sqinter>a \<in> events_of P \<rightarrow> x) \<sqinter> SKIPS UNIV)\<close> for t X
    proof (induct t arbitrary: s)
      case Nil
      have * : \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P after\<^sub>\<T> s)\<close>
        by (metis After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps(1) Nil.prems(1, 2) deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_characterization df\<^sub>S\<^sub>K\<^sub>I\<^sub>P_P)
      have \<open>([], X \<union> (- initials (P after\<^sub>\<T> s))) \<in> \<F> (P after\<^sub>\<T> s)\<close>
        by (metis (no_types, opaque_lifting) ComplD initials_memI
                  Nil.prems(3) append_eq_Cons_conv is_processT5_S7')
      from this[THEN set_rev_mp, OF "*"[unfolded deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def]]
      show \<open>([], X) \<in> \<F> ((\<sqinter>a \<in> events_of P \<rightarrow> x) \<sqinter> SKIPS UNIV)\<close>
        apply (subst (asm) F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S, simp add: F_Ndet F_SKIPS F_Mndetprefix write0_def F_Mprefix image_iff)
        using Nil.prems(1, 2) events_of_iff_reachable_ev
              reachable_ev_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T by blast
    next
      case (Cons e t)
      from Cons.prems(1, 2) have * : \<open>P after\<^sub>\<T> s \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
        by (auto simp add: reachable_processes_is)
      have \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P after\<^sub>\<T> s)\<close>
        by (metis After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps(1) Cons.prems(1, 2) deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_characterization df\<^sub>S\<^sub>K\<^sub>I\<^sub>P_P)
      then consider a where \<open>e = ev a\<close> \<open>a \<in> events_of P\<close> | r where \<open>e = \<checkmark>(r)\<close>
        unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def
        apply (subst (asm) F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S, simp add: subset_iff image_iff)
        by (metis reachable_ev_iff_in_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_for_some_tickFree_T Cons.prems
                  initials_memI F_T events_of_iff_reachable_ev list.distinct(1) list.sel(1))
      thus ?case
      proof cases
        fix a assume ** : \<open>e = ev a\<close> \<open>a \<in> events_of P\<close>
        from Cons.prems F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e "**"(1)
        have \<open>(t, X) \<in> \<F> (P after\<^sub>\<T> (s @ [e]))\<close> by (simp add: F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq)
        also have \<open>\<dots> \<subseteq> \<F> x\<close>
          apply (rule hyp[rule_format, unfolded failure_refine_def,
                        of \<open>P after\<^sub>\<T> (s @ [e])\<close>, simplified])
          apply (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc "**"(1) After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
          apply (rule reachable_after[OF "*" ])
          using Cons.prems(3) initials_memI F_T "**"(1) by blast
        finally have \<open>(t, X) \<in> \<F> x\<close> .
        with "**" show ?case by (auto simp add: F_Ndet F_Mndetprefix write0_def F_Mprefix)
      next
        fix r assume \<open>e = \<checkmark>(r)\<close>
        hence \<open>t = []\<close>
          by (metis Cons.prems(3) F_imp_front_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_Cons_iff)
        thus ?case by (simp add: \<open>e = \<checkmark>(r)\<close> F_Ndet F_SKIPS)
      qed
    qed
  qed
qed


context fixes P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> begin

theorem deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>deadlock_free P \<longleftrightarrow> \<checkmark>s(P) = {} \<and> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
proof (intro iffI conjI)
  from deadlock_free_implies_non_terminating tickFree_traces_iff_empty_ticks_of
  show \<open>deadlock_free P \<Longrightarrow> \<checkmark>s(P) = {}\<close> by fast
next
  show \<open>deadlock_free P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
    by (fact deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)
next
  have \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>F Q \<Longrightarrow> DF UNIV \<sqsubseteq>\<^sub>F Q\<close> if \<open>\<checkmark>s(P) = {}\<close> for Q
  proof (unfold DF_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct arbitrary: Q rule: cont_parallel_fix_ind)
    show \<open>cont (\<lambda>x. (\<sqinter>a\<in>UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV)\<close> by simp
  next
    show \<open>cont (\<lambda>x. \<sqinter>a\<in>UNIV \<rightarrow> x)\<close> by simp
  next
    show \<open>adm (\<lambda>x. \<forall>Q. Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<longrightarrow> fst x \<sqsubseteq>\<^sub>F Q \<longrightarrow> snd x \<sqsubseteq>\<^sub>F Q)\<close> by simp
  next
    show \<open>\<And>Q. \<bottom> \<sqsubseteq>\<^sub>F Q\<close> by simp
  next
    fix x y Q assume hyp : \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> x \<sqsubseteq>\<^sub>F Q \<Longrightarrow> y \<sqsubseteq>\<^sub>F Q\<close> for Q
    assume \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close>
    from \<open>\<checkmark>s(P) = {}\<close> \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> have \<open>\<checkmark>s(Q) = {}\<close>
      using ticks_of_reachable_processes_subset by auto

    from \<open>\<checkmark>s(Q) = {}\<close> initial_tick_imp_in_ticks_of have \<open>{r. \<checkmark>(r) \<in> Q\<^sup>0} = {}\<close> by force
    moreover from \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close>
    have \<open>Q\<^sup>0 \<noteq> {}\<close> by (auto simp add: initials_empty_iff_STOP Process_eq_spec failure_refine_def
                                      F_Ndet F_Mndetprefix' F_SKIPS subset_iff F_STOP) 
    ultimately have \<open>{a. ev a \<in> Q\<^sup>0} \<noteq> {}\<close>
      by (metis empty_Collect_eq equals0I event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
    hence \<open>\<sqinter>a \<in> UNIV \<rightarrow> y \<sqsubseteq>\<^sub>F \<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> y\<close>
      by (metis Mndetprefix_F_subset top_greatest)
    moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F \<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a\<close>
    proof (rule mono_Mndetprefix_F, clarify, rule hyp)
      show \<open>ev a \<in> Q\<^sup>0 \<Longrightarrow> Q after a \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> for a
        by (simp add: \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> reachable_after)
    next
      show \<open>ev a \<in> Q\<^sup>0 \<Longrightarrow> x \<sqsubseteq>\<^sub>F Q after a\<close> for a
        by (frule mono_After_F[OF _ \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close>])
           (simp add: After_Ndet initials_Mndetprefix image_iff After_Mndetprefix)
    qed
    moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F Q\<close>
    proof (unfold failure_refine_def, safe)
      show \<open>(t, X) \<in> \<F> (\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a)\<close> if \<open>(t, X) \<in> \<F> Q\<close> for t X
      proof (cases t)
        from initial_tick_imp_in_ticks_of \<open>\<checkmark>s(Q) = {}\<close> have \<open>range tick \<subseteq> - Q\<^sup>0\<close> by force
        assume \<open>t = []\<close>
        with \<open>(t, X) \<in> \<F> Q\<close> have \<open>([], X \<union> - Q\<^sup>0) \<in> \<F> Q\<close>
          by (metis ComplD initials_memI is_processT5_S7' self_append_conv2)
        with \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close>
        show \<open>(t, X) \<in> \<F> (\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a)\<close>
          by (simp add: failure_refine_def F_Ndet F_SKIPS \<open>t = []\<close> F_Mndetprefix' subset_iff)
             (meson Compl_iff UnI1 UnI2 \<open>range tick \<subseteq> - Q\<^sup>0\<close> list.distinct(1) range_subsetD)
      next
        from \<open>(t, X) \<in> \<F> Q\<close> \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close> \<open>{a. ev a \<in> Q\<^sup>0} \<noteq> {}\<close> \<open>\<checkmark>s(Q) = {}\<close>
        show \<open>t = e # t' \<Longrightarrow> (t, X) \<in> \<F> (\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a)\<close> for e t'
          by (simp add: failure_refine_def F_Ndet F_SKIPS F_Mndetprefix' F_After subset_iff)
             (metis F_T empty_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust initial_tick_imp_in_ticks_of initials_memI)
      qed
    qed
    ultimately show \<open>\<sqinter>a \<in> UNIV \<rightarrow> y \<sqsubseteq>\<^sub>F Q\<close> using trans_F by blast
  qed
  thus \<open>\<checkmark>s(P) = {} \<and> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> deadlock_free P\<close>
    by (simp add: reachable_self deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def deadlock_free_F)
qed



lemma reachable_processes_DF_UNIV_leF_imp_DF_events_of_leF :
  \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> DF UNIV \<sqsubseteq>\<^sub>F Q \<Longrightarrow> DF \<alpha>(P) \<sqsubseteq>\<^sub>F Q\<close> for Q
proof (unfold DF_def, induct arbitrary: Q rule: cont_parallel_fix_ind)
  show \<open>cont (\<lambda>x. \<sqinter>a \<in> UNIV \<rightarrow> x)\<close> by simp
next
  show \<open>cont (\<lambda>x. \<sqinter>a \<in> \<alpha>(P) \<rightarrow> x)\<close> by simp
next
  show \<open>adm (\<lambda>x. \<forall>Q. Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<longrightarrow> fst x \<sqsubseteq>\<^sub>F Q \<longrightarrow> snd x \<sqsubseteq>\<^sub>F Q)\<close> by simp
next
  show \<open>\<And>Q. \<bottom> \<sqsubseteq>\<^sub>F Q\<close> by simp
next
  fix x y Q assume hyp : \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> x \<sqsubseteq>\<^sub>F Q \<Longrightarrow> y \<sqsubseteq>\<^sub>F Q\<close> for Q
  assume \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> and \<open>\<sqinter>a \<in> UNIV \<rightarrow> x \<sqsubseteq>\<^sub>F Q\<close>

  from \<open>\<sqinter>a \<in> UNIV \<rightarrow> x \<sqsubseteq>\<^sub>F Q\<close> obtain a where \<open>ev a \<in> Q\<^sup>0\<close> by (elim leF_ev_initialE)

  have \<open>\<sqinter>a \<in> \<alpha>(P) \<rightarrow> y \<sqsubseteq>\<^sub>F \<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> y\<close>
    by (metis (mono_tags, lifting) Mndetprefix_F_subset \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
              \<open>ev a \<in> Q\<^sup>0\<close> empty_iff events_of_reachable_processes_subset
              initial_ev_imp_in_events_of mem_Collect_eq subset_iff)
  moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F \<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a\<close>
  proof (rule mono_Mndetprefix_F, clarify)
    show \<open>ev a \<in> Q\<^sup>0 \<Longrightarrow> y \<sqsubseteq>\<^sub>F Q after a\<close> for a
      by (metis mono_After_F After_Mndetprefix UNIV_I \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
                \<open>\<sqinter>a\<in>UNIV \<rightarrow> x \<sqsubseteq>\<^sub>F Q\<close> hyp reachable_processes.simps)
  qed
  moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F Q\<close>
  proof (unfold failure_refine_def, safe)
    show \<open>(t, X) \<in> \<F> (\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a)\<close> if \<open>(t, X) \<in> \<F> Q\<close> for t X
    proof (cases t)
      assume \<open>t = []\<close>
      with \<open>(t, X) \<in> \<F> Q\<close> have \<open>([], X \<union> (- Q\<^sup>0)) \<in> \<F> Q\<close>
        by (metis ComplD initials_memI is_processT5_S7' self_append_conv2)
      from \<open>\<sqinter>a \<in> UNIV \<rightarrow> x \<sqsubseteq>\<^sub>F Q\<close> \<open>([], X \<union> (- Q\<^sup>0)) \<in> \<F> Q\<close> have \<open>\<not> range ev \<subseteq> X \<union> - Q\<^sup>0\<close>
        by (simp add: failure_refine_def F_Mndetprefix' subset_iff) blast
      then obtain b where \<open>ev b \<in> Q\<^sup>0\<close> \<open>ev b \<notin> X\<close> by auto
      with \<open>t = []\<close> \<open>ev a \<in> Q\<^sup>0\<close> show \<open>(t, X) \<in> \<F> (\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a)\<close>
        by (auto simp add: F_Mndetprefix')
    next
      from \<open>\<sqinter>a \<in> UNIV \<rightarrow> x \<sqsubseteq>\<^sub>F Q\<close> \<open>(t, X) \<in> \<F> Q\<close> \<open>ev a \<in> Q\<^sup>0\<close>
      show \<open>t = e # t' \<Longrightarrow> (t, X) \<in> \<F> (\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a)\<close> for e t'
        by (auto simp add: failure_refine_def F_Mndetprefix' F_After intro!: F_T initials_memI)
    qed
  qed
  ultimately show \<open>\<sqinter>a \<in> \<alpha>(P) \<rightarrow> y \<sqsubseteq>\<^sub>F Q\<close> using trans_F by blast
qed


lemma reachable_processes_CHAOS_UNIV_leF_imp_CHAOS_events_of_leF :
  \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>F Q \<Longrightarrow> CHAOS \<alpha>(P) \<sqsubseteq>\<^sub>F Q\<close> for Q
proof (unfold CHAOS_def, induct arbitrary: Q rule: cont_parallel_fix_ind)
  show \<open>cont (\<lambda>x. STOP \<sqinter> (\<box>a \<in> UNIV \<rightarrow> x))\<close> by simp
next
  show \<open>cont (\<lambda>x. STOP \<sqinter> (\<box>a \<in> \<alpha>(P) \<rightarrow> x))\<close> by simp
next
  show \<open>adm (\<lambda>x. \<forall>Q. Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<longrightarrow> fst x \<sqsubseteq>\<^sub>F Q \<longrightarrow> snd x \<sqsubseteq>\<^sub>F Q)\<close> by simp
next
  show \<open>\<And>Q. \<bottom> \<sqsubseteq>\<^sub>F Q\<close> by simp
next
  fix x y Q assume hyp : \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> x \<sqsubseteq>\<^sub>F Q \<Longrightarrow> y \<sqsubseteq>\<^sub>F Q\<close> for Q
  assume \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> and \<open>STOP \<sqinter> (\<box>a\<in>UNIV \<rightarrow> x) \<sqsubseteq>\<^sub>F Q\<close>

  from \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> events_of_reachable_processes_subset initial_ev_imp_in_events_of
  have \<open>STOP \<sqinter> (\<box>a \<in> \<alpha>(P) \<rightarrow> y) \<sqsubseteq>\<^sub>F STOP \<sqinter> (\<box>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> y)\<close>
    by (fastforce simp add: failure_refine_def Ndet_projs Mprefix_projs STOP_projs)
  moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F STOP \<sqinter> (\<box>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a)\<close>
  proof (intro mono_Ndet_F[OF idem_F] mono_Mprefix_F, clarify)
    show \<open>ev a \<in> Q\<^sup>0 \<Longrightarrow> y \<sqsubseteq>\<^sub>F Q after a\<close> for a
      by (frule mono_After_F[OF _ \<open>STOP \<sqinter> (\<box>a\<in>UNIV \<rightarrow> x) \<sqsubseteq>\<^sub>F Q\<close>])
         (simp add: After_Ndet initials_Mprefix After_Mprefix
                    \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> hyp reachable_after)
  qed
  moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F Q\<close>
  proof (unfold failure_refine_def, safe)
    from \<open>STOP \<sqinter> (\<box>a\<in>UNIV \<rightarrow> x) \<sqsubseteq>\<^sub>F Q\<close>
    show \<open>(t, X) \<in> \<F> Q \<Longrightarrow> (t, X) \<in> \<F> (STOP \<sqinter> (\<box>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a))\<close> for t X
      by (auto simp add: refine_defs F_Ndet F_Mprefix F_After intro!: F_T initials_memI)
  qed
  ultimately show \<open>STOP \<sqinter> (\<box>a \<in> \<alpha>(P) \<rightarrow> y) \<sqsubseteq>\<^sub>F Q\<close> using trans_F by blast
qed


lemma reachable_processes_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_UNIV_UNIV_leF_imp_CHAOS_events_of_ticks_of_leFD :
  \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> for Q
proof (unfold CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct arbitrary: Q rule: cont_parallel_fix_ind)
  show \<open>cont (\<lambda>x. SKIPS UNIV \<sqinter> STOP \<sqinter> (\<box>a \<in> UNIV \<rightarrow> x))\<close> by simp
next
  show \<open>cont (\<lambda>x. SKIPS \<checkmark>s(P) \<sqinter> STOP \<sqinter> (\<box>a \<in> \<alpha>(P) \<rightarrow> x))\<close> by simp
next
  show \<open>adm (\<lambda>x. \<forall>Q. Q \<in>\<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<longrightarrow> fst x \<sqsubseteq>\<^sub>F\<^sub>D Q \<longrightarrow> snd x \<sqsubseteq>\<^sub>F\<^sub>D Q)\<close> by simp
next
  show \<open>\<And>Q. \<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> by simp
next
  fix x y Q assume hyp : \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> y \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> for Q
  assume \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> and \<open>SKIPS UNIV \<sqinter> STOP \<sqinter> (\<box>a \<in> UNIV \<rightarrow> x) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>

  from \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> ticks_of_reachable_processes_subset initial_tick_imp_in_ticks_of
  have \<open>SKIPS \<checkmark>s(P) \<sqinter> STOP \<sqsubseteq>\<^sub>F\<^sub>D SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0} \<sqinter> STOP\<close>
    by (fastforce simp add: refine_defs Ndet_projs STOP_projs SKIPS_projs)
  moreover from \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> events_of_reachable_processes_subset initial_ev_imp_in_events_of
  have \<open>STOP \<sqinter> (\<box>a \<in> \<alpha>(P) \<rightarrow> y) \<sqsubseteq>\<^sub>F\<^sub>D STOP \<sqinter> (\<box>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> y)\<close>
    by (fastforce simp add: refine_defs Ndet_projs STOP_projs Mprefix_projs)
  ultimately have \<open>SKIPS \<checkmark>s(P) \<sqinter> STOP \<sqinter> (\<box>a \<in> \<alpha>(P) \<rightarrow> y) \<sqsubseteq>\<^sub>F\<^sub>D
                   SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0} \<sqinter> STOP \<sqinter> (\<box>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> y)\<close>
    by (auto simp add: refine_defs Ndet_projs)
  moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0} \<sqinter> STOP \<sqinter> (\<box>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a)\<close>
  proof (intro mono_Ndet_FD[OF idem_FD] mono_Mprefix_FD, clarify)
    show \<open>ev a \<in> Q\<^sup>0 \<Longrightarrow> y \<sqsubseteq>\<^sub>F\<^sub>D Q after a\<close> for a
      by (frule mono_After_FD[OF _ \<open>SKIPS UNIV \<sqinter> STOP \<sqinter> (\<box>a \<in> UNIV \<rightarrow> x) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>])
         (simp add: After_Ndet initials_Mprefix initials_Ndet image_iff
                    After_Mprefix \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> hyp reachable_after)
  qed
  moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  proof (unfold refine_defs, safe)
    from \<open>SKIPS UNIV \<sqinter> STOP \<sqinter> (\<box>a \<in> UNIV \<rightarrow> x) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
    show \<open>t \<in> \<D> Q \<Longrightarrow> t \<in> \<D> (SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0} \<sqinter> STOP \<sqinter> (\<box>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a))\<close> for t
      by (auto simp add: refine_defs D_Ndet D_Mprefix D_STOP D_After D_SKIPS)
         (use D_T initials_memI in blast)
  next
    from \<open>SKIPS UNIV \<sqinter> STOP \<sqinter> (\<box>a \<in> UNIV \<rightarrow> x) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
    show \<open>(t, X) \<in> \<F> Q \<Longrightarrow> (t, X) \<in> \<F> (SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0} \<sqinter> STOP \<sqinter> (\<box>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a))\<close> for t X
      by (cases t, simp_all add: refine_defs F_Ndet F_Mprefix F_After F_SKIPS F_STOP)
         (use F_T initials_memI in blast)
  qed
  ultimately show \<open>SKIPS \<checkmark>s(P) \<sqinter> STOP \<sqinter> (\<box>a \<in> \<alpha>(P) \<rightarrow> y) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> by force
qed



theorem deadlock_free_iff_DF_events_of_leF :
  \<open>deadlock_free P \<longleftrightarrow> \<alpha>(P) \<noteq> {} \<and> DF \<alpha>(P) \<sqsubseteq>\<^sub>F P\<close>
proof (intro iffI conjI)
  show \<open>\<alpha>(P) \<noteq> {} \<and> DF \<alpha>(P) \<sqsubseteq>\<^sub>F P \<Longrightarrow> deadlock_free P\<close>
    by (meson DF_Univ_freeness deadlock_free_F order_refl trans_F)
next
  show \<open>deadlock_free P \<Longrightarrow> \<alpha>(P) \<noteq> {}\<close> by (simp add: nonempty_events_of_if_deadlock_free)
next
  show \<open>deadlock_free P \<Longrightarrow> DF \<alpha>(P) \<sqsubseteq>\<^sub>F P\<close>
    by (simp add: deadlock_free_F reachable_self
                  reachable_processes_DF_UNIV_leF_imp_DF_events_of_leF)
qed

corollary deadlock_free_iff_DF_events_of_leFD :
  \<open>deadlock_free P \<longleftrightarrow> \<alpha>(P) \<noteq> {} \<and> DF \<alpha>(P) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis deadlock_free_iff_DF_events_of_leF deadlock_free_def div_free_DF
            divergence_refine_def failure_divergence_refine_def)

corollary deadlock_free_iff_DF_strict_events_of_leF :
  \<open>deadlock_free P \<longleftrightarrow> \<^bold>\<alpha>(P) \<noteq> {} \<and> DF \<^bold>\<alpha>(P) \<sqsubseteq>\<^sub>F P\<close> 
  by (metis anti_mono_events_of_F deadlock_free_iff_DF_events_of_leF
            deadlock_free_implies_div_free events_of_DF events_of_is_strict_events_of_or_UNIV
            order_class.order_eq_iff strict_events_of_subset_events_of)

corollary deadlock_free_iff_DF_strict_events_of_leFD :
  \<open>deadlock_free P \<longleftrightarrow> \<^bold>\<alpha>(P) \<noteq> {} \<and> DF \<^bold>\<alpha>(P) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
 by (metis DF_Univ_freeness deadlock_free_iff_DF_events_of_leFD
            deadlock_free_implies_div_free events_of_is_strict_events_of_or_UNIV)



theorem lifelock_free_iff_CHAOS_events_of_leF :
  \<open>lifelock_free P \<longleftrightarrow> CHAOS \<alpha>(P) \<sqsubseteq>\<^sub>F P\<close>
proof (intro iffI conjI)
  show \<open>CHAOS \<alpha>(P) \<sqsubseteq>\<^sub>F P \<Longrightarrow> lifelock_free P\<close>
    by (meson CHAOS_subset_FD lifelock_free_def non_terminating_F
              non_terminating_FD top_greatest trans_F)
next
  show \<open>lifelock_free P \<Longrightarrow> CHAOS \<alpha>(P) \<sqsubseteq>\<^sub>F P\<close>
    by (simp add: leFD_imp_leF lifelock_free_def reachable_self
                  reachable_processes_CHAOS_UNIV_leF_imp_CHAOS_events_of_leF)
qed

corollary lifelock_free_iff_CHAOS_strict_events_of_leF :
  \<open>lifelock_free P \<longleftrightarrow> CHAOS \<^bold>\<alpha>(P) \<sqsubseteq>\<^sub>F P\<close>
  by (metis anti_mono_ticks_of_F bot.extremum_uniqueI empty_not_UNIV
      events_of_is_strict_events_of_or_UNIV lifelock_free_iff_CHAOS_events_of_leF
      ticks_CHAOS ticks_of_is_strict_ticks_of_or_UNIV)

corollary lifelock_free_iff_CHAOS_events_of_leFD :
  \<open>lifelock_free P \<longleftrightarrow> CHAOS \<alpha>(P) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis div_free_CHAOS divergence_refine_def failure_divergence_refine_def
            lifelock_free_def lifelock_free_iff_CHAOS_events_of_leF)

corollary lifelock_free_iff_CHAOS_strict_events_of_leFD :
  \<open>lifelock_free P \<longleftrightarrow> CHAOS \<^bold>\<alpha>(P) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis anti_mono_events_of_F antisym events_of_CHAOS leFD_imp_leF
      lifelock_free_iff_CHAOS_events_of_leFD
      lifelock_free_iff_CHAOS_strict_events_of_leF strict_events_of_subset_events_of)





theorem lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_events_of_ticks_of_FD :
  \<open>lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
proof (intro iffI)
  show \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
    by (metis events_of_is_strict_events_of_or_UNIV lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def
              lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_div_free ticks_of_is_strict_ticks_of_or_UNIV)
next
  show \<open>lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
    by (simp add: lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def reachable_self
                  reachable_processes_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_UNIV_UNIV_leF_imp_CHAOS_events_of_ticks_of_leFD)
qed

corollary lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_strict_events_of_strict_ticks_of_FD :
  \<open>lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<^bold>\<alpha>(P) \<^bold>\<checkmark>\<^bold>s(P) \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis (no_types) anti_mono_events_of_FD anti_mono_ticks_of_FD events_of_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S
      events_of_is_strict_events_of_or_UNIV lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_events_of_ticks_of_FD
      lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_div_free ticks_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ticks_of_is_strict_ticks_of_or_UNIV top.extremum_uniqueI)

   

theorem deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_events_of_ticks_of_leF :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> (  if \<alpha>(P) = {} \<and> \<checkmark>s(P) = {} then False
                            else   if \<checkmark>s(P) = {} then DF \<alpha>(P) \<sqsubseteq>\<^sub>F P
                                 else   if \<alpha>(P) = {} then SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F P
                                      else DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F P)\<close>
  (is \<open>_ \<longleftrightarrow> ?rhs\<close>)
proof (split if_split, intro conjI impI)
  from deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S nonempty_events_of_if_deadlock_free
  show \<open>\<alpha>(P) = {} \<and> \<checkmark>s(P) = {} \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> False\<close> by blast
next
  assume \<open>\<not> (\<alpha>(P) = {} \<and> \<checkmark>s(P) = {})\<close>
  show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow>
        (  if \<checkmark>s(P) = {} then DF \<alpha>(P) \<sqsubseteq>\<^sub>F P
         else if \<alpha>(P) = {} then SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F P else DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F P)\<close>
  proof (split if_split, intro conjI impI)
    from \<open>\<not> (\<alpha>(P) = {} \<and> \<checkmark>s(P) = {})\<close> deadlock_free_iff_DF_events_of_leF
         deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 
    show \<open>\<checkmark>s(P) = {} \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> DF \<alpha>(P) \<sqsubseteq>\<^sub>F P\<close> by blast
  next
    show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow>
          (if \<alpha>(P) = {} then SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F P else DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F P)\<close> if \<open>\<checkmark>s(P) \<noteq> {}\<close>
    proof (split if_split, intro conjI impI)
      assume \<open>\<alpha>(P) = {}\<close>
      with initial_ev_imp_in_events_of have \<open>range ev \<subseteq> - P\<^sup>0\<close> by force
      show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F P\<close>
      proof (rule iffI)
        show \<open>SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
          by (metis deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIPS deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def \<open>\<checkmark>s(P) \<noteq> {}\<close> trans_F)
      next
        show \<open>SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F P\<close> if \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
        proof (unfold failure_refine_def, safe)
          show \<open>(t, X) \<in> \<F> (SKIPS \<checkmark>s(P))\<close> if \<open>(t, X) \<in> \<F> P\<close> for t X
          proof (cases t)
            assume \<open>t = []\<close>
            with \<open>(t, X) \<in> \<F> P\<close> have \<open>(t, X \<union> - P\<^sup>0) \<in> \<F> P\<close>
              by (metis ComplD initials_memI is_processT5_S7' self_append_conv2)
            with \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> have \<open>(t, X \<union> - P\<^sup>0) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close>
              by (auto simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def)
            with \<open>range ev \<subseteq> - P\<^sup>0\<close> \<open>\<checkmark>s(P) \<noteq> {}\<close> show \<open>(t, X) \<in> \<F> (SKIPS \<checkmark>s(P))\<close>
              by (subst (asm) DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
                 (auto simp add: F_Ndet F_Mndetprefix' F_SKIPS \<open>t = []\<close>
                          intro: initial_tick_imp_in_ticks_of)
          next
            fix e t' assume \<open>t = e # t'\<close>
            with F_T \<open>(t, X) \<in> \<F> P\<close> \<open>\<alpha>(P) = {}\<close> obtain r where \<open>r \<in> \<checkmark>s(P)\<close> \<open>e = \<checkmark>(r)\<close> \<open>t' = []\<close>
              by (metis F_imp_front_tickFree empty_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust events_of_memI
                        front_tickFree_Cons_iff initial_tick_imp_in_ticks_of
                        initials_memI is_ev_def list.set_intros(1))
            thus \<open>(t, X) \<in> \<F> (SKIPS \<checkmark>s(P))\<close>
              by (simp add: F_Mndetprefix' F_SKIPS \<open>\<checkmark>s(P) \<noteq> {}\<close> \<open>t = e # t'\<close>)
          qed
        qed
      qed
    next
      show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F P\<close> if \<open>\<alpha>(P) \<noteq> {}\<close>
      proof (rule iffI)
        show \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
          by (meson DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_subset \<open>\<checkmark>s(P) \<noteq> {}\<close> \<open>\<alpha>(P) \<noteq> {}\<close>
                    deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def leFD_imp_leF subset_UNIV that trans_F)
      next
        have \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>F Q \<Longrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F Q\<close> for Q
        proof (unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct arbitrary: Q rule: cont_parallel_fix_ind)
          show \<open>cont (\<lambda>x. (\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV)\<close> by simp
        next
          show \<open>cont (\<lambda>x. (\<sqinter>a \<in> \<alpha>(P) \<rightarrow> x) \<sqinter> SKIPS \<checkmark>s(P))\<close> by simp
        next
          show \<open>adm (\<lambda>x. \<forall>Q. Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<longrightarrow> fst x \<sqsubseteq>\<^sub>F Q \<longrightarrow> snd x \<sqsubseteq>\<^sub>F Q)\<close> by simp
        next
          show \<open>\<And>Q. \<bottom> \<sqsubseteq>\<^sub>F Q\<close> by simp
        next
          fix x y Q assume hyp : \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> x \<sqsubseteq>\<^sub>F Q \<Longrightarrow> y \<sqsubseteq>\<^sub>F Q\<close> for Q
          assume \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> and \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close>
          consider \<open>{a. ev a \<in> Q\<^sup>0} = {}\<close> \<open>{r. \<checkmark>(r) \<in> Q\<^sup>0} = {}\<close>
            | \<open>{a. ev a \<in> Q\<^sup>0} = {}\<close> \<open>{r. \<checkmark>(r) \<in> Q\<^sup>0} \<noteq> {}\<close>
            | \<open>{a. ev a \<in> Q\<^sup>0} \<noteq> {}\<close> by blast
            
          thus \<open>(\<sqinter>a \<in> \<alpha>(P) \<rightarrow> y) \<sqinter> SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F Q\<close>
          proof cases
            assume \<open>{a. ev a \<in> Q\<^sup>0} = {}\<close> \<open>{r. \<checkmark>(r) \<in> Q\<^sup>0} = {}\<close>
            hence \<open>Q\<^sup>0 = {}\<close> by (metis Collect_empty_eq all_not_in_conv event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
            hence \<open>Q = STOP\<close> by (simp add: initials_empty_iff_STOP)
            with \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close> have False
              by (auto simp add: failure_refine_def Process_eq_spec
                                 F_STOP F_Ndet F_Mndetprefix' F_SKIPS)
            thus \<open>(\<sqinter>a \<in> \<alpha>(P) \<rightarrow> y) \<sqinter> SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F Q\<close> ..
          next
            assume \<open>{a. ev a \<in> Q\<^sup>0} = {}\<close> \<open>{r. \<checkmark>(r) \<in> Q\<^sup>0} \<noteq> {}\<close>
            have \<open>SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0} \<sqsubseteq>\<^sub>F Q\<close>
            proof (unfold failure_refine_def, safe)
              show \<open>(t, X) \<in> \<F> (SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0})\<close> if \<open>(t, X) \<in> \<F> Q\<close> for t X
              proof (cases t)
                assume \<open>t = []\<close>
                with \<open>(t, X) \<in> \<F> Q\<close> have \<open>([], X \<union> - Q\<^sup>0) \<in> \<F> Q\<close>
                  by (metis ComplD initials_memI is_processT5_S7' self_append_conv2)
                with \<open>t = []\<close> \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close> \<open>{a. ev a \<in> Q\<^sup>0} = {}\<close>
                show \<open>(t, X) \<in> \<F> (SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0})\<close>
                  by (simp add: failure_refine_def F_Ndet F_Mndetprefix' F_SKIPS subset_iff)
                     (metis Compl_iff Un_iff neq_Nil_conv)
              next
                from \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close> \<open>{a. ev a \<in> Q\<^sup>0} = {}\<close>
                      \<open>(t, X) \<in> \<F> Q\<close> F_T initials_memI
                show \<open>t = e # t' \<Longrightarrow> (t, X) \<in> \<F> (SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0})\<close> for e t'
                  by (simp add: failure_refine_def F_Ndet F_Mndetprefix' F_SKIPS) blast
              qed
            qed
            moreover from \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> \<open>{r. \<checkmark>(r) \<in> Q\<^sup>0} \<noteq> {}\<close> initial_tick_imp_in_ticks_of
                          ticks_of_reachable_processes_subset
            have \<open>SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F SKIPS {r. \<checkmark>(r) \<in> Q\<^sup>0}\<close>
              by (force simp add: SKIPS_F_SKIPS_iff \<open>\<checkmark>s(P) \<noteq> {}\<close>)
            ultimately show \<open>(\<sqinter>a \<in> \<alpha>(P) \<rightarrow> y) \<sqinter> SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F Q\<close>
              using Ndet_F_self_right trans_F by blast
          next
            assume \<open>{a. ev a \<in> Q\<^sup>0} \<noteq> {}\<close>
            from \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> initial_tick_imp_in_ticks_of ticks_of_reachable_processes_subset
            have \<open>{r. \<checkmark>(r) \<in> Q\<^sup>0} \<subseteq> \<checkmark>s(P)\<close> by force
            from \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> events_of_reachable_processes_subset initial_ev_imp_in_events_of
            have \<open>(\<sqinter>a \<in> \<alpha>(P) \<rightarrow> y) \<sqinter> SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F (\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> y) \<sqinter> SKIPS \<checkmark>s(P)\<close>
              by (force intro: mono_Ndet_F[OF Mndetprefix_F_subset[OF \<open>{a. ev a \<in> Q\<^sup>0} \<noteq> {}\<close>] idem_F])
            moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F (\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a) \<sqinter> SKIPS \<checkmark>s(P)\<close>
            proof (rule mono_Ndet_F[OF mono_Mndetprefix_F idem_F], clarify)
              show \<open>ev a \<in> Q\<^sup>0 \<Longrightarrow> y \<sqsubseteq>\<^sub>F Q after a\<close> for a
                by (frule mono_After_F[OF _ \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close>])
                   (simp add: After_Ndet initials_Mndetprefix image_iff
                              After_Mndetprefix reachable_after \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close> hyp)
            qed
            moreover have \<open>\<dots> \<sqsubseteq>\<^sub>F Q\<close>
            proof (unfold failure_refine_def, safe)
              show \<open>(t, X) \<in> \<F> ((\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a) \<sqinter> SKIPS \<checkmark>s(P))\<close> if \<open>(t, X) \<in> \<F> Q\<close> for t X
              proof (cases t)
                assume \<open>t = []\<close>
                with \<open>(t, X) \<in> \<F> Q\<close> have \<open>([], X \<union> - Q\<^sup>0) \<in> \<F> Q\<close>
                  by (metis ComplD eq_Nil_appendI initials_memI' is_processT5_S7')
                with \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close> \<open>{r. \<checkmark>(r) \<in> Q\<^sup>0} \<subseteq> \<checkmark>s(P)\<close>
                show \<open>(t, X) \<in> \<F> ((\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a) \<sqinter> SKIPS \<checkmark>s(P))\<close>
                  by (simp add: failure_refine_def F_Ndet F_Mndetprefix' \<open>t = []\<close> F_SKIPS \<open>\<checkmark>s(P) \<noteq> {}\<close> subset_iff)
                     (meson ComplI UnI1 UnI2 list.distinct(1))
              next
                from \<open>(t, X) \<in> \<F> Q\<close> \<open>(\<sqinter>a \<in> UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV \<sqsubseteq>\<^sub>F Q\<close> \<open>{r. \<checkmark>(r) \<in> Q\<^sup>0} \<subseteq> \<checkmark>s(P)\<close>
                show \<open>t = e # t' \<Longrightarrow> (t, X) \<in> \<F> ((\<sqinter>a \<in> {a. ev a \<in> Q\<^sup>0} \<rightarrow> Q after a) \<sqinter> SKIPS \<checkmark>s(P))\<close> for e t'
                  by (simp add: failure_refine_def F_Ndet F_Mndetprefix' F_SKIPS F_After \<open>\<checkmark>s(P) \<noteq> {}\<close> subset_iff)
                     (metis F_T initials_memI list.distinct(1) list.inject)
              qed
            qed
            ultimately show \<open>(\<sqinter>a \<in> \<alpha>(P) \<rightarrow> y) \<sqinter> SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F Q\<close> using trans_F by blast
          qed
        qed
        thus \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F P\<close>
          by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def reachable_self)
      qed
    qed
  qed
qed

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_events_of_ticks_of_leFD :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> (  if \<alpha>(P) = {} \<and> \<checkmark>s(P) = {} then False
                            else   if \<checkmark>s(P) = {} then DF \<alpha>(P) \<sqsubseteq>\<^sub>F\<^sub>D P
                                 else   if \<alpha>(P) = {} then SKIPS \<checkmark>s(P) \<sqsubseteq>\<^sub>F\<^sub>D P
                                      else DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<alpha>(P) \<checkmark>s(P) \<sqsubseteq>\<^sub>F\<^sub>D P)\<close>
  by (metis deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_events_of_ticks_of_leF D_SKIPS deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD
            div_free_DF div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S divergence_refine_def failure_divergence_refine_def)

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_strict_events_of_strict_ticks_of_leF :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> (  if \<^bold>\<alpha>(P) = {} \<and> \<^bold>\<checkmark>\<^bold>s(P) = {} then False
                            else   if \<^bold>\<checkmark>\<^bold>s(P) = {} then DF \<^bold>\<alpha>(P) \<sqsubseteq>\<^sub>F P
                                 else   if \<^bold>\<alpha>(P) = {} then SKIPS \<^bold>\<checkmark>\<^bold>s(P) \<sqsubseteq>\<^sub>F P
                                      else DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<^bold>\<alpha>(P) \<^bold>\<checkmark>\<^bold>s(P) \<sqsubseteq>\<^sub>F P)\<close>
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_events_of_ticks_of_leF
                events_of_is_strict_events_of_or_UNIV ticks_of_is_strict_ticks_of_or_UNIV)
     (meson deadlock_free_iff_DF_strict_events_of_leF DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_subset deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIPS
            deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free trans_F
            deadlock_free_implies_div_free failure_divergence_refine_def subset_UNIV)

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_strict_events_of_strict_ticks_of_leFD :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> (  if \<^bold>\<alpha>(P) = {} \<and> \<^bold>\<checkmark>\<^bold>s(P) = {} then False
                            else   if \<^bold>\<checkmark>\<^bold>s(P) = {} then DF \<^bold>\<alpha>(P) \<sqsubseteq>\<^sub>F\<^sub>D P
                                 else   if \<^bold>\<alpha>(P) = {} then SKIPS \<^bold>\<checkmark>\<^bold>s(P) \<sqsubseteq>\<^sub>F\<^sub>D P
                                      else DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S \<^bold>\<alpha>(P) \<^bold>\<checkmark>\<^bold>s(P) \<sqsubseteq>\<^sub>F\<^sub>D P)\<close>
  by (metis deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_events_of_ticks_of_leFD
            deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_strict_events_of_strict_ticks_of_leF
            deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_implies_div_free events_of_is_strict_events_of_or_UNIV
            leFD_imp_leF ticks_of_is_strict_ticks_of_or_UNIV)



subsection \<open>Big results\<close>

text \<open>As consequences, we have very powerful results,
      and especially a ``data independence'' deadlock freeness theorem.\<close>

lemma deadlock_free_is_right:
  \<open>deadlock_free P \<longleftrightarrow> (\<forall>t \<in> \<T> P. tF t \<and> (t,      UNIV) \<notin> \<F> P)\<close>
  \<open>deadlock_free P \<longleftrightarrow> (\<forall>t \<in> \<T> P. tF t \<and> (t, ev ` UNIV) \<notin> \<F> P)\<close>
proof -
  from  deadlock_free_iff_empty_ticks_of_and_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right tickFree_traces_iff_empty_ticks_of
  show \<open>deadlock_free P \<longleftrightarrow> (\<forall>t \<in> \<T> P. tF t \<and> (t, UNIV) \<notin> \<F> P)\<close> by blast
  thus \<open>deadlock_free P \<longleftrightarrow> (\<forall>t \<in> \<T> P. tF t \<and> (t, ev ` UNIV) \<notin> \<F> P)\<close>
    by (auto intro: is_processT4)
       (metis After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps(1) deadlock_free_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_characterization
              F_imp_R_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e deadlock_free_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_characterization)
qed

end

\<comment>\<open>We may probably prove \<^term>\<open>deadlock_free P \<longleftrightarrow> (\<forall>t \<in> \<T> P. tF t \<and> (t, ev ` \<alpha>(P)) \<notin> \<F> P)\<close>\<close>



theorem data_independence_deadlock_free_Sync:
  fixes P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes df_P : \<open>deadlock_free P\<close> and df_Q : \<open>deadlock_free Q\<close>
  and hyp : \<open>events_of Q \<inter> S = {} \<or> (\<exists>y. events_of Q \<inter> S = {y} \<and> events_of P \<inter> S \<subseteq> {y})\<close>
shows \<open>deadlock_free (P \<lbrakk>S\<rbrakk> Q)\<close>
proof -
  have non_BOT : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close>
    by (simp_all add: BOT_iff_Nil_D deadlock_free_implies_div_free df_P df_Q)

  have nonempty_events : \<open>events_of P \<noteq> {}\<close> \<open>events_of Q \<noteq> {}\<close>
    by (simp_all add: df_P df_Q nonempty_events_of_if_deadlock_free)
  
  obtain a b where initial : \<open>ev a \<in> P\<^sup>0\<close> \<open>ev b \<in> Q\<^sup>0\<close>
    by (meson deadlock_free_initial_evE df_P df_Q)

  have \<open>ev a \<in> (P \<lbrakk>S\<rbrakk> Q)\<^sup>0 \<or> ev b \<in> (P \<lbrakk>S\<rbrakk> Q)\<^sup>0\<close>
    by (simp add: initials_Sync non_BOT image_iff)
       (metis events_of_iff_reachable_ev reachable_ev.intros(1) 
              Int_iff initial empty_iff hyp insert_iff subset_singleton_iff)
  hence nonempty_events_Sync: \<open>\<alpha>(P \<lbrakk>S\<rbrakk> Q) \<noteq> {}\<close>
    by (metis events_of_iff_reachable_ev empty_iff reachable_ev.intros(1))

  have * : \<open>DF (\<alpha>(P) \<union> \<alpha>(Q)) \<sqsubseteq>\<^sub>F\<^sub>D DF \<alpha>(P) \<lbrakk>S\<rbrakk> DF \<alpha>(Q)\<close>
    by (simp add: DF_FD_DF_Sync_DF hyp nonempty_events)

  also have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D P \<lbrakk>S\<rbrakk> Q\<close>
    by (meson deadlock_free_iff_DF_events_of_leFD df_P df_Q mono_Sync_FD)

  ultimately show \<open>deadlock_free (P \<lbrakk>S\<rbrakk> Q)\<close>
    by (meson DF_Univ_freeness Un_empty nonempty_events(1) trans_FD)
qed

lemma data_independence_deadlock_free_Sync_bis:
  \<open>\<lbrakk>deadlock_free P; deadlock_free Q; \<alpha>(Q) \<inter> S = {}\<rbrakk> \<Longrightarrow>
   deadlock_free (P \<lbrakk>S\<rbrakk> Q)\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  by (simp add: data_independence_deadlock_free_Sync)


text \<open>We can't expect much better without hypothesis on the processes \<^term>\<open>P\<close> and \<^term>\<open>Q\<close>.
      We can easily build the following counter example.\<close>

lemma \<open>\<exists>P Q S. deadlock_free P \<and> deadlock_free Q \<and>
               (\<exists>y z. events_of Q \<inter> S \<subseteq> {y, z} \<and> events_of P \<inter> S \<subseteq> {y, z}) \<and>
               \<not> deadlock_free (P \<lbrakk>S :: nat set\<rbrakk> Q)\<close>
proof (intro exI conjI)
  show \<open>deadlock_free (DF {0})\<close> and \<open>deadlock_free (DF {Suc 0})\<close>
    by (metis DF_Univ_freeness empty_not_insert idem_FD)+
next
  show \<open>events_of (DF {Suc 0}) \<inter> {0, Suc 0} \<subseteq> {0, Suc 0}\<close>
   and \<open>events_of (DF {0}) \<inter> {0, Suc 0} \<subseteq> {0, Suc 0}\<close> by simp_all
next
  have \<open>DF {0} \<lbrakk>{0, Suc 0}\<rbrakk> DF {Suc 0} = STOP\<close>
    by (simp add: initials_empty_iff_STOP[symmetric]
                  initials_Sync initials_DF BOT_iff_Nil_D div_free_DF)
  from this[THEN arg_cong[where f = deadlock_free]]
  show \<open>\<not> deadlock_free (DF {0} \<lbrakk>{0, Suc 0}\<rbrakk> DF {Suc 0})\<close>
    by (simp add: non_deadlock_free_STOP)
qed

end

find_theorems name:  data_independence_deadlock_free_Sync_bis

\<comment> \<open>Think about a \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close> version.\<close>


subsection \<open>Results with other references Processes \<close>

subsubsection \<open>\<^const>\<open>RUN\<close> and \<^const>\<open>non_terminating\<close>\<close>

lemma non_terminating_STOP [simp] : \<open>non_terminating STOP\<close>
  unfolding non_terminating_def by simp

lemma not_non_terminating_SKIP [simp]: \<open>\<not> non_terminating (SKIP r)\<close>
  unfolding non_terminating_is_right by (simp add: T_SKIP)

lemma not_non_terminating_BOT [simp] : \<open>\<not> non_terminating \<bottom>\<close>
  unfolding non_terminating_is_right T_BOT
  using front_tickFree_single non_tickFree_tick by (metis mem_Collect_eq)


context AfterExt begin

lemma non_terminating_iff_RUN_events_T:
  \<open>non_terminating P \<longleftrightarrow> RUN \<alpha>(P) \<sqsubseteq>\<^sub>T P\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (intro iffI)
  have RUN_subset_T: \<open>(A :: 'a set) \<subseteq> B \<Longrightarrow> RUN B \<sqsubseteq>\<^sub>T RUN A\<close> for A B
    by (drule RUN_subset_DT, unfold trace_divergence_refine_def, elim conjE, assumption)
  show \<open>RUN (events_of P) \<sqsubseteq>\<^sub>T P \<Longrightarrow> non_terminating P\<close>
    unfolding non_terminating_def by (meson RUN_subset_T UNIV_I subsetI trans_T)
next
  assume non_terminating_P: \<open>non_terminating P\<close>
  have \<open>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P \<Longrightarrow> RUN (events_of P) \<sqsubseteq>\<^sub>T Q\<close> for Q
  proof (unfold RUN_def, induct rule: reachable_processes_fix_ind_T)
    show \<open>cont (\<lambda>x. \<box>e \<in> events_of P \<rightarrow> x)\<close> by simp
  next
    fix x s
    assume hyp: \<open>\<forall>Q \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P. x \<sqsubseteq>\<^sub>T Q\<close>
    show \<open>s \<in> \<T> P \<Longrightarrow> tickFree s \<Longrightarrow> \<box>e \<in> events_of P \<rightarrow> x \<sqsubseteq>\<^sub>T P after\<^sub>\<T> s\<close>
    proof (unfold trace_refine_def, safe)
      show \<open>s \<in> \<T> P \<Longrightarrow> tickFree s \<Longrightarrow> t \<in> \<T> (P after\<^sub>\<T> s) \<Longrightarrow>
            t \<in> \<T> (\<box>e \<in> events_of P \<rightarrow> x)\<close> for t
      proof (induct t arbitrary: s)
        show \<open>[] \<in> \<T> (\<box>e\<in>events_of P \<rightarrow> x)\<close> by simp
      next
        case (Cons e t)
        from Cons.prems(1, 2) have * : \<open>P after\<^sub>\<T> s \<in> \<R>\<^sub>p\<^sub>r\<^sub>o\<^sub>c P\<close>
          by (auto simp add: reachable_processes_is)
        obtain e' where ** : \<open>e = ev e'\<close> \<open>e' \<in> events_of P\<close>
          by (meson Cons.prems(1, 3) initials_memI imageE
                    non_terminating_P initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_subset_events_of set_mp)
        from Cons.prems T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e "**"(1)
        have \<open>t \<in> \<T> (P after\<^sub>\<T> (s @ [e]))\<close> by (simp add: T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq)
        also have \<open>\<dots> \<subseteq> \<T> x\<close>
          apply (rule hyp[rule_format, unfolded trace_refine_def,
                        of \<open>P after\<^sub>\<T> (s @ [e])\<close>, simplified])
          apply (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc "**"(1) After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
          apply (rule reachable_after[OF "*" ])
          using Cons.prems(3) initials_memI F_T "**"(1) by blast
        finally have \<open>t \<in> \<T> x\<close> .
        with "**" show ?case by (auto simp add: T_Mprefix)
      qed
    qed
  qed
  with reachable_self show \<open>RUN \<alpha>(P) \<sqsubseteq>\<^sub>T P\<close> by blast
qed



lemma lifelock_free_F: \<open>lifelock_free P \<longleftrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>F P\<close>
  by (simp add: lifelock_free_is_non_terminating non_terminating_F)



end 

(*<*)
end
(*>*)
