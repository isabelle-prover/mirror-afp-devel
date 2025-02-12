(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
 *
 * This file       : Common work for operational semantics
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

chapter \<open> Generic Operational Semantics as a Locale\<close>

(*<*)
theory  Operational_Semantics_Laws
  imports After_Trace_Operator
begin
  (*>*)


paragraph \<open>Some Properties of Monotony\<close>

lemma FD_iff_eq_Ndet: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<longleftrightarrow> P = P \<sqinter> Q\<close>
  by (auto simp add: Process_eq_spec failure_divergence_refine_def failure_refine_def
      divergence_refine_def F_Ndet D_Ndet)

lemma non_BOT_mono_Det_F :
  \<open>P = \<bottom> \<or> P' \<noteq> \<bottom> \<Longrightarrow> Q = \<bottom> \<or> Q' \<noteq> \<bottom> \<Longrightarrow> P \<sqsubseteq>\<^sub>F P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F Q' \<Longrightarrow> P \<box> Q \<sqsubseteq>\<^sub>F P' \<box> Q'\<close>
  using F_subset_imp_T_subset by (simp add: failure_refine_def F_Det BOT_iff_Nil_D) blast

lemma non_BOT_mono_Det_left_F  : \<open>P = \<bottom> \<or> P' \<noteq> \<bottom> \<or> Q = \<bottom> \<Longrightarrow> P \<sqsubseteq>\<^sub>F P' \<Longrightarrow> P \<box> Q \<sqsubseteq>\<^sub>F P' \<box> Q \<close>
  and non_BOT_mono_Det_right_F : \<open>Q = \<bottom> \<or> Q' \<noteq> \<bottom> \<or> P = \<bottom> \<Longrightarrow> Q \<sqsubseteq>\<^sub>F Q' \<Longrightarrow> P \<box> Q \<sqsubseteq>\<^sub>F P  \<box> Q'\<close>
  by (metis Det_is_BOT_iff idem_F non_BOT_mono_Det_F)+

lemma non_BOT_mono_Sliding_F :
  \<open>P = \<bottom> \<or> P' \<noteq> \<bottom> \<or> Q = \<bottom> \<Longrightarrow> P \<sqsubseteq>\<^sub>F P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F Q' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>F P' \<rhd> Q'\<close>
  unfolding Sliding_def by (metis Ndet_is_BOT_iff idem_F mono_Ndet_F non_BOT_mono_Det_F)



section \<open>Definition\<close>

locale OpSemTransitions = AfterExt \<Psi> \<Omega>
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> 
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    \<comment> \<open>Just declaring the types \<^typ>\<open>'a\<close> and \<^typ>\<open>'r\<close>.\<close> +
  fixes \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
  assumes \<tau>_trans_NdetL: \<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> P\<close>
    and \<tau>_trans_transitivity: \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> Q \<leadsto>\<^sub>\<tau> R \<Longrightarrow> P \<leadsto>\<^sub>\<tau> R\<close>
    and \<tau>_trans_anti_mono_initials: \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> initials Q \<subseteq> initials P\<close>
    and \<tau>_trans_mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k: \<open>e \<in> initials Q \<Longrightarrow> P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> P after\<^sub>\<checkmark> e \<leadsto>\<^sub>\<tau> Q after\<^sub>\<checkmark> e\<close>

begin

text \<open>This locale needs to be instantiated with:
      \<^item> a function @{term [show_types = true] \<Psi>} that is a placeholder for the value
        of \<^term>\<open>P after e\<close> when \<^term>\<open>ev e \<notin> initials P\<close>
      \<^item> a function @{term [show_types = true] \<Omega>} that is a placeholder for the value
        of \<^term>\<open>P after\<^sub>\<checkmark> \<checkmark>(r)\<close>
      \<^item> a binary relation @{term [show_types] \<open>(\<leadsto>\<^sub>\<tau>)\<close>} which:
        \<^item> is compatible with \<^const>\<open>Ndet\<close>
        \<^item> is transitive
        \<^item> makes \<^const>\<open>initials\<close> anti-monotonic
        \<^item> makes @{const [source] After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} monotonic.\<close>

text \<open>From the \<open>\<tau>\<close> transition \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q\<close> we derive the event transition as follows:\<close>

abbreviation ev_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>\<^bsub>e\<^esub> Q \<equiv> ev e \<in> P\<^sup>0 \<and> P after\<^sub>\<checkmark> ev e \<leadsto>\<^sub>\<tau> Q\<close>

abbreviation tick_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (\<open>_ \<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q \<equiv> \<checkmark>(r) \<in> P\<^sup>0 \<and> P after\<^sub>\<checkmark> \<checkmark>(r) \<leadsto>\<^sub>\<tau> Q\<close>

lemma ev_trans_is: \<open>P \<leadsto>\<^bsub>e\<^esub> Q \<longleftrightarrow> ev e \<in> initials P \<and> P after e \<leadsto>\<^sub>\<tau> Q\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)

lemma tick_trans_is: \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q \<longleftrightarrow> \<checkmark>(r) \<in> P\<^sup>0 \<and> \<Omega> P r \<leadsto>\<^sub>\<tau> Q\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)

lemma reverse_event_trans_is:
  \<open>e \<in> P\<^sup>0 \<and> P after\<^sub>\<checkmark> e \<leadsto>\<^sub>\<tau> Q \<longleftrightarrow> (case e of \<checkmark>(r) \<Rightarrow> P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q | ev x \<Rightarrow> P \<leadsto>\<^bsub>x\<^esub> Q)\<close>
  by (simp split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)



text \<open>From idempotence, commutativity and \<^term>\<open>\<bottom>\<close> absorbency of \<^term>\<open>(\<sqinter>)\<close>, 
      we get the following free of charge.\<close>

lemma \<tau>_trans_eq: \<open>P \<leadsto>\<^sub>\<tau> P\<close>
  and \<tau>_trans_NdetR: \<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> Q\<close>
  and BOT_\<tau>_trans_anything: \<open>\<bottom> \<leadsto>\<^sub>\<tau> P\<close>
    apply (metis Ndet_id \<tau>_trans_NdetL)
   apply (metis Ndet_commute \<tau>_trans_NdetL)
  by (metis Ndet_BOT \<tau>_trans_NdetL)

lemma BOT_ev_trans_anything: \<open>\<bottom> \<leadsto>\<^bsub>e\<^esub> P\<close>
  and BOT_tick_trans: \<open>\<bottom> \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> \<bottom> r\<close>
  by (simp_all add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_BOT \<tau>_trans_eq BOT_\<tau>_trans_anything)



text \<open>As immediate consequences of the axioms, we prove that event transitions 
      absorb \<open>\<tau>\<close> transitions on right and on left.\<close>

lemma   ev_trans_\<tau>_trans: \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P' \<leadsto>\<^sub>\<tau> P'' \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P''\<close>
  and tick_trans_\<tau>_trans: \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> P' \<leadsto>\<^sub>\<tau> P'' \<Longrightarrow> P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P''\<close>
  by (meson \<tau>_trans_transitivity)+

lemma   \<tau>_trans_ev_trans: \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P' \<leadsto>\<^bsub>e\<^esub> P'' \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P''\<close>
  and \<tau>_trans_tick_trans: \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P' \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P'' \<Longrightarrow> P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P''\<close>
  using \<tau>_trans_mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<tau>_trans_transitivity \<tau>_trans_anti_mono_initials by blast+



text \<open>We can also add these result which will be useful later.\<close>

lemma initial_tick_imp_\<tau>_trans_SKIP: \<open>P \<leadsto>\<^sub>\<tau> SKIP r\<close> if \<open>\<checkmark>(r) \<in> P\<^sup>0\<close>
proof -
  from that have \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r\<close> by (simp add: initial_tick_iff_FD_SKIP)
  with FD_iff_eq_Ndet have \<open>P = P \<sqinter> SKIP r\<close> ..
  thus \<open>P \<leadsto>\<^sub>\<tau> SKIP r\<close> by (metis \<tau>_trans_NdetR)
qed

lemma exists_tick_trans_is_initial_tick: \<open>(\<exists>P'. P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P') \<longleftrightarrow> \<checkmark>(r) \<in> P\<^sup>0\<close>
  using \<tau>_trans_eq by blast



text \<open>There is also a major property we can already prove.\<close>

lemma \<tau>_trans_imp_leT : \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close>
proof (unfold trace_refine_def, rule subsetI)
  show \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> s \<in> \<T> P\<close> for s
  proof (induct s arbitrary: P Q)
    show \<open>\<And>P. [] \<in> \<T> P\<close> by simp
  next
    fix e s P Q
    assume   hyp : \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> s \<in> \<T> P\<close> for P Q
    assume prems : \<open>P \<leadsto>\<^sub>\<tau> Q\<close> \<open>e # s \<in> \<T> Q\<close>
    from prems(2)[THEN initials_memI] have \<open>e \<in> Q\<^sup>0\<close> .
    show \<open>e # s \<in> \<T> P\<close>
    proof (cases e)
      fix r assume \<open>e = \<checkmark>(r)\<close>
      hence \<open>s = []\<close> by (metis append_Cons append_Nil append_T_imp_tickFree non_tickFree_tick prems(2))
      with \<open>e = \<checkmark>(r)\<close> \<open>P \<leadsto>\<^sub>\<tau> Q\<close>[THEN \<tau>_trans_anti_mono_initials] \<open>e # s \<in> \<T> Q\<close>
      show \<open>e # s \<in> \<T> P\<close> by (simp add: initials_def subset_iff)
    next
      fix x
      assume \<open>e = ev x\<close>
      from \<open>e \<in> Q\<^sup>0\<close> prems(2) have \<open>s \<in> \<T> (Q after\<^sub>\<checkmark> e)\<close> 
        by (simp add: \<open>e = ev x\<close> T_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      from \<tau>_trans_mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>e \<in> Q\<^sup>0\<close> \<open>P \<leadsto>\<^sub>\<tau> Q\<close>]
      have \<open>P after\<^sub>\<checkmark> e \<leadsto>\<^sub>\<tau> Q after\<^sub>\<checkmark> e\<close> .
      from hyp[OF this \<open>s \<in> \<T> (Q after\<^sub>\<checkmark> e)\<close>] have \<open>s \<in> \<T> (P after\<^sub>\<checkmark> e)\<close> .
      with \<open>e \<in> Q\<^sup>0\<close>[THEN \<open>P \<leadsto>\<^sub>\<tau> Q\<close>[THEN \<tau>_trans_anti_mono_initials, THEN set_mp]]
      show \<open>e # s \<in> \<T> P\<close> by (simp add: T_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>e = ev x\<close>)
    qed
  qed
qed



text \<open>We can now define the concept of transition with a trace 
      and demonstrate the first properties.\<close>

inductive trace_trans :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  (\<open>_ \<leadsto>\<^sup>*_ _\<close> [50, 3, 51] 50)
  where    trace_\<tau>_trans : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<leadsto>\<^sup>* [] P'\<close>
  |     trace_tick_trans : \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> P \<leadsto>\<^sup>* [\<checkmark>(r)] P'\<close>
  |  trace_Cons_ev_trans : \<open>P \<leadsto>\<^bsub>e\<^esub>  P' \<Longrightarrow> P' \<leadsto>\<^sup>* s P'' \<Longrightarrow> P \<leadsto>\<^sup>* (ev e) # s P''\<close>

lemma trace_trans_\<tau>_trans: \<open>P \<leadsto>\<^sup>*s P' \<Longrightarrow> P' \<leadsto>\<^sub>\<tau> P'' \<Longrightarrow> P \<leadsto>\<^sup>*s P''\<close>
  apply (induct rule: trace_trans.induct)
  using \<tau>_trans_transitivity trace_\<tau>_trans apply blast
  using \<tau>_trans_transitivity trace_tick_trans apply blast
  using trace_Cons_ev_trans by blast

lemma \<tau>_trans_trace_trans:  \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P' \<leadsto>\<^sup>*s P'' \<Longrightarrow> P \<leadsto>\<^sup>*s P''\<close>
  apply (rotate_tac, induct rule: trace_trans.induct)
  using \<tau>_trans_transitivity trace_\<tau>_trans apply blast
  using \<tau>_trans_tick_trans trace_trans.simps apply blast
  using \<tau>_trans_ev_trans trace_Cons_ev_trans by blast


lemma BOT_trace_trans_tickFree_anything : \<open>tickFree s \<Longrightarrow> \<bottom> \<leadsto>\<^sup>*s P\<close>
proof (induct s arbitrary: P)
  show \<open>\<And>P. tickFree [] \<Longrightarrow> \<bottom> \<leadsto>\<^sup>*[] P\<close>
    by (simp add: BOT_\<tau>_trans_anything trace_\<tau>_trans)
next
  fix e s P
  assume prem: \<open>tickFree (e # s)\<close> and hyp: \<open>tickFree s \<Longrightarrow> \<bottom> \<leadsto>\<^sup>*s P\<close> for P
  have * : \<open>tickFree s\<close> using prem by auto
  obtain a where \<open>e = ev a\<close> by (meson is_ev_def prem tickFree_Cons_iff)
  thus \<open>\<bottom> \<leadsto>\<^sup>*e # s P\<close>
    by simp (rule trace_Cons_ev_trans[OF _ hyp];
        simp add: * After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_BOT BOT_\<tau>_trans_anything)
qed



section \<open>Consequences of \<^term>\<open>P \<leadsto>\<^sup>*s Q\<close> on \<^term>\<open>\<F>\<close>, \<^term>\<open>\<T>\<close> and \<^term>\<open>\<D>\<close>\<close>

lemma trace_trans_imp_F_if_\<tau>_trans_imp_leF:
  \<open>P \<leadsto>\<^sup>*s Q \<Longrightarrow> X \<in> \<R> Q \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  if \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F Q\<close>
proof (induct rule: trace_trans.induct)
  show \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> X \<in> \<R> Q \<Longrightarrow> ([], X) \<in> \<F> P\<close> for P Q
    by (meson failure_refine_def in_mono Refusals_iff that)
next
  show \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q \<Longrightarrow> X \<in> \<R> Q \<Longrightarrow> ([\<checkmark>(r)], X) \<in> \<F> P\<close> for P Q r
    by (metis append_Nil mem_Collect_eq initials_def tick_T_F)
next
  fix P e Q s Q'
  assume * : \<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close> \<open>X \<in> \<R> Q' \<Longrightarrow> (s, X) \<in> \<F> Q\<close> \<open>X \<in> \<R> Q'\<close>
  have \<open>P after\<^sub>\<checkmark> ev e \<sqsubseteq>\<^sub>F Q\<close> using *(1) that by blast
  hence \<open>(s, X) \<in> \<F> (P after\<^sub>\<checkmark> ev e)\<close> by (simp add: failure_refine_def subsetD *(2, 3))
  thus \<open>(ev e # s, X) \<in> \<F> P\<close> by (simp add: F_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k *(1))
qed


lemma trace_trans_imp_T: \<open>P \<leadsto>\<^sup>*s Q \<Longrightarrow> s \<in> \<T> P\<close> 
proof (induct rule: trace_trans.induct)
  show \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> [] \<in> \<T> P\<close> for P Q by simp
next
  show \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q \<Longrightarrow> [\<checkmark>(r)] \<in> \<T> P\<close> for P Q r
    by (simp add: initials_def)
next
  fix P e Q s Q'
  assume * : \<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close> \<open>s \<in> \<T> Q\<close>
  have \<open>P after\<^sub>\<checkmark> ev e \<sqsubseteq>\<^sub>T Q\<close> using *(1) \<tau>_trans_imp_leT by blast
  hence \<open>s \<in> \<T> (P after\<^sub>\<checkmark> ev e)\<close> by (simp add: *(2) subsetD trace_refine_def)
  with *(1) list.collapse show \<open>ev e # s \<in> \<T> P\<close> 
    by (force simp add: T_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k initials_def)
qed


(* see if this hypothesis can be in the locale assumptions *)
(* the previous version was with (\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>D Q),
   which is a stronger assumption *)
lemma tickFree_trace_trans_BOT_imp_D_if_\<tau>_trans_BOT_imp_eq_BOT_weak:
  \<open>tickFree s \<Longrightarrow> P \<leadsto>\<^sup>*s \<bottom> \<Longrightarrow> s \<in> \<D> P\<close> 
  if \<open>\<forall>P. P \<leadsto>\<^sub>\<tau> \<bottom> \<longrightarrow> P = \<bottom>\<close>
proof (induct s arbitrary: P)
  show \<open>P \<leadsto>\<^sup>*[] \<bottom> \<Longrightarrow> [] \<in> \<D> P\<close> for P
    apply (erule trace_trans.cases)
    using BOT_iff_Nil_D that by blast+
next
  fix e s P
  assume prems : \<open>tickFree (e # s)\<close> \<open>P \<leadsto>\<^sup>*e # s \<bottom>\<close> 
  assume hyp: \<open>tickFree s \<Longrightarrow> P \<leadsto>\<^sup>*s \<bottom> \<Longrightarrow> s \<in> \<D> P\<close> for P
  from prems(1) have \<open>tickFree s\<close> by simp
  from prems(2) have \<open>P after\<^sub>\<checkmark> e \<leadsto>\<^sup>*s \<bottom>\<close>
    by (cases rule: trace_trans.cases)
      (auto simp add:  trace_\<tau>_trans intro: \<tau>_trans_trace_trans)
  show \<open>e # s \<in> \<D> P\<close>
    apply (rule trace_trans.cases[OF prems(2)])
    using hyp[OF \<open>tickFree s\<close> \<open>P after\<^sub>\<checkmark> e \<leadsto>\<^sup>*s \<bottom>\<close>] prems(1)
    by (simp_all add: D_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed



section \<open>Characterizations for \<^term>\<open>P \<leadsto>\<^sup>*s Q\<close>\<close>

lemma trace_trans_iff :
  \<open>P \<leadsto>\<^sup>* [] Q \<longleftrightarrow> P \<leadsto>\<^sub>\<tau> Q\<close>
  \<open>P \<leadsto>\<^sup>* [\<checkmark>(r)] Q \<longleftrightarrow> P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q\<close>
  \<open>P \<leadsto>\<^sup>* (ev e) # s Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^bsub>e\<^esub> Q \<and> Q \<leadsto>\<^sup>* s Q')\<close>
  \<open>(P \<leadsto>\<^sup>* s @ [f] Q') \<longleftrightarrow> 
   tickFree s \<and> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> (case f of \<checkmark>(r) \<Rightarrow> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q' | ev x \<Rightarrow> Q \<leadsto>\<^bsub>x\<^esub> Q'))\<close>
  \<open>front_tickFree (s @ t) \<Longrightarrow> (P \<leadsto>\<^sup>*s @ t Q') \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t Q')\<close>
proof -
  show f1 : \<open>\<And>P Q. P \<leadsto>\<^sup>* [] Q \<longleftrightarrow> P \<leadsto>\<^sub>\<tau> Q\<close>
    and f2 : \<open>\<And>P Q. P \<leadsto>\<^sup>* [\<checkmark>(r)] Q \<longleftrightarrow> P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub>  Q\<close>
    and f3 : \<open>\<And>P Q' e. P \<leadsto>\<^sup>* (ev e) # s Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^bsub>e\<^esub> Q \<and> Q \<leadsto>\<^sup>* s Q')\<close>
    by ((subst trace_trans.simps, auto)[1])+

  show f4 : \<open>(P \<leadsto>\<^sup>* s @ [f] Q') \<longleftrightarrow> 
             tickFree s \<and> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> (case f of \<checkmark>(r) \<Rightarrow> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q' | ev x \<Rightarrow> Q \<leadsto>\<^bsub>x\<^esub> Q'))\<close> for s f P Q'
  proof safe
    from append_T_imp_tickFree trace_trans_imp_T
    show \<open>P \<leadsto>\<^sup>*s @ [f] Q' \<Longrightarrow> tickFree s\<close> by blast
  next
    show \<open>P \<leadsto>\<^sup>*s @ [f] Q' \<Longrightarrow> \<exists>Q. P \<leadsto>\<^sup>*s Q \<and> (case f of ev x \<Rightarrow> Q \<leadsto>\<^bsub>x\<^esub> Q' | \<checkmark>(r) \<Rightarrow> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q')\<close>
    proof (induct s arbitrary: P)
      case Nil
      thus ?case 
        apply (subst (asm) trace_trans.simps, cases f; simp)
        using \<tau>_trans_eq \<tau>_trans_transitivity f1 by blast+
    next
      case (Cons e s)
      from Cons.prems have * : \<open>e \<in> initials P \<and> P after\<^sub>\<checkmark> e \<leadsto>\<^sup>*s @ [f] Q'\<close>
        by (subst (asm) trace_trans.simps)
          (auto simp add:  intro: \<tau>_trans_trace_trans)
      with Cons.hyps obtain Q
        where ** : \<open>P after\<^sub>\<checkmark> e \<leadsto>\<^sup>*s Q\<close> 
          \<open>(case f of ev x \<Rightarrow> Q \<leadsto>\<^bsub>x\<^esub> Q' | \<checkmark>(r) \<Rightarrow> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q')\<close> by blast
      have \<open>P \<leadsto>\<^sup>*e # s Q\<close>
      proof (cases e)
        fix e'
        assume \<open>e = ev e'\<close>
        thus \<open>P \<leadsto>\<^sup>*e # s Q\<close>
          apply simp
          by (rule trace_Cons_ev_trans[OF _ **(1)]) (use * \<tau>_trans_eq in blast)
      next
        from Cons.prems have \<open>e = \<checkmark>(r) \<Longrightarrow> s = []\<close> for r by (subst (asm) trace_trans.simps) auto
        thus \<open>e = \<checkmark>(r) \<Longrightarrow> P \<leadsto>\<^sup>*e # s Q\<close> for r using * **(1) f1 f2 trace_tick_trans by auto
      qed
      with "**"(2) show \<open>\<exists>Q. P \<leadsto>\<^sup>* e # s Q \<and> (case f of ev x \<Rightarrow> Q \<leadsto>\<^bsub>x\<^esub> Q' | \<checkmark>(r) \<Rightarrow> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q')\<close> by blast
    qed
  next
    show \<open>tickFree s \<Longrightarrow> P \<leadsto>\<^sup>*s Q \<Longrightarrow> (case f of ev x \<Rightarrow> Q \<leadsto>\<^bsub>x\<^esub> Q' | \<checkmark>(r) \<Rightarrow> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q')
          \<Longrightarrow> P \<leadsto>\<^sup>*s @ [f] Q'\<close> for Q
    proof (induct s arbitrary: P Q)
      show \<open>tickFree [] \<Longrightarrow> P \<leadsto>\<^sup>*[] Q \<Longrightarrow>
            (case f of ev x \<Rightarrow> Q \<leadsto>\<^bsub>x\<^esub> Q' | \<checkmark>(r) \<Rightarrow> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q') \<Longrightarrow> P \<leadsto>\<^sup>*[] @ [f] Q'\<close> for P Q
        apply (cases f; simp add: f1 f2)
         apply (meson \<tau>_trans_eq \<tau>_trans_ev_trans trace_Cons_ev_trans trace_\<tau>_trans)
        using \<tau>_trans_tick_trans trace_tick_trans by blast
    next
      case (Cons e s)
      from Cons.prems(2) have * : \<open>e \<in> initials P \<and> P after\<^sub>\<checkmark> e \<leadsto>\<^sup>*s Q\<close>
        by (subst (asm) trace_trans.simps)
          (auto simp add: f1 intro: \<tau>_trans_trace_trans)
      show ?case
      proof (cases e)
        fix e'
        assume \<open>e = ev e'\<close>
        thus \<open>P \<leadsto>\<^sup>*(e # s) @ [f] Q'\<close> 
          by (cases f; simp)
            (metis (no_types, lifting) "*" Cons.hyps Cons.prems(1, 3) 
              \<tau>_trans_eq tickFree_Cons_iff trace_trans.simps)+
      next
        show \<open>e = \<checkmark>(r) \<Longrightarrow> P \<leadsto>\<^sup>*(e # s) @ [f] Q'\<close> for r using Cons.prems(1) by auto
      qed
    qed
  qed

  show \<open>front_tickFree (s @ t) \<Longrightarrow> P \<leadsto>\<^sup>*s @ t Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t Q')\<close>
  proof (induct t arbitrary: Q' rule: rev_induct)
    show \<open>P \<leadsto>\<^sup>*s @ [] Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*[] Q')\<close> for Q'
      by (metis \<tau>_trans_eq append.right_neutral trace_trans_\<tau>_trans f1)
  next
    case (snoc e t)
    from snoc.prems have $ : \<open>tickFree s\<close> \<open>tickFree t\<close> 
      by (simp_all add: front_tickFree_append_iff)
    show \<open>P \<leadsto>\<^sup>*s @ t @ [e] Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t @ [e] Q')\<close>
    proof (intro iffI)
      assume assm : \<open>P \<leadsto>\<^sup>*s @ t @ [e] Q'\<close>
      from f4[of P \<open>s @ t\<close> e Q', simplified] assm "$" obtain Q
        where * : \<open>P \<leadsto>\<^sup>*s @ t Q\<close> \<open>case e of ev x \<Rightarrow> Q \<leadsto>\<^bsub>x\<^esub> Q' | \<checkmark>(r) \<Rightarrow> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q'\<close> by blast
      obtain R where ** : \<open>P \<leadsto>\<^sup>*s R\<close> \<open>R \<leadsto>\<^sup>*t Q\<close>
        by (metis "*"(1) append.assoc front_tickFree_dw_closed snoc.hyps snoc.prems)
      show \<open>\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t @ [e] Q'\<close>
      proof (intro exI conjI)
        show \<open>P \<leadsto>\<^sup>*s R\<close> by (fact "**"(1))
      next
        from "*"(2) "**"(2) show \<open>R \<leadsto>\<^sup>*t @ [e] Q'\<close> by (simp add: f4 "$"(2)) blast
      qed
    next
      assume \<open>\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t @ [e] Q'\<close>
      then obtain Q where * : \<open>P \<leadsto>\<^sup>*s Q\<close> \<open>Q \<leadsto>\<^sup>*t @ [e] Q'\<close> by blast
      from f4[of Q t e Q', simplified this(2)]
      obtain R where \<open>Q \<leadsto>\<^sup>*t R\<close> \<open>case e of ev x \<Rightarrow> R \<leadsto>\<^bsub>x\<^esub> Q' | \<checkmark>(r) \<Rightarrow> R \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q'\<close> by blast
      with "*"(1) show \<open>P \<leadsto>\<^sup>*s @ t @ [e] Q'\<close>
        by (simp add: f4[of P \<open>s @ t\<close> e Q', simplified] "$", cases e; simp)
          (metis append.assoc front_tickFree_dw_closed snoc.hyps snoc.prems)+
    qed
  qed
qed



section \<open>Finally: \<^term>\<open>P \<leadsto>\<^sup>*s Q\<close> is \<^term>\<open>P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> Q\<close>\<close>

theorem trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans : 
  \<open>(P \<leadsto>\<^sup>*s Q) \<longleftrightarrow> s \<in> \<T> P \<and> P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> Q\<close>
proof -
  have \<open>s \<in> \<T> P \<Longrightarrow> (P \<leadsto>\<^sup>*s Q) \<longleftrightarrow> P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> Q\<close>
    \<comment>\<open>This is a trick to reuse the proof of this less powerful version
     (@{thm [source] trace_trans_imp_T} was not proven at the time\<open>\<dots>\<close>).\<close>
  proof (intro iffI)
    show \<open>P \<leadsto>\<^sup>*s Q \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> Q\<close>
    proof (induct s arbitrary: P Q)
      show \<open>\<And>P Q. P \<leadsto>\<^sup>*[] Q \<Longrightarrow> [] \<in> \<T> P \<Longrightarrow> P after\<^sub>\<T> [] \<leadsto>\<^sub>\<tau> Q\<close>
        using trace_trans.cases by auto
    next
      show \<open>(\<And>P Q. P \<leadsto>\<^sup>*s Q \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> Q) \<Longrightarrow> 
            P \<leadsto>\<^sup>*e # s Q \<Longrightarrow> e # s \<in> \<T> P \<Longrightarrow> P after\<^sub>\<T> (e # s) \<leadsto>\<^sub>\<tau> Q\<close> for s e P Q
        apply (cases e; simp)
        by (meson \<tau>_trans_trace_trans trace_trans_iff(3) trace_trans_imp_T)
          (metis After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps(1) T_imp_front_tickFree front_tickFree_Cons_iff
            non_tickFree_tick tickFree_Cons_iff tickFree_Nil trace_trans_iff(2))
    qed
  next
    show \<open>P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> P \<leadsto>\<^sup>*s Q\<close>
    proof (induct arbitrary: P Q rule: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.induct)
      show \<open>\<And>P Q. P after\<^sub>\<T> [] \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> [] \<in> \<T> P \<Longrightarrow> P \<leadsto>\<^sup>*[] Q\<close>
        by (simp add: trace_\<tau>_trans)
    next
      fix e and s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and Q P
      assume   hyp : \<open>P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> P \<leadsto>\<^sup>*s Q\<close> for P Q
      assume prems : \<open>P after\<^sub>\<T> (e # s) \<leadsto>\<^sub>\<tau> Q\<close> \<open>e # s \<in> \<T> P\<close>
      have * : \<open>e \<in> initials P \<and> s \<in> \<T> (P after\<^sub>\<checkmark> e)\<close>
        by (metis After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e.simps(1, 2) initials_memI 
            T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e append_Cons append_Nil prems(2))
      show \<open>P \<leadsto>\<^sup>*e # s Q\<close>
      proof (cases e)
        fix e'
        assume ** : \<open>e = ev e'\<close>
        from * ** have \<open>P \<leadsto>\<^bsub>e'\<^esub> P after\<^sub>\<checkmark> (ev e')\<close> by (simp add: \<tau>_trans_eq)
        thus \<open>P \<leadsto>\<^sup>*e # s Q\<close>
          by (subst **, rule trace_Cons_ev_trans[OF _ hyp[OF prems(1)[simplified] 
                  *[THEN conjunct2], simplified **]])
      next
        have \<open>e = \<checkmark>(r) \<Longrightarrow> s = []\<close> for r
          by (metis T_imp_front_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_Cons_iff prems(2))
        with "*" prems(1) trace_tick_trans
        show \<open>e = \<checkmark>(r) \<Longrightarrow> P \<leadsto>\<^sup>*e # s Q\<close> for r by auto
      qed
    qed
  qed
  with trace_trans_imp_T show \<open>(P \<leadsto>\<^sup>*s Q) \<longleftrightarrow> s \<in> \<T> P \<and> P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> Q\<close> by blast
qed



text \<open>As corollaries we obtain the reciprocal results of 

      @{thm trace_trans_imp_F_if_\<tau>_trans_imp_leF
            trace_trans_imp_T
            tickFree_trace_trans_BOT_imp_D_if_\<tau>_trans_BOT_imp_eq_BOT_weak}\<close>

lemma tickFree_F_imp_exists_trace_trans:
  \<open>tickFree s \<Longrightarrow> (s, X) \<in> \<F> P \<Longrightarrow> \<exists>Q. (P \<leadsto>\<^sup>*s Q) \<and> X \<in> \<R> Q\<close>
  by (meson F_T F_imp_R_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans \<tau>_trans_eq)

lemma T_imp_exists_trace_trans: \<open>s \<in> \<T> P \<Longrightarrow> \<exists>Q. P \<leadsto>\<^sup>*s Q\<close>
  using trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans \<tau>_trans_eq by blast

lemma tickFree_D_imp_trace_trans_BOT: \<open>tickFree s \<Longrightarrow> s \<in> \<D> P \<Longrightarrow> P \<leadsto>\<^sup>*s \<bottom>\<close>
  by (simp add: D_imp_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_is_BOT D_T \<tau>_trans_eq
      trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans)


text \<open>And therefore, we obtain equivalences.\<close>

lemma F_trace_trans_reality_check_weak: 
  \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> tickFree s \<Longrightarrow> 
   (s, X) \<in> \<F> P \<longleftrightarrow> (\<exists>Q. (P \<leadsto>\<^sup>*s Q) \<and> X \<in> \<R> Q)\<close>
  using tickFree_F_imp_exists_trace_trans trace_trans_imp_F_if_\<tau>_trans_imp_leF by blast

lemma T_trace_trans_reality_check: \<open>s \<in> \<T> P \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q)\<close>
  using T_imp_exists_trace_trans trace_trans_imp_T by blast

lemma D_trace_trans_reality_check_weak:
  \<open>\<forall>P. P \<leadsto>\<^sub>\<tau> \<bottom> \<longrightarrow> P = \<bottom> \<Longrightarrow> tickFree s \<Longrightarrow> s \<in> \<D> P \<longleftrightarrow> P \<leadsto>\<^sup>*s \<bottom>\<close>
  using tickFree_D_imp_trace_trans_BOT
    tickFree_trace_trans_BOT_imp_D_if_\<tau>_trans_BOT_imp_eq_BOT_weak by blast




text \<open>When we have more information on \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q\<close>, we obtain:\<close>

lemma STOP_trace_trans_iff: \<open>STOP \<leadsto>\<^sup>*s P \<longleftrightarrow> s = [] \<and> P = STOP\<close>
  using STOP_T_iff \<tau>_trans_imp_leT 
  by (subst trace_trans.simps) (auto simp add: \<tau>_trans_eq) 


lemma \<Omega>_SKIP_is_STOP_imp_\<tau>_trans_imp_leF_imp_SKIP_trace_trans_iff: 
  \<open>\<Omega> (SKIP r) r = STOP \<Longrightarrow> (\<And>P Q. P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q) \<Longrightarrow>
   (SKIP r \<leadsto>\<^sup>*s P) \<longleftrightarrow> s = [] \<and> P = SKIP r \<or> s = [\<checkmark>(r)] \<and> P = STOP\<close>
  using SKIP_F_iff STOP_F_iff
  apply (subst trace_trans.simps)
  apply (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP \<tau>_trans_eq)
  by fastforce blast+


lemma trace_trans_imp_initials_subset_initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e:
  \<open>P \<leadsto>\<^sup>*s Q \<Longrightarrow> initials Q \<subseteq> initials (P after\<^sub>\<T> s)\<close>
  using trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans 
    anti_mono_initials_T trace_trans_imp_T \<tau>_trans_imp_leT by blast


lemma imp_trace_trans_imp_initial:
  \<open>P \<leadsto>\<^sup>*(s @ e # t) Q \<Longrightarrow> e \<in> initials (P after\<^sub>\<T> s)\<close>
  using initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e trace_trans_imp_T by blast



text \<open>Under additional assumptions, we can show that the event
      transition and the trace transition are admissible.\<close>

lemma ev_trans_adm_weak[simp]:
  assumes \<tau>_trans_adm:
    \<open>\<And>u v. cont (u :: 'b :: cpo \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<leadsto>\<^sub>\<tau> v x)\<close>
    and \<Psi>_cont_hyp : \<open>cont (\<lambda>P. \<Psi> P e)\<close>
    and cont_u: \<open>cont (u :: 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close> and monofun_v : \<open>monofun v\<close>
  shows \<open>adm(\<lambda>x. u x \<leadsto>\<^bsub>e\<^esub> (v x))\<close>
  apply (intro adm_conj)
  by (fact initial_adm[OF cont_u])
    (rule \<tau>_trans_adm[OF _ monofun_v], simp add: \<Psi>_cont_hyp cont_u)

lemma tick_trans_adm_weak[simp]:
  assumes \<tau>_trans_adm:
    \<open>\<And>u v. cont (u :: 'b :: cpo \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<leadsto>\<^sub>\<tau> v x)\<close>
    and \<Omega>_cont_hyp : \<open>cont (\<lambda>P. \<Omega> P r)\<close>
    and cont_u: \<open>cont (u :: 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close> and monofun_v : \<open>monofun v\<close>
  shows \<open>adm(\<lambda>x. u x \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> (v x))\<close>
  apply (intro adm_conj)
  by (fact initial_adm[OF cont_u])
    (rule \<tau>_trans_adm[OF _ monofun_v], simp add: \<Omega>_cont_hyp cont_u)

lemma trace_trans_adm_weak[simp]:
  assumes \<tau>_trans_adm: \<open>\<And>u v. cont (u :: 'b :: cpo \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Longrightarrow> monofun v \<Longrightarrow> adm (\<lambda>x. u x \<leadsto>\<^sub>\<tau> v x)\<close>
    and After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_cont_hyps: \<open>\<forall>x. ev x \<in> set s \<longrightarrow> cont (\<lambda>P. \<Psi> P x)\<close> \<open>\<forall>r. \<checkmark>(r) \<in> set s \<longrightarrow> cont (\<lambda>P. \<Omega> P r)\<close>
    and cont_u: \<open>cont (u :: 'b :: cpo \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close> and monofun_v: \<open>monofun v\<close>
  shows \<open>adm (\<lambda>x. u x \<leadsto>\<^sup>* s (v x))\<close>
  apply (subst trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans)
  apply (intro adm_conj)
   apply (solves \<open>simp add: adm_in_T cont_u\<close>)
  by (rule \<tau>_trans_adm[OF _ monofun_v], rule After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_cont; 
      simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_cont_hyps cont_u)



section \<open>General Rules of Operational Semantics\<close>

text \<open>We can now derive some rules or the operational semantics that we are defining.\<close>

(* maybe also write the rules for event_trans when it's consequence of \<tau>_trans *)

(* assumes \<Omega>_SKIP_is_STOP : \<open>\<Omega> SKIP = STOP\<close> in a extension of the locale ?
   not really useful yet, we will just put \<Omega> SKIP instead of STOP *)

lemma SKIP_trans_tick_\<Omega>_SKIP: \<open>SKIP r \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP \<tau>_trans_eq)

lemmas SKIP_OpSem_rule = SKIP_trans_tick_\<Omega>_SKIP

text \<open>This is quite obvious, but we can get better.\<close>

lemma initial_tick_imp_tick_trans_\<Omega>_SKIP: \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> P\<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  using SKIP_trans_tick_\<Omega>_SKIP \<tau>_trans_tick_trans
    initial_tick_imp_\<tau>_trans_SKIP by blast

lemma tick_trans_imp_tick_trans_\<Omega>_SKIP : \<open>\<exists>P'. P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> P\<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  using initial_tick_imp_tick_trans_\<Omega>_SKIP by blast


(* lemma tick_trans_imp_BOT_L_or_STOP_R: \<open>P \<leadsto>\<^sub>\<checkmark> Q \<Longrightarrow> P = \<bottom> \<or> Q = STOP\<close>
  by (metis \<tau>_trans_anti_mono_initials initials_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k initials_empty_iff_STOP subset_empty)

lemma STOP_trace_trans_iff : \<open>STOP \<leadsto>\<^sup>*s P \<longleftrightarrow> s = [] \<and> P = STOP\<close>
  by (metis After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP SKIP_neq_BOT SKIP_trans_tick empty_iff trace_trans.cases
            initials_STOP tick_trans_imp_BOT_L_or_STOP_R trace_trans_iff(1))

 *)


(* 

lemma tick_trans_iff : \<open>P \<leadsto>\<^sub>\<checkmark> P' \<longleftrightarrow> P = \<bottom> \<or> P \<leadsto>\<^sub>\<tau> SKIP \<and> P' = STOP\<close>
  by (metis After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_BOT BOT_\<tau>_trans_anything SKIP_trans_tick \<tau>_trans_event_trans 
            initial_tick_imp_\<tau>_trans_SKIP tick_trans_imp_BOT_L_or_STOP_R) *)


lemma SKIP_cant_ev_trans:   \<open>\<not> SKIP r \<leadsto>\<^bsub>e\<^esub> P\<close>
  and STOP_cant_ev_trans:   \<open>\<not> STOP \<leadsto>\<^bsub>e\<^esub> P\<close>
  and STOP_cant_tick_trans: \<open>\<not> STOP \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P\<close> by simp_all




lemma ev_trans_Mprefix: \<open>e \<in> A \<Longrightarrow> \<box>a \<in> A \<rightarrow> P a \<leadsto>\<^bsub>e\<^esub> (P e)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Mprefix \<tau>_trans_eq initials_Mprefix)

lemma ev_trans_Mndetprefix: \<open>e \<in> A \<Longrightarrow> \<sqinter>a \<in> A \<rightarrow> P a \<leadsto>\<^bsub>e\<^esub> (P e)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Mndetprefix \<tau>_trans_eq initials_Mndetprefix)

lemma ev_trans_prefix: \<open>e \<rightarrow> P \<leadsto>\<^bsub>e\<^esub> P\<close>
  by (metis ev_trans_Mprefix insertI1 write0_def)

lemmas prefix_OpSem_rules = ev_trans_prefix ev_trans_Mprefix ev_trans_Mndetprefix



lemma \<tau>_trans_GlobalNdet: \<open>\<sqinter>a \<in> A. P a \<leadsto>\<^sub>\<tau> P e\<close> if \<open>e \<in> A\<close>
proof -
  have \<open>\<sqinter>a \<in> A. P a = P e \<sqinter> (\<sqinter>a \<in> A. P a)\<close>
    by (metis GlobalNdet_factorization_union GlobalNdet_unit
        empty_iff insertI1 insert_absorb insert_is_Un that)
  thus \<open>\<sqinter>a \<in> A. P a \<leadsto>\<^sub>\<tau> P e\<close> by (metis \<tau>_trans_NdetL)
qed

lemmas Ndet_OpSem_rules = \<tau>_trans_NdetL \<tau>_trans_NdetR \<tau>_trans_GlobalNdet



lemma \<tau>_trans_fix_point: \<open>cont f \<Longrightarrow> P = (\<mu> X. f X) \<Longrightarrow> P \<leadsto>\<^sub>\<tau> f P\<close>
  by (metis \<tau>_trans_eq cont_process_rec)

lemmas fix_point_OpSem_rule = \<tau>_trans_fix_point




lemma ev_trans_DetL: \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P \<box> Q \<leadsto>\<^bsub>e\<^esub> P'\<close>
  by (metis After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_is_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Ndet UnCI \<tau>_trans_NdetL \<tau>_trans_ev_trans initials_Det)

lemma ev_trans_DetR: \<open>Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> P \<box> Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>
  by (metis Det_commute ev_trans_DetL)

lemma tick_trans_DetL: \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> P \<box> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  by (metis UnCI initials_Det initial_tick_imp_tick_trans_\<Omega>_SKIP)

lemma tick_trans_DetR: \<open>Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q' \<Longrightarrow> P \<box> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  by (metis Det_commute tick_trans_DetL)

lemma ev_trans_GlobalDet:
  \<open>\<box>a \<in> A. P a \<leadsto>\<^bsub>e\<^esub> Q\<close> if \<open>a \<in> A\<close> and \<open>P a \<leadsto>\<^bsub>e\<^esub> Q\<close>
proof (cases \<open>A = {a}\<close>)
  show \<open>A = {a} \<Longrightarrow> \<box>a \<in> A. P a \<leadsto>\<^bsub>e\<^esub> Q\<close> by (simp add: \<open>P a \<leadsto>\<^bsub>e\<^esub> Q\<close>)
next
  assume \<open>A \<noteq> {a}\<close>
  with \<open>a \<in> A\<close> obtain A' where \<open>a \<notin> A'\<close> \<open>A = {a} \<union> A'\<close>
    by (metis insert_is_Un mk_disjoint_insert)
  have \<open>\<box>a \<in> A. P a = P a \<box> GlobalDet A' P\<close>
    by (simp add: \<open>A = {a} \<union> A'\<close> GlobalDet_distrib_unit_bis[OF \<open>a \<notin> A'\<close>])
  also from ev_trans_DetL \<open>P a \<leadsto>\<^bsub>e\<^esub> Q\<close> have \<open>\<dots> \<leadsto>\<^bsub>e\<^esub> Q\<close> by blast
  finally show \<open>\<box>a \<in> A. P a \<leadsto>\<^bsub>e\<^esub> Q\<close> .
qed

lemma tick_trans_GlobalDet:
  \<open>\<box>a \<in> A. P a \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close> if \<open>a \<in> A\<close> and \<open>P a \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q\<close>
proof (cases \<open>A = {a}\<close>)
  show \<open>A = {a} \<Longrightarrow> \<box>a \<in> A. P a \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
    by (simp add: initial_tick_imp_tick_trans_\<Omega>_SKIP \<open>P a \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q\<close>)
next
  assume \<open>A \<noteq> {a}\<close>
  with \<open>a \<in> A\<close> obtain A' where \<open>a \<notin> A'\<close> \<open>A = {a} \<union> A'\<close>
    by (metis insert_is_Un mk_disjoint_insert)
  have \<open>\<box>a \<in> A. P a = P a \<box> GlobalDet A' P\<close>
    by (simp add: \<open>A = {a} \<union> A'\<close> GlobalDet_distrib_unit_bis[OF \<open>a \<notin> A'\<close>])
  also from tick_trans_DetL \<open>P a \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q\<close> have \<open>\<dots> \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close> by blast
  finally show \<open>\<box>a \<in> A. P a \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close> .
qed



lemma ev_trans_SlidingL: \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P \<rhd> Q \<leadsto>\<^bsub>e\<^esub> P'\<close>
  by (simp add: Sliding_def)
    (meson \<tau>_trans_NdetL \<tau>_trans_ev_trans ev_trans_DetL)

lemma tick_trans_SlidingL: \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> P \<rhd> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  by (metis UnCI initials_Sliding initial_tick_imp_tick_trans_\<Omega>_SKIP)

lemma \<tau>_trans_SlidingR: \<open>P \<rhd> Q \<leadsto>\<^sub>\<tau> Q\<close>
  by (simp add: Sliding_def \<tau>_trans_NdetR)



(* a very good surprise *)
lemma \<tau>_trans_SeqR: \<open>P \<^bold>; Q \<leadsto>\<^sub>\<tau> Q'\<close> if \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P'\<close> and \<open>Q \<leadsto>\<^sub>\<tau> Q'\<close>
proof -
  from that(1) have \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r\<close> by (simp add: initial_tick_iff_FD_SKIP)
  with FD_iff_eq_Ndet have \<open>P = P \<sqinter> SKIP r\<close> ..
  hence \<open>P \<^bold>; Q = (P \<^bold>; Q) \<sqinter> (SKIP r \<^bold>; Q)\<close> by (metis Seq_distrib_Ndet_right)
  also have \<open>\<dots> = (P \<^bold>; Q) \<sqinter> Q\<close> by simp
  also have \<open>\<dots> \<leadsto>\<^sub>\<tau> Q\<close> by (simp add: \<tau>_trans_NdetR)
  finally show \<open>P \<^bold>; Q \<leadsto>\<^sub>\<tau> Q'\<close> by (rule \<tau>_trans_transitivity) (fact that(2))
qed

(* obvious now *)
lemma \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> P \<^bold>; Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>
  using \<tau>_trans_SeqR \<tau>_trans_eq \<tau>_trans_ev_trans by blast

(* we can't recover the rules for left side yet *)



lemma tick_trans_Hiding: \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> P \ B \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  by (simp add: initial_tick_imp_tick_trans_\<Omega>_SKIP initial_tick_imp_initial_tick_Hiding)


(* of course we can't recover \<tau>_trans yet, and idem for inside and not inside rules*)



lemma \<tau>_trans_SKIP_SyncL: \<open>P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^sub>\<tau> SKIP r \<lbrakk>S\<rbrakk> Q\<close> if \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P'\<close>
proof -
  from that have \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r\<close> by (simp add: initial_tick_iff_FD_SKIP)
  with FD_iff_eq_Ndet have \<open>P = P \<sqinter> SKIP r\<close> ..
  hence \<open>P \<lbrakk>S\<rbrakk> Q = (P \<lbrakk>S\<rbrakk> Q) \<sqinter> (SKIP r \<lbrakk>S\<rbrakk> Q)\<close> by (metis Sync_distrib_Ndet_right)
  also have \<open>\<dots> \<leadsto>\<^sub>\<tau> (SKIP r \<lbrakk>S\<rbrakk> Q)\<close> by (rule \<tau>_trans_NdetR)
  finally show \<open>P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^sub>\<tau> SKIP r \<lbrakk>S\<rbrakk> Q\<close> .
qed

lemma \<tau>_trans_SKIP_SyncR: \<open>Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^sub>\<tau> P \<lbrakk>S\<rbrakk> SKIP r\<close>
  by (metis Sync_commute \<tau>_trans_SKIP_SyncL)

lemma tick_trans_SKIP_Sync_SKIP: \<open>SKIP r \<lbrakk>S\<rbrakk> SKIP r \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  by (simp add: SKIP_trans_tick_\<Omega>_SKIP)

lemma \<open>SKIP r \<lbrakk>S\<rbrakk> SKIP r \<leadsto>\<^sub>\<tau> SKIP r\<close>
  by (simp add: \<tau>_trans_eq)



lemma tick_trans_InterruptL : \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> P \<triangle> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  and tick_trans_InterruptR : \<open>Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q' \<Longrightarrow> P \<triangle> Q \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  by (rule initial_tick_imp_tick_trans_\<Omega>_SKIP, simp add: initials_Interrupt)+


lemma tick_trans_ThrowL : \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> P \<Theta> a \<in> A. Q a \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> \<Omega> (SKIP r) r\<close>
  by (rule initial_tick_imp_tick_trans_\<Omega>_SKIP)
    (simp add: initials_Throw)

lemma ev_trans_ThrowR_inside:
  \<open>e \<in> A \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P \<Theta> a \<in> A. Q a \<leadsto>\<^bsub>e\<^esub> (Q e)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Throw initials_Throw BOT_\<tau>_trans_anything \<tau>_trans_eq)

end



section \<open>Recovering other operational rules\<close>

text \<open>By adding a \<open>\<tau>\<close>-transition hypothesis on each operator,
      we can recover the remaining operational rules.\<close>

subsection \<open>@{const [source] Det} Laws\<close>

locale OpSemTransitionsDet = OpSemTransitions \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_DetL : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<box> Q \<leadsto>\<^sub>\<tau> P' \<box> Q\<close>
begin

lemma \<tau>_trans_DetR : \<open>Q \<leadsto>\<^sub>\<tau> Q' \<Longrightarrow> P \<box> Q \<leadsto>\<^sub>\<tau> P \<box> Q'\<close>
  by (metis Det_commute \<tau>_trans_DetL)

lemmas Det_OpSem_rules = \<tau>_trans_DetL \<tau>_trans_DetR
  ev_trans_DetL ev_trans_DetR
  tick_trans_DetL tick_trans_DetR

(* discuss the fact that we don't have the exact rules from Roscoe's book here *)
end


subsection \<open>@{const [source] Det} relaxed Laws\<close>

\<comment>\<open>Introduced to recover some rules with \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> refinement.\<close>

locale OpSemTransitionsDetRelaxed = OpSemTransitions \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_DetL : \<open>P = \<bottom> \<or> P' \<noteq> \<bottom> \<or> Q = \<bottom> \<Longrightarrow> P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<box> Q \<leadsto>\<^sub>\<tau> P' \<box> Q\<close>
begin

lemma \<tau>_trans_DetR : \<open>Q = \<bottom> \<or> Q' \<noteq> \<bottom> \<or> Q = \<bottom> \<Longrightarrow> Q \<leadsto>\<^sub>\<tau> Q' \<Longrightarrow> P \<box> Q \<leadsto>\<^sub>\<tau> P \<box> Q'\<close>
  by (metis Det_commute \<tau>_trans_DetL)

lemmas Det_OpSem_rules = \<tau>_trans_DetL \<tau>_trans_DetR
  ev_trans_DetL ev_trans_DetR
  tick_trans_DetL tick_trans_DetR

(* discuss the fact that we don't have the exact rules from Roscoe's book here *)
end



subsection \<open>@{const [source] Seq} Laws\<close>

locale OpSemTransitionsSeq = OpSemTransitions \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_SeqL : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<^bold>; Q \<leadsto>\<^sub>\<tau> P' \<^bold>; Q\<close>
begin

lemma ev_trans_SeqL: \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P \<^bold>; Q \<leadsto>\<^bsub>e\<^esub> P' \<^bold>; Q\<close>
  apply (cases \<open>P = \<bottom>\<close>, solves \<open>simp add: BOT_ev_trans_anything\<close>)
  apply (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq initials_Seq image_iff disjoint_iff)
  by (meson \<tau>_trans_NdetL \<tau>_trans_SeqL \<tau>_trans_transitivity ev_trans_is)

lemmas Seq_OpSem_rules = \<tau>_trans_SeqL ev_trans_SeqL \<tau>_trans_SeqR

end



subsection \<open>@{const [source] Renaming} Laws\<close>

text \<open>We are used to it now:  we need to duplicate the locale in order
      to obtain the rules for the \<^const>\<open>Renaming\<close> operator.\<close>

locale OpSemTransitionsDuplicated = 
  OpSemTransitions\<^sub>\<alpha>: OpSemTransitions \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> \<open>(\<^sub>\<alpha>\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitions\<^sub>\<beta>: OpSemTransitions \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta> \<open>(\<^sub>\<beta>\<leadsto>\<^sub>\<tau>)\<close>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<alpha>\<leadsto>\<^sub>\<tau>\<close> 50)
    and \<Psi>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'b] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<beta>\<leadsto>\<^sub>\<tau>\<close> 50)
begin

notation OpSemTransitions\<^sub>\<alpha>.ev_trans   (\<open>_ \<^sub>\<alpha>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>\<alpha>.tick_trans (\<open>_ \<^sub>\<alpha>\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>\<beta>.ev_trans   (\<open>_ \<^sub>\<beta>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitions\<^sub>\<beta>.tick_trans (\<open>_ \<^sub>\<beta>\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)

lemma tick_trans_Renaming: \<open>P \<^sub>\<alpha>\<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> Renaming P f g \<^sub>\<beta>\<leadsto>\<^sub>\<checkmark>\<^bsub>g r\<^esub> (\<Omega>\<^sub>\<beta> (SKIP (g r)) (g r))\<close>
  by (metis OpSemTransitions\<^sub>\<beta>.initial_tick_imp_tick_trans_\<Omega>_SKIP
      Renaming_SKIP mono_Renaming_FD initial_tick_iff_FD_SKIP)

end

sublocale OpSemTransitionsDuplicated \<subseteq> AfterExtDuplicated .
    \<comment>\<open>Recovering @{thm [source] AfterExtDuplicated.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Renaming}
   (and @{thm [source] AfterDuplicated.After_Renaming})\<close>


locale OpSemTransitionsRenaming =
  OpSemTransitionsDuplicated \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> \<tau>_trans\<^sub>\<alpha> \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta> \<tau>_trans\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<alpha>\<leadsto>\<^sub>\<tau>\<close> 50)
    and \<Psi>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'b] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<beta>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_Renaming : \<open>P \<^sub>\<alpha>\<leadsto>\<^sub>\<tau> P' \<Longrightarrow> Renaming P f g \<^sub>\<beta>\<leadsto>\<^sub>\<tau> Renaming P' f g\<close>
begin

lemma ev_trans_Renaming: \<open>Renaming P f g \<^sub>\<beta>\<leadsto>\<^bsub>b\<^esub> (Renaming P' f g)\<close>
  if \<open>f a = b\<close> and \<open>P \<^sub>\<alpha>\<leadsto>\<^bsub>a\<^esub> P'\<close>
proof (cases \<open>P = \<bottom>\<close>)
  show \<open>P = \<bottom> \<Longrightarrow> Renaming P f g \<^sub>\<beta>\<leadsto>\<^bsub>b\<^esub> (Renaming P' f g)\<close>
    by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Renaming)
      (simp add: OpSemTransitions\<^sub>\<beta>.BOT_\<tau>_trans_anything
        OpSemTransitions\<^sub>\<beta>.BOT_ev_trans_anything)
next
  assume non_BOT: \<open>P \<noteq> \<bottom>\<close>
  from that have initial : \<open>\<exists>a. ev a \<in> initials P \<and> f a = b\<close> by blast
  show \<open>Renaming P f g \<^sub>\<beta>\<leadsto>\<^bsub>b\<^esub> (Renaming P' f g)\<close>
  proof (intro conjI)
    from initial show \<open>ev b \<in> (Renaming P f g)\<^sup>0\<close>
      by (force simp add: initials_Renaming image_iff) 
  next
    show \<open>OpSemTransitions\<^sub>\<beta>.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k (Renaming P f g) (ev b) \<^sub>\<beta>\<leadsto>\<^sub>\<tau> Renaming P' f g\<close>
      apply (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Renaming non_BOT initial)
      apply (rule OpSemTransitions\<^sub>\<beta>.\<tau>_trans_transitivity
          [OF OpSemTransitions\<^sub>\<beta>.\<tau>_trans_GlobalNdet[of a] \<tau>_trans_Renaming])
       apply (solves \<open>simp add: that\<close>)
      using OpSemTransitions\<^sub>\<alpha>.ev_trans_is that(2) by blast
  qed
qed

lemmas Renaming_OpSem_rules = \<tau>_trans_Renaming tick_trans_Renaming ev_trans_Renaming

end



subsection \<open>@{const [source] Hiding} Laws\<close>

locale OpSemTransitionsHiding = OpSemTransitions \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_Hiding : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \ A \<leadsto>\<^sub>\<tau> P' \ A\<close>
begin

lemma \<tau>_trans_Hiding_inside: \<open>P \ A \<leadsto>\<^sub>\<tau> P' \ A\<close> if \<open>e \<in> A\<close> and \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close>
proof -
  have \<open>P \ A \<sqsubseteq>\<^sub>F\<^sub>D P after\<^sub>\<checkmark> ev e \ A\<close>
    by (simp add: Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside that)
  with FD_iff_eq_Ndet have \<open>P \ A = (P \ A) \<sqinter> (P after\<^sub>\<checkmark> ev e \ A)\<close> ..
  moreover have \<open>\<dots> \<leadsto>\<^sub>\<tau> P after\<^sub>\<checkmark> ev e \ A\<close> by (simp add: \<tau>_trans_NdetR)
  moreover have \<open>\<dots> \<leadsto>\<^sub>\<tau> P' \ A\<close> by (simp add: \<tau>_trans_Hiding that(2))
  ultimately show \<open>P \ A \<leadsto>\<^sub>\<tau> P' \ A\<close> by (metis \<tau>_trans_transitivity)
qed


lemma ev_trans_Hiding_notin: \<open>P \ A \<leadsto>\<^bsub>e\<^esub> P' \ A\<close> if \<open>e \<notin> A\<close> and \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close>
proof -
  note initial = initial_notin_imp_initial_Hiding[OF that(2)[THEN conjunct1] that(1)]
  have \<open>(P \ A) after\<^sub>\<checkmark> ev e \<sqsubseteq>\<^sub>F\<^sub>D P after\<^sub>\<checkmark> ev e \ A\<close>
    by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin that)
  with FD_iff_eq_Ndet
  have \<open>(P \ A) after\<^sub>\<checkmark> ev e = (P \ A) after\<^sub>\<checkmark> ev e \<sqinter> (P after\<^sub>\<checkmark> ev e \ A)\<close> ..
  moreover have \<open>\<dots> \<leadsto>\<^sub>\<tau> P after\<^sub>\<checkmark> ev e \ A\<close> by (simp add: \<tau>_trans_NdetR)
  moreover have \<open>\<dots> \<leadsto>\<^sub>\<tau> P' \ A\<close> by (simp add: \<tau>_trans_Hiding that(2))
  ultimately show \<open>P \ A \<leadsto>\<^bsub>e\<^esub> P' \ A\<close> by (metis (no_types) \<tau>_trans_transitivity initial)
qed

lemmas Hiding_OpSem_rules = \<tau>_trans_Hiding tick_trans_Hiding
  ev_trans_Hiding_notin \<tau>_trans_Hiding_inside

end



subsection \<open>@{const [source] Sync} Laws\<close>

locale OpSemTransitionsSync = OpSemTransitions \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_SyncL : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^sub>\<tau> P' \<lbrakk>S\<rbrakk> Q\<close>
begin

lemma \<tau>_trans_SyncR : \<open>Q \<leadsto>\<^sub>\<tau> Q' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^sub>\<tau> P \<lbrakk>S\<rbrakk> Q'\<close>
  by (metis Sync_commute \<tau>_trans_SyncL)


lemma ev_trans_SyncL : \<open>e \<notin> S \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^bsub>e\<^esub> P' \<lbrakk>S\<rbrakk> Q\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync initials_Sync BOT_\<tau>_trans_anything image_iff)
    (meson \<tau>_trans_NdetL \<tau>_trans_SyncL \<tau>_trans_transitivity ev_trans_is)

lemma ev_trans_SyncR : \<open>e \<notin> S \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^bsub>e\<^esub> P \<lbrakk>S\<rbrakk> Q'\<close>
  by (metis Sync_commute ev_trans_SyncL)

lemma ev_trans_SyncLR :
  \<open>e \<in> S \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^bsub>e\<^esub> P' \<lbrakk>S\<rbrakk> Q'\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync BOT_\<tau>_trans_anything initials_Sync)
    (meson \<tau>_trans_SyncL \<tau>_trans_SyncR \<tau>_trans_transitivity ev_trans_is)


lemmas Sync_OpSem_rules = \<tau>_trans_SyncL \<tau>_trans_SyncR
  ev_trans_SyncL ev_trans_SyncR
  ev_trans_SyncLR
  \<tau>_trans_SKIP_SyncL \<tau>_trans_SKIP_SyncR
  tick_trans_SKIP_Sync_SKIP

end



subsection \<open>@{const [source] Sliding} Laws\<close>

locale OpSemTransitionsSliding = OpSemTransitions \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_SlidingL : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<rhd> Q \<leadsto>\<^sub>\<tau> P' \<rhd> Q\<close>
    \<comment>\<open>We just add the @{thm [source] \<tau>_trans_SlidingL} property.\<close>
begin

lemmas Sliding_OpSem_rules = \<tau>_trans_SlidingR \<tau>_trans_SlidingL
  ev_trans_SlidingL tick_trans_SlidingL

end

(* sublocale OpSemTransitionsDet \<subseteq> OpSemTransitionsSliding
  apply unfold_locales 
  apply (simp add: Sliding_def)

  oops

  We need an additional assumption: kind of monotony of \<tau>_trans on both sides *)


subsection \<open>@{const [source] Sliding} relaxed Laws\<close>

\<comment>\<open>Introduced to recover some rules with \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> refinement.\<close>

locale OpSemTransitionsSlidingRelaxed = OpSemTransitions \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_SlidingL : \<open>P = \<bottom> \<or> P' \<noteq> \<bottom> \<or> Q = \<bottom> \<Longrightarrow> P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<rhd> Q \<leadsto>\<^sub>\<tau> P' \<rhd> Q\<close>
    \<comment>\<open>We just add the @{thm [source] \<tau>_trans_SlidingL} property.\<close>
begin

lemmas Sliding_OpSem_rules = \<tau>_trans_SlidingR \<tau>_trans_SlidingL
  ev_trans_SlidingL tick_trans_SlidingL

end



subsection \<open>@{const [source] Interrupt} Laws\<close>

locale OpSemTransitionsInterruptL = OpSemTransitions \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_InterruptL : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<triangle> Q \<leadsto>\<^sub>\<tau> P' \<triangle> Q \<close>
begin

lemma ev_trans_InterruptL: \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P \<triangle> Q \<leadsto>\<^bsub>e\<^esub> P' \<triangle> Q\<close>
  apply (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Interrupt initials_Interrupt)
  using \<tau>_trans_InterruptL \<tau>_trans_NdetR \<tau>_trans_transitivity by blast


(* lemma event_trans_InterruptR: \<open>Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> P \<triangle> Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>
  oops *)
(* same issue as everywhere with \<Omega>, we need to split *)

lemma ev_trans_InterruptR: \<open>Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> P \<triangle> Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>
  apply (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Interrupt initials_Interrupt)
  using \<tau>_trans_NdetL \<tau>_trans_transitivity by blast

end


locale OpSemTransitionsInterrupt = OpSemTransitionsInterruptL \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_InterruptR : \<open>Q \<leadsto>\<^sub>\<tau> Q' \<Longrightarrow> P \<triangle> Q \<leadsto>\<^sub>\<tau> P \<triangle> Q'\<close>
    \<comment>\<open>We just add the @{thm [source] \<tau>_trans_InterruptR} property.\<close>
begin

lemmas Interrupt_OpSem_rules = \<tau>_trans_InterruptL \<tau>_trans_InterruptR
  ev_trans_InterruptL ev_trans_InterruptR
  tick_trans_InterruptL tick_trans_InterruptR

end



subsection \<open>@{const [source] Throw} Laws\<close>

locale OpSemTransitionsThrow = OpSemTransitions \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> 
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  assumes \<tau>_trans_ThrowL : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<Theta> a \<in> A. Q a \<leadsto>\<^sub>\<tau> P' \<Theta> a \<in> A. Q a\<close>
begin

(* We don't want \<tau>_trans_ThrowR in "The expressiveness of CSP extended by priority" 
   because only the first argument is active *)

lemma ev_trans_ThrowL_notin:
  \<open>e \<notin> A \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P \<Theta> a \<in> A. Q a \<leadsto>\<^bsub>e\<^esub> (P' \<Theta> a \<in> A. Q a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Throw initials_Throw BOT_\<tau>_trans_anything \<tau>_trans_ThrowL)

lemmas Throw_OpSem_rules = \<tau>_trans_ThrowL tick_trans_ThrowL
  ev_trans_ThrowL_notin ev_trans_ThrowR_inside

end





section \<open>Locales, Assemble !\<close>

text \<open>It is now time to assemble our locales.\<close>

locale OpSemTransitionsAll =
  OpSemTransitionsDet \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsSeq \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsHiding \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsSync \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsSliding \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsInterrupt \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsThrow \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close>
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)


text \<open>Of course we need to duplicate the locale for obtaining \<^const>\<open>Renaming\<close> rules.\<close>

locale OpSemTransitionsAllDuplicated = 
  OpSemTransitionsAll\<^sub>\<alpha>: OpSemTransitionsAll \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> \<open>(\<^sub>\<alpha>\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsAll\<^sub>\<beta>: OpSemTransitionsAll \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta> \<open>(\<^sub>\<beta>\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsRenaming \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> \<tau>_trans\<^sub>\<alpha> \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta> \<tau>_trans\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<alpha>\<leadsto>\<^sub>\<tau>\<close> 50)
    and \<Psi>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'b] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<^sub>\<beta>\<leadsto>\<^sub>\<tau>\<close> 50)
begin

notation OpSemTransitionsAll\<^sub>\<alpha>.ev_trans (\<open>_ \<^sub>\<alpha>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitionsAll\<^sub>\<alpha>.tick_trans (\<open>_ \<^sub>\<alpha>\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitionsAll\<^sub>\<beta>.ev_trans (\<open>_ \<^sub>\<beta>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemTransitionsAll\<^sub>\<beta>.tick_trans (\<open>_ \<^sub>\<beta>\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)

end



section \<open>\<open>(\<leadsto>\<^sub>\<tau>)\<close> instantiated with \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close> or \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>\<close>

subsection \<open>\<open>(\<leadsto>\<^sub>\<tau>)\<close> instantiated with \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>\<close>

locale OpSemFD =
  fixes \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes mono_\<Omega>_FD: \<open>\<checkmark>(r) \<in> Q\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> \<Omega> P r \<sqsubseteq>\<^sub>F\<^sub>D \<Omega> Q r\<close>


sublocale OpSemFD \<subseteq> OpSemTransitionsAll _ _ \<open>(\<sqsubseteq>\<^sub>F\<^sub>D) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
proof unfold_locales
  show \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F\<^sub>D P\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact Ndet_FD_self_left)
next      
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D R \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D R\<close> for P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact trans_FD)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Q\<^sup>0 \<subseteq> P\<^sup>0\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact anti_mono_initials_FD)
next
  show \<open>e \<in> Q\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow>
        AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> P e \<sqsubseteq>\<^sub>F\<^sub>D AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> Q e\<close> for e P Q
    by (cases e) (simp_all add: AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After.mono_After_FD mono_\<Omega>_FD)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> P \<box> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<box> Q\<close> for P P' Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (intro mono_Det_FD idem_FD)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> P \<^bold>; Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<^bold>; Q\<close> for P P' Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (intro mono_Seq_FD idem_FD)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>F\<^sub>D P' \ A\<close> for P P' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and A
    by (intro mono_Hiding_FD idem_FD)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<lbrakk>S\<rbrakk> Q\<close> for P P' Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and S
    by (intro mono_Sync_FD idem_FD)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> P \<rhd> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<rhd> Q\<close> for P P' Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (intro mono_Sliding_FD idem_FD)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<triangle> Q\<close> for P P' Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (intro mono_Interrupt_FD idem_FD)
next
  show \<open>Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>F\<^sub>D P \<triangle> Q'\<close> for P Q Q' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (intro mono_Interrupt_FD idem_FD)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>F\<^sub>D P' \<Theta> a \<in> A. Q a\<close> for P P' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and  A Q
    by (intro mono_Throw_FD idem_FD)
qed



context OpSemFD
begin

text \<open>Finally, the only remaining hypothesis is @{thm mono_\<Omega>_FD} when we instantiate our locale
      with the failure-divergence refinement \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>.\<close>

text \<open>Of course, we can strengthen some previous results.\<close>

(* no_notation failure_divergence_refine (infix \<open>\<sqsubseteq>\<^sub>F\<^sub>D\<close> 60) *)

notation failure_divergence_refine (infixl \<open>\<^sub>F\<^sub>D\<leadsto>\<^sub>\<tau>\<close> 50)
notation ev_trans (\<open>_ \<^sub>F\<^sub>D\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation tick_trans (\<open>_ \<^sub>F\<^sub>D\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation trace_trans (\<open>_ \<^sub>F\<^sub>D\<leadsto>\<^sup>*_ _\<close> [50, 3, 51] 50)


lemma trace_trans_imp_F: \<open>P \<^sub>F\<^sub>D\<leadsto>\<^sup>*s Q \<Longrightarrow> X \<in> \<R> Q \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  by (rule trace_trans_imp_F_if_\<tau>_trans_imp_leF) (simp add: leFD_imp_leF)

lemma tickFree_trace_trans_BOT_imp_D: \<open>tickFree s \<Longrightarrow> P \<^sub>F\<^sub>D\<leadsto>\<^sup>*s \<bottom> \<Longrightarrow> s \<in> \<D> P\<close>
  by (rule tickFree_trace_trans_BOT_imp_D_if_\<tau>_trans_BOT_imp_eq_BOT_weak) (simp add: FD_antisym)

lemma F_trace_trans_reality_check: \<open>tickFree s \<Longrightarrow> (s, X) \<in> \<F> P \<longleftrightarrow> (\<exists>Q. (P \<^sub>F\<^sub>D\<leadsto>\<^sup>*s Q) \<and> X \<in> \<R> Q)\<close>
  by (simp add: F_trace_trans_reality_check_weak leFD_imp_leF)

lemma D_trace_trans_reality_check: \<open>tickFree s \<Longrightarrow> s \<in> \<D> P \<longleftrightarrow> P \<^sub>F\<^sub>D\<leadsto>\<^sup>*s \<bottom>\<close>
  by (simp add: D_trace_trans_reality_check_weak FD_antisym)


lemma \<Omega>_SKIP_is_STOP_imp_SKIP_trace_trans_iff: 
  \<open>\<Omega> (SKIP r) r = STOP \<Longrightarrow> (SKIP r \<^sub>F\<^sub>D\<leadsto>\<^sup>*s P) \<longleftrightarrow> s = [] \<and> P = SKIP r \<or> s = [\<checkmark>(r)] \<and> P = STOP\<close>
  by (erule \<Omega>_SKIP_is_STOP_imp_\<tau>_trans_imp_leF_imp_SKIP_trace_trans_iff)
    (simp add: leFD_imp_leF)


lemmas \<tau>_trans_adm = le_FD_adm 

lemma ev_trans_adm[simp]:
  \<open>\<lbrakk>cont (\<lambda>P. \<Psi> P e); cont u; monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<^sub>F\<^sub>D\<leadsto>\<^bsub>e\<^esub> v x)\<close>
  by simp

lemma tick_trans_adm[simp]:
  \<open>\<lbrakk>cont (\<lambda>P. \<Omega> P r); cont u; monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<^sub>F\<^sub>D\<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> v x)\<close>
  by simp


lemma trace_trans_adm[simp]:
  \<open>\<lbrakk>\<forall>x. ev x \<in> set s \<longrightarrow> cont (\<lambda>P. \<Psi> P x);
    \<forall>r. \<checkmark>(r) \<in> set s \<longrightarrow> cont (\<lambda>P. \<Omega> P r); cont u; monofun v\<rbrakk>
   \<Longrightarrow> adm (\<lambda>x. u x \<^sub>F\<^sub>D\<leadsto>\<^sup>*s (v x))\<close>
  by simp

end

locale OpSemFDDuplicated =
  OpSemFD\<^sub>\<alpha>: OpSemFD \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> + OpSemFD\<^sub>\<beta>: OpSemFD \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'b] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>

sublocale OpSemFDDuplicated \<subseteq> OpSemTransitionsAllDuplicated _ _ \<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close> _ _ \<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>
  by (unfold_locales) (simp add: mono_Renaming_FD)




subsection \<open>\<open>(\<leadsto>\<^sub>\<tau>)\<close> instantiated with \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>\<close>

locale OpSemDT =
  fixes \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes mono_\<Omega>_DT: \<open>\<checkmark>(r) \<in> Q\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> \<Omega> P r \<sqsubseteq>\<^sub>D\<^sub>T \<Omega> Q r\<close>


sublocale OpSemDT \<subseteq> OpSemTransitionsAll _ _ \<open>(\<sqsubseteq>\<^sub>D\<^sub>T) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
proof unfold_locales
  show \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>D\<^sub>T P\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact Ndet_DT_self_left)
next      
  show \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T R \<Longrightarrow> P\<sqsubseteq>\<^sub>D\<^sub>T R\<close> for P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact trans_DT)
next
  show \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Q\<^sup>0 \<subseteq> P\<^sup>0\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact anti_mono_initials_DT)
next
  show \<open>e \<in> Q\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow>
        AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> P e \<sqsubseteq>\<^sub>D\<^sub>T AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> Q e\<close> for e P Q
    by (cases e) (simp_all add: AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After.mono_After_DT mono_\<Omega>_DT)
qed (simp_all add: mono_Det_DT mono_Seq_DT mono_Hiding_DT mono_Sync_DT
    mono_Sliding_DT mono_Interrupt_DT mono_Throw_DT)


context OpSemDT
begin

text \<open>Finally, the only remaining hypothesis is @{thm mono_\<Omega>_DT} when we instantiate our locale
      with the failure-divergence refinement \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>.\<close>

text \<open>Of course, we can strengthen some previous results.\<close>

(* no_notation failure_divergence_refine (infix \<open>\<sqsubseteq>\<^sub>D\<^sub>T\<close> 60) *)

notation trace_divergence_refine (infixl \<open>\<^sub>D\<^sub>T\<leadsto>\<^sub>\<tau>\<close> 50)
notation ev_trans (\<open>_ \<^sub>D\<^sub>T\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation tick_trans (\<open>_ \<^sub>D\<^sub>T\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation trace_trans (\<open>_ \<^sub>D\<^sub>T\<leadsto>\<^sup>*_ _\<close> [50, 3, 51] 50)


lemma tickFree_trace_trans_BOT_imp_D: \<open>tickFree s \<Longrightarrow> P \<^sub>D\<^sub>T\<leadsto>\<^sup>*s \<bottom> \<Longrightarrow> s \<in> \<D> P\<close>
  by (rule tickFree_trace_trans_BOT_imp_D_if_\<tau>_trans_BOT_imp_eq_BOT_weak)
    (meson BOT_iff_Nil_D divergence_refine_def leDT_imp_leD subsetD)

lemma D_trace_trans_reality_check: \<open>tickFree s \<Longrightarrow> s \<in> \<D> P \<longleftrightarrow> P \<^sub>D\<^sub>T\<leadsto>\<^sup>*s \<bottom>\<close>
  by (simp add: D_trace_trans_reality_check_weak BOT_iff_Nil_D tickFree_trace_trans_BOT_imp_D trace_\<tau>_trans)


lemmas \<tau>_trans_adm = le_DT_adm 

lemma ev_trans_adm[simp]:
  \<open>\<lbrakk>cont (\<lambda>P. \<Psi> P e); cont u; monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<^sub>D\<^sub>T\<leadsto>\<^bsub>e\<^esub> v x)\<close>
  by simp


lemma tick_trans_adm[simp]:
  \<open>\<lbrakk>cont (\<lambda>P. \<Omega> P r); cont u; monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<^sub>D\<^sub>T\<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> v x)\<close>
  by simp


lemma trace_trans_adm[simp]:
  \<open>\<lbrakk>\<forall>x. ev x \<in> set s \<longrightarrow> cont (\<lambda>P. \<Psi> P x);
    \<forall>r. \<checkmark>(r) \<in> set s \<longrightarrow> cont (\<lambda>P. \<Omega> P r); cont u; monofun v\<rbrakk>
   \<Longrightarrow> adm (\<lambda>x. u x \<^sub>D\<^sub>T\<leadsto>\<^sup>*s (v x))\<close>
  by simp


text \<open>If we only look at the traces and the divergences, non-deterministic and deterministic 
      choices are the same. Therefore we can obtain even stronger results for the operational rules.\<close>

lemma \<tau>_trans_Det_is_\<tau>_trans_Ndet: \<open>P \<box> Q \<^sub>D\<^sub>T\<leadsto>\<^sub>\<tau> R \<longleftrightarrow> P \<sqinter> Q \<^sub>D\<^sub>T\<leadsto>\<^sub>\<tau> R\<close>
  unfolding trace_divergence_refine_def trace_refine_def divergence_refine_def
  by (simp add: T_Det T_Ndet D_Det D_Ndet)

lemma \<tau>_trans_Sliding_is_\<tau>_trans_Ndet: \<open>P \<rhd> Q \<^sub>D\<^sub>T\<leadsto>\<^sub>\<tau> R \<longleftrightarrow> P \<sqinter> Q \<^sub>D\<^sub>T\<leadsto>\<^sub>\<tau> R\<close>
  unfolding Sliding_def by (metis Det_assoc Det_id \<tau>_trans_Det_is_\<tau>_trans_Ndet)

end

locale OpSemDTDuplicated =
  OpSemDT\<^sub>\<alpha>: OpSemDT \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> + OpSemDT\<^sub>\<beta>: OpSemDT \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'b] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>

sublocale OpSemDTDuplicated \<subseteq> OpSemTransitionsAllDuplicated _ _ \<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close> _ _ \<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>
  by (unfold_locales) (simp add: mono_Renaming_DT)




section \<open>\<open>(\<leadsto>\<^sub>\<tau>)\<close> instantiated with \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> or \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>\<close>

text \<open>We will only recover the rules for some operators.\<close>

subsection \<open>\<open>(\<leadsto>\<^sub>\<tau>)\<close> instantiated with \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>\<close>

locale OpSemF =
  fixes \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes mono_\<Omega>_F: \<open>\<checkmark>(r) \<in> Q\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> \<Omega> P r \<sqsubseteq>\<^sub>F \<Omega> Q r\<close>

sublocale OpSemF \<subseteq> OpSemTransitionsHiding _ _ \<open>(\<sqsubseteq>\<^sub>F) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> +
  OpSemTransitionsDetRelaxed _ _ \<open>(\<sqsubseteq>\<^sub>F) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> +
  OpSemTransitionsSlidingRelaxed _ _ \<open>(\<sqsubseteq>\<^sub>F) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
proof unfold_locales
  show \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>F P\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact Ndet_F_self_left)
next      
  show \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F R \<Longrightarrow> P\<sqsubseteq>\<^sub>F R\<close> for P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact trans_F)
next
  show \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Q\<^sup>0 \<subseteq> P\<^sup>0\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact anti_mono_initials_F)
next
  show \<open>e \<in> Q\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q \<Longrightarrow>
        AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> P e \<sqsubseteq>\<^sub>F AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> Q e\<close> for e P Q
    by (cases e) (simp_all add: AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After.mono_After_F mono_\<Omega>_F)
qed (simp_all add: non_BOT_mono_Det_left_F non_BOT_mono_Sliding_F mono_Hiding_F)


context OpSemF
begin

notation failure_refine (infixl \<open>\<^sub>F\<leadsto>\<^sub>\<tau>\<close> 50)
notation ev_trans (\<open>_ \<^sub>F\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation tick_trans (\<open>_ \<^sub>F\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation trace_trans (\<open>_ \<^sub>F\<leadsto>\<^sup>*_ _\<close> [50, 3, 51] 50)

text \<open>For @{const [source] Det} and @{const [source] Sliding},
      we have relaxed versions on \<open>\<tau>\<close> transitions.\<close>

end

text \<open>By duplicating the locale, we can recover a rules for \<^const>\<open>Renaming\<close>.\<close>

locale OpSemFDuplicated =
  OpSemF\<^sub>\<alpha>: OpSemF \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> + OpSemF\<^sub>\<beta>: OpSemF \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'b] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>

sublocale OpSemFDuplicated \<subseteq> OpSemTransitionsDuplicated _ _ \<open>(\<sqsubseteq>\<^sub>F)\<close> _ _ \<open>(\<sqsubseteq>\<^sub>F)\<close>
  by unfold_locales

context OpSemFDuplicated
begin

notation OpSemF\<^sub>\<alpha>.ev_trans (\<open>_ \<^sub>\<alpha>\<^sub>F\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemF\<^sub>\<alpha>.tick_trans (\<open>_ \<^sub>\<alpha>\<^sub>F\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemF\<^sub>\<beta>.ev_trans (\<open>_ \<^sub>\<beta>\<^sub>F\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50) 
notation OpSemF\<^sub>\<beta>.tick_trans (\<open>_ \<^sub>\<beta>\<^sub>F\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)

end


context OpSemF
begin

lemma trace_trans_imp_F: \<open>P \<^sub>F\<leadsto>\<^sup>*s Q \<Longrightarrow> X \<in> \<R> Q \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  by (rule trace_trans_imp_F_if_\<tau>_trans_imp_leF) simp


lemma \<Omega>_SKIP_is_STOP_imp_SKIP_trace_trans_iff: 
  \<open>\<Omega> (SKIP r) r = STOP \<Longrightarrow> (SKIP r \<^sub>F\<leadsto>\<^sup>*s P) \<longleftrightarrow> s = [] \<and> P = SKIP r \<or> s = [\<checkmark>(r)] \<and> P = STOP\<close>
  by (erule \<Omega>_SKIP_is_STOP_imp_\<tau>_trans_imp_leF_imp_SKIP_trace_trans_iff) simp



lemmas \<tau>_trans_adm = le_F_adm 

lemma ev_trans_adm[simp]:
  \<open>\<lbrakk>cont (\<lambda>P. \<Psi> P e); cont u; monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<^sub>F\<leadsto>\<^bsub>e\<^esub> v x)\<close>
  by simp

lemma tick_trans_adm[simp]:
  \<open>\<lbrakk>cont (\<lambda>P. \<Omega> P r); cont u; monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<^sub>F\<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> v x)\<close>
  by simp


lemma trace_trans_adm[simp]:
  \<open>\<lbrakk>\<forall>x. ev x \<in> set s \<longrightarrow> cont (\<lambda>P. \<Psi> P x);
    \<forall>r. \<checkmark>(r) \<in> set s \<longrightarrow> cont (\<lambda>P. \<Omega> P r);
    cont u; monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<^sub>F\<leadsto>\<^sup>*s (v x))\<close>
  by simp

end


subsection \<open>\<open>(\<leadsto>\<^sub>\<tau>)\<close> instantiated with \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>\<close>

locale OpSemTransitionsForT = 
  OpSemTransitionsDet \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsHiding \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsSliding \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close> +
  OpSemTransitionsInterrupt \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close>
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<tau>_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)

locale OpSemT =
  fixes \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes mono_\<Omega>_T: \<open>\<checkmark>(r) \<in> Q\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> \<Omega> P r \<sqsubseteq>\<^sub>T \<Omega> Q r\<close>

sublocale OpSemT \<subseteq> OpSemTransitionsForT _ _ \<open>(\<sqsubseteq>\<^sub>T) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
proof unfold_locales
  show \<open>P \<sqinter> Q \<sqsubseteq>\<^sub>T P\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact Ndet_T_self_left)
next      
  show \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>T R \<Longrightarrow> P\<sqsubseteq>\<^sub>T R\<close> for P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact trans_T)
next
  show \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Q\<^sup>0 \<subseteq> P\<^sup>0\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by (fact anti_mono_initials_T)
next
  show \<open>e \<in> Q\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow>
        AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> P e \<sqsubseteq>\<^sub>T AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> Q e\<close> for e P Q
    by (cases e) (simp_all add: AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After.mono_After_T mono_\<Omega>_T)
qed (simp_all add: mono_Det_T mono_Sliding_T mono_Hiding_T mono_Interrupt_T)

context OpSemT
begin

notation trace_refine (infixl \<open>\<^sub>T\<leadsto>\<^sub>\<tau>\<close> 50)
notation ev_trans (\<open>_ \<^sub>T\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation tick_trans (\<open>_ \<^sub>T\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation trace_trans (\<open>_ \<^sub>T\<leadsto>\<^sup>*_ _\<close> [50, 3, 51] 50)

end

text \<open>By duplicating the locale, we can recover a rules for \<^const>\<open>Renaming\<close>.\<close>

locale OpSemTDuplicated =
  OpSemT\<^sub>\<alpha>: OpSemT \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> + OpSemT\<^sub>\<beta>: OpSemT \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'b] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>

sublocale OpSemTDuplicated \<subseteq> OpSemTransitionsDuplicated _ _ \<open>(\<sqsubseteq>\<^sub>T)\<close> _ _ \<open>(\<sqsubseteq>\<^sub>T)\<close>
  by unfold_locales

context OpSemTDuplicated
begin

notation OpSemT\<^sub>\<alpha>.ev_trans (\<open>_ \<^sub>\<alpha>\<^sub>T\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemT\<^sub>\<alpha>.tick_trans (\<open>_ \<^sub>\<alpha>\<^sub>T\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
notation OpSemT\<^sub>\<beta>.ev_trans (\<open>_ \<^sub>\<beta>\<^sub>T\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50) 
notation OpSemT\<^sub>\<beta>.tick_trans (\<open>_ \<^sub>\<beta>\<^sub>T\<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)


end


context OpSemT
begin

lemmas \<tau>_trans_adm = le_T_adm 

lemma ev_trans_adm[simp]:
  \<open>\<lbrakk>cont (\<lambda>P. \<Psi> P e); cont u; monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<^sub>T\<leadsto>\<^bsub>e\<^esub> v x)\<close>
  by simp

lemma tick_trans_adm[simp]:
  \<open>\<lbrakk>cont (\<lambda>P. \<Omega> P r); cont u; monofun v\<rbrakk> \<Longrightarrow> adm (\<lambda>x. u x \<^sub>T\<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> v x)\<close>
  by simp

lemma trace_trans_adm[simp]:
  \<open>\<lbrakk>\<forall>x. ev x \<in> set s \<longrightarrow> cont (\<lambda>P. \<Psi> P x);
    \<forall>r. \<checkmark>(r) \<in> set s \<longrightarrow> cont (\<lambda>P. \<Omega> P r); cont u; monofun v\<rbrakk>
   \<Longrightarrow> adm (\<lambda>x. u x \<^sub>T\<leadsto>\<^sup>*s (v x))\<close>
  by simp


text \<open>If we only look at the traces, non-deterministic and deterministic choices are the same.
      Therefore we can obtain even stronger results for the operational rules.\<close>

lemma \<tau>_trans_Det_is_\<tau>_trans_Ndet: \<open>P \<box> Q \<^sub>T\<leadsto>\<^sub>\<tau> R \<longleftrightarrow> P \<sqinter> Q \<^sub>T\<leadsto>\<^sub>\<tau> R\<close>
  unfolding trace_divergence_refine_def trace_refine_def divergence_refine_def
  by (simp add: T_Det T_Ndet D_Det D_Ndet)

lemma \<tau>_trans_Sliding_is_\<tau>_trans_Ndet: \<open>P \<rhd> Q \<^sub>T\<leadsto>\<^sub>\<tau> R \<longleftrightarrow> P \<sqinter> Q \<^sub>T\<leadsto>\<^sub>\<tau> R\<close>
  unfolding Sliding_def by (metis Det_assoc Det_id \<tau>_trans_Det_is_\<tau>_trans_Ndet)


end

(*<*)
end
  (*>*)
