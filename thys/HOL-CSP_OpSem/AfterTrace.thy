(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Extension of the AfterExt operator
 *
 * Copyright (c) 2023 Université Paris-Saclay, France
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

section\<open> The AfterTrace Operator \<close>

theory  AfterTrace
  imports AfterExt "HOL-CSPM.DeadlockResults"
begin


subsection \<open>Definition\<close>

text \<open>We just defined \<^term>\<open>P afterExt e\<close> for @{term [show_types] \<open>P :: '\<alpha> process\<close>}
      and @{term [show_types] \<open>e :: '\<alpha> event\<close>}.
      Since a trace of a \<^term>\<open>P\<close> is just an \<^typ>\<open>'\<alpha> event list\<close>, the following 
      inductive definition is natural.\<close>

fun AfterTrace :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> trace \<Rightarrow> '\<alpha> process\<close> (infixl \<open>afterTrace\<close> 77)
  where \<open>P afterTrace [] = P\<close>
  |     \<open>P afterTrace (e # s) = P afterExt e afterTrace s\<close>



text \<open>We can also induct backward.\<close>

lemma AfterTrace_append: \<open>P afterTrace (s @ t) = P afterTrace s afterTrace t\<close>
  apply (induct t rule: rev_induct, simp)
  apply (induct s rule: rev_induct, simp)
  by (metis AfterTrace.simps append.assoc append.right_neutral append_Cons append_Nil)

lemma AfterTrace_snoc : \<open>P afterTrace (s @ [e]) = P afterTrace s afterExt e\<close>
  by (simp add: AfterTrace_append)



text \<open>We have some immediate properties.\<close>

lemma AfterTrace_BOT : \<open>\<bottom> afterTrace s = \<bottom>\<close>
  by (induct s) (simp_all add: AfterExt_BOT)

lemma AfterTrace_STOP : \<open>STOP afterTrace s = STOP\<close>
  by (induct s) (simp_all add: AfterExt_STOP)

lemma AfterTrace_SKIP : \<open>SKIP afterTrace s = (if s = [] then SKIP else STOP)\<close>
  by (induct s) (simp_all add: AfterExt_SKIP AfterTrace_STOP)



subsection \<open>Projections\<close>

lemma F_AfterTrace : \<open>(s @ t, X) \<in> \<F> P \<Longrightarrow> (t, X) \<in> \<F> (P afterTrace s)\<close>
  apply (induct s arbitrary: t rule: rev_induct, simp)
  apply (simp add: AfterTrace_snoc F_AfterExt)
  by (metis Cons_in_T_imp_elem_ready_set F_T butlast_tl front_tickFree_butlast
            is_processT2 list.distinct(1) list.sel(1, 3) tickFree_tl)

lemma D_AfterTrace : \<open>s @ t \<in> \<D> P \<Longrightarrow> t \<in> \<D> (P afterTrace s)\<close>
  apply (induct s arbitrary: t rule: rev_induct, simp)
  apply (simp add: AfterTrace_snoc D_AfterExt)
  by (metis D_imp_front_tickFree butlast_tl front_tickFree_butlast
            list.distinct(1) list.sel(1, 3) tickFree_tl)

lemma T_AfterTrace : \<open>s @ t \<in> \<T> P \<Longrightarrow> t \<in> \<T> (P afterTrace s)\<close>
  using F_AfterTrace T_F_spec by blast


corollary ready_set_AfterTrace :
  \<open>s @ e # t \<in> \<T> P \<Longrightarrow> e \<in> ready_set (P afterTrace s)\<close>
  by (metis Cons_in_T_imp_elem_ready_set T_AfterTrace)

corollary F_imp_R_AfterTrace: \<open>(s, X) \<in> \<F> P \<Longrightarrow> X \<in> \<R> (P afterTrace s)\<close>
  by (simp add: F_AfterTrace Refusals_iff)

corollary D_imp_AfterTrace_is_BOT: \<open>s \<in> \<D> P \<Longrightarrow> P afterTrace s = \<bottom>\<close>
  by (simp add: BOT_iff_D D_AfterTrace)



subsection \<open>Monotony\<close>

lemma mono_AfterTrace : \<open>P \<sqsubseteq> Q \<Longrightarrow> P afterTrace s \<sqsubseteq> Q afterTrace s\<close>
  by (induct s rule: rev_induct) (simp_all add: mono_AfterExt AfterTrace_snoc)

lemma mono_AfterTrace_T : 
  \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> tickFree s \<Longrightarrow> P afterTrace s \<sqsubseteq>\<^sub>T Q afterTrace s\<close>
  by (induct s rule: rev_induct; simp add: AfterTrace_snoc)
     (rule mono_AfterExt_T; use is_processT3_ST in blast)

lemma mono_AfterTrace_F : 
  \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> tickFree s \<Longrightarrow> P afterTrace s \<sqsubseteq>\<^sub>F Q afterTrace s\<close>
  by (induct s rule: rev_induct; simp add: AfterTrace_snoc)
     (metis event.exhaust is_processT3_ST mono_AfterExt_F ready_set_AfterTrace)

lemma mono_AfterTrace_D : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P afterTrace s \<sqsubseteq>\<^sub>D Q afterTrace s\<close>
  by (induct s rule: rev_induct) (simp_all add: mono_AfterExt_D AfterTrace_snoc)

lemma mono_AfterTrace_FD :
  \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> P afterTrace s \<sqsubseteq>\<^sub>F\<^sub>D Q afterTrace s\<close>
  by (induct s rule: rev_induct; simp add: AfterTrace_snoc)
     (meson Cons_in_T_imp_elem_ready_set T_AfterTrace is_processT3_ST mono_AfterExt_FD)

lemma mono_AfterTrace_DT :
  \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P afterTrace s \<sqsubseteq>\<^sub>D\<^sub>T Q afterTrace s\<close>
  by (induct s rule: rev_induct; simp add: AfterTrace_snoc mono_AfterExt_DT)




subsection \<open>Another Definition of \<^const>\<open>events_of\<close>\<close>

inductive reachable_event :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> \<Rightarrow> bool\<close>
  where \<open>ev e \<in> ready_set P \<Longrightarrow> reachable_event P e\<close>
  |     \<open>reachable_event (P after f) e \<Longrightarrow> reachable_event P e\<close>


lemma events_of_iff_reachable_event: \<open>e \<in> events_of P \<longleftrightarrow> reachable_event P e\<close>
proof (intro iffI)
  show \<open>reachable_event P e \<Longrightarrow> e \<in> events_of P\<close>
    apply (induct rule: reachable_event.induct;
           simp add: T_After events_of_def ready_set_def split: if_split_asm)
    by (meson list.set_intros(1)) (meson list.set_sel(2))
next
  assume \<open>e \<in> events_of P\<close>
  then obtain s where * : \<open>s \<in> \<T> P\<close> \<open>ev e \<in> set s\<close> unfolding events_of_def by blast
  thus \<open>reachable_event P e\<close>
  proof (induct s arbitrary: P)
    show \<open>\<And>P e. ev e \<in> set [] \<Longrightarrow> reachable_event P e\<close> by simp
  next
    case (Cons f s)
    from Cons.prems(1) is_processT3_ST 
    have * : \<open>f \<in> ready_set P\<close> unfolding ready_set_def by force
    from Cons.prems(2) consider \<open>f = ev e\<close> | \<open>ev e \<in> set s\<close> by auto
    thus \<open>reachable_event P e\<close>
    proof cases
      assume \<open>f = ev e\<close>
      from *[simplified this]
      show \<open>reachable_event P e\<close> by (rule reachable_event.intros(1))
    next
      assume \<open>ev e \<in> set s\<close>
      show \<open>reachable_event P e\<close>
      proof (cases f)
        fix f'
        assume \<open>f = ev f'\<close>
        with * Cons.prems(1) have \<open>s \<in> \<T> (P after f')\<close> by (force simp add: T_After)
        show \<open>reachable_event P e\<close>
          apply (rule reachable_event.intros(2))
          by (rule Cons.hyps[OF \<open>s \<in> \<T> (P after f')\<close> \<open>ev e \<in> set s\<close>])
      next
        from Cons.prems(1) have \<open>f = \<checkmark> \<Longrightarrow> s = []\<close> 
          by simp (metis butlast.simps(2) front_tickFree_butlast is_processT2_TR tickFree_Cons)
        thus \<open>f = \<checkmark> \<Longrightarrow> reachable_event P e\<close> 
          using \<open>ev e \<in> set s\<close> by force
      qed
    qed
  qed
qed


lemma reachable_event_BOT: \<open>reachable_event \<bottom> e\<close>
  by (simp add: reachable_event.intros(1) ready_set_BOT)

lemma not_reachable_event_STOP: \<open>\<not> reachable_event STOP e\<close>
  by (subst events_of_iff_reachable_event[symmetric])
     (unfold events_of_def, simp add: T_STOP)

lemma reachable_tick_SKIP: \<open>\<not> reachable_event SKIP \<checkmark>\<close>
  by (subst events_of_iff_reachable_event[symmetric])
     (unfold events_of_def, simp add: T_SKIP)



lemma reachable_event_iff_in_ready_set_AfterTrace:
  \<open>reachable_event P e \<longleftrightarrow> e \<in> {e| e s. ev e \<in> ready_set (P afterTrace s)}\<close>
proof - 
  have \<open>reachable_event P e \<Longrightarrow> \<exists>s. ev e \<in> ready_set (P afterTrace s)\<close>
  proof (induct rule: reachable_event.induct)
    case (1 e P)
    thus ?case by (metis AfterTrace.simps(1))
  next
    case (2 P f e)
    from "2.hyps"(2) obtain s where \<open>ev e \<in> ready_set (P after f afterTrace s)\<close> by blast
    hence \<open>ev e \<in> ready_set (P afterTrace (ev f # s))\<close> by (simp add: AfterExt_def)
    thus ?case by blast
  qed
  also have \<open>ev e \<in> ready_set (P afterTrace s) \<Longrightarrow> reachable_event P e\<close> for s
  proof (induct s arbitrary: P)
    show \<open>ev e \<in> ready_set (P afterTrace []) \<Longrightarrow> reachable_event P e\<close> for P
      by (simp add: reachable_event.intros(1))
  next
    fix f s P
    assume  hyp : \<open>ev e \<in> ready_set (P afterTrace s) \<Longrightarrow> reachable_event P e\<close> for P
    assume prem : \<open>ev e \<in> ready_set (P afterTrace (f # s))\<close>
    show \<open>reachable_event P e\<close>
    proof (cases f)
      fix f'
      assume \<open>f = ev f'\<close>
      show \<open>reachable_event P e\<close> by (rule reachable_event.intros(2)[OF hyp])
                                    (use prem in \<open>simp add: AfterExt_def \<open>f = ev f'\<close>\<close>)
    next
      case tick
      with prem show \<open>f = \<checkmark> \<Longrightarrow> reachable_event P e\<close>
        by (simp add: AfterExt_def reachable_event_BOT AfterTrace_STOP ready_set_STOP 
               split: if_split_asm)
    qed
  qed
  ultimately show ?thesis by blast
qed




subsection \<open>Characterizations for Deadlock Freeness\<close> 

lemma deadlock_free_AfterExt_characterization: 
  \<open>deadlock_free P \<longleftrightarrow> range ev \<notin> \<R> P \<and>
                       (\<forall>e \<in> ready_set P. deadlock_free (P afterExt e))\<close>
  (is \<open>deadlock_free P \<longleftrightarrow> ?rhs\<close>)
proof (intro iffI)
  have \<open>range ev \<notin> \<R> P \<longleftrightarrow> UNIV - {\<checkmark>} \<notin> \<R> P\<close>
    by (metis Diff_insert_absorb UNIV_eq_I event.simps(3) event_set image_iff)
  thus \<open>deadlock_free P \<Longrightarrow> ?rhs\<close>
    by (metis DF_FD_AfterExt Diff_Diff_Int Diff_partition Diff_subset F_T
              deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_is_right deadlock_free_def
              deadlock_free_implies_non_terminating deadlock_free_is_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P
              inf_top_left is_processT5_S2a non_tickFree_tick Refusals_iff self_append_conv2)
next
  assume assm : \<open>?rhs\<close>
  with BOT_iff_D process_charn have non_BOT : \<open>P \<noteq> \<bottom>\<close> by (metis Refusals_iff)
  show \<open>deadlock_free P\<close>
  proof (unfold deadlock_free_F failure_refine_def, safe)
    from assm have * : \<open>range ev \<notin> \<R> P\<close>
      \<open>e \<in> ready_set P \<Longrightarrow>
       {(tl s, X) |s X. (s, X) \<in> \<F> P \<and> s \<noteq> [] \<and> hd s = e} \<subseteq> \<F> (DF UNIV)\<close> for e
      by (simp_all add: deadlock_free_F failure_refine_def F_AfterExt non_BOT)

    fix s X
    assume ** : \<open>(s, X) \<in> \<F> P\<close>
    show \<open>(s, X) \<in> \<F> (DF UNIV)\<close>
    proof (cases s)
      show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> (DF UNIV)\<close>
        by (subst F_DF, simp)
           (metis "*"(1) "**" Refusals_iff image_subset_iff is_processT4)
    next
      fix e s'
      assume *** : \<open>s = e # s'\<close>
      with "**" Cons_in_T_imp_elem_ready_set F_T have \<open>e \<in> ready_set P\<close> by blast
      with "*"(2)[OF this] show \<open>(s, X) \<in> \<F> (DF UNIV)\<close>
        by (subst F_DF, simp add: subset_iff)
           (metis (no_types, lifting) "*"(1) "**" "***" CollectD Refusals_iff
                  event_set hd_append2 hd_in_set in_set_conv_decomp_first insert_iff
                  is_processT6_S2 list.sel(1) list.set_intros(1) rangeE ready_set_def)
    qed
  qed
qed


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_AfterExt_characterization: 
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<longleftrightarrow> 
   UNIV \<notin> \<R> P \<and> (\<forall>e \<in> ready_set P - {\<checkmark>}. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P afterExt e))\<close>
  (is \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<longleftrightarrow> ?rhs\<close>)
proof (intro iffI)
  show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<Longrightarrow> ?rhs\<close>
    by (metis Diff_iff Nil_elem_T deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_AfterExt
              deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_is_right insertI1 Refusals_iff tickFree_Nil)
next
  assume assm : \<open>?rhs\<close>
  with BOT_iff_D process_charn have non_BOT : \<open>P \<noteq> \<bottom>\<close> by (metis Refusals_iff)
  show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P\<close>
  proof (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def failure_refine_def, safe)
    from assm have * : \<open>UNIV \<notin> \<R> P\<close>
      \<open>e \<in> ready_set P \<and> e \<noteq> \<checkmark> \<Longrightarrow>
       {(tl s, X) |s X. (s, X) \<in> \<F> P \<and> s \<noteq> [] \<and> hd s = e} \<subseteq> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)\<close> for e
      by (simp_all add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def failure_refine_def F_AfterExt non_BOT)

    fix s X
    assume ** : \<open>(s, X) \<in> \<F> P\<close>
    show \<open>(s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)\<close>
    proof (cases s)
      show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)\<close>
        by (subst F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P, simp)
           (metis "*"(1) "**" UNIV_eq_I event.exhaust Refusals_iff)
    next
      fix e s'
      assume *** : \<open>s = e # s'\<close>
      show \<open>(s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)\<close>
      proof (cases e)
        fix e'
        assume \<open>e = ev e'\<close>
        with "**" "***" Cons_in_T_imp_elem_ready_set F_T
        have \<open>e \<in> ready_set P \<and> e \<noteq> \<checkmark>\<close> by blast
        with "*"(2)[OF this] show \<open>(s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)\<close>
          by (subst F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P, simp add: subset_iff)
             (metis "**" "***" \<open>e = ev e'\<close> list.distinct(1) list.sel(1))
      next
        assume \<open>e = \<checkmark>\<close>
        hence \<open>s = [\<checkmark>]\<close>
          by (metis "**" "***" F_T append_butlast_last_id append_single_T_imp_tickFree
                    butlast.simps(2) list.distinct(1) tickFree_Cons)
        thus \<open>(s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)\<close>
          by (subst F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P, simp)
      qed
    qed
  qed
qed



end
