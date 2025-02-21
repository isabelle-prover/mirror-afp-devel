(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Results on events and ticks
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


chapter \<open>Results on \<open>events_of\<close> and \<open>ticks_of\<close>\<close>

(*<*)
theory Events_Ticks_CSPM_Laws
  imports CSPM_Laws
begin
  (*>*)

section \<open>Events\<close>


lemma events_of_GlobalDet :
  \<open>\<alpha>(\<box>a \<in> A. P a) = (\<Union>a\<in>A. \<alpha>(P a))\<close>
  by (simp add: events_of_def T_GlobalDet)

lemma strict_events_of_GlobalDet_subset : \<open>\<^bold>\<alpha>(\<box>a \<in> A. P a) \<subseteq> (\<Union>a\<in>A. \<^bold>\<alpha>(P a))\<close>
  by (auto simp add: strict_events_of_def GlobalDet_projs)


lemma events_of_MultiSync_subset :
  \<open>\<alpha>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># M. P a) \<subseteq> (\<Union>a \<in> set_mset M. \<alpha>(P a))\<close>
  by (induct M rule: induct_subset_mset_empty_single, simp_all)
    (meson Diff_subset_conv dual_order.trans events_of_Sync_subset)

lemma events_of_MultiInter :
  \<open>\<alpha>(\<^bold>|\<^bold>|\<^bold>| a \<in># M. P a) = (\<Union>a \<in> set_mset M. \<alpha>(P a))\<close>
  by (induct M rule: induct_subset_mset_empty_single)
    (simp_all add: events_of_Inter)

lemma strict_events_of_MultiSync_subset : 
  \<open>\<^bold>\<alpha>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># M. P a) \<subseteq> (\<Union>a \<in> set_mset M. \<^bold>\<alpha>(P a))\<close>
  by (induct M rule: induct_subset_mset_empty_single, simp_all)
    (metis (no_types, lifting) inf_sup_aci(7) le_supI2 strict_events_of_Sync_subset sup.orderE)


lemma events_of_Throw_subset :
  \<open>\<alpha>(P \<Theta> a \<in> A. Q a) \<subseteq> \<alpha>(P) \<union> (\<Union>a \<in> A \<inter> \<alpha>(P). \<alpha>(Q a))\<close>
proof (intro subsetI)
  fix e assume \<open>e \<in> \<alpha>(P \<Theta> a \<in> A. Q a)\<close>
  then obtain s where * : \<open>ev e \<in> set s\<close> \<open>s \<in> \<T> (P \<Theta> a \<in> A. Q a)\<close>
    by (simp add: events_of_def) blast
  from "*"(2) consider \<open>s \<in> \<T> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
    | t1 t2   where \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> \<open>tF t1\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
    | t1 a t2 where \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
      \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q a)\<close>
    by (simp add: T_Throw) blast
  thus \<open>e \<in> \<alpha>(P) \<union> (\<Union>a \<in> A \<inter> \<alpha>(P). \<alpha>(Q a))\<close>
  proof cases
    from "*"(1) show \<open>s \<in> \<T> P \<Longrightarrow> set s \<inter> ev ` A = {} \<Longrightarrow>
                      e \<in> \<alpha>(P) \<union> (\<Union>a \<in> A \<inter> \<alpha>(P). \<alpha>(Q a))\<close>
      by (simp add: events_of_def) blast
  next
    show \<open>\<lbrakk>s = t1 @ t2; t1 \<in> \<D> P; tF t1; set t1 \<inter> ev ` A = {}; ftF t2\<rbrakk> \<Longrightarrow>
          e \<in> \<alpha>(P) \<union> (\<Union>a \<in> A \<inter> \<alpha>(P). \<alpha>(Q a))\<close> for t1 t2
      by (metis "*"(1) D_T UnI1 events_of_memI is_processT7)
  next
    fix t1 a t2
    assume ** : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
      \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q a)\<close>
    from "*"(1) "**"(1) have \<open>ev e \<in> set (t1 @ [ev a]) \<or> ev e \<in> set t2\<close> by simp
    thus \<open>e \<in> \<alpha>(P) \<union> (\<Union>a \<in> A \<inter> \<alpha>(P). \<alpha>(Q a))\<close>
    proof (elim disjE)
      show \<open>ev e \<in> set (t1 @ [ev a]) \<Longrightarrow> e \<in> \<alpha>(P) \<union> (\<Union>a \<in> A \<inter> \<alpha>(P). \<alpha>(Q a))\<close>
        by (metis "**"(2) UnI1 events_of_memI)
    next
      show \<open>ev e \<in> set t2 \<Longrightarrow> e \<in> \<alpha>(P) \<union> (\<Union>a \<in> A \<inter> \<alpha>(P). \<alpha>(Q a))\<close>
        by (metis (no_types, lifting) "**"(2, 4, 5) Int_iff UN_iff UnI2
            events_of_memI list.set_intros(1) set_append)
    qed
  qed
qed

(* TODO: strict_events_of *)

lemma events_of_Interrupt : \<open>\<alpha>(P \<triangle> Q) = \<alpha>(P) \<union> \<alpha>(Q)\<close>
  by (safe elim!: events_of_memE,
      auto simp add: events_of_def Interrupt_projs)
    (metis append_Nil is_processT1_TR tickFree_Nil)

lemma strict_events_of_Interrupt_subset : \<open>\<^bold>\<alpha>(P \<triangle> Q) \<subseteq> \<^bold>\<alpha>(P) \<union> \<^bold>\<alpha>(Q)\<close>
  by (safe elim!:strict_events_of_memE,
      auto simp add: strict_events_of_def Interrupt_projs)
    (metis DiffI T_imp_front_tickFree is_processT7)




(* TODO: see about the generalization of that *)
(* lemma events_MultiSeq:
  \<open>events_of (SEQ a \<in>@ L. P a) =
   (\<Union>a \<in> set (take (Suc (first_elem (\<lambda>a. non_terminating (P a)) L)) L). 
    events_of (P a))\<close>
  by (subst non_terminating_MultiSeq, induct L; simp add: events_SKIP events_Seq)

lemma events_MultiSeq_subset:
  \<open>events_of (SEQ a \<in>@ L. P a) \<subseteq> (\<Union>a \<in> set L. events_of (P a))\<close>
  using in_set_takeD by (subst events_MultiSeq) fastforce *)






section \<open>Ticks\<close>

lemma ticks_of_GlobalDet:
  \<open>ticks_of (\<box>a \<in> A. P a) = (\<Union>a\<in>A. ticks_of (P a))\<close>
  by (auto simp add: ticks_of_def T_GlobalDet)

lemma strict_ticks_of_GlobalDet_subset : \<open>\<^bold>\<checkmark>\<^bold>s(\<box>a \<in> A. P a) \<subseteq> (\<Union>a\<in>A. \<^bold>\<checkmark>\<^bold>s(P a))\<close>
  by (auto simp add: strict_ticks_of_def GlobalDet_projs)







lemma ticks_of_MultiSync_subset :
  \<open>\<checkmark>s(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># M. P a) \<subseteq> (\<Union>a \<in> set_mset M. \<checkmark>s(P a))\<close>
  by (induct M rule: induct_subset_mset_empty_single, simp_all)
    (meson Diff_subset_conv dual_order.trans ticks_of_Sync_subset)

lemma strict_ticks_of_MultiSync_subset :
  \<open>\<^bold>\<checkmark>\<^bold>s(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># M. P a) \<subseteq> (\<Inter>a \<in> set_mset M. \<^bold>\<checkmark>\<^bold>s(P a))\<close>
  by (induct M rule: induct_subset_mset_empty_single, simp_all)
    (use strict_ticks_of_Sync_subset in fastforce)




lemma ticks_Throw_subset :
  \<open>\<checkmark>s(P \<Theta> a\<in>A. Q a) \<subseteq> \<checkmark>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<checkmark>s(Q a))\<close>
proof (rule subsetI, elim ticks_of_memE)
  fix t r assume \<open>t @ [\<checkmark>(r)] \<in> \<T> (P \<Theta> a\<in>A. Q a)\<close>
  from \<open>t @ [\<checkmark>(r)] \<in> \<T> (P \<Theta> a\<in>A. Q a)\<close> consider \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close>
    | t1 t2   where \<open>t @ [\<checkmark>(r)] = t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> \<open>tF t1\<close> \<open>ftF t2\<close>
    | t1 a t2 where \<open>t @ [\<checkmark>(r)] = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q a)\<close>
    unfolding T_Throw by blast
  thus \<open>r \<in> \<checkmark>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<checkmark>s(Q a))\<close>
  proof cases
    show \<open>t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> r \<in> \<checkmark>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<checkmark>s(Q a))\<close>
      by (simp add: ticks_of_memI)
  next
    show \<open>\<lbrakk>t @ [\<checkmark>(r)] = t1 @ t2; t1 \<in> \<D> P; tF t1; ftF t2\<rbrakk>
          \<Longrightarrow> r \<in> \<checkmark>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<checkmark>s(Q a))\<close> for t1 t2
      by (cases t2 rule: rev_cases, auto)
        (metis D_T append_assoc is_processT7 ticks_of_memI)
  next
    show \<open>\<lbrakk>t @ [\<checkmark>(r)] = t1 @ ev a # t2; t1 @ [ev a] \<in> \<T> P; a \<in> A; t2 \<in> \<T> (Q a)\<rbrakk>
          \<Longrightarrow> r \<in> \<checkmark>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<checkmark>s(Q a))\<close> for t1 a t2
      by (cases t2 rule: rev_cases, simp_all)
        (meson IntI events_of_memI in_set_conv_decomp ticks_of_memI)
  qed
qed


(* TODO: strict_ticks_of *)

lemma ticks_of_Interrupt : \<open>\<checkmark>s(P \<triangle> Q) = \<checkmark>s(P) \<union> \<checkmark>s(Q)\<close>
  by (safe elim!: ticks_of_memE,
      auto simp add: ticks_of_def Interrupt_projs)
    (metis append.right_neutral last_appendR snoc_eq_iff_butlast,
      metis append_Nil is_processT1_TR tickFree_Nil)

lemma strict_ticks_of_Interrupt_subset : \<open>\<^bold>\<checkmark>\<^bold>s(P \<triangle> Q) \<subseteq> \<^bold>\<checkmark>\<^bold>s(P) \<union> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
  by (safe elim!: strict_ticks_of_memE,
      auto simp add: strict_ticks_of_def Interrupt_projs)
    (meson is_processT9,
      metis (no_types, opaque_lifting) Nil_is_append_conv append_assoc
      append_butlast_last_id butlast_snoc is_processT9 last_appendR list.distinct(1))




text \<open>\<^const>\<open>events_of\<close> and \<^const>\<open>deadlock_free\<close>\<close>

lemma nonempty_events_of_if_deadlock_free: \<open>deadlock_free P \<Longrightarrow> \<alpha>(P) \<noteq> {}\<close>
  unfolding deadlock_free_def events_of_def failure_divergence_refine_def
    failure_refine_def divergence_refine_def 
  apply (simp add: div_free_DF, subst (asm) DF_unfold)
  apply (auto simp add: F_Mndetprefix write0_def F_Mprefix subset_iff)
  by (metis (full_types) Nil_elem_T T_F is_processT5_S7
      list.set_intros(1) rangeI snoc_eq_iff_butlast)

lemma nonempty_strict_events_of_if_deadlock_free: \<open>deadlock_free P \<Longrightarrow> \<^bold>\<alpha>(P) \<noteq> {}\<close>
  by (metis deadlock_free_implies_div_free events_of_is_strict_events_of_or_UNIV nonempty_events_of_if_deadlock_free)

lemma events_of_in_DF: \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> \<alpha>(P) \<subseteq> A\<close>
  by (metis anti_mono_events_of_FD events_of_DF)


lemma nonempty_events_of_if_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> (\<exists>r. [\<checkmark>(r)] \<in> \<T> P) \<or> \<alpha>(P) \<noteq> {}\<close>
  unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def events_of_def failure_refine_def 
  apply (subst (asm) DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
  apply (auto simp add: F_Mndetprefix write0_def F_Mprefix subset_iff F_Ndet F_SKIPS)
  by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust is_processT1_TR is_processT5_S7 iso_tuple_UNIV_I list.set_intros(1) self_append_conv2)


lemma events_of_in_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> \<alpha>(P) \<subseteq> A\<close>
  by (metis anti_mono_events_of_FD events_of_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)

lemma \<open>\<not> \<alpha>(P) \<subseteq> A \<Longrightarrow> \<not> DF A \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  and \<open>\<not> \<alpha>(P) \<subseteq> A \<Longrightarrow> \<not> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis anti_mono_events_of_FD events_of_DF)
    (metis anti_mono_events_of_FD events_of_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)


lemma \<open>chain Y \<Longrightarrow> \<alpha>(\<Squnion>i. Y i) = (\<Union>i. \<alpha>(Y i))\<close>
  apply (simp add: events_of_def limproc_is_thelub T_LUB D_LUB)
  apply auto

(* not provable as expected *)
  oops

lemma f1 : \<open>chain Y \<Longrightarrow> \<^bold>\<alpha>(\<Squnion>i. Y i) = (\<Union>i. \<^bold>\<alpha>(Y i))\<close>
  apply (simp add: strict_events_of_def limproc_is_thelub T_LUB D_LUB)
  apply auto
    (* TODO: break this smt *)
  by (smt (verit, ccfv_threshold) D_T DiffI INT_iff Inter_iff le_approx2T lim_proc_is_ub rangeI ub_rangeD)

find_theorems Lub 

lemma f2 : \<open>chain Y \<Longrightarrow> \<D> (Y i) = {} \<Longrightarrow> (\<Union>i. \<^bold>\<alpha>(Y i)) = \<^bold>\<alpha>(Y i)\<close>
  apply (auto simp add: strict_events_of_def)
  by (meson ND_F_dir2' chain_lemma)

(*<*)
end
  (*>*)