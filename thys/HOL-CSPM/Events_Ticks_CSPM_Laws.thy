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

lemma events_of_MultiSeq_subset :
  \<open>\<alpha>(SEQ l \<in>@ L. P l) \<subseteq> (\<Union>l \<in> set L. \<Union>r. \<alpha>(P l))\<close>
  by (induct L rule: rev_induct) (auto simp add: events_of_Seq)

lemma strict_events_of_MultiSeq_subset :
  \<open>\<^bold>\<alpha>(SEQ l \<in>@ L. P l) \<subseteq> (\<Union>l \<in> set L. \<Union>r. \<^bold>\<alpha>(P l))\<close>
  by (induct L rule: rev_induct)
    (auto intro!: subset_trans[OF strict_events_of_Seq_subset]
      split: if_split_asm)



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
    (metis append_Nil is_processT1_TR tF_Nil)

lemma strict_events_of_Interrupt_subset : \<open>\<^bold>\<alpha>(P \<triangle> Q) \<subseteq> \<^bold>\<alpha>(P) \<union> \<^bold>\<alpha>(Q)\<close>
  by (safe elim!:strict_events_of_memE,
      auto simp add: strict_events_of_def Interrupt_projs)
    (metis DiffI T_imp_ftF is_processT7)




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
      metis append_Nil is_processT1_TR tF_Nil)

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



section \<open>Minimal Events\<close>

text \<open>New in Isabelle26.\<close>

lemma minimal_events_of_GlobalDet_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(\<box>a \<in> A. P a) \<subseteq> (\<Union>a\<in>A. \<alpha>\<^sub>m\<^sub>i\<^sub>n(P a))\<close>
  by (auto simp add: minimal_events_of_def
      dest!: strict_events_of_GlobalDet_subset[THEN set_mp] D\<^sub>m\<^sub>i\<^sub>n_GlobalDet_subset[THEN set_mp])


lemma minimal_events_of_Interrupt_subset : \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<triangle> Q) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
proof (rule subsetI)
  fix a assume \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<triangle> Q)\<close>
  then consider \<open>a \<in> \<^bold>\<alpha>(P \<triangle> Q)\<close>
    | t where \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n(P \<triangle> Q)\<close> \<open>ev a \<in> set t\<close>
    by (blast dest: minimal_events_of_memD intro: strict_events_of_memI)
  thus \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
  proof cases
    show \<open>a \<in> \<^bold>\<alpha>(P \<triangle> Q) \<Longrightarrow> a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
      by (metis (no_types, lifting) Un_iff minimal_events_of_def_bis
          strict_events_of_Interrupt_subset subset_iff)
  next
    fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n(P \<triangle> Q)\<close> \<open>ev a \<in> set t\<close>
    from this(1) consider \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close>
      | t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>t1 \<notin> \<D> P\<close> \<open>tF t1\<close> \<open>t2 \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q\<close>
      by (blast dest: D\<^sub>m\<^sub>i\<^sub>n_Interrupt_subset[THEN set_mp])
    thus \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
    proof cases
      from \<open>ev a \<in> set t\<close> show \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<Longrightarrow> a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
        by (simp add: minimal_events_of_memI(2))
    next
      fix t1 t2 assume \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>t1 \<notin> \<D> P\<close> \<open>tF t1\<close> \<open>t2 \<in> \<D>\<^sub>m\<^sub>i\<^sub>n Q\<close>
      with \<open>ev a \<in> set t\<close> show \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q)\<close>
        by (auto intro: Un_iff minimal_events_of_memI)
    qed
  qed
qed


lemma minimal_events_of_Throw_subset :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P \<Theta> a \<in> A. Q a) \<subseteq> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<union> (\<Union>a \<in> A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P). \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q a))\<close>
  (is \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(?P) \<subseteq> ?rhs\<close>)
proof (rule subsetI)
  fix a assume \<open>a \<in> \<alpha>\<^sub>m\<^sub>i\<^sub>n(?P)\<close>
  then consider t where \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?P\<close> \<open>ev a \<in> set t\<close>
    | t where \<open>t \<in> \<T> ?P - \<D> ?P\<close> \<open>ev a \<in> set t\<close>
    by (blast dest: minimal_events_of_memD)
  thus \<open>a \<in> ?rhs\<close>
  proof cases
    fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?P\<close> \<open>ev a \<in> set t\<close>
    from this(1) consider \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close>
      | (D_Q) t1 b t2 where \<open>t = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> P\<close> \<open>t1 \<notin> \<D> P\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>b \<in> A\<close> \<open>t2 \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (Q b)\<close>
      by (blast dest: D\<^sub>m\<^sub>i\<^sub>n_Throw_subset[THEN set_mp])
    thus \<open>a \<in> ?rhs\<close>
    proof cases
      from \<open>ev a \<in> set t\<close> show \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<Longrightarrow> a \<in> ?rhs\<close>
        by (simp add: minimal_events_of_memI(2))
    next
      case D_Q
      have \<open>t1 @ [ev b] \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close>
        by (metis D_Q(2, 3) UnCI min_elems3 DiffI)
      from mem_D\<^sub>m\<^sub>i\<^sub>n_Un_T_Diff_D_imp_set_subset[OF this] D_Q(2)[THEN T_imp_ftF]
      have \<open>set (t1 @ [ev b]) \<subseteq> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close>
        by (auto simp add: ftF_append_iff tickFree_def disjoint_iff)
      with \<open>ev a \<in> set t\<close> D_Q(1, 5, 6) show \<open>a \<in> ?rhs\<close>
        by (auto intro: minimal_events_of_memI)
    qed
  next
    fix t assume \<open>t \<in> \<T> ?P - \<D> ?P\<close> \<open>ev a \<in> set t\<close>
    from this(1) consider (T_P) \<open>t \<in> \<T> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
      | (T_Q) t1 b t2 where \<open>t = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>b \<in> A\<close> \<open>t2 \<in> \<T> (Q b)\<close>
      by (auto simp add: Throw_projs)
    thus \<open>a \<in> ?rhs\<close>
    proof cases
      case T_P
      from T_P(1)[THEN T_imp_ftF] T_P(2) \<open>t \<in> \<T> ?P - \<D> ?P\<close> have \<open>t \<notin> \<D> P\<close>
        by (elim ftF_E, simp_all add: D_Throw)
          (fastforce, metis ftF_single is_processT9)
      with T_P(1) \<open>ev a \<in> set t\<close> show \<open>a \<in> ?rhs\<close>
        by (simp add: minimal_events_of_memI(1))
    next
      case T_Q
      with \<open>t \<in> \<T> ?P - \<D> ?P\<close> have \<open>t1 @ [ev b] \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close>
        by (simp add: Throw_projs)
          (metis T_imp_ftF event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) not_Cons_self2
            ftF_Cons_iff ftF_nonempty_append_imp min_elems3)
      from mem_D\<^sub>m\<^sub>i\<^sub>n_Un_T_Diff_D_imp_set_subset[OF this] T_Q(2)[THEN T_imp_ftF]
      have \<open>set (t1 @ [ev b]) \<subseteq> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close>
        by (auto simp add: ftF_append_iff tickFree_def disjoint_iff)
      from T_Q(1-4) \<open>t \<in> \<T> ?P - \<D> ?P\<close> have \<open>t2 \<notin> \<D> (Q b)\<close>
        by (simp add: D_Throw)
      with T_Q(5) have \<open>set t2 \<subseteq> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(Q b) \<union> tick ` \<^bold>\<checkmark>\<^bold>s(Q b)\<close>
        by (simp add: mem_D\<^sub>m\<^sub>i\<^sub>n_Un_T_Diff_D_imp_set_subset)
      with \<open>set (t1 @ [ev b]) \<subseteq> ev ` \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close> \<open>ev a \<in> set t\<close> T_Q(1, 4)
      show \<open>a \<in> ?rhs\<close> by auto
    qed
  qed
qed




section \<open>Restriction of the Events\<close>

subsection \<open>Throw\<close>

lemma Throw_is_restrictable_on_minimal_events_of :
  \<open>P \<Theta> a \<in> A. Q a = P \<Theta> a \<in> (A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)). Q a\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  have $ : \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P) \<Longrightarrow> set t \<inter> ev ` (A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) = {} \<longleftrightarrow> set t \<inter> ev ` A = {}\<close> for t
    by (drule mem_D\<^sub>m\<^sub>i\<^sub>n_Un_T_Diff_D_imp_set_subset) blast
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eqI_D\<^sub>m\<^sub>i\<^sub>n_version)
    fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?lhs\<close>
    then consider (D_P) \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close> \<open>tF t\<close> \<open>set t \<inter> ev ` A = {}\<close>
      | (D_Q) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>t1 \<notin> \<D> P\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (Q a)\<close>
      by (blast dest: D\<^sub>m\<^sub>i\<^sub>n_Throw_subset[THEN set_mp])
    thus \<open>t \<in> \<D> ?rhs\<close>
    proof cases
      case D_P thus \<open>t \<in> \<D> ?rhs\<close>
        by (auto simp add: D_Throw intro: D\<^sub>m\<^sub>i\<^sub>n_D ftF_Nil)
    next
      case D_Q
      have \<open>t1 @ [ev a] \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close>
        by (metis D_Q(2, 3) Diff_iff Un_iff min_elems3)
      from "$"[OF this] D_Q(4, 5) have \<open>set t1 \<inter> ev ` (A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) = {}\<close> \<open>a \<in> A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close> by auto
      with D_Q(1, 2, 6) show \<open>t \<in> \<D> ?rhs\<close> by (simp add: D_Throw) (metis D\<^sub>m\<^sub>i\<^sub>n_D)
    qed
  next
    fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?rhs\<close>
    then consider (D_P) \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close> \<open>tF t\<close> \<open>set t \<inter> ev ` (A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) = {}\<close>
      | (D_Q) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>t1 \<notin> \<D> P\<close> \<open>set t1 \<inter> ev ` (A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) = {}\<close> \<open>a \<in> A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close> \<open>t2 \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (Q a)\<close>
      by (blast dest: D\<^sub>m\<^sub>i\<^sub>n_Throw_subset[THEN set_mp])
    thus \<open>t \<in> \<D> ?lhs\<close>
    proof cases
      case D_P thus \<open>t \<in> \<D> ?lhs\<close>
        by (auto simp add: D_Throw "$" intro: D\<^sub>m\<^sub>i\<^sub>n_D ftF_Nil)
    next
      case D_Q
      have \<open>t1 @ [ev a] \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close>
        by (metis D_Q(2, 3) Diff_iff Un_iff min_elems3)
      from "$"[OF this] D_Q(2, 3, 4, 5) have \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close>
        by (auto dest: is_processT3_TR_append intro: minimal_events_of_memI(1))
      with D_Q(1, 2, 6) show \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_Throw) (metis D\<^sub>m\<^sub>i\<^sub>n_D)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then consider (F_P) \<open>(t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
      | (F_Q) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close>
      by (auto simp add: Throw_projs)
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      case F_P thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (auto simp add: F_Throw)
    next
      case F_Q
      from \<open>(t, X) \<in> \<F> ?lhs\<close>[THEN F_imp_ftF] \<open>t \<notin> \<D> ?lhs\<close> F_Q(1, 3) have \<open>t1 \<notin> \<D> P\<close>
        by (simp add: D_Throw)
          (metis ftF_nonempty_append_imp list.distinct(1))
      hence \<open>t1 @ [ev a] \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close>
        by (metis F_Q(2) Un_iff min_elems3 Un_Diff_cancel)
      from "$"[OF this] F_Q(3, 4) have \<open>set t1 \<inter> ev ` (A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) = {}\<close> \<open>a \<in> A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close> by auto
      with F_Q(1, 2, 5) show \<open>(t, X) \<in> \<F> ?rhs\<close> by (auto simp add: F_Throw)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    then consider (F_P) \<open>(t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` (A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) = {}\<close>
      | (F_Q) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` (A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)) = {}\<close> \<open>a \<in> A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P)\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close>
      by (auto simp add: Throw_projs)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      case F_P
      from \<open>(t, X) \<in> \<F> ?rhs\<close>[THEN F_imp_ftF] \<open>t \<notin> \<D> ?rhs\<close> F_P(2) have \<open>t \<notin> \<D> P\<close>
        by (elim ftF_E, simp_all add: D_Throw)
          (fastforce, metis ftF_single is_processT9)
      with F_P(1) have \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close> by (blast intro: F_T)
      from "$"[OF this] F_P(2) have \<open>set t \<inter> ev ` A = {}\<close> by simp
      with F_P(1) show \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_Throw)
    next
      case F_Q
      from \<open>(t, X) \<in> \<F> ?rhs\<close>[THEN F_imp_ftF] \<open>t \<notin> \<D> ?rhs\<close> F_Q(1, 3) have \<open>t1 \<notin> \<D> P\<close>
        by (simp add: D_Throw)
          (metis ftF_nonempty_append_imp list.distinct(1))
      hence \<open>t1 @ [ev a] \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P \<union> (\<T> P - \<D> P)\<close>
        by (metis F_Q(2) Un_iff min_elems3 Un_Diff_cancel)
      from "$"[OF this] F_Q(2, 3, 4) \<open>t1 \<notin> \<D> P\<close> have \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close>
        by (auto dest: is_processT3_TR_append intro: minimal_events_of_memI(1))
      with F_Q(1, 2, 5) show \<open>(t, X) \<in> \<F> ?lhs\<close> by (auto simp add: F_Throw)
    qed
  qed
qed

corollary Throw_is_restrictable_on_superset_minimal_events_of :
  \<open>\<alpha>\<^sub>m\<^sub>i\<^sub>n(P) \<subseteq> A \<Longrightarrow> P \<Theta> a \<in> S. Q a = P \<Theta> a \<in> (S \<inter> A). Q a\<close>
  by (metis Throw_is_restrictable_on_minimal_events_of inf.absorb_iff2 inf_assoc)

corollary Throw_disjoint_minimal_events_of: \<open>A \<inter> \<alpha>\<^sub>m\<^sub>i\<^sub>n(P) = {} \<Longrightarrow> P \<Theta> a \<in> A. Q a = P\<close>
  by (metis Throw_empty_set Throw_is_restrictable_on_minimal_events_of)





(*<*)
end
  (*>*)