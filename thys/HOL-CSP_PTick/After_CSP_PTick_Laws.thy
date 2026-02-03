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


chapter \<open>Operational Semantics Laws\<close>

(*<*)
theory After_CSP_PTick_Laws
  imports Basic_CSP_PTick_Laws
    "HOL-CSP_OpSem"
begin
  (*>*)



section \<open>Behaviour of \<^const>\<open>initials\<close>\<close>

subsection \<open>\<^const>\<open>TickSwap\<close>\<close>

lemma initials_TickSwap :
  \<open>(TickSwap P)\<^sup>0 = (  if P = \<bottom> then UNIV
                    else {ev a |a. ev a \<in> P\<^sup>0} \<union> {\<checkmark>((s, r)) |r s. \<checkmark>((r, s)) \<in> P\<^sup>0})\<close>
  by (auto simp add: TickSwap_is_Renaming initials_Renaming image_iff
      map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff 
      tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    (metis tick_swap.elims)



subsection \<open>Sequential Composition\<close>

lemma initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : 
  \<open>(P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0 = (  if P = \<bottom> then UNIV
                else {ev a |a. ev a \<in> P\<^sup>0} \<union> (\<Union>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0}. (Q r)\<^sup>0))\<close>
  (is \<open>_ = (if _ then _ else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<Longrightarrow> (P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0 = UNIV\<close> by simp
next
  show \<open>(P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0 = {ev a |a. ev a \<in> P\<^sup>0} \<union> (\<Union>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0}. (Q r)\<^sup>0)\<close> if \<open>P \<noteq> \<bottom>\<close>
  proof (intro subset_antisym subsetI)
    fix e assume \<open>e \<in> (P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0\<close>
    from event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust consider a where \<open>e = ev a\<close> | r where \<open>e = \<checkmark>(r)\<close> by blast
    thus \<open>e \<in> ?rhs\<close>
    proof cases
      from \<open>e \<in> (P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0\<close> \<open>P \<noteq> \<bottom>\<close> show \<open>e = ev a \<Longrightarrow> e \<in> ?rhs\<close> for a
        by (auto simp add: image_iff initials_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Cons_eq_append_conv BOT_iff_Nil_D intro: D_T dest: initials_memD)
          (use initials_memI in \<open>blast dest: initials_memD\<close>)
    next
      from \<open>e \<in> (P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0\<close> \<open>P \<noteq> \<bottom>\<close> show \<open>e = \<checkmark>(r) \<Longrightarrow> e \<in> ?rhs\<close> for r
        by (auto simp add: image_iff initials_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs BOT_iff_Nil_D Cons_eq_append_conv)
    qed
  next
    show \<open>e \<in> ?rhs \<Longrightarrow> e \<in> (P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0\<close> for e
      by (simp add: initials_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs, elim disjE exE conjE)
        (fastforce, metis list.simps(8) self_append_conv2 tickFree_Nil)
  qed
qed



subsection \<open>Synchronization Product\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0 =
   (if P = \<bottom> \<or> Q = \<bottom> then UNIV else
    {ev a |a. a \<in> S \<and> ev a \<in> P\<^sup>0 \<and> ev a \<in> Q\<^sup>0 \<or> a \<notin> S \<and> (ev a \<in> P\<^sup>0 \<or> ev a \<in> Q\<^sup>0)} \<union>
    {\<checkmark>(r_s) |r_s r s. tick_join r s = Some r_s \<and> \<checkmark>(r) \<in> P\<^sup>0 \<and> \<checkmark>(s) \<in> Q\<^sup>0})\<close>
  (is \<open>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0 = (if P = \<bottom> \<or> Q = \<bottom> then UNIV else ?rhs_ev \<union> ?rhs_tick)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<or> Q = \<bottom> \<Longrightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0 = UNIV\<close>
    by (metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff initials_BOT)
next
  show \<open>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0 = ?rhs_ev \<union> ?rhs_tick\<close> if non_BOT : \<open>\<not> (P = \<bottom> \<or> Q = \<bottom>)\<close>
  proof (intro subset_antisym subsetI)
    show \<open>e \<in> ?rhs_ev \<union> ?rhs_tick \<Longrightarrow> e \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close> for e
    proof (elim UnE)
      assume \<open>e \<in> ?rhs_ev\<close>
      then consider a where \<open>e = ev a\<close> \<open>a \<in> S\<close> \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close>
        | a where \<open>e = ev a\<close> \<open>a \<notin> S\<close> \<open>ev a \<in> P\<^sup>0 \<or> ev a \<in> Q\<^sup>0\<close> by blast
      thus \<open>e \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
      proof cases
        fix a assume \<open>e = ev a\<close> \<open>a \<in> S\<close> \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close>
        have * : \<open>[ev a] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([ev a], [ev a]), S)\<close>
          by (simp add: \<open>a \<in> S\<close>)
        from \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close> show \<open>e \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
          by (simp add: \<open>e = ev a\<close> initials_def T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (use "*" in blast)
      next
        fix a assume \<open>e = ev a\<close> \<open>a \<notin> S\<close> \<open>ev a \<in> P\<^sup>0 \<or> ev a \<in> Q\<^sup>0\<close>
        from \<open>ev a \<in> P\<^sup>0 \<or> ev a \<in> Q\<^sup>0\<close> show \<open>e \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
        proof (elim disjE)
          assume \<open>ev a \<in> P\<^sup>0\<close>
          have * : \<open>[ev a] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([ev a], []), S)\<close>
            by (simp add: \<open>a \<notin> S\<close>)
          from \<open>ev a \<in> P\<^sup>0\<close> show \<open>e \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
            by (simp add: \<open>e = ev a\<close> initials_def T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (meson "*" is_processT1_TR)
        next
          assume \<open>ev a \<in> Q\<^sup>0\<close>
          have * : \<open>[ev a] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], [ev a]), S)\<close>
            by (simp add: \<open>a \<notin> S\<close>)
          from \<open>ev a \<in> Q\<^sup>0\<close> show \<open>e \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
            by (simp add: \<open>e = ev a\<close> initials_def T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (meson "*" is_processT1_TR)
        qed
      qed
    next
      assume \<open>e \<in> ?rhs_tick\<close>
      then obtain r_s r s where \<open>tick_join r s = Some r_s\<close>
        \<open>e = \<checkmark>(r_s)\<close> \<open>\<checkmark>(r) \<in> P\<^sup>0\<close> \<open>\<checkmark>(s) \<in> Q\<^sup>0\<close> by blast
      have * : \<open>[\<checkmark>(r_s)] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([\<checkmark>(r)], [\<checkmark>(s)]), S)\<close>
        by (simp add: \<open>tick_join r s = Some r_s\<close>)
      from \<open>\<checkmark>(r) \<in> P\<^sup>0\<close> \<open>\<checkmark>(s) \<in> Q\<^sup>0\<close> show \<open>e \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
        by (simp add: \<open>e = \<checkmark>(r_s)\<close> initials_def T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (use "*" in blast)
    qed
  next
    fix e assume \<open>e \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
    then consider t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
      \<open>[e] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close> 
    | (div) t u t_P t_Q
    where \<open>[e] = t @ u\<close> \<open>ftF u\<close> \<open>tF t \<or> u = []\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding initials_def T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    thus \<open>e \<in> ?rhs_ev \<union> ?rhs_tick\<close>
    proof cases
      show \<open>t_P \<in> \<T> P \<Longrightarrow> t_Q \<in> \<T> Q \<Longrightarrow>
            [e] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S) \<Longrightarrow>
            e \<in> ?rhs_ev \<union> ?rhs_tick\<close> for t_P t_Q
        by (cases e; cases t_P; cases t_Q)
          (auto simp add: initials_def setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
            split: if_split_asm option.split_asm event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.splits
            dest!: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    next
      case div
      have \<open>t \<noteq> []\<close> by (metis BOT_iff_Nil_D Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k div(4,5) non_BOT)
      hence \<open>t = [e] \<and> u = []\<close>
        by (metis append_Cons append_Nil div(1) list.inject neq_Nil_conv)
      with div(4, 5) non_BOT show \<open>e \<in> ?rhs_ev \<union> ?rhs_tick\<close>
        by (cases e; cases t_P; cases t_Q)
          (auto simp add: initials_def setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps BOT_iff_Nil_D
            split: if_split_asm event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.splits option.split_asm 
            dest!: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro: D_T)
    qed
  qed
qed



section \<open>Laws of After\<close>

subsection \<open>Sequential Composition\<close>

locale AfterDuplicated_same_events = AfterDuplicated \<Psi>\<^sub>\<alpha> \<Psi>\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>('a, 'r ) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a \<Rightarrow> ('a, 'r ) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>\<beta> :: \<open>('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
begin

notation After\<^sub>\<alpha>.After (infixl \<open>after\<^sub>\<alpha>\<close> 86)
notation After\<^sub>\<beta>.After (infixl \<open>after\<^sub>\<beta>\<close> 86)


lemma not_skippable_or_not_initialR_After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = (if ev a \<in> P\<^sup>0 then P  after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q else \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a)\<close>
  if \<open>range tick \<inter> P\<^sup>0 = {} \<or> (\<forall>r. \<checkmark>(r) \<in> P\<^sup>0 \<longrightarrow> ev a \<notin> (Q r)\<^sup>0)\<close>
proof (cases \<open>P = \<bottom>\<close>)
  show \<open>P = \<bottom> \<Longrightarrow> (P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a =
        (if ev a \<in> P\<^sup>0 then P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q else \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a)\<close>
    by (simp add: After.After_BOT)
next
  note denot_projs = After.After_projs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
  assume non_BOT: \<open>P \<noteq> \<bottom>\<close>
  with that have $ : \<open>ev a \<in> (P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0 \<longleftrightarrow> ev a \<in> P\<^sup>0\<close>
    by (auto simp add: initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  show \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = (if ev a \<in> P\<^sup>0 then P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q else \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a)\<close>
  proof (split if_split, intro conjI impI)
    from "$" show \<open>ev a \<notin> P\<^sup>0 \<Longrightarrow> (P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a\<close>
      by (simp add: After\<^sub>\<beta>.not_initial_After)
  next
    assume initial_P : \<open>ev a \<in> P\<^sup>0\<close>
    show \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q\<close>
    proof (rule Process_eq_optimizedI)
      fix t assume \<open>t \<in> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
      then consider (D_P) t' u where \<open>ev a # t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
        | (D_Q) t' r u where \<open>ev a # t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>u \<in> \<D> (Q r)\<close>
        by (auto simp add: denot_projs "$" initial_P)
      thus \<open>t \<in> \<D> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q)\<close>
      proof cases
        case D_P with non_BOT initial_P show \<open>t \<in> \<D> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q)\<close>
          by (cases t') (auto simp add: BOT_iff_Nil_D denot_projs)
      next
        case D_Q with initial_P show \<open>t \<in> \<D> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q)\<close>
          by (cases t', simp_all add: BOT_iff_Nil_D denot_projs)
            (metis D_T disjoint_iff initials_memI rangeI that, blast)
      qed
    next
      fix t assume \<open>t \<in> \<D> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q)\<close>
      then consider (D_P) t' u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>ev a # t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
        | (D_Q) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>ev a # t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>u \<in> \<D> (Q r)\<close>
        by (auto simp add: denot_projs initial_P)
      thus \<open>t \<in> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
      proof cases
        case D_P thus \<open>t \<in> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
          by (simp add: denot_projs "$" initial_P Cons_eq_append_conv Cons_eq_map_conv)
            (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) tickFree_Cons_iff)
      next
        case D_Q thus \<open>t \<in> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
          by (simp add: denot_projs "$" initial_P Cons_eq_append_conv Cons_eq_map_conv)
            (metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) is_ev_def tickFree_Cons_iff)
      qed
    next
      fix t X assume \<open>(t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close> \<open>t \<notin> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
      then consider (F_P) t' where \<open>ev a # t = map (ev \<circ> of_ev) t'\<close>
        \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close> \<open>tF t'\<close>
      | (F_Q) t' r u where \<open>ev a # t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close>
        \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (Q r)\<close>
        by (auto simp add: denot_projs "$" initial_P)
          (metis (mono_tags, lifting) comp_apply list.simps(9) tickFree_Cons_iff)
      thus \<open>(t, X) \<in> \<F> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q)\<close>
      proof cases
        case F_P thus \<open>(t, X) \<in> \<F> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q)\<close>
          by (auto simp add: denot_projs initial_P)
      next
        case F_Q thus \<open>(t, X) \<in> \<F> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q)\<close>
          by (cases t', auto simp add:denot_projs initial_P intro: initials_memI)
            (metis F_T Int_iff empty_iff initials_memI rangeI that)
      qed
    next
      fix t X assume \<open>(t, X) \<in> \<F> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q)\<close>
      then consider (F_P) t' where \<open>t = map (ev \<circ> of_ev) t'\<close>
        \<open>(ev a # t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close> \<open>tF t'\<close>
      | (F_Q) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>ev a # t' @ [\<checkmark>(r)] \<in> \<T> P\<close>
        \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (Q r)\<close>
        by (auto simp add: denot_projs initial_P)
      thus \<open>(t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
      proof cases
        case F_P thus \<open>(t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
          by (simp add: denot_projs "$" initial_P Cons_eq_map_conv)
            (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) tickFree_Cons_iff)
      next
        case F_Q thus \<open>(t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
          by (simp add: denot_projs "$" initial_P Cons_eq_append_conv Cons_eq_map_conv)
            (metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) tickFree_Cons_iff)
      qed
    qed
  qed
qed


lemma skippable_not_initialL_After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = (  if (\<exists>r. \<checkmark>(r) \<in> P\<^sup>0 \<and> ev a \<in> (Q r)\<^sup>0)
                       then \<sqinter>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0 \<and> ev a \<in> (Q r)\<^sup>0}. Q r after\<^sub>\<beta> a
                       else \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a)\<close>
  (is \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = (if ?prem then ?rhs else _)\<close>) if \<open>ev a \<notin> P\<^sup>0\<close>
proof -
  note denot_projs = After.After_projs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs GlobalNdet_projs
  from initials_BOT \<open>ev a \<notin> P\<^sup>0\<close> have non_BOT : \<open>P \<noteq> \<bottom>\<close> by blast
  with \<open>ev a \<notin> P\<^sup>0\<close> have $ : \<open>ev a \<in> (P \<^bold>;\<^sub>\<checkmark> Q)\<^sup>0 \<longleftrightarrow> ?prem\<close>
    by (auto simp add: initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  show \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = (if ?prem then ?rhs else \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a)\<close>
  proof (split if_split, intro conjI impI)
    show \<open>\<not> ?prem \<Longrightarrow> (P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a\<close>
      by (rule After\<^sub>\<beta>.not_initial_After, use "$" in blast)
  next
    show \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = ?rhs\<close> if ?prem
    proof (rule Process_eq_optimizedI)
      fix t assume \<open>t \<in> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
      then consider (D_P) t' u where \<open>ev a # t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
        | (D_Q) t' r u where \<open>ev a # t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>u \<in> \<D> (Q r)\<close>
        by (auto simp add: denot_projs \<open>?prem\<close> "$" \<open>ev a \<notin> P\<^sup>0\<close>)
      thus \<open>t \<in> \<D> ?rhs\<close>
      proof cases
        case D_P with non_BOT \<open>ev a \<notin> P\<^sup>0\<close> show \<open>t \<in> \<D> ?rhs\<close>
          by (simp add: denot_projs Cons_eq_append_conv Cons_eq_map_conv BOT_iff_Nil_D)
            (metis D_T event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) initials_memI tickFree_Cons_iff)
      next
        case D_Q with \<open>ev a \<notin> P\<^sup>0\<close> show \<open>t \<in> \<D> ?rhs\<close>
          by (simp add: denot_projs Cons_eq_append_conv Cons_eq_map_conv)
            (metis D_T append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) initials_memI
              is_processT3_TR_append tickFree_Cons_iff)
      qed
    next
      from \<open>?prem\<close> show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close> for t
        by (simp add: denot_projs "$" Cons_eq_append_conv)
          (metis append_Nil initials_memD tickFree_Nil)
    next
      fix t X assume \<open>(t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close> \<open>t \<notin> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
      then consider (F_P) t' where \<open>ev a # t = map (ev \<circ> of_ev) t'\<close>
        \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close> \<open>tF t'\<close>
      | (F_Q) t' r u where \<open>ev a # t = map (ev \<circ> of_ev) t' @ u\<close>
        \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (Q r)\<close>
        by (simp add: denot_projs "$" \<open>?prem\<close>) metis
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      proof cases
        case F_P with \<open>ev a \<notin> P\<^sup>0\<close> show \<open>(t, X) \<in> \<F> ?rhs\<close>
          by (cases t', simp_all add: denot_projs \<open>?prem\<close>)
            (use F_T initials_memI in blast)
      next
        case F_Q with \<open>ev a \<notin> P\<^sup>0\<close> \<open>?prem\<close> show \<open>(t, X) \<in> \<F> ?rhs\<close>
          by (cases t', auto simp add: denot_projs intro: initials_memI)
            (metis F_T initials_memI)
      qed
    next
      from \<open>?prem\<close> show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> t \<notin> \<D> ?rhs \<Longrightarrow>
                         (t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close> for t X
        by (simp add: denot_projs "$" Cons_eq_append_conv Cons_eq_map_conv split: if_split_asm)
          (metis initials_memD self_append_conv2 tickFree_Nil)
    qed
  qed
qed



lemma skippable_initialL_initialR_After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> (\<sqinter>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0 \<and> ev a \<in> (Q r)\<^sup>0}. Q r after\<^sub>\<beta> a)\<close>
  (is \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs\<close>)
  if assms : \<open>\<exists>r. \<checkmark>(r) \<in> P\<^sup>0 \<and> ev a \<in> (Q r)\<^sup>0\<close> \<open>ev a \<in> P\<^sup>0\<close>
proof (cases \<open>P = \<bottom>\<close>)
  show \<open>P = \<bottom> \<Longrightarrow> (P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs\<close>
    by (simp add: After.After_BOT)
next
  note denot_projs = After.After_projs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs GlobalNdet_projs Ndet_projs
  show \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs\<close> if \<open>P \<noteq> \<bottom>\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
    then consider (D_P) t' u where \<open>ev a # t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
      | (D_Q) t' r u where \<open>ev a # t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>u \<in> \<D> (Q r)\<close>
      by (auto simp add: denot_projs initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k assms split: if_split_asm)
    thus \<open>t \<in> \<D> ((P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs)\<close>
    proof cases
      case D_P with \<open>P \<noteq> \<bottom>\<close> show \<open>t \<in> \<D> ((P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs)\<close>
        by (auto simp add: denot_projs assms Cons_eq_append_conv BOT_iff_Nil_D)
    next
      case D_Q thus \<open>t \<in> \<D> ((P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs)\<close>
        by (auto simp add: denot_projs assms Cons_eq_append_conv)
          (meson D_T initials_memI, blast)
    qed
  next
    from \<open>P \<noteq> \<bottom>\<close> show \<open>t \<in> \<D> ((P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs) \<Longrightarrow> t \<in> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close> for t
      by (auto simp add: denot_projs assms initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Cons_eq_append_conv Cons_eq_map_conv)
        (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) tickFree_Cons_iff,
          metis Cons_eq_appendI append_T_imp_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) list.distinct(1),
          metis append_Nil initials_memD tickFree_Nil)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close> \<open>t \<notin> \<D> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
    then consider (F_P) t' where \<open>ev a # t = map (ev \<circ> of_ev) t'\<close>
      \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close> \<open>tF t'\<close>
    | (F_Q) t' r u where \<open>ev a # t = map (ev \<circ> of_ev) t' @ u\<close>
      \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (Q r)\<close>
      by (simp add: denot_projs assms initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k split: if_split_asm) meson+
    thus \<open>(t, X) \<in> \<F> ((P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs)\<close>
    proof cases
      case F_P thus \<open>(t, X) \<in> \<F> ((P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs)\<close>
        by (auto simp add: denot_projs assms)
    next
      case F_Q with assms show \<open>(t, X) \<in> \<F> ((P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs)\<close>
        by (cases t', simp_all add: denot_projs)
          (meson F_T initials_memI, blast)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ((P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs)\<close> \<open>t \<notin> \<D> ((P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> ?rhs)\<close>
    hence \<open>(t, X) \<in> \<F> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<and> t \<notin> \<D> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<or>
           (t, X) \<in> \<F> ?rhs \<and> t \<notin> \<D> ?rhs\<close> by (simp add: Ndet_projs)
    thus \<open>(t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
    proof (elim disjE conjE)
      show \<open>(t, X) \<in> \<F> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> t \<notin> \<D> (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow>
            (t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
        by (simp add: denot_projs assms initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>P \<noteq> \<bottom>\<close> Cons_eq_append_conv Cons_eq_map_conv)
          (metis (no_types, lifting) Cons_eq_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) is_ev_def tickFree_Cons_iff)
    next
      from assms show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> t \<notin> \<D> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ((P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a)\<close>
        by (simp add: denot_projs initials_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>P \<noteq> \<bottom>\<close>
            Cons_eq_append_conv Cons_eq_map_conv split: if_split_asm)
          (metis append_Nil initials_memD tickFree_Nil)
    qed
  qed
qed


lemma not_initialL_not_initialR_After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>ev a \<notin> P\<^sup>0 \<Longrightarrow> (\<And>r. \<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> ev a \<notin> (Q r)\<^sup>0) \<Longrightarrow> 
   (P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a = \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a\<close>
  by (meson skippable_not_initialL_After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)


lemma After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>(P \<^bold>;\<^sub>\<checkmark> Q) after\<^sub>\<beta> a =
   (  if \<forall>r. \<checkmark>(r) \<in> P\<^sup>0 \<longrightarrow> ev a \<notin> (Q r)\<^sup>0
    then   if ev a \<in> P\<^sup>0 then P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q else \<Psi>\<^sub>\<beta> (P \<^bold>;\<^sub>\<checkmark> Q) a
    else   if ev a \<in> P\<^sup>0
         then (P after\<^sub>\<alpha> a \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> (\<sqinter>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0 \<and> ev a \<in> (Q r)\<^sup>0}. Q r after\<^sub>\<beta> a)
         else \<sqinter>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0 \<and> ev a \<in> (Q r)\<^sup>0}. Q r after\<^sub>\<beta> a)\<close>
  by (simp add: not_skippable_or_not_initialR_After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      skippable_initialL_initialR_After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k skippable_not_initialL_After_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

end



subsection \<open>Synchronization Product\<close>

text \<open>Because of the types, we have to extend the \<^theory_text>\<open>locale\<close>.\<close>

locale After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale = Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale tick_join +
  After\<^sub>l\<^sub>h\<^sub>s : After \<Psi>\<^sub>l\<^sub>h\<^sub>s + After\<^sub>r\<^sub>h\<^sub>s : After \<Psi>\<^sub>r\<^sub>h\<^sub>s + After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : After \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  for tick_join :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close>
    and \<Psi>\<^sub>l\<^sub>h\<^sub>s :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>r\<^sub>h\<^sub>s :: \<open>[('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>[('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
begin

notation After\<^sub>l\<^sub>h\<^sub>s.After (infixl \<open>after\<^sub>l\<^sub>h\<^sub>s\<close> 86)
notation After\<^sub>r\<^sub>h\<^sub>s.After (infixl \<open>after\<^sub>r\<^sub>h\<^sub>s\<close> 86)
notation After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After (infixl \<open>after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> 86)

sublocale After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym :
  After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>s r. tick_join r s\<close> \<Psi>\<^sub>r\<^sub>h\<^sub>s \<Psi>\<^sub>l\<^sub>h\<^sub>s \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  by unfold_locales



lemma initialL_not_initialR_not_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k a = P after\<^sub>l\<^sub>h\<^sub>s a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close> (is \<open>?lhs = ?rhs\<close>)
  if initial_hyps: \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<notin> Q\<^sup>0\<close> and notin: \<open>a \<notin> S\<close>
proof (cases \<open>P = \<bottom> \<or> Q = \<bottom>\<close>)
  show \<open>P = \<bottom> \<or> Q = \<bottom> \<Longrightarrow> ?lhs = ?rhs\<close>
    by (elim disjE) (simp_all add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After_BOT After\<^sub>l\<^sub>h\<^sub>s.After_BOT)
next
  from initial_hyps and notin have init : \<open>ev a \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
    by (simp add: initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  show \<open>?lhs = ?rhs\<close> if non_BOT : \<open>\<not> (P = \<bottom> \<or> Q = \<bottom>)\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    with init have \<open>ev a # t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.D_After)
    then obtain u v t_P t_Q
      where * : \<open>ev a # t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
        \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from "*"(4, 5) non_BOT have \<open>u \<noteq> []\<close>
      by (auto simp add: BOT_iff_Nil_D dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    with "*"(1) obtain u' where \<open>u = ev a # u'\<close> \<open>t = u' @ v\<close>
      by (cases u) simp_all
    from "*"(4, 5) initial_hyps(2) obtain t_P'
      where \<open>t_P = ev a # t_P'\<close> \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
      by (cases t_P; cases t_Q)
        (auto simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps \<open>u = ev a # u'\<close>
          split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.splits if_split_asm option.split_asm
          intro: D_T initials_memI)
    moreover from \<open>t_P = ev a # t_P'\<close> "*"(2, 5)
    have \<open>t_P' \<in> \<D> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<T> Q \<or>
          t_P' \<in> \<T> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<D> Q\<close>
      by (simp add: After\<^sub>l\<^sub>h\<^sub>s.After_projs initial_hyps(1))
    moreover from "*"(2) have \<open>tF u'\<close> by (simp add: \<open>u = ev a # u'\<close>)
    ultimately show \<open>t \<in> \<D> ?rhs\<close>
      using "*"(3) by (auto simp add: \<open>t = u' @ v\<close> D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain u v t_P t_Q
      where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
        \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>t_P \<in> \<D> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<T> Q \<or>
         t_P \<in> \<T> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<D> Q\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    have \<open>ev a # t = (ev a # u) @ v\<close> by (simp add: "*"(1))
    moreover from "*"(2) have \<open>tF (ev a # u)\<close> by simp
    moreover from "*"(4)
    have \<open>ev a # u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # t_P, t_Q), S)\<close>
      by (metis notin rev.simps(2) rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff
          setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL)
    moreover from "*"(5) have \<open>ev a # t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or>
                               ev a # t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      by (simp add: After\<^sub>l\<^sub>h\<^sub>s.After_projs initial_hyps(1))
    ultimately have \<open>ev a # t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      using "*"(3) unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    thus \<open>t \<in> \<D> ?lhs\<close>
      by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.D_After init)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close>
      \<open>t \<notin> \<D> ?lhs\<close>
    hence \<open>(ev a # t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>ev a # t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (simp_all add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After_projs init)
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>ev a # t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from "*"(2, 3) initial_hyps(2) obtain t_P'
      where \<open>t_P = ev a # t_P'\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
      by (metis Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE F_T initials_memI)
    moreover from "*"(1) have \<open>(t_P', X_P) \<in> \<F> (P after\<^sub>l\<^sub>h\<^sub>s a)\<close>
      by (simp add: \<open>t_P = ev a # t_P'\<close> After\<^sub>l\<^sub>h\<^sub>s.F_After initial_hyps(1))
    ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
      using "*"(2, 4) by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close>
      \<open>t \<notin> \<D> ?rhs\<close>
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> (P after\<^sub>l\<^sub>h\<^sub>s a)\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from "*"(1) have \<open>(ev a # t_P, X_P) \<in> \<F> P\<close>
      by (simp add: After\<^sub>l\<^sub>h\<^sub>s.F_After initial_hyps(1))
    moreover from "*"(3)
    have \<open>ev a # t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # t_P, t_Q), S)\<close>
      by (metis notin rev.simps(2) rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff
          setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL)
    ultimately have \<open>(ev a # t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      using "*"(2, 4) by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.F_After init)
  qed
qed


lemma (in After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) not_initialL_initialR_not_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k a = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q after\<^sub>r\<^sub>h\<^sub>s a\<close> (is \<open>?lhs = ?rhs\<close>)
  if initial_hyps: \<open>ev a \<notin> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close> and notin: \<open>a \<notin> S\<close>
  using After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.initialL_not_initialR_not_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
    [OF \<open>ev a \<in> Q\<^sup>0\<close> \<open>ev a \<notin> P\<^sup>0\<close> \<open>a \<notin> S\<close>]
  by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)


lemma not_initialL_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>ev a \<notin> P\<^sup>0 \<Longrightarrow> a \<in> S \<Longrightarrow> 
   (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k a = (if Q = \<bottom> then \<bottom> else \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) a)\<close>
  by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After_BOT, rule impI)
    (subst After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.not_initial_After, auto simp add: initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemma not_initialR_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>ev a \<notin> Q\<^sup>0 \<Longrightarrow> a \<in> S \<Longrightarrow> 
   (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k a = (if P = \<bottom> then \<bottom> else \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) a)\<close>
  by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After_BOT, rule impI)
    (subst After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.not_initial_After, auto simp add: initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)


lemma initialL_initialR_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k a = P after\<^sub>l\<^sub>h\<^sub>s a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q after\<^sub>r\<^sub>h\<^sub>s a\<close> (is \<open>?lhs = ?rhs\<close>)
  if initial_hyps: \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close> and inside: \<open>a \<in> S\<close>
proof (cases \<open>P = \<bottom> \<or> Q = \<bottom>\<close>)
  show \<open>P = \<bottom> \<or> Q = \<bottom> \<Longrightarrow> ?lhs = ?rhs\<close>
    by (elim disjE) (simp_all add: After.After_BOT)
next
  from initial_hyps inside have init : \<open>ev a \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
    by (simp add: initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  show \<open>?lhs = ?rhs\<close> if non_BOT : \<open>\<not> (P = \<bottom> \<or> Q = \<bottom>)\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ((P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k a)\<close>
    hence \<open>ev a # t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.D_After init)
    then obtain u v t_P t_Q
      where * : \<open>ev a # t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
        \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from "*"(4, 5) non_BOT have \<open>u \<noteq> []\<close>
      by (auto simp add: BOT_iff_Nil_D dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    with "*"(1) obtain u' where \<open>u = ev a # u'\<close> \<open>t = u' @ v\<close>
      by (cases u) simp_all
    from "*"(4) inside initial_hyps(1, 2) \<open>u = ev a # u'\<close>
    obtain t_P' t_Q' where \<open>t_P = ev a # t_P'\<close> \<open>t_Q = ev a # t_Q'\<close>
      \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'), S)\<close>
      by (metis (no_types, opaque_lifting) Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    moreover from "*"(2) have \<open>tF u'\<close> by (simp add: \<open>u = ev a # u'\<close>)
    moreover from "*"(5)
    have \<open>t_P' \<in> \<D> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q' \<in> \<T> (Q after\<^sub>r\<^sub>h\<^sub>s a) \<or>
          t_P' \<in> \<T> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q' \<in> \<D> (Q after\<^sub>r\<^sub>h\<^sub>s a)\<close>
      by (simp add: \<open>t_P = ev a # t_P'\<close> \<open>t_Q = ev a # t_Q'\<close>
          After.After_projs initial_hyps)
    ultimately show \<open>t \<in> \<D> ?rhs\<close>
      using "*"(3) by (auto simp add: \<open>t = u' @ v\<close> D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain u v t_P t_Q
      where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
        \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>t_P \<in> \<D> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<T> (Q after\<^sub>r\<^sub>h\<^sub>s a) \<or>
                 t_P \<in> \<T> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<D> (Q after\<^sub>r\<^sub>h\<^sub>s a)\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from "*"(1) have \<open>ev a # t = (ev a # u) @ v\<close> by simp
    moreover from "*"(2) have \<open>tF (ev a # u)\<close> by simp
    moreover from "*"(4) have \<open>ev a # u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub>
                               ((ev a # t_P, ev a # t_Q), S)\<close>
      by (simp add: inside)
    moreover from "*"(5) have \<open>ev a # t_P \<in> \<D> P \<and> ev a # t_Q \<in> \<T> Q \<or>
                               ev a # t_P \<in> \<T> P \<and> ev a # t_Q \<in> \<D> Q\<close>
      by (simp add: After.After_projs initial_hyps)
    ultimately have \<open>ev a # t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using "*"(3) by blast
    thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.D_After init)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    hence \<open>(ev a # t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>ev a # t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (simp_all add: After.After_projs init)
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>ev a # t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from "*"(3) obtain t_P' t_Q'
      where \<open>t_P = ev a # t_P'\<close> \<open>t_Q = ev a # t_Q'\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'), S)\<close>
      by (metis (no_types) Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE inside)
    moreover from "*"(1, 2) have \<open>(t_P', X_P) \<in> \<F> (P after\<^sub>l\<^sub>h\<^sub>s a)\<close>
      \<open>(t_Q', X_Q) \<in> \<F> (Q after\<^sub>r\<^sub>h\<^sub>s a)\<close>
      by (simp_all add: \<open>t_P = ev a # t_P'\<close> \<open>t_Q = ev a # t_Q'\<close> 
          After.F_After initial_hyps)
    ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
      by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro!: "*"(4))
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> (P after\<^sub>l\<^sub>h\<^sub>s a)\<close>
        \<open>(t_Q, X_Q) \<in> \<F> (Q after\<^sub>r\<^sub>h\<^sub>s a)\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from "*"(1, 2) have \<open>(ev a # t_P, X_P) \<in> \<F> P\<close>
      \<open>(ev a # t_Q, X_Q) \<in> \<F> Q\<close>
      by (simp_all add: After.F_After initial_hyps)
    moreover from "*"(3) have \<open>ev a # t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub>
                               ((ev a # t_P, ev a # t_Q), S)\<close>
      by (simp add: inside)
    ultimately have \<open>(ev a # t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      using "*"(4) by (simp (no_asm) add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.F_After init)
  qed
qed



lemma initialL_initialR_not_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: 
  \<open>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k a = (P after\<^sub>l\<^sub>h\<^sub>s a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<sqinter> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q after\<^sub>r\<^sub>h\<^sub>s a)\<close>
  (is \<open>?lhs = ?rhs1 \<sqinter> ?rhs2\<close>)
  if initial_hyps: \<open>ev a \<in> P\<^sup>0\<close> \<open>ev a \<in> Q\<^sup>0\<close> and notin: \<open>a \<notin> S\<close>
proof (cases \<open>P = \<bottom> \<or> Q = \<bottom>\<close>)
  show \<open>P = \<bottom> \<or> Q = \<bottom> \<Longrightarrow> ?lhs = ?rhs1 \<sqinter> ?rhs2\<close>
    by (elim disjE) (simp_all add: After.After_BOT)
next
  from initial_hyps(1) notin have init : \<open>ev a \<in> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<^sup>0\<close>
    by (simp add: initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  show \<open>?lhs = ?rhs1 \<sqinter> ?rhs2\<close> if non_BOT : \<open>\<not> (P = \<bottom> \<or> Q = \<bottom>)\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    hence \<open>ev a # t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.D_After init)
    then obtain u v t_P t_Q
      where * : \<open>ev a # t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
        \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    from "*"(4, 5) non_BOT have \<open>u \<noteq> []\<close>
      by (auto simp add: BOT_iff_Nil_D dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    with "*"(1) obtain u' where \<open>u = ev a # u'\<close> \<open>t = u' @ v\<close>
      by (cases u) simp_all
    from "*"(2) have \<open>tF u'\<close> by (simp add: \<open>u = ev a # u'\<close>)
    from "*"(4) notin \<open>u = ev a # u'\<close>
    consider t_P' where \<open>t_P = ev a # t_P'\<close>
      \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
    | t_Q' where \<open>t_Q = ev a # t_Q'\<close>
      \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q'), S)\<close>
      by (metis (no_types) Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    thus \<open>t \<in> \<D> (?rhs1 \<sqinter> ?rhs2)\<close>
    proof cases
      fix t_P' assume $ : \<open>t_P = ev a # t_P'\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
      from "*"(5) have \<open>t_P' \<in> \<D> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<T> Q \<or>
                        t_P' \<in> \<T> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<D> Q\<close>
        by (simp add: "$"(1) After\<^sub>l\<^sub>h\<^sub>s.After_projs initial_hyps(1))
      with "$"(2) "*"(3) \<open>tF u'\<close> have \<open>t \<in> \<D> ?rhs1\<close>
        by (auto simp add: \<open>t = u' @ v\<close> D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      thus \<open>t \<in> \<D> (?rhs1 \<sqinter> ?rhs2)\<close> by (simp add: D_Ndet)
    next
      fix t_Q' assume $ : \<open>t_Q = ev a # t_Q'\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q'), S)\<close>
      from "*"(5) have \<open>t_P \<in> \<D> P \<and> t_Q' \<in> \<T> (Q after\<^sub>r\<^sub>h\<^sub>s a) \<or>
                        t_P \<in> \<T> P \<and> t_Q' \<in> \<D> (Q after\<^sub>r\<^sub>h\<^sub>s a)\<close>
        by (simp add: "$"(1) After\<^sub>r\<^sub>h\<^sub>s.After_projs initial_hyps(2))
      with "$"(2) "*"(3) \<open>tF u'\<close> have \<open>t \<in> \<D> ?rhs2\<close>
        by (auto simp add: \<open>t = u' @ v\<close> D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      thus \<open>t \<in> \<D> (?rhs1 \<sqinter> ?rhs2)\<close> by (simp add: D_Ndet)
    qed
  next
    fix t assume \<open>t \<in> \<D> (?rhs1 \<sqinter> ?rhs2)\<close>
    then consider \<open>t \<in> \<D> ?rhs1\<close> | \<open>t \<in> \<D> ?rhs2\<close>
      by (auto simp add: D_Ndet)
    hence \<open>ev a # t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    proof cases
      assume \<open>t \<in> \<D> ?rhs1\<close>
      then obtain u v t_P t_Q
        where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
          \<open>t_P \<in> \<D> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<T> Q \<or>
                   t_P \<in> \<T> (P after\<^sub>l\<^sub>h\<^sub>s a) \<and> t_Q \<in> \<D> Q\<close>
        unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      from "*"(1) have \<open>ev a # t = (ev a # u) @ v\<close> by simp
      moreover from "*"(2) have \<open>tF (ev a # u)\<close> by simp
      moreover from "*"(4)
      have \<open>ev a # u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # t_P, t_Q), S)\<close>
        by (metis notin rev.simps(2) rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff
            setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL)
      moreover from "*"(5) have \<open>ev a # t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or>
                                 ev a # t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
        by (simp add: After\<^sub>l\<^sub>h\<^sub>s.After_projs initial_hyps(1))
      ultimately show \<open>ev a # t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        using "*"(3) unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    next
      assume \<open>t \<in> \<D> ?rhs2\<close>
      then obtain u v t_P t_Q
        where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
          \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> (Q after\<^sub>r\<^sub>h\<^sub>s a) \<or>
                   t_P \<in> \<T> P \<and> t_Q \<in> \<D> (Q after\<^sub>r\<^sub>h\<^sub>s a)\<close>
        unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      from "*"(1) have \<open>ev a # t = (ev a # u) @ v\<close> by simp
      moreover from "*"(2) have \<open>tF (ev a # u)\<close> by simp
      moreover from "*"(4) have \<open>ev a # u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, ev a # t_Q), S)\<close>
        by (metis notin rev.simps(2) rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff
            setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinR)
      moreover from "*"(5) have \<open>t_P \<in> \<D> P \<and> ev a # t_Q \<in> \<T> Q \<or>
                                 t_P \<in> \<T> P \<and> ev a # t_Q \<in> \<D> Q\<close>
        by (simp add: After\<^sub>r\<^sub>h\<^sub>s.After_projs initial_hyps(2))
      ultimately show \<open>ev a # t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        using "*"(3) unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
    qed
    thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.D_After init)
  next  
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    hence \<open>(ev a # t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>ev a # t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (simp_all add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After_projs init)
    then obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>ev a # t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from "*"(3) notin
    consider t_P' where \<open>t_P = ev a # t_P'\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
    | t_Q' where \<open>t_Q = ev a # t_Q'\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q'), S)\<close>
      by (metis (no_types) Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    thus \<open>(t, X) \<in> \<F> (?rhs1 \<sqinter> ?rhs2)\<close>
    proof cases
      fix t_P' assume $ : \<open>t_P = ev a # t_P'\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
      from "*"(1) have \<open>(t_P', X_P) \<in> \<F> (P after\<^sub>l\<^sub>h\<^sub>s a)\<close>
        by (simp add: "$"(1) After\<^sub>l\<^sub>h\<^sub>s.F_After initial_hyps(1))
      with "$"(2) "*"(2, 4) have \<open>(t, X) \<in> \<F> ?rhs1\<close>
        by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      thus \<open>(t, X) \<in> \<F> (?rhs1 \<sqinter> ?rhs2)\<close> by (simp add: F_Ndet)
    next
      fix t_Q' assume $ : \<open>t_Q = ev a # t_Q'\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q'), S)\<close>
      from "*"(2) have \<open>(t_Q', X_Q) \<in> \<F> (Q after\<^sub>r\<^sub>h\<^sub>s a)\<close>
        by (simp add: "$"(1) After\<^sub>r\<^sub>h\<^sub>s.F_After initial_hyps(2))
      with "$"(2) "*"(1, 4) have \<open>(t, X) \<in> \<F> ?rhs2\<close>
        by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      thus \<open>(t, X) \<in> \<F> (?rhs1 \<sqinter> ?rhs2)\<close> by (simp add: F_Ndet)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> (?rhs1 \<sqinter> ?rhs2)\<close> \<open>t \<notin> \<D> (?rhs1 \<sqinter> ?rhs2)\<close>
    then consider \<open>(t, X) \<in> \<F> ?rhs1\<close> \<open>t \<notin> \<D> ?rhs1\<close>
      | \<open>(t, X) \<in> \<F> ?rhs2\<close> \<open>t \<notin> \<D> ?rhs2\<close>
      by (auto simp add: Ndet_projs)
    hence \<open>(ev a # t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    proof cases
      assume \<open>(t, X) \<in> \<F> ?rhs1\<close> \<open>t \<notin> \<D> ?rhs1\<close>
      then obtain t_P t_Q X_P X_Q
        where * : \<open>(t_P, X_P) \<in> \<F> (P after\<^sub>l\<^sub>h\<^sub>s a)\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
          \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      from "*"(1) have \<open>(ev a # t_P, X_P) \<in> \<F> P\<close>
        by (simp add: After\<^sub>l\<^sub>h\<^sub>s.F_After initial_hyps(1))
      moreover from "*"(3)
      have \<open>ev a # t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # t_P, t_Q), S)\<close>
        by (metis notin rev.simps(2) rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff
            setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL)
      ultimately show \<open>(ev a # t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro!: "*"(2, 4))
    next
      assume \<open>(t, X) \<in> \<F> ?rhs2\<close> \<open>t \<notin> \<D> ?rhs2\<close>
      then obtain t_P t_Q X_P X_Q
        where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> (Q after\<^sub>r\<^sub>h\<^sub>s a)\<close>
          \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
          \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      from "*"(2) have \<open>(ev a # t_Q, X_Q) \<in> \<F> Q\<close>
        by (simp add: After\<^sub>r\<^sub>h\<^sub>s.F_After initial_hyps(2))
      moreover from "*"(3)
      have \<open>ev a # t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, ev a # t_Q), S)\<close>
        by (metis notin rev.simps(2) rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff
            setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinR)
      ultimately show \<open>(ev a # t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro!: "*"(1, 4))
    qed
    thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.F_After init)
  qed
qed



lemma not_initialL_not_initialR_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>ev a \<notin> P\<^sup>0 \<Longrightarrow> ev a \<notin> Q\<^sup>0 \<Longrightarrow> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k a = \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) a\<close>
  by (subst After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.not_initial_After) (auto simp add: initials_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)



text \<open>Finally, the monster theorem !\<close>

theorem After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: 
  \<open>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) after\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k a =
   (  if P = \<bottom> \<or> Q = \<bottom> then \<bottom>
    else   if ev a \<in> P\<^sup>0 \<and> ev a \<in> Q\<^sup>0
         then   if a \<in> S then P after\<^sub>l\<^sub>h\<^sub>s a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q after\<^sub>r\<^sub>h\<^sub>s a
              else (P after\<^sub>l\<^sub>h\<^sub>s a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<sqinter> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q after\<^sub>r\<^sub>h\<^sub>s a)
         else   if ev a \<in> P\<^sup>0 \<and> a \<notin> S then P after\<^sub>l\<^sub>h\<^sub>s a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q
              else   if ev a \<in> Q\<^sup>0 \<and> a \<notin> S then P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q after\<^sub>r\<^sub>h\<^sub>s a
                   else \<Psi>\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) a)\<close>
  by (auto simp add: After\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.After_BOT initialL_not_initialR_not_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      initialL_initialR_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k initialL_initialR_not_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      not_initialL_initialR_not_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k not_initialL_not_initialR_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      not_initialR_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k not_initialL_in_After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)


end


(*<*)
end
  (*>*)