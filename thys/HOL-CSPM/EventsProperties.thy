(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Results on events_of
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

chapter \<open>Results on \<open>events_of\<close>\<close>

theory EventsProperties
  imports CSPM
begin



section \<open>With Operators of \<^session>\<open>HOL-CSP\<close>\<close>

lemma events_of_def_tickFree: 
  \<open>events_of P = (\<Union>t\<in>{t \<in> \<T> P. tickFree t}. {a. ev a \<in> set t})\<close>
proof -
  have \<open>s \<in> \<T> P \<Longrightarrow> \<not> tickFree s \<Longrightarrow> ev e \<in> set s \<Longrightarrow> ev e \<in> set (butlast s)\<close> for e s
    by (cases s rule: rev_cases) (simp_all add: append_single_T_imp_tickFree)
  thus ?thesis
    by (auto simp add: events_of_def)
       (metis butlast_snoc front_tickFree_butlast is_processT2_TR
              is_processT3_ST nonTickFree_n_frontTickFree)
qed


lemma events_BOT:  \<open>events_of \<bottom> = UNIV\<close>
  and events_SKIP: \<open>events_of SKIP = {}\<close>
  and events_STOP: \<open>events_of STOP = {}\<close>
  by (auto simp add: events_of_def T_UU T_SKIP T_STOP)
     (meson front_tickFree_single list.set_intros(1))


lemma anti_mono_events_T: \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> events_of Q \<subseteq> events_of P\<close>
  unfolding trace_refine_def events_of_def by fast

lemma anti_mono_events_F: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> events_of Q \<subseteq> events_of P\<close>
  by (intro anti_mono_events_T leF_imp_leT)

lemma anti_mono_events_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> events_of Q \<subseteq> events_of P\<close>
  by (intro anti_mono_events_F leFD_imp_leF)



lemmas events_fix_prefix = 
       events_DF[of \<open>{a}\<close>, simplified DF_def Mndetprefix_unit] for a

lemma events_Mndetprefix:
  \<open>events_of (Mndetprefix A P) = A \<union> (\<Union>a\<in>A. events_of (P a))\<close>
  apply (cases \<open>A = {}\<close>, simp add: events_STOP)
  unfolding events_of_def 
  apply (simp add: T_Mndetprefix T_Mprefix write0_def, safe; simp)
    apply (metis event.inject list.exhaust_sel set_ConsD)
  by (metis Nil_elem_T list.sel(1, 3) list.set_intros(1)) 
     (metis list.sel(1, 3) list.set_intros(2))


lemma events_Mprefix:
  \<open>events_of (Mprefix A P) = A \<union> (\<Union>a\<in>A. events_of (P a))\<close>
  apply (rule subset_antisym)
   apply (rule subset_trans[OF anti_mono_events_FD[OF Mprefix_refines_Mndetprefix_FD]],
          simp add: events_Mndetprefix)
  unfolding events_of_def 
  apply (simp add: T_Mprefix, safe; simp)
  by (metis Nil_elem_T list.sel(1, 3) list.set_intros(1))
     (metis list.sel(1, 3) list.set_intros(2))


lemma events_prefix: \<open>events_of (a \<rightarrow> P) = insert a (events_of P)\<close>
  unfolding write0_def by (simp add: events_Mprefix)


lemma events_Ndet: \<open>events_of (P \<sqinter> Q) = events_of P \<union> events_of Q\<close>
  unfolding events_of_def by (simp add: T_Ndet)


lemma events_Det: \<open>events_of (P \<box> Q) = events_of P \<union> events_of Q\<close>
  unfolding events_of_def by (simp add: T_Det)


lemma events_Renaming:
  \<open>events_of (Renaming P f) = (if \<D> P = {} then f ` events_of P else UNIV)\<close>
proof (split if_split, intro conjI impI)
  show \<open>\<D> P \<noteq> {} \<Longrightarrow> events_of (Renaming P f) = UNIV\<close>
    by (rule events_div, simp add: D_Renaming)
       (metis D_imp_front_tickFree ex_in_conv front_tickFree_charn
        front_tickFree_implies_tickFree is_processT9_S_swap nonTickFree_n_frontTickFree)
next
  show \<open>events_of (Renaming P f) = f ` events_of P\<close> if div_free : \<open>\<D> P = {}\<close>
  proof (intro subset_antisym subsetI)
    fix e
    assume \<open>e \<in> events_of (Renaming P f)\<close>
    then obtain s t where * : \<open>t \<in> \<T> P\<close> \<open>s = map (EvExt f) t\<close> \<open>ev e \<in> set s\<close>
      by (auto simp add: events_of_def T_Renaming div_free)
    from "*"(2, 3) obtain e' where \<open>e = f e'\<close> \<open>ev e' \<in> set t\<close>
      by (auto simp add: EvExt_def split: event.split_asm)
    with "*"(1) show \<open>e \<in> f ` events_of P\<close>
      unfolding events_of_def by blast
  next
    fix e
    assume \<open>e \<in> f ` events_of P\<close>
    then obtain e' where * : \<open>e = f e'\<close> \<open>e' \<in> events_of P\<close> by blast
    from "*"(2) obtain t where \<open>t \<in> \<T> P\<close> \<open>ev e' \<in> set t\<close>
      unfolding events_of_def by blast
    thus \<open>e \<in> events_of (Renaming P f)\<close>
      apply (simp add: events_of_def T_Renaming)
      apply (rule disjI1)
      apply (rule_tac x = \<open>map (EvExt f) t\<close> in exI)
      using "*"(1) by (auto simp add: EvExt_def image_iff split: event.split)
  qed
qed
     
     


lemma events_Seq:
  \<open>events_of (P \<^bold>; Q) =
   (if non_terminating P then events_of P else events_of P \<union> events_of Q)\<close>
proof (split if_split, intro conjI impI)
  show \<open>non_terminating P \<Longrightarrow> events_of (P \<^bold>; Q) = events_of P\<close>
    by (simp add: non_terminating_Seq)
next
  show \<open>events_of (P \<^bold>; Q) = events_of P \<union> events_of Q\<close> if \<open>\<not> non_terminating P\<close>
  proof (intro subset_antisym subsetI)
    show \<open>e \<in> events_of (P \<^bold>; Q) \<Longrightarrow> e \<in> events_of P \<union> events_of Q\<close> for e
      by (auto simp add: events_of_def T_Seq F_T D_T intro: is_processT3_ST)
  next
    fix s
    assume \<open>s \<in> events_of P \<union> events_of Q\<close>
    then consider \<open>s \<in> events_of P\<close> | \<open>s \<in> events_of Q\<close> by fast
    thus \<open>s \<in> events_of (P \<^bold>; Q)\<close>
    proof cases
      show \<open>s \<in> events_of P \<Longrightarrow> s \<in> events_of (P \<^bold>; Q)\<close>
        by (simp add: events_of_def_tickFree T_Seq)
           (metis Nil_elem_T append.right_neutral is_processT5_S7 singletonD)
    next
      from non_terminating_refine_DF that 
      obtain t1 where * : \<open>t1 \<in> \<T> P\<close> \<open>t1 \<notin> \<T> (DF UNIV)\<close>
        by (metis subsetI trace_refine_def)
      then obtain t1' where \<open>t1 = t1' @ [tick]\<close>
        using DF_all_tickfree_traces2 T_nonTickFree_imp_decomp is_processT3_ST by blast
      hence \<open>t2 \<in> \<T> Q \<Longrightarrow> t1' @ t2 \<in> \<T> (P \<^bold>; Q)\<close> for t2
        using "*"(1) T_Seq by blast
      thus \<open>s \<in> events_of Q \<Longrightarrow> s \<in> events_of (P \<^bold>; Q)\<close>
        by (simp add: events_of_def, elim bexE)
           (metis UnCI set_append)
    qed
  qed
qed



lemma events_Sync: \<open>events_of (P \<lbrakk>S\<rbrakk> Q) \<subseteq> events_of P \<union> events_of Q\<close>
  apply (subst events_of_def, subst T_Sync, simp add: subset_iff)
proof (intro allI impI conjI, goal_cases)
  case (1 a)
  thus ?case by (metis (no_types, lifting) UN_I events_of_def ftf_Sync1 mem_Collect_eq) 
next
  case (2 a)
  then obtain t u where \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> by blast
  thus ?case using events_div by blast
qed


lemma events_Inter:
  \<open>events_of ((P :: '\<alpha> process) ||| Q) = events_of P \<union> events_of Q\<close>
proof (rule subset_antisym[OF events_Sync])
  have \<open>\<lbrakk>tickFree s; s \<in> \<T> (P :: '\<alpha> process)\<rbrakk> \<Longrightarrow> s \<in> \<T> (P ||| Q)\<close> for s P Q
    apply (simp add: T_Sync)
    apply (rule disjI1)
    apply (rule_tac x = s in exI, simp)
    apply (rule_tac x = \<open>[]\<close> in exI, simp add: Nil_elem_T)
    by (metis Sync.sym emptyLeftSelf singletonD tickFree_def)
  hence \<open>events_of (P :: '\<alpha> process) \<subseteq> events_of (P ||| Q)\<close> for P Q
    unfolding events_of_def_tickFree by fast
  thus \<open>events_of P \<union> events_of Q \<subseteq> events_of (P ||| Q)\<close>
    by (metis Inter_commute Un_least)
qed



lemma empty_div_hide_events_Hiding: \<open>events_of (P \ B) \<subseteq> events_of P - B\<close>
  if \<open>div_hide P B = {}\<close>
  unfolding events_of_def T_Hiding
  apply (subst that, simp)
  using F_T by auto blast

lemma not_empty_div_hide_events_Hiding:
  \<open>div_hide P B \<noteq> {} \<Longrightarrow> events_of (P \ B) = UNIV\<close>
  using D_Hiding events_div by blast



text \<open>\<^const>\<open>events_of\<close> and \<^const>\<open>deadlock_free\<close>\<close>

lemma nonempty_events_if_deadlock_free: \<open>deadlock_free P \<Longrightarrow> events_of P \<noteq> {}\<close>
  unfolding deadlock_free_def events_of_def failure_divergence_refine_def le_ref_def 
  apply (simp add: div_free_DF, subst (asm) DF_unfold)
  apply (simp add: F_Mndetprefix write0_def F_Mprefix subset_iff)
  by (metis Nil_elem_T T_F_spec UNIV_I hd_in_set is_processT5_S7
            list.distinct(1) self_append_conv2)

lemma events_in_DF: \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> events_of P \<subseteq> A\<close>
  by (metis anti_mono_events_FD events_DF)


lemma nonempty_events_if_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<Longrightarrow> [tick] \<in> \<T> P \<or> events_of P \<noteq> {}\<close>
  unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def events_of_def failure_refine_def le_ref_def 
  apply (subst (asm) DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
  apply (simp add: F_Mndetprefix write0_def F_Mprefix subset_iff F_Ndet F_SKIP)
  by (metis Nil_elem_T T_F_spec UNIV_I hd_in_set is_processT5_S7
            list.distinct(1) self_append_conv2)

lemma events_in_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> events_of P \<subseteq> A\<close>
  by (metis anti_mono_events_FD events_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P)

lemma \<open>\<not> events_of P \<subseteq> A \<Longrightarrow> \<not> DF A \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  and \<open>\<not> events_of P \<subseteq> A \<Longrightarrow> \<not> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis anti_mono_events_FD events_DF)
     (metis anti_mono_events_FD events_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P)
  
 

section \<open>With Architectural Operators of \<^session>\<open>HOL-CSPM\<close>\<close>

lemma events_MultiNdet:
  \<open>finite A \<Longrightarrow> events_of (MultiNdet A P) = (\<Union>a\<in>A. events_of (P a))\<close>
  by (cases \<open>A = {}\<close>, simp add: events_STOP)
     (rotate_tac, induct A rule: finite_set_induct_nonempty; simp add: events_Ndet)
  

lemma events_MultiDet:
  \<open>finite A \<Longrightarrow> events_of (MultiDet A P) = (\<Union>a\<in>A. events_of (P a))\<close>
  by (induct A rule: finite_induct) (simp_all add: events_STOP events_Det)


lemma events_MultiSeq:
  \<open>events_of (SEQ a \<in>@ L. P a) =
   (\<Union>a \<in> set (take (Suc (first_elem (\<lambda>a. non_terminating (P a)) L)) L). 
    events_of (P a))\<close>
  by (subst non_terminating_MultiSeq, induct L; simp add: events_SKIP events_Seq)

lemma events_MultiSeq_subset:
  \<open>events_of (SEQ a \<in>@ L. P a) \<subseteq> (\<Union>a \<in> set L. events_of (P a))\<close>
  using in_set_takeD by (subst events_MultiSeq) fastforce



lemma events_MultiSync:
  \<open>events_of (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># M. P a) \<subseteq> (\<Union>a \<in> set_mset M. events_of (P a))\<close>
  by (induct M rule: induct_subset_mset_empty_single; simp add: events_STOP)
     (meson Diff_subset_conv dual_order.trans events_Sync)


lemma events_MultiInter:
  \<open>events_of (\<^bold>|\<^bold>|\<^bold>| a \<in># M. P a) = (\<Union>a \<in> set_mset M. events_of (P a))\<close>
  by (induct M rule: induct_subset_mset_empty_single)
     (simp_all add: events_STOP events_Inter)
 



end