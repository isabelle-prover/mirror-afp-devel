(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
 *
 * This file       : Initials events of a process
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

chapter \<open> The Initials Notion \<close>

(*<*)
theory  Initials
  imports "HOL-CSPM.CSPM"
begin
  (*>*)


text \<open>This will be discussed more precisely later, but we want to define a new operator 
      which would in some way be the reciprocal of the prefix operator \<^term>\<open>e \<rightarrow> P\<close>.

      A first observation is that by prefixing \<^term>\<open>P\<close> with \<^term>\<open>e\<close>,
      we force its nonempty traces to begin with \<^term>\<open>ev e\<close>.

      Therefore we must define a notion that captures this idea.\<close>

section \<open>Definition\<close>

text \<open>The initials notion captures the set of events that can be used to begin a given process.\<close>

definition initials :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close> (\<open>(_\<^sup>0)\<close> [1000] 999)
  where \<open>P\<^sup>0 \<equiv> {e. [e] \<in> \<T> P}\<close>

lemma initials_memI' : \<open>[e] \<in> \<T> P \<Longrightarrow> e \<in> P\<^sup>0\<close>
  and initials_memD  : \<open>e \<in> P\<^sup>0 \<Longrightarrow> [e] \<in> \<T> P\<close>
  by (simp_all add: initials_def)

lemma initials_def_bis: \<open>P\<^sup>0 = {e. \<exists>s. e # s \<in> \<T> P}\<close>
  by (simp add: set_eq_iff initials_def)
    (metis Prefix_Order.prefixI append_Cons append_Nil is_processT3_TR)

lemma initials_memI : \<open>e # s \<in> \<T> P \<Longrightarrow> e \<in> P\<^sup>0\<close>
  unfolding initials_def_bis by blast


text \<open>We say here that the \<^const>\<open>initials\<close> of a process \<^term>\<open>P\<close> is the set
      of events \<^term>\<open>e\<close> such that there is a trace of \<^term>\<open>P\<close> starting with \<^term>\<open>e\<close>.

      One could also think about defining \<^term>\<open>initials P\<close> as the set of events that
      \<^term>\<open>P\<close> can not refuse at first: \<^term>\<open>{e. {e} \<notin> \<R> P}\<close>.
      These two definitions are not equivalent (and the second one is more restrictive
      than the first one). Moreover, the second does not behave well with the 
      non-deterministic choice \<^const>\<open>Ndet\<close> (see the \<^theory_text>\<open>notepad\<close> below).
      
      Therefore, we will keep the first one.

      We also have a strong argument of authority: this is the definition given
      by Roscoe \<^cite>\<open>\<open>p.40\<close> in "Roscoe2010UnderstandingCS"\<close>.\<close>


notepad
begin
  fix e :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> \<comment>\<open>just fixing \<^typ>\<open>'a\<close> type\<close>

  define bad_initials
    where \<open>bad_initials (P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<equiv> {e. {e} \<notin> \<R> P}\<close> for P

\<comment>\<open>This notion is more restrictive than \<^const>\<open>initials\<close>\<close>
  have bad_initials_subset_initials:
    \<open>bad_initials P \<subseteq> initials P\<close> for P
    unfolding bad_initials_def initials_def Refusals_iff
    using is_processT1_TR is_processT5_S7 by force

\<comment>\<open>and does not behave well with @{const [source] Ndet}.\<close>
  have bad_behaviour_with_Ndet: 
    \<open>\<exists>P Q. bad_initials (P \<sqinter> Q) \<noteq> bad_initials P \<union> bad_initials Q\<close>
  proof (intro exI)
    show \<open>bad_initials (SKIP undefined \<sqinter> \<bottom>) \<noteq> bad_initials (SKIP undefined) \<union> bad_initials \<bottom>\<close>
      by (simp add: bad_initials_def F_Ndet F_SKIP F_BOT Refusals_iff)
  qed
end



section \<open>Anti-Mono Rules\<close>

lemma anti_mono_initials_T: \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> initials Q \<subseteq> initials P\<close>
  by (simp add: Collect_mono_iff trace_refine_def initials_def subsetD)

lemma anti_mono_initials_F: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> initials Q \<subseteq> initials P\<close>
  unfolding failure_refine_def
  by (drule F_subset_imp_T_subset) (fact anti_mono_initials_T[unfolded trace_refine_def])

text \<open>Of course, this anti-monotony does not hold for \<^term>\<open>(\<sqsubseteq>\<^sub>D)\<close>.\<close>

lemma anti_mono_initials_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> initials Q \<subseteq> initials P\<close>
  by (simp add: anti_mono_initials_F leFD_imp_leF)

lemma anti_mono_initials: \<open>P \<sqsubseteq> Q \<Longrightarrow> initials Q \<subseteq> initials P\<close>
  by (simp add: anti_mono_initials_T le_approx_lemma_T trace_refine_def)

lemma anti_mono_initials_DT: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> initials Q \<subseteq> initials P\<close>
  by (simp add: anti_mono_initials_T leDT_imp_leT)


section \<open>Behaviour of \<^const>\<open>initials\<close> with \<^const>\<open>STOP\<close>, \<^const>\<open>SKIP\<close> and \<^term>\<open>\<bottom>\<close>\<close>

lemma initials_STOP [simp] : \<open>STOP\<^sup>0 = {}\<close>
  by (simp add: initials_def T_STOP)

text \<open>We already had @{thm STOP_iff_T}. As an immediate consequence we obtain a 
      characterization of being \<^const>\<open>STOP\<close> involving \<^const>\<open>initials\<close>.\<close>

lemma initials_empty_iff_STOP: \<open>P\<^sup>0 = {} \<longleftrightarrow> P = STOP\<close>
proof (intro iffI)
  { assume \<open>\<T> P \<noteq> {[]}\<close>
    then obtain a s where \<open>a # s \<in> \<T> P\<close> 
      by (metis Nil_elem_T is_singleton_the_elem is_singletonI'
          list.exhaust_sel singletonI empty_iff)
    with initials_memD initials_memI have \<open>\<exists>a. [a] \<in> \<T> P\<close> by blast}
  thus \<open>P\<^sup>0 = {} \<Longrightarrow> P = STOP\<close> 
    by (simp add: STOP_iff_T initials_def) presburger
next
  show \<open>P = STOP \<Longrightarrow> P\<^sup>0 = {}\<close> by simp
qed


lemma initials_SKIP [simp] : \<open>(SKIP r)\<^sup>0 = {\<checkmark>(r)}\<close>
  by (simp add: initials_def T_SKIP)

lemma initials_SKIPS [simp] : \<open>(SKIPS R)\<^sup>0 = tick ` R\<close>
  by (auto simp add: initials_def T_SKIPS)

lemma initials_BOT [simp] : \<open>\<bottom>\<^sup>0 = UNIV\<close>
  by (simp add: initials_def T_BOT)

text \<open>These two, on the other hand, are not characterizations.\<close>

lemma \<open>\<exists>P. P\<^sup>0 = {\<checkmark>(r)} \<and> P \<noteq> (SKIP r)\<close>
proof (intro exI)
  show \<open>(STOP \<sqinter> SKIP r)\<^sup>0 = {\<checkmark>(r)} \<and> STOP \<sqinter> SKIP r \<noteq> SKIP r\<close>
    by (simp add: initials_def T_Ndet T_STOP T_SKIP)
      (metis Ndet_FD_self_left SKIP_FD_iff SKIP_Neq_STOP)
qed

lemma \<open>\<exists>P. P\<^sup>0 = UNIV \<and> P \<noteq> \<bottom>\<close>
proof (intro exI)
  show \<open>((\<box>a \<in> UNIV \<rightarrow> \<bottom>) \<sqinter> SKIPS UNIV)\<^sup>0 = UNIV \<and> (\<box>a \<in> UNIV \<rightarrow> \<bottom>) \<sqinter> SKIPS UNIV \<noteq> \<bottom>\<close>
    by (simp add: set_eq_iff BOT_iff_Nil_D Ndet_projs Mprefix_projs
        SKIPS_projs initials_def) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
qed


text \<open>But when \<^term>\<open>\<checkmark>(r) \<in> P\<^sup>0\<close>, we can still have this refinement:\<close>

lemma initial_tick_iff_FD_SKIP : \<open>\<checkmark>(r) \<in> P\<^sup>0 \<longleftrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r\<close>
proof (intro iffI)
  show \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r\<close>
    unfolding failure_divergence_refine_def failure_refine_def divergence_refine_def
    by (simp add: F_SKIP D_SKIP subset_iff initials_def)
      (metis append_Nil is_processT6_TR_notin tick_T_F)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r \<Longrightarrow> \<checkmark>(r) \<in> P\<^sup>0\<close> by (auto dest: anti_mono_initials_FD)
qed


lemma initial_ticks_iff_FD_SKIPS : \<open>R \<noteq> {} \<Longrightarrow> tick ` R \<subseteq> P\<^sup>0 \<longleftrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D SKIPS R\<close>
proof (rule iffI)
  show \<open>R \<noteq> {} \<Longrightarrow> tick ` R \<subseteq> P\<^sup>0 \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D SKIPS R\<close>
    by (unfold SKIPS_def, rule mono_GlobalNdet_FD_const)
      (simp_all add: image_subset_iff initial_tick_iff_FD_SKIP)
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIPS R \<Longrightarrow> tick ` R \<subseteq> P\<^sup>0\<close>
    by (metis anti_mono_initials_FD initials_SKIPS)
qed



text \<open>We also obtain characterizations for \<^term>\<open>P \<^bold>; Q = \<bottom>\<close>.\<close>

lemma Seq_is_BOT_iff : \<open>P \<^bold>; Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> (\<exists>r. \<checkmark>(r) \<in> P\<^sup>0 \<and> Q = \<bottom>)\<close>
  by (simp add: BOT_iff_Nil_D D_Seq initials_def)

(* lemma MultiSeq_is_BOT_iff:
  \<open>(SEQ l \<in>@ L. P l) = \<bottom> \<longleftrightarrow> 
   (\<exists>j < first_elem (\<lambda>l. range \<checkmark> \<inter> initials (P l) = {}) L. P (L ! j) = \<bottom>)\<close>
  apply (induct L)
  apply (solves \<open>simp add: SKIP_neq_BOT\<close>)
  using initials_BOT less_Suc_eq_0_disj by (auto simp add: Seq_is_BOT_iff) *)



section \<open>Behaviour of \<^const>\<open>initials\<close> with Operators of \<^session>\<open>HOL-CSP\<close>\<close>

lemma initials_Mprefix :     \<open>(\<box>a \<in> A \<rightarrow> P a)\<^sup>0 = ev ` A\<close>
  and initials_Mndetprefix : \<open>(\<sqinter>a \<in> A \<rightarrow> P a)\<^sup>0 = ev ` A\<close>
  and initials_write0 :      \<open>(a \<rightarrow> Q)\<^sup>0        = {ev a}\<close>
  and initials_write :       \<open>(c\<^bold>!a \<rightarrow> Q)\<^sup>0     = {ev (c a)}\<close>
  and initials_read :        \<open>(c\<^bold>?a\<in>A \<rightarrow> P a)\<^sup>0 = ev ` c ` A\<close>
  and initials_ndet_write :  \<open>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<^sup>0 = ev ` c ` A\<close>
  by (auto simp: initials_def T_Mndetprefix write0_def
      write_def T_Mprefix read_def ndet_write_def)


text \<open>As discussed earlier, \<^const>\<open>initials\<close> behaves very well
      with \<^term>\<open>(\<box>)\<close>, \<^term>\<open>(\<sqinter>)\<close> and \<^term>\<open>(\<rhd>)\<close>.\<close>

lemma initials_Det :     \<open>(P \<box> Q)\<^sup>0 = P\<^sup>0 \<union> Q\<^sup>0\<close>
  and initials_Ndet :    \<open>(P \<sqinter> Q)\<^sup>0 = P\<^sup>0 \<union> Q\<^sup>0\<close>
  and initials_Sliding : \<open>(P \<rhd> Q)\<^sup>0 = P\<^sup>0 \<union> Q\<^sup>0\<close>
  by (auto simp add: initials_def T_Det T_Ndet T_Sliding)


lemma initials_Seq: 
  \<open>(P \<^bold>; Q)\<^sup>0 = (  if P = \<bottom> then UNIV
               else P\<^sup>0 - range tick \<union> (\<Union>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0}. Q\<^sup>0))\<close>
  (is \<open>_ = (if _ then _ else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<Longrightarrow> (P \<^bold>; Q)\<^sup>0 = UNIV\<close> by simp
next
  show \<open>(P \<^bold>; Q)\<^sup>0 = P\<^sup>0 - range tick \<union> (\<Union>r\<in>{r. \<checkmark>(r) \<in> P\<^sup>0}. Q\<^sup>0)\<close> if \<open>P \<noteq> \<bottom>\<close>
  proof (intro subset_antisym subsetI)
    fix e assume \<open>e \<in> (P \<^bold>; Q)\<^sup>0\<close>
    from event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust consider a where \<open>e = ev a\<close> | r where \<open>e = \<checkmark>(r)\<close> by blast
    thus \<open>e \<in> ?rhs\<close>
    proof cases
      from \<open>e \<in> (P \<^bold>; Q)\<^sup>0\<close> show \<open>e = ev a \<Longrightarrow> e \<in> ?rhs\<close> for a
        by (simp add: image_iff initials_def T_Seq)
          (metis (no_types, lifting) D_T append_Cons append_Nil
            is_processT3_TR_append list.exhaust_sel list.sel(1))
    next
      from \<open>e \<in> (P \<^bold>; Q)\<^sup>0\<close> \<open>P \<noteq> \<bottom>\<close> show \<open>e = \<checkmark>(r) \<Longrightarrow> e \<in> ?rhs\<close> for r
        by (simp add: image_iff initials_def T_Seq BOT_iff_tick_D)
          (metis (no_types, opaque_lifting) append_T_imp_tickFree append_eq_Cons_conv
            event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) not_Cons_self2 tickFree_Cons_iff)
    qed
  next
    fix e assume \<open>e \<in> ?rhs\<close>
    then consider a where \<open>e = ev a\<close> \<open>ev a \<in> P\<^sup>0\<close>
      | r where \<open>\<checkmark>(r) \<in> P\<^sup>0\<close> \<open>e \<in> Q\<^sup>0\<close>
      by simp (metis empty_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust rangeI)
    thus \<open>e \<in> (P \<^bold>; Q)\<^sup>0\<close>
    proof cases
      show \<open>e = ev a \<Longrightarrow> ev a \<in> P\<^sup>0 \<Longrightarrow> e \<in> (P \<^bold>; Q)\<^sup>0\<close> for a
        by (simp add: initials_def T_Seq)
    next
      show \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> e \<in> Q\<^sup>0 \<Longrightarrow> e \<in> (P \<^bold>; Q)\<^sup>0\<close> for r
        by (simp add: initials_def T_Seq) (metis append_Nil)
    qed
  qed
qed




lemma initials_Sync:
  \<open>(P \<lbrakk>S\<rbrakk> Q)\<^sup>0 = (if P = \<bottom> \<or> Q = \<bottom> then UNIV else
                P\<^sup>0 \<union> Q\<^sup>0 - (range tick \<union> ev ` S) \<union> P\<^sup>0 \<inter> Q\<^sup>0 \<inter> (range tick \<union> ev ` S))\<close>
  (is \<open>(P \<lbrakk>S\<rbrakk> Q)\<^sup>0 = (if P = \<bottom> \<or> Q = \<bottom> then UNIV else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<or> Q = \<bottom> \<Longrightarrow> (P \<lbrakk>S\<rbrakk> Q)\<^sup>0 = UNIV\<close>
    by (metis Sync_is_BOT_iff initials_BOT)
next
  show \<open>(P \<lbrakk>S\<rbrakk> Q)\<^sup>0 = ?rhs\<close> if non_BOT : \<open>\<not> (P = \<bottom> \<or> Q = \<bottom>)\<close>
  proof (intro subset_antisym subsetI)
    show \<open>e \<in> ?rhs \<Longrightarrow> e \<in> (P \<lbrakk>S\<rbrakk> Q)\<^sup>0\<close> for e
    proof (elim UnE)
      assume \<open>e \<in> P\<^sup>0 \<union> Q\<^sup>0 - (range tick \<union> ev ` S)\<close>
      hence \<open>[e] \<in> \<T> P \<or> [e] \<in> \<T> Q\<close> \<open>e \<notin> range tick \<union> ev ` S\<close>
        by (auto dest: initials_memD)
      have \<open>[e] setinterleaves (([e], []), range tick \<union> ev ` S)\<close>
        using \<open>e \<notin> range tick \<union> ev ` S\<close> by simp
      with \<open>[e] \<in> \<T> P \<or> [e] \<in> \<T> Q\<close> is_processT1_TR setinterleaving_sym
      have \<open>[e] \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)\<close> by (simp (no_asm) add: T_Sync) blast
      thus \<open>e \<in> (P \<lbrakk>S\<rbrakk> Q)\<^sup>0\<close> by (simp add: initials_memI)
    next
      assume \<open>e \<in> P\<^sup>0 \<inter> Q\<^sup>0 \<inter> (range tick \<union> ev ` S)\<close>
      hence \<open>[e] \<in> \<T> P\<close> \<open>[e] \<in> \<T> Q\<close> \<open>e \<in> range tick \<union> ev ` S\<close>
        by (simp_all add: initials_memD)
      have \<open>[e] setinterleaves (([e], [e]), range tick \<union> ev ` S)\<close>
        using \<open>e \<in> range tick \<union> ev ` S\<close> by simp
      with \<open>[e] \<in> \<T> P\<close> \<open>[e] \<in> \<T> Q\<close> have \<open>[e] \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp (no_asm) add: T_Sync) blast
      thus \<open>e \<in> (P \<lbrakk>S\<rbrakk> Q)\<^sup>0\<close> by (simp add: initials_memI)
    qed
  next
    fix e
    assume \<open>e \<in> (P \<lbrakk>S\<rbrakk> Q)\<^sup>0\<close>
    then consider t u where \<open>t \<in> \<T> P\<close> \<open>u \<in> \<T> Q\<close> \<open>[e] setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
      | (div) t u r v where \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> \<open>[e] = r @ v\<close>
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
        \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close>
      by (simp add: initials_def T_Sync) blast
    thus \<open>e \<in> ?rhs\<close>
    proof cases
      show \<open>t \<in> \<T> P \<Longrightarrow> u \<in> \<T> Q \<Longrightarrow> [e] setinterleaves ((t, u), range tick \<union> ev ` S)
            \<Longrightarrow> e \<in> ?rhs\<close> for t u
        by (cases t; cases u; simp add: initials_def image_iff split: if_split_asm)
          (use empty_setinterleaving setinterleaving_sym in blast)+
    next
      case div
      have \<open>r \<noteq> []\<close> using div(4, 5) BOT_iff_Nil_D empty_setinterleaving that by blast
      hence \<open>r = [e] \<and> v = []\<close>
        by (metis (no_types, lifting) div(3) Nil_is_append_conv append_eq_Cons_conv)
      also from div(5) BOT_iff_Nil_D non_BOT
      obtain e' t' where \<open>t = e' # t'\<close> by (cases t) blast+
      ultimately show \<open>e \<in> ?rhs\<close> 
        using div(4, 5)
        by (cases u, simp_all add: initials_def subset_iff T_Sync image_iff split: if_split_asm)
          (metis [[metis_verbose = false]] D_T setinterleaving_sym empty_setinterleaving)+
    qed
  qed
qed



lemma initials_Renaming:
  \<open>(Renaming P f g)\<^sup>0 = (if P = \<bottom> then UNIV else map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g ` P\<^sup>0)\<close>
proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<Longrightarrow> (Renaming P f g)\<^sup>0 = UNIV\<close> by simp
next
  assume \<open>P \<noteq> \<bottom>\<close>
  hence \<open>[] \<notin> \<D> P\<close> by (simp add: BOT_iff_Nil_D)
  show \<open>(Renaming P f g)\<^sup>0 = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g ` P\<^sup>0\<close>
  proof (intro subset_antisym subsetI)
    fix e assume \<open>e \<in> (Renaming P f g)\<^sup>0\<close>
    with \<open>[] \<notin> \<D> P\<close> obtain s where * : \<open>[e] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s\<close> \<open>s \<in> \<T> P\<close>
      by (simp add: initials_def T_Renaming)
        (metis D_T append.right_neutral append_is_Nil_conv list.map_disc_iff list.sel(3) tl_append2)
    from "*"(1) obtain e' where ** : \<open>s = [e']\<close> \<open>e = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e'\<close> by blast
    from "**"(1) "*"(2) have \<open>e' \<in> P\<^sup>0\<close> by (simp add: initials_def)
    with "**"(2) show \<open>e \<in> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g ` P\<^sup>0\<close> by simp
  next
    fix e assume \<open>e \<in> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g ` P\<^sup>0\<close>
    then obtain e' where \<open>e = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e'\<close> \<open>e' \<in> P\<^sup>0\<close> by fast
    thus \<open>e \<in> (Renaming P f g)\<^sup>0\<close> by (auto simp add: initials_def T_Renaming)
  qed
qed




text \<open>Because for the expression of its traces (and more specifically of its divergences),
      dealing with \<^const>\<open>Hiding\<close> is much more difficult.\<close>

text \<open>We start with two characterizations:
      \<^item> the first one to understand \<^prop>\<open>P \ S = \<bottom>\<close>
      \<^item> the other one to understand \<^prop>\<open>[e] \<in> \<D> (P \ S)\<close>.\<close>

lemma Hiding_is_BOT_iff : 
  \<open>P \ S = \<bottom> \<longleftrightarrow> (\<exists>t. set t \<subseteq> ev ` S \<and> 
                      (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f)))\<close>
  (is \<open>P \ S = \<bottom> \<longleftrightarrow> ?rhs\<close>)
proof (subst BOT_iff_Nil_D, intro iffI)
  show \<open>[] \<in> \<D> (P \ S) \<Longrightarrow> ?rhs\<close>
    by (simp add: D_Hiding)
      (metis (no_types, lifting) filter_empty_conv subsetI)
next
  assume \<open>?rhs\<close>
  then obtain t where * : \<open>set t \<subseteq> ev ` S\<close>
    \<open>t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P S \<and> t \<in> range f)\<close> by blast
  hence \<open>tickFree t \<and> [] = trace_hide t (ev ` S)\<close>
    unfolding tickFree_def by (auto simp add: D_Hiding subset_iff)
  with "*"(2) show \<open>[] \<in> \<D> (P \ S)\<close> by (simp add: D_Hiding) metis
qed

lemma event_in_D_Hiding_iff :
  \<open>[e] \<in> \<D> (P \ S) \<longleftrightarrow>
   P \ S = \<bottom> \<or> (\<exists>x t. e = ev x \<and> x \<notin> S \<and> [ev x] = trace_hide t (ev ` S) \<and>
                      (t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P S \<and> t \<in> range f)))\<close>
  (is \<open>[e] \<in> \<D> (P \ S) \<longleftrightarrow> P \ S = \<bottom> \<or> ?ugly_assertion\<close>)
proof (intro iffI)
  assume assm : \<open>[e] \<in> \<D> (P \ S)\<close>
  show \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close>
  proof (cases e)
    fix r assume \<open>e = \<checkmark>(r)\<close>
    with assm have \<open>P \ S = \<bottom>\<close>
      using BOT_iff_tick_D front_tickFree_Nil is_processT9_tick by blast
    thus \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close> by blast
  next
    fix x
    assume \<open>e = ev x\<close>
    with assm obtain t u
      where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close>
        \<open>[ev x] = trace_hide t (ev ` S) @ u\<close>
        \<open>t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f)\<close>
      by (simp add: D_Hiding) blast
    from "*"(3) consider \<open>set t \<subseteq> ev ` S\<close> | \<open>x \<notin> S\<close> \<open>ev x \<in> set t\<close>
      by (metis (no_types, lifting) Cons_eq_append_conv empty_filter_conv
          filter_eq_Cons_iff filter_is_subset image_eqI list.set_intros(1) subset_code(1))
    thus \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close>
    proof cases
      assume \<open>set t \<subseteq> ev ` S\<close>
      hence \<open>P \ S = \<bottom>\<close> by (meson "*"(4) Hiding_is_BOT_iff)
      thus \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close> by blast
    next
      assume \<open>x \<notin> S\<close> \<open>ev x \<in> set t\<close>
      with "*"(3) have \<open>[ev x] = trace_hide t (ev ` S)\<close>
        by (induct t) (auto split: if_split_asm)
      with "*"(4) \<open>e = ev x\<close> \<open>x \<notin> S\<close> have \<open>?ugly_assertion\<close> by blast
      thus \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close> by blast
    qed
  qed
next
  show \<open>P \ S = \<bottom> \<or> ?ugly_assertion \<Longrightarrow> [e] \<in> \<D> (P \ S)\<close>
  proof (elim disjE)
    show \<open>P \ S = \<bottom> \<Longrightarrow> [e] \<in> \<D> (P \ S)\<close> by (simp add: D_BOT)
  next
    show \<open>?ugly_assertion \<Longrightarrow> [e] \<in> \<D> (P \ S)\<close>
      by (elim exE conjE, simp add: D_Hiding)
        (metis Hiding_tickFree append_Cons append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1)
          front_tickFree_Nil non_tickFree_imp_not_Nil tickFree_Cons_iff)
  qed
qed


text \<open>Now we can express \<^term>\<open>initials (P \ S)\<close>.
      This result contains the term \<^term>\<open>P \ S = \<bottom>\<close> that can be unfolded with
      @{thm [source] Hiding_is_BOT_iff} and the term \<^term>\<open>[ev x] \<in> \<D> (P \ S)\<close>
      that can be unfolded with @{thm [source] event_in_D_Hiding_iff}.\<close>

lemma initials_Hiding:
  \<open>(P \ S)\<^sup>0 = (if P \ S = \<bottom> then UNIV else
               {e. case e of ev x \<Rightarrow> x \<notin> S \<and> ([ev x] \<in> \<D> (P \ S) \<or> (\<exists>t. [ev x] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P))
                           | \<checkmark>(r) \<Rightarrow> \<exists>t. set t \<subseteq> ev ` S \<and> t @ [\<checkmark>(r)] \<in> \<T> P})\<close>
  (is \<open>initials (P \ S) = (if P \ S = \<bottom> then UNIV else ?set)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>P \ S = \<bottom> \<Longrightarrow> initials (P \ S) = UNIV\<close> by simp
next
  assume non_BOT : \<open>P \ S \<noteq> \<bottom>\<close>
  show \<open>initials (P \ S) = ?set\<close>
  proof (intro subset_antisym subsetI)
    fix e
    assume initial : \<open>e \<in> initials (P \ S)\<close>
      \<comment> \<open>This implies \<^prop>\<open>e \<notin> ev ` S\<close> with our other assumptions.\<close>
    { fix x
      assume assms : \<open>x \<in> S\<close> \<open>ev x \<in> initials (P \ S)\<close>
      then consider \<open>\<exists>t. [ev x] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
        | \<open>\<exists>t u. front_tickFree u \<and> tickFree t \<and> [ev x] = trace_hide t (ev ` S) @ u \<and> 
                 (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f))\<close>
        by (simp add: initials_def T_Hiding) blast
      hence \<open>P \ S = \<bottom>\<close>
      proof cases
        assume \<open>\<exists>t. [ev x] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
        hence False by (metis Cons_eq_filterD image_eqI assms(1))
        thus \<open>P \ S = \<bottom>\<close> by blast
      next
        assume \<open>\<exists>t u. front_tickFree u \<and> tickFree t \<and> [ev x] = trace_hide t (ev ` S) @ u \<and>
                      (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f))\<close>
        then obtain t u 
          where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>[ev x] = trace_hide t (ev ` S) @ u\<close>
            \<open>t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f)\<close> by blast
        from *(3) have ** : \<open>set t \<subseteq> ev ` S\<close>
          by (induct t) (simp_all add: assms(1) split: if_split_asm)
        from *(4) "**" Hiding_is_BOT_iff show \<open>P \ S = \<bottom>\<close> by blast
      qed
    }
    with initial have * : \<open>e \<notin> ev ` S\<close> using non_BOT by blast

    from initial consider \<open>[e] \<in> \<D> (P \ S)\<close>
      | \<open>\<exists>t. [e] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
      unfolding initials_def by (simp add: T_Hiding D_Hiding) blast
    thus \<open>e \<in> ?set\<close>
    proof cases
      assume assm : \<open>[e] \<in> \<D> (P \ S)\<close>
      then obtain x where \<open>e = ev x\<close>
        by (metis BOT_iff_Nil_D append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust non_BOT process_charn)
      with assm "*" show \<open>e \<in> ?set\<close> by (simp add: image_iff)
    next
      assume \<open>\<exists>t. [e] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
      then obtain t where ** : \<open>[e] = trace_hide t (ev ` S)\<close>
        \<open>(t, ev ` S) \<in> \<F> P\<close> by blast
      thus \<open>e \<in> ?set\<close>
      proof (cases e)
        have \<open>e = \<checkmark>(r) \<Longrightarrow> set (butlast t) \<subseteq> ev ` S \<and> butlast t @ [\<checkmark>(r)] \<in> \<T> P\<close> for r
          using "**" by (cases t rule: rev_cases; simp add: F_T empty_filter_conv subset_eq split: if_split_asm)
            (metis F_T Hiding_tickFree append_T_imp_tickFree neq_Nil_conv non_tickFree_tick)
        thus \<open>e = \<checkmark>(r) \<Longrightarrow> e \<in> ?set\<close> for r by auto
      next
        fix x
        assume \<open>e = ev x\<close>
        with "*" have \<open>x \<notin> S\<close> by blast
        with \<open>e = ev x\<close> "**"(1) "**"(2) show \<open>e \<in> ?set\<close> by auto
      qed
    qed
  next
    fix e
    assume \<open>e \<in> ?set\<close>
    then consider r where \<open>e = \<checkmark>(r)\<close> \<open>\<exists>t. set t \<subseteq> ev ` S \<and> t @ [\<checkmark>(r)] \<in> \<T> P\<close>
      | a where \<open>e = ev a\<close> \<open>a \<notin> S\<close>
        \<open>[ev a] \<in> \<D> (P \ S) \<or>
                 (\<exists>t. [ev a] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P)\<close> by (cases e) simp_all
    thus \<open>e \<in> initials (P \ S)\<close>
    proof cases
      fix r assume assms : \<open>e = \<checkmark>(r)\<close> \<open>\<exists>t. set t \<subseteq> ev ` S \<and> t @ [\<checkmark>(r)] \<in> \<T> P\<close>
      from assms(2) obtain t
        where * : \<open>set t \<subseteq> ev ` S\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> by blast
      have ** : \<open>[e] = trace_hide (t @ [\<checkmark>(r)]) (ev ` S) \<and> (t @ [\<checkmark>(r)], ev ` S) \<in> \<F> P\<close>
        using "*"(1) by (simp add: assms(1) image_iff tick_T_F[OF "*"(2)] subset_iff)
      show \<open>e \<in> initials (P \ S)\<close>
        unfolding initials_def by (simp add: T_Hiding) (use "**" in blast)
    next
      show \<open>[ev a] \<in> \<D> (P \ S) \<or>
            (\<exists>t. [ev a] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P) \<Longrightarrow> e \<in> (P \ S)\<^sup>0\<close>
        if \<open>e = ev a\<close> for a
      proof (elim exE conjE disjE)
        show \<open>[ev a] \<in> \<D> (P \ S) \<Longrightarrow> e \<in> (P \ S)\<^sup>0\<close>
          by (simp add: \<open>e = ev a\<close> D_T initials_memI')
      next
        show \<open>[ev a] = trace_hide t (ev ` S) \<Longrightarrow> (t, ev ` S) \<in> \<F> P \<Longrightarrow> e \<in> (P \ S)\<^sup>0\<close> for t
          by (metis F_T initials_memI' mem_T_imp_mem_T_Hiding \<open>e = ev a\<close>)
      qed
    qed
  qed
qed


text \<open>In the end the result would look something like this:

      @{thm initials_Hiding[unfolded event_in_D_Hiding_iff Hiding_is_BOT_iff, no_vars]}\<close>

text \<open>Obviously, it is not very easy to use. We will therefore rely more on the corollaries below.\<close>

corollary initial_tick_Hiding_iff :
  \<open>\<checkmark>(r) \<in> (P \ B)\<^sup>0 \<longleftrightarrow> P \ B = \<bottom> \<or> (\<exists>t. set t \<subseteq> ev ` B \<and> t @ [\<checkmark>(r)] \<in> \<T> P)\<close>
  by (simp add: initials_Hiding)

corollary initial_tick_imp_initial_tick_Hiding:
  \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> \<checkmark>(r) \<in> (P \ B)\<^sup>0\<close>
  by (subst initials_Hiding, simp add: initials_def)
    (metis append_Nil empty_iff empty_set subset_iff)


corollary initial_inside_Hiding_iff :
  \<open>e \<in> S \<Longrightarrow> ev e \<in> (P \ S)\<^sup>0 \<longleftrightarrow> P \ S = \<bottom>\<close>
  by (simp add: initials_Hiding)


corollary initial_notin_Hiding_iff :
  \<open>e \<notin> S \<Longrightarrow> ev e \<in> (P \ S)\<^sup>0 \<longleftrightarrow>
   P \ S = \<bottom> \<or>
   (\<exists>t. [ev e] = trace_hide t (ev ` S) \<and>
        (t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P S \<and> t \<in> range f) \<or> (t, ev ` S) \<in> \<F> P))\<close>
  by (auto simp add: initials_Hiding event_in_D_Hiding_iff split: if_split_asm)


corollary initial_notin_imp_initial_Hiding:
  \<open>ev e \<in> (P \ S)\<^sup>0\<close> if initial : \<open>ev e \<in> P\<^sup>0\<close> and notin : \<open>e \<notin> S\<close>
proof -
  from inf_hidden[of S \<open>[ev e]\<close> P]
  consider f where \<open>isInfHiddenRun f P S\<close> \<open>[ev e] \<in> range f\<close>  
    | t where \<open>[ev e] = trace_hide t (ev ` S)\<close> \<open>(t, ev ` S) \<in> \<F> P\<close>
    by (simp add: initials_Hiding image_iff[of \<open>ev e\<close>] notin)
      (metis mem_Collect_eq initial initials_def)
  thus \<open>ev e \<in> initials (P \ S)\<close>
  proof cases
    show \<open>ev e \<in> (P \ S)\<^sup>0\<close> if \<open>isInfHiddenRun f P S\<close> \<open>[ev e] \<in> range f\<close> for f
    proof (intro initials_memI[of \<open>ev e\<close> \<open>[]\<close>] D_T)
      from that show \<open>[ev e] \<in> \<D> (P \ S)\<close>
        by (simp add: event_in_D_Hiding_iff image_iff[of \<open>ev e\<close>] notin)
          (metis (no_types, lifting) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) filter.simps image_iff notin)
    qed
  next
    show \<open>[ev e] = trace_hide t (ev ` S) \<Longrightarrow> (t, ev ` S) \<in> \<F> P \<Longrightarrow> ev e \<in> (P \ S)\<^sup>0\<close> for t
      by (auto simp add: initials_Hiding notin)
  qed
qed  



section \<open>Behaviour of \<^const>\<open>initials\<close> with Operators of \<^session>\<open>HOL-CSPM\<close>\<close>

lemma initials_GlobalDet:
  \<open>(\<box>a \<in> A. P a)\<^sup>0 = (\<Union>a \<in> A. initials (P a))\<close>
  by (auto simp add: initials_def T_GlobalDet)

lemma initials_GlobalNdet:
  \<open>(\<sqinter>a \<in> A. P a)\<^sup>0 = (\<Union>a \<in> A. initials (P a))\<close>
  by (auto simp add: initials_def T_GlobalNdet)



(* lemma initials_MultiSeq:
  \<open>initials (SEQ l \<in>@ L. P l) =
   (let i = first_elem (\<lambda>l. \<checkmark> \<notin> initials (P l)) L
     in   if (\<exists>j < i. P (L ! j) = \<bottom>)
        then UNIV 
        else let S = (\<Union>l \<in> set (take (Suc i) L). initials (P l)) - {\<checkmark>}
              in if i < length L then S else insert \<checkmark> S)\<close>
  unfolding Let_def
proof (induct L)
  case Nil
  thus ?case by (simp add: initials_SKIP SKIP_neq_BOT)
next
  case (Cons l L)
  show ?case
    apply (simp add: initials_Seq initials_BOT local.Cons, intro conjI impI)
           apply ((metis nth_Cons_0 zero_less_Suc)+)[1]
          apply ((metis Suc_less_eq nth_Cons_Suc)+)[2]
        apply (metis nth_Cons_0 zero_less_Suc)
    by (metis less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc, blast)+
qed *)


lemma initials_MultiSync:
  \<open>initials (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m) =
   (  if M = {#} then {}
    else if \<exists>m \<in># M. P m = \<bottom> then UNIV
    else if \<exists>m. M = {#m#} then initials (P (THE m. M = {#m#}))
    else {e. \<exists>m \<in># M. e \<in> initials (P m) - (range tick \<union> ev ` S)} \<union>
         {e \<in> range tick \<union> ev ` S. \<forall>m \<in># M. e \<in> initials (P m)})\<close>
proof -
  have * : \<open>initials (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># (M + {#a, a'#}). P m) = 
            {e. \<exists>m \<in># M + {#a, a'#}. e \<in> initials (P m) - (range tick \<union> ev ` S)} \<union>
            {e \<in> range tick \<union> ev ` S. \<forall>m \<in># M + {#a, a'#}. e \<in> initials (P m)}\<close>
    if non_BOT : \<open>\<forall>m \<in># M + {#a, a'#}. P m \<noteq> \<bottom>\<close> for a a' M
  proof (induct M rule: msubset_induct'[OF subset_mset.refl])
    case 1
    then show ?case by (auto simp add: non_BOT initials_Sync)
  next
    case (2 a'' M')
    have * : \<open>MultiSync S (add_mset a'' M' + {#a, a'#}) P = 
              P a'' \<lbrakk>S\<rbrakk> (MultiSync S (M' + {#a, a'#}) P)\<close> 
      by (simp add: add_mset_commute)
    have ** : \<open>\<not> (P a'' = \<bottom> \<or> MultiSync S (M' + {#a, a'#}) P = \<bottom>)\<close>
      using "2.hyps"(1, 2) in_diffD non_BOT 
      by (auto simp add: MultiSync_is_BOT_iff Sync_is_BOT_iff, fastforce, meson mset_subset_eqD)
    show ?case
      by (auto simp only: * initials_Sync ** "2.hyps"(3), auto)
  qed

  show ?thesis
  proof (cases \<open>\<exists>m \<in># M. P m = \<bottom>\<close>)
    show \<open>\<exists>m \<in># M. P m = \<bottom> \<Longrightarrow> ?thesis\<close>
      by simp (metis MultiSync_BOT_absorb initials_BOT)
  next
    show \<open>\<not> (\<exists>m\<in>#M. P m = \<bottom>) \<Longrightarrow> ?thesis\<close>
    proof (cases \<open>\<exists>a a' M'. M = M' + {#a, a'#}\<close>)
      assume assms : \<open>\<not> (\<exists>m\<in>#M. P m = \<bottom>)\<close> \<open>\<exists>a a' M'. M = M' + {#a, a'#}\<close>
      from assms(2) obtain a a' M' where \<open>M = M' + {#a, a'#}\<close> by blast
      with * assms(1) show ?thesis by simp
    next
      assume \<open>\<nexists>a a' M'. M = M' + {#a, a'#}\<close>
      hence \<open>M = {#} \<or> (\<exists>m. M = {#m#})\<close>
        by (metis add.right_neutral multiset_cases union_mset_add_mset_right)
      thus ?thesis by auto
    qed
  qed
qed



lemma initials_Throw : \<open>(P \<Theta> a \<in> A. Q a)\<^sup>0 = P\<^sup>0\<close>
proof (cases \<open>P = \<bottom>\<close>)
  show \<open>P = \<bottom> \<Longrightarrow> (P \<Theta> a \<in> A. Q a)\<^sup>0 = P\<^sup>0\<close> by simp
next
  show \<open>(P \<Theta> a \<in> A. Q a)\<^sup>0 = P\<^sup>0\<close> if \<open>P \<noteq> \<bottom>\<close>
  proof (intro subset_antisym subsetI)
    from \<open>P \<noteq> \<bottom>\<close> show \<open>e \<in> (P \<Theta> a \<in> A. Q a)\<^sup>0 \<Longrightarrow> e \<in> P\<^sup>0\<close> for e
      by (auto simp add: T_Throw D_T is_processT7 Cons_eq_append_conv BOT_iff_Nil_D
          intro!: initials_memI' dest!: initials_memD)
  next
    show \<open>e \<in> P\<^sup>0 \<Longrightarrow> e \<in> (P \<Theta> a \<in> A. Q a)\<^sup>0\<close> for e
      by (auto simp add: initials_memD T_Throw Cons_eq_append_conv
          intro!: initials_memI')
  qed
qed


lemma initials_Interrupt: \<open>(P \<triangle> Q)\<^sup>0 = P\<^sup>0 \<union> Q\<^sup>0\<close>
proof (intro subset_antisym subsetI)
  show \<open>e \<in> (P \<triangle> Q)\<^sup>0 \<Longrightarrow> e \<in> P\<^sup>0 \<union> Q\<^sup>0\<close> for e
    by (auto simp add: T_Interrupt Cons_eq_append_conv
        dest!: initials_memD intro: initials_memI)
next
  show \<open>e \<in> P\<^sup>0 \<union> Q\<^sup>0 \<Longrightarrow> e \<in> (P \<triangle> Q)\<^sup>0\<close> for e
    by (force simp add: initials_def T_Interrupt)
qed







section \<open>Behaviour of \<^const>\<open>initials\<close> with Reference Processes\<close>

lemma initials_DF: \<open>(DF A)\<^sup>0 = ev ` A\<close>
  by (subst DF_unfold) (simp add: initials_Mndetprefix)

lemma initials_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: \<open>(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<^sup>0 = ev ` A \<union> tick ` R\<close>
  by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
    (simp add: initials_Mndetprefix initials_Ndet)

lemma initials_RUN: \<open>(RUN A)\<^sup>0 = ev ` A\<close>
  by (subst RUN_unfold) (simp add: initials_Mprefix)

lemma initials_CHAOS: \<open>(CHAOS A)\<^sup>0 = ev ` A\<close>
  by (subst CHAOS_unfold)
    (simp add: initials_Mprefix initials_Ndet)

lemma initials_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: \<open>(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<^sup>0 = ev ` A \<union> tick ` R\<close>
  by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
    (auto simp add: initials_Mprefix initials_Ndet)


lemma empty_ev_initials_iff_empty_events_of :
  \<open>{a. ev a \<in> P\<^sup>0} = {} \<longleftrightarrow> \<alpha>(P) = {}\<close>
proof (rule iffI)
  show \<open>\<alpha>(P) = {} \<Longrightarrow> {a. ev a \<in> P\<^sup>0} = {}\<close>
    by (auto simp add: initials_def events_of_def)
next
  show \<open>\<alpha>(P) = {}\<close> if \<open>{a. ev a \<in> P\<^sup>0} = {}\<close>
  proof (rule ccontr)
    assume \<open>\<alpha>(P) \<noteq> {}\<close>
    then obtain a t where \<open>t \<in> \<T> P\<close> \<open>ev a \<in> set t\<close>
      by (meson equals0I events_of_memD)
    from \<open>t \<in> \<T> P\<close> consider \<open>t = []\<close> | r where \<open>t = [\<checkmark>(r)]\<close> | b t' where \<open>t = ev b # t'\<close>
      by (metis T_imp_front_tickFree \<open>ev a \<in> set t\<close> front_tickFree_Cons_iff
          is_ev_def list.distinct(1) list.set_cases)
    thus False
    proof cases
      from \<open>ev a \<in> set t\<close> show \<open>t = [] \<Longrightarrow> False\<close> by simp
    next
      from \<open>ev a \<in> set t\<close> show \<open>t = [\<checkmark>(r)] \<Longrightarrow> False\<close> for r by simp
    next
      fix b t' assume \<open>t = ev b # t'\<close>
      with \<open>t \<in> \<T> P\<close> have \<open>b \<in> {a. ev a \<in> P\<^sup>0}\<close> by (simp add: initials_memI)
      with \<open>{a. ev a \<in> P\<^sup>0} = {}\<close> show False by simp
    qed
  qed
qed



section \<open>Properties of \<^const>\<open>initials\<close> related to continuity\<close>

text \<open>We prove here some properties that we will need later in continuity or admissibility proofs.\<close>

lemma initials_LUB:
  \<open>chain Y \<Longrightarrow> (\<Squnion>i. Y i)\<^sup>0 = (\<Inter>P \<in> (range Y). P\<^sup>0)\<close>
  unfolding initials_def by (auto simp add: limproc_is_thelub T_LUB)


lemma adm_in_F: \<open>cont u \<Longrightarrow> adm (\<lambda>x. (s, X) \<in> \<F> (u x))\<close>
  by (simp add: adm_def cont2contlubE limproc_is_thelub ch2ch_cont F_LUB)

lemma adm_in_D: \<open>cont u \<Longrightarrow> adm (\<lambda>x. s \<in> \<D> (u x))\<close>
  by (simp add: D_LUB_2 adm_def ch2ch_cont cont2contlubE limproc_is_thelub)

lemma adm_in_T: \<open>cont u \<Longrightarrow> adm (\<lambda>x. s \<in> \<T> (u x))\<close>
  by (fold T_F_spec) (fact adm_in_F)

lemma initial_adm[simp] : \<open>cont u \<Longrightarrow> adm (\<lambda>x. e \<in> (u x)\<^sup>0)\<close>
  unfolding initials_def by (simp add: adm_in_T)


(*<*)
end
  (*>*)
