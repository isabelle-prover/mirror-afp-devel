(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Basic laws
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

section\<open> The Basic Laws \<close>

(*<*)
theory Basic_CSP_Laws                                               
  imports Constant_Processes Deterministic_Choice Non_Deterministic_Choice
    Global_Non_Deterministic_Choice Sliding_Choice
    Multi_Deterministic_Prefix_Choice Multi_Non_Deterministic_Prefix_Choice
    Sequential_Composition Synchronization_Product Hiding Renaming CSP_Monotonies
begin
  (*>*)

text \<open>By ``basic'' laws we mean the behaviour of \<^term>\<open>\<bottom>\<close>, \<^const>\<open>STOP\<close> and \<^const>\<open>SKIP\<close>,
      plus the associativity of some concerned operators.\<close>


subsection \<open>The Laws of \<^term>\<open>\<bottom>\<close>\<close>

text \<open>From the characterization @{thm BOT_iff_Nil_D}, we can easily derive the behaviour
      of \<^term>\<open>\<bottom>\<close> wrt. \<^const>\<open>STOP\<close>, \<^const>\<open>SKIP\<close>, and the operators.\<close>

lemma BOT_less1 [simp]: \<open>(\<bottom> :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<le> X\<close>
  by (simp add: le_approx_imp_le_ref)

lemma STOP_neq_BOT [simp] : \<open>STOP   \<noteq> \<bottom>\<close>
  and SKIP_neq_BOT [simp] : \<open>SKIP r \<noteq> \<bottom>\<close>
  by (simp_all add: BOT_iff_Nil_D D_STOP D_SKIP)


lemma Det_is_BOT_iff : \<open>P \<box> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Det D_BOT)

lemma Det_BOT [simp] : \<open>P \<box> \<bottom> = \<bottom>\<close> and BOT_Det [simp] : \<open>\<bottom> \<box> P = \<bottom>\<close>
  by (simp_all add: Det_is_BOT_iff)


lemma Ndet_is_BOT_iff : \<open>P \<sqinter> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Ndet D_BOT)

lemma Ndet_BOT [simp] : \<open>P \<sqinter> \<bottom> = \<bottom>\<close> and BOT_Ndet [simp] : \<open>\<bottom> \<sqinter> P = \<bottom>\<close>
  by (simp_all add: Ndet_is_BOT_iff)


lemma Sliding_is_BOT_iff: \<open>P \<rhd> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: Sliding_def Ndet_is_BOT_iff Det_is_BOT_iff)

lemma Sliding_BOT [simp] : \<open>P \<rhd> \<bottom> = \<bottom>\<close> and BOT_Sliding [simp] : \<open>\<bottom> \<rhd> P = \<bottom>\<close>
  by (simp_all add: Sliding_is_BOT_iff)


lemma Mprefix_neq_BOT [simp] : \<open>\<box> a \<in> A \<rightarrow> P a \<noteq> \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Mprefix)

lemma Mndetprefix_neq_BOT [simp] : \<open>\<sqinter> a \<in> A \<rightarrow> P a \<noteq> \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Mndetprefix write0_def D_Mprefix)


lemma Seq_is_BOT_iff : \<open>P \<^bold>; Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> (\<exists>r. [\<checkmark>(r)] \<in> \<T> P \<and> Q = \<bottom>)\<close>
  by (simp add: BOT_iff_Nil_D D_Seq)

lemma BOT_Seq [simp] : \<open>\<bottom> \<^bold>; P = \<bottom>\<close> by (simp add: Seq_is_BOT_iff)


lemma Hiding_BOT [simp] : \<open>\<bottom> \ A = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Hiding BOT_projs)
    (meson filter.simps(1) tickFree_Nil tickFree_imp_front_tickFree)


lemma Sync_is_BOT_iff : \<open>P \<lbrakk>S\<rbrakk> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Sync)
    (metis si_empty1 empty_setinterleaving insertI1 is_processT1_TR)

lemma Sync_BOT [simp] : \<open>P \<lbrakk> S \<rbrakk> \<bottom> = \<bottom>\<close> and BOT_Sync [simp] : \<open>\<bottom> \<lbrakk> S \<rbrakk> P = \<bottom>\<close>
  by (simp_all add: Sync_is_BOT_iff)


lemma Renaming_is_BOT_iff : \<open>Renaming P f g = \<bottom> \<longleftrightarrow> P = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Renaming)

lemma Renaming_BOT [simp] : \<open>Renaming \<bottom> f g = \<bottom>\<close>
  by (simp add: Renaming_is_BOT_iff)


lemma GlobalNdet_is_BOT_iff : \<open>(\<sqinter>a\<in>A. P a) = \<bottom> \<longleftrightarrow> (\<exists>a\<in>A. P a = \<bottom>)\<close>
  by (simp add: BOT_iff_Nil_D D_GlobalNdet)

lemma GlobalNdet_BOT [simp] : \<open>a \<in> A \<Longrightarrow> P a = \<bottom> \<Longrightarrow> (\<sqinter>a\<in>A. P a) = \<bottom>\<close>
  by (auto simp add: GlobalNdet_is_BOT_iff)



subsection \<open>The Laws of \<^const>\<open>STOP\<close>\<close>

text \<open>From the characterization @{thm STOP_iff_T}, we can easily derive the behaviour
      of \<^const>\<open>STOP\<close> wrt. \<^const>\<open>SKIP\<close> and the operators.\<close>

lemma SKIP_Neq_STOP : \<open>SKIP r \<noteq> STOP\<close>
  by (simp add: STOP_iff_T T_SKIP)


lemma Det_is_STOP_iff : \<open>P \<box> Q = STOP \<longleftrightarrow> P = STOP \<and> Q = STOP\<close>
  by (simp add: STOP_iff_T T_Det) (use Nil_elem_T in blast)

lemma Det_STOP [simp] : \<open>P \<box> STOP = P\<close> and STOP_Det [simp] : \<open>STOP \<box> P = P\<close>
  by (auto simp add: Process_eq_spec F_Det F_STOP D_Det D_STOP T_STOP
      intro: is_processT8 is_processT6_TR_notin)


lemma Ndet_is_STOP_iff : \<open>P \<sqinter> Q = STOP \<longleftrightarrow> P = STOP \<and> Q = STOP\<close>
  by (simp add: STOP_iff_T T_Ndet) (use Nil_elem_T in blast)


lemma Sliding_is_STOP_iff: \<open>P \<rhd> Q = STOP \<longleftrightarrow> P = STOP \<and> Q = STOP\<close>
  by (simp add: Sliding_def Ndet_is_STOP_iff Det_is_STOP_iff)

lemma Sliding_STOP [simp] : \<open>P \<rhd> STOP = P \<sqinter> STOP\<close> and STOP_Sliding [simp] : \<open>STOP \<rhd> P = P\<close>
  by (simp_all add: Sliding_def)


lemma Mprefix_is_STOP_iff : \<open>\<box> a \<in> A \<rightarrow> P a = STOP \<longleftrightarrow> A = {}\<close>
  by (simp add: STOP_iff_T T_Mprefix) (use Nil_elem_T in blast)

lemma Mprefix_empty [simp] : \<open>\<box> a \<in> {} \<rightarrow> P a = STOP\<close>
  by (simp add: Mprefix_is_STOP_iff)

lemma Mndetprefix_is_STOP_iff : \<open>\<sqinter> a \<in> A \<rightarrow> P a = STOP \<longleftrightarrow> A = {}\<close>
  by (simp add: STOP_iff_T T_Mndetprefix') (use Nil_elem_T in blast)

lemma Mndetprefix_empty [simp] : \<open>\<sqinter> a \<in> {} \<rightarrow> P a = STOP\<close>
  by (simp add: Mndetprefix_is_STOP_iff)


lemma Seq_is_STOP_iff :
  \<open>P \<^bold>; Q = STOP \<longleftrightarrow> \<T> P \<subseteq> insert [] {[\<checkmark>(r)]| r. True} \<and> (P \<noteq> STOP \<longrightarrow> Q = STOP)\<close>
proof (intro iffI conjI subsetI)
  show \<open>P \<^bold>; Q = STOP \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> t \<in> insert [] {[\<checkmark>(r)] |r. True}\<close> for t
    by (simp add: STOP_iff_T T_Seq set_eq_iff)
      (metis T_nonTickFree_imp_decomp append.right_neutral append_Nil is_processT1_TR)
next
  show \<open>P \<^bold>; Q = STOP \<Longrightarrow> P \<noteq> STOP \<longrightarrow> Q = STOP\<close>
    by (simp add: STOP_iff_T T_Seq set_eq_iff)
      (metis T_nonTickFree_imp_decomp append_is_Nil_conv is_processT1_TR)
next
  show \<open>\<T> P \<subseteq> insert [] {[\<checkmark>(r)] |r. True} \<and> (P \<noteq> STOP \<longrightarrow> Q = STOP) \<Longrightarrow> P \<^bold>; Q = STOP\<close>
    by (simp add: STOP_iff_T T_Seq subset_iff, safe, simp_all)
      (((use D_T in fastforce)+)[3],
        metis D_T event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) front_tickFree_single is_processT9_tick list.sel(1) not_Cons_self)
qed

lemma STOP_Seq [simp] : \<open>STOP \<^bold>; P = STOP\<close> by (simp add: Seq_is_STOP_iff T_STOP)


lemma Hiding_STOP [simp] : \<open>STOP \ A = STOP\<close>
  by (auto simp add: STOP_iff_T T_Hiding F_STOP D_STOP T_STOP strict_mono_def) blast


lemma STOP_Sync_STOP [simp] : \<open>STOP \<lbrakk>S\<rbrakk> STOP = STOP\<close>
  by (simp add: STOP_iff_T T_Sync T_STOP D_STOP)


lemma Renaming_is_STOP_iff : \<open>Renaming P f g = STOP \<longleftrightarrow> P = STOP\<close>
proof (rule iffI)
  show \<open>P = STOP \<Longrightarrow> Renaming P f g = STOP\<close>
    by (simp add: STOP_iff_T T_Renaming subset_iff)
      (metis D_STOP STOP_iff_T empty_iff)
next
  assume \<open>Renaming P f g = STOP\<close>
  hence \<open>P \<noteq> \<bottom>\<close> by force
  with \<open>Renaming P f g = STOP\<close> show \<open>P = STOP\<close>
    by (simp add: BOT_iff_Nil_D STOP_iff_T T_Renaming set_eq_iff) blast
qed

lemma Renaming_STOP [simp] : \<open>Renaming STOP f g = STOP\<close>
  by (simp add: Renaming_is_STOP_iff)


lemma GlobalNdet_is_STOP_iff : \<open>(\<sqinter>a\<in>A. P a) = STOP \<longleftrightarrow> (\<forall>a\<in>A. P a = STOP)\<close>
  by (simp add: STOP_iff_T T_GlobalNdet) (use Nil_elem_T in blast)

lemma GlobalNdet_empty [simp] : \<open>(\<sqinter>a\<in>{}. P a) = STOP\<close>
  by (simp add: GlobalNdet_is_STOP_iff)

lemma GlobalNdet_id [simp] : \<open>(\<sqinter>a\<in>A. P) = (if A = {} then STOP else P)\<close>
  by simp 

lemma \<open>(\<sqinter>a\<in>A. STOP) = STOP\<close> by simp



subsubsection \<open>More powerful Laws\<close>

lemma Inter_STOP [simp] : \<open>P ||| STOP = P \<^bold>; STOP\<close>
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> (P ||| STOP) \<Longrightarrow> t \<in> \<D> (P \<^bold>; STOP)\<close> for t
    by (simp add: D_Sync D_Seq D_STOP T_STOP)
      (metis emptyRightProperty is_processT7 self_append_conv)
next
  show \<open>t \<in> \<D> (P \<^bold>; STOP) \<Longrightarrow> t \<in> \<D> (P ||| STOP)\<close> for t
    apply (simp add: D_Sync D_Seq D_STOP T_STOP)
    apply (frule D_imp_front_tickFree)
    apply (rule exI[of _ \<open>if tF t then t else butlast t\<close>],
        rule exI[of _ \<open>if tF t then t else butlast t\<close>])
    apply (simp split: if_split_asm)
    by (metis butlast_snoc disjoint_iff emptyLeftSelf front_tickFree_iff_tickFree_butlast
        front_tickFree_single is_processT9 nonTickFree_n_frontTickFree setinterleaving_sym tickFree_def)
next
  fix t X assume \<open>(t, X) \<in> \<F> (P ||| STOP)\<close> \<open>t \<notin> \<D> (P ||| STOP)\<close>
  then obtain t_P X_P X_Q where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>t setinterleaves ((t_P, []), range tick)\<close>
    \<open>X = (X_P \<union> X_Q) \<inter> range tick \<union> X_P \<inter> X_Q\<close>
    by (simp add: F_Sync D_Sync F_STOP) blast
  from \<open>t setinterleaves ((t_P, []), range tick)\<close> EmptyLeftSync
  have \<open>tF t \<and> t = t_P\<close> by (metis inf_commute setinterleaving_sym tickFree_def)
  show \<open>(t, X) \<in> \<F> (P \<^bold>; STOP)\<close>
  proof (cases \<open>\<exists>r. t_P @ [\<checkmark>(r)] \<in> \<T> P\<close>)
    show \<open>\<exists>r. t_P @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>; STOP)\<close>
      using \<open>tF t \<and> t = t_P\<close> by (simp add: F_Seq F_STOP)
  next
    assume \<open>\<nexists>r. t_P @ [\<checkmark>(r)] \<in> \<T> P\<close>
    with \<open>(t_P, X_P) \<in> \<F> P\<close> have \<open>(t_P, X_P \<union> range tick) \<in> \<F> P\<close>
      by (metis is_processT5_S7' rangeE)
    moreover from \<open>X = (X_P \<union> X_Q) \<inter> range tick \<union> X_P \<inter> X_Q\<close>
    have \<open>X \<union> range tick \<subseteq> X_P \<union> range tick\<close> by auto
    ultimately have \<open>(t_P, X \<union> range tick) \<in> \<F> P\<close> by (fact is_processT4)
    with \<open>tF t \<and> t = t_P\<close> show \<open>(t, X) \<in> \<F> (P \<^bold>; STOP)\<close> by (auto simp add: F_Seq)
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> (P \<^bold>; STOP)\<close> \<open>t \<notin> \<D> (P \<^bold>; STOP)\<close>
  then consider \<open>(t, X \<union> range tick) \<in> \<F> P\<close> \<open>tF t\<close> | r where \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close>
    by (simp add: Seq_projs F_STOP) blast
  thus \<open>(t, X) \<in> \<F> (P ||| STOP)\<close>
  proof cases
    assume \<open>(t, X \<union> range tick) \<in> \<F> P\<close> and \<open>tF t\<close>
    from \<open>tF t\<close> have \<open>t setinterleaves ((t, []), range tick)\<close>
      by (metis disjoint_iff emptyLeftSelf setinterleaving_sym tickFree_def)
    with \<open>(t, X \<union> range tick) \<in> \<F> P\<close> show \<open>(t, X) \<in> \<F> (P ||| STOP)\<close>
      apply (simp add: F_Sync F_STOP)
      by (metis Int_Un_eq(1) Un_Int_eq(3) is_processT4 sup_ge1)
  next
    fix r assume \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close>
    hence * : \<open>(t, X - {\<checkmark>(r)}) \<in> \<F> P\<close> and \<open>tF t\<close>
      by (auto simp add: T_F_spec is_processT6 intro: append_T_imp_tickFree)
    from \<open>tF t\<close> have \<open>t setinterleaves ((t, []), range tick)\<close>
      by (metis disjoint_iff emptyLeftSelf setinterleaving_sym tickFree_def)
    hence \<open>(t, (X - {\<checkmark>(r)} \<union> UNIV) \<inter> range tick \<union> (X - {\<checkmark>(r)}) \<inter> UNIV) \<in> \<F> (P ||| STOP)\<close>
      by (simp add: F_Sync F_STOP) (use "*" in blast)
    moreover have \<open>X \<subseteq> (X - {\<checkmark>(r)} \<union> UNIV) \<inter> range tick \<union> (X - {\<checkmark>(r)}) \<inter> UNIV\<close> by auto
    ultimately show \<open>(t, X) \<in> \<F> (P ||| STOP)\<close> by (fact is_processT4)
  qed
qed

corollary STOP_Inter [simp] : \<open>STOP ||| P = P \<^bold>; STOP\<close>
  by (metis Inter_STOP Sync_commute)


lemma Par_STOP [simp] : \<open>P || STOP = (if P = \<bottom> then \<bottom> else STOP)\<close>
proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<Longrightarrow> P || STOP = \<bottom>\<close> by simp
next
  assume \<open>P \<noteq> \<bottom>\<close>
  from \<open>P \<noteq> \<bottom>\<close> show \<open>P || STOP = STOP\<close>
    by (simp add: STOP_iff_T T_Sync STOP_projs set_eq_iff BOT_iff_Nil_D)
      (metis EmptyLeftSync si_empty1 inf_top.right_neutral insertI1
        is_processT1_TR set_empty2 setinterleaving_sym)
qed

lemma STOP_Par [simp] : \<open>STOP || P = (if P = \<bottom> then \<bottom> else STOP)\<close>
  by (metis Par_STOP Sync_commute)




subsection \<open>The Laws of \<^const>\<open>SKIP\<close>\<close>

subsubsection \<open>The definition of SKIPS\<close>

definition SKIPS :: \<open>'r set \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>SKIPS R \<equiv> \<sqinter>r \<in> R. SKIP r\<close>

lemma SKIPS_empty [simp]         : \<open>SKIPS {} = STOP\<close>
  and SKIPS_singl_is_SKIP [simp] : \<open>SKIPS {r} = SKIP r\<close> by (simp_all add: SKIPS_def)


lemma F_SKIPS :
  \<open>\<F> (SKIPS R) = (  if R = {} then {(s, X). s = []}
                  else {([], X) |X. \<exists>r \<in> R. tick r \<notin> X} \<union>
                       {(s, X). \<exists>r \<in> R. s = [tick r]})\<close>
  by (auto simp add: SKIPS_def F_GlobalNdet F_SKIP)

lemma D_SKIPS : \<open>\<D> (SKIPS R) = {}\<close>
  by (auto simp add: SKIPS_def D_GlobalNdet D_SKIP)

lemma T_SKIPS : \<open>\<T> (SKIPS R) = insert [] {[tick r]| r. r \<in> R}\<close>
  by (auto simp add: SKIPS_def T_GlobalNdet T_SKIP)

lemmas SKIPS_projs = F_SKIPS D_SKIPS T_SKIPS



subsubsection \<open>Laws\<close>

lemma SKIP_Sliding [simp] : \<open>SKIP r \<rhd> P = P \<sqinter> SKIP r\<close>
  by (auto simp add: Process_eq_spec F_Sliding D_Sliding F_Ndet D_Ndet SKIP_projs)

lemma Sliding_SKIP [simp] : \<open>P \<rhd> SKIP r = P \<box> SKIP r\<close> 
  by (auto simp add: Process_eq_spec F_Sliding D_Sliding F_Det D_Det SKIP_projs)


lemma Mprefix_neq_SKIP [simp] : \<open>\<box> a \<in> A \<rightarrow> P a \<noteq> SKIP r\<close>
  by (auto simp add: Process_eq_spec F_Mprefix F_SKIP)

lemma Mndetprefix_neq_SKIP [simp] : \<open>\<sqinter> a \<in> A \<rightarrow> P a \<noteq> SKIP r\<close>
  by (auto simp add: Process_eq_spec F_Mndetprefix write0_def F_Mprefix F_SKIP)


lemma SKIP_Seq [simp] : \<open>SKIP r \<^bold>; P = P\<close>
  by (simp add: Process_eq_spec Seq_projs SKIP_projs)

lemma Seq_SKIP [simp] : \<open>P \<^bold>; SKIP () = P\<close>
  \<comment>\<open>This is only true when the type \<^typ>\<open>'r\<close> of \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> is set to \<^typ>\<open>unit\<close>
     (morally, we have ``only one \<^const>\<open>tick\<close>'').\<close>
  by (auto simp add: Process_eq_spec Seq_projs SKIP_projs tick_T_F intro: is_processT4 is_processT6_TR_notin is_processT8)
    (metis (full_types) append.right_neutral is_processT5_S7' old.unit.exhaust rangeE,
      metis (full_types) F_T T_imp_front_tickFree nonTickFree_n_frontTickFree old.unit.exhaust)


lemma Hiding_SKIP [simp] : \<open>SKIP r \ A = SKIP r\<close>
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> (SKIP r \ A) \<Longrightarrow> s \<in> \<D> (SKIP r)\<close> for s
    by (auto simp add: D_Hiding D_SKIP T_SKIP)
      (metis (full_types) Hiding_tickFree non_tickFree_tick not_less_eq_eq strict_mono_eq)
next
  show \<open>s \<in> \<D> (SKIP r) \<Longrightarrow> s \<in> \<D> (SKIP r \ A)\<close> for s
    by (simp add: D_Hiding D_SKIP T_SKIP)
next
  show \<open>(s, X) \<in> \<F> (SKIP r \ A) \<Longrightarrow> (s, X) \<in> \<F> (SKIP r)\<close> for s X
    by (auto simp add: F_Hiding SKIP_projs image_iff)
      (metis (mono_tags, lifting) filter.simps(1) non_tickFree_tick,
        (metis less_tail list.sel(3) nil_less strict_mono_Suc_iff)+)
next
  show \<open>(s, X) \<in> \<F> (SKIP r) \<Longrightarrow> (s, X) \<in> \<F> (SKIP r \ A)\<close> for s X
    by (simp add: F_Hiding SKIP_projs)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) filter.simps(1, 2) image_iff)
qed



subsubsection \<open>Synchronization\<close>

lemma SKIP_Sync_SKIP [simp] : \<open>SKIP r \<lbrakk> S \<rbrakk> SKIP s = (if r = s then SKIP r else STOP)\<close>
  for S :: \<open>'a set\<close> and r :: 'r
proof (split if_split, intro conjI impI)
  show \<open>SKIP r \<lbrakk>S\<rbrakk> SKIP s = SKIP r\<close> if \<open>r = s\<close>
  proof (fold \<open>r = s\<close>, subst Process_eq_spec_optimized, safe)
    show \<open>s \<in> \<D> (SKIP r \<lbrakk>S\<rbrakk> SKIP r) \<Longrightarrow> s \<in> \<D> (SKIP r)\<close>
      and \<open>s \<in> \<D> (SKIP r) \<Longrightarrow> s \<in> \<D> (SKIP r \<lbrakk>S\<rbrakk> SKIP r)\<close> for s
      by (simp_all add: D_Sync D_SKIP)
  next
    assume same_div : \<open>\<D> (SKIP r \<lbrakk>S\<rbrakk> SKIP r) = \<D> (SKIP r)\<close>
    fix s X assume \<open>(s, X) \<in> \<F> (SKIP r \<lbrakk>S\<rbrakk> SKIP r)\<close>
    then consider \<open>s \<in> \<D> (SKIP r \<lbrakk>S\<rbrakk> SKIP r)\<close>
      | s_P s_Q X_P X_Q where
        \<open>(s_P, X_P) \<in> \<F> (SKIP r)\<close> \<open>(s_Q, X_Q) \<in> \<F> (SKIP r)\<close>
        \<open>s setinterleaves ((s_P, s_Q), range tick \<union> ev ` S)\<close>
        \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
      by (simp add: F_Sync D_Sync) blast
    thus \<open>(s, X) \<in> \<F> (SKIP r)\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> (SKIP r \<lbrakk>S\<rbrakk> SKIP r) \<Longrightarrow> (s, X) \<in> \<F> (SKIP r)\<close> by blast
    next
      fix s_P s_Q X_P X_Q
      assume * : \<open>(s_P, X_P) \<in> \<F> (SKIP r)\<close> \<open>(s_Q, X_Q) \<in> \<F> (SKIP r)\<close>
        \<open>s setinterleaves ((s_P, s_Q), range tick \<union> ev ` S)\<close>
        \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
      from "*"(1, 2, 3) consider \<open>s = []\<close> \<open>s_P = []\<close> \<open>s_Q = []\<close>
        | \<open>s = [tick r]\<close> \<open>s_P = [tick r]\<close> \<open>s_Q = [tick r]\<close>
        by (cases s_P; cases s_Q; simp add: image_iff F_SKIP split: if_split_asm)
      thus \<open>(s, X) \<in> \<F> (SKIP r)\<close>
      proof cases
        assume \<open>s = []\<close> and \<open>s_P = []\<close> and \<open>s_Q = []\<close>
        from \<open>s_P = []\<close> "*"(1) have \<open>tick r \<notin> X_P\<close> by (simp add: F_SKIP)
        moreover from \<open>s_Q = []\<close> "*"(2) have \<open>tick r \<notin> X_Q\<close> by (simp add: F_SKIP)
        ultimately have \<open>tick r \<notin> X\<close> by (simp add: "*"(4))
        with \<open>s = []\<close> show \<open>(s, X) \<in> \<F> (SKIP r)\<close> by (simp add: F_SKIP)
      next
        show \<open>s = [tick r] \<Longrightarrow> (s, X) \<in> \<F> (SKIP r)\<close> by (simp add: F_SKIP)
      qed
    qed
  next
    fix s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and X assume \<open>(s, X) \<in> \<F> (SKIP r)\<close>
    then consider \<open>s = []\<close> \<open>tick r \<notin> X\<close> | \<open>s = [tick r]\<close> by (simp add: F_SKIP) blast
    thus \<open>(s, X) \<in> \<F> (SKIP r \<lbrakk>S\<rbrakk> SKIP r)\<close>
    proof cases
      assume \<open>s = []\<close> and \<open>tick r \<notin> X\<close>
      have \<open>([], X) \<in> \<F> (SKIP r)\<close> by (simp add: F_SKIP \<open>tick r \<notin> X\<close>)
      moreover have \<open>[] setinterleaves (([], []), range tick \<union> ev ` S)\<close> by simp
      moreover have \<open>X = (X \<union> X) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> X\<close> by simp
      ultimately show \<open>(s, X) \<in> \<F> (SKIP r \<lbrakk>S\<rbrakk> SKIP r)\<close>
        unfolding F_Sync using \<open>s = []\<close> by blast
    next
      assume \<open>s = [tick r]\<close>
      have \<open>([tick r], X) \<in> \<F> (SKIP r)\<close> by (simp add: F_SKIP)
      moreover have \<open>[tick r] setinterleaves (([tick r], [tick r]), range tick \<union> ev ` S)\<close> by simp
      moreover have \<open>X = (X \<union> X) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> X\<close> by simp
      ultimately show \<open>(s, X) \<in> \<F> (SKIP r \<lbrakk>S\<rbrakk> SKIP r)\<close>
        unfolding F_Sync using \<open>s = [tick r]\<close> by blast
    qed
  qed
next
  show \<open>r \<noteq> s \<Longrightarrow> SKIP r \<lbrakk>S\<rbrakk> SKIP s = STOP\<close>
    by (force simp add: STOP_iff_T T_Sync T_SKIP D_SKIP)
qed


lemma SKIP_Sync_STOP [simp] : \<open>SKIP r \<lbrakk>S\<rbrakk> STOP   = STOP\<close>
  and STOP_Sync_SKIP [simp] : \<open>STOP   \<lbrakk>S\<rbrakk> SKIP r = STOP\<close>
  by (force simp add: STOP_iff_T T_Sync T_SKIP D_SKIP T_STOP D_STOP)+

lemma Mprefix_Sync_SKIP : \<open>(\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> SKIP res = \<box>a \<in> (A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> SKIP res)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then obtain a t u r v
    where * : \<open>a \<in> A\<close> \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>s = r @ v\<close>
      \<open>r setinterleaves ((ev a # t, u), range tick \<union> ev ` S)\<close>
      \<open>t \<in> \<D> (P a)\<close> \<open>u = [] \<or> u = [tick res]\<close>
    by (simp add: D_Sync D_SKIP T_SKIP D_Mprefix image_iff) blast
  from "*"(5, 7) obtain r'
    where ** : \<open>a \<notin> S\<close> \<open>r = ev a # r'\<close> \<open>r' setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
    by (elim disjE; simp add: image_iff split: if_split_asm, blast)
  show \<open>s \<in> \<D> ?rhs\<close>
    by (simp add: D_Mprefix "*"(1, 4) "**"(1, 2) D_Sync T_SKIP D_SKIP)
      (use "*"(2, 3, 6, 7) "**"(2, 3) tickFree_Cons_iff in blast)
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then obtain s' a t u r v
    where * : \<open>s = ev a # s'\<close> \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>front_tickFree v\<close> \<open>t \<in> \<D> (P a)\<close>
      \<open>tickFree r \<or> v = []\<close> \<open>s' = r @ v\<close> \<open>u = [] \<or> u = [tick res]\<close>
      \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
    by (simp add: D_Mprefix D_Sync T_SKIP D_SKIP image_iff) blast
  from "*"(8, 9) have \<open>(ev a # r) setinterleaves ((ev a # t, u), range tick \<union> ev ` S)\<close>
    by (elim disjE; simp add: "*"(3) image_iff)
  moreover have \<open>ev a # t \<in> \<D> (\<box>a \<in> A \<rightarrow> P a)\<close> by (simp add: D_Mprefix "*"(2, 5))
  ultimately show \<open>s \<in> \<D> ?lhs\<close>
    apply (simp add: D_Sync T_SKIP D_SKIP "*"(1, 7))
    apply (rule exI[of _ \<open>ev a # t\<close>], rule exI[of _ u],
        rule exI[of _ \<open>ev a # r\<close>], simp)
    using "*"(4) "*"(6) "*"(8) by blast
next
  fix s Z
  assume same_div: \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, Z) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | t u X Y where \<open>(t, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close> \<open>(u, Y) \<in> \<F> (SKIP res)\<close>
      \<open>s setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
      \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
    by (simp add: F_Sync D_Sync) blast
  thus \<open>(s, Z) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, Z) \<in> \<F> ?rhs\<close> by blast
  next
    fix t u X Y
    assume assms : \<open>(t, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close> \<open>(u, Y) \<in> \<F> (SKIP res)\<close>
      \<open>s setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
      \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
    from assms(1) have \<open>t = [] \<and> X \<inter> ev ` A = {} \<or>
                        (\<exists>a t'. a \<in> A \<and> t = ev a # t' \<and> (t', X) \<in> \<F> (P a))\<close>
      by (simp add: F_Mprefix image_iff) blast
    thus \<open>(s, Z) \<in> \<F> ?rhs\<close>
    proof (elim disjE exE conjE)
      assume \<open>t = []\<close> and \<open>X \<inter> ev ` A = {}\<close>
      from \<open>t = []\<close> assms(2, 3) emptyLeftProperty have \<open>s = [] \<and> u = []\<close>
        by (cases s; cases u; simp add: F_SKIP split: if_split_asm)
      with \<open>X \<inter> ev ` A = {}\<close> show \<open>(s, Z) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Mprefix assms(4))
    next
      fix a t'
      assume \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>(t', X) \<in> \<F> (P a)\<close>
      from assms(2, 3) \<open>t = ev a # t'\<close> obtain s'
        where * : \<open>a \<notin> S\<close> \<open>s = ev a # s'\<close> \<open>s' setinterleaves ((t', u), range tick \<union> ev ` S)\<close>
        by (simp add: F_SKIP, elim disjE; simp split: if_split_asm, blast)
      show \<open>(s, Z) \<in> \<F> ?rhs\<close>
        by (simp add: F_Mprefix \<open>s = ev a # s'\<close> \<open>a \<in> A\<close> \<open>a \<notin> S\<close> F_Sync)
          (use "*"(3) \<open>(t', X) \<in> \<F> (P a)\<close> assms(2, 4) in blast)
    qed
  qed
next
  fix s Z
  assume same_div: \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, Z) \<in> \<F> ?rhs\<close>
  hence \<open>s = [] \<and> Z \<inter> ev ` (A - S) = {} \<or> (\<exists>a s'. a \<in> A \<and> a \<notin> S \<and> s = ev a # s' \<and> (s', Z) \<in> \<F> (P a \<lbrakk>S\<rbrakk> SKIP res))\<close>
    by (simp add: F_Mprefix image_iff) blast
  thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
  proof (elim disjE exE conjE)
    assume \<open>s = []\<close> and \<open>Z \<inter> ev ` (A - S) = {}\<close>
    hence * : \<open>([], Z - ev ` S) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a) \<and> ([], Z - {tick res}) \<in> \<F> (SKIP res) \<and>
               s setinterleaves (([], []), range tick \<union> ev ` S) \<and>
               Z = (Z - ev ` S \<union> (Z - {tick res})) \<inter> (range tick \<union> ev ` S) \<union> (Z - ev ` S) \<inter> (Z - {tick res})\<close>
      by (auto simp add: F_Mprefix F_SKIP)
    show \<open>(s, Z) \<in> \<F> ?lhs\<close> by (simp add: F_Sync) (metis "*")
  next  
    fix a s'
    assume \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>s = ev a # s'\<close> \<open>(s', Z) \<in> \<F> (P a \<lbrakk>S\<rbrakk> SKIP res)\<close>
    from \<open>(s', Z) \<in> \<F> (P a \<lbrakk>S\<rbrakk> SKIP res)\<close> consider \<open>s' \<in> \<D> (P a \<lbrakk>S\<rbrakk> SKIP res)\<close>
      | t u X Y where \<open>(t, X) \<in> \<F> (P a)\<close> \<open>(u, Y) \<in> \<F> (SKIP res)\<close>
        \<open>s' setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
        \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
      by (simp add: F_Sync D_Sync) blast
    thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>s' \<in> \<D> (P a \<lbrakk>S\<rbrakk> SKIP res)\<close>
      with \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>s = ev a # s'\<close> have \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Mprefix)
      with same_div D_F show \<open>(s, Z) \<in> \<F> ?lhs\<close> by blast
    next
      fix t u X Y
      assume assms: \<open>(t, X) \<in> \<F> (P a)\<close> \<open>(u, Y) \<in> \<F> (SKIP res)\<close>
        \<open>s' setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
        \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
      hence \<open>(ev a # t, X) \<in> \<F> (\<box>a\<in> A \<rightarrow> P a) \<and> s setinterleaves ((ev a # t, u), range tick \<union> ev ` S)\<close>
        by (simp add: F_SKIP F_Mprefix \<open>s = ev a # s'\<close>, elim disjE)
          (simp_all add: \<open>a \<in> A\<close> \<open>a \<notin> S\<close> image_iff)
      with assms(2, 4) show \<open>(s, Z) \<in> \<F> ?lhs\<close> by (simp add: F_Sync) blast
    qed
  qed
qed

lemma SKIP_Sync_Mprefix : \<open>SKIP res \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> P b) = \<box>b \<in> (B - S) \<rightarrow> (SKIP res \<lbrakk>S\<rbrakk> P b)\<close>
  by (metis (no_types, lifting) Mprefix_Sync_SKIP Sync_commute mono_Mprefix_eq)



(* TODO: probably not true, see if we put SKIPS definition in Assertions again  *)
(* lemma Renaming_is_SKIP_iff : \<open>Renaming P f g = SKIP s \<longleftrightarrow> (\<exists>R. P = SKIPS R \<and> g ` R = {s})\<close>
proof (intro iffI exI conjI)
  show \<open>\<exists>R. P = SKIPS R \<and> g ` R = {s} \<Longrightarrow> Renaming P f g = SKIP s\<close>
    apply (elim exE conjE, clarify)
    apply (simp add: Process_eq_spec F_Renaming D_Renaming F_SKIPS D_SKIPS F_SKIP D_SKIP )
    by (safe, auto) (metis imageE map_renaming_fun_eq_tick_iff singletonI)
next
  assume \<open>Renaming P f g = SKIP s\<close>
  from this[THEN arg_cong[where f = \<D>]] have \<open>\<D> P = {}\<close>
    by (simp add: D_SKIP D_Renaming)
       (metis D_imp_front_tickFree equals0I front_tickFree_Nil front_tickFree_append_iff
              is_processT9 list.distinct(1) nonTickFree_n_frontTickFree)
  define R where \<open>R \<equiv> {r. [\<checkmark>(r)] \<in> \<T> P \<and> g r = s}\<close>
  from \<open>Renaming P f g = SKIP s\<close>[THEN arg_cong[where f = \<T>]] have \<open>R \<noteq> {}\<close>
    by (simp add: T_Renaming \<open>\<D> P = {}\<close> T_SKIP R_def set_eq_iff)
       (metis (no_types, opaque_lifting) map_renaming_fun_eq_tick_iff)

  thus \<open>g ` R = {s}\<close> by (auto simp add: R_def)

  show \<open>P = SKIPS R\<close>
  proof (subst Process_eq_spec, safe)
    show \<open>u \<in> \<D> P \<Longrightarrow> u \<in> \<D> (SKIPS R)\<close>
     and \<open>u \<in> \<D> (SKIPS R) \<Longrightarrow> u \<in> \<D> P\<close> for u by (simp_all add: \<open>\<D> P = {}\<close> D_SKIPS)
  next
    show \<open>(u, X) \<in> \<F> (SKIPS R) \<Longrightarrow> (u, X) \<in> \<F> P\<close> for u X
      by (simp add: F_SKIPS \<open>R \<noteq> {}\<close>, simp add: R_def)
         (metis append_Nil is_processT6_TR_notin tick_T_F)
  next
    fix u X assume \<open>(u, X) \<in> \<F> P\<close>
    from this[THEN F_T] \<open>Renaming P f g = SKIP s\<close>[THEN arg_cong[where f = \<T>]]
    consider \<open>u = []\<close> | r where \<open>u = [\<checkmark>(r)]\<close>
      by (simp add: Process_eq_spec T_Renaming \<open>\<D> P = {}\<close> T_SKIP set_eq_iff)
         (metis Nil_is_map_conv map_renaming_fun_eq_tick_iff)
    thus \<open>(u, X) \<in> \<F> (SKIPS R)\<close>
    proof cases
      assume \<open>u = []\<close>
      find_theorems \<open>?S = ?t \<Longrightarrow> ?S \<subseteq> ?t\<close>
      from \<open>Renaming P f g = SKIP s\<close>
           [THEN arg_cong[where f = \<F>], THEN equalityD1, THEN set_mp, of \<open>([], renaming_fun f g ` X)\<close>]
      have \<open>\<exists>r\<in>R. \<checkmark>(r) \<notin> X\<close>
        apply (auto simp add: F_Renaming \<open>\<D> P = {}\<close> F_SKIP subset_iff vimage_image_eq)
        apply (auto simp add: renaming_fun_def event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.case_eq_if image_iff split: if_splits)
        find_theorems image vimage
        sledgehammer
        apply (simp add: F_Renaming \<open>\<D> P = {}\<close> F_SKIP)
      have \<open>(u, X) \<in> \<F> (SKIPS R)\<close>
        apply (simp add: F_SKIPS \<open>R \<noteq> {}\<close>)


      oops
      show \<open>u = [] \<Longrightarrow> (u, X) \<in> \<F> (SKIPS R)\<close>
        sledgehammer
  
      oops
    consider \<open>u = []\<close> \<open>(tick ` R) \<inter> X = {}\<close> | r where \<open>g r = s\<close> \<open>u = [\<checkmark>(r)]\<close>
      apply (cases u; auto simp add: Process_eq_spec F_Renaming \<open>\<D> P = {}\<close> F_SKIP disjoint_iff set_eq_iff image_iff R_def vimage_def)
      sledgehammer
    from \<open>Renaming P f g = SKIP s\<close>[THEN arg_cong[where f = \<F>]] show \<open>\<F> P = \<F> (SKIPS R)\<close>
      apply (simp add: F_Renaming \<open>\<D> P = {}\<close> F_SKIPS \<open>R \<noteq> {}\<close> F_SKIP)
      apply (simp add: R_def set_eq_iff, safe)
         apply simp_all
      sledgehammer defer sledgehammer defer sledgehammer defer sledgehammer
    
  proof (rule conjI)
    from \<open>Renaming P f g = SKIP s\<close>[THEN arg_cong[where f = \<T>]]
    show \<open>g ` R = {s}\<close>
      apply (simp add: T_Renaming \<open>\<D> P = {}\<close> T_SKIP set_eq_iff image_iff)
      sledgehammer
  
      sledgehammer
  
  from \<open>Renaming P f g = SKIP s\<close>[THEN arg_cong[where f = \<F>]]
  have \<open>(u, X) \<in> \<F> (Renaming P f g) \<longleftrightarrow> u = [\<checkmark>(s)] \<or> u = [] \<and> \<checkmark>(s) \<notin> X\<close> for u X
    by (auto simp add: F_SKIP)
  hence \<open>(\<exists>v. u = map (renaming_fun f g) v \<and> (v, renaming_fun f g -` X) \<in> \<F> P) \<longleftrightarrow>
         u = [\<checkmark>(s)] \<or> u = [] \<and> \<checkmark>(s) \<notin> X\<close> for u X
    by (simp add: F_Renaming \<open>\<D> P = {}\<close>)
  thm this[simplified F_Renaming \<open>\<D> P = {}\<close>, simplified]
    thm F_SKIP
  have \<open>\<forall>a b. (\<exists>s1. a = map (renaming_fun f g) s1 \<and>
                (\<exists>X. (\<forall>x. (x \<in> b) = (x \<in> X)) \<and> (s1, renaming_fun f g -` X) \<in> \<F> P)) =
          (a = [] \<and> (\<exists>X. (\<forall>x. (x \<in> b) = (x \<in> X)) \<and> \<checkmark>(s) \<notin> X) \<or> a = [\<checkmark>(s)])\<close>
    by (simp add: F_Renaming F_SKIP \<open>\<D> P = {}\<close> set_eq_iff)

  oops
  have \<open>\<exists>r. P = SKIP r \<and> g r = s\<close>
    apply (simp add: F_Renaming F_SKIP \<open>\<D> P = {}\<close> set_eq_iff)
    apply (subst Process_eq_spec, simp add: Process_eq_spec F_SKIP D_SKIP)
    sledgehammer
  show \<open>\<exists>r. P = SKIP r \<and> g r = s\<close> if \<open>Renaming P f g = SKIP s\<close>
    apply (simp add: Process_eq_spec F_Renaming D_Renaming F_SKIP D_SKIP)
    apply safe
    apply (meson front_tickFree_Nil)
     defer sledgehammer


    oops
    apply (simp add: set_eq_iff)

    oops
  apply (simp add: Process_eq_spec F_Renaming F_SKIP D_Renaming D_SKIP)
  sledgehammer *)


lemma Renaming_SKIP [simp] : \<open>Renaming (SKIP r) f g = SKIP (g r)\<close>
  by (force simp add: Process_eq_spec F_Renaming F_SKIP D_Renaming D_SKIP)



subsubsection \<open>Associative Operators\<close>

lemma Det_assoc: \<open>P \<box> (Q \<box> R) = P \<box> Q \<box> R\<close>
  by (auto simp add: Process_eq_spec D_Det F_Det T_Det)


lemma Ndet_assoc: \<open>P \<sqinter> (Q \<sqinter> R) = P \<sqinter> Q \<sqinter> R\<close>
  by (auto simp add: Process_eq_spec D_Ndet F_Ndet)


lemma Sliding_assoc: \<open>P \<rhd> (Q \<rhd> R) = P \<rhd> Q \<rhd> R\<close>
  by (auto simp add: Process_eq_spec F_Sliding D_Sliding T_Sliding)


lemma Seq_assoc : \<open>P \<^bold>; (Q \<^bold>; R) = P \<^bold>; Q \<^bold>; R\<close>
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> (P \<^bold>; (Q \<^bold>; R)) \<Longrightarrow> t \<in> \<D> (P \<^bold>; Q \<^bold>; R)\<close> for t
    by (simp add: D_Seq T_Seq_bis) (metis append.assoc)
next
  fix t assume \<open>t \<in> \<D> (P \<^bold>; Q \<^bold>; R)\<close>
  then consider \<open>t \<in> \<D> (P \<^bold>; Q)\<close> 
    | u v r where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>; Q)\<close> \<open>v \<in> \<D> R\<close>
    by (simp add: D_Seq) blast
  thus \<open>t \<in> \<D> (P \<^bold>; (Q \<^bold>; R))\<close>
  proof cases
    show \<open>t \<in> \<D> (P \<^bold>; Q) \<Longrightarrow> t \<in> \<D> (P \<^bold>; (Q \<^bold>; R))\<close> by (auto simp add: D_Seq)
  next
    fix u v r assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>; Q)\<close> \<open>v \<in> \<D> R\<close>
    from \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>; Q)\<close> consider \<open>u @ [\<checkmark>(r)] \<in> \<D> P\<close>
      | w x s where \<open>u @ [\<checkmark>(r)] = w @ x\<close> \<open>w @ [\<checkmark>(s)] \<in> \<T> P\<close> \<open>x \<in> \<T> Q\<close>
      by (simp add: T_Seq_bis) blast
    thus \<open>t \<in> \<D> (P \<^bold>; (Q \<^bold>; R))\<close>
    proof cases
      from \<open>v \<in> \<D> R\<close> show \<open>u @ [\<checkmark>(r)] \<in> \<D> P \<Longrightarrow> t \<in> \<D> (P \<^bold>; (Q \<^bold>; R))\<close>
        by (simp add: D_Seq \<open>t = u @ v\<close>)
          (metis D_imp_front_tickFree butlast_snoc is_processT7 is_processT9
            front_tickFree_iff_tickFree_butlast)
    next
      from \<open>v \<in> \<D> R\<close> show \<open>\<lbrakk>u @ [\<checkmark>(r)] = w @ x; w @ [\<checkmark>(s)] \<in> \<T> P; x \<in> \<T> Q\<rbrakk> \<Longrightarrow> t \<in> \<D> (P \<^bold>; (Q \<^bold>; R))\<close> for w x s
        by (cases x rule: rev_cases, simp_all add: D_Seq \<open>t = u @ v\<close>)
          (meson append_T_imp_tickFree non_tickFree_tick not_Cons_self2 tickFree_append_iff, blast)
    qed
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> (P \<^bold>; (Q \<^bold>; R))\<close> \<open>t \<notin> \<D> (P \<^bold>; Q \<^bold>; R)\<close> \<open>t \<notin> \<D> (P \<^bold>; Q \<^bold>; R)\<close>
  then consider \<open>(t, X \<union> range tick) \<in> \<F> P\<close> \<open>tF t\<close>
    | u v r where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(v, X) \<in> \<F> (Q \<^bold>; R)\<close>
    unfolding Seq_projs by simp metis
  thus \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<^bold>; R)\<close>
  proof cases
    show \<open>(t, X \<union> range tick) \<in> \<F> P \<Longrightarrow> tF t \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>; Q \<^bold>; R)\<close>
      by (simp add: F_Seq)
  next
    fix u v r assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(v, X) \<in> \<F> (Q \<^bold>; R)\<close>
    with \<open>t \<notin> \<D> (P \<^bold>; Q \<^bold>; R)\<close> consider \<open>(v, X \<union> range tick) \<in> \<F> Q\<close> \<open>tF v\<close>
      | w x s where \<open>v = w @ x\<close> \<open>w @ [\<checkmark>(s)] \<in> \<T> Q\<close> \<open>(x, X) \<in> \<F> R\<close>
      unfolding Seq_projs by fast
    thus \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<^bold>; R)\<close>
    proof cases
      show \<open>(v, X \<union> range tick) \<in> \<F> Q \<Longrightarrow> tF v \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>; Q \<^bold>; R)\<close>
        by (simp add: \<open>t = u @ v\<close> F_Seq)
          (metis \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> append_T_imp_tickFree list.discI)
    next
      show \<open>v = w @ x \<Longrightarrow> w @ [\<checkmark>(s)] \<in> \<T> Q \<Longrightarrow> (x, X) \<in> \<F> R \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>; Q \<^bold>; R)\<close> for w x s
        by (simp add: \<open>t = u @ v\<close> F_Seq T_Seq_bis) (metis \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> append_assoc)
    qed
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<^bold>; R)\<close> \<open>t \<notin> \<D> (P \<^bold>; Q \<^bold>; R)\<close> \<open>t \<notin> \<D> (P \<^bold>; (Q \<^bold>; R))\<close>
  then consider \<open>(t, X \<union> range tick) \<in> \<F> (P \<^bold>; Q)\<close> \<open>tF t\<close>
    | u v r where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>; Q)\<close> \<open>(v, X) \<in> \<F> R\<close>
    unfolding Seq_projs[of \<open>P \<^bold>; Q\<close>] by blast
  thus \<open>(t, X) \<in> \<F> (P \<^bold>; (Q \<^bold>; R))\<close>
  proof cases
    show \<open>(t, X \<union> range tick) \<in> \<F> (P \<^bold>; Q) \<Longrightarrow> tF t \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>; (Q \<^bold>; R))\<close>
      by (simp add: F_Seq) (metis tickFree_append_iff)
  next
    fix u v r assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>; Q)\<close> \<open>(v, X) \<in> \<F> R\<close>
    with \<open>t \<notin> \<D> (P \<^bold>; (Q \<^bold>; R))\<close> obtain w x s
      where \<open>u @ [\<checkmark>(r)] = w @ x\<close> \<open>w @ [\<checkmark>(s)] \<in> \<T> P\<close> \<open>x \<in> \<T> Q\<close>
      by (simp add: D_Seq T_Seq)
        (meson F_imp_front_tickFree \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>; Q)\<close>
          append_T_imp_tickFree is_processT7 is_processT9 not_Cons_self2)
    with \<open>(v, X) \<in> \<F> R\<close> show \<open>(t, X) \<in> \<F> (P \<^bold>; (Q \<^bold>; R))\<close>
      by (cases x rule: rev_cases, simp_all add: \<open>t = u @ v\<close> F_Seq)
        (metis append_T_imp_tickFree non_tickFree_tick
          not_Cons_self2 tickFree_append_iff, blast)
  qed
qed



subsubsection \<open>Synchronization\<close>


lemma interleave_set: \<open>s setinterleaves ((t, u), C) \<Longrightarrow> set t \<union> set u \<subseteq> set s\<close>
  by (induct \<open>(t, C, u)\<close> arbitrary: t u s rule: setinterleaving.induct)
    (simp split: if_split_asm; meson dual_order.trans list.set_intros set_subset_Cons)+


lemma interleave_order: \<open>s setinterleaves ((t1 @ t2, u), C) \<Longrightarrow> set t2 \<subseteq> set (drop (length t1) s)\<close>
proof (induct \<open>(t1, C, u)\<close> arbitrary: t1 u s rule: setinterleaving.induct)
  case 1
  with emptyRightProperty show ?case by auto
next
  case (2 y u)
  with interleave_set show ?case by simp blast
next
  case (3 x t1)
  thus ?case by (simp split: if_split_asm) (metis drop_Suc_Cons)
next
  case (4 x t1 y u)
  thus ?case
    apply (simp split: if_split_asm)
       apply (metis drop_Suc_Cons)
      apply (metis (mono_tags, opaque_lifting) drop_Suc_Cons dual_order.refl le_SucI set_drop_subset_set_drop subset_trans)
     apply (metis (no_types, opaque_lifting) drop_Suc_Cons dual_order.trans le_SucI order_refl set_drop_subset_set_drop)
    by (metis drop_Suc_Cons)
qed


lemma interleave_append_left : 
  \<open>s setinterleaves ((t1 @ t2, u), C) \<Longrightarrow>
   \<exists>u1 u2 s1 s2. u = u1 @ u2 \<and> s = s1 @ s2 \<and>
                 s1 setinterleaves ((t1, u1), C) \<and> s2 setinterleaves ((t2, u2), C)\<close>
proof (induct \<open>(t1, C, u)\<close> arbitrary: t1 u s rule: setinterleaving.induct)
  case 1
  thus ?case by simp
next
  case (2 y u)
  thus ?case by (metis si_empty1 append_Nil singletonI)
next
  case (3 x t1)
  thus ?case by (simp split: if_split_asm) (metis append_Cons)
next
  case (4 x t1 y u)
  from "4.prems" consider v where \<open>x \<in> C\<close> \<open>y \<in> C\<close> \<open>x = y\<close> \<open>s = y # v\<close> \<open>v setinterleaves ((t1 @ t2, u), C)\<close>
    | v where \<open>x \<in> C\<close> \<open>y \<notin> C\<close> \<open>s = y # v\<close> \<open>v setinterleaves (((x # t1) @ t2, u), C)\<close>
    | v where \<open>x \<notin> C\<close> \<open>y \<notin> C\<close> \<open>s = x # v\<close> \<open>v setinterleaves ((t1 @ t2, y # u), C)\<close>
    | v where \<open>x \<notin> C\<close> \<open>y \<notin> C\<close> \<open>s = y # v\<close> \<open>v setinterleaves (((x # t1) @ t2, u), C)\<close>
    | v where \<open>x \<notin> C\<close> \<open>y \<in> C\<close> \<open>s = x # v\<close> \<open>v setinterleaves ((t1 @ t2, y # u), C)\<close>
    by (auto split: if_split_asm)
  thus ?case
  proof cases
    fix v assume * : \<open>x \<in> C\<close> \<open>y \<in> C\<close> \<open>x = y\<close> \<open>s = y # v\<close> \<open>v setinterleaves ((t1 @ t2, u), C)\<close>
    from "4.hyps"(1)[OF "*"(1, 2, 3, 5)] obtain u1 u2 s1 s2
      where ** : \<open>u = u1 @ u2\<close> \<open>v = s1 @ s2\<close> \<open>s1 setinterleaves ((t1, u1), C)\<close>
        \<open>s2 setinterleaves ((t2, u2), C)\<close> by blast
    show ?case
      apply (rule exI[of _ \<open>y # u1\<close>], rule exI[of _ u2])
      apply (rule exI[of _ \<open>y # s1\<close>], rule exI[of _ s2])
      by (simp add: "*"(2, 3, 4) "**")
  next
    fix v assume * : \<open>x \<in> C\<close> \<open>y \<notin> C\<close> \<open>s = y # v\<close> \<open>v setinterleaves (((x # t1) @ t2, u), C)\<close>
    from "4.hyps"(2)[OF "*"(1, 2, 4)] obtain u1 u2 s1 s2
      where ** : \<open>u = u1 @ u2\<close> \<open>v = s1 @ s2\<close> \<open>s1 setinterleaves ((x # t1, u1), C)\<close>
        \<open>s2 setinterleaves ((t2, u2), C)\<close> by blast
    show ?case
      apply (rule exI[of _ \<open>y # u1\<close>], rule exI[of _ u2])
      apply (rule exI[of _ \<open>y # s1\<close>], rule exI[of _ s2])
      by (simp add: "*"(1, 2, 3) "**")
  next
    fix v assume * : \<open>x \<notin> C\<close> \<open>y \<notin> C\<close> \<open>s = x # v\<close> \<open>v setinterleaves ((t1 @ t2, y # u), C)\<close>
    from "4.hyps"(3)[OF "*"(1, 2, 4)] obtain u1 u2 s1 s2
      where ** : \<open>y # u = u1 @ u2\<close> \<open>v = s1 @ s2\<close> \<open>s1 setinterleaves ((t1, u1), C)\<close>
        \<open>s2 setinterleaves ((t2, u2), C)\<close> by blast
    show ?case
      apply (rule exI[of _ \<open>u1\<close>],     rule exI[of _ u2])
      apply (rule exI[of _ \<open>x # s1\<close>], rule exI[of _ s2])
      by (cases u1) (use "**" in \<open>simp_all add: "*"(1, 2, 3)\<close>)
  next
    fix v assume * : \<open>x \<notin> C\<close> \<open>y \<notin> C\<close> \<open>s = y # v\<close> \<open>v setinterleaves (((x # t1) @ t2, u), C)\<close>
    from "4.hyps"(4)[OF "*"(1, 2, 4)] obtain u1 u2 s1 s2
      where ** : \<open>u = u1 @ u2\<close> \<open>v = s1 @ s2\<close> \<open>s1 setinterleaves ((x # t1, u1), C)\<close>
        \<open>s2 setinterleaves ((t2, u2), C)\<close> by blast
    show ?case
      apply (rule exI[of _ \<open>y # u1\<close>], rule exI[of _ u2])
      apply (rule exI[of _ \<open>y # s1\<close>], rule exI[of _ s2])
      by (simp add: "*"(1, 2, 3) "**")
  next
    fix v assume * : \<open>x \<notin> C\<close> \<open>y \<in> C\<close> \<open>s = x # v\<close> \<open>v setinterleaves ((t1 @ t2, y # u), C)\<close>
    from "4.hyps"(5)[simplified, OF "*"(1, 2, 4)] obtain u1 u2 s1 s2
      where ** : \<open>y # u = u1 @ u2\<close> \<open>v = s1 @ s2\<close> \<open>s1 setinterleaves ((t1, u1), C)\<close>
        \<open>s2 setinterleaves ((t2, u2), C)\<close> by blast
    show ?case
      apply (rule exI[of _ \<open>u1\<close>],     rule exI[of _ u2])
      apply (rule exI[of _ \<open>x # s1\<close>], rule exI[of _ s2])
      by (cases u1) (use "**" in \<open>simp_all add: "*"(1, 2, 3)\<close>)
  qed
qed


lemma interleave_append_right : 
  \<open>s setinterleaves ((t, u1 @ u2), C) \<Longrightarrow>
   \<exists>t1 t2 s1 s2. t = t1 @ t2 \<and> s = s1 @ s2 \<and>
                 s1 setinterleaves ((t1, u1), C) \<and> s2 setinterleaves ((t2, u2), C)\<close>
  by (subst (asm) setinterleaving_sym, drule interleave_append_left)
    (simp add: setinterleaving_sym)

lemma interleave_append_tail_left: 
  \<open>s setinterleaves ((t1, u), C) \<Longrightarrow> set t2 \<inter> C = {} \<Longrightarrow> (s @ t2) setinterleaves ((t1 @ t2, u), C)\<close>
  by (induct \<open>(t1, C, u)\<close> arbitrary: t1 t2 u s rule: setinterleaving.induct,
      auto split: if_split_asm)
    (metis disjoint_iff emptyLeftSelf setinterleaving_sym,
      metis SyncSingleHeadAdd setinterleaving_sym)


lemma interleave_append_tail_right: 
  \<open>s setinterleaves ((t, u1), C) \<Longrightarrow> set u2 \<inter> C = {} \<Longrightarrow> (s @ u2) setinterleaves ((t, u1 @ u2), C)\<close>
  by (metis (no_types) setinterleaving_sym interleave_append_tail_left)



lemma interleave_assoc_1: 
  \<open>\<lbrakk>tu setinterleaves ((t, u), A); tuv setinterleaves ((tu, v), A)\<rbrakk> \<Longrightarrow>
   \<exists>uv. uv setinterleaves ((u, v), A) \<and> tuv setinterleaves ((t, uv), A)\<close>
proof (induct \<open>(tu, A, v)\<close> arbitrary: t u tu v tuv rule: setinterleaving.induct)
  case 1
  with emptyLeftProperty empty_setinterleaving show ?case by blast
next
  case (2 z v)
  from "2.prems"(2) emptyLeftProperty have \<open>tuv = z # v\<close> by blast
  with "2.prems" empty_setinterleaving setinterleaving_sym show ?case by blast
next
  case (3 y tu)
  from "3.prems"(2) emptyRightProperty have \<open>tuv = y # tu\<close> by blast
  with "3.prems" show ?case
    by (metis (no_types) EmptyLeftSync Un_iff disjoint_iff
        emptyLeftSelf interleave_set setinterleaving_sym subsetD)
next
  case (4 y tu z v)
  consider \<open>y \<in> A\<close> \<open>z \<in> A\<close> | \<open>y \<in> A\<close> \<open>z \<notin> A\<close> | \<open>y \<notin> A\<close> \<open>z \<in> A\<close> | \<open>y \<notin> A\<close> \<open>z \<notin> A\<close> by blast
  thus ?case
  proof cases
    assume \<open>y \<in> A\<close> and \<open>z \<in> A\<close>
    with "4.prems"(2) obtain tuv'
      where \<open>y = z\<close> \<open>tuv = y # tuv'\<close> \<open>tuv' setinterleaves ((tu, v), A)\<close>
      by (simp split: if_split_asm) blast
    from \<open>tuv = y # tuv'\<close> \<open>y = z\<close> \<open>z \<in> A\<close> "4.prems"(1)
      "4.hyps"(1)[OF \<open>y \<in> A\<close> \<open>z \<in> A\<close> \<open>y = z\<close> _ \<open>tuv' setinterleaves ((tu, v), A)\<close>]
    show ?case by (induct \<open>(t, A, u)\<close> arbitrary: t u tu rule: setinterleaving.induct;
          fastforce split: if_split_asm)
  next
    assume \<open>y \<in> A\<close> and \<open>z \<notin> A\<close>
    with "4.prems"(2) obtain tuv'
      where \<open>tuv = z # tuv'\<close> \<open>tuv' setinterleaves ((y # tu, v), A)\<close>
      by (simp split: if_split_asm) blast
    from \<open>y \<in> A\<close> and \<open>z \<notin> A\<close> \<open>tuv = z # tuv'\<close> "4.prems"(1)
      "4.hyps"(2)[OF _ _ _ \<open>tuv' setinterleaves ((y # tu, v), A)\<close>]
    show ?case
      apply (cases \<open>(t, A, u)\<close> rule: setinterleaving.cases; simp split: if_split_asm)
      by (metis "4.prems"(1) SyncHdAdd list.distinct(1) list.sel(1, 3)) fastforce
  next
    assume \<open>y \<notin> A\<close> and \<open>z \<in> A\<close>
    with "4.prems"(2) obtain tuv'
      where \<open>tuv = y # tuv'\<close> \<open>tuv' setinterleaves ((tu, z # v), A)\<close>
      by (simp split: if_split_asm) blast
    from \<open>y \<notin> A\<close> \<open>z \<in> A\<close> \<open>tuv = y # tuv'\<close> "4.prems"(1)
      "4.hyps"(5)[OF _ _ _ \<open>tuv' setinterleaves ((tu, z # v), A)\<close>]
    show ?case by (cases \<open>(t, A, u)\<close> rule: setinterleaving.cases; fastforce split: if_split_asm)
  next
    assume \<open>y \<notin> A\<close> and \<open>z \<notin> A\<close>
    with "4.prems"(2) obtain tuv'
      where \<open>tuv = y # tuv' \<and> tuv' setinterleaves ((tu, z # v), A) \<or>
             tuv = z # tuv' \<and> tuv' setinterleaves ((y # tu, v), A)\<close> by auto
    thus ?case
    proof (elim disjE conjE)      
      assume \<open>tuv = y # tuv'\<close> \<open>tuv' setinterleaves ((tu, z # v), A)\<close>
      show ?case
      proof (cases \<open>(t, A, u)\<close> rule: setinterleaving.cases)
        from "4.prems"(1) show \<open>(t, A, u) = ([], X, []) \<Longrightarrow> ?case\<close> for X by simp
      next
        show \<open>(t, A, u) = ([], X, y' # u') \<Longrightarrow> ?case\<close> for X y' u'
          by (metis "4.prems"(1) "4.prems"(2) Pair_inject emptyLeftProperty
              emptyLeftSelf empty_iff empty_set ftf_Sync1 ftf_Sync21)
      next
        show \<open>(t, A, u) = (x' # t', X, []) \<Longrightarrow> ?case\<close> for X x' t'
          by (metis (no_types, lifting) "4.prems" Nil_in_shufflesI Pair_inject si_empty1
              emptyLeftNonSync emptyLeftSelf emptyRightProperty ftf_Sync21 shuffles.simps(1))
      next
        fix X x' t' y' u'
        assume \<open>(t, A, u) = (x' # t', X, y' # u')\<close>
        hence \<open>t = x' # t'\<close> \<open>u = y' # u'\<close> \<open>X = A\<close> by simp_all
        consider \<open>x' \<in> A\<close> \<open>y' \<in> A\<close> | \<open>x' \<in> A\<close> \<open>y' \<notin> A\<close>
          | \<open>x' \<notin> A\<close> \<open>y' \<in> A\<close> | \<open>x' \<notin> A\<close> \<open>y' \<notin> A\<close> by blast
        thus ?case
        proof cases
          assume \<open>x' \<in> A\<close> \<open>y' \<in> A\<close>
          with "4.prems"(1) \<open>t = x' # t'\<close> \<open>u = y' # u'\<close> \<open>y \<notin> A\<close> have False
            by (metis SyncSameHdTl list.sel(1))
          thus ?case by simp
        next
          assume \<open>x' \<in> A\<close> \<open>y' \<notin> A\<close>
          with "4.prems"(1) \<open>t = x' # t'\<close> \<open>u = y' # u'\<close>
          have \<open>y' = y\<close> \<open>tu setinterleaves ((x' # t', u'), A)\<close> by simp_all
          from "4.hyps"(3)[OF \<open>y \<notin> A\<close> \<open>z \<notin> A\<close> this(2) \<open>tuv' setinterleaves ((tu, z # v), A)\<close>]
          obtain uv where \<open>uv setinterleaves ((u', z # v), A) \<and>
                           tuv' setinterleaves ((x' # t', uv), A)\<close> ..
          hence \<open>(y # uv) setinterleaves ((u, z # v), A) \<and> tuv setinterleaves ((t, y # uv), A)\<close>
            by (simp add: \<open>u = y' # u'\<close> \<open>z \<notin> A\<close> \<open>y' = y\<close> \<open>y \<notin> A\<close> \<open>t = x' # t'\<close> \<open>tuv = y # tuv'\<close>)
          thus ?case by blast
        next
          assume \<open>x' \<notin> A\<close> \<open>y' \<in> A\<close>
          with "4.prems"(1) \<open>t = x' # t'\<close> \<open>u = y' # u'\<close>
          have \<open>x' = y\<close> \<open>tu setinterleaves ((t', y' # u'), A)\<close> by simp_all
          from "4.hyps"(3)[OF \<open>y \<notin> A\<close> \<open>z \<notin> A\<close> this(2) \<open>tuv' setinterleaves ((tu, z # v), A)\<close>]
          obtain uv where \<open>uv setinterleaves ((y' # u', z # v), A) \<and>
                           tuv' setinterleaves ((t', uv), A)\<close> ..
          hence \<open>uv setinterleaves ((u, z # v), A) \<and> tuv setinterleaves ((t, uv), A)\<close>
            by (simp add: \<open>tuv = y # tuv'\<close> \<open>u = y' # u'\<close> \<open>z \<notin> A\<close>
                \<open>t = x' # t'\<close> \<open>x' = y\<close> \<open>y \<notin> A\<close> SyncSingleHeadAdd)
          thus ?case by blast
        next
          assume \<open>x' \<notin> A\<close> \<open>y' \<notin> A\<close>
          with "4.prems"(1) \<open>t = x' # t'\<close> \<open>u = y' # u'\<close>
          have \<open>x' = y \<and> tu setinterleaves ((t', y' # u'), A) \<or>
                y' = y \<and> tu setinterleaves ((x' # t', u'), A)\<close> by auto
          thus ?case
          proof (elim disjE conjE)
            assume \<open>x' = y\<close> \<open>tu setinterleaves ((t', y' # u'), A)\<close>
            from "4.hyps"(3)[OF \<open>y \<notin> A\<close> \<open>z \<notin> A\<close> this(2) \<open>tuv' setinterleaves ((tu, z # v), A)\<close>]
            obtain uv where \<open>uv setinterleaves ((y' # u', z # v), A) \<and>
                             tuv' setinterleaves ((t', uv), A)\<close> ..
            hence \<open>uv setinterleaves ((u, z # v), A) \<and> tuv setinterleaves ((t, uv), A)\<close>
              by (simp add: \<open>x' = y\<close> \<open>y \<notin> A\<close> \<open>t = x' # t'\<close>
                  \<open>tuv = y # tuv'\<close> \<open>u = y' # u'\<close> SyncSingleHeadAdd)
            thus ?case by blast
          next
            assume \<open>y' = y\<close> \<open>tu setinterleaves ((x' # t', u'), A)\<close>
            from "4.hyps"(3)[OF \<open>y \<notin> A\<close> \<open>z \<notin> A\<close> this(2) \<open>tuv' setinterleaves ((tu, z # v), A)\<close>]
            obtain uv where \<open>uv setinterleaves ((u', z # v), A) \<and>
                             tuv' setinterleaves ((x' # t', uv), A)\<close> ..
            hence \<open>(y # uv) setinterleaves ((u, z # v), A) \<and> tuv setinterleaves ((t, y # uv), A)\<close>
              by (simp add: \<open>u = y' # u'\<close> \<open>y' = y\<close> \<open>y \<notin> A\<close> \<open>z \<notin> A\<close> \<open>t = x' # t'\<close> \<open>tuv = y # tuv'\<close>)
            thus ?case by blast
          qed
        qed
      qed
    next
      assume \<open>tuv = z # tuv'\<close> \<open>tuv' setinterleaves ((y # tu, v), A)\<close>
      from "4.hyps"(4)[OF \<open>y \<notin> A\<close> \<open>z \<notin> A\<close> "4.prems"(1) \<open>tuv' setinterleaves ((y # tu, v), A)\<close>]
      obtain uv where \<open>uv setinterleaves ((u, v), A) \<and> tuv' setinterleaves ((t, uv), A)\<close> ..
      hence \<open>(z # uv) setinterleaves ((u, z # v), A) \<and> tuv setinterleaves ((t, z # uv), A)\<close>
        by (cases u; cases t) (simp_all add: \<open>z \<notin> A\<close> \<open>tuv = z # tuv'\<close>)
      thus ?case by blast
    qed
  qed
qed 


lemma interleave_assoc_2:
  assumes  *:\<open>uv setinterleaves ((u, v), A)\<close> and 
    **:\<open>tuv setinterleaves ((t, uv), A)\<close>
  shows \<open>\<exists>tu. tu setinterleaves ((t, u), A) \<and> tuv setinterleaves ((tu, v), A)\<close>
  using "*" "**" setinterleaving_sym interleave_assoc_1 by blast



theorem Sync_assoc: \<open>P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R) = P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R\<close> for P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule FD_antisym)
  show \<open>P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R) \<sqsubseteq>\<^sub>F\<^sub>D P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R\<close> for P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (rule failure_divergence_refine_optimizedI)
    fix s assume \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R)\<close>
    from this[simplified D_Sync[of \<open>P \<lbrakk>S\<rbrakk> Q\<close>]] obtain t u r v
      where * : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>s = r @ v\<close> 
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
        \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<and> u \<in> \<T> R \<or> t \<in> \<D> R \<and> u \<in> \<T> (P \<lbrakk>S\<rbrakk> Q) - \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by simp (metis D_T setinterleaving_sym)
    from "*"(5) show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close>
    proof (elim disjE conjE)
      assume \<open>t \<in> \<D> R\<close> and \<open>u \<in> \<T> (P \<lbrakk>S\<rbrakk> Q) - \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      from \<open>u \<in> \<T> (P \<lbrakk>S\<rbrakk> Q) - \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> obtain t1 u1
        where ** : \<open>u setinterleaves ((t1, u1), range tick \<union> ev ` S)\<close>
          \<open>t1 \<in> \<T> P\<close> \<open>u1 \<in> \<T> Q\<close> by (simp add: D_Sync T_Sync) blast
      from interleave_assoc_1[OF "**"(1)] obtain uv
        where *** : \<open>uv setinterleaves ((u1, t), range tick \<union> ev ` S)\<close>
          \<open>r setinterleaves ((t1, uv), range tick \<union> ev ` S)\<close>
        using "*"(4) setinterleaving_sym by blast
      from "***"(1) setinterleaving_sym \<open>t \<in> \<D> R\<close> \<open>u1 \<in> \<T> Q\<close> front_tickFree_Nil
      have \<open>uv \<in> \<D> (Q \<lbrakk>S\<rbrakk> R)\<close> unfolding D_Sync by blast
      with "*"(1, 2, 3) "**"(2) "***"(2) setinterleaving_sym
      show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close> by (subst D_Sync) blast
    next
      assume \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> and \<open>u \<in> \<T> R\<close>
      from \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> obtain t1 u1 r1 v1
        where ** : \<open>front_tickFree v1\<close> \<open>tickFree r1 \<or> v1 = []\<close> \<open>t = r1 @ v1\<close>
          \<open>r1 setinterleaves ((t1, u1), range tick \<union> ev ` S)\<close>
          \<open>t1 \<in> \<D> P \<and> u1 \<in> \<T> Q \<or> t1 \<in> \<D> Q \<and> u1 \<in> \<T> P\<close>
        by (simp add: D_Sync) blast
      from interleave_append_left[OF "*"(4)[unfolded "**"(3)]] obtain r' r'' u' u''
        where *** : \<open>r' setinterleaves ((r1, u'), range tick \<union> ev ` S)\<close>
          \<open>r = r' @ r''\<close> \<open>u = u' @ u''\<close> by blast
      have \<open>u' \<in> \<T> R\<close> by (metis "***"(3) prefixI \<open>u \<in> \<T> R\<close> is_processT3_TR)
      have $ : \<open>front_tickFree (r'' @ v)\<close>
        by (metis "*"(3) "***"(2) D_imp_front_tickFree \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R)\<close>
            front_tickFree_append_iff front_tickFree_charn tickFree_append_iff)
      have $$ : \<open>tickFree r' \<or> r'' @ v = []\<close>
        by (metis "*"(3) "***"(2) D_imp_front_tickFree \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R)\<close>
            append.right_neutral front_tickFree_append_iff tickFree_append_iff)
      have $$$ : \<open>s = r' @ r'' @ v\<close> by (simp add: "*"(3) "***"(2))

      from "**"(5) show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close>
      proof (elim disjE conjE)
        assume \<open>t1 \<in> \<D> P\<close> and \<open>u1 \<in> \<T> Q\<close>
        from interleave_assoc_1[OF "**"(4) "***"(1)] obtain uv
          where **** : \<open>uv setinterleaves ((u1, u'), range tick \<union> ev ` S)\<close>
            \<open>r' setinterleaves ((t1, uv), range tick \<union> ev ` S)\<close> by blast
        from \<open>u' \<in> \<T> R\<close> "****"(1) \<open>u1 \<in> \<T> Q\<close> have \<open>uv \<in> \<T> (Q \<lbrakk>S\<rbrakk> R)\<close>
          unfolding T_Sync by blast
        with "$" "$$" "$$$" "****"(2) \<open>t1 \<in> \<D> P\<close>
        show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close> unfolding D_Sync by blast
      next
        assume \<open>t1 \<in> \<D> Q\<close> \<open>u1 \<in> \<T> P\<close>
        from interleave_assoc_2[OF "**"(4)] "***"(1) setinterleaving_sym obtain tu
          where "****" : \<open>tu setinterleaves ((u', t1), range tick \<union> ev ` S)\<close>
            \<open>r' setinterleaves ((tu, u1), range tick \<union> ev ` S)\<close> by blast
        from \<open>u' \<in> \<T> R\<close> "****"(1)[unfolded setinterleaving_sym] front_tickFree_Nil \<open>t1 \<in> \<D> Q\<close>
        have \<open>tu \<in> \<D> (Q \<lbrakk>S\<rbrakk> R)\<close> unfolding D_Sync by blast
        with "$" "$$" "$$$" "****"(2) \<open>u1 \<in> \<T> P\<close>
        show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close> unfolding D_Sync by blast
      qed
    qed
  next
    let ?Sync_set = \<open>\<lambda>X Y. (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
    assume subset_div : \<open>\<D> (P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R) \<subseteq> \<D> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close>
    fix s Z assume \<open>(s, Z) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R)\<close>
    then consider (D) \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R)\<close>
      | (F) t X u Y where \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> \<open>(u, Y) \<in> \<F> R\<close> \<open>Z = ?Sync_set X Y\<close>
        \<open>s setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
      unfolding F_Sync D_Sync by blast
    thus \<open>(s, Z) \<in> \<F> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close>
    proof cases
      from subset_div D_F show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R) \<Longrightarrow> (s, Z) \<in> \<F> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close> by blast
    next
      case F
      from "F"(1) consider (D1) \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        | (F1) t1 X1 u1 Y1 where \<open>(t1, X1) \<in> \<F> P\<close> \<open>(u1, Y1) \<in> \<F> Q\<close> \<open>X = ?Sync_set X1 Y1\<close>
          \<open>t setinterleaves ((t1, u1), range tick \<union> ev ` S)\<close>
        unfolding F_Sync D_Sync by blast
      thus \<open>(s, Z) \<in> \<F> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close>
      proof cases
        assume \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        with F(2) F(4) F_T front_tickFree_Nil
        have \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R)\<close> unfolding D_Sync by blast
        with subset_div D_F show \<open>(s, Z) \<in> \<F> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close> by blast
      next
        case F1
        from interleave_assoc_1[OF F1(4) F(4)] obtain uv
          where * : \<open>uv setinterleaves ((u1, u), range tick \<union> ev ` S)\<close>
            \<open>s setinterleaves ((t1, uv), range tick \<union> ev ` S)\<close> by blast
        from "*"(1) F(2) F1(2) have \<open>(uv, ?Sync_set Y1 Y) \<in> \<F> (Q \<lbrakk>S\<rbrakk> R)\<close>
          unfolding F_Sync by blast
        with "*"(2) F1(1) have \<open>(s, ?Sync_set X1 (?Sync_set Y1 Y)) \<in> \<F> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close>
          by (subst F_Sync) blast
        also from F(3) F1(3) have \<open>?Sync_set X1 (?Sync_set Y1 Y) = Z\<close> by blast
        finally show \<open>(s, Z) \<in> \<F> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R))\<close> .
      qed
    qed
  qed
  thus \<open>P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> R \<sqsubseteq>\<^sub>F\<^sub>D P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> R)\<close> by (metis Sync_commute)
qed


(*<*)
end
  (*>*)
