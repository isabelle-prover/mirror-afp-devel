(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Powerful results on DF and deadlock freeness
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


chapter \<open> Deadlock results \<close>

(*<*)
theory CSPM_Deadlock_Results
  imports CSPM_Laws CSPM_Monotonies
begin
  (*>*)

text \<open>When working with the interleaving \<^term>\<open>P ||| Q\<close>, we intuitively expect it to be
      \<^const>\<open>deadlock_free\<close> when both \<^term>\<open>P\<close> and \<^term>\<open>Q\<close> are.

      This chapter contains several results about deadlock notion, and concludes
      with a proof of the theorem we just mentioned.\<close>



section \<open>Unfolding lemmas for the projections of \<^const>\<open>DF\<close> and \<^const>\<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>\<close>

text \<open>\<^const>\<open>DF\<close> and \<^const>\<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close> naturally appear when we work around \<^const>\<open>deadlock_free\<close>
      and \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close> notions (because

      @{thm deadlock_free_def[of P] deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def[of P]}).

      It is therefore convenient to have the following rules for unfolding the projections.\<close>

lemma F_DF: 
  \<open>\<F> (DF A) =
   (if A = {} then {(s, X). s = []}
    else (\<Union>a\<in>A. {[]} \<times> {X. ev a \<notin> X} \<union> {(ev a # s, X)| s X. (s, X) \<in> \<F> (DF A)}))\<close>
  by (subst DF_unfold) (auto simp add: F_STOP F_Mndetprefix write0_def F_Mprefix)


lemma F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: 
  \<open>\<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) =
   (  if A = {} then {(s, X). s = [] \<or> (\<exists>r\<in>R. s = [\<checkmark>(r)])}
    else (\<Union>a\<in>A. {[]} \<times> {X. ev a \<notin> X} \<union> 
                 {(ev a # s, X)| s X. (s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)}) \<union>
         (  if R = {} then {(s, X). s = []}
          else {([], X) |X. \<exists>r\<in>R. \<checkmark>(r) \<notin> X} \<union> {(s, X). \<exists>r\<in>R. s = [\<checkmark>(r)]}))\<close>
  by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold, simp add: F_Ndet F_STOP F_SKIPS F_Mndetprefix write0_def F_Mprefix, safe, simp_all)


corollary Cons_F_DF:
  \<open>(x # t, X) \<in> \<F> (DF A) \<Longrightarrow> (t, X) \<in> \<F> (DF A)\<close>
  and Cons_F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>x \<notin> tick ` R \<Longrightarrow> (x # t, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) \<Longrightarrow> (t, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)\<close>
  by (subst (asm) F_DF F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S; auto split: if_split_asm)+


lemma D_DF: \<open>\<D> (DF A) = (if A = {} then {} else {ev a # s| a s. a \<in> A \<and> s \<in> \<D> (DF A)})\<close>
  and D_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: \<open>\<D> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = (if A = {} then {} else {ev a # s| a s. a \<in> A \<and> s \<in> \<D> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R)})\<close>
  by (subst DF_unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold; 
      auto simp add: D_Mndetprefix D_Mprefix write0_def D_Ndet D_SKIPS)+

thm T_SKIPS[of R]
lemma T_DF: 
  \<open>\<T> (DF A) = (if A = {} then {[]} else insert [] {ev a # s| a s. a \<in> A \<and> s \<in> \<T> (DF A)})\<close>
  and T_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S: 
  \<open>\<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) = (if A = {} then insert [] {[\<checkmark>(r)] |r. r \<in> R}
    else {s. s = [] \<or> (\<exists>r\<in>R. s = [\<checkmark>(r)]) \<or> 
             s \<noteq> [] \<and> (\<exists>a\<in>A. hd s = ev a \<and> tl s \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R))})\<close>
  by (subst DF_unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold;
      auto simp add: T_STOP T_Mndetprefix write0_def T_Mprefix T_Ndet T_SKIPS)+
    (metis list.collapse)


section \<open>Characterizations for \<^const>\<open>deadlock_free\<close>, \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>\<close>

text \<open>We want more results like @{thm deadlock_free_Ndet_iff[of P Q]},
      and we want to add the reciprocal when possible.\<close>

text \<open>The first thing we notice is that we only have to care about the failures\<close>
lemma \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<equiv> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV \<sqsubseteq>\<^sub>F P\<close>
  by (fact deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def)

lemma deadlock_free_F: \<open>deadlock_free P \<longleftrightarrow> DF UNIV \<sqsubseteq>\<^sub>F P\<close>
  by (auto simp add: deadlock_free_def refine_defs F_subset_imp_T_subset
      non_terminating_refine_DF nonterminating_implies_div_free)



lemma deadlock_free_Mprefix_iff: \<open>deadlock_free (\<box> a \<in> A \<rightarrow> P a) \<longleftrightarrow> 
                                  A \<noteq> {} \<and> (\<forall>a \<in> A. deadlock_free (P a))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mprefix_iff: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Mprefix A P) \<longleftrightarrow> 
                                     A \<noteq> {} \<and> (\<forall>a \<in> A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P a))\<close>
  unfolding deadlock_free_F deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def
   apply (all \<open>subst F_DF F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>,
      auto simp add: div_free_DF F_Mprefix D_Mprefix subset_iff)
  by blast+


lemma deadlock_free_read_iff :
  \<open>deadlock_free (c\<^bold>?a\<in>A \<rightarrow> P a) \<longleftrightarrow> A \<noteq> {} \<and> (\<forall>a\<in>c ` A. deadlock_free ((P \<circ> inv_into A c) a))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_read_iff :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (c\<^bold>?a\<in>A \<rightarrow> P a) \<longleftrightarrow> A \<noteq> {} \<and> (\<forall>a\<in>c ` A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ((P \<circ> inv_into A c) a))\<close>
  by (simp_all add: read_def deadlock_free_Mprefix_iff deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mprefix_iff) 

lemma deadlock_free_read_inj_on_iff :
  \<open>inj_on c A \<Longrightarrow> deadlock_free (c\<^bold>?a\<in>A \<rightarrow> P a) \<longleftrightarrow> A \<noteq> {} \<and> (\<forall>a\<in>A. deadlock_free (P a))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_read_inj_on_iff :
  \<open>inj_on c A \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (c\<^bold>?a\<in>A \<rightarrow> P a) \<longleftrightarrow> A \<noteq> {} \<and> (\<forall>a\<in>A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P a))\<close>
  by (simp_all add: deadlock_free_read_iff deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_read_iff)

lemma deadlock_free_write_iff :
  \<open>deadlock_free (c\<^bold>!a \<rightarrow> P) \<longleftrightarrow> deadlock_free P\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write_iff :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (c\<^bold>!a \<rightarrow> P) \<longleftrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  by (simp_all add: deadlock_free_Mprefix_iff deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mprefix_iff write_def)

lemma deadlock_free_write0_iff :
  \<open>deadlock_free (a \<rightarrow> P) \<longleftrightarrow> deadlock_free P\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write0_iff :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (a \<rightarrow> P) \<longleftrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  by (simp_all add: deadlock_free_Mprefix_iff deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mprefix_iff write0_def)

(* TODO: see what we declare simp *)


lemma deadlock_free_GlobalNdet_iff: \<open>deadlock_free (\<sqinter> a \<in> A. P a) \<longleftrightarrow>
                                     A \<noteq> {} \<and> (\<forall> a \<in> A. deadlock_free (P a))\<close> 
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalNdet_iff: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> a \<in> A. P a) \<longleftrightarrow>
                                        A \<noteq> {} \<and> (\<forall> a \<in> A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P a))\<close>
  by (metis (mono_tags, lifting) GlobalNdet_refine_FD deadlock_free_def trans_FD
      mono_GlobalNdet_FD_const non_deadlock_free_STOP GlobalNdet_empty)
    (metis (mono_tags, lifting) GlobalNdet_refine_FD deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD trans_FD
      mono_GlobalNdet_FD_const non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_STOP GlobalNdet_empty)



lemma deadlock_free_Mndetprefix_iff: \<open>deadlock_free (\<sqinter> a \<in> A \<rightarrow> P a) \<longleftrightarrow>
                                      A \<noteq> {} \<and> (\<forall>a\<in>A. deadlock_free (P a))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mndetprefix_iff: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> a \<in> A \<rightarrow> P a) \<longleftrightarrow> 
                                         A \<noteq> {} \<and> (\<forall>a\<in>A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P a))\<close>
  by (simp_all add: Mndetprefix_GlobalNdet
      deadlock_free_GlobalNdet_iff deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalNdet_iff
      deadlock_free_write0_iff deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_write0_iff)


(* TODO: remove this from here *)
lemma deadlock_free_Ndet_iff: \<open>deadlock_free (P \<sqinter> Q) \<longleftrightarrow> 
                               deadlock_free P \<and> deadlock_free Q\<close> 
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Ndet_iff: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<sqinter> Q) \<longleftrightarrow>
                                  deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<and> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q\<close>
  unfolding deadlock_free_F deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def
  by (simp_all add: F_Ndet)



lemma deadlock_free_is_right: (* see OpSem *)
  \<open>deadlock_free (P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<longleftrightarrow> (\<forall>s \<in> \<T> P. tickFree s \<and> (s,      UNIV) \<notin> \<F> P)\<close>
  \<open>deadlock_free  P                \<longleftrightarrow> (\<forall>s \<in> \<T> P. tickFree s \<and> (s, ev ` UNIV) \<notin> \<F> P)\<close>
  oops


(* TODO: do something here *)

lemma \<open>deadlock_free (P \<box> Q) \<longleftrightarrow> P = STOP \<and> deadlock_free Q \<or> deadlock_free P \<and> Q = STOP\<close>
  (*  apply (simp add: deadlock_free_is_right(2))
  apply (simp add: Det_projs, safe)
                      apply simp_all *)
  oops




lemma deadlock_free_GlobalDet_iff :
  \<open>\<lbrakk>A \<noteq> {}; finite A; \<forall>a\<in>A. deadlock_free (P a)\<rbrakk> \<Longrightarrow> deadlock_free (\<box>a \<in> A. P a)\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_MultiDet:
  \<open>\<lbrakk>A \<noteq> {}; finite A; \<forall>a\<in>A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P a)\<rbrakk> \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<box>a \<in> A. P a)\<close>
  by (metis GlobalNdet_FD_GlobalDet deadlock_free_GlobalNdet_iff deadlock_free_def trans_FD)
    (metis GlobalNdet_FD_GlobalDet deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalNdet_iff trans_FD)



lemma deadlock_free_Det:
  \<open>deadlock_free    P \<Longrightarrow> deadlock_free    Q \<Longrightarrow> deadlock_free    (P \<box> Q)\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Det:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<box> Q)\<close>
  by (metis deadlock_free_Ndet_iff Ndet_FD_Det deadlock_free_def trans_FD)
    (metis deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Ndet_iff Ndet_F_Det deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def trans_F)



text \<open>For \<^term>\<open>P \<box> Q\<close>, we can not expect more:\<close>

lemma
  \<open>\<exists>P Q. deadlock_free    P \<and> \<not> deadlock_free    Q \<and> 
         deadlock_free     (P \<box> Q)\<close>
  \<open>\<exists>P Q. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<and> \<not> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Q \<and> 
         deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P \<box> Q)\<close>
  by (rule_tac x = \<open>DF UNIV\<close> in exI, rule_tac x = STOP in exI, 
      simp add: non_deadlock_free_STOP, simp add: deadlock_free_def)
    (rule_tac x = \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV\<close> in exI, rule_tac x = STOP in exI,
      simp add: non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_STOP, simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD)




lemma FD_Mndetprefix_iff:
  \<open>A \<noteq> {} \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter> a \<in> A \<rightarrow> Q \<longleftrightarrow> (\<forall>a \<in> A. P \<sqsubseteq>\<^sub>F\<^sub>D (a \<rightarrow> Q))\<close>
  by (auto simp: failure_divergence_refine_def failure_refine_def divergence_refine_def
      subset_iff D_Mndetprefix F_Mndetprefix write0_def D_Mprefix F_Mprefix)


lemma Mndetprefix_FD: \<open>(\<exists>a \<in> A. (a \<rightarrow> Q) \<sqsubseteq>\<^sub>F\<^sub>D P) \<Longrightarrow> \<sqinter> a \<in> A \<rightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis FD_Mndetprefix_iff ex_in_conv idem_FD trans_FD)




text \<open>\<^const>\<open>Mprefix\<close>, \<^const>\<open>Sync\<close> and \<^const>\<open>deadlock_free\<close>\<close>

lemma Mprefix_Sync_deadlock_free:
  assumes not_all_empty: \<open>A \<noteq> {} \<or> B \<noteq> {} \<or> A' \<inter> B' \<noteq> {}\<close>
    and \<open>A \<inter> S = {}\<close> and \<open>A' \<subseteq> S\<close> and \<open>B \<inter> S = {}\<close> and \<open>B' \<subseteq> S\<close>
    and \<open>\<forall>x\<in>A. deadlock_free (P x \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q)\<close>
    and \<open>\<forall>y\<in>B. deadlock_free (Mprefix (A \<union> A') P \<lbrakk>S\<rbrakk> Q y)\<close>
    and \<open>\<forall>x\<in>A' \<inter> B'. deadlock_free ((P x \<lbrakk>S\<rbrakk> Q x))\<close> 
  shows \<open>deadlock_free (Mprefix (A \<union> A') P \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q)\<close> 
proof -
  have \<open>A = {} \<and> B \<noteq> {} \<and> A' \<inter> B' \<noteq> {} \<or> A \<noteq> {} \<and> B = {} \<and> A' \<inter> B' = {} \<or>
        A \<noteq> {} \<and> B = {} \<and> A' \<inter> B' \<noteq> {} \<or> A = {} \<and> B \<noteq> {} \<and> A' \<inter> B' = {} \<or> 
        A \<noteq> {} \<and> B \<noteq> {} \<and> A' \<inter> B' = {} \<or> A = {} \<and> B = {} \<and> A' \<inter> B' \<noteq> {} \<or>
        A \<noteq> {} \<and> B \<noteq> {} \<and> A' \<inter> B' \<noteq> {}\<close> by (meson not_all_empty)
  thus ?thesis
    by (elim disjE, all \<open>subst Mprefix_Sync_Mprefix_bis[OF assms(2-5)]\<close>)
      (use assms(6-8) in \<open>auto intro!: deadlock_free_Det deadlock_free_Mprefix_iff[THEN iffD2]\<close>)
qed



lemmas Mprefix_Sync_subset_deadlock_free = Mprefix_Sync_deadlock_free
  [where A  = \<open>{}\<close> and B  = \<open>{}\<close>, simplified]
  and Mprefix_Sync_indep_deadlock_free  = Mprefix_Sync_deadlock_free
  [where A' = \<open>{}\<close> and B' = \<open>{}\<close>, simplified]
  and Mprefix_Sync_right_deadlock_free  = Mprefix_Sync_deadlock_free
  [where A  = \<open>{}\<close> and B' = \<open>{}\<close>, simplified]
  and Mprefix_Sync_left_deadlock_free   = Mprefix_Sync_deadlock_free
  [where A' = \<open>{}\<close> and B  = \<open>{}\<close>, simplified]




section \<open>Results on \<^const>\<open>Renaming\<close>\<close> 

text \<open>The \<^const>\<open>Renaming\<close> operator is new (release of 2023), so here are its properties
      on reference processes from \<^theory>\<open>HOL-CSP.CSP_Assertions\<close>, and deadlock notion.\<close>

subsection \<open>Behaviour with references processes\<close>

text \<open>For \<^const>\<open>DF\<close>\<close>

lemma DF_FD_Renaming_DF: \<open>DF (f ` A) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f g\<close>
proof (subst DF_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f g)\<close> by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f g\<close> by simp
next
  show \<open>(\<Lambda> x. \<sqinter>a \<in> f ` A \<rightarrow>  x)\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f g\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f g\<close> for x
    apply simp
    apply (subst DF_unfold)
    apply (subst Renaming_Mndetprefix)
    by (auto simp add: that intro!: mono_Mndetprefix_FD)
qed

lemma Renaming_DF_FD_DF: \<open>Renaming (DF A) f g \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A)\<close>
  if finitary: \<open>finitary f\<close> \<open>finitary g\<close>
proof (subst DF_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f g \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f g \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A)\<close> by simp
next
  show \<open>Renaming ((\<Lambda> x. \<sqinter>a \<in> A \<rightarrow>  x)\<cdot>x) f g \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A)\<close>
    if \<open>Renaming x f g \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A)\<close> for x
    apply simp
    apply (subst Renaming_Mndetprefix)
    apply (subst DF_unfold)
    by (auto simp add: that intro!: mono_Mndetprefix_FD)
qed


text \<open>For \<^const>\<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>\<close>

(* TODO: move this *)


lemma Renaming_SKIPS [simp] : \<open>Renaming (SKIPS R) f g = SKIPS (g ` R)\<close>
  by (simp add: SKIPS_def Renaming_distrib_GlobalNdet)
    (metis mono_GlobalNdet_eq2)


lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g\<close>
proof (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g)\<close> by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g\<close> by simp
next
  show \<open>(\<Lambda> x. (\<sqinter> a\<in>f ` A \<rightarrow>  x) \<sqinter> SKIPS (g ` R))\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g\<close> for x
    by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: Renaming_Ndet Renaming_Mndetprefix
        intro!: mono_Ndet_FD mono_Mndetprefix_FD that)
qed

lemma Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close>
  if finitary: \<open>finitary f\<close> \<open>finitary g\<close>
proof (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f g \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f g \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close> by simp
next
  show \<open>Renaming ((\<Lambda> x. (\<sqinter>a \<in> A \<rightarrow>  x) \<sqinter> SKIPS R)\<cdot>x) f g \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close>
    if \<open>Renaming x f g \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close> for x
    by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: Renaming_Ndet Renaming_Mndetprefix
        intro!: mono_Ndet_FD mono_Mndetprefix_FD that)
qed



text \<open>For \<^const>\<open>RUN\<close>\<close>

lemma RUN_FD_Renaming_RUN: \<open>RUN (f ` A) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f g\<close>
proof (subst RUN_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f g)\<close> by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f g\<close> by simp
next
  show \<open>(\<Lambda> x. \<box>a \<in> f ` A \<rightarrow>  x)\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f g\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f g\<close> for x
    by (subst RUN_unfold)
      (auto simp add: Renaming_Mprefix intro!: mono_Mprefix_FD that)
qed

lemma Renaming_RUN_FD_RUN: \<open>Renaming (RUN A) f g \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A)\<close>
  if finitary: \<open>finitary f\<close> \<open>finitary g\<close>
proof (subst RUN_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f g \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f g \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A)\<close> by simp
next
  show \<open>Renaming ((\<Lambda> x. \<box>a \<in> A \<rightarrow>  x)\<cdot>x) f g \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A)\<close>
    if \<open>Renaming x f g \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A)\<close> for x
    by (subst RUN_unfold)
      (auto simp add: Renaming_Mprefix intro!: mono_Mprefix_FD that)
qed


text \<open>For \<^const>\<open>CHAOS\<close>\<close>

lemma CHAOS_FD_Renaming_CHAOS:
  \<open>CHAOS (f ` A) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f g\<close>
proof (subst CHAOS_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f g)\<close> by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f g\<close> by simp
next
  show \<open>(\<Lambda> x. STOP \<sqinter> (\<box>a\<in>f ` A \<rightarrow> x))\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f g\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f g\<close> for x
    by (subst CHAOS_unfold)
      (auto simp add: Renaming_Mprefix Renaming_Ndet
        intro!: mono_Ndet_FD[OF idem_FD] mono_Mprefix_FD that)
qed

lemma Renaming_CHAOS_FD_CHAOS:
  \<open>Renaming (CHAOS A) f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A)\<close>
  if finitary: \<open>finitary f\<close> \<open>finitary g\<close>
proof (subst CHAOS_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A)\<close> by simp
next
  show \<open>Renaming ((\<Lambda> x. STOP \<sqinter> (\<box>xa\<in>A \<rightarrow> x))\<cdot>x) f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A)\<close>
    if \<open>Renaming x f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A)\<close> for x
    by (subst CHAOS_unfold)
      (auto simp add: Renaming_Mprefix Renaming_Ndet
        intro!: mono_Ndet_FD[OF idem_FD] mono_Mprefix_FD that)
qed


text \<open>For \<^const>\<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>\<close>

lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g\<close>
proof (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g)\<close>
    by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g\<close> by simp
next
  show \<open>(\<Lambda> x. SKIPS (g ` R) \<sqinter> STOP \<sqinter> (\<box>xa\<in>f ` A \<rightarrow> x))\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D 
        Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g\<close> for x
    by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: Renaming_Ndet Renaming_Mprefix
        intro!: mono_Ndet_FD mono_Mprefix_FD that)
qed

lemma Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close>
  if finitary: \<open>finitary f\<close> \<open>finitary g\<close>
proof (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close> by simp
next
  show \<open> Renaming ((\<Lambda> x. SKIPS R \<sqinter> STOP \<sqinter> (\<box>xa\<in>A \<rightarrow> x))\<cdot>x) f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close>
    if \<open>Renaming x f g \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` A) (g ` R)\<close> for x
    by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
      (auto simp add: Renaming_Ndet Renaming_Mprefix
        intro!: mono_Ndet_FD mono_Mprefix_FD that)
qed



subsection \<open>Corollaries on \<^const>\<open>deadlock_free\<close> and \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>\<close>

lemmas Renaming_DF = 
  FD_antisym[OF Renaming_DF_FD_DF DF_FD_Renaming_DF]
  and Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S =
  FD_antisym[OF Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S]
  and Renaming_RUN =
  FD_antisym[OF Renaming_RUN_FD_RUN RUN_FD_Renaming_RUN]
  and Renaming_CHAOS =
  FD_antisym[OF Renaming_CHAOS_FD_CHAOS CHAOS_FD_Renaming_CHAOS]
  and Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S =
  FD_antisym[OF Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S
    CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S]



lemma deadlock_free_imp_deadlock_free_Renaming: \<open>deadlock_free (Renaming P f g)\<close>
  if \<open>deadlock_free P\<close>
  apply (rule DF_Univ_freeness[of \<open>range f\<close>], simp)
  apply (rule trans_FD[OF DF_FD_Renaming_DF])
  apply (rule mono_Renaming_FD)
  by (rule that[unfolded deadlock_free_def])

(* TODO: should be true without inj g since no tick in the traces *)
lemma deadlock_free_Renaming_imp_deadlock_free: \<open>deadlock_free P\<close>
  if \<open>inj f\<close> and \<open>inj g\<close> and \<open>deadlock_free (Renaming P f g)\<close>
  apply (subst Renaming_inv[OF that(1, 2), symmetric])
  apply (rule deadlock_free_imp_deadlock_free_Renaming)
  by (rule that(3))

corollary deadlock_free_Renaming_iff:
  \<open>inj f \<Longrightarrow> inj g \<Longrightarrow> deadlock_free (Renaming P f g) \<longleftrightarrow> deadlock_free P\<close>
  using deadlock_free_Renaming_imp_deadlock_free
    deadlock_free_imp_deadlock_free_Renaming by blast



lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Renaming:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Renaming P f g)\<close>
  unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD
  apply (rule trans_FD[of _ \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (f ` UNIV) (g ` UNIV)\<close>])
  by (simp add: DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_subset) (meson DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S mono_Renaming_FD trans_FD)


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Renaming_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> if \<open>inj f\<close> and \<open>inj g\<close> and \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Renaming P f g)\<close>
  apply (subst Renaming_inv[OF that(1, 2), symmetric])
  apply (rule deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Renaming)
  by (rule that(3))

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Renaming_iff:
  \<open>inj f \<Longrightarrow> inj g \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Renaming P f g) \<longleftrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  using deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Renaming_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S
    deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Renaming by blast







section \<open>The big results\<close>

subsection \<open>An interesting equivalence\<close>

lemma deadlock_free_of_Sync_iff_DF_FD_DF_Sync_DF:
  \<open>(\<forall>P Q. deadlock_free (P::('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<longrightarrow> deadlock_free Q \<longrightarrow>
          deadlock_free (P \<lbrakk>S\<rbrakk> Q))
   \<longleftrightarrow> (DF UNIV :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<sqsubseteq>\<^sub>F\<^sub>D (DF UNIV \<lbrakk>S\<rbrakk> DF UNIV)\<close> (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
proof (rule iffI)
  assume ?lhs
  show ?rhs by (fold deadlock_free_def, rule \<open>?lhs\<close>[rule_format])
      (simp_all add: deadlock_free_def)
next
  assume ?rhs
  show ?lhs unfolding deadlock_free_def
    by (intro allI impI trans_FD[OF \<open>?rhs\<close>]) (rule mono_Sync_FD)
qed

text \<open>From this general equivalence on \<^const>\<open>Sync\<close>, we immediately obtain the equivalence
      on \<^term>\<open>(A ||| B)\<close>: @{thm deadlock_free_of_Sync_iff_DF_FD_DF_Sync_DF[of \<open>{}\<close>]}.\<close>


subsection \<open>\<^const>\<open>STOP\<close> and \<^const>\<open>SKIP\<close> synchronized with \<^term>\<open>DF A\<close>\<close>

lemma DF_FD_DF_Sync_STOP_or_SKIP_iff: 
  \<open>(DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P) \<longleftrightarrow> A \<inter> S = {}\<close>
  if P_disj: \<open>P = STOP \<or> P = SKIP r\<close>
proof
  { assume a1: \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P\<close> and a2: \<open>A \<inter> S \<noteq> {}\<close>
    from a2 obtain x where f1: \<open>x \<in> A\<close> and f2: \<open>x \<in> S\<close> by blast
    have \<open>DF A \<lbrakk>S\<rbrakk> P \<sqsubseteq>\<^sub>F\<^sub>D DF {x} \<lbrakk>S\<rbrakk> P\<close>
      by (intro mono_Sync_FD[OF _ idem_FD]) (simp add: DF_subset f1)
    also have \<open>\<dots> = STOP\<close>
      apply (subst DF_unfold)
      using P_disj apply (rule disjE; simp)
        (* TODO: write lemmas with Sync Mprefix and STOP  *)
       apply (simp add: write0_def, subst Mprefix_empty[symmetric])
       apply (subst Mprefix_Sync_Mprefix_right, (simp_all add: f2)[3])
      by (subst DF_unfold, simp add: f2 write0_Sync_SKIP)
    finally have False
      by (metis DF_Univ_freeness a1 empty_not_insert f1
          insert_absorb non_deadlock_free_STOP trans_FD)
  }
  thus \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P \<Longrightarrow> A \<inter> S = {}\<close> by blast
next
  have D_P: \<open>\<D> P = {}\<close> using D_SKIP[of r] D_STOP P_disj by blast
  note F_T_P = F_STOP T_STOP F_SKIP D_SKIP
  { assume a1: \<open>\<not> DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P\<close> and a2: \<open>A \<inter> S = {}\<close>
    have False
    proof (cases \<open>A = {}\<close>)
      assume \<open>A = {}\<close>
      with a1[unfolded DF_def] that show ?thesis
        by (auto simp add: fix_const)
    next
      assume a3: \<open>A \<noteq> {}\<close>
      from a1 show ?thesis
        unfolding failure_divergence_refine_def failure_refine_def divergence_refine_def
      proof (auto simp add: F_Sync D_Sync D_P div_free_DF subset_iff, goal_cases)
        case (1 a t u X Y)
        then show ?case
        proof (induct t arbitrary: a)
          case Nil
          show ?case by (rule disjE[OF P_disj], insert Nil a2)
              (subst (asm) F_DF, auto simp add: a3 F_T_P)+
        next
          case (Cons x t)
          from Cons(4) have f1: \<open>u = []\<close>
            apply (subst disjE[OF P_disj], simp_all add: F_T_P) 
            by (metis Cons.prems(1, 2, 4) F_T F_imp_front_tickFree Int_iff TickLeftSync
                append_T_imp_tickFree inf_sup_absorb is_processT5_S7 list.distinct(1)
                non_tickFree_tick rangeI setinterleaving_sym tickFree_Cons_iff tickFree_Nil tickFree_butlast)
          from Cons(2, 3) show False
            apply (subst (asm) (1 2) F_DF, auto simp add: a3)
            by (metis Cons.hyps Cons.prems(3, 4) setinterleaving_sym
                SyncTlEmpty emptyLeftProperty f1 list.sel(3))
        qed
      qed
    qed
  }
  thus \<open>A \<inter> S = {} \<Longrightarrow> DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P\<close> by blast
qed



lemma DF_Sync_STOP_or_SKIP_FD_DF: \<open>DF A \<lbrakk>S\<rbrakk> P \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close> 
  if P_disj: \<open>P = STOP \<or> P = SKIP r\<close> and empty_inter: \<open>A \<inter> S = {}\<close>
proof (cases \<open>A = {}\<close>)
  from P_disj show \<open>A = {} \<Longrightarrow> DF A \<lbrakk>S\<rbrakk> P \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close>
    by (rule disjE) (simp_all add: DF_def fix_const)
next
  assume \<open>A \<noteq> {}\<close>
  show ?thesis
  proof (subst DF_def, induct rule: fix_ind)
    show \<open>adm (\<lambda>a. a \<lbrakk>S\<rbrakk> P \<sqsubseteq>\<^sub>F\<^sub>D DF A)\<close> by (simp add: cont2mono)
  next
    show \<open>\<bottom> \<lbrakk>S\<rbrakk> P \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close> by (metis BOT_leFD Sync_BOT Sync_commute)
  next
    case (3 x)
    have \<open>(\<sqinter>a \<in> A \<rightarrow> x) \<lbrakk>S\<rbrakk> P \<sqsubseteq>\<^sub>F\<^sub>D (a \<rightarrow> DF A)\<close> if \<open>a \<in> A\<close> for a
      find_theorems  Mndetprefix name: set 
      apply (rule trans_FD[OF mono_Sync_FD
            [OF Mndetprefix_FD_subset
              [of \<open>{a}\<close>, simplified, OF that] idem_FD]])
      apply (rule disjE[OF P_disj], simp_all)
       apply (subst Mprefix_Sync_Mprefix_left
          [of \<open>{a}\<close> _ \<open>{}\<close> \<open>\<lambda>a. x\<close>, simplified, folded write0_def])
      using empty_inter that apply blast
      using "3" mono_write0_FD apply fast
      by (metis "3" disjoint_iff empty_inter mono_write0_FD that write0_Sync_SKIP)
    thus ?case by (subst DF_unfold, subst FD_Mndetprefix_iff; simp add: \<open>A \<noteq> {}\<close>)
  qed
qed



lemmas DF_FD_DF_Sync_STOP_iff = 
  DF_FD_DF_Sync_STOP_or_SKIP_iff[of STOP, simplified]
  and DF_FD_DF_Sync_SKIP_iff =
  DF_FD_DF_Sync_STOP_or_SKIP_iff[of \<open>SKIP r\<close>, simplified]
  and DF_Sync_STOP_FD_DF =
  DF_Sync_STOP_or_SKIP_FD_DF[of STOP, simplified]
  and DF_Sync_SKIP_FD_DF = 
  DF_Sync_STOP_or_SKIP_FD_DF[of \<open>SKIP r\<close>, simplified] for r



subsection \<open>Finally, \<^term>\<open>deadlock_free (P ||| Q)\<close>\<close>

theorem DF_F_DF_Sync_DF: \<open>(DF (A \<union> B) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<sqsubseteq>\<^sub>F DF A \<lbrakk>S\<rbrakk> DF B\<close>
  if  nonempty: \<open>A \<noteq> {} \<and> B \<noteq> {}\<close>
    and intersect_hyp: \<open>B \<inter> S = {} \<or> (\<exists>y. B \<inter> S = {y} \<and> A \<inter> S \<subseteq> {y})\<close>
proof -
  let ?Z = \<open>range tick \<union> ev ` S :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  have \<open>\<lbrakk>(t, X) \<in> \<F> (DF A); (u, Y) \<in> \<F> (DF B); v setinterleaves ((t, u), ?Z)\<rbrakk>
        \<Longrightarrow> (v, (X \<union> Y) \<inter> ?Z \<union> X \<inter> Y) \<in> \<F> (DF (A \<union> B))\<close> for v t u :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and X Y
  proof (induct \<open>(t, ?Z, u)\<close> arbitrary: t u v rule: setinterleaving.induct)
    case (1 v)
    from "1.prems"(3) emptyLeftProperty have \<open>v = []\<close> by blast
    with intersect_hyp "1.prems"(1, 2) show ?case
      by (subst (asm) (1 2) F_DF, subst F_DF) 
        (simp add: nonempty image_iff subset_iff, metis IntI empty_iff insertE)
  next
    case (2 y u)
    from "2.prems"(3) emptyLeftProperty obtain b
      where \<open>b \<notin> S\<close> \<open>y = ev b\<close> \<open>v = y # u\<close> \<open>u setinterleaves (([], u), ?Z)\<close>
      by (cases y) (auto simp add: image_iff split: if_split_asm)
    from "2.prems"(2) have \<open>b \<in> B\<close> \<open>(u, Y) \<in> \<F> (DF B)\<close>
      by (subst (asm) F_DF; simp add: \<open>y = ev b\<close> nonempty)+
    have \<open>(u, (X \<union> Y) \<inter> ?Z \<union> X \<inter> Y) \<in> \<F> (DF (A \<union> B))\<close>
      by (rule "2.hyps")
        (simp_all add: "2.prems"(1) \<open>(u, Y) \<in> \<F> (DF B)\<close> \<open>b \<notin> S\<close> \<open>y = ev b\<close>
          \<open>u setinterleaves (([], u), ?Z)\<close> image_iff)
    thus ?case by (subst F_DF) (simp add: nonempty \<open>v = y # u\<close> \<open>y = ev b\<close> \<open>b \<in> B\<close>)
  next
    case (3 x t)
    from "3.prems"(3) emptyRightProperty obtain a
      where \<open>a \<notin> S\<close> \<open>x = ev a\<close> \<open>v = x # t\<close> \<open>t setinterleaves ((t, []), ?Z)\<close>
      by (cases x) (auto simp add: image_iff split: if_split_asm)
    from "3.prems"(1) have \<open>a \<in> A\<close> \<open>(t, X) \<in> \<F> (DF A)\<close>
      by (subst (asm) F_DF; simp add: \<open>x = ev a\<close> nonempty)+
    have \<open>(t, (X \<union> Y) \<inter> ?Z \<union> X \<inter> Y) \<in> \<F> (DF (A \<union> B))\<close>
      by (rule "3.hyps")
        (simp_all add: "3.prems"(2) \<open>(t, X) \<in> \<F> (DF A)\<close> \<open>a \<notin> S\<close> \<open>x = ev a\<close>
          \<open>t setinterleaves ((t, []), ?Z)\<close> image_iff)
    thus ?case by (subst F_DF) (simp add: nonempty \<open>v = x # t\<close> \<open>x = ev a\<close> \<open>a \<in> A\<close>)
  next
    case (4 x t y u)
    from "4.prems"(1) obtain a where \<open>a \<in> A\<close> \<open>x = ev a\<close> \<open>(t, X) \<in> \<F> (DF A)\<close>
      by (subst (asm) F_DF) (auto simp add: nonempty)
    from "4.prems"(2) obtain b where \<open>b \<in> B\<close> \<open>y = ev b\<close> \<open>(u, Y) \<in> \<F> (DF B)\<close>
      by (subst (asm) F_DF) (auto simp add: nonempty)
    consider \<open>x \<in> ?Z\<close> \<open>y \<in> ?Z\<close> | \<open>x \<in> ?Z\<close> \<open>y \<notin> ?Z\<close>
      | \<open>x \<notin> ?Z\<close> \<open>y \<in> ?Z\<close> | \<open>x \<notin> ?Z\<close> \<open>y \<notin> ?Z\<close> by blast
    thus ?case
    proof cases
      assume \<open>x \<in> ?Z\<close> \<open>y \<in> ?Z\<close>
      with "4.prems"(3) obtain v'
        where \<open>x = y\<close> \<open>v = y # v'\<close> \<open>v' setinterleaves ((t, u), ?Z)\<close>
        by (simp split: if_split_asm) blast
      from "4.hyps"(1)[OF \<open>x \<in> ?Z\<close> \<open>y \<in> ?Z\<close> \<open>x = y\<close>
          \<open>(t, X) \<in> \<F> (DF A)\<close> \<open>(u, Y) \<in> \<F> (DF B)\<close> this(3)]
      have \<open>(v', (X \<union> Y) \<inter> ?Z \<union> X \<inter> Y) \<in> \<F> (DF (A \<union> B))\<close> .
      thus ?case by (subst F_DF) (simp add: nonempty \<open>v = y # v'\<close> \<open>y = ev b\<close> \<open>b \<in> B\<close>)
    next
      assume \<open>x \<in> ?Z\<close> \<open>y \<notin> ?Z\<close>
      with "4.prems"(3) obtain v'
        where \<open>v = y # v'\<close> \<open>v' setinterleaves ((x # t, u), ?Z)\<close>
        by (simp split: if_split_asm) blast
      from "4.hyps"(2)[OF \<open>x \<in> ?Z\<close> \<open>y \<notin> ?Z\<close> "4.prems"(1) \<open>(u, Y) \<in> \<F> (DF B)\<close> this(2)]
      have \<open>(v', (X \<union> Y) \<inter> ?Z \<union> X \<inter> Y) \<in> \<F> (DF (A \<union> B))\<close> .
      thus ?case by (subst F_DF) (simp add: nonempty \<open>v = y # v'\<close> \<open>y = ev b\<close> \<open>b \<in> B\<close>)
    next
      assume \<open>x \<notin> ?Z\<close> \<open>y \<in> ?Z\<close>
      with "4.prems"(3) obtain v'
        where \<open>v = x # v'\<close> \<open>v' setinterleaves ((t, y # u), ?Z)\<close>
        by (simp split: if_split_asm) blast
      from "4.prems"(2) "4.hyps"(5) \<open>x \<notin> ?Z\<close> \<open>y \<in> ?Z\<close> \<open>(t, X) \<in> \<F> (DF A)\<close> this(2)
      have \<open>(v', (X \<union> Y) \<inter> ?Z \<union> X \<inter> Y) \<in> \<F> (DF (A \<union> B))\<close> by simp
      thus ?case by (subst F_DF) (simp add: nonempty \<open>v = x # v'\<close> \<open>x = ev a\<close> \<open>a \<in> A\<close>)
    next
      assume \<open>x \<notin> ?Z\<close> \<open>y \<notin> ?Z\<close>
      with "4.prems"(3) obtain v'
        where \<open>v = x # v' \<and> v' setinterleaves ((t, y # u), ?Z) \<or>
               v = y # v' \<and> v' setinterleaves ((x # t, u), ?Z)\<close> by auto
      thus ?case
      proof (elim disjE conjE)
        assume \<open>v = x # v'\<close> \<open>v' setinterleaves ((t, y # u), ?Z)\<close>
        from "4.hyps"(3)[OF \<open>x \<notin> ?Z\<close> \<open>y \<notin> ?Z\<close> \<open>(t, X) \<in> \<F> (DF A)\<close> "4.prems"(2) this(2)]
        have \<open>(v', (X \<union> Y) \<inter> ?Z \<union> X \<inter> Y) \<in> \<F> (DF (A \<union> B))\<close> .
        thus ?case by (subst F_DF) (simp add: nonempty \<open>v = x # v'\<close> \<open>x = ev a\<close> \<open>a \<in> A\<close>)
      next
        assume \<open>v = y # v'\<close> \<open>v' setinterleaves ((x # t, u), ?Z)\<close>
        from "4.hyps"(4)[OF \<open>x \<notin> ?Z\<close> \<open>y \<notin> ?Z\<close> "4.prems"(1) \<open>(u, Y) \<in> \<F> (DF B)\<close> this(2)]
        have \<open>(v', (X \<union> Y) \<inter> ?Z \<union> X \<inter> Y) \<in> \<F> (DF (A \<union> B))\<close> .
        thus ?case by (subst F_DF) (simp add: nonempty \<open>v = y # v'\<close> \<open>y = ev b\<close> \<open>b \<in> B\<close>)
      qed
    qed
  qed

  thus \<open>(DF (A \<union> B) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<sqsubseteq>\<^sub>F DF A \<lbrakk>S\<rbrakk> DF B\<close>
    by (auto simp add: failure_refine_def F_Sync div_free_DF)
qed


lemma DF_FD_DF_Sync_DF:
  \<open>A \<noteq> {} \<and> B \<noteq> {} \<Longrightarrow> B \<inter> S = {} \<or> (\<exists>y. B \<inter> S = {y} \<and> A \<inter> S \<subseteq> {y}) \<Longrightarrow> 
   DF (A \<union> B) \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> DF B\<close>
  unfolding failure_divergence_refine_def failure_refine_def divergence_refine_def 
  by (simp add: div_free_DF D_Sync)
    (simp add: DF_F_DF_Sync_DF[unfolded failure_refine_def])

theorem DF_FD_DF_Sync_DF_iff:
  \<open>DF (A \<union> B) \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> DF B \<longleftrightarrow> 
   (     if A = {} then B \<inter> S = {}
    else if B = {} then A \<inter> S = {}
    else A \<inter> S = {} \<or> (\<exists>a. A \<inter> S = {a} \<and> B \<inter> S \<subseteq> {a}) \<or>
         B \<inter> S = {} \<or> (\<exists>b. B \<inter> S = {b} \<and> A \<inter> S \<subseteq> {b}))\<close>
  (is \<open>?FD_ref \<longleftrightarrow> (     if A = {} then B \<inter> S = {}
                    else if B = {} then A \<inter> S = {} 
                    else ?cases)\<close>)

  apply (cases \<open>A = {}\<close>, simp,
      metis DF_FD_DF_Sync_STOP_iff DF_unfold Sync_commute Mndetprefix_empty)
  apply (cases \<open>B = {}\<close>, simp,
      metis DF_FD_DF_Sync_STOP_iff DF_unfold Sync_commute Mndetprefix_empty)
proof (simp, intro iffI)
  { assume \<open>A \<noteq> {}\<close> and \<open>B \<noteq> {}\<close> and ?FD_ref and \<open>\<not> ?cases\<close>
    from \<open>\<not> ?cases\<close>[simplified] 
    obtain a and b where \<open>a \<in> A\<close> \<open>a \<in> S\<close> \<open>b \<in> B\<close> \<open>b \<in> S\<close> \<open>a \<noteq> b\<close> by blast
    have \<open>DF A \<lbrakk>S\<rbrakk> DF B \<sqsubseteq>\<^sub>F\<^sub>D (a \<rightarrow> DF A) \<lbrakk>S\<rbrakk> (b \<rightarrow> DF B)\<close>
      by (intro mono_Sync_FD; subst DF_unfold, meson Mndetprefix_FD_write0 \<open>a \<in> A\<close> \<open>b \<in> B\<close>)
    also have \<open>\<dots> = STOP\<close> by (simp add: \<open>a \<in> S\<close> \<open>a \<noteq> b\<close> \<open>b \<in> S\<close> write0_Sync_write0_subset)
    finally have False
      by (metis DF_Univ_freeness Un_empty \<open>A \<noteq> {}\<close>
          trans_FD[OF \<open>?FD_ref\<close>] non_deadlock_free_STOP)}
  thus \<open>A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> ?FD_ref \<Longrightarrow> ?cases\<close> by fast
qed (metis Sync_commute Un_commute DF_FD_DF_Sync_DF)





lemma
  \<open>(\<forall>a \<in> A. X a \<inter> S = {} \<or> (\<forall>b \<in> A. \<exists>y. X a \<inter> S = {y} \<and> X b \<inter> S \<subseteq> {y}))
   \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> A. \<exists>y. (X a \<union> X b) \<inter> S \<subseteq> {y})\<close>
  \<comment> \<open>this is the reason we write ugly\_hyp this way\<close>
  apply (subst Int_Un_distrib2, auto)
  by (metis subset_insertI) blast


lemma DF_FD_DF_MultiSync_DF:
  \<open>(DF (\<Union> x \<in> (insert a A). X x) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk> x \<in># mset_set (insert a A). DF (X x)\<close>
  if fin: \<open>finite A\<close> and nonempty: \<open>X a \<noteq> {}\<close> \<open>\<forall>b \<in> A. X b \<noteq> {}\<close>
    and ugly_hyp: \<open>\<forall>b \<in> A. X b \<inter> S = {} \<or> (\<exists>y. X b \<inter> S = {y} \<and> X a \<inter> S \<subseteq> {y})\<close>
    \<open>\<forall>b \<in> A. \<forall>c \<in> A. \<exists>y. (X b \<union> X c) \<inter> S \<subseteq> {y}\<close>

  apply (rule conjunct1[where Q = \<open>\<forall>b \<in> A. X b \<inter> S = {} \<or> 
                        (\<exists>y. X b \<inter> S = {y} \<and> \<Union> (X ` insert a A) \<inter> S \<subseteq> {y})\<close>])
        (* we need to add this in our induction *)
proof (induct rule: finite_subset_induct_singleton'
    [of a \<open>insert a A\<close>, simplified, OF fin, 
      simplified subset_insertI, simplified])
  case 1
  show ?case by (simp add: ugly_hyp)
next
  case (2 b A') 
  show ?case
  proof (rule conjI; subst image_insert, subst Union_insert)
    show \<open>DF (X b \<union> \<Union> (X ` insert a A')) \<sqsubseteq>\<^sub>F\<^sub>D
          \<^bold>\<lbrakk>S\<^bold>\<rbrakk> a\<in>#mset_set (insert b (insert a A')). (DF (X a) :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
      apply (subst Un_commute)
      apply (rule trans_FD[OF DF_FD_DF_Sync_DF[where S = S]])
        apply (simp add: "2.hyps"(2) nonempty ugly_hyp(1))
      using "2.hyps"(2, 5) apply blast
      apply (subst Sync_commute,
          rule trans_FD[OF mono_Sync_FD
            [OF idem_FD "2.hyps"(5)[THEN conjunct1]]])
      by (simp add: "2.hyps"(1, 4) mset_set_empty_iff)
  next
    show \<open>\<forall>c \<in> A. X c \<inter> S = {} \<or> (\<exists>y. X c \<inter> S = {y} \<and> 
                  (X b \<union> \<Union> (X ` insert a A')) \<inter> S \<subseteq> {y})\<close>
      apply (subst Int_Un_distrib2, subst Un_subset_iff)
      by (metis "2.hyps"(2, 5) Int_Un_distrib2 Un_subset_iff 
          subset_singleton_iff ugly_hyp(2))
  qed
qed



lemma DF_FD_DF_MultiSync_DF':
  \<open>\<lbrakk>finite A; \<forall>a \<in> A. X a \<noteq> {}; \<forall>a \<in> A. \<forall>b \<in> A. \<exists>y. (X a \<union> X b) \<inter> S \<subseteq> {y}\<rbrakk>
   \<Longrightarrow> DF (\<Union> a \<in> A. X a) \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># mset_set A. DF (X a)\<close>
  apply (cases A rule: finite.cases, assumption)
   apply (subst DF_unfold, simp)
  apply clarify
  apply (rule DF_FD_DF_MultiSync_DF)
  by simp_all (metis Int_Un_distrib2 Un_subset_iff subset_singleton_iff)



lemmas DF_FD_DF_MultiInter_DF  = 
  DF_FD_DF_MultiSync_DF'[where S = \<open>{}\<close>, simplified]
  and   DF_FD_DF_MultiPar_DF  = 
  DF_FD_DF_MultiSync_DF [where S = UNIV, simplified]
  and   DF_FD_DF_MultiPar_DF' = 
  DF_FD_DF_MultiSync_DF'[where S = UNIV, simplified]



lemma \<open>DF {a} = DF {a} \<lbrakk>S\<rbrakk> STOP \<longleftrightarrow> a \<notin> S\<close>
  by (metis DF_FD_DF_Sync_STOP_iff DF_Sync_STOP_FD_DF Diff_disjoint 
      Diff_insert_absorb FD_antisym insert_disjoint(2))

lemma \<open>DF {a} \<lbrakk>S\<rbrakk> STOP = STOP \<longleftrightarrow> a \<in> S\<close>
  by (metis (no_types, lifting) DF_unfold Diff_disjoint Diff_eq_empty_iff Int_commute
      Int_insert_left Mndetprefix_Sync_STOP Mndetprefix_is_STOP_iff
      Ndet_is_STOP_iff empty_not_insert inf_le2)


corollary DF_FD_DF_Inter_DF: \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A ||| DF A\<close>
  by (metis DF_FD_DF_Sync_DF_iff inf_bot_right sup.idem)

corollary DF_UNIV_FD_DF_UNIV_Inter_DF_UNIV:
  \<open>DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D DF UNIV ||| DF UNIV\<close>
  by (fact DF_FD_DF_Inter_DF)

corollary Inter_deadlock_free:
  \<open>deadlock_free P \<Longrightarrow> deadlock_free Q \<Longrightarrow> deadlock_free (P ||| Q)\<close>
  using DF_FD_DF_Inter_DF deadlock_free_of_Sync_iff_DF_FD_DF_Sync_DF by blast


theorem MultiInter_deadlock_free:
  \<open>\<lbrakk>M \<noteq> {#}; \<And>m. m \<in># M \<Longrightarrow> deadlock_free (P m)\<rbrakk> \<Longrightarrow>
   deadlock_free (\<^bold>|\<^bold>|\<^bold>| p \<in># M. P p)\<close>
proof (induct rule: mset_induct_nonempty)
  case (m_singleton a) thus ?case by simp
next
  case (add x F) with Inter_deadlock_free show ?case by auto
qed

(*<*)
end
  (*>*)
