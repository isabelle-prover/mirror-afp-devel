(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Powerful results on DF and deadlock_free
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


chapter \<open> Deadlock Results \<close>

theory DeadlockResults
  imports CSPM
begin

text \<open>When working with the interleaving \<^term>\<open>P ||| Q\<close>, we intuitively expect it to be
      \<^const>\<open>deadlock_free\<close> when both \<^term>\<open>P\<close> and \<^term>\<open>Q\<close> are.

      This chapter contains several results about deadlock notion, and concludes
      with a proof of the theorem we just mentioned.\<close>



section \<open>Unfolding Lemmas for the Projections of \<^const>\<open>DF\<close> and \<^const>\<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close>\<close>

text \<open>\<^const>\<open>DF\<close> and \<^const>\<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close> naturally appear when we work around \<^const>\<open>deadlock_free\<close>
      and \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close> notions (because

      @{thm deadlock_free_def[of P] deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def[of P]}).

      It is therefore convenient to have the following rules for unfolding the projections.\<close>

lemma F_DF: 
  \<open>\<F> (DF A) =
   (if A = {} then {(s, X). s = []}
    else (\<Union>x\<in>A. {[]} \<times> {ref. ev x \<notin> ref} \<union> 
                 {(tr, ref). tr \<noteq> [] \<and> hd tr = ev x \<and> (tl tr, ref) \<in> \<F> (DF A)}))\<close>
  and F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: 
  \<open>\<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) =
   (if A = {} then {(s, X). s = [] \<or> s = [tick]}
    else {(s, X)| s X. s = [] \<and> tick \<notin> X \<or> s = [tick]} \<union>
         (\<Union>x\<in>A. {[]} \<times> {ref. ev x \<notin> ref} \<union> 
                 {(tr, ref). tr \<noteq> [] \<and> hd tr = ev x \<and> (tl tr, ref) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)}))\<close>
  by (subst DF_unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold;
      auto simp add: F_STOP F_Mprefix F_Mndetprefix write0_def F_SKIP F_Ndet)+


corollary Cons_F_DF:
  \<open>(x # t, X) \<in> \<F> (DF A) \<Longrightarrow> (t, X) \<in> \<F> (DF A)\<close>
      and Cons_F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>x \<noteq> tick \<Longrightarrow> (x # t, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<Longrightarrow> (t, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)\<close>
  by (subst (asm) F_DF F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P; auto split: if_split_asm)+


lemma D_DF: \<open>\<D> (DF A) = (if A = {} then {}
             else {s. s \<noteq> [] \<and> (\<exists>x \<in> A. hd s = ev x \<and> tl s \<in> \<D> (DF A))})\<close>
  and D_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: \<open>\<D> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = (if A = {} then {}
                else {s. s \<noteq> [] \<and> (\<exists>x \<in> A. hd s = ev x \<and> tl s \<in> \<D> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A))})\<close>
  by (subst DF_unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold; 
      auto simp add: D_Mndetprefix D_Mprefix write0_def D_Ndet D_SKIP)+


lemma T_DF: 
  \<open>\<T> (DF A) = 
   (if A = {} then {[]}
    else {s. s = [] \<or> s \<noteq> [] \<and> (\<exists>x \<in> A. hd s = ev x \<and> tl s \<in> \<T> (DF A))})\<close>
  and T_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: 
  \<open>\<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) =
   (if A = {} then {[], [tick]}
    else {s. s = [] \<or> s = [tick] \<or> 
             s \<noteq> [] \<and> (\<exists>x \<in> A. hd s = ev x \<and> tl s \<in> \<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A))})\<close>
  by (subst DF_unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold; 
      auto simp add: T_STOP T_Mndetprefix write0_def T_Mprefix T_Ndet T_SKIP)+



section \<open>Characterizations for \<^const>\<open>deadlock_free\<close>, \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close>\<close>

text \<open>We want more results like @{thm deadlock_free_Ndet[of P Q]},
      and we want to add the reciprocal when possible.\<close>

text \<open>The first thing we notice is that we only have to care about the failures\<close>
lemma \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<equiv> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F P\<close>
  by (fact deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def)

lemma deadlock_free_F: \<open>deadlock_free P \<longleftrightarrow> DF UNIV \<sqsubseteq>\<^sub>F P\<close>
  by (metis deadlock_free_def div_free_divergence_refine(5) leFD_imp_leF
            leF_imp_leT leF_leD_imp_leFD non_terminating_refine_DF
            nonterminating_implies_div_free)
 


lemma deadlock_free_Mprefix_iff: \<open>deadlock_free (\<box> a \<in> A \<rightarrow> P a) \<longleftrightarrow> 
                                  A \<noteq> {} \<and> (\<forall>a \<in> A. deadlock_free (P a))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Mprefix_iff: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (Mprefix A P) \<longleftrightarrow> 
                                     A \<noteq> {} \<and> (\<forall>a \<in> A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P a))\<close>
  unfolding deadlock_free_F deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def failure_refine_def
   apply (all \<open>subst F_DF F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close>,
          auto simp add: div_free_DF F_Mprefix D_Mprefix subset_iff)
  by (metis imageI list.distinct(1) list.sel(1, 3))
     (metis (no_types, lifting) event.distinct(1) image_eqI list.sel(1, 3) neq_Nil_conv)
  

lemmas deadlock_free_prefix_iff = 
       deadlock_free_Mprefix_iff   [of \<open>{a}\<close> \<open>\<lambda>a. P\<close>, folded write0_def, simplified]
   and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_prefix_iff = 
       deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Mprefix_iff[of \<open>{a}\<close> \<open>\<lambda>a. P\<close>, folded write0_def, simplified]
   for a P


lemma deadlock_free_Mndetprefix_iff: \<open>deadlock_free (\<sqinter> a \<in> A \<rightarrow> P a) \<longleftrightarrow>
                                      A \<noteq> {} \<and> (\<forall>a\<in>A. deadlock_free (P a))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Mndetprefix_iff: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (\<sqinter> a \<in> A \<rightarrow> P a) \<longleftrightarrow> 
                                         A \<noteq> {} \<and> (\<forall>a\<in>A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P a))\<close>
   apply (all \<open>intro iffI conjI\<close>)
  using non_deadlock_free_STOP 
       apply force
      apply (meson Mprefix_refines_Mndetprefix_FD 
      deadlock_free_Mprefix_iff deadlock_free_def trans_FD)
     apply (metis (no_types, lifting) Mndetprefix_GlobalNdet 
      deadlock_free_def deadlock_free_prefix_iff mono_GlobalNdet_FD_const)
  using non_deadlock_free_v2_STOP 
    apply force
   apply (meson Mprefix_refines_Mndetprefix_FD deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD
      deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Mprefix_iff trans_FD)
  by (metis (no_types, lifting) Mndetprefix_GlobalNdet deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_prefix_iff
            deadlock_free_v2_FD mono_GlobalNdet_FD_const)





lemma deadlock_free_Ndet_iff: \<open>deadlock_free (P \<sqinter> Q) \<longleftrightarrow> 
                               deadlock_free P \<and> deadlock_free Q\<close> 
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Ndet_iff: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P \<sqinter> Q) \<longleftrightarrow>
                                  deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<and> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P Q\<close>
  unfolding deadlock_free_F deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def failure_refine_def
  by (simp_all add: F_Ndet)



lemma deadlock_free_GlobalNdet_iff: \<open>deadlock_free (\<sqinter> a \<in> A. P a) \<longleftrightarrow>
                                     A \<noteq> {} \<and> (\<forall> a \<in> A. deadlock_free (P a))\<close> 
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_GlobalNdet_iff: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (\<sqinter> a \<in> A. P a) \<longleftrightarrow>
                                        A \<noteq> {} \<and> (\<forall> a \<in> A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P a))\<close>
  by (metis (mono_tags, lifting) GlobalNdet_refine_FD deadlock_free_def trans_FD
            mono_GlobalNdet_FD_const non_deadlock_free_STOP empty_GlobalNdet)
     (metis (mono_tags, lifting) GlobalNdet_refine_FD deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD trans_FD
            mono_GlobalNdet_FD_const non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_STOP empty_GlobalNdet)


lemma deadlock_free_MultiNdet_iff: \<open>deadlock_free (\<Sqinter> a \<in> A. P a) \<longleftrightarrow>
                                    A \<noteq> {} \<and> (\<forall> a \<in> A. deadlock_free (P a))\<close> 
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_MultiNdet_iff: \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (\<Sqinter> a \<in> A. P a) \<longleftrightarrow> 
                                       A \<noteq> {} \<and> (\<forall> a \<in> A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P a))\<close>
   if fin: \<open>finite A\<close>
  by (metis deadlock_free_GlobalNdet_iff    finite_GlobalNdet_is_MultiNdet that)
     (metis deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_GlobalNdet_iff finite_GlobalNdet_is_MultiNdet that)




lemma deadlock_free_MultiDet:
  \<open>\<lbrakk>A \<noteq> {}; finite A; \<forall>a\<in>A. deadlock_free (P a)\<rbrakk> \<Longrightarrow> deadlock_free (\<^bold>\<box>a \<in> A. P a)\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_MultiDet:
  \<open>\<lbrakk>A \<noteq> {}; finite A; \<forall>a\<in>A. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P a)\<rbrakk> \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (\<^bold>\<box>a \<in> A. P a)\<close>
  by (metis deadlock_free_MultiNdet_iff deadlock_free_def
            mono_MultiNdet_MultiDet_FD trans_FD)
     (metis deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_MultiNdet_iff
            mono_MultiNdet_MultiDet_FD trans_FD)


lemma deadlock_free_Det:
  \<open>deadlock_free    P \<Longrightarrow> deadlock_free    Q \<Longrightarrow> deadlock_free    (P \<box> Q)\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Det:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P Q \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P \<box> Q)\<close>
  by (meson deadlock_free_Ndet deadlock_free_def mono_Ndet_Det_FD trans_FD)
     (metis deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Ndet_iff mono_Ndet_Det_FD trans_FD)



text \<open>For \<^term>\<open>P \<box> Q\<close>, we can not expect more:\<close>

lemma
  \<open>\<exists>P Q. deadlock_free    P \<and> \<not> deadlock_free    Q \<and>
         deadlock_free     (P \<box> Q)\<close>
  \<open>\<exists>P Q. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<and> \<not> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P Q \<and>
         deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P \<box> Q)\<close>
  by (metis Det_STOP deadlock_free_def idem_FD non_deadlock_free_STOP)
     (metis Det_STOP deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD idem_FD non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_STOP)

 


lemma FD_Mndetprefix_iff:
  \<open>A \<noteq> {} \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter> a \<in> A \<rightarrow> Q \<longleftrightarrow> (\<forall>a \<in> A. P \<sqsubseteq>\<^sub>F\<^sub>D (a \<rightarrow> Q))\<close>
  by (auto simp: failure_divergence_refine_def le_ref_def subset_iff
                 D_Mndetprefix F_Mndetprefix write0_def D_Mprefix F_Mprefix) blast


lemma Mndetprefix_FD: \<open>(\<exists>a \<in> A. (a \<rightarrow> Q) \<sqsubseteq>\<^sub>F\<^sub>D P) \<Longrightarrow> \<sqinter> a \<in> A \<rightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (meson Mndetprefix_refine_FD failure_divergence_refine_def trans_FD)




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
    apply (subst Mprefix_Sync_distr; simp add: assms Mprefix_STOP) 
    by (metis (no_types, lifting) Det_STOP Det_commute Mprefix_STOP
              assms(6, 7, 8) deadlock_free_Det deadlock_free_Mprefix_iff)
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
      on reference processes from \<^theory>\<open>HOL-CSP.Assertions\<close>, and deadlock notion.\<close>

subsection \<open>Behaviour with References Processes\<close>

text \<open>For \<^const>\<open>DF\<close>\<close>

lemma DF_FD_Renaming_DF: \<open>DF (f ` A) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f\<close>
proof (subst DF_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f)\<close> by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f\<close> by simp
next
  show \<open>(\<Lambda> x. \<sqinter>a \<in> f ` A \<rightarrow>  x)\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF A) f\<close> for x
    apply simp
    apply (subst DF_unfold)
    apply (subst Renaming_Mndetprefix)
    by (rule mono_Mndetprefix_FD[rule_format, OF that])
qed

lemma Renaming_DF_FD_DF: \<open>Renaming (DF A) f \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A)\<close>
  if finitary: \<open>finitary f\<close>
proof (subst DF_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A)\<close> by (simp add: Renaming_BOT)
next
  show \<open>Renaming ((\<Lambda> x. \<sqinter>a \<in> A \<rightarrow>  x)\<cdot>x) f \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A)\<close>
    if \<open>Renaming x f \<sqsubseteq>\<^sub>F\<^sub>D DF (f ` A)\<close> for x
    apply simp
    apply (subst Renaming_Mndetprefix)
    apply (subst DF_unfold)
    by (rule mono_Mndetprefix_FD[rule_format, OF that])
qed


text \<open>For \<^const>\<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close>\<close>

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f\<close>
proof (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f)\<close> by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f\<close> by simp
next
  show \<open>(\<Lambda> x. (\<sqinter> a\<in>f ` A \<rightarrow>  x) \<sqinter> SKIP)\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f\<close> for x
    apply simp
    apply (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
    apply (simp add: Renaming_Ndet Renaming_SKIP)
    apply (subst Renaming_Mndetprefix)
    apply (rule mono_Ndet_FD [OF _ idem_FD])
    by (rule mono_Mndetprefix_FD[rule_format, OF that])
qed

lemma Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>Renaming (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A)\<close>
  if finitary: \<open>finitary f\<close>
proof (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A)\<close> by (simp add: Renaming_BOT)
next
  show \<open>Renaming ((\<Lambda> x. (\<sqinter>a \<in> A \<rightarrow>  x) \<sqinter> SKIP)\<cdot>x) f \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A)\<close>
    if \<open>Renaming x f \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A)\<close> for x
    apply simp
    apply (simp add: Renaming_Ndet Renaming_SKIP)
    apply (subst Renaming_Mndetprefix)
    apply (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
    apply (rule mono_Ndet_FD [OF _ idem_FD])
    by (rule mono_Mndetprefix_FD[rule_format, OF that])
qed



text \<open>For \<^const>\<open>RUN\<close>\<close>

lemma RUN_FD_Renaming_RUN: \<open>RUN (f ` A) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f\<close>
proof (subst RUN_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f)\<close> by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f\<close> by simp
next
  show \<open>(\<Lambda> x. \<box>a \<in> f ` A \<rightarrow>  x)\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (RUN A) f\<close> for x
    apply simp
    apply (subst RUN_unfold)
    apply (subst Renaming_Mprefix)
    by (rule mono_Mprefix_FD[rule_format, OF that])
qed

lemma Renaming_RUN_FD_RUN: \<open>Renaming (RUN A) f \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A)\<close>
  if finitary: \<open>finitary f\<close>
proof (subst RUN_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A)\<close> by (simp add: Renaming_BOT)
next
  show \<open>Renaming ((\<Lambda> x. \<box>a \<in> A \<rightarrow>  x)\<cdot>x) f \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A)\<close>
    if \<open>Renaming x f \<sqsubseteq>\<^sub>F\<^sub>D RUN (f ` A)\<close> for x
    apply simp
    apply (subst Renaming_Mprefix)
    apply (subst RUN_unfold)
    by (rule mono_Mprefix_FD[rule_format, OF that])
qed


text \<open>For \<^const>\<open>CHAOS\<close>\<close>

lemma CHAOS_FD_Renaming_CHAOS:
  \<open>CHAOS (f ` A) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f\<close>
proof (subst CHAOS_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f)\<close> by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f\<close> by simp
next
  show \<open>(\<Lambda> x. STOP \<sqinter> (\<box>a\<in>f ` A \<rightarrow> x))\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS A) f\<close> for x
    apply simp
    apply (subst CHAOS_unfold)
    apply (simp add: Renaming_Ndet Renaming_STOP)
    apply (rule mono_Ndet_FD[OF idem_FD])
    apply (subst Renaming_Mprefix)
    by (rule mono_Mprefix_FD[rule_format, OF that])
qed

lemma Renaming_CHAOS_FD_CHAOS:
  \<open>Renaming (CHAOS A) f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A)\<close>
  if finitary: \<open>finitary f\<close>
proof (subst CHAOS_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A)\<close> by (simp add: Renaming_BOT)
next
  show \<open>Renaming ((\<Lambda> x. STOP \<sqinter> (\<box>xa\<in>A \<rightarrow> x))\<cdot>x) f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A)\<close>
    if \<open>Renaming x f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS (f ` A)\<close> for x
    apply simp
    apply (simp add: Renaming_Ndet Renaming_STOP)
    apply (subst CHAOS_unfold)
    apply (subst Renaming_Mprefix)
    apply (rule mono_Ndet_FD[OF idem_FD])
    by (rule mono_Mprefix_FD[rule_format, OF that])
qed


text \<open>For \<^const>\<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close>\<close>

lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A) \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f\<close>
proof (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f)\<close>
    by (simp add: monofun_def)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f\<close> by simp
next
  show \<open>(\<Lambda> x. SKIP \<sqinter> STOP \<sqinter> (\<box>xa\<in>f ` A \<rightarrow> x))\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D 
        Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f\<close>
    if \<open>x \<sqsubseteq>\<^sub>F\<^sub>D Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f\<close> for x
    apply simp
    apply (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
    apply (simp add: Renaming_Ndet Renaming_STOP Renaming_SKIP)
    apply (rule mono_Ndet_FD[OF idem_FD])
    apply (subst Renaming_Mprefix)
    by (rule mono_Mprefix_FD[rule_format, OF that])
qed

lemma Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>Renaming (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A)\<close>
  if finitary: \<open>finitary f\<close>
proof (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, induct rule: fix_ind)
  show \<open>adm (\<lambda>a. Renaming a f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A))\<close>
    by (simp add: finitary monofun_def)
next
  show \<open>Renaming \<bottom> f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A)\<close> by (simp add: Renaming_BOT)
next
  show \<open>Renaming ((\<Lambda> x. SKIP \<sqinter> STOP \<sqinter> (\<box>xa\<in>A \<rightarrow> x))\<cdot>x) f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A)\<close>
    if \<open>Renaming x f \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P (f ` A)\<close> for x
    apply simp
    apply (simp add: Renaming_Ndet Renaming_STOP Renaming_SKIP)
    apply (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
    apply (subst Renaming_Mprefix)
    apply (rule mono_Ndet_FD[OF idem_FD])
    by (rule mono_Mprefix_FD[rule_format, OF that])
qed



subsection \<open>Corollaries on \<^const>\<open>deadlock_free\<close> and \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close>\<close>

lemmas Renaming_DF = 
       FD_antisym[OF Renaming_DF_FD_DF DF_FD_Renaming_DF]
   and Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P =
      FD_antisym[OF Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P]
   and Renaming_RUN =
       FD_antisym[OF Renaming_RUN_FD_RUN RUN_FD_Renaming_RUN]
   and Renaming_CHAOS =
       FD_antisym[OF Renaming_CHAOS_FD_CHAOS CHAOS_FD_Renaming_CHAOS]
   and Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P =
       FD_antisym[OF Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P
                     CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_Renaming_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P]
    


lemma deadlock_free_imp_deadlock_free_Renaming: \<open>deadlock_free (Renaming P f)\<close>
  if \<open>deadlock_free P\<close>
  apply (rule DF_Univ_freeness[of \<open>range f\<close>], simp)
  apply (rule trans_FD[OF DF_FD_Renaming_DF])
  apply (rule mono_Renaming_FD)
  by (rule that[unfolded deadlock_free_def])

lemma deadlock_free_Renaming_imp_deadlock_free: \<open>deadlock_free P\<close>
  if \<open>inj f\<close> and \<open>deadlock_free (Renaming P f)\<close>
  apply (subst Renaming_inv[OF that(1), symmetric])
  apply (rule deadlock_free_imp_deadlock_free_Renaming)
  by (rule that(2))

corollary deadlock_free_Renaming_iff:
  \<open>inj f \<Longrightarrow> deadlock_free (Renaming P f) \<longleftrightarrow> deadlock_free P\<close>
  using deadlock_free_Renaming_imp_deadlock_free
        deadlock_free_imp_deadlock_free_Renaming by blast



lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Renaming:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (Renaming P f)\<close> if \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P\<close>
  unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD
  apply (rule trans_FD[OF DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_subset_FD[of \<open>range f\<close>]], simp_all)
  apply (rule trans_FD[OF DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_Renaming_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P])
  by (rule mono_Renaming_FD[OF that[unfolded deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD]])
 
lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Renaming_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P\<close> if \<open>inj f\<close> and \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (Renaming P f)\<close>
  apply (subst Renaming_inv[OF that(1), symmetric])
  apply (rule deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Renaming)
  by (rule that(2))

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Renaming_iff:
  \<open>inj f \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (Renaming P f) \<longleftrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P\<close>
  using deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Renaming_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P
        deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_Renaming by blast







section \<open>Big Results\<close>

subsection \<open>Interesting Equivalence\<close>

lemma deadlock_free_of_Sync_iff_DF_FD_DF_Sync_DF:
  \<open>(\<forall>P Q. deadlock_free (P::'\<alpha> process) \<longrightarrow> deadlock_free Q \<longrightarrow>
          deadlock_free (P \<lbrakk>S\<rbrakk> Q))
   \<longleftrightarrow> (DF (UNIV::'\<alpha> set) \<sqsubseteq>\<^sub>F\<^sub>D (DF UNIV \<lbrakk>S\<rbrakk> DF UNIV))\<close> (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
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


subsection \<open>\<^const>\<open>STOP\<close> and \<^const>\<open>SKIP\<close> Synchronized with \<^term>\<open>DF A\<close>\<close>

lemma DF_FD_DF_Sync_STOP_or_SKIP_iff: 
  \<open>(DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P) \<longleftrightarrow> A \<inter> S = {}\<close>
  if P_disj: \<open>P = STOP \<or> P = SKIP\<close>
proof
  { assume a1: \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P\<close> and a2: \<open>A \<inter> S \<noteq> {}\<close>
    from a2 obtain x where f1: \<open>x \<in> A\<close> and f2: \<open>x \<in> S\<close> by blast
    have \<open>DF A \<lbrakk>S\<rbrakk> P \<sqsubseteq>\<^sub>F\<^sub>D DF {x} \<lbrakk>S\<rbrakk> P\<close>
      by (intro mono_Sync_FD[OF _ idem_FD]) (simp add: DF_subset f1)
    also have \<open>\<dots> = STOP\<close>
      apply (subst DF_unfold)
      using P_disj 
      apply (rule disjE; simp add: Mndetprefix_unit)
       apply (simp add: write0_def, subst Mprefix_STOP[symmetric],
              subst Mprefix_Sync_distr_right, (simp_all add: f2 Mprefix_STOP)[3])
      by (subst DF_unfold, simp add: Mndetprefix_unit f2 prefix_Sync_SKIP2)
      finally have False
        by (metis DF_Univ_freeness a1 empty_not_insert f1
                  insert_absorb non_deadlock_free_STOP trans_FD)
  }
  thus \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P \<Longrightarrow> A \<inter> S = {}\<close> by blast
next
  have D_P: \<open>\<D> P = {}\<close> using D_SKIP D_STOP P_disj by blast
  note F_T_P = F_STOP T_STOP F_SKIP D_SKIP
  { assume a1: \<open>\<not> DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P\<close> and a2: \<open>A \<inter> S = {}\<close>
    have False
    proof (cases \<open>A = {}\<close>)
      assume \<open>A = {}\<close>
      with a1[unfolded DF_def] show False
        by (simp add: fix_const)
           (metis Sync_SKIP_STOP Sync_STOP_STOP Sync_commute idem_FD that)
    next
      assume a3: \<open>A \<noteq> {}\<close>
      have falsify: \<open>(a, (X \<union> Y) \<inter> insert tick (ev ` S) \<union> X \<inter> Y) \<notin> \<F> (DF A) \<Longrightarrow>
                     (t, X) \<in> \<F> (DF A) \<Longrightarrow> (u, Y) \<in> \<F> P \<Longrightarrow> 
                     a setinterleaves ((t, u), insert tick (ev ` S)) \<Longrightarrow> False\<close> for a t u X Y
      proof (induct t arbitrary: a)
        case Nil
        show ?case by (rule disjE[OF P_disj], insert Nil a2)
                      (subst (asm) F_DF, auto simp add: a3 F_T_P)+
      next
        case (Cons x t)
        from Cons(4) have f1: \<open>u = []\<close>
          apply (subst disjE[OF P_disj], simp_all add: F_T_P) 
          by (metis Cons(2, 3, 5) F_T Sync.sym TickLeftSync empty_iff
                    ftf_Sync21 insertI1 nonTickFree_n_frontTickFree 
                    non_tickFree_tick process_charn tickFree_def tick_T_F)
        from Cons(2, 3) show False
          apply (subst (asm) (1 2) F_DF, auto simp add: a3)
          by (metis Cons.hyps Cons.prems(3, 4) Sync.sym SyncTlEmpty 
                    emptyLeftProperty f1 list.distinct(1) list.sel(1, 3))
      qed
      from a1 show False
        unfolding failure_divergence_refine_def le_ref_def
        by (auto simp add: F_Sync D_Sync D_P div_free_DF subset_iff intro: falsify)
    qed
  }
  thus \<open>A \<inter> S = {} \<Longrightarrow> DF A \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> P\<close> by blast
qed



lemma DF_Sync_STOP_or_SKIP_FD_DF: \<open>DF A \<lbrakk>S\<rbrakk> P \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close> 
  if P_disj: \<open>P = STOP \<or> P = SKIP\<close> and empty_inter: \<open>A \<inter> S = {}\<close>
proof (cases \<open>A = {}\<close>)
  from P_disj show \<open>A = {} \<Longrightarrow> DF A \<lbrakk>S\<rbrakk> P \<sqsubseteq>\<^sub>F\<^sub>D DF A\<close>
    by (rule disjE) (simp_all add: DF_def fix_const Sync_SKIP_STOP
                                   Sync_STOP_STOP Sync_commute)
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
      apply (rule trans_FD[OF mono_Sync_FD
                  [OF mono_Mndetprefix_FD_set
                      [of \<open>{a}\<close>, simplified, OF that] idem_FD]])
      apply (rule disjE[OF P_disj], simp_all add: Mndetprefix_unit)
       apply (subst Mprefix_Sync_distr_left
                    [of \<open>{a}\<close> _ \<open>{}\<close> \<open>\<lambda>a. x\<close>, 
                     simplified Mprefix_STOP, folded write0_def],
              (insert empty_inter that "3", auto)[3])
      by (subst prefix_Sync_SKIP1, (insert empty_inter that "3", auto)[2])
    thus ?case by (subst DF_unfold, subst FD_Mndetprefix_iff; simp add: \<open>A \<noteq> {}\<close>)
  qed
qed



lemmas DF_FD_DF_Sync_STOP_iff = 
       DF_FD_DF_Sync_STOP_or_SKIP_iff[of STOP, simplified]
   and DF_FD_DF_Sync_SKIP_iff =
       DF_FD_DF_Sync_STOP_or_SKIP_iff[of SKIP, simplified]
   and DF_Sync_STOP_FD_DF =
       DF_Sync_STOP_or_SKIP_FD_DF[of STOP, simplified]
   and DF_Sync_SKIP_FD_DF = 
       DF_Sync_STOP_or_SKIP_FD_DF[of SKIP, simplified]



subsection \<open>Finally, \<^term>\<open>deadlock_free (P ||| Q)\<close>\<close>

theorem DF_F_DF_Sync_DF: \<open>DF (A \<union> B::'\<alpha> set) \<sqsubseteq>\<^sub>F DF A \<lbrakk>S\<rbrakk> DF B\<close>
  if  nonempty: \<open>A \<noteq> {} \<and> B \<noteq> {}\<close>
 and intersect_hyp: \<open>B \<inter> S = {} \<or> (\<exists>y. B \<inter> S = {y} \<and> A \<inter> S \<subseteq> {y})\<close>
  unfolding failure_refine_def apply (simp add: F_Sync div_free_DF, safe)
proof -
  fix v t u X Y
  assume * : \<open>(t, X) \<in> \<F> (DF A)\<close> \<open>(u, Y) \<in> \<F> (DF B)\<close> 
             \<open>v setinterleaves ((t, u), insert tick (ev ` S))\<close>
  define \<beta> where \<open>\<beta> \<equiv> (t, insert tick (ev ` S), u)\<close>
  with * have \<open>(fst \<beta>, X) \<in> \<F> (DF A)\<close> \<open>(snd (snd \<beta>), Y) \<in> \<F> (DF B)\<close>
              \<open>v \<in> setinterleaving \<beta>\<close> by simp_all

  thus \<open>(v, (X \<union> Y) \<inter> insert tick (ev ` S) \<union> X \<inter> Y) \<in> \<F> (DF (A \<union> B))\<close>
    apply (subst F_DF, simp add: nonempty)
  proof (induct arbitrary: v rule: setinterleaving.induct)

    case (1 Z)
    hence mt_a: \<open>v = []\<close> using emptyLeftProperty by blast
    from intersect_hyp
    consider \<open>B \<inter> S = {}\<close> | \<open>\<exists>y. B \<inter> S = {y} \<and> A \<inter> S \<subseteq> {y}\<close> by blast
    thus ?case
    proof cases
      case 11: 1
      with "1"(2) show ?thesis by (subst (asm) F_DF)
                                  (auto simp add: nonempty mt_a)
    next
      case 12: 2
      then obtain y where f12: \<open>B \<inter> S = {y}\<close> and \<open>A \<inter> S \<subseteq> {y}\<close> by blast
      from this(2) consider \<open>A \<inter> S = {}\<close> | \<open>A \<inter> S = {y}\<close> by blast
      thus ?thesis
      proof cases
        case 121: 1
        with "1"(1) show ?thesis by (subst (asm) F_DF)
                                    (auto simp add: nonempty mt_a)
      next
        case 122: 2
        with "1"(1, 2) f12 nonempty mt_a mk_disjoint_insert show ?thesis
          by (subst (asm) (1 2) F_DF) (auto, fastforce)
      qed
    qed
  next

    case (2 Z y u)
    have * : \<open>y \<notin> Z\<close> \<open>([], X) \<in> \<F> (DF A)\<close> \<open>(u, Y) \<in> \<F> (DF B)\<close> \<open>v = y # u\<close>
      using "2.prems" Cons_F_DF by (auto simp add: emptyLeftProperty)
    have ** : \<open>u setinterleaves (([], u), Z)\<close>
      by (metis "*"(4) "2.prems"(3) SyncTlEmpty list.sel(3))
    from "2.prems"(2) obtain b where  *** : \<open>b \<in> B\<close> \<open>y = ev b\<close>
      by (subst (asm) F_DF, simp split: if_split_asm) blast
    show ?case
      apply (rule disjI2, rule_tac x = b in bexI)
      using "2.hyps"[simplified, OF *(1, 2, 3) **] 
      by (subst F_DF) (auto simp add: *(4) ***)
  next

    case (3 x t Z)
    have * : \<open>x \<notin> Z\<close> \<open>(t, X) \<in> \<F> (DF A)\<close> \<open>([], Y) \<in> \<F> (DF B)\<close> \<open>v = x # t\<close>
      using "3.prems" Cons_F_DF by (auto simp add: Sync.sym emptyLeftProperty)
    have ** : \<open>t setinterleaves ((t, []), Z)\<close>
      by (metis "*"(4) "3.prems"(3) Sync.sym SyncTlEmpty list.sel(3))
    from "3.prems"(1) obtain a where  *** : \<open>a \<in> A\<close> \<open>x = ev a\<close>
      by (subst (asm) F_DF, simp split: if_split_asm) blast
    show ?case
      apply (rule disjI1, rule_tac x = a in bexI)
      using "3.hyps"[simplified, OF *(1, 2, 3) **] 
      by (subst F_DF) (auto simp add: *(4) ***)
  next

    case (4 x t Z y u)
    consider \<open>x \<in> Z\<close> \<open>y \<in> Z\<close> | \<open>x \<in> Z\<close> \<open>y \<notin> Z\<close>
          |  \<open>x \<notin> Z\<close> \<open>y \<in> Z\<close> | \<open>x \<notin> Z\<close> \<open>y \<notin> Z\<close> by blast
    then show ?case
    proof (cases)
      assume hyps: \<open>x \<in> Z\<close> \<open>y \<in> Z\<close>
      obtain v' where * : \<open>x = y\<close> \<open>(t, X) \<in> \<F> (DF A)\<close>
                          \<open>(u, Y) \<in> \<F> (DF B)\<close> \<open>v = x # v'\<close>
        using "4.prems" Cons_F_DF by (simp add: hyps split: if_split_asm) blast
      have ** : \<open>v' setinterleaves ((t, u), Z)\<close>
        using "*"(1, 4) "4.prems"(3) hyps(1) by force
      from "4.prems"(1) obtain a where  *** : \<open>a \<in> A\<close> \<open>x = ev a\<close>
        by (subst (asm) F_DF, simp split: if_split_asm) blast
      show ?case
        apply (rule disjI1, rule_tac x = a in bexI)
        using "4.hyps"(1)[simplified, OF hyps(2) *(1, 2, 3) **] 
        by (subst F_DF) (auto simp add: *(4) ***)
    next
      assume hyps: \<open>x \<in> Z\<close> \<open>y \<notin> Z\<close>
      obtain v' where * : \<open>(x # t, X) \<in> \<F> (DF A)\<close> \<open>(u, Y) \<in> \<F> (DF B)\<close>
                          \<open>v = y # v'\<close> \<open>v' setinterleaves ((x # t, u), Z)\<close>
        using "4.prems" Cons_F_DF by (simp add: hyps split: if_split_asm) blast
      from "4.prems"(2) "4.hyps"(2)[simplified, OF hyps *(1, 2, 4)]
      show ?case by (subst (asm) F_DF, subst F_DF) 
                      (auto simp add: nonempty *(3))
    next
      assume hyps: \<open>x \<notin> Z\<close> \<open>y \<in> Z\<close>
      obtain v' where * : \<open>(t, X) \<in> \<F> (DF A)\<close> \<open>(y # u, Y) \<in> \<F> (DF B)\<close>
                          \<open>v = x # v'\<close> \<open>v' setinterleaves ((t, y # u), Z)\<close>
        using "4.prems" Cons_F_DF by (simp add: hyps split: if_split_asm) blast
      from "4.prems"(1) "4.hyps"(5)[simplified, OF hyps *(1, 2, 4)]
      show ?case by (subst (asm) F_DF, subst F_DF) 
                      (auto simp add: nonempty *(3))
    next
      assume hyps: \<open>x \<notin> Z\<close> \<open>y \<notin> Z\<close>
      note f4 = "4"[simplified, simplified hyps, simplified]
      from f4(8) obtain v' v''
        where \<open>v = x # v'  \<and> v'  setinterleaves ((t, y # u), Z) \<or> 
               v = y # v'' \<and> v'' setinterleaves ((x # t, u), Z)\<close>
              (is \<open>?left \<or> ?right\<close>) by blast
      then consider \<open>?left\<close> | \<open>?right\<close> by fast
      then show ?thesis 
      proof cases
        assume \<open>?left\<close>
        from f4(6) f4(3)[OF f4(6)[THEN Cons_F_DF] f4(7)
             \<open>?left\<close>[THEN conjunct2]]
        show ?thesis by (subst (asm) F_DF, subst F_DF)
                        (auto simp add:  \<open>?left\<close> nonempty)
      next
        assume \<open>?right\<close>
        from f4(7) f4(4)[OF f4(6) f4(7)[THEN Cons_F_DF] 
             \<open>?right\<close>[THEN conjunct2]]
        show ?thesis by (subst (asm) F_DF, subst F_DF)
                        (auto simp add: \<open>?right\<close> nonempty)
      qed
    qed
  qed
qed


lemma DF_FD_DF_Sync_DF:
  \<open>A \<noteq> {} \<and> B \<noteq> {} \<Longrightarrow> B \<inter> S = {} \<or> (\<exists>y. B \<inter> S = {y} \<and> A \<inter> S \<subseteq> {y}) \<Longrightarrow> 
   DF (A \<union> B) \<sqsubseteq>\<^sub>F\<^sub>D DF A \<lbrakk>S\<rbrakk> DF B\<close>
  unfolding failure_divergence_refine_def le_ref_def 
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
proof -
  { assume \<open>A \<noteq> {}\<close> and \<open>B \<noteq> {}\<close> and ?FD_ref and \<open>\<not> ?cases\<close>
    from \<open>\<not> ?cases\<close>[simplified] 
    obtain a and b where \<open>a \<in> A\<close> \<open>a \<in> S\<close> \<open>b \<in> B\<close> \<open>b \<in> S\<close> \<open>a \<noteq> b\<close> by blast
    have \<open>DF A \<lbrakk>S\<rbrakk> DF B \<sqsubseteq>\<^sub>F\<^sub>D (a \<rightarrow> DF A) \<lbrakk>S\<rbrakk> (b \<rightarrow> DF B)\<close>
      by (intro mono_Sync_FD; subst DF_unfold,
          subst Mndetprefix_unit[symmetric], simp add: \<open>a \<in> A\<close> \<open>b \<in> B\<close>)
    also have \<open>\<dots> = STOP\<close> by (simp add: \<open>a \<in> S\<close> \<open>a \<noteq> b\<close> \<open>b \<in> S\<close> prefix_Sync1)
    finally have False
      by (metis DF_Univ_freeness Un_empty \<open>A \<noteq> {}\<close>
                trans_FD[OF \<open>?FD_ref\<close>] non_deadlock_free_STOP)
  }
  thus ?thesis
    apply (cases \<open>A = {}\<close>, simp,
           metis DF_FD_DF_Sync_STOP_iff DF_unfold Sync_commute mt_Mndetprefix)
    apply (cases \<open>B = {}\<close>, simp,
           metis DF_FD_DF_Sync_STOP_iff DF_unfold Sync_commute mt_Mndetprefix)
    by (metis Sync_commute Un_commute DF_FD_DF_Sync_DF)
qed 

  



lemma
  \<open>(\<forall>a \<in> A. X a \<inter> S = {} \<or> (\<forall>b \<in> A. \<exists>y. X a \<inter> S = {y} \<and> X b \<inter> S \<subseteq> {y}))
   \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> A. \<exists>y. (X a \<union> X b) \<inter> S \<subseteq> {y})\<close>
 \<comment> \<open>this is the reason we write ugly\_hyp this way\<close>
  apply (subst Int_Un_distrib2, auto)
  by (metis subset_insertI) blast


lemma DF_FD_DF_MultiSync_DF:
  \<open>DF (\<Union> x \<in> (insert a A). X x) \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk> x \<in># mset_set (insert a A). DF (X x)\<close>
  if fin: \<open>finite A\<close> and nonempty: \<open>X a \<noteq> {}\<close> \<open>\<forall>b \<in> A. X b \<noteq> {}\<close>
 and ugly_hyp: \<open>\<forall>b \<in> A. X b \<inter> S = {} \<or> (\<exists>y. X b \<inter> S = {y} \<and> X a \<inter> S \<subseteq> {y})\<close>
               \<open>\<forall>b \<in> A. \<forall>c \<in> A. \<exists>y. (X b \<union> X c) \<inter> S \<subseteq> {y}\<close>
proof -
  have \<open>DF (\<Union> (X ` insert a A)) \<sqsubseteq>\<^sub>F\<^sub>D (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> x \<in># mset_set (insert a A). DF (X x)) \<and>
        (\<forall>b\<in>A. X b \<inter> S = {} \<or> (\<exists>y. X b \<inter> S = {y} \<and> \<Union> (X ` insert a A) \<inter> S \<subseteq> {y}))\<close>
  \<comment> \<open>We need to add this in our induction\<close>
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
            \<^bold>\<lbrakk>S\<^bold>\<rbrakk> a\<in>#mset_set (insert b (insert a A')).  DF (X a)\<close>
        apply (subst Un_commute)
        apply (rule trans_FD[OF DF_FD_DF_Sync_DF[where S = S]])
          apply (simp add: "2.hyps"(2) nonempty ugly_hyp(1))
        using "2.hyps"(2, 5) 
         apply blast
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
  thus ?thesis by (rule conjunct1)
qed



lemma DF_FD_DF_MultiSync_DF':
  \<open>\<lbrakk>finite A; \<forall>a \<in> A. X a \<noteq> {}; \<forall>a \<in> A. \<forall>b \<in> A. \<exists>y. (X a \<union> X b) \<inter> S \<subseteq> {y}\<rbrakk>
   \<Longrightarrow> DF (\<Union> a \<in> A. X a) \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># mset_set A. DF (X a)\<close>
  apply (cases A rule: finite.cases, assumption)
   apply (metis DF_unfold MultiSync_rec0 UN_empty idem_FD
                mset_set.empty mt_Mndetprefix)
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
  by (metis DF_FD_DF_Sync_STOP_iff DF_unfold Diff_disjoint Sync_SKIP_STOP
            Diff_insert_absorb Mndetprefix_unit Sync_STOP_STOP
            Sync_assoc UNIV_I insert_disjoint(2) prefix_Sync_SKIP2)
 

corollary DF_FD_DF_Inter_DF: \<open>DF (A::'\<alpha> set) \<sqsubseteq>\<^sub>F\<^sub>D DF A ||| DF A\<close>
  by (metis DF_FD_DF_Sync_DF_iff inf_bot_right sup.idem)

corollary DF_UNIV_FD_DF_UNIV_Inter_DF_UNIV:
  \<open>DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D DF UNIV ||| DF UNIV\<close>
  by (fact DF_FD_DF_Inter_DF)

corollary Inter_deadlock_free:
  \<open>deadlock_free P \<Longrightarrow> deadlock_free Q \<Longrightarrow> deadlock_free (P ||| Q)\<close>
  using DF_FD_DF_Inter_DF deadlock_free_of_Sync_iff_DF_FD_DF_Sync_DF by blast


theorem MultiInter_deadlock_free:
  \<open>M \<noteq> {#} \<Longrightarrow> \<forall>p \<in># M. deadlock_free (P p) \<Longrightarrow>
   deadlock_free (\<^bold>|\<^bold>|\<^bold>| p \<in># M. P p)\<close>
proof (induct rule: mset_induct_nonempty)
  case (m_singleton a)
  thus ?case by simp
next
  case (add x F)
  thus ?case using Inter_deadlock_free by auto
qed


end
