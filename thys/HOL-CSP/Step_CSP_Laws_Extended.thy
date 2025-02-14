(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Extension of the step laws
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


section\<open> Extension of the Step-Laws \<close>

(*<*)
theory Step_CSP_Laws_Extended                                               
  imports Basic_CSP_Laws Step_CSP_Laws Non_Deterministic_CSP_Distributivity
begin 
  (*>*)

subsection \<open>Derived step-laws for \<^const>\<open>Sync\<close>\<close>

lemma Mprefix_Inter_Mprefix :
  \<open>\<box>a\<in>A \<rightarrow> P a ||| \<box>b\<in>B \<rightarrow> Q b = (\<box>a\<in>A \<rightarrow> (P a ||| \<box>b\<in>B \<rightarrow> Q b)) \<box> (\<box>b\<in>B \<rightarrow> (\<box>a \<in> A \<rightarrow> P a ||| Q b))\<close>
  by (fact Mprefix_Sync_Mprefix[where S = \<open>{}\<close>, simplified])

lemma Mprefix_Par_Mprefix : \<open>\<box>a\<in>A \<rightarrow> P a || \<box>b\<in>B \<rightarrow> Q b = \<box>x\<in>(A \<inter> B) \<rightarrow> (P x || Q x)\<close>
  by (fact Mprefix_Sync_Mprefix[where S = \<open>UNIV\<close>, simplified])

lemma Mprefix_Sync_Mprefix_subset :
  \<open>\<lbrakk>A \<subseteq> S; B \<subseteq> S\<rbrakk> \<Longrightarrow> Mprefix A P \<lbrakk>S\<rbrakk> Mprefix B Q = \<box>x\<in>(A \<inter> B) \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x)\<close>
  by (fact Mprefix_Sync_Mprefix_bis[of \<open>{}\<close> S A \<open>{}\<close> B, simplified])

lemma Mprefix_Sync_Mprefix_indep :
  \<open>A \<inter> S = {} \<Longrightarrow> B \<inter> S = {} \<Longrightarrow>
   Mprefix A P \<lbrakk>S\<rbrakk> Mprefix B Q = (\<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> Mprefix B Q)) \<box> (\<box>b\<in>B \<rightarrow> (Mprefix A P \<lbrakk>S\<rbrakk> Q b))\<close>
  by (fact Mprefix_Sync_Mprefix_bis[of A S \<open>{}\<close> B \<open>{}\<close>, simplified])

lemma Mprefix_Sync_Mprefix_left :
  \<open>A \<inter> S = {} \<Longrightarrow> B \<subseteq> S \<Longrightarrow> Mprefix A P \<lbrakk>S\<rbrakk> Mprefix B Q = \<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> Mprefix B Q)\<close>
  by (fact Mprefix_Sync_Mprefix_bis[of A S \<open>{}\<close> \<open>{}\<close> B, simplified])

lemma Mprefix_Sync_Mprefix_right :
  \<open>A \<subseteq> S \<Longrightarrow> B \<inter> S = {} \<Longrightarrow> Mprefix A P \<lbrakk>S\<rbrakk> Mprefix B Q = \<box>b\<in>B \<rightarrow> (Mprefix A P \<lbrakk>S\<rbrakk> Q b)\<close>
  by (fact Mprefix_Sync_Mprefix_bis[of \<open>{}\<close> S A B \<open>{}\<close>, simplified])


lemma Mprefix_Sync_STOP : \<open>(\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> STOP = \<box>a \<in> (A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)\<close>
  by (subst Mprefix_empty[symmetric], subst Mprefix_Sync_Mprefix, simp)

lemma STOP_Sync_Mprefix : \<open>STOP \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b) = \<box>b \<in> (B - S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)\<close>
  by (metis (no_types, lifting) Mprefix_Sync_STOP Sync_commute mono_Mprefix_eq)




paragraph \<open>Mixing deterministic and non deterministic prefix choices\<close>

lemma Mndetprefix_Sync_Mprefix :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b)
    else \<sqinter>a\<in>A. (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b)))) \<box>
                (\<box>b\<in>(B - S) \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b)) \<box>
                (if a \<in> B \<inter> S then (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)) else STOP))\<close>
  by (unfold Mndetprefix_GlobalNdet Sync_distrib_GlobalNdet_right
      write0_def Mprefix_Sync_Mprefix)
    (auto simp add: Mprefix_singl insert_Diff_if Int_insert_left
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>] mono_Mprefix_eq)

lemma Mprefix_Sync_Mndetprefix :
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if B = {} then (\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> STOP
    else \<sqinter>b\<in>B. (if b \<in> S then STOP else (b \<rightarrow> ((\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b))) \<box>
                (\<box>a\<in>(A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> (b \<rightarrow> Q b))) \<box>
                (if b \<in> A \<inter> S then (b \<rightarrow> (P b \<lbrakk>S\<rbrakk> Q b)) else STOP))\<close>
  by (subst (1 2 3 4 5) Sync_commute) (simp add: Mndetprefix_Sync_Mprefix)


text \<open>In particular, we can obtain the theorem for \<^const>\<open>Mndetprefix\<close> synchronized with \<^const>\<open>STOP\<close>.\<close>

lemma Mndetprefix_Sync_STOP :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> STOP =
   (  if A \<inter> S = {} then \<sqinter>a \<in> A \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)
    else (\<sqinter>a \<in> (A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if A \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>)
proof -
  have \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> STOP =
        \<sqinter>a\<in>A. (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)))\<close> (is \<open>?lhs = ?rhs'\<close>)
    by (subst Mndetprefix_Sync_Mprefix[where B = \<open>{}\<close>, simplified])
      (auto intro: mono_GlobalNdet_eq)
  also have \<open>?rhs' = (if A \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>
  proof (split if_split, intro conjI impI)
    show \<open>A \<inter> S = {} \<Longrightarrow> ?rhs' = ?rhs1\<close>
      by (auto simp add: Mndetprefix_GlobalNdet intro!: mono_GlobalNdet_eq)
  next
    show \<open>?rhs' = ?rhs2 \<sqinter> STOP\<close> if \<open>A \<inter> S \<noteq> {}\<close>
    proof (cases \<open>A - S = {}\<close>)
      show \<open>?rhs' = ?rhs2 \<sqinter> STOP\<close> if \<open>A - S = {}\<close>
        by (simp add: \<open>A - S = {}\<close> GlobalNdet_is_STOP_iff)
          (use \<open>A - S = {}\<close> in blast)
    next
      show \<open>?rhs' = ?rhs2 \<sqinter> STOP\<close> if \<open>A - S \<noteq> {}\<close>
      proof (subst Int_Diff_Un[symmetric],
          subst GlobalNdet_factorization_union
          [OF \<open>A \<inter> S \<noteq> {}\<close> \<open>A - S \<noteq> {}\<close>, symmetric])
        have \<open>(\<sqinter>a\<in>(A \<inter> S). (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP))))
              = STOP\<close> (is \<open>?fact1 = STOP\<close>)
          by (simp add: GlobalNdet_is_STOP_iff)
        moreover have \<open>(\<sqinter>a\<in>(A - S). (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP))))
                       = ?rhs2\<close> (is \<open>?fact2 = ?rhs2\<close>)
          by (auto simp add: Mndetprefix_GlobalNdet intro: mono_GlobalNdet_eq)
        ultimately show \<open>?fact1 \<sqinter> ?fact2 = ?rhs2 \<sqinter> STOP\<close> by (simp add: Ndet_commute)
      qed
    qed
  qed
  finally show \<open>?lhs = (if A \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close> .
qed

corollary STOP_Sync_Mndetprefix :
  \<open>STOP \<lbrakk>S\<rbrakk> (\<sqinter>b \<in> B \<rightarrow> Q b)  =
   (  if B \<inter> S = {} then \<sqinter>b \<in> B \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)
    else (\<sqinter>b \<in> (B - S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)) \<sqinter> STOP)\<close>
  by (subst (1 2 3) Sync_commute) (simp add: Mndetprefix_Sync_STOP)

(* (  if A = {} then STOP \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b)
    else \<sqinter>a\<in>A. (if a \<in> B then (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)) else STOP)) *)

corollary Mndetprefix_Sync_Mprefix_subset :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A \<subseteq> B then \<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)
    else (\<sqinter>a \<in> (A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if A \<subseteq> B then ?rhs1 else ?rhs2)\<close>) if \<open>A \<subseteq> S\<close> \<open>B \<subseteq> S\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?lhs = (if A \<subseteq> B then ?rhs1 else ?rhs2)\<close>
    by (simp add: Mprefix_is_STOP_iff STOP_Sync_Mprefix \<open>B \<subseteq> S\<close>)
next
  from \<open>A \<subseteq> S\<close> have  * : \<open>a \<in> A \<Longrightarrow> a \<in> S\<close> for a by blast
  from \<open>B \<subseteq> S\<close> have ** : \<open>B - S = {}\<close> \<open>a \<in> B \<and> a \<in> S \<longleftrightarrow> a \<in> B\<close> for a by auto
  assume \<open>A \<noteq> {}\<close>
  have \<open>?lhs = \<sqinter>a\<in>A. (if a \<in> B then (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)) else STOP)\<close> (is \<open>?lhs = ?rhs'\<close>)
    by (auto simp add: Mndetprefix_Sync_Mprefix "*" "**" \<open>A \<noteq> {}\<close> intro: mono_GlobalNdet_eq)
  also have \<open>?rhs' = (if A \<subseteq> B then ?rhs1 else ?rhs2)\<close>
  proof (split if_split, intro conjI impI)
    show \<open>A \<subseteq> B \<Longrightarrow> ?rhs' = \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)\<close>
      by (auto simp add: Mndetprefix_GlobalNdet intro!: mono_GlobalNdet_eq)
  next
    show \<open>?rhs' = (\<sqinter>a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)) \<sqinter> STOP\<close> if \<open>\<not> A \<subseteq> B\<close>
    proof (cases \<open>A \<inter> B = {}\<close>)
      show \<open>A \<inter> B = {} \<Longrightarrow> ?rhs' = (\<sqinter>a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)) \<sqinter> STOP\<close>
        by (auto simp add: GlobalNdet_is_STOP_iff)
    next
      assume \<open>A \<inter> B \<noteq> {}\<close>
      from \<open>\<not> A \<subseteq> B\<close> have \<open>A - B \<noteq> {}\<close> by blast
      show \<open>?rhs' = (\<sqinter>a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)) \<sqinter> STOP\<close>
        by (auto simp add: Mndetprefix_GlobalNdet GlobalNdet_is_STOP_iff
            simp flip: GlobalNdet_factorization_union
            [OF \<open>A \<inter> B \<noteq> {}\<close> \<open>A - B \<noteq> {}\<close>, unfolded Int_Diff_Un]
            intro!: arg_cong2[where f = \<open>(\<sqinter>)\<close>] mono_GlobalNdet_eq)
    qed
  qed
  finally show \<open>?lhs = (if A \<subseteq> B then ?rhs1 else ?rhs2)\<close> by simp
qed


corollary Mprefix_Sync_Mndetprefix_subset :
  \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow>
   \<box>a \<in> A \<rightarrow> P a \<lbrakk>S\<rbrakk> \<sqinter>b \<in> B \<rightarrow> Q b =
   (  if B \<subseteq> A then \<sqinter>b \<in> B \<rightarrow> (P b \<lbrakk>S\<rbrakk> Q b)
    else (\<sqinter>b \<in> (A \<inter> B) \<rightarrow> (P b \<lbrakk>S\<rbrakk> Q b)) \<sqinter> STOP)\<close>
  by (subst (1 2 3) Sync_commute) (simp add: Mndetprefix_Sync_Mprefix_subset Int_commute)



corollary Mndetprefix_Sync_Mprefix_indep :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A = {} then \<box>b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)
    else \<sqinter>a\<in>A. (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b))) \<box>
                (\<box>b\<in>B \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b)))\<close>
  if \<open>A \<inter> S = {}\<close> and \<open>B \<inter> S = {}\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?thesis\<close>
    by (simp add: Diff_triv STOP_Sync_Mprefix \<open>B \<inter> S = {}\<close>)
next
  from that(1) have   * : \<open>a \<in> A \<Longrightarrow> a \<notin> S\<close> for a by blast
  from that(2) have  ** : \<open>a \<in> B \<and> a \<in> S \<longleftrightarrow> False\<close> for a by blast
  from that(2) have *** : \<open>B - S = B\<close> by blast
  show ?thesis if \<open>A \<noteq> {}\<close>
    by (simp add: Mndetprefix_Sync_Mprefix \<open>A \<noteq> {}\<close>)   
      (rule mono_GlobalNdet_eq, simp add: "*" "**" "***")
qed

corollary Mprefix_Sync_Mndetprefix_indep :
  \<open>A \<inter> S = {} \<Longrightarrow> B \<inter> S = {} \<Longrightarrow>
   (\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if B = {} then \<box>a \<in> A \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)
    else \<sqinter>b\<in>B. (b \<rightarrow> ((\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b)) \<box>
                (\<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> (b \<rightarrow> Q b))))\<close>
  by (subst (1 2 3 4) Sync_commute) (simp add: Mndetprefix_Sync_Mprefix_indep)


corollary Mndetprefix_Sync_Mprefix_left :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b)
    else \<sqinter>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b)))\<close>
  if \<open>A \<inter> S = {}\<close> and \<open>B \<subseteq> S\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?thesis\<close> by simp
next
  from that(1) have   * : \<open>a \<in> A \<Longrightarrow> a \<notin> S\<close> for a by blast
  from that(2) have  ** : \<open>B - S = {}\<close> by blast
  show ?thesis if \<open>A \<noteq> {}\<close>
    by (simp add: Mndetprefix_Sync_Mprefix \<open>A \<noteq> {}\<close>, unfold Mndetprefix_GlobalNdet)
      (rule mono_GlobalNdet_eq, simp add: "*" "**")
qed

corollary Mndetprefix_Sync_Mprefix_right :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk> (\<box>b \<in> B \<rightarrow> Q b)
    else \<box>b\<in>B \<rightarrow> ((\<sqinter>a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b))\<close>
  if \<open>A \<subseteq> S\<close> and \<open>B \<inter> S = {}\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?thesis\<close> by simp
next
  from that(1) have   * : \<open>a \<in> A \<Longrightarrow> a \<in> S\<close> for a by blast
  from that(2) have  ** : \<open>B - S = B\<close> by blast
  show ?thesis if \<open>A \<noteq> {}\<close>
    by (simp add: Mndetprefix_Sync_Mprefix \<open>A \<noteq> {}\<close>,
        simp add: Mndetprefix_GlobalNdet Sync_distrib_GlobalNdet_right \<open>A \<noteq> {}\<close>
        flip: GlobalNdet_Mprefix_distr)
      (rule mono_GlobalNdet_eq, use "*" "**" in auto)
qed


corollary Mprefix_Sync_Mndetprefix_left :
  \<open>A \<inter> S = {}  \<Longrightarrow> B \<subseteq> S \<Longrightarrow>
   (\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if B = {} then (\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> STOP
    else \<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> (\<sqinter>b \<in> B \<rightarrow> Q b)))\<close>
  by (subst (1 2 3) Sync_commute) (simp add: Mndetprefix_Sync_Mprefix_right)

corollary Mprefix_Sync_Mndetprefix_right :
  \<open>A \<subseteq> S \<Longrightarrow> B \<inter> S = {} \<Longrightarrow>
   (\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if B = {} then (\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> STOP
    else \<sqinter>b\<in>B \<rightarrow> ((\<box>a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b))\<close>
  by (subst (1 2 3) Sync_commute) (simp add: Mndetprefix_Sync_Mprefix_left)



corollary Mndetprefix_Par_Mprefix :
  \<open>\<sqinter>a \<in> A \<rightarrow> P a || \<box>b \<in> B \<rightarrow> Q b =
   (if A \<subseteq> B then \<sqinter>a \<in> A \<rightarrow> (P a || Q a) else (\<sqinter>a \<in> (A \<inter> B) \<rightarrow> (P a || Q a)) \<sqinter> STOP)\<close>
  by (simp add: Mndetprefix_Sync_Mprefix_subset)

corollary Mprefix_Par_Mndetprefix :
  \<open>\<box>a \<in> A \<rightarrow> P a || \<sqinter>b \<in> B \<rightarrow> Q b =
   (if B \<subseteq> A then \<sqinter>b \<in> B \<rightarrow> (P b || Q b) else (\<sqinter>b \<in> (A \<inter> B) \<rightarrow> (P b || Q b)) \<sqinter> STOP)\<close>
  by (simp add: Mprefix_Sync_Mndetprefix_subset)


corollary Mndetprefix_Inter_Mprefix :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) ||| (\<box>b \<in> B \<rightarrow> Q b) =
   (  if A = {} then (\<box>b \<in> B \<rightarrow> Q b \<^bold>; STOP)
    else \<sqinter>a\<in>A. (a \<rightarrow> (P a ||| (\<box>b \<in> B \<rightarrow> Q b))) \<box>
                (\<box>b\<in>B \<rightarrow> ((a \<rightarrow> P a) ||| Q b)))\<close>
  by (simp add: Mndetprefix_Sync_Mprefix_indep Mprefix_Seq)

corollary Mprefix_Inter_Mndetprefix :
  \<open>(\<box>a \<in> A \<rightarrow> P a) ||| (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if B = {} then (\<box>a \<in> A \<rightarrow> P a \<^bold>; STOP)
    else \<sqinter>b\<in>B. (b \<rightarrow> ((\<box>a \<in> A \<rightarrow> P a) ||| Q b)) \<box>
                (\<box>a\<in>A \<rightarrow> (P a ||| (b \<rightarrow> Q b))))\<close>
  by (simp add: Mprefix_Sync_Mndetprefix_indep Mprefix_Seq)



subsection \<open>Non deterministic step-laws\<close>

text \<open>The \<^const>\<open>Mndetprefix\<close> operator slightly differs
      from \<^const>\<open>Mprefix\<close> so we can often adapt the step-laws.\<close>

lemma Mndetprefix_Ndet_Mndetprefix :
  \<comment> \<open>We assume \<^term>\<open>A \<inter> B \<noteq> {}\<close>, otherwise this rewriting rule is not interesting.\<close>
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<sqinter> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (  if A = B then \<sqinter>b \<in> B \<rightarrow> P b \<sqinter> Q b
    else   if A \<subseteq> B then (\<sqinter>b \<in> (B - A) \<rightarrow> Q b) \<sqinter> (\<sqinter>x \<in> A \<rightarrow> P x \<sqinter> Q x)
         else   if B \<subseteq> A then (\<sqinter>a \<in> (A - B) \<rightarrow> P a) \<sqinter> (\<sqinter>x \<in> B \<rightarrow> P x \<sqinter> Q x)
              else (\<sqinter>a \<in> (A - B) \<rightarrow> P a) \<sqinter> (\<sqinter>b \<in> (B - A) \<rightarrow> Q b) \<sqinter> (\<sqinter>x \<in> (A \<inter> B) \<rightarrow> P x \<sqinter> Q x))\<close>
  (is \<open>?lhs = (if A = B then ?rhs1 else if A \<subseteq> B then ?rhs2 else if B \<subseteq> A then ?rhs3 else ?rhs4)\<close>)
  if \<open>A \<inter> B \<noteq> {}\<close>
proof (split if_split, intro conjI impI)
  show \<open>A = B \<Longrightarrow> ?lhs = ?rhs1\<close> by (simp add: Mndetprefix_distrib_Ndet)
next
  show \<open>?lhs = (if A \<subseteq> B then ?rhs2 else if B \<subseteq> A then ?rhs3 else ?rhs4)\<close> if \<open>A \<noteq> B\<close>
  proof (split if_split, intro conjI impI)
    from \<open>A \<inter> B \<noteq> {}\<close> \<open>A \<noteq> B\<close> show \<open>A \<subseteq> B \<Longrightarrow> ?lhs = ?rhs2\<close>
      by (simp add: Process_eq_spec Ndet_projs STOP_projs Mndetprefix_projs, safe, auto)
  next
    show \<open>?lhs = (if B \<subseteq> A then ?rhs3 else ?rhs4)\<close> if \<open>\<not> A \<subseteq> B\<close>
    proof (split if_split, intro conjI impI)
      from \<open>A \<noteq> B\<close> show \<open>B \<subseteq> A \<Longrightarrow> ?lhs = ?rhs3\<close>
        by (simp add: Process_eq_spec Ndet_projs STOP_projs Mndetprefix_projs, safe, auto)
    next
      from \<open>A \<inter> B \<noteq> {}\<close> \<open>\<not> A \<subseteq> B\<close> show \<open>\<not> B \<subseteq> A \<Longrightarrow> ?lhs = ?rhs4\<close>
        by (simp add: Process_eq_spec Ndet_projs STOP_projs Mndetprefix_projs, safe, auto)
    qed
  qed
qed

lemma Mndetprefix_Det_Mndetprefix :
  \<open>(\<sqinter>a\<in> A \<rightarrow> P a) \<box> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   (if A = {} then \<sqinter>b \<in> B \<rightarrow> Q b else if B = {} then \<sqinter>a \<in> A \<rightarrow> P a
    else \<sqinter>a \<in> A. \<sqinter>b \<in> B. (if a = b then a \<rightarrow> P a \<sqinter> Q a else (a \<rightarrow> P a) \<box> (b \<rightarrow> Q b)))\<close>
  (is \<open>?lhs = (if A = {} then ?rhs1 else if B = {} then ?rhs2 else ?rhs3)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs = ?rhs1\<close> by simp
next
  show \<open>?lhs = (if B = {} then ?rhs2 else ?rhs3)\<close> if \<open>A \<noteq> {}\<close>
  proof (split if_split, intro conjI impI)
    show \<open>B = {} \<Longrightarrow> ?lhs = ?rhs2\<close> by simp
  next
    from \<open>A \<noteq> {}\<close> show \<open>B \<noteq> {} \<Longrightarrow> ?lhs = ?rhs3\<close>
      by (auto simp add: Mndetprefix_GlobalNdet Det_distrib_GlobalNdet_left
          Det_distrib_GlobalNdet_right GlobalNdet_sets_commute[of A]
          intro!: mono_GlobalNdet_eq split: if_split_asm)
        (simp add: Process_eq_spec Det_projs write0_def Mprefix_projs Ndet_projs, safe, auto)
  qed
qed

lemma FD_Mndetprefix_Det_Mndetprefix : 
  \<open>\<sqinter>x\<in>(A \<union> B) \<rightarrow> (if x \<in> A \<inter> B then P x \<sqinter> Q x else if x \<in> A then P x else Q x)
   \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter>a\<in> A \<rightarrow> P a) \<box> (\<sqinter>b \<in> B \<rightarrow> Q b)\<close>
  (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (rule failure_divergence_refineI)
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Det D_Ndet D_Mndetprefix')
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s) (auto simp add: F_Det F_Ndet Mndetprefix_projs split: if_split_asm)
qed



lemma FD_Mndetprefix_Sliding_Mndetprefix :
  \<open>(\<sqinter>x \<in> (A \<union> B) \<rightarrow> (if x \<in> A \<inter> B then P x \<sqinter> Q x else if x \<in> A then P x else Q x)) \<sqinter>
   (\<sqinter>b \<in> B \<rightarrow> (if b \<in> A then P b \<sqinter> Q b else Q b)) \<sqsubseteq>\<^sub>F\<^sub>D
   (\<sqinter>a\<in> A \<rightarrow> P a) \<rhd> (\<sqinter>b \<in> B \<rightarrow> Q b)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (rule failure_divergence_refineI)
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Sliding D_Ndet D_Mndetprefix')
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s) (auto simp add: F_Sliding F_Ndet Mndetprefix_projs split: if_split_asm)
qed


lemma Mndetprefix_Sliding_superset_Mndetprefix :
  \<open>(\<sqinter>a\<in> A \<rightarrow> P a) \<rhd> (\<sqinter>b \<in> B \<rightarrow> Q b) =
   \<sqinter>b \<in> B \<rightarrow> (if b \<in> A then P b \<sqinter> Q b else Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>A \<subseteq> B\<close>
proof (subst Process_eq_spec, safe)
  from \<open>A \<subseteq> B\<close> show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: D_Sliding D_Ndet D_Mndetprefix')
next
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Sliding D_Ndet D_Mndetprefix' split: if_split_asm)
next
  from \<open>A \<subseteq> B\<close> show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s) (auto simp add: F_Sliding F_Ndet Mndetprefix_projs split: if_split_asm)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s) (auto simp add: F_Sliding F_Ndet Mndetprefix_projs split: if_split_asm)
qed

corollary Mndetprefix_Sliding_same_set_Mndetprefix :
  \<open>(\<sqinter>a\<in> A \<rightarrow> P a) \<rhd> (\<sqinter>a \<in> A \<rightarrow> Q a) = \<sqinter>a \<in> A \<rightarrow> P a \<sqinter> Q a\<close>
  by (simp add: Mndetprefix_Sliding_superset_Mndetprefix)
    (rule mono_Mndetprefix_eq, simp)





lemma Renaming_Mndetprefix :
  \<open>Renaming (\<sqinter>a \<in> A \<rightarrow> P a) f g = \<sqinter>b \<in> f ` A \<rightarrow> \<sqinter>a \<in> {a \<in> A. b = f a}. Renaming (P a) f g\<close>
proof -
  have * : \<open>A = (\<Union>b \<in> f ` A. {a \<in> A. b = f a})\<close> by auto
  have ** : \<open>{b \<in> f ` A. {a \<in> A. b = f a} \<noteq> {}} = f ` A\<close> by auto
  have \<open>Renaming (\<sqinter>a \<in> A \<rightarrow> P a) f g = \<sqinter>a \<in> A. (f a \<rightarrow> Renaming (P a) f g)\<close>
    by (auto simp add: Mndetprefix_GlobalNdet Renaming_distrib_GlobalNdet write0_def Renaming_Mprefix
        intro!: mono_GlobalNdet_eq mono_Mprefix_eq)
  also have \<open>\<dots> = \<sqinter>b \<in> f ` A. \<sqinter>a \<in> {a \<in> A. b = f a}. (f a \<rightarrow> Renaming (P a) f g)\<close>
    by (subst "*", subst GlobalNdet_Union, subst "**", fact refl)
  also have \<open>\<dots> = \<sqinter>b \<in> f ` A. (b \<rightarrow> (\<sqinter>a \<in> {a \<in> A. b = f a}. Renaming (P a) f g))\<close>
    by (rule mono_GlobalNdet_eq, subst write0_GlobalNdet)
      (auto intro: mono_GlobalNdet_eq)
  also have \<open>\<dots> = \<sqinter>b \<in> f ` A \<rightarrow> \<sqinter>a \<in> {a \<in> A. b = f a}. Renaming (P a) f g\<close>
    by (simp add: Mndetprefix_GlobalNdet)
  finally show \<open>Renaming (\<sqinter>a \<in> A \<rightarrow> P a) f g = \<dots>\<close> .
qed


lemma Mndetprefix_Seq : \<open>\<sqinter>a \<in> A \<rightarrow> P a \<^bold>; Q = \<sqinter>a \<in> A \<rightarrow> (P a \<^bold>; Q)\<close>
  by (simp add: Mndetprefix_GlobalNdet Seq_distrib_GlobalNdet_right)
    (rule mono_GlobalNdet_eq, simp add: write0_def Mprefix_Seq)



text \<open>For \<^const>\<open>Hiding\<close>, we can not use the distributivity of
      \<^const>\<open>GlobalNdet\<close> since it is only working for finite non determinism.
      But we can still reuse some previous results in the following proof.\<close>

theorem Hiding_Mndetprefix_disjoint : 
  \<open>\<sqinter>a \<in> A \<rightarrow> P a \ S = \<sqinter>a \<in> A \<rightarrow> (P a \ S)\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>A \<inter> S = {}\<close>
proof (subst Process_eq_spec_optimized, safe)
  have \<open>\<D> ?lhs = \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
    by (simp add: D_Hiding_seqRun Mndetprefix_projs Mprefix_projs)
  also have \<open>\<dots> = \<D> (\<box>a \<in> A \<rightarrow> (P a \ S))\<close> 
    by (simp add: Hiding_Mprefix_disjoint \<open>A \<inter> S = {}\<close>)
  also have \<open>\<dots> = \<D> ?rhs\<close>
    by (simp add: D_Mndetprefix' D_Mprefix)
  finally show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s by simp_all
next
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  fix s X assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | t where \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (\<sqinter>a \<in> A \<rightarrow> P a)\<close>
    unfolding F_Hiding_seqRun D_Hiding_seqRun by blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    fix t assume * : \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (\<sqinter>a \<in> A \<rightarrow> P a)\<close>
    show \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof (cases \<open>t = []\<close>)
      from "*" show \<open>t = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Mndetprefix' split: if_split_asm)
    next
      assume \<open>t \<noteq> []\<close>
      with "*"(2) have \<open>(t, X \<union> ev ` S) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close>
        by (simp add: F_Mprefix F_Mndetprefix' split: if_split_asm)
      with "*"(1) have \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
        unfolding F_Hiding by blast
      hence \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> (P a \ S))\<close>
        by (simp add: Hiding_Mprefix_disjoint \<open>A \<inter> S = {}\<close>)
      thus \<open>(s, X) \<in> \<F> ?rhs\<close> by (auto simp add: F_Mprefix F_Mndetprefix')
    qed
  qed
next
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>    
  show \<open>(s, X) \<in> \<F> ?lhs\<close> if \<open>(s, X) \<in> \<F> ?rhs\<close> for s X
  proof (cases \<open>s = []\<close>)
    assume \<open>s = []\<close>
    with \<open>(s, X) \<in> \<F> ?rhs\<close> have \<open>A = {} \<or> (\<exists>a \<in> A. ev a \<notin> X)\<close>
      by (simp add: F_Mndetprefix' split: if_split_asm)
    with \<open>A \<inter> S = {}\<close> show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: Mndetprefix_projs F_Hiding_seqRun disjoint_iff)
        (metis (no_types, lifting) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) filter.simps(1) imageE)
  next
    assume \<open>s \<noteq> []\<close>
    with \<open>(s, X) \<in> \<F> ?rhs\<close> have \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> (P a \ S))\<close>
      by (simp add: F_Mprefix F_Mndetprefix' split: if_split_asm)
    hence \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      by (simp add: Hiding_Mprefix_disjoint \<open>A \<inter> S = {}\<close>)
    then consider \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      | t where \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close>
      unfolding F_Hiding_seqRun D_Hiding_seqRun by blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      hence \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Hiding_seqRun Mprefix_projs Mndetprefix_projs)
      with D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
    next
      fix t assume * : \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close>
      from \<open>s \<noteq> []\<close> "*"(1) filter.simps(1) have \<open>t \<noteq> []\<close> by blast
      with "*" show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Hiding F_Mprefix F_Mndetprefix') blast
    qed
  qed
qed

theorem Hiding_Mndetprefix_subset : 
  \<open>\<sqinter>a \<in> A \<rightarrow> P a \ S = \<sqinter>a \<in> A. (P a \ S)\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>A \<subseteq> S\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> ?lhs = ?rhs\<close> by simp
next
  assume \<open>A \<noteq> {}\<close>
  hence \<open>A \<inter> S \<noteq> {}\<close> by (simp add: inf_absorb1 \<open>A \<subseteq> S\<close>)
  show \<open>?lhs = ?rhs\<close>
  proof (subst Process_eq_spec_optimized, safe)
    have \<open>\<D> ?lhs = \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      by (simp add: D_Hiding_seqRun Mndetprefix_projs Mprefix_projs)
    also have \<open>\<dots> = \<D> ((\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) \<rhd> (\<sqinter>a \<in> (A \<inter> S). (P a \ S)))\<close> 
      by (simp add: Hiding_Mprefix_non_disjoint \<open>A \<inter> S \<noteq> {}\<close>)
    also have \<open>\<dots> = \<D> ?rhs\<close>
      by (use \<open>A \<subseteq> S\<close> in \<open>auto simp add: D_GlobalNdet D_Mprefix D_Sliding\<close>)
    finally show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
      and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s by simp_all
  next
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    fix s X assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>s \<in> \<D> ?lhs\<close>
      | t where \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (\<sqinter>a \<in> A \<rightarrow> P a)\<close>
      unfolding F_Hiding D_Hiding by blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
    next
      fix t assume * : \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (\<sqinter>a \<in> A \<rightarrow> P a)\<close>
      from "*"(2) \<open>A \<subseteq> S\<close> obtain a t' where \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>(t', X \<union> ev ` S) \<in> \<F> (P a)\<close>
        by (auto simp add: F_Mndetprefix' \<open>A \<noteq> {}\<close> subset_iff)
      hence \<open>(t, X \<union> ev ` S) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close> by (simp add: F_Mprefix)
      with "*"(1) have \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
        by (auto simp add: F_Hiding_seqRun)
      hence \<open>(s, X) \<in> \<F> ((\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) \<rhd> (\<sqinter>a \<in> (A \<inter> S). (P a \ S)))\<close> 
        by (simp add: Hiding_Mprefix_non_disjoint \<open>A \<inter> S \<noteq> {}\<close>)
      also have \<open>(\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) = STOP\<close>
        by (simp add: Mprefix_is_STOP_iff \<open>A \<subseteq> S\<close>)
      also from \<open>A \<subseteq> S\<close> have \<open>A \<inter> S = A\<close> by blast
      finally show \<open>(s, X) \<in> \<F> (\<sqinter>a \<in> A. (P a \ S))\<close> by simp
    qed
  next
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    fix s X assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    then obtain a where \<open>a \<in> A\<close> \<open>(s, X) \<in> \<F> (P a \ S)\<close>
      by (auto simp add: F_GlobalNdet \<open>A \<noteq> {}\<close>)
    from \<open>(s, X) \<in> \<F> (P a \ S)\<close> consider \<open>s \<in> \<D> (P a \ S)\<close>
      | t where \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
      unfolding F_Hiding D_Hiding by blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>s \<in> \<D> (P a \ S)\<close>
      with \<open>a \<in> A\<close> have \<open>s \<in> \<D> ?rhs\<close> by (auto simp add: D_GlobalNdet)
      with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
    next
      from \<open>a \<in> A\<close> \<open>A \<subseteq> S\<close>
      show \<open>s = trace_hide t (ev ` S) \<Longrightarrow> (t, X \<union> ev ` S) \<in> \<F> (P a)
            \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for t
        by (simp add: F_Hiding F_Mndetprefix' \<open>A \<noteq> {}\<close> subset_iff)
          (metis (no_types, lifting) filter.simps(2) image_eqI)
    qed
  qed
qed

theorem Hiding_Mndetprefix_non_disjoint_not_subset :
  \<open>\<sqinter>a \<in> A \<rightarrow> P a \ S = (\<sqinter>a \<in> (A - S) \<rightarrow> (P a \ S)) \<sqinter> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close>
  (is \<open>?lhs = ?rhs1 \<sqinter> ?rhs2\<close>) if \<open>A \<inter> S \<noteq> {}\<close> and \<open>\<not> A \<subseteq> S\<close>
proof -
  from \<open>\<not> A \<subseteq> S\<close> have \<open>A - S \<noteq> {}\<close> by blast
  moreover have \<open>A - S \<union> A \<inter> S = A\<close> by blast
  ultimately have \<open>(\<sqinter>a \<in> A \<rightarrow> P a) = (\<sqinter>a \<in> (A - S) \<rightarrow> P a) \<sqinter> (\<sqinter>a \<in> (A \<inter> S) \<rightarrow> P a)\<close>
    by (metis Mndetprefix_Un_distrib \<open>A \<inter> S \<noteq> {}\<close>)
  hence \<open>?lhs = (\<sqinter>a \<in> (A - S) \<rightarrow> P a \ S) \<sqinter> (\<sqinter>a \<in> (A \<inter> S) \<rightarrow> P a \ S)\<close>
    by (simp add: Hiding_distrib_Ndet)
  also have \<open>\<sqinter>a \<in> (A - S) \<rightarrow> P a \ S = ?rhs1\<close>
    by (simp add: Hiding_Mndetprefix_disjoint inf.commute)
  also have \<open>\<sqinter>a \<in> (A \<inter> S) \<rightarrow> P a \ S = ?rhs2\<close>
    by (simp add: Hiding_Mndetprefix_subset)
  finally show \<open>?lhs = ?rhs1 \<sqinter> ?rhs2\<close> .
qed


(*<*)
end
  (*>*)