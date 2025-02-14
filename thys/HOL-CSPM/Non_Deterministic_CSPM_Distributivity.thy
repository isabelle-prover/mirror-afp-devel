(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Distributivity of non determinism
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


(*<*)
theory Non_Deterministic_CSPM_Distributivity
  imports Global_Deterministic_Choice Multi_Synchronization_Product
    Multi_Sequential_Composition Interrupt Throw
begin
  (*>*)

subsection \<open>The Throw Operator\<close>

lemma Throw_distrib_Ndet_right :
  \<open>P \<sqinter> P' \<Theta> a \<in> A. Q a = (P \<Theta> a \<in> A. Q a) \<sqinter> (P' \<Theta> a \<in> A. Q a)\<close>
  and Throw_distrib_Ndet_left :
  \<open>P \<Theta> a \<in> A. Q a \<sqinter> Q' a = (P \<Theta> a \<in> A. Q a) \<sqinter> (P \<Theta> a \<in> A. Q' a)\<close>
  by (simp add: Process_eq_spec F_Throw F_Ndet D_Throw D_Ndet T_Ndet,
      safe, simp_all; blast)+


lemma Throw_distrib_GlobalNdet_right :
  \<open>(\<sqinter>a \<in> A. P a) \<Theta> b \<in> B. Q b = \<sqinter>a \<in> A. (P a \<Theta> b \<in> B. Q b)\<close>
  and Throw_distrib_GlobalNdet_left :
  \<open>P' \<Theta> a \<in> A. (\<sqinter>b \<in> B. Q' a b) = 
   (if B = {} then P' \<Theta> a \<in> A. STOP else \<sqinter>b \<in> B. (P' \<Theta> a \<in> A. Q' a b))\<close>                
  by (simp add: Process_eq_spec Throw_projs GlobalNdet_projs, safe, simp_all; blast)
    (simp add: Process_eq_spec Throw_projs GlobalNdet_projs STOP_projs; blast)



subsection \<open>The Interrupt Operator\<close>

lemma Interrupt_distrib_GlobalNdet_left :
  \<open>P \<triangle> (\<sqinter>a \<in> A. Q a) = (if A = {} then P else \<sqinter>a \<in> A. P \<triangle> Q a)\<close>
  (is \<open>?lhs = (if _ then _ else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs = P\<close> by simp
next
  show \<open>?lhs = ?rhs\<close> if \<open>A \<noteq> {}\<close>
  proof (rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (auto simp add: \<open>A \<noteq> {}\<close> D_Interrupt D_GlobalNdet)
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (auto simp add: \<open>A \<noteq> {}\<close> D_Interrupt D_GlobalNdet)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    with \<open>A \<noteq> {}\<close> consider r u where \<open>t = u @ [\<checkmark>(r)]\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
      | r where \<open>\<checkmark>(r) \<notin> X\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close>
      | a where \<open>a \<in> A\<close> \<open>(t, X) \<in> \<F> P\<close> \<open>tF t\<close> \<open>([], X) \<in> \<F> (Q a)\<close>
      | a u v where \<open>a \<in> A\<close> \<open>t = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close> \<open>(v, X) \<in> \<F> (Q a)\<close> \<open>v \<noteq> []\<close>
      | a r where \<open>a \<in> A\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>t \<in> \<T> P\<close> \<open>tF t\<close> \<open>[\<checkmark>(r)] \<in> \<T> (Q a)\<close>
      unfolding Interrupt_projs GlobalNdet_projs by force
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      from \<open>A \<noteq> {}\<close> show \<open>t = u @ [\<checkmark>(r)] \<Longrightarrow> u @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for r u
        by (auto simp add: F_GlobalNdet F_Interrupt)
    next
      show \<open>\<checkmark>(r) \<notin> X \<Longrightarrow> t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for r
        by (simp add: F_GlobalNdet F_Interrupt)
          (metis Diff_insert_absorb all_not_in_conv \<open>A \<noteq> {}\<close>)
    next
      show \<open>a \<in> A \<Longrightarrow> (t, X) \<in> \<F> P \<Longrightarrow> tF t \<Longrightarrow> ([], X) \<in> \<F> (Q a) \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for a
        by (auto simp add: F_GlobalNdet F_Interrupt)
    next
      show \<open>\<lbrakk>a \<in> A; t = u @ v; u \<in> \<T> P; tF u; (v, X) \<in> \<F> (Q a); v \<noteq> []\<rbrakk>
            \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for a u v by (auto simp add: F_GlobalNdet F_Interrupt)
    next
      show \<open>\<lbrakk>a \<in> A; \<checkmark>(r) \<notin> X; t \<in> \<T> P; tF t; [\<checkmark>(r)] \<in> \<T> (Q a)\<rbrakk> \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for a r
        by (simp add: F_GlobalNdet F_Interrupt) (metis Diff_insert_absorb \<open>A \<noteq> {}\<close>)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    from \<open>(t, X) \<in> \<F> ?rhs\<close> obtain a where \<open>a \<in> A\<close> \<open>(t, X) \<in> \<F> (P \<triangle> Q a)\<close>
      by (auto simp add: \<open>A \<noteq> {}\<close> F_GlobalNdet)
    with \<open>t \<notin> \<D> ?rhs\<close> consider u r where \<open>t = u @ [\<checkmark>(r)]\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
      | r where \<open>\<checkmark>(r) \<notin> X\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close>
      | \<open>(t, X) \<in> \<F> P\<close> \<open>tF t\<close> \<open>([], X) \<in> \<F> (Q a)\<close>
      | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close> \<open>(v, X) \<in> \<F> (Q a)\<close> \<open>v \<noteq> []\<close>
      | r where \<open>\<checkmark>(r) \<notin> X\<close> \<open>t \<in> \<T> P\<close> \<open>tF t\<close> \<open>[\<checkmark>(r)] \<in> \<T> (Q a)\<close>
      unfolding D_GlobalNdet Interrupt_projs by blast
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      show \<open>t = u @ [\<checkmark>(r)] \<Longrightarrow> u @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u r
        by (simp add: F_Interrupt)
    next
      show \<open>\<checkmark>(r) \<notin> X \<Longrightarrow> t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for r
        by (auto simp add: F_Interrupt)
    next
      from \<open>a \<in> A\<close> show \<open>\<lbrakk>(t, X) \<in> \<F> P; tF t; ([], X) \<in> \<F> (Q a)\<rbrakk> \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close>
        by (auto simp add: F_Interrupt F_GlobalNdet)
    next
      from \<open>a \<in> A\<close> show \<open>\<lbrakk>t = u @ v; u \<in> \<T> P; tF u; (v, X) \<in> \<F> (Q a); v \<noteq> []\<rbrakk> \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u v
        by (simp add: \<open>A \<noteq> {}\<close> F_Interrupt F_GlobalNdet) blast
    next
      from \<open>a \<in> A\<close> show \<open>\<lbrakk>\<checkmark>(r) \<notin> X; t \<in> \<T> P; tF t; [\<checkmark>(r)] \<in> \<T> (Q a)\<rbrakk> \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for r
        by (simp add: F_Interrupt GlobalNdet_projs) blast
    qed
  qed
qed


lemma Interrupt_distrib_GlobalNdet_right :
  \<open>(\<sqinter>a \<in> A. P a) \<triangle> Q = (if A = {} then Q else \<sqinter>a \<in> A. P a \<triangle> Q)\<close>
  (is \<open>?lhs = (if _ then _ else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs = Q\<close> by simp
next
  show \<open>?lhs = ?rhs\<close> if \<open>A \<noteq> {}\<close>
  proof (rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (simp add: GlobalNdet_projs D_Interrupt)
        (metis ex_in_conv is_processT1_TR \<open>A \<noteq> {}\<close>)
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (auto simp add: GlobalNdet_projs D_Interrupt)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then consider u r where \<open>t = u @ [\<checkmark>(r)]\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (\<sqinter>a \<in> A. P a)\<close>
      | r where \<open>\<checkmark>(r) \<notin> X\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> (\<sqinter>a \<in> A. P a)\<close>
      | \<open>(t, X) \<in> \<F> (\<sqinter>a \<in> A. P a)\<close> \<open>tF t\<close> \<open>([], X) \<in> \<F> Q\<close>
      | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> (\<sqinter>a \<in> A. P a)\<close> \<open>tF u\<close> \<open>(v, X) \<in> \<F> Q\<close> \<open>v \<noteq> []\<close>
      | r where \<open>\<checkmark>(r) \<notin> X\<close> \<open>t \<in> \<T> (\<sqinter>a \<in> A. P a)\<close> \<open>tF t\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q\<close>
      unfolding Interrupt_projs by blast
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      show \<open>t = u @ [\<checkmark>(r)] \<Longrightarrow> u @ [\<checkmark>(r)] \<in> \<T> (\<sqinter>a \<in> A. P a) \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for u r
        by (auto simp add: \<open>A \<noteq> {}\<close> GlobalNdet_projs F_Interrupt)
    next
      show \<open>\<checkmark>(r) \<notin> X \<Longrightarrow> t @ [\<checkmark>(r)] \<in> \<T> (\<sqinter>a \<in> A. P a) \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for r
        by (simp add: \<open>A \<noteq> {}\<close> GlobalNdet_projs F_Interrupt) (metis Diff_insert_absorb)
    next
      show \<open>(t, X) \<in> \<F> (\<sqinter>a \<in> A. P a) \<Longrightarrow> tF t \<Longrightarrow> ([], X) \<in> \<F> Q \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: \<open>A \<noteq> {}\<close> F_GlobalNdet F_Interrupt)
    next
      show \<open>\<lbrakk>t = u @ v; u \<in> \<T> (\<sqinter>a \<in> A. P a); tF u; (v, X) \<in> \<F> Q; v \<noteq> []\<rbrakk>
            \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for u v
        by (simp add: \<open>A \<noteq> {}\<close> GlobalNdet_projs F_Interrupt)
          (metis ex_in_conv is_processT1_TR \<open>A \<noteq> {}\<close>)
    next
      show \<open>\<checkmark>(r) \<notin> X \<Longrightarrow> t \<in> \<T> (\<sqinter>a \<in> A. P a) \<Longrightarrow> tF t \<Longrightarrow> [\<checkmark>(r)] \<in> \<T> Q \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for r
        by (simp add: \<open>A \<noteq> {}\<close> GlobalNdet_projs F_Interrupt)
          (metis Diff_insert_absorb equals0I is_processT1_TR \<open>A \<noteq> {}\<close>)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    from \<open>(t, X) \<in> \<F> ?rhs\<close> obtain a where \<open>a \<in> A\<close> \<open>(t, X) \<in> \<F> (P a \<triangle> Q)\<close>
      by (auto simp add: \<open>A \<noteq> {}\<close> F_GlobalNdet)
    with \<open>t \<notin> \<D> ?rhs\<close> consider u r where \<open>t = u @ [\<checkmark>(r)]\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P a)\<close>
      | r where \<open>\<checkmark>(r) \<notin> X\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> (P a)\<close>
      | \<open>(t, X) \<in> \<F> (P a)\<close> \<open>tF t\<close> \<open>([], X) \<in> \<F> Q\<close>
      | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> (P a)\<close> \<open>tF u\<close> \<open>(v, X) \<in> \<F> Q\<close> \<open>v \<noteq> []\<close>
      | r where \<open>\<checkmark>(r) \<notin> X\<close> \<open>t \<in> \<T> (P a)\<close> \<open>tF t\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q\<close>
      unfolding D_GlobalNdet Interrupt_projs by blast
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      from \<open>a \<in> A\<close> show \<open>t = u @ [\<checkmark>(r)] \<Longrightarrow> u @ [\<checkmark>(r)] \<in> \<T> (P a) \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u r
        by (auto simp add: F_Interrupt T_GlobalNdet)
    next
      from \<open>a \<in> A\<close> show \<open>\<checkmark>(r) \<notin> X \<Longrightarrow> t @ [\<checkmark>(r)] \<in> \<T> (P a) \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for r
        by (auto simp add: F_Interrupt GlobalNdet_projs)
    next
      from \<open>a \<in> A\<close> show \<open>(t, X) \<in> \<F> (P a) \<Longrightarrow> tF t \<Longrightarrow> ([], X) \<in> \<F> Q \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close>
        by (auto simp add: F_Interrupt F_GlobalNdet)
    next
      from \<open>a \<in> A\<close> show \<open>\<lbrakk>t = u @ v; u \<in> \<T> (P a); tF u; (v, X) \<in> \<F> Q; v \<noteq> []\<rbrakk>
                         \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u v
        by (simp add: F_Interrupt GlobalNdet_projs) blast
    next
      from \<open>a \<in> A\<close> show \<open>\<lbrakk>\<checkmark>(r) \<notin> X; t \<in> \<T> (P a); tF t; [\<checkmark>(r)] \<in> \<T> Q\<rbrakk> \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for r
        by (simp add: F_Interrupt GlobalNdet_projs) blast
    qed
  qed
qed



corollary Interrupt_distrib_Ndet_left : \<open>P \<triangle> Q1 \<sqinter> Q2 = (P \<triangle> Q1) \<sqinter> (P \<triangle> Q2)\<close>
proof -
  have \<open>P \<triangle> Q1 \<sqinter> Q2 = P \<triangle> (\<sqinter>n \<in> {0::nat, 1}. (if n = 0 then Q1 else Q2))\<close>
    by (simp add: GlobalNdet_distrib_unit)
  also have \<open>\<dots> = (\<sqinter>n \<in> {0::nat, 1}. P \<triangle> (if n = 0 then Q1 else Q2))\<close>
    by (simp add: Interrupt_distrib_GlobalNdet_left)
  also have \<open>\<dots> = (P \<triangle> Q1) \<sqinter> (P \<triangle> Q2)\<close>
    by (simp add: GlobalNdet_distrib_unit)
  finally show ?thesis .
qed

corollary Interrupt_distrib_Ndet_right : \<open>P1 \<sqinter> P2 \<triangle> Q = (P1 \<triangle> Q) \<sqinter> (P2 \<triangle> Q)\<close>
proof -
  have \<open>P1 \<sqinter> P2 \<triangle> Q = (\<sqinter>n \<in> {0::nat, 1}. (if n = 0 then P1 else P2)) \<triangle> Q\<close>
    by (simp add: GlobalNdet_distrib_unit)
  also have \<open>\<dots> = (\<sqinter>n \<in> {0::nat, 1}. (if n = 0 then P1 else P2) \<triangle> Q)\<close>
    by (simp add: Interrupt_distrib_GlobalNdet_right)
  also have \<open>\<dots> = (P1 \<triangle> Q) \<sqinter> (P2 \<triangle> Q)\<close>
    by (simp add: GlobalNdet_distrib_unit)
  finally show ?thesis .
qed



subsection \<open>Global Deterministic Choice\<close>

lemma GlobalDet_distrib_Ndet_left :
  \<open>(\<box>a \<in> A. P a \<sqinter> Q) = (if A = {} then STOP else (\<box>a \<in> A. P a) \<sqinter> Q)\<close>
  by (auto simp add: Process_eq_spec Ndet_projs GlobalDet_projs F_STOP D_STOP
      intro: is_processT8 is_processT6_TR_notin)

lemma GlobalDet_distrib_Ndet_right :
  \<open>(\<box>a \<in> A. P \<sqinter> Q a) = (if A = {} then STOP else P \<sqinter> (\<box>a \<in> A. Q a))\<close>
  by (subst (1 2) Ndet_commute) (fact GlobalDet_distrib_Ndet_left)

lemma Ndet_distrib_GlobalDet_left :
  \<open>P \<sqinter> (\<box>a \<in> A. Q a) = (if A = {} then P \<sqinter> STOP else \<box>a \<in> A. P \<sqinter> Q a)\<close>
  by (simp add: GlobalDet_distrib_Ndet_right)

lemma Ndet_distrib_GlobalDet_right :
  \<open>(\<box>a \<in> A. P a) \<sqinter> Q = (if A = {} then Q \<sqinter> STOP else \<box>a \<in> A. P a \<sqinter> Q)\<close>
  by (metis (no_types) GlobalDet_distrib_Ndet_left GlobalDet_empty Ndet_commute)


(*<*)
end
  (*>*)
