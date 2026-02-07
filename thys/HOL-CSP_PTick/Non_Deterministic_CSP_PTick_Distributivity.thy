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


(*<*)
theory Non_Deterministic_CSP_PTick_Distributivity
  imports Sequential_Composition_Generalized
    Synchronization_Product_Generalized
begin
  (*>*)


section \<open>Distributivity of Non-Determinism\<close>

subsection \<open>Sequential Composition\<close>

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left :
  \<open>P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. \<sqinter> a\<in>A. Q a r) = (if A = {} then P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. STOP) else \<sqinter> a\<in>A. (P \<^bold>;\<^sub>\<checkmark> Q a))\<close>
  by simp (auto simp add: Process_eq_spec GlobalNdet_projs STOP_projs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right : \<open>(\<sqinter> a\<in>A. P a) \<^bold>;\<^sub>\<checkmark> Q = \<sqinter> a\<in>A. (P a \<^bold>;\<^sub>\<checkmark> Q)\<close>
  by (simp add: Process_eq_spec GlobalNdet_projs STOP_projs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    (safe; simp; blast) \<comment> \<open>quicker than auto proof\<close>


lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_left : \<open>P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<sqinter> R r) = (P \<^bold>;\<^sub>\<checkmark> Q) \<sqinter> (P \<^bold>;\<^sub>\<checkmark> R)\<close>
  by (fact Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left[of P \<open>{0 :: nat, 1}\<close>
        \<open>\<lambda>n. if n = 0 then Q else if n = 1 then R else undefined\<close>,
        simplified GlobalNdet_distrib_unit_bis, simplified])

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_right : \<open>P \<sqinter> Q \<^bold>;\<^sub>\<checkmark> R = (P \<^bold>;\<^sub>\<checkmark> R) \<sqinter> (Q \<^bold>;\<^sub>\<checkmark> R)\<close>
  by (fact Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right[of \<open>{0 :: nat, 1}\<close>
        \<open>\<lambda>n. if n = 0 then P else if n = 1 then Q else undefined\<close> R,
        simplified GlobalNdet_distrib_unit_bis, simplified])



subsection \<open>Synchronization Product\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin

lemma Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left : 
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<sqinter> a\<in>A. Q a = (if A = {} then P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP else \<sqinter> a\<in>A. (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a))\<close>
  (is \<open>?lhs = (if A = {} then P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP\<close>
    by (simp add: GlobalNdet.abs_eq STOP.abs_eq)
next
  show \<open>?lhs = ?rhs\<close> if \<open>A \<noteq> {}\<close>
  proof (subst Process_eq_spec_optimized, safe)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k GlobalNdet_projs)
        (metis \<open>A \<noteq> {}\<close> ex_in_conv is_processT1_TR)
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (simp add: GlobalNdet_projs D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  next
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close>
    with \<open>A \<noteq> {}\<close> consider \<open>t \<in> \<D> ?lhs\<close>
      | (fail) t_P t_Q X_P X_Q a where
        \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>a \<in> A\<close> \<open>(t_Q, X_Q) \<in> \<F> (Q a)\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs F_GlobalNdet by force
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>t \<in> \<D> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> by blast
    next
      case fail
      thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (simp add: F_GlobalNdet F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    qed
  next
    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X  
      by (simp add: GlobalNdet_projs F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>A \<noteq> {}\<close>) blast
  qed
qed

lemma Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right : 
  \<open>\<sqinter> a\<in>A. P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q = (if A = {} then STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q else \<sqinter> a\<in>A. (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  (is \<open>?lhs = (if A = {} then STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs = STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close>
    by (simp add: GlobalNdet.abs_eq STOP.abs_eq)
next
  show \<open>?lhs = ?rhs\<close> if \<open>A \<noteq> {}\<close>
  proof (subst Process_eq_spec_optimized, safe)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k GlobalNdet_projs)
        (metis \<open>A \<noteq> {}\<close> ex_in_conv is_processT1_TR)
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (simp add: GlobalNdet_projs D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  next
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close>
    with \<open>A \<noteq> {}\<close> consider \<open>t \<in> \<D> ?lhs\<close>
      | (fail) t_P t_Q X_P X_Q a where
        \<open>(t_P, X_P) \<in> \<F> (P a)\<close> \<open>a \<in> A\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs F_GlobalNdet by force
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>t \<in> \<D> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> by blast
    next
      case fail
      thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (simp add: F_GlobalNdet F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    qed
  next
    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X  
      by (simp add: GlobalNdet_projs F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>A \<noteq> {}\<close>) blast
  qed
qed


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalNdet_cartprod:
  \<open>(\<sqinter> (a, b) \<in> A \<times> B. (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) = 
   (if A = {} \<or> B = {} then STOP else (\<sqinter>a \<in> A. P a) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> (\<sqinter>b \<in> B. Q b))\<close>  
  by (simp add: GlobalNdet_cartprod Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left
      Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right GlobalNdet_sets_commute[of A])


lemma Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_left : 
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q \<sqinter> R = (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<sqinter> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> R)\<close>
  by (rule trans[OF trans[OF _ Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_left
          [of P S \<open>{True, False}\<close> \<open>\<lambda>b. if b then Q else R\<close>]]])
    (simp_all add: GlobalNdet_distrib_unit)

corollary Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_Ndet_right : 
  \<open>P \<sqinter> Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> R = (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> R) \<sqinter> (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> R)\<close>
  by (rule trans[OF trans[OF _ Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_distrib_GlobalNdet_right
          [of \<open>{True, False}\<close> \<open>\<lambda>b. if b then P else Q\<close> S R]]])
    (simp_all add: GlobalNdet_distrib_unit)


end

(*<*)
end
  (*>*)