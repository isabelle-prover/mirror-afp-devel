(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
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

section \<open>Non Destructiveness of Choices\<close>

(*<*)
theory Choices_Non_Destructive
  imports Process_Restriction_Space "HOL-CSPM.CSPM_Laws"
begin
  (*>*)


subsection \<open>Equality\<close>

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Ndet : \<open>P \<sqinter> Q \<down> n = (P \<down> n) \<sqinter> (Q \<down> n)\<close>
  by (auto simp add: Process_eq_spec Ndet_projs restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalNdet :
  \<open>(\<sqinter>a \<in> A. P a) \<down> n = (if n = 0 then \<bottom> else \<sqinter>a \<in> A. (P a \<down> n))\<close>
  by simp (auto simp add: Process_eq_spec GlobalNdet_projs restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)


lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalDet :
  \<open>(\<box>a \<in> A. P a) \<down> n = (if n = 0 then \<bottom> else \<box>a \<in> A. (P a \<down> n))\<close>
  (is \<open>?lhs = (if n = 0 then \<bottom> else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>n = 0 \<Longrightarrow> ?lhs = \<bottom>\<close> by simp
next
  show \<open>?lhs = ?rhs\<close> if \<open>n \<noteq> 0\<close>
  proof (rule Process_eq_optimized_bisI)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (auto simp add: GlobalDet_projs D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>n \<noteq> 0\<close> split: if_split_asm)
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (auto simp add: GlobalDet_projs D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    show \<open>([], X) \<in> \<F> ?lhs \<Longrightarrow> ([], X) \<in> \<F> ?rhs\<close> for X
      by (auto simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs F_GlobalDet)
  next
    show \<open>([], X) \<in> \<F> ?rhs \<Longrightarrow> ([], X) \<in> \<F> ?lhs\<close> for X
      by (auto simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs F_GlobalDet)
        (metis append_eq_Cons_conv event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) tickFree_Cons_iff)
  next
    show \<open>(e # t, X) \<in> \<F> ?lhs \<Longrightarrow> (e # t, X) \<in> \<F> ?rhs\<close> for e t X
      by (auto simp add: \<open>n \<noteq> 0\<close> F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k GlobalDet_projs split: if_split_asm)
  next
    show \<open>(e # t, X) \<in> \<F> ?rhs \<Longrightarrow> (e # t, X) \<in> \<F> ?lhs\<close> for e t X
      by (auto simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k GlobalDet_projs)
  qed
qed


lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det: \<open>P \<box> Q \<down> n = (P \<down> n) \<box> (Q \<down> n)\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  have \<open>P \<box> Q \<down> n = \<box>i \<in> {0, 1 :: nat}. (if i = 0 then P else Q) \<down> n\<close>
    by (simp add: GlobalDet_distrib_unit_bis)
  also have \<open>\<dots> = (if n = 0 then \<bottom> else \<box>i \<in> {0, 1 :: nat}. (if i = 0 then P \<down> n else Q \<down> n))\<close>
    by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalDet if_distrib if_distribR)
  also have \<open>\<dots> = (P \<down> n) \<box> (Q \<down> n)\<close> by (simp add: GlobalDet_distrib_unit_bis)
  finally show \<open>P \<box> Q \<down> n = (P \<down> n) \<box> (Q \<down> n)\<close> .
qed


corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sliding: \<open>P \<rhd> Q \<down> n = (P \<down> n) \<rhd> (Q \<down> n)\<close>
  by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Ndet Sliding_def)




subsection \<open>Non Destructiveness\<close>

lemma GlobalNdet_non_destructive : \<open>non_destructive (\<lambda>P. \<sqinter>a \<in> A. P a)\<close>
  by (auto intro: non_destructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalNdet restriction_fun_def)

lemma Ndet_non_destructive : \<open>non_destructive (\<lambda>(P, Q). P \<sqinter> Q)\<close>
  by (auto intro: non_destructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Ndet restriction_prod_def)

lemma GlobalDet_non_destructive : \<open>non_destructive (\<lambda>P. \<box>a \<in> A. P a)\<close>
  by (auto intro: non_destructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalDet restriction_fun_def)

lemma Det_non_destructive : \<open>non_destructive (\<lambda>(P, Q). P \<box> Q)\<close>
  by (auto intro: non_destructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det restriction_prod_def)

corollary Sliding_non_destructive : \<open>non_destructive (\<lambda>(P, Q). P \<rhd> Q)\<close>
  by (auto intro: non_destructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sliding restriction_prod_def)


(*<*)
end
  (*>*)