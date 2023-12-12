(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Multi-sequential composition
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


chapter \<open>The MultiSeq Operator\<close>

theory MultiSeq
  imports Patch
begin



section \<open>Definition\<close>

definition MultiSeq :: \<open>['a list, 'a \<Rightarrow> 'b process] \<Rightarrow> 'b process\<close>
  where    \<open>MultiSeq S P = foldr (\<lambda>a r.  (P a) \<^bold>;  r  ) S SKIP\<close>


syntax  "_MultiSeq" :: \<open>[pttrn,'a list, 'b process] \<Rightarrow> 'b process\<close>
                       (\<open>(3SEQ _\<in>@_./ _)\<close> 73)
translations  "SEQ i \<in>@ A. P " \<rightleftharpoons> "CONST MultiSeq A (\<lambda>i. P)"



section \<open>First Properties\<close>

lemma MultiSeq_rec0[simp]: \<open>(SEQ p \<in>@ []. P p) = SKIP\<close>
  by (simp add: MultiSeq_def)


lemma MultiSeq_rec1[simp]: \<open>(SEQ p \<in>@ [a]. P p) = P a\<close>
  by (simp add: MultiSeq_def Seq_SKIP)


lemma MultiSeq_Cons[simp]: \<open>(SEQ i \<in>@ a # L. P i) = P a \<^bold>; (SEQ i \<in>@ L. P i)\<close>
  by (simp add: MultiSeq_def)



section \<open>Some Tests\<close>

lemma \<open>(SEQ p \<in>@ []. P p) = SKIP\<close> 
  and \<open>(SEQ p \<in>@ [a]. P p) = P a\<close> 
  and \<open>(SEQ p \<in>@ [a,b]. P p) = P a \<^bold>; P b\<close> 
  and \<open>(SEQ p \<in>@ [a,b,c]. P p) = P a \<^bold>; P b \<^bold>; P c\<close> 
  by (simp_all add: Seq_SKIP Seq_assoc)


lemma test_MultiSeq: \<open>(SEQ p \<in>@ [1::int .. 3]. P p) = P 1 \<^bold>; P 2 \<^bold>; P 3\<close>
  by (simp add: upto.simps Seq_SKIP Seq_assoc)



section \<open>Continuity\<close>

lemma MultiSeq_cont[simp]:
  \<open>\<forall>x \<in> set L. cont (P x) \<Longrightarrow> cont (\<lambda>y. SEQ z \<in>@ L. P z y)\<close> 
  by (induct L) force+



section \<open>Factorization of \<^const>\<open>Seq\<close> in front of \<^const>\<open>MultiSeq\<close>\<close>

lemma MultiSeq_factorization_append:
  \<open>(SEQ p \<in>@ A. P p) \<^bold>; (SEQ p \<in>@ B. P p) = (SEQ p \<in>@ A @ B . P p)\<close>
  by (induct A rule: list.induct, simp_all add: SKIP_Seq, metis Seq_assoc)



section \<open>\<^term>\<open>\<bottom>\<close> Absorbance\<close>


lemma MultiSeq_BOT_absorb:
  \<open>P a = \<bottom> \<Longrightarrow> (SEQ z \<in>@ l1 @ [a] @ l2. P z) = (SEQ z \<in>@ l1. P z) \<^bold>; \<bottom>\<close>
  by (metis BOT_Seq MultiSeq_Cons MultiSeq_factorization_append)



section \<open>First Properties\<close>

lemma MultiSeq_SKIP_neutral:
  \<open>P a = SKIP \<Longrightarrow> (SEQ z \<in>@ l1 @ [a] @ l2. P z) = SEQ z \<in>@ l1 @ l2. P z\<close>
  by (simp add: MultiSeq_def SKIP_Seq)


lemma MultiSeq_STOP_absorb:
  \<open>P a = STOP \<Longrightarrow>
   (SEQ z \<in>@ l1 @ [a] @ l2. P z) = (SEQ z \<in>@ l1. P z) \<^bold>; STOP\<close>
  by (metis STOP_Seq MultiSeq_Cons MultiSeq_factorization_append)


lemma mono_MultiSeq_eq:
  \<open>\<forall>x \<in> set L. P x = Q x \<Longrightarrow> MultiSeq L P = MultiSeq L Q\<close>
  by (induct L) fastforce+


lemma MultiSeq_is_SKIP_iff:
  \<open>MultiSeq L P = SKIP \<longleftrightarrow> (\<forall>a \<in> set L. P a = SKIP)\<close>
  by (induct L, simp_all add: Seq_is_SKIP_iff)



section \<open>Commutativity\<close>

text \<open>Of course, since the sequential composition \<^term>\<open>P \<^bold>; Q\<close> is not commutative,
      the result here is negative: the order of the elements of list \<^term>\<open>L\<close>
      does matter in @{term [eta_contract = false] \<open>SEQ z \<in>@ L. P z\<close>}.\<close>



section \<open>Behaviour with Injectivity\<close>

lemma inj_on_mapping_over_MultiSeq:
  \<open>inj_on f (set C) \<Longrightarrow>
   (SEQ x \<in>@  C. P x) = SEQ x \<in>@ map f C. P (inv_into (set C) f x)\<close>
proof (induct C)
  case Nil
  show ?case by simp
next
  case (Cons a C)
  hence f1: \<open>inv_into (insert a (set C)) f (f a) = a\<close> by force
  show ?case
    apply (simp add: f1, rule arg_cong[where f = \<open>\<lambda>x. P a \<^bold>; x\<close>])
    apply (subst "Cons.hyps"(1), rule inj_on_subset[OF "Cons.prems"],
           simp add: subset_insertI)
    apply (rule mono_MultiSeq_eq)
    using "Cons.prems" by fastforce
qed



section \<open>Definition of \<open>first_elem\<close>\<close>

primrec first_elem :: \<open>['\<alpha> \<Rightarrow> bool, '\<alpha> list] \<Rightarrow> nat\<close>
  where \<open>first_elem P [] = 0\<close>
  |     \<open>first_elem P (x # L) = (if P x then 0 else Suc (first_elem P L))\<close>

text \<open>\<^const>\<open>first_elem\<close> returns the first index \<^term>\<open>i\<close> such that
      \<^term>\<open>P (L ! i) = True\<close> if it exists, \<^term>\<open>length L\<close> otherwise.

      This will be very useful later.\<close>

value \<open>first_elem (\<lambda>x. 4 < x) [0::nat, 2, 5]\<close>
lemma \<open>first_elem (\<lambda>x. 5 < x) [0::nat, 2, 5] = 3\<close> by simp 
lemma \<open>P ` set L \<subseteq> {False} \<Longrightarrow> first_elem P L = length L\<close> by (induct L; simp)



end