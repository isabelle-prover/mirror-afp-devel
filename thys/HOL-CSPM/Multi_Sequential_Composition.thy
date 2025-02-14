(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Multi sequential composition
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


section \<open>Multiple Sequential Composition\<close>

(*<*)
theory Multi_Sequential_Composition
  imports "HOL-CSP.CSP"
begin
  (*>*)

text \<open>Because of the fact that \<^term>\<open>SKIP r\<close> is not exactly a neutral element for
      @{const [source] Seq} (cf @{thm SKIP_Seq Seq_SKIP}), we do the folding
      on the reversed list.\<close>


subsection \<open>Definition\<close>

fun MultiSeq_rev :: \<open>['b list, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where MultiSeq_rev_Nil  : \<open>MultiSeq_rev   []    P = SKIP undefined\<close>
  |     MultiSeq_rev_Cons : \<open>MultiSeq_rev (l # L) P = MultiSeq_rev L P \<^bold>; P l\<close>


definition MultiSeq :: \<open>['b list, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>MultiSeq L P \<equiv> MultiSeq_rev (rev L) P\<close>


lemma MultiSeq_Nil  [simp] : \<open>MultiSeq []        P = SKIP undefined\<close>
  and MultiSeq_snoc [simp] : \<open>MultiSeq (L @ [l]) P = MultiSeq L P \<^bold>; P l\<close>
  by (simp_all add: MultiSeq_def)


lemma MultiSeq_elims :
  \<open>MultiSeq L P = Q \<Longrightarrow>
   (\<And>P'. L = [] \<Longrightarrow> P = P' \<Longrightarrow> Q = SKIP undefined \<Longrightarrow> thesis) \<Longrightarrow>
   (\<And>l L' P'. L = L' @ [l] \<Longrightarrow> P = P' \<Longrightarrow> Q = MultiSeq L' P' \<^bold>; P' l \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (simp add: MultiSeq_def, erule MultiSeq_rev.elims, simp_all)



syntax  "_MultiSeq" :: \<open>[pttrn, 'b list, 'b \<Rightarrow> 'r \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3SEQ _\<in>@_./ _)\<close> [78,78,77] 77)
syntax_consts "_MultiSeq" \<rightleftharpoons> MultiSeq
translations  "SEQ p \<in>@ L. P" \<rightleftharpoons> "CONST MultiSeq L (\<lambda>p. P)"



subsection \<open>First Properties\<close>

lemma \<open>SEQ p \<in>@ []. P p = SKIP undefined\<close> by (fact MultiSeq_Nil)

lemma \<open>SEQ i \<in>@ (L @ [l]). P i = SEQ i \<in>@ L. P i \<^bold>; P l\<close> by (fact MultiSeq_snoc)

lemma MultiSeq_singl [simp] : \<open>SEQ l \<in>@ [l]. P l = P l\<close> by (simp add: MultiSeq_def)



subsection \<open>Some Tests\<close>

lemma \<open>SEQ p \<in>@ []. P p = SKIP undefined\<close> 
  and \<open>SEQ p \<in>@ [a]. P p = P a\<close> 
  and \<open>SEQ p \<in>@ [a, b]. P p = P a \<^bold>; P b\<close> 
  and \<open>SEQ p \<in>@ [a, b, c]. P p = P a \<^bold>; P b \<^bold>; P c\<close>
  by (simp_all add: MultiSeq_def)


lemma test_MultiSeq: \<open>(SEQ p \<in>@ [1::int .. 3]. P p) = P 1 \<^bold>; P 2 \<^bold>; P 3\<close>
  by (simp add: upto.simps MultiSeq_def)


subsection \<open>Continuity\<close>

lemma mono_MultiSeq :
  \<open>(\<And>x. x \<in> set L \<Longrightarrow> P x \<sqsubseteq> Q x) \<Longrightarrow> SEQ l \<in>@ L. P l \<sqsubseteq> SEQ l \<in>@ L. Q l\<close>
  by (induct L rule: rev_induct, simp_all add: fun_belowI mono_Seq)

lemma MultiSeq_cont[simp]:
  \<open>(\<And>x. x \<in> set L \<Longrightarrow> cont (P x)) \<Longrightarrow> cont (\<lambda>y. SEQ z \<in>@ L. P z y)\<close>
  by (induct L rule: rev_induct) simp_all



subsection \<open>Factorization of \<^const>\<open>Seq\<close> in front of \<^const>\<open>MultiSeq\<close>\<close>

lemma MultiSeq_factorization_append:
  \<open>L2 \<noteq> [] \<Longrightarrow> SEQ p \<in>@ L1. P p \<^bold>; SEQ p \<in>@ L2. P p = SEQ p \<in>@ (L1 @ L2). P p\<close>
  by (induct L2 rule: rev_induct, simp_all)
    (metis (no_types, lifting) MultiSeq_singl MultiSeq_snoc
      Seq_assoc append_assoc append_self_conv2)



subsection \<open>\<^term>\<open>\<bottom>\<close> Absorbtion\<close>


lemma MultiSeq_BOT_absorb:
  \<open>SEQ z \<in>@ (L1 @ a # L2). P z = SEQ z \<in>@ L1. P z \<^bold>; \<bottom>\<close> if \<open>P a = \<bottom>\<close>
proof (cases \<open>L2 = []\<close>)
  from \<open>P a = \<bottom>\<close> show \<open>L2 = [] \<Longrightarrow> MultiSeq (L1 @ a # L2) P = MultiSeq L1 P \<^bold>; \<bottom>\<close> by simp
next
  show \<open>L2 \<noteq> [] \<Longrightarrow> MultiSeq (L1 @ a # L2) P = MultiSeq L1 P \<^bold>; \<bottom>\<close>
    by (simp add: \<open>P a = \<bottom>\<close> flip: Seq_assoc MultiSeq_factorization_append
        [of L2 \<open>L1 @ [a]\<close>, simplified])
qed



subsection \<open>First Properties\<close>

lemma MultiSeq_SKIP_neutral:
  \<open>SEQ z \<in>@ (L1 @ a # L2). P z =
   (  if L2 = [] then SEQ z \<in>@ L1. P z \<^bold>; SKIP r
    else SEQ z \<in>@ (L1 @ L2). P z)\<close> if \<open>P a = SKIP r\<close>
proof (split if_split, intro conjI impI)
  show \<open>L2 = [] \<Longrightarrow> MultiSeq (L1 @ a # L2) P = MultiSeq L1 P \<^bold>; SKIP r\<close>
    by (simp add: \<open>P a = SKIP r\<close>)
next
  assume \<open>L2 \<noteq> []\<close>
  have \<open>MultiSeq (L1 @ a # L2) P = MultiSeq L1 P \<^bold>; P a \<^bold>; MultiSeq L2 P\<close>
    by (metis (mono_tags, opaque_lifting) Cons_eq_appendI MultiSeq_factorization_append
        MultiSeq_snoc \<open>L2 \<noteq> []\<close> append_eq_appendI self_append_conv2)
  also have \<open>\<dots> = MultiSeq L1 P \<^bold>; MultiSeq L2 P\<close>
    by (simp add: \<open>P a = SKIP r\<close> flip: Seq_assoc)
  also have \<open>\<dots> = MultiSeq (L1 @ L2) P\<close>
    by (simp add: MultiSeq_factorization_append \<open>L2 \<noteq> []\<close>)
  finally show \<open>MultiSeq (L1 @ a # L2) P = MultiSeq (L1 @ L2) P\<close> .
qed


lemma MultiSeq_STOP_absorb:
  \<open>SEQ z \<in>@ (L1 @ a # L2). P z = SEQ z \<in>@ L1. P z \<^bold>; STOP\<close> if \<open>P a = STOP\<close>
proof (cases \<open>L2 = []\<close>)
  show \<open>L2 = [] \<Longrightarrow> MultiSeq (L1 @ a # L2) P = MultiSeq L1 P \<^bold>; STOP\<close>
    by (simp add: \<open>P a = STOP\<close>)
next
  show \<open>L2 \<noteq> [] \<Longrightarrow> MultiSeq (L1 @ a # L2) P = MultiSeq L1 P \<^bold>; STOP\<close>
    by (simp add: \<open>P a = STOP\<close> flip: Seq_assoc MultiSeq_factorization_append
        [of L2 \<open>L1 @ [a]\<close>, simplified])
qed


lemma mono_MultiSeq_eq:
  \<open>(\<And>x. x \<in> set L \<Longrightarrow> P x = Q x) \<Longrightarrow> MultiSeq L P = MultiSeq L Q\<close>
  by (induct L rule: rev_induct) simp_all


(* TODO: try this when we will have Seq_is_SKIP_iff *)
(* lemma MultiSeq_is_SKIP_iff:
  \<open>MultiSeq L P = SKIP \<longleftrightarrow> (\<forall>a \<in> set L. P a = SKIP)\<close>
  by (induct L, simp_all add: Seq_is_SKIP_iff) *)



subsection \<open>Commutativity\<close>

text \<open>Of course, since the sequential composition \<^term>\<open>P \<^bold>; Q\<close> is not commutative,
      the result here is negative: the order of the elements of list \<^term>\<open>L\<close>
      does matter in @{term [eta_contract = false] \<open>SEQ z \<in>@ L. P z\<close>}.\<close>



subsection \<open>Behaviour with Injectivity\<close>

lemma inj_on_mapping_over_MultiSeq:
  \<open>inj_on f (set C) \<Longrightarrow>
   SEQ x \<in>@ C. P x = SEQ x \<in>@ map f C. P (inv_into (set C) f x)\<close>
proof (induct C rule: rev_induct)
  show \<open>inj_on f (set []) \<Longrightarrow> MultiSeq [] P =
        SEQ x\<in>@map f []. P (inv_into (set []) f x)\<close> by simp
next
  case (snoc a C)
  hence f1: \<open>inv_into (insert a (set C)) f (f a) = a\<close> by force
  show ?case
    apply (simp add: f1, intro ext arg_cong[where f = \<open>\<lambda>x. x \<^bold>; P a\<close>])
    apply (subst "snoc.hyps"(1), rule inj_on_subset[OF "snoc.prems"],
        simp add: subset_insertI)
    using snoc.prems by (auto intro!: mono_MultiSeq_eq)
qed



subsection \<open>Definition of \<open>first_elem\<close>\<close>

primrec first_elem :: \<open>['a \<Rightarrow> bool, 'a list] \<Rightarrow> nat\<close>
  where \<open>first_elem P [] = 0\<close>
  |     \<open>first_elem P (x # L) = (if P x then 0 else Suc (first_elem P L))\<close>

text \<open>\<^const>\<open>first_elem\<close> returns the first index \<^term>\<open>i\<close> such that
      \<^term>\<open>P (L ! i) = True\<close> if it exists, \<^term>\<open>length L\<close> otherwise.

      This will be very useful later.\<close>

value \<open>first_elem (\<lambda>x. 4 < x) [0::nat, 2, 5]\<close>
lemma \<open>first_elem (\<lambda>x. 5 < x) [0::nat, 2, 5] = 3\<close> by simp 
lemma \<open>P ` set L \<subseteq> {False} \<Longrightarrow> first_elem P L = length L\<close> by (induct L; simp)


(*<*)
end
  (*>*)