(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Multi synchronization product
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


section \<open>Multiple Synchronization Product\<close>

(*<*)
theory Multi_Synchronization_Product
  imports Induction_Rules_CSPM "HOL-CSP.CSP"
begin
  (*>*)


subsection \<open>Definition\<close>

text \<open>As in the \<^const>\<open>Ndet\<close> case, we have no neutral element so we will also have to go through lists
first. But the binary operator \<^const>\<open>Sync\<close> is not idempotent either, so the generalization will be done
on \<^typ>\<open>'b multiset\<close> and not on \<^typ>\<open>'b set\<close>.\<close>

text \<open>Note that a \<^typ>\<open>'b multiset\<close> is by construction finite (cf. theorem
      @{thm Multiset.finite_set_mset[no_vars]}).\<close>

fun MultiSync_list :: \<open>['a set, 'b list, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>MultiSync_list S   []    P = STOP\<close>
  |     \<open>MultiSync_list S (l # L) P = fold (\<lambda>x r. r \<lbrakk>S\<rbrakk> P x) L (P l)\<close> 
    (* 

syntax "_MultiSync_list" :: \<open>[pttrn, 'a set, 'b list, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3\<^bold>\<lbrakk>_\<^bold>\<rbrakk>\<^sub>l_\<in>_./ _)\<close> 63)
translations  "\<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>l p \<in> L. P " \<rightleftharpoons> "CONST MultiSync_list S L (\<lambda>p. P)"
 *)

interpretation MultiSync: comp_fun_commute where f = \<open>\<lambda>x r. r \<lbrakk>E\<rbrakk> P x\<close>
  unfolding comp_fun_commute_def comp_fun_idem_axioms_def comp_def
  by (metis Sync_assoc Sync_commute)


lemma MultiSync_list_mset:
  \<open>mset L = mset L' \<Longrightarrow> MultiSync_list S L P = MultiSync_list S L' P\<close> 
proof (cases L, simp_all)
  fix a l
  assume * : \<open>add_mset a (mset l) = mset L'\<close>  and  ** : \<open>L = a # l\<close>
  then obtain a' l' where *** : \<open> L' = a' # l'\<close>
    by (metis list.exhaust mset.simps(2) mset_zero_iff)
  note **** = *[simplified ***, simplified]
  have a0: \<open>a \<noteq> a' \<Longrightarrow> MultiSync_list S L P = 
                       fold (\<lambda>x r. r \<lbrakk>S\<rbrakk> P x) (a' # (remove1 a' l)) (P a)\<close>
    apply (subst fold_multiset_equiv[where ys = \<open>l\<close>])
      apply (metis MultiSync.comp_fun_commute_axioms comp_fun_commute_def)
     apply (simp_all add: * ** ***) 
    by (metis **** insert_DiffM insert_noteq_member)
  have a1: \<open>a \<noteq> a' \<Longrightarrow> MultiSync_list S L' P =
                       fold (\<lambda>x r. r \<lbrakk>S\<rbrakk> P x) (a # (remove1 a l')) (P a')\<close>   
    apply (subst fold_multiset_equiv[where ys = \<open>l'\<close>])
      apply (metis MultiSync.comp_fun_commute_axioms comp_fun_commute_def)
     apply (simp_all add: * ** ***)
    by (metis **** insert_DiffM insert_noteq_member)
  from **** ** *** a0 a1 
  show \<open>fold (\<lambda>x r. r \<lbrakk>S\<rbrakk> P x) l (P a) = MultiSync_list S L' P\<close>
    apply (cases \<open>a = a'\<close>, simp)
     apply (subst fold_multiset_equiv[where ys = l'])      
       apply (metis MultiSync.comp_fun_commute_axioms comp_fun_commute_def)
      apply (simp_all)
    apply (subst fold_multiset_equiv[where ys = \<open>remove1 a l'\<close>],
        simp_all add: Sync_commute)
     apply (metis MultiSync.comp_fun_commute_axioms
        comp_fun_commute.comp_fun_commute) 
    by (metis add_mset_commute add_mset_diff_bothsides)
qed


definition MultiSync :: \<open>['a set, 'b multiset, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>MultiSync S M P = MultiSync_list S (SOME L. mset L = M) P\<close> 

syntax "_MultiSync" :: \<open>['a set,pttrn,'b multiset,('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3\<^bold>\<lbrakk>_\<^bold>\<rbrakk> _\<in>#_./ _)\<close> [78,78,78,77] 77)
syntax_consts "_MultiSync" \<rightleftharpoons> MultiSync
translations "\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. P " \<rightleftharpoons> "CONST MultiSync S M (\<lambda>p. P)"




text \<open>Special case of \<^term>\<open>MultiSync E P\<close> when \<^term>\<open>E = {}\<close>.\<close>

abbreviation MultiInter :: \<open>['b multiset, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>MultiInter M P \<equiv> MultiSync {} M P\<close> 

syntax "_MultiInter" :: \<open>[pttrn, 'b multiset, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3\<^bold>|\<^bold>|\<^bold>| _\<in>#_./ _)\<close> [78,78,77] 77)
syntax_consts "_MultiInter" \<rightleftharpoons> MultiInter
translations "\<^bold>|\<^bold>|\<^bold>| p \<in># M. P" \<rightleftharpoons> "CONST MultiInter M (\<lambda>p. P)"



text \<open>Special case of \<^term>\<open>MultiSync E P\<close> when \<^term>\<open>E = UNIV\<close>.\<close>

abbreviation MultiPar :: \<open>['b multiset, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>MultiPar M P \<equiv> MultiSync UNIV M P\<close> 

syntax "_MultiPar" :: \<open>[pttrn, 'b multiset, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3\<^bold>|\<^bold>| _\<in>#_. / _)\<close> [78,78,77] 77)
syntax_consts "_MultiPar" \<rightleftharpoons> MultiPar
translations "\<^bold>|\<^bold>| p \<in># M. P" \<rightleftharpoons> "CONST MultiPar M (\<lambda>p. P)"



subsection \<open>First properties\<close>

lemma MultiSync_rec0[simp]: \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># {#}. P p) = STOP\<close>
  unfolding MultiSync_def by simp


lemma MultiSync_rec1[simp]: \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># {#a#}. P p) = P a\<close> 
  unfolding MultiSync_def apply(rule someI2_ex) by simp_all


lemma MultiSync_add[simp]:   
  \<open>M \<noteq> {#} \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># add_mset m M. P p) = P m \<lbrakk>S\<rbrakk> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. P p)\<close>
  unfolding MultiSync_def
  apply(rule someI2_ex, simp add: ex_mset)+
proof(goal_cases)
  case (1 x x')
  thus \<open>MultiSync_list S x' P = P m \<lbrakk>S\<rbrakk> MultiSync_list S x P\<close>
    apply (subst MultiSync_list_mset[where L = \<open>x'\<close> and L' = \<open>x @ [m]\<close>], simp) 
    by (cases x) (simp_all add: Sync_commute)
qed


lemma mono_MultiSync_eq:
  \<open>(\<And>x. x \<in># M \<Longrightarrow> P x = Q x) \<Longrightarrow> MultiSync S M P = MultiSync S M Q\<close>
  by (cases \<open>M = {#}\<close>, simp, induct_tac rule: mset_induct_nonempty) auto

lemma mono_MultiSync_eq2:
  \<open>(\<And>x. x \<in># M \<Longrightarrow> P (f x) = Q x) \<Longrightarrow> MultiSync S (image_mset f M) P = MultiSync S M Q\<close>
  by (cases \<open>M = {#}\<close>, simp, induct_tac rule: mset_induct_nonempty) auto


lemmas MultiInter_rec0 = MultiSync_rec0[where S = \<open>{}\<close>]
  and MultiPar_rec0 = MultiSync_rec0[where S = \<open>UNIV\<close>]
  and MultiInter_rec1 = MultiSync_rec1[where S = \<open>{}\<close>]
  and MultiPar_rec1 = MultiSync_rec1[where S = \<open>UNIV\<close>]
  and MultiInter_add  =  MultiSync_add[where S = \<open>{}\<close>]
  and MultiPar_add  =  MultiSync_add[where S = \<open>UNIV\<close>]
  and mono_MultiInter_eq = mono_MultiSync_eq[where S = \<open>{}\<close>]
  and mono_MultiPar_eq = mono_MultiSync_eq[where S = \<open>UNIV\<close>]
  and mono_MultiInter_eq2 = mono_MultiSync_eq2[where S = \<open>{}\<close>]
  and mono_MultiPar_eq2 = mono_MultiSync_eq2[where S = \<open>UNIV\<close>]



subsection \<open>Some Tests\<close>


lemma \<open>MultiSync_list S [] P = STOP\<close> 
  and \<open>MultiSync_list S [a] P = P a\<close> 
  and \<open>MultiSync_list S [a, b] P = P a \<lbrakk>S\<rbrakk> P b\<close>  
  and \<open>MultiSync_list S [a, b, c] P = P a \<lbrakk>S\<rbrakk> P b \<lbrakk>S\<rbrakk> P c\<close>    
  by simp+


lemma test_MultiSync: 
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># mset []. P p) = STOP\<close>
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># mset [a]. P p) = P a\<close>
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># mset [a, b]. P p) = P a \<lbrakk>S\<rbrakk> P b\<close>
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># mset [a, b, c]. P p) = P a \<lbrakk>S\<rbrakk> P b \<lbrakk>S\<rbrakk> P c\<close>
  by (simp_all add: Sync_assoc)


lemma MultiSync_set1: \<open>MultiSync S (mset_set {k::nat..<k}) P = STOP\<close>
  by fastforce


lemma MultiSync_set2: \<open>MultiSync S (mset_set {k..<Suc k}) P = P k\<close>
  by fastforce


lemma MultiSync_set3:
  \<open>l <  k \<Longrightarrow> MultiSync S (mset_set {l ..< Suc k}) P =
   P l \<lbrakk>S\<rbrakk> (MultiSync S (mset_set {Suc l ..< Suc k}) P)\<close>
  by (simp add: Icc_eq_insert_lb_nat atLeastLessThanSuc_atLeastAtMost)


lemma test_MultiSync':
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># mset_set {1::int .. 3}. P p) = P 1 \<lbrakk>S\<rbrakk> P 2 \<lbrakk>S\<rbrakk> P 3\<close>
proof -
  have \<open>{1::int .. 3} = insert 1 (insert 2 (insert 3 {}))\<close> by fastforce
  thus \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># mset_set {1::int .. 3}. P p) = P 1 \<lbrakk>S\<rbrakk> P 2 \<lbrakk>S\<rbrakk> P 3\<close> by (simp add: Sync_assoc)
qed


lemma test_MultiSync'':
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># mset_set {0::nat .. a}. P p) =
    \<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># mset_set ({a} \<union> {1 .. a} \<union> {0}) . P p\<close>
  by (metis Un_insert_right atMost_atLeast0 boolean_algebra_cancel.sup0
      image_Suc_lessThan insert_absorb2 insert_is_Un lessThan_Suc
      lessThan_Suc_atMost lessThan_Suc_eq_insert_0)



lemmas   test_MultiInter =   test_MultiSync[where S = \<open>{}\<close>]
  and   test_MultiPar =   test_MultiSync[where S = \<open>UNIV\<close>]
  and   MultiInter_set1 =   MultiSync_set1[where S = \<open>{}\<close>]
  and   MultiPar_set1 =   MultiSync_set1[where S = \<open>UNIV\<close>]
  and   MultiInter_set2 =   MultiSync_set2[where S = \<open>{}\<close>]
  and   MultiPar_set2 =   MultiSync_set2[where S = \<open>UNIV\<close>]
  and   MultiInter_set3 =   MultiSync_set3[where S = \<open>{}\<close>]
  and   MultiPar_set3 =   MultiSync_set3[where S = \<open>UNIV\<close>]
  and  test_MultiInter' =  test_MultiSync'[where S = \<open>{}\<close>]
  and  test_MultiPar' =  test_MultiSync'[where S = \<open>UNIV\<close>]
  and test_MultiInter'' = test_MultiSync''[where S = \<open>{}\<close>]
  and test_MultiPar'' = test_MultiSync''[where S = \<open>UNIV\<close>]



subsection \<open>Continuity\<close>

lemma mono_MultiSync :
  \<open>(\<And>x. x \<in># M \<Longrightarrow> P x \<sqsubseteq> Q x) \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m) \<sqsubseteq> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. Q m)\<close>
  by (cases \<open>M = {#}\<close>, simp, erule mset_induct_nonempty, simp_all add: mono_Sync)

lemmas mono_MultiInter = mono_MultiSync[where S = \<open>{}\<close>]
  and mono_MultiPar = mono_MultiSync[where S = UNIV]


lemma MultiSync_cont[simp]:
  \<open>(\<And>x. x \<in># M \<Longrightarrow> cont (P x)) \<Longrightarrow> cont (\<lambda>y. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> z \<in># M. P z y)\<close>
  by (cases \<open>M = {#}\<close>, simp, erule mset_induct_nonempty, simp+)

lemmas MultiInter_cont[simp] = MultiSync_cont[where S = \<open>{}\<close>]
  and   MultiPar_cont[simp] = MultiSync_cont[where S = \<open>UNIV\<close>]



subsection \<open>Factorization of \<^const>\<open>Sync\<close> in front of \<^const>\<open>MultiSync\<close>\<close>

lemma MultiSync_factorization_union:
  \<open>\<lbrakk>M \<noteq> {#}; N \<noteq> {#}\<rbrakk> \<Longrightarrow>
   (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> z \<in># M. P z) \<lbrakk>S\<rbrakk> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> z \<in># N. P z) = \<^bold>\<lbrakk>S\<^bold>\<rbrakk> z\<in># (M + N). P z\<close>
  by (erule mset_induct_nonempty, simp_all add: Sync_assoc[symmetric])


lemmas MultiInter_factorization_union =
  MultiSync_factorization_union[where S = \<open>{}\<close>]
  and   MultiPar_factorization_union =
  MultiSync_factorization_union[where S = \<open>UNIV\<close>]



subsection \<open>\<^term>\<open>\<bottom>\<close> Absorbtion\<close>

lemma MultiSync_BOT_absorb:
  \<open>m \<in># M \<Longrightarrow> P m = \<bottom> \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> z \<in># M. P z) = \<bottom>\<close>
  by (metis MultiSync_add MultiSync_rec1 mset_add Sync_BOT Sync_commute)


lemmas MultiInter_BOT_absorb = MultiSync_BOT_absorb[where S =  \<open>{}\<close> ]
  and   MultiPar_BOT_absorb = MultiSync_BOT_absorb[where S = \<open>UNIV\<close>]


lemma MultiSync_is_BOT_iff:
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m) = \<bottom> \<longleftrightarrow> (\<exists>m \<in># M. P m = \<bottom>)\<close>
  apply (cases \<open>M = {#}\<close>, simp add: BOT_iff_Nil_D D_STOP)
  by (rotate_tac, induct M rule: mset_induct_nonempty, auto simp add: Sync_is_BOT_iff)


lemmas MultiInter_is_BOT_iff = MultiSync_is_BOT_iff[where S =  \<open>{}\<close> ]
  and   MultiPar_is_BOT_iff = MultiSync_is_BOT_iff[where S = \<open>UNIV\<close>]



subsection \<open>Other Properties\<close>

lemma MultiSync_SKIP_id:
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> r \<in># M. SKIP r) = (if \<exists>r. set_mset M = {r} then SKIP (THE r. set_mset M = {r}) else STOP)\<close>
  apply (cases \<open>M = {#}\<close>, simp)
  apply (induct M rule: mset_induct_nonempty, simp)
  by (simp add: subset_singleton_iff split: if_splits)


lemmas     MultiInter_SKIP_id = MultiSync_SKIP_id[where S = \<open>{}\<close>]
  and       MultiPar_SKIP_id = MultiSync_SKIP_id[where S = \<open>UNIV\<close>]



lemma MultiPar_prefix_two_distincts_STOP:
  assumes \<open>m \<in># M\<close> and \<open>m' \<in># M\<close> and \<open>fst m \<noteq> fst m'\<close>
  shows \<open>(\<^bold>|\<^bold>| a \<in># M. (fst a \<rightarrow> P (snd a))) = STOP\<close>
proof -
  obtain M' where f2: \<open>M = add_mset m (add_mset m' M')\<close>
    by (metis diff_union_swap insert_DiffM assms)
  show \<open>(\<^bold>|\<^bold>| x \<in># M. (fst x \<rightarrow> P (snd x))) = STOP\<close>
    apply (simp add: f2, cases \<open>M' = {#}\<close>, simp add: assms(3) write0_Par_write0)
    apply (induct M' rule: mset_induct_nonempty)
     apply (simp add: Sync_commute assms(3) write0_Par_write0)
    by simp (metis (no_types, lifting) STOP_Sync_write0 Sync_assoc Sync_commute UNIV_I)
qed    


lemma MultiPar_prefix_two_distincts_STOP':
  \<open>\<lbrakk>(m, n) \<in># M; (m', n') \<in># M; m \<noteq> m'\<rbrakk> \<Longrightarrow> 
   (\<^bold>|\<^bold>| (m, n) \<in># M. (m \<rightarrow> P n)) = STOP\<close>
  apply (subst cond_case_prod_eta[where g = \<open>\<lambda> x. (fst x \<rightarrow> P (snd x))\<close>])
  by (simp_all add: MultiPar_prefix_two_distincts_STOP)



subsection \<open>Behaviour of \<^const>\<open>MultiSync\<close> with \<^const>\<open>Sync\<close>\<close>

lemma MultiSync_Sync:
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> z \<in># M. P z) \<lbrakk>S\<rbrakk> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> z \<in># M. P' z) = \<^bold>\<lbrakk>S\<^bold>\<rbrakk> z \<in># M. (P z \<lbrakk>S\<rbrakk> P' z)\<close>
  apply (cases \<open>M = {#}\<close>, simp)
  apply (induct M rule: mset_induct_nonempty)
  by simp_all (metis (no_types, lifting) Sync_assoc Sync_commute)


lemmas MultiInter_Inter = MultiSync_Sync[where S = \<open>{}\<close>]
  and     MultiPar_Par = MultiSync_Sync[where S = \<open>UNIV\<close>]



subsection \<open>Commutativity\<close>

lemma MultiSync_sets_commute:
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># M. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> b \<in># N. P a b) = \<^bold>\<lbrakk>S\<^bold>\<rbrakk> b \<in># N. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> a \<in># M. P a b\<close>
  apply (cases \<open>N = {#}\<close>, induct M, simp_all, 
      metis MultiSync_add MultiSync_rec1 STOP_Sync_STOP)
  apply (induct N rule: mset_induct_nonempty, fastforce)
  by simp (metis MultiSync_Sync)


lemmas MultiInter_sets_commute = MultiSync_sets_commute[where S = \<open>{}\<close>]
  and   MultiPar_sets_commute = MultiSync_sets_commute[where S = \<open>UNIV\<close>]



subsection \<open>Behaviour with Injectivity\<close>

lemma inj_on_mapping_over_MultiSync:
  \<open>inj_on f (set_mset M) \<Longrightarrow> 
   (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> x \<in># M. P x) = \<^bold>\<lbrakk>S\<^bold>\<rbrakk> x \<in># image_mset f M. P (inv_into (set_mset M) f x)\<close>
proof (induct M rule: induct_subset_mset_empty_single, simp, simp)
  case (3 N a)
  hence f1: \<open>inv_into (insert a (set_mset N)) f (f a) = a\<close> by force
  show ?case
    apply (simp add: "3.hyps"(2) "3.hyps"(3) f1,
        rule arg_cong[where f = \<open>\<lambda>x. P a \<lbrakk>S\<rbrakk> x\<close>])
    apply (subst "3.hyps"(4), rule inj_on_subset[OF "3.prems"],
        simp add: subset_insertI)
    apply (rule mono_MultiSync_eq)
    using "3.prems" by fastforce
qed


lemmas inj_on_mapping_over_MultiInter =
  inj_on_mapping_over_MultiSync[where S = \<open>{}\<close>]
  and inj_on_mapping_over_MultiPar   =
  inj_on_mapping_over_MultiSync[where S = \<open>UNIV\<close>]

(*<*)
end
  (*>*)