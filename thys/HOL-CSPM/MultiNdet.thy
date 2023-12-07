(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Multi-non-deterministic choice
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


chapter \<open>The MultiNdet Operator\<close>

theory MultiNdet
  imports Patch PreliminaryWork
begin



section \<open>Definition\<close>



text \<open>Defining the multi operator of \<^const>\<open>Ndet\<close> requires more work than with \<^const>\<open>Det\<close>
      since there is no neutral element. 
      We will first build a version on \<^typ>\<open>'\<alpha> list\<close> that we will generalize to \<^typ>\<open>'\<alpha> set\<close>.\<close>

fun MultiNdet_list :: \<open>['a list, 'a \<Rightarrow> 'b process] \<Rightarrow> 'b process\<close>
  where \<open>MultiNdet_list   []    P = STOP\<close>
  |     \<open>MultiNdet_list (a # l) P = fold (\<lambda>x r. r \<sqinter> P x) l (P a)\<close> 


syntax       "_MultiNdet_list" :: \<open>[pttrn,'a set,'b process] \<Rightarrow> 'b process\<close>
                                  (\<open>(3\<Sqinter>\<^sub>l _\<in>_. / _)\<close> 76)
translations  "\<Sqinter>\<^sub>l p \<in> l. P "  \<rightleftharpoons> "CONST MultiNdet_list l (\<lambda>p. P)"


interpretation MultiNdet: comp_fun_idem where f=\<open>\<lambda>x r. r \<sqinter> P x\<close>
  unfolding comp_fun_idem_def comp_fun_commute_def
            comp_fun_idem_axioms_def comp_def
  by (metis Ndet_commute Ndet_assoc Ndet_id)


lemma MultiNdet_list_set:
  \<open>set L = set L' \<Longrightarrow> MultiNdet_list L P = MultiNdet_list L' P\<close> 
  apply (cases L, simp_all)
proof -
  fix a  l
  assume * : \<open>insert a (set l) = set L'\<close> and  ** : \<open>L = a # l\<close> 
  then obtain a' l' where *** : \<open>L' = a' # l'\<close> by (metis insertI1 list.set_cases)
  note * = *[simplified ***, simplified]
  have a0: \<open>MultiNdet_list L P =
            Finite_Set.fold (\<lambda>x r. r \<sqinter> P x) (P a) (set L - {a})\<close>
    by (metis ** List.finite_set MultiNdet.fold_fun_left_comm
              MultiNdet.fold_insert_idem2 MultiNdet.fold_rec
              MultiNdet.fold_set_fold MultiNdet_list.simps(2)
              insert_iff list.simps(15) Ndet_id set_removeAll)
  have a11: \<open>a' \<in> set L\<close>
   and a12: \<open>a \<noteq> a' \<Longrightarrow> insert a' (set L - {a, a'}) = set L - {a}\<close>
    by (auto simp add: * **)
  hence a2: \<open>Finite_Set.fold (\<lambda>x r. r \<sqinter> P x) (P a) (insert a' (set L - {a, a'})) = 
             Finite_Set.fold (\<lambda>x r. r \<sqinter> P x) (P a \<sqinter> P a') (set L - {a, a'})\<close> 
    by (subst MultiNdet.fold_insert_idem2, simp_all)
  have a3:\<open>MultiNdet_list L' P =
           Finite_Set.fold (\<lambda>x r. r \<sqinter> P x) (P a') (set L' - {a'})\<close> 
    by (metis *** List.finite_set MultiNdet.fold_fun_left_comm
              MultiNdet.fold_insert_idem2 MultiNdet.fold_rec
              MultiNdet.fold_set_fold MultiNdet_list.simps(2)
              insert_iff list.simps(15) Ndet_id set_removeAll)
  have a41: \<open>a \<in> set L'\<close>
   and a42: \<open>a \<noteq> a' \<Longrightarrow> insert a (set L' - {a, a'}) = set L' - {a'}\<close> 
    using * *** by auto
  hence a5: \<open>Finite_Set.fold (\<lambda>x r. r \<sqinter> P x) (P a') (insert a (set L' - {a, a'}))
           = Finite_Set.fold (\<lambda>x r. r \<sqinter> P x) (P a \<sqinter> P a') (set L' - {a, a'})\<close>
    by (subst MultiNdet.fold_insert_idem2, simp_all add: Ndet_commute)
  have a6: \<open>(set L - {a, a'}) = (set L' - {a, a'})\<close>
    using * ** *** by force
  from  * ** *** a0 a11 a12 a2 a3 a41 a42 a5 a6 
  show \<open>fold (\<lambda>x r. r \<sqinter> P x) l (P a) = MultiNdet_list L' P\<close>
    by (metis MultiNdet_list.simps(2) list.simps(15))
qed


definition MultiNdet :: \<open>['a set, 'a \<Rightarrow> 'b process] \<Rightarrow> 'b process\<close>
  where    \<open>MultiNdet A P = MultiNdet_list (SOME L. set L = A) P\<close> 


syntax "_MultiNdet" :: \<open>[pttrn, 'a set, 'b process] \<Rightarrow> 'b process\<close> (\<open>(3\<Sqinter> _\<in>_. / _)\<close> 76)
translations "\<Sqinter> p \<in> A. P" \<rightleftharpoons> "CONST MultiNdet A (\<lambda>p. P)"



section \<open>First Properties\<close>

lemma MultiNdet_rec0[simp]: \<open>(\<Sqinter> p \<in> {}. P p) = STOP\<close>
  by(simp add: MultiNdet_def)


lemma MultiNdet_rec1[simp]: \<open>(\<Sqinter> p \<in> {a}. P p) = P a\<close>
  unfolding MultiNdet_def apply (rule someI2[of _ \<open>[a]\<close>], simp)
  by (rule MultiNdet_list_set[where L' = \<open>[a]\<close>, simplified])

  
lemma MultiNdet_in_id[simp]:
  \<open>a \<in> A \<Longrightarrow> (\<Sqinter> p \<in> insert a A. P p) = \<Sqinter> p \<in> A. P p\<close>
  unfolding MultiNdet_def by (simp add: insert_absorb)


lemma MultiNdet_insert[simp]:
  assumes fin: \<open>finite A\<close> and notempty: \<open>A \<noteq> {}\<close> and notin: \<open>a \<notin> A\<close>
  shows \<open>(\<Sqinter> p \<in> insert a A. P p) = P a \<sqinter> (\<Sqinter> p \<in> A. P p)\<close>
  unfolding MultiNdet_def
  apply (rule someI2_ex, simp add: fin finite_list)+
proof-
  fix l l'
  assume \<open>set l = A\<close> and \<open>set l' = insert a A\<close>
  from notempty and \<open>set l = A\<close> have \<open>l \<noteq> []\<close> by fastforce
  then have \<open>MultiNdet_list (a # l) P = P a \<sqinter> MultiNdet_list l P\<close>
    proof(induct l rule: List.list_nonempty_induct)
    case (single x)
    show \<open>MultiNdet_list [a, x] P = P a \<sqinter> MultiNdet_list [x] P\<close> by simp
  next
    case (cons x xs)
    have \<open>MultiNdet_list (a # x # xs) P = P a \<sqinter> ((MultiNdet_list xs P) \<sqinter> P x)\<close>
      by (metis List.finite_set MultiNdet.fold_insert_idem MultiNdet.fold_set_fold
                MultiNdet_list.simps(2) cons.hyps(2) list.simps(15) Ndet_assoc)
    thus \<open>MultiNdet_list (a # x # xs) P = P a \<sqinter> MultiNdet_list (x # xs) P\<close>
    proof -
      have f1: \<open>MultiNdet_list (a # x # xs) P =
                Finite_Set.fold (\<lambda>a p. p \<sqinter> P a) (P x \<sqinter> P a) (set xs)\<close>
        by (simp add: MultiNdet.fold_set_fold Ndet_commute)
      have \<open>MultiNdet_list (x # xs) P =
            Finite_Set.fold (\<lambda>a p. p \<sqinter> P a) (P x) (set xs)\<close>
        by (simp add: MultiNdet.fold_set_fold)
      hence \<open>MultiNdet_list (a # x # xs) P = MultiNdet_list (x # xs) P \<sqinter> P a\<close>
        using f1 by (simp add: MultiNdet.fold_fun_left_comm)
      thus \<open>MultiNdet_list (a # x # xs) P = P a \<sqinter> MultiNdet_list (x # xs) P\<close>
        by (simp add: Ndet_commute)
    qed
  qed
  moreover have \<open>set l' = set (a # l)\<close>
    by (simp add: \<open>set l = A\<close> \<open>set l' = insert a A\<close>)
  ultimately show \<open>MultiNdet_list l' P = P a \<sqinter> MultiNdet_list l P\<close>
    by (metis MultiNdet_list_set)
qed


lemma MultiNdet_insert'[simp]:
  \<open>\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<Sqinter> p \<in> insert a A. P p) = P a \<sqinter> (\<Sqinter> p \<in> A. P p)\<close>
  apply (cases \<open>a \<in> A\<close>, subst Set.insert_absorb, simp_all)
  apply (cases \<open>A = {a}\<close>, simp add: Ndet_id)
proof -
  assume \<open>finite A\<close> and \<open>a \<in> A\<close> and \<open>A \<noteq> {a}\<close>
  then obtain A' where \<open>A' \<noteq> {}\<close> \<open>A = insert a A'\<close> \<open>a \<notin> A'\<close> \<open>finite A'\<close>
    by (metis Set.set_insert finite_insert)
  hence \<open>MultiNdet A P = P a \<sqinter> MultiNdet A' P\<close> by simp
  hence \<open>MultiNdet A P = P a \<sqinter> P a \<sqinter> MultiNdet A' P\<close> by (simp add: Ndet_id)
  thus \<open>MultiNdet A P = P a \<sqinter> MultiNdet A P\<close> by (metis Ndet_id Ndet_assoc)
qed


lemma mono_MultiNdet_eq:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x = Q x \<Longrightarrow> MultiNdet A P = MultiNdet A Q\<close>
  by (induct A rule: induct_subset_empty_single; simp)



section \<open>Some Tests\<close>

lemma \<open>(\<Sqinter>\<^sub>l p \<in> []. P p) = STOP\<close> 
  and \<open>(\<Sqinter>\<^sub>l p \<in> [a]. P p) = P a\<close> 
  and \<open>(\<Sqinter>\<^sub>l p \<in> [a, b]. P p) = P a \<sqinter> P b\<close>    
  and \<open>(\<Sqinter>\<^sub>l p \<in> [a, b, c]. P p) = P a \<sqinter> P b \<sqinter> P c\<close>   
  by auto


lemma \<open>(\<Sqinter> p \<in> {}. P p) = STOP\<close> 
  and \<open>(\<Sqinter> p \<in> {a}. P p) = P a\<close> 
  and \<open>(\<Sqinter> p \<in> {a, b}. P p) = P a \<sqinter> P b\<close>    
  and \<open>(\<Sqinter> p \<in> {a, b, c}. P p) = P a \<sqinter> P b \<sqinter> P c\<close>   
  by (simp add: Ndet_assoc)+


lemma test_MultiNdet: \<open>(\<Sqinter> p \<in> {1::int .. 3}. P p) = P 1 \<sqinter> P 2 \<sqinter> P 3\<close>
proof -
  have \<open>{1::int .. 3} = insert 1 (insert 2 (insert 3 {}))\<close> by fastforce
  thus \<open>(\<Sqinter> p \<in> {1::int .. 3}. P p) = P 1 \<sqinter> P 2 \<sqinter> P 3\<close> by (simp add: Ndet_assoc)
qed


lemma test_MultiNdet':
  \<open>(\<Sqinter> p \<in> {0::nat .. a}. P p) = (\<Sqinter> p \<in> {a} \<union> {1 .. a} \<union> {0} . P p)\<close>
  by (metis Un_insert_right atMost_atLeast0 boolean_algebra_cancel.sup0
            image_Suc_lessThan insert_absorb2 insert_is_Un lessThan_Suc 
            lessThan_Suc_atMost lessThan_Suc_eq_insert_0)



section \<open>Continuity\<close>

lemma MultiNdet_cont[simp]:
  \<open>\<lbrakk>finite A; \<forall>x \<in> A. cont (P x)\<rbrakk> \<Longrightarrow> cont (\<lambda>y. \<Sqinter> z\<in>A. P z y)\<close>
  by (cases \<open>A = {}\<close>, simp, erule finite_set_induct_nonempty; simp)



section \<open>Factorization of \<^const>\<open>Ndet\<close> in front of \<^const>\<open>MultiNdet\<close>\<close>

lemma MultiNdet_factorization_union:
  \<open>\<lbrakk>A \<noteq> {}; finite A; B \<noteq> {}; finite B\<rbrakk> \<Longrightarrow>
   (\<Sqinter> p \<in> A. P p) \<sqinter> (\<Sqinter> p \<in> B. P p) = \<Sqinter> p \<in> A \<union> B . P p\<close>
  by (erule finite_set_induct_nonempty, simp_all add: Ndet_assoc)



section \<open>\<^term>\<open>\<bottom>\<close> Absorbance\<close>

lemma MultiNdet_BOT_absorb:
  assumes fin: \<open>finite A\<close> and bot: \<open>P a = \<bottom>\<close> and dom: \<open>a \<in> A\<close> 
    shows \<open>(\<Sqinter> x \<in> A. P x) = \<bottom>\<close>
  apply(rule rev_mp[OF dom], rule rev_mp[OF bot])
  by (metis MultiNdet_insert MultiNdet_rec1 Ndet_commute fin
            finite_insert mk_disjoint_insert Ndet_BOT) 


lemma MultiNdet_is_BOT_iff:
  \<open>finite A \<Longrightarrow> (\<Sqinter> p \<in> A. P p) = \<bottom> \<longleftrightarrow> (\<exists>a \<in> A. P a = \<bottom>)\<close>
  apply (cases \<open>A = {}\<close>, simp add: STOP_neq_BOT)
  by (rotate_tac, induct A rule: finite_set_induct_nonempty) (simp_all add: Ndet_is_BOT_iff)




section \<open>First Properties\<close>

lemma MultiNdet_id: \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> (\<Sqinter> p \<in> A. P) = P\<close>
  by (erule finite_set_induct_nonempty, (simp_all add: Ndet_id))


lemma MultiNdet_STOP_id: \<open>finite A \<Longrightarrow> (\<Sqinter> p \<in> A. STOP) = STOP\<close>
  by (cases \<open>A = {}\<close>) (simp_all add: MultiNdet_id)


lemma MultiNdet_is_STOP_iff:
  \<open>finite A \<Longrightarrow> (\<Sqinter> p \<in> A. P p) = STOP \<longleftrightarrow> A = {} \<or> (\<forall>a \<in> A. P a = STOP)\<close>
  apply (cases \<open>A = {}\<close>, simp)
  by (rotate_tac, induct A rule: finite_set_induct_nonempty) (simp_all add: Ndet_is_STOP_iff)



section \<open>Behaviour of \<^const>\<open>MultiNdet\<close> with \<^const>\<open>Ndet\<close>\<close>

lemma MultiNdet_Ndet:
  \<open>finite A \<Longrightarrow> (\<Sqinter> a \<in> A. P a) \<sqinter> (\<Sqinter> a \<in> A. Q a) = \<Sqinter> a \<in> A. P a \<sqinter> Q a\<close>
  apply (cases \<open>A = {}\<close>, simp add: Ndet_id)
  apply (rotate_tac, induct A rule: finite_set_induct_nonempty)
  by simp_all (metis (no_types, lifting) Ndet_commute Ndet_assoc)



section \<open>Commutativity\<close>

lemma MultiNdet_sets_commute: 
  \<open>\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow>
   (\<Sqinter> a \<in> A. \<Sqinter> b \<in> B. P a b) = \<Sqinter> b \<in> B. \<Sqinter> a \<in> A. P a b\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>finite A \<Longrightarrow> finite B \<Longrightarrow> A = {} \<Longrightarrow> 
        (\<Sqinter> a\<in>A.  MultiNdet B (P a)) = \<Sqinter> b\<in>B.  \<Sqinter> a\<in>A.  P a b\<close>
    by (simp add: MultiNdet_STOP_id)
next 
  assume \<open>A \<noteq> {}\<close> and \<open>finite A\<close> and \<open>finite B\<close>
  thus \<open>(\<Sqinter> a\<in>A.  MultiNdet B (P a)) = \<Sqinter> b\<in>B.  \<Sqinter> a\<in>A.  P a b\<close>
    apply (induct A rule: finite_set_induct_nonempty)
    by (simp_all add: MultiNdet_Ndet)
qed



section \<open>Behaviour with Injectivity\<close>

lemma inj_on_mapping_over_MultiNdet:
  \<open>\<lbrakk>finite A; inj_on f A\<rbrakk> \<Longrightarrow> (\<Sqinter> x \<in> A. P x) = \<Sqinter> x \<in> f ` A. P (inv_into A f x)\<close>
proof (induct A rule: induct_subset_empty_single)
  show \<open>MultiNdet {} P = \<Sqinter> x\<in>f ` {}.  P (inv_into {} f x)\<close> by force
next
  case 2
  show ?case by force
next
  case (3 F a)
  hence f1: \<open>inv_into (insert a F) f (f a) = a\<close> by force
  show ?case
    apply (simp add: "3.hyps"(2) "3.hyps"(4) f1)
    apply (rule arg_cong[where f = \<open>\<lambda>x. P a \<sqinter> x\<close>])
    apply (subst "3.hyps"(5), rule inj_on_subset[OF "3.prems" subset_insertI])
    apply (rule mono_MultiNdet_eq, simp add: "3.hyps"(2))
    using "3.prems" by fastforce
qed



section \<open>The Projections\<close>

lemma D_MultiNdet: \<open>finite A \<Longrightarrow> \<D> (\<Sqinter> x \<in> A. P x) = (\<Union> p \<in> A. \<D> (P p))\<close>
  apply (cases \<open>A = {}\<close>, simp add: D_STOP, rotate_tac)
  by (induct rule: finite_set_induct_nonempty) (simp_all add: D_Ndet)

lemma F_MultiNdet:
  \<open>finite A \<Longrightarrow> \<F> (\<Sqinter> x \<in> A. P x) =
                (if A = {} then {(s, X). s = []} else \<Union> p \<in> A. \<F> (P p))\<close>
  apply (simp add: F_STOP, intro impI, rotate_tac)
  by (induct rule: finite_set_induct_nonempty) (simp_all add: F_Ndet)

lemma T_MultiNdet:
  \<open>finite A \<Longrightarrow> \<T> (\<Sqinter> x \<in> A. P x) =
                (if A = {} then {[]} else \<Union> p \<in> A. \<T> (P p))\<close>
  apply (simp add: T_STOP, intro impI, rotate_tac)
  by (induct rule: finite_set_induct_nonempty) (simp_all add: T_Ndet)



section \<open>Cartesian Product Results\<close>

lemma MultiNdet_cartprod_\<sigma>s_set_\<sigma>s_set:
  (*we can't remove hypothesis on len\<^sub>1 in this proof for injectivity*)
  \<open>\<lbrakk>finite A; finite B; \<forall>s \<in> A. length s = len\<^sub>1\<rbrakk> \<Longrightarrow> 
   (\<Sqinter> (s, t) \<in> A \<times> B. P (s @ t)) = \<Sqinter> u \<in> {s @ t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst inj_on_mapping_over_MultiNdet[where f = \<open>\<lambda> (s, t). s @ t\<close>],
         simp_all add: inj_on_def)
  apply (subst prem_Multi_cartprod(1)[simplified, symmetric])
  apply (rule mono_MultiNdet_eq, simp add: finite_image_set2)
  by (metis (no_types, lifting) case_prod_unfold f_inv_into_f)


lemma MultiNdet_cartprod_s_set_\<sigma>s_set:
  \<open>\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow>
   (\<Sqinter> (s, t) \<in> A \<times> B. P (s # t)) = \<Sqinter> u \<in> {s # t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst inj_on_mapping_over_MultiNdet[where f = \<open>\<lambda> (s, t). s # t\<close>],
         simp_all add: inj_on_def) 
  apply (subst prem_Multi_cartprod(2)[simplified, symmetric])
  apply (rule mono_MultiNdet_eq, simp add: finite_image_set2)
  by (metis (no_types, lifting) case_prod_unfold f_inv_into_f)


lemma MultiNdet_cartprod_s_set_s_set:
  \<open>\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow>
   (\<Sqinter> (s, t) \<in> A \<times> B. P [s, t]) = \<Sqinter> u \<in> {[s, t] |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst inj_on_mapping_over_MultiNdet[where f = \<open>\<lambda> (s, t). [s, t]\<close>],
         simp_all add: inj_on_def) 
  apply (subst prem_Multi_cartprod(3)[simplified, symmetric])
  apply (rule mono_MultiNdet_eq, simp add: finite_image_set2)
  by (metis (no_types, lifting) case_prod_unfold f_inv_into_f)


lemma MultiNdet_cartprod: 
  \<open>\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> (\<Sqinter> (s, t) \<in> A \<times> B. P s t) = \<Sqinter> s\<in>A. \<Sqinter> t\<in>B. P s t\<close>
  supply arg_cong_Ndet = arg_cong[where f = \<open>\<lambda>Q. _ \<sqinter> Q\<close>]
proof (induct \<open>card A\<close> arbitrary: A B rule: nat_less_induct)
  case (1 A B)
  from \<open>finite A\<close> \<open>finite B\<close> consider \<open>A = {}\<close> | \<open>B = {}\<close> | 
      \<open>\<exists>mA mB a b A' B'. A = insert a A' \<and> B = insert b B' \<and> mA = card A' \<and> 
                         mB = card B' \<and> mA < card A \<and> mB < card B\<close> 
    by (metis card_Diff1_less_iff ex_in_conv insert_Diff)
  thus \<open>(\<Sqinter>(x, y) \<in> A \<times> B.  P x y) = \<Sqinter> s\<in>A.  MultiNdet B (P s)\<close>
  proof cases
    show \<open>A = {} \<Longrightarrow> (\<Sqinter> (x, y)\<in>A \<times> B. P x y) = \<Sqinter> s\<in>A. MultiNdet B (P s)\<close>
      by simp
  next 
    show \<open>B = {} \<Longrightarrow> (\<Sqinter> (x, y)\<in>A \<times> B. P x y) = \<Sqinter> s\<in>A. MultiNdet B (P s)\<close>
      by (simp add: MultiNdet_STOP_id[OF "1.prems"(1)])
  next
    assume \<open>\<exists>mA mB a b A' B'. A = insert a A' \<and> B = insert b B' \<and> 
            mA = card A' \<and> mB = card B' \<and> mA < card A \<and> mB < card B\<close>
    then obtain mA mB a b A' B'
      where * : \<open>A = insert a A'\<close> \<open>B = insert b B'\<close> \<open>mA = card A'\<close>
                \<open>mB = card B'\<close> \<open>mA < card A\<close> \<open>mB < card B\<close> by blast
    have **  : \<open>Pair a ` B' = {a} \<times> B'\<close>
     and *** : \<open>(\<lambda>a. (a, b)) ` A' = A' \<times> {b}\<close> unfolding image_def by blast+
    show \<open>(\<Sqinter>(x, y) \<in> A \<times> B.  P x y) = \<Sqinter> s\<in>A.  MultiNdet B (P s)\<close>
      using "*"(1, 2) \<open>finite A\<close> \<open>finite B\<close>
      apply (cases \<open>A' = {}\<close>; cases \<open>B' = {}\<close>; simp_all)
        apply (rule arg_cong_Ndet)
        apply (subst inj_on_mapping_over_MultiNdet[of B' \<open>\<lambda>b. (a, b)\<close>],
               simp_all add: inj_on_def "**")
        apply (rule mono_MultiNdet_eq, simp_all)
        apply (metis Pair_inject f_inv_into_f image_eqI)
       apply (rule arg_cong_Ndet)
       apply (subst inj_on_mapping_over_MultiNdet[of A' \<open>\<lambda>a. (a, b)\<close>],
              simp_all add: inj_on_def "***")
       apply (rule mono_MultiNdet_eq, simp_all)
       apply (metis (no_types, lifting) f_inv_into_f image_eqI prod.inject)

      apply (subst MultiNdet_factorization_union[symmetric], simp_all)
      apply (subst "1"(1)[rule_format, OF "*"(5, 3)], simp_all)
      apply (simp add: MultiNdet_Ndet[symmetric])
      apply (subst Ndet_assoc, rule arg_cong_Ndet)
      apply (subst (3) Ndet_commute, rule arg_cong_Ndet)
      apply (subst inj_on_mapping_over_MultiNdet[of B' \<open>\<lambda>b. (a, b)\<close>],
             simp_all add: inj_on_def "**")
      apply (rule mono_MultiNdet_eq)
       apply (simp; fail)
      by (metis "**" case_prod_conv f_inv_into_f)
  qed
qed



end