(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Multi-deterministic choice
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


chapter \<open>The MultiDet Operator\<close>

theory MultiDet
  imports Patch PreliminaryWork
begin



section \<open>Definition\<close>


definition  MultiDet :: \<open>['a set, 'a \<Rightarrow> 'b process] \<Rightarrow> 'b process\<close>
  where    \<open>MultiDet A P = Finite_Set.fold (\<lambda>a r. r \<box> P a) STOP A\<close>

(* Unfortunately, we don't have a big \<box> in jedit *)
syntax "_MultiDet" :: \<open>[pttrn, 'a set, 'b process] \<Rightarrow> 'b process\<close>  (\<open>(3\<^bold>\<box>_\<in>_. / _)\<close> 75)
translations "\<^bold>\<box> p \<in> A. P"  \<rightleftharpoons>  "CONST MultiDet A (\<lambda>p. P)"



section \<open>First Properties\<close>

lemma MultiDet_rec0[simp]: \<open>(\<^bold>\<box> p \<in> {}. P p) = STOP\<close>
  by(simp add: MultiDet_def)

lemma MultiDet_rec1[simp]: \<open>(\<^bold>\<box> p \<in> {a}. P p) = P a\<close>
  unfolding MultiDet_def
  apply (subst comp_fun_commute_on.fold_insert_remove[where S = \<open>{a}\<close>])
  by (simp_all add: comp_fun_commute_on_def
                    Det_commute[of \<open>STOP\<close>, simplified Det_STOP])


lemma MultiDet_in_id[simp]:
  \<open>a \<in> A \<Longrightarrow> (\<^bold>\<box> p \<in> insert a A. P p) = \<^bold>\<box> p \<in> A. P p\<close>
  unfolding MultiDet_def by (simp add: insert_absorb)


lemma MultiDet_insert[simp]:
  \<open>finite A \<Longrightarrow> (\<^bold>\<box> p \<in> insert a A. P p) = P a \<box> (\<^bold>\<box> p \<in> A - {a}. P p)\<close>
  unfolding MultiDet_def
  apply (subst comp_fun_commute_on.fold_insert_remove[where S = \<open>insert a A\<close>])
  unfolding comp_fun_commute_on_def comp_def
     apply (metis Det_assoc Det_commute)
  by (auto simp: comp_fun_commute_on_def Det_commute Det_assoc comp_def)


lemma MultiDet_insert'[simp]:
  \<open>finite A \<Longrightarrow> (\<^bold>\<box> p \<in> insert a A. P p) = (P a \<box> (\<^bold>\<box> p \<in> A. P p))\<close>
  by (cases \<open>a \<in> A\<close>, metis MultiDet_insert Det_assoc Det_id insert_absorb, simp)


lemma mono_MultiDet_eq:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x = Q x \<Longrightarrow> MultiDet A P = MultiDet A Q\<close>
  by (induct A rule: induct_subset_empty_single, simp, simp)
     (metis MultiDet_insert' insertCI)



section \<open>Some Tests\<close>

lemma test_MultiDet: \<open>(\<^bold>\<box> p \<in> {1::int .. 3}. P p) = P 1 \<box> P 2 \<box> P 3\<close> 
proof -
  have \<open>{1::int .. 3} = insert 1 (insert 2 (insert 3 {}))\<close> by fastforce
  thus \<open>(\<^bold>\<box> p \<in> {1::int .. 3}. P p) = P 1 \<box> P 2 \<box> P 3\<close> by (simp add: Det_assoc)
qed


lemma test_MultiDet':
  \<open>(\<^bold>\<box> p \<in> {0::nat .. a}. P p) = (\<^bold>\<box> p \<in> {a} \<union> {1 .. a} \<union> {0} . P p)\<close>
  by (metis Un_insert_right atMost_atLeast0 boolean_algebra_cancel.sup0
            image_Suc_lessThan insert_absorb2 insert_is_Un lessThan_Suc
            lessThan_Suc_atMost lessThan_Suc_eq_insert_0)



section \<open>Continuity\<close>

lemma MultiDet_cont[simp]:
  \<open>\<lbrakk>finite A; \<forall>x \<in> A. cont (P x)\<rbrakk> \<Longrightarrow> cont (\<lambda>y. \<^bold>\<box> z\<in>A. P z y)\<close>
  by (rule Finite_Set.finite_subset_induct[of A A], simp+)



section \<open>Factorization of \<^const>\<open>Det\<close> in front of \<^const>\<open>MultiDet\<close>\<close>

lemma MultiDet_factorization_union:
  \<open>\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> (\<^bold>\<box> p \<in> A. P p) \<box> (\<^bold>\<box> p \<in> B. P p) = \<^bold>\<box> p \<in> A \<union> B . P p\<close>
  apply (erule finite_induct, simp_all)
  by (metis Det_commute Det_STOP)
     (metis MultiDet_insert MultiDet_insert' Det_assoc finite_UnI)



section \<open>\<^term>\<open>\<bottom>\<close> Absorbance\<close>

lemma MultiDet_BOT_absorb:
  assumes fin: \<open>finite A\<close> and bot: \<open>P a = \<bottom>\<close> and dom: \<open>a \<in> A\<close> 
  shows \<open>(\<^bold>\<box> x \<in> A. P x) = \<bottom>\<close>
  apply(rule rev_mp[OF dom], rule rev_mp[OF bot]) 
  by (metis Det_commute MultiDet_insert' Det_BOT fin insert_absorb)


lemma MultiDet_is_BOT_iff:
  \<open>finite A \<Longrightarrow> MultiDet A P = \<bottom> \<longleftrightarrow> (\<exists>a \<in> A. P a = \<bottom>)\<close>
  by (induct A rule: finite_induct) (auto simp add: STOP_neq_BOT Det_is_BOT_iff)



section \<open>First Properties\<close>

lemma MultiDet_id: \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> (\<^bold>\<box>p \<in> A. P) = P\<close>
  by (erule finite_set_induct_nonempty, simp_all add: Det_id)


lemma MultiDet_STOP_id: \<open>finite A \<Longrightarrow> (\<^bold>\<box>p \<in> A. STOP) = STOP\<close> 
  by (cases \<open>A = {}\<close>) (simp_all add: MultiDet_id)


lemma MultiDet_STOP_neutral:
  \<open>finite A \<Longrightarrow> P a = STOP \<Longrightarrow> (\<^bold>\<box> z \<in> insert a A. P z) = \<^bold>\<box> z \<in> A. P z\<close>
  by (metis Det_commute MultiDet_insert' Det_STOP)


lemma MultiDet_is_STOP_iff:
  \<open>finite A \<Longrightarrow> (\<^bold>\<box> a \<in> A. P a) = STOP \<longleftrightarrow> A = {} \<or> (\<forall>a \<in> A. P a = STOP)\<close>
  by (induct rule: finite_induct) (auto simp add: Det_is_STOP_iff)



section \<open>Behaviour of \<^const>\<open>MultiDet\<close> with \<^const>\<open>Det\<close>\<close>

lemma MultiDet_Det:
  \<open>finite A \<Longrightarrow> (\<^bold>\<box> a \<in> A. P a) \<box> (\<^bold>\<box> a \<in> A. Q a) = \<^bold>\<box> a \<in> A. P a \<box> Q a\<close>
proof (induct A rule: finite_induct)
  case empty show ?case by (simp add: Det_id)
next
  case (insert x F)
  hence \<open>MultiDet (insert x F) P \<box> MultiDet (insert x F) Q =
         P x \<box> MultiDet F P \<box> Q x \<box> MultiDet F Q\<close> by (simp add: Det_assoc)
  also have \<open>\<dots> = (P x \<box> Q x) \<box> (\<^bold>\<box> a\<in>F.  P a \<box> Q a)\<close>
    by (metis (no_types, lifting) Det_assoc Det_commute insert.hyps(3))
  ultimately show \<open>MultiDet (insert x F) P \<box> MultiDet (insert x F) Q = 
                   (\<^bold>\<box> a\<in>insert x F.  P a \<box> Q a)\<close>
    by (simp add: \<open>finite F\<close> \<open>x \<notin> F\<close>)
qed



section \<open>Commutativity\<close>

lemma MultiDet_sets_commute:
  \<open>\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> (\<^bold>\<box> a \<in> A. \<^bold>\<box> b \<in> B. P a b) = \<^bold>\<box> b \<in> B. \<^bold>\<box> a \<in> A. P a b\<close>
  by (induct A rule: finite_induct) (simp_all add: MultiDet_STOP_id MultiDet_Det)



section \<open>Behaviour with Injectivity\<close>

lemma inj_on_mapping_over_MultiDet:
  \<open>\<lbrakk>finite A; inj_on f A\<rbrakk> \<Longrightarrow> (\<^bold>\<box> x \<in> A. P x) = \<^bold>\<box> x \<in> f ` A. P (inv_into A f x)\<close>
proof (induct A rule: induct_subset_empty_single)
  case 1
  thus ?case by force
next
  case 2
  thus ?case by force
next
  case (3 F a)
  hence f1: \<open>inv_into (insert a F) f (f a) = a\<close> by force
  show ?case
    apply (simp add: "3.hyps"(2) "3.hyps"(4) f1 del: MultiDet_insert)
    apply (rule arg_cong[where f = \<open>\<lambda>x. P a \<box> x\<close>])
    apply (subst "3.hyps"(5), rule inj_on_subset[OF "3.prems" subset_insertI])
    apply (rule mono_MultiDet_eq, simp add: "3.hyps"(2))
    using "3.prems" by fastforce
qed



section \<open>The Projections\<close>

lemma D_MultiDet: \<open>finite A \<Longrightarrow> \<D> (\<^bold>\<box> x \<in> A. P x) = (\<Union> p \<in> A. \<D> (P p))\<close>
  by (induct rule: finite_induct) (simp_all add: D_Det D_STOP)

lemma T_MultiDet:
  \<open>finite A \<Longrightarrow> \<T> (\<^bold>\<box> x \<in> A. P x) = (if A = {} then {[]} else \<Union> p \<in> A. \<T> (P p))\<close>
  apply (simp add: T_STOP, intro impI, rotate_tac)
  by (induct rule: finite_set_induct_nonempty) (simp_all add: T_Det T_STOP)



section \<open>Cartesian Product Results\<close>

lemma MultiDet_cartprod_\<sigma>s_set_\<sigma>s_set:
  (*we can't remove hypothesis on len\<^sub>1 for injectivity*)
  \<open>\<lbrakk>finite A; finite B; \<forall>s \<in> A. length s = len\<^sub>1\<rbrakk> \<Longrightarrow> 
   (\<^bold>\<box> (s, t) \<in> A \<times> B. P (s @ t)) = \<^bold>\<box> u \<in> {s @ t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst inj_on_mapping_over_MultiDet[where f = \<open>\<lambda> (s, t). s @ t\<close>],
         simp_all add: inj_on_def)
  apply (subst prem_Multi_cartprod(1)[simplified, symmetric])
  apply (rule mono_MultiDet_eq, simp add: finite_image_set2)
  by (metis (no_types, lifting) case_prod_unfold f_inv_into_f)


lemma MultiDet_cartprod_s_set_\<sigma>s_set:
  \<open>\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow>
   (\<^bold>\<box> (s, t) \<in> A \<times> B. P (s # t)) = \<^bold>\<box> u \<in> {s # t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst inj_on_mapping_over_MultiDet[where f = \<open>\<lambda> (s, t). s # t\<close>],
         simp_all add: inj_on_def) 
  apply (subst prem_Multi_cartprod(2)[simplified, symmetric])
  apply (rule mono_MultiDet_eq, simp add: finite_image_set2)
  by (metis (no_types, lifting) case_prod_unfold f_inv_into_f)


lemma MultiDet_cartprod_s_set_s_set:
  \<open>\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow>
   (\<^bold>\<box> (s, t) \<in> A \<times> B. P [s, t]) = \<^bold>\<box> u \<in> {[s, t] |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst inj_on_mapping_over_MultiDet[where f = \<open>\<lambda> (s, t). [s, t]\<close>],
         simp_all add: inj_on_def) 
  apply (subst prem_Multi_cartprod(3)[simplified, symmetric])
  apply (rule mono_MultiDet_eq, simp add: finite_image_set2)
  by (metis (no_types, lifting) case_prod_unfold f_inv_into_f)


lemma MultiDet_cartprod: 
  \<open>finite A \<Longrightarrow> finite B \<Longrightarrow> (\<^bold>\<box> (s, t) \<in> A \<times> B. P s t) = \<^bold>\<box> s\<in>A. \<^bold>\<box> t\<in>B. P s t\<close>
  supply arg_cong_Det = arg_cong[where f = \<open>\<lambda>Q. _ \<box> Q\<close>]
  supply MultiDet_insert[simp del]
proof (induct \<open>card A\<close> arbitrary: A B rule: nat_less_induct)
  case (1 A B)
  from \<open>finite A\<close> \<open>finite B\<close> consider \<open>A = {}\<close> | \<open>B = {}\<close> | 
      \<open>\<exists>mA mB a b A' B'. A = insert a A' \<and> B = insert b B' \<and> mA = card A' \<and> 
                         mB = card B' \<and> mA < card A \<and> mB < card B\<close> 
    by (metis card_Diff1_less_iff ex_in_conv insert_Diff)
  thus \<open>(\<^bold>\<box>(x, y)\<in>A \<times> B.  P x y) = \<^bold>\<box>s\<in>A.  MultiDet B (P s)\<close>
  proof cases
    show \<open>A = {} \<Longrightarrow> (\<^bold>\<box>(x, y)\<in>A \<times> B. P x y) = \<^bold>\<box>s\<in>A. MultiDet B (P s)\<close>
      by simp
  next
    show \<open>B = {} \<Longrightarrow> (\<^bold>\<box>(x, y)\<in>A \<times> B. P x y) = \<^bold>\<box>s\<in>A. MultiDet B (P s)\<close>
      by (simp add: MultiDet_STOP_id[OF "1.prems"(1)])
  next
    assume \<open>\<exists>mA mB a b A' B'. A = insert a A' \<and> B = insert b B' \<and> 
            mA = card A' \<and> mB = card B' \<and> mA < card A \<and> mB < card B\<close>
    then obtain mA mB a b A' B'
      where * : \<open>A = insert a A'\<close> \<open>B = insert b B'\<close> \<open>mA = card A'\<close>
                \<open>mB = card B'\<close> \<open>mA < card A\<close> \<open>mB < card B\<close> by blast
    have ** : \<open>Pair a ` B' = {a} \<times> B'\<close> unfolding image_def by blast
    show \<open>(\<^bold>\<box>(x, y)\<in>A \<times> B.  P x y) = \<^bold>\<box>s\<in>A.  MultiDet B (P s)\<close>
      using "*"(1, 2) \<open>finite A\<close> \<open>finite B\<close> apply simp
      apply (subst MultiDet_factorization_union[symmetric], simp_all)
      apply (subst "1"(1)[rule_format, OF "*"(5, 3)], simp_all)
      apply (simp add: MultiDet_Det[symmetric])
      apply (subst Det_assoc, rule arg_cong_Det)
      apply (subst (3) Det_commute, rule arg_cong_Det)
      apply (subst inj_on_mapping_over_MultiDet[of B' \<open>\<lambda>b. (a, b)\<close>],
             simp_all add: inj_on_def "**")
      apply (rule mono_MultiDet_eq)
       apply (simp; fail)
      by (metis "**" case_prod_conv f_inv_into_f)
  qed
qed



end