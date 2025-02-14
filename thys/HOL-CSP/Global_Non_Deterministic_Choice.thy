(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Global non deterministic choice
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


chapter\<open> The Global non Deterministic Choice \<close>

(*<*)
theory Global_Non_Deterministic_Choice
  imports Constant_Processes Deterministic_Choice
    Non_Deterministic_Choice Multi_Non_Deterministic_Prefix_Choice
begin 
  (*>*)

section\<open> General non Deterministic Choice Definition\<close>

text\<open> This is an experimental definition of a generalized non deterministic choice  \<^term>\<open>a \<sqinter> b\<close>
for an arbitrary set. The present version is ``totalised'' for the case of \<^term>\<open>A = {}\<close> by
\<^const>\<open>STOP\<close>, which is not the neutral element of the \<^const>\<open>Ndet\<close> operator (because
there is no neutral element for \<^const>\<open>Ndet\<close>).\<close>

lemma \<open>\<nexists>P. \<forall>Q. (P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<sqinter> Q = Q\<close>
proof (rule ccontr, simp, elim exE)
  fix P
  assume * : \<open>\<forall>Q. (P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<sqinter> Q = Q\<close>
  hence \<open>P = STOP\<close>
    by (erule_tac x = STOP in allE) (auto simp add: STOP_iff_T T_Ndet T_STOP)
  with * show False
    apply (erule_tac x = \<open>SKIP undefined\<close> in allE) 
    apply (simp add: Process_eq_spec F_STOP F_Ndet F_SKIP set_eq_iff)
    by (metis UNIV_I not_Cons_self)
qed



lift_definition GlobalNdet :: \<open>['b set, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda>A P.   if A = {} 
            then ({(s, X). s = []}, {})
            else (\<Union>a\<in>A. \<F> (P a), \<Union>a\<in>A. \<D> (P a))\<close>
proof (split if_split, intro conjI impI)
  show \<open>is_process ({(s, X). s = []}, {})\<close> by (metis STOP.rsp eq_onp_def)
next
  show \<open>is_process (\<Union>a\<in>A. \<F> (P a), \<Union>a\<in>A. \<D> (P a))\<close> (is \<open>is_process (?f, ?d)\<close>)
    if \<open>A \<noteq> {}\<close> for P :: \<open>'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and A
  proof (unfold is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv,
      intro conjI impI allI)
    from \<open>A \<noteq> {}\<close> is_processT1 show \<open>([], {}) \<in> ?f\<close> by blast
  next
    from is_processT2 show \<open>(s, X) \<in> ?f \<Longrightarrow> ftF s\<close> for s X by blast
  next
    from is_processT3 show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t by blast
  next
    from is_processT4 show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y by blast
  next
    from is_processT5
    show \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f)
          \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for s X Y by simp blast
  next
    from is_processT6
    show \<open>(s @ [\<checkmark>(r)], {}) \<in> ?f \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> ?f\<close> for s r X by fast
  next
    from is_processT7 show \<open>s \<in> ?d \<and> tF s \<and> ftF t \<Longrightarrow> s @ t \<in> ?d\<close> for s t by blast
  next
    from is_processT8 show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X by blast
  next
    from is_processT9 show \<open>s @ [\<checkmark>(r)] \<in> ?d \<Longrightarrow> s \<in> ?d\<close> for s r by fast
  qed
qed


syntax "_GlobalNdet" :: \<open>[pttrn,'b set,('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3\<sqinter>((_)/\<in>(_))./ (_))\<close> [78,78,77] 77)
syntax_consts "_GlobalNdet" == GlobalNdet
translations  "\<sqinter> a \<in> A. P " \<rightleftharpoons> "CONST GlobalNdet A (\<lambda>a. P)"

text\<open>Note that the global non deterministic choice @{term [eta_contract = false] \<open>\<sqinter> a \<in> A. P a\<close>}
     is different from the multiple non deterministic prefix choice which guarantees continuity 
     even when \<^term>\<open>A\<close> is \<^const>\<open>infinite\<close> due to the fact that it communicates
     its choice via an internal prefix operator.\<close>


section \<open>The projections\<close>

lemma F_GlobalNdet:
  \<open>\<F> (\<sqinter> a \<in> A. P a) = (if A = {} then {(s, X). s = []} else (\<Union> a\<in>A. \<F> (P a)))\<close>
  by (simp add: Failures.rep_eq FAILURES_def GlobalNdet.rep_eq)

lemma D_GlobalNdet: \<open>\<D> (\<sqinter> a \<in> A. P a) = (\<Union> a\<in>A. \<D> (P a))\<close>
  by (simp add: Divergences.rep_eq DIVERGENCES_def GlobalNdet.rep_eq)

lemma T_GlobalNdet:
  \<open>\<T> (\<sqinter> a \<in> A. P a) = (if A = {} then {[]} else (\<Union> a\<in>A. \<T> (P a)))\<close>
  by (auto simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] 
      F_GlobalNdet intro: F_T T_F)

lemma T_GlobalNdet': \<open>\<T> (\<sqinter> a \<in> A. P a) = insert [] (\<Union> a\<in>A. \<T> (P a))\<close>
  by (simp add: T_GlobalNdet)
    (metis T_GlobalNdet insert_absorb is_processT1_TR)

lemmas GlobalNdet_projs = F_GlobalNdet D_GlobalNdet T_GlobalNdet'


lemma mono_GlobalNdet_eq:
  \<open>(\<And>a. a \<in> A \<Longrightarrow> P a = Q a) \<Longrightarrow> GlobalNdet A P = GlobalNdet A Q\<close>
  by (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)

lemma mono_GlobalNdet_eq2:
  \<open>(\<And>a. a \<in> A \<Longrightarrow> P (f a) = Q a) \<Longrightarrow> GlobalNdet (f ` A) P = GlobalNdet A Q\<close>
  by (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)




section \<open>Factorization of \<^const>\<open>Ndet\<close> in front of \<^const>\<open>GlobalNdet\<close>\<close>

lemma GlobalNdet_factorization_union:
  \<open>\<lbrakk>A \<noteq> {}; B \<noteq> {}\<rbrakk> \<Longrightarrow>
   (\<sqinter> p \<in> A. P p) \<sqinter> (\<sqinter> p \<in> B. P p) = (\<sqinter> p \<in> (A \<union> B) . P p)\<close>
  by (subst Process_eq_spec) (simp add: F_GlobalNdet D_GlobalNdet F_Ndet D_Ndet)

lemma GlobalNdet_Union :
  \<open>(\<sqinter>a \<in> (\<Union>i \<in> I. A i). P a) = \<sqinter>i \<in> {i \<in> I. A i \<noteq> {}}. \<sqinter>a \<in> A i. P a\<close>
  by (auto simp add: Process_eq_spec GlobalNdet_projs)


section \<open>First properties\<close>

lemma GlobalNdet_id [simp] : \<open>A \<noteq> {} \<Longrightarrow> (\<sqinter> p \<in> A. P) = P\<close>
  by (subst Process_eq_spec) (simp add: F_GlobalNdet D_GlobalNdet)


lemma GlobalNdet_unit[simp] : \<open>(\<sqinter> x \<in> {a}. P x) = P a\<close> 
  by(auto simp : Process_eq_spec F_GlobalNdet D_GlobalNdet)


lemma GlobalNdet_distrib_unit:
  \<open>A - {a} \<noteq> {} \<Longrightarrow> (\<sqinter> x \<in> insert a A. P x) = P a \<sqinter> (\<sqinter> x \<in> (A - {a}). P x)\<close>
  by (metis GlobalNdet_factorization_union GlobalNdet_unit 
      empty_not_insert insert_Diff_single insert_is_Un)

lemma GlobalNdet_distrib_unit_bis : 
  \<open>(\<sqinter> x \<in> insert a A. P x) = (if A - {a} = {} then P a else P a \<sqinter> (\<sqinter> x \<in> (A - {a}). P x))\<close>
  by (metis GlobalNdet_distrib_unit GlobalNdet_unit insert_Diff_single)



section \<open>Behaviour of \<^const>\<open>GlobalNdet\<close> with \<^const>\<open>Ndet\<close>\<close>

lemma GlobalNdet_Ndet:
  \<open>(\<sqinter> a \<in> A. P a) \<sqinter> (\<sqinter> a \<in> A. Q a) = \<sqinter> a \<in> A. P a \<sqinter> Q a\<close>
  by (auto simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet F_Ndet D_Ndet)



section \<open>Commutativity\<close>

lemma GlobalNdet_sets_commute:
  \<open>(\<sqinter> a \<in> A. \<sqinter> b \<in> B. P a b) = \<sqinter> b \<in> B. \<sqinter> a \<in> A. P a b\<close>
  by (auto simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet)



section \<open>Behaviour with injectivity\<close>

lemma inj_on_mapping_over_GlobalNdet: 
  \<open>inj_on f A \<Longrightarrow> (\<sqinter> x \<in> A. P x) = \<sqinter> x \<in> f ` A. P (inv_into A f x)\<close>
  by (simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet)






section \<open>Cartesian product results\<close>

lemma GlobalNdet_cartprod_\<sigma>s_set_\<sigma>s_set:
  \<open>(\<sqinter> (s, t) \<in> A \<times> B. P (s @ t)) = \<sqinter> u \<in> {s @ t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)
  by safe auto


lemma GlobalNdet_cartprod_s_set_\<sigma>s_set:
  \<open>(\<sqinter> (s, t) \<in> A \<times> B. P (s # t)) = \<sqinter> u \<in> {s # t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)
  by safe auto


lemma GlobalNdet_cartprod_s_set_s_set:
  \<open>(\<sqinter> (s, t) \<in> A \<times> B. P [s, t]) = \<sqinter> u \<in> {[s, t] |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)
  by safe auto


lemma GlobalNdet_cartprod: \<open>(\<sqinter>(s, t) \<in> A \<times> B. P s t) = \<sqinter>s \<in> A. \<sqinter>t \<in> B. P s t\<close>
  apply (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)
  by safe auto



(* section \<open>Link with \<^const>\<open>MultiNdet\<close>\<close>

text \<open>This operator is in fact an extension of \<^const>\<open>MultiNdet\<close> to arbitrary sets:
      when \<^term>\<open>A\<close> is \<^const>\<open>finite\<close>, we have
      @{term [eta_contract = false] \<open>(\<sqinter>a \<in> A. P a) = \<Sqinter>a \<in> A. P a\<close>}.\<close>

lemma finite_GlobalNdet_is_MultiNdet:
  \<open>finite A \<Longrightarrow> (\<sqinter> p \<in> A. P p) = \<Sqinter> p \<in> A. P p\<close>
  by (simp add: Process_eq_spec F_GlobalNdet F_MultiNdet D_GlobalNdet D_MultiNdet)


text \<open>We obtain immediately the continuity when \<^term>\<open>A\<close> is \<^const>\<open>finite\<close>
      (and this is a necessary hypothesis for continuity).\<close>

lemma GlobalNdet_cont[simp]:
  \<open>\<lbrakk>finite A; \<forall>x. cont (f x)\<rbrakk> \<Longrightarrow> cont (\<lambda>y. (\<sqinter> z \<in> A. (f z y)))\<close>
  by (simp add: finite_GlobalNdet_is_MultiNdet)  *)



section \<open>Link with \<^const>\<open>Mndetprefix\<close>\<close>

text \<open>This is a trick to make proof of \<^const>\<open>Mndetprefix\<close> using
      \<^const>\<open>GlobalNdet\<close> as it has an easier denotational definition.\<close>

lemma Mndetprefix_GlobalNdet: \<open>\<sqinter> a \<in> A \<rightarrow> P a = \<sqinter> a \<in> A. a \<rightarrow> P a\<close>
  by (cases \<open>A = {}\<close>; subst Process_eq_spec_optimized) 
    (simp_all add: F_Mndetprefix D_Mndetprefix F_GlobalNdet D_GlobalNdet)

lemma write0_GlobalNdet:
  \<open>x \<rightarrow> \<sqinter> a \<in> A. P a = (if A = {} then x \<rightarrow> STOP else \<sqinter> a \<in> A. x \<rightarrow> P a)\<close>
  by (auto simp add: Process_eq_spec write0_def STOP_projs
      F_GlobalNdet D_GlobalNdet F_Mprefix D_Mprefix)

lemma ndet_write_is_GlobalNdet_write0 :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a = \<sqinter>b\<in>c ` A. b \<rightarrow> P (inv_into A c b)\<close>
  by (simp add: ndet_write_def Mndetprefix_GlobalNdet)

lemma ndet_write_is_GlobalNdet_write :
  \<open>inj_on c A \<Longrightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a = \<sqinter>a\<in>A. c\<^bold>!a \<rightarrow> P a\<close>
  by (auto simp add: ndet_write_is_GlobalNdet_write0 write_def write0_def
      intro: mono_GlobalNdet_eq2)


(* lemma Mndetprefix_Mprefix_Sync_distr:
  \<open>\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk> (\<box> b \<in> B \<rightarrow> Q b) =
                      \<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk> C \<rbrakk> Q a)\<close>
  \<comment> \<open>does not hold in general when \<^term>\<open>A \<subseteq> C\<close>\<close>
  apply (cases \<open>A = {}\<close>, simp,
         metis (no_types, lifting) Mprefix_STOP Mprefix_Sync_distr_subset
                                   empty_subsetI inf_bot_left)
  apply (cases \<open>B = {}\<close>, simp add: Mprefix_STOP Mndetprefix_STOP)
  apply (subst Mndetprefix_GlobalNdet, subst GlobalNdet_Sync_distr, assumption)
  apply (subst Mndetprefix_GlobalNdet, subst Mprefix_singl[symmetric]) 
  apply (unfold write0_def, rule mono_GlobalNdet_eq[rule_format])
  apply (subst Mprefix_Sync_distr_subset[of _ C B P Q], blast, blast)
  by (metis (no_types, lifting) in_mono inf_le1 insert_disjoint(1)
                                Mprefix_singl subset_singletonD) *)


(* corollary Mndetprefix_Mprefix_Par_distr:
  \<open>A \<subseteq> B \<Longrightarrow> ((\<sqinter> a \<in> A \<rightarrow> P a) || (\<box> b \<in> B \<rightarrow> Q b)) = \<sqinter> a \<in> A \<rightarrow> P a || Q a\<close>
  by (simp add: Mndetprefix_Mprefix_Sync_distr) *)





lemma GlobalNdet_Mprefix_distr:
  \<open>A \<noteq> {} \<Longrightarrow> (\<sqinter> a \<in> A. \<box> b \<in> B \<rightarrow> P a b) = \<box> b \<in> B \<rightarrow> (\<sqinter> a \<in> A. P a b)\<close>
  by (auto simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet F_Mprefix D_Mprefix)



lemma GlobalNdet_Det_distrib:
  \<open>(\<sqinter> a \<in> A. P a \<box> Q a) = (\<sqinter> a \<in> A. P a) \<box> (\<sqinter> a \<in> A. Q a)\<close>
  if \<open>\<exists>Q' b. \<forall>a. Q a = (b \<rightarrow> Q' a)\<close>
proof -
  from that obtain b Q' where \<open>\<forall>a. (Q a = (b \<rightarrow> Q' a))\<close> by blast
  thus ?thesis
    by (auto simp add: Process_eq_spec F_Det D_Det write0_def
        F_GlobalNdet D_GlobalNdet T_GlobalNdet F_STOP D_STOP
        F_Mprefix D_Mprefix T_Mprefix)
qed



section \<open>Continuity\<close>

lemma mono_GlobalNdet : \<open>(\<And>a. a \<in> A \<Longrightarrow> P a \<sqsubseteq> Q a) \<Longrightarrow> (\<sqinter>a \<in> A. P a) \<sqsubseteq> \<sqinter>a \<in> A. Q a\<close>
  by (simp add: le_approx_def D_GlobalNdet Refusals_after_def F_GlobalNdet
      min_elems_def T_GlobalNdet subset_iff) blast

lemma chain_GlobalNdet : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. \<sqinter>a \<in> A. Y i a)\<close>
  by (simp add: ch2ch_monofun fun_belowD mono_GlobalNdet monofunI)


lemma GlobalNdet_cont [simp] : \<open>\<lbrakk>finite A; \<And>a. a \<in> A \<Longrightarrow> cont (P a)\<rbrakk> \<Longrightarrow> cont (\<lambda>y. \<sqinter> z\<in>A. P z y)\<close>
proof (induct A rule: finite_induct)
  case empty
  thus ?case by (simp add: GlobalNdet.abs_eq)
next
  case (insert a A)
  thus ?case
    by (cases \<open>A = {}\<close>, simp)
      (subst GlobalNdet_distrib_unit[of A a], auto)
qed


(*<*)
end
  (*>*)
