(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Global deterministic choice
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

chapter \<open>Definitions of the Architectural Operators\<close>

section\<open> The Global Deterministic Choice \<close>

(*<*)
theory Global_Deterministic_Choice 
  imports "HOL-CSP.CSP"
begin
  (*>*)

subsection \<open>Definition\<close>

text \<open>This is an experimental generalization of the deterministic choice.
      In previous versions, this was done by folding the binary operator \<^term>\<open>(\<box>)\<close>,
      but the set was of course necessarily finite.
      Now we give an abstract definition with the failures and the divergences.\<close>

lift_definition GlobalDet :: \<open>['b set, 'b \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda>A P. ({(s, X). s = [] \<and> (s, X) \<in> (\<Inter>a\<in>A. \<F> (P a))} \<union>
             {(s, X). s \<noteq> [] \<and> (s, X) \<in> (\<Union>a\<in>A. \<F> (P a))} \<union>
             {(s, X). s = [] \<and> s \<in> (\<Union>a\<in>A. \<D> (P a))} \<union>
             {(s, X). \<exists>r. s = [] \<and> \<checkmark>(r) \<notin> X \<and> [\<checkmark>(r)] \<in> (\<Union>a\<in>A. \<T> (P a))},
             \<Union>a\<in>A. \<D> (P a))\<close>
proof -
  show \<open>?thesis A P\<close> (is \<open>is_process (?f, \<Union>a\<in>A. \<D> (P a))\<close>) for A P
  proof (unfold is_process_def DIVERGENCES_def FAILURES_def fst_conv snd_conv, intro conjI allI impI)
    show \<open>([], {}) \<in> ?f\<close> by (simp add: is_processT1)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> ftF s\<close> for s X by (auto intro: is_processT2)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
      by (auto intro!: is_processT1 dest: is_processT3)
  next
    fix s X Y
    assume assm : \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y\<close>
    then consider \<open>s = []\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> (s, Y) \<in> \<F> (P a)\<close>
      | e s' a where \<open>a \<in> A\<close> \<open>s = e # s'\<close> \<open>(s, Y) \<in> \<F> (P a)\<close>
      | a where \<open>a \<in> A\<close> \<open>s = []\<close> \<open>s \<in> \<D> (P a)\<close>
      | a r where \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> Y\<close> \<open>[\<checkmark>(r)] \<in> \<T> (P a)\<close>
      by (cases s) auto
    thus \<open>(s, X) \<in> ?f\<close>
    proof cases
      assume \<open>s = []\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> (s, Y) \<in> \<F> (P a)\<close>
      from this(2) assm have \<open>a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (P a)\<close> for a
        by (meson is_processT4)
      with \<open>s = []\<close> show \<open>(s, X) \<in> ?f\<close> by fast
    next
      fix e s' a assume \<open>a \<in> A\<close> \<open>s = e # s'\<close> \<open>(s, Y) \<in> \<F> (P a)\<close>
      from \<open>(s, Y) \<in> \<F> (P a)\<close> assm[THEN conjunct2]
      have \<open>(s, X) \<in> \<F> (P a)\<close> by (fact is_processT4)
      with \<open>a \<in> A\<close> \<open>s = e # s'\<close> show \<open>(s, X) \<in> ?f\<close> by blast
    next
      show \<open>a \<in> A \<Longrightarrow> s = [] \<Longrightarrow> s \<in> \<D> (P a) \<Longrightarrow> (s, X) \<in> ?f\<close> for a by blast
    next
      fix a r assume \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> Y\<close> \<open>[\<checkmark>(r)] \<in> \<T> (P a)\<close>
      from \<open>\<checkmark>(r) \<notin> Y\<close> assm[THEN conjunct2] have \<open>\<checkmark>(r) \<notin> X\<close> by blast
      with \<open>a \<in> A\<close> \<open>s = []\<close> \<open>[\<checkmark>(r)] \<in> \<T> (P a)\<close> show \<open>(s, X) \<in> ?f\<close> by blast
    qed
  next
    fix s X Y
    assume assm : \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f)\<close>
    then consider \<open>s = []\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (P a)\<close>
      | e s' a where \<open>a \<in> A\<close> \<open>s = e # s'\<close> \<open>(s, X) \<in> \<F> (P a)\<close>
      | a where \<open>a \<in> A\<close> \<open>s = []\<close> \<open>s \<in> \<D> (P a)\<close>
      | a r where \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>[\<checkmark>(r)] \<in> \<T> (P a)\<close>
      by (cases s) auto
    thus \<open>(s, X \<union> Y) \<in> ?f\<close>
    proof cases
      assume \<open>s = []\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (P a)\<close>
      from this(2) assm[THEN conjunct2]
      have \<open>a \<in> A \<Longrightarrow> (s, X \<union> Y) \<in> \<F> (P a)\<close> for a
        by (simp add: is_processT5)
      with \<open>s = []\<close> show \<open>(s, X \<union> Y) \<in> ?f\<close> by blast
    next
      fix e s' a assume \<open>a \<in> A\<close> \<open>s = e # s'\<close> \<open>(s, X) \<in> \<F> (P a)\<close>
      from \<open>(s, X) \<in> \<F> (P a)\<close> assm[THEN conjunct2]
      have \<open>(s, X \<union> Y) \<in> \<F> (P a)\<close> by (simp add: \<open>a \<in> A\<close> is_processT5)
      with \<open>a \<in> A\<close> \<open>s = e # s'\<close> show \<open>(s, X \<union> Y) \<in> ?f\<close> by blast
    next
      show \<open>a \<in> A \<Longrightarrow> s = [] \<Longrightarrow> s \<in> \<D> (P a) \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for a by blast
    next
      fix a r assume \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>[\<checkmark>(r)] \<in> \<T> (P a)\<close>
      with assm[THEN conjunct2] T_F show \<open>(s, X \<union> Y) \<in> ?f\<close> by simp blast
    qed
  next
    fix s r X
    assume \<open>(s @ [\<checkmark>(r)], {}) \<in> ?f\<close>
    then obtain a where \<open>a \<in> A\<close> \<open>(s @ [\<checkmark>(r)], {}) \<in> \<F> (P a)\<close> by blast
    from this(2) have \<open>(s, X - {\<checkmark>(r)}) \<in> \<F> (P a)\<close> by (fact is_processT6)
    show \<open>(s, X - {\<checkmark>(r)}) \<in> ?f\<close>
    proof (cases \<open>s = []\<close>)
      show \<open>s = [] \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> ?f\<close>
        by simp (metis F_T \<open>(s @ [\<checkmark>(r)], {}) \<in> \<F> (P a)\<close> \<open>a \<in> A\<close> append_Nil)
    next
      assume \<open>s \<noteq> []\<close>
      with \<open>a \<in> A\<close> \<open>(s, X - {\<checkmark>(r)}) \<in> \<F> (P a)\<close>
      show \<open>(s, X - {\<checkmark>(r)}) \<in> ?f\<close> by blast
    qed
  next
    show \<open>s \<in> (\<Union>a\<in>A. \<D> (P a)) \<and> tF s \<and> ftF t \<Longrightarrow> s @ t \<in> (\<Union>a\<in>A. \<D> (P a))\<close> for s t
      by (blast intro: is_processT7)
  next
    show \<open>s \<in> (\<Union>a\<in>A. \<D> (P a)) \<Longrightarrow> (s, X) \<in> ?f\<close> for s X
      by (blast intro: is_processT8)
  next
    show \<open>s @ [\<checkmark>(r)] \<in> (\<Union>a\<in>A. \<D> (P a)) \<Longrightarrow> s \<in> (\<Union>a\<in>A. \<D> (P a))\<close> for s r
      by (blast intro: is_processT9)
  qed
qed


syntax "_GlobalDet" :: \<open>[pttrn,'b set,('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3\<box>((_)/\<in>(_))./ (_))\<close> [78,78,77] 77)
syntax_consts "_GlobalDet" \<rightleftharpoons> GlobalDet
translations  "\<box> p \<in> A. P " \<rightleftharpoons> "CONST GlobalDet A (\<lambda>p. P)"



subsection \<open>The projections\<close>

lemma F_GlobalDet:
  \<open>\<F> (\<box> x \<in> A. P x) =
   {(s, X). s = [] \<and> (s, X) \<in> (\<Inter>a\<in>A. \<F> (P a))} \<union>
   {(s, X). s \<noteq> [] \<and> (s, X) \<in> (\<Union>a\<in>A. \<F> (P a))} \<union>
   {(s, X). s = [] \<and> s \<in> (\<Union>a\<in>A. \<D> (P a))} \<union>
   {(s, X). \<exists>r. s = [] \<and> \<checkmark>(r) \<notin> X \<and> [\<checkmark>(r)] \<in> (\<Union>a\<in>A. \<T> (P a))}\<close>
  by (simp add: Failures.rep_eq FAILURES_def GlobalDet.rep_eq)

lemma F_GlobalDet':
  \<open>\<F> (\<box> x \<in> A. P x) =
   {([], X)| X. (\<exists>a\<in>A. P a = \<bottom>) \<or> (\<forall>a\<in>A. ([], X) \<in> \<F> (P a)) \<or>
                (\<exists>a\<in>A. \<exists>r. \<checkmark>(r) \<notin> X \<and> [\<checkmark>(r)] \<in> \<T> (P a))} \<union>
   {(s, X)| a s X. a \<in> A \<and> s \<noteq> [] \<and> (s, X) \<in> \<F> (P a)}\<close>
  (is \<open>\<F> (\<box> x \<in> A. P x) = ?rhs\<close>)
proof (intro subset_antisym subsetI)
  fix sX assume \<open>sX \<in> \<F> (\<box> x \<in> A. P x)\<close>
  obtain s X where \<open>sX = (s, X)\<close> using prod.exhaust_sel by blast
  with \<open>sX \<in> \<F> (\<box> x \<in> A. P x)\<close> show \<open>sX \<in> ?rhs\<close>
    by (auto simp add: F_GlobalDet BOT_iff_Nil_D)
next
  fix sX assume \<open>sX \<in> ?rhs\<close>
  obtain s X where \<open>sX = (s, X)\<close> using prod.exhaust_sel by blast
  with \<open>sX \<in> ?rhs\<close> show \<open>sX \<in> \<F> (\<box> x \<in> A. P x)\<close>
    by (auto simp add: F_GlobalDet BOT_iff_Nil_D)
qed


lemma D_GlobalDet: \<open>\<D> (\<box> x \<in> A. P x) = (\<Union>a\<in>A. \<D> (P a))\<close>
  by (simp add: Divergences.rep_eq DIVERGENCES_def GlobalDet.rep_eq)

lemma T_GlobalDet:
  \<open>\<T> (\<box> x \<in> A. P x) = (if A = {} then {[]} else (\<Union> x\<in>A. \<T> (P x)))\<close>
  by (auto simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_GlobalDet
      intro: is_processT1 is_processT8)

lemma T_GlobalDet': \<open>\<T> (\<box> x \<in> A. P x) = (insert [] (\<Union> x\<in>A. \<T> (P x)))\<close>
  by (simp add: T_GlobalDet)
    (metis T_GlobalDet insert_absorb is_processT1_TR)

lemmas GlobalDet_projs = F_GlobalDet D_GlobalDet T_GlobalDet


lemma mono_GlobalDet_eq:
  \<open>(\<And>x. x \<in> A \<Longrightarrow> P x = Q x) \<Longrightarrow> GlobalDet A P = GlobalDet A Q\<close>
  by (subst Process_eq_spec, simp add: F_GlobalDet D_GlobalDet)

lemma mono_GlobalDet_eq2:
  \<open>(\<And>x. x \<in> A \<Longrightarrow> P (f x) = Q x) \<Longrightarrow> GlobalDet (f ` A) P = GlobalDet A Q\<close>
  by (subst Process_eq_spec, simp add: F_GlobalDet D_GlobalDet)




subsection \<open>Factorization of \<^const>\<open>Det\<close> in front of \<^const>\<open>GlobalDet\<close>\<close>

lemma Process_eq_optimized_bisI :
  assumes \<open>\<And>s. s \<in> \<D> P \<Longrightarrow> s \<in> \<D> Q\<close> \<open>\<And>s. s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> P\<close>
    and \<open>\<And>X. \<D> P = \<D> Q \<Longrightarrow> ([], X) \<in> \<F> P \<Longrightarrow> ([], X) \<in> \<F> Q\<close>
    and \<open>\<And>X. \<D> Q = \<D> P \<Longrightarrow> ([], X) \<in> \<F> Q \<Longrightarrow> ([], X) \<in> \<F> P\<close>
    and \<open>\<And>a s X. \<D> P = \<D> Q \<Longrightarrow> (a # s, X) \<in> \<F> P \<Longrightarrow> (a # s, X) \<in> \<F> Q\<close>
    and \<open>\<And>a s X. \<D> Q = \<D> P \<Longrightarrow> (a # s, X) \<in> \<F> Q \<Longrightarrow> (a # s, X) \<in> \<F> P\<close>
  shows \<open>P = Q\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> Q\<close> for s by (fact assms(1))
next
  show \<open>s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> P\<close> for s by (fact assms(2))
next
  show \<open>\<D> P = \<D> Q \<Longrightarrow> (s, X) \<in> \<F> P \<Longrightarrow> (s, X) \<in> \<F> Q\<close> for s X
    by (metis assms(3, 5) neq_Nil_conv)
next
  show \<open>\<D> P = \<D> Q \<Longrightarrow> (s, X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> P\<close> for s X
    by (metis assms(4, 6) neq_Nil_conv)
qed


lemma GlobalDet_factorization_union:
  \<open>(\<box> p \<in> A. P p) \<box> (\<box> p \<in> B. P p) = \<box> p \<in> (A \<union> B) . P p\<close>
  by (rule Process_eq_optimized_bisI)
    (auto simp add: D_Det D_GlobalDet F_Det F_GlobalDet T_GlobalDet split: if_split_asm)

lemma GlobalDet_Union :
  \<open>(\<box>a \<in> (\<Union>i \<in> I. A i). P a) = \<box>i \<in> I. \<box>a \<in> A i. P a\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_GlobalDet)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s) (auto simp add: GlobalDet_projs)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s; simp add: GlobalDet_projs split: if_split_asm) blast+
qed


subsection \<open>First properties\<close>

lemma GlobalDet_id [simp] : \<open>A \<noteq> {} \<Longrightarrow> (\<box> p \<in> A. P) = P\<close>
  by (auto simp add: Process_eq_spec F_GlobalDet D_GlobalDet
      intro: is_processT8 is_processT6_TR_notin)

lemma GlobalDet_unit[simp] : \<open>(\<box> x \<in> {a}. P x) = P a\<close> 
  by (auto simp add: Process_eq_spec F_GlobalDet D_GlobalDet
      intro: is_processT8 is_processT6_TR_notin)

(* TODO: move this ? *)
lemma GlobalDet_empty[simp] : \<open>(\<box>a \<in> {}. P a) = STOP\<close>
  by (simp add: STOP_iff_T T_GlobalDet)


lemma GlobalDet_distrib_unit:
  \<open>(\<box> x \<in> insert a A. P x) = P a \<box> (\<box> x \<in> (A - {a}). P x)\<close>
  by (metis GlobalDet_factorization_union GlobalDet_unit Un_Diff_cancel insert_is_Un)

(* useful ? *)
lemma GlobalDet_distrib_unit_bis : 
  \<open>a \<notin> A \<Longrightarrow> (\<box> x \<in> insert a A. P x) = P a \<box> (\<box> x \<in> A. P x)\<close>
  by (simp add: GlobalDet_distrib_unit)



subsection \<open>Behaviour of \<^const>\<open>GlobalDet\<close> with \<^const>\<open>Det\<close>\<close>

lemma GlobalDet_Det_GlobalDet:
  \<open>(\<box> a \<in> A. P a) \<box> (\<box> a \<in> A. Q a) = \<box> a \<in> A. P a \<box> Q a\<close>
  (is \<open>?G1 \<box> ?G2 = ?G\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> (?G1 \<box> ?G2) \<Longrightarrow> s \<in> \<D> ?G\<close>
    and \<open>s \<in> \<D> ?G \<Longrightarrow> s \<in> \<D> (?G1 \<box> ?G2)\<close> for s
    by (auto simp add: D_Det D_GlobalDet)
next
  show \<open>(s, X) \<in> \<F> (?G1 \<box> ?G2) \<Longrightarrow> (s, X) \<in> \<F> ?G\<close> for s X
    by (cases s) (auto simp add: F_Det D_Det T_Det D_GlobalDet T_GlobalDet' F_GlobalDet)
next
  show \<open>(s, X) \<in> \<F> ?G \<Longrightarrow> (s, X) \<in> \<F> (?G1 \<box> ?G2)\<close> for s X
    by (cases s; simp add: F_Det D_Det T_Det D_GlobalDet T_GlobalDet' F_GlobalDet) blast+
qed


subsection \<open>Commutativity\<close>

lemma GlobalDet_sets_commute:
  \<open>(\<box> a \<in> A. \<box> b \<in> B. P a b) = \<box> b \<in> B. \<box> a \<in> A. P a b\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_GlobalDet)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s; simp add: F_GlobalDet T_GlobalDet' D_GlobalDet split: if_split_asm, blast)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s; simp add: F_GlobalDet T_GlobalDet' D_GlobalDet split: if_split_asm, blast)
qed


subsection \<open>Behaviour with injectivity\<close>

lemma inj_on_mapping_over_GlobalDet: 
  \<open>inj_on f A \<Longrightarrow> (\<box> x \<in> A. P x) = \<box> x \<in> f ` A. P (inv_into A f x)\<close>
  by (simp add: Process_eq_spec F_GlobalDet D_GlobalDet)



subsection \<open>Cartesian product results\<close>

lemma GlobalDet_cartprod_\<sigma>s_set_\<sigma>s_set:
  \<open>(\<box> (s, t) \<in> A \<times> B. P (s @ t)) = \<box> u \<in> {s @ t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_GlobalDet)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s; simp add: F_GlobalDet, blast)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s; simp add: F_GlobalDet, blast)
qed



lemma GlobalDet_cartprod_s_set_\<sigma>s_set:
  \<open>(\<box> (s, t) \<in> A \<times> B. P (s # t)) = \<box> u \<in> {s # t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_GlobalDet)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s; simp add: F_GlobalDet, blast)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s; simp add: F_GlobalDet, blast)
qed


lemma GlobalDet_cartprod_s_set_s_set:
  \<open>(\<box> (s, t) \<in> A \<times> B. P [s, t]) = \<box> u \<in> {[s, t] |s t. (s, t) \<in> A \<times> B}. P u\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_GlobalDet)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s; simp add: F_GlobalDet, blast)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s; simp add: F_GlobalDet, blast)
qed


lemma GlobalDet_cartprod: \<open>(\<box>(s, t) \<in> A \<times> B. P s t) = \<box>s \<in> A. \<box>t \<in> B. P s t\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_GlobalDet)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s) (auto simp add: F_GlobalDet T_GlobalDet D_GlobalDet)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s; simp add: F_GlobalDet T_GlobalDet D_GlobalDet
        split: if_split_asm) blast
qed



subsection \<open>Link with \<^const>\<open>Mprefix\<close>\<close>

text \<open>This is a trick to make proof of \<^const>\<open>Mprefix\<close> using
      \<^const>\<open>GlobalDet\<close> as it has an easier denotational definition.\<close>

lemma Mprefix_GlobalDet: \<open>\<box> a \<in> A \<rightarrow> P a = \<box> a \<in> A. a \<rightarrow> P a\<close>
  by (simp add: Process_eq_spec write0_projs GlobalDet_projs Mprefix_projs, safe, auto)

lemma read_is_GlobalDet_write0 :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a = \<box>b\<in>c ` A. b \<rightarrow> P (inv_into A c b)\<close>
  by (simp add: read_def Mprefix_GlobalDet)

lemma read_is_GlobalDet_write :
  \<open>inj_on c A \<Longrightarrow> c\<^bold>?a\<in>A \<rightarrow> P a = \<box>a\<in>A. c\<^bold>!a \<rightarrow> P a\<close>
  by (auto simp add: read_is_GlobalDet_write0 write_def write0_def
      intro: mono_GlobalDet_eq2)




subsection \<open>Properties\<close>

lemma GlobalDet_Det: \<open>(\<box> a \<in> A. P a) \<box> Q = (if A = {} then Q else \<box> a \<in> A. P a \<box> Q)\<close>
  (is \<open>?lhs = (if A = {} then Q else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs = Q\<close>
    by (auto simp add: Process_eq_spec F_Det F_STOP D_STOP T_STOP D_Det
        intro: is_processT8 is_processT6_TR_notin)
next
  show \<open>?lhs = ?rhs\<close> if \<open>A \<noteq> {}\<close>
  proof (subst Process_eq_spec, safe)
    show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
      and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
      by (auto simp add: \<open>A \<noteq> {}\<close> D_Det D_GlobalDet)
  next
    from \<open>A \<noteq> {}\<close> show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
      by (cases s) (auto simp add: F_Det F_GlobalDet D_Det T_Det D_GlobalDet T_GlobalDet)
  next
    from \<open>A \<noteq> {}\<close> show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
      by (cases s; simp add: F_Det F_GlobalDet D_Det T_Det D_GlobalDet T_GlobalDet, blast)
  qed
qed


(* TODO: useful ? *)
lemma Mndetprefix_Sync_Mprefix_strong_subset:
  \<open>\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> \<sqinter> a \<in> A \<rightarrow> P a \<lbrakk> C \<rbrakk> \<box> b \<in> B \<rightarrow> Q b = \<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk> C \<rbrakk> Q a)\<close>
  by (simp add: Mndetprefix_Sync_Mprefix_subset STOP_Sync_Mprefix Mprefix_is_STOP_iff)

lemma Mprefix_Sync_Mndetprefix_strong_subset:
  \<open>\<lbrakk>A \<subseteq> C; B \<subseteq> A\<rbrakk> \<Longrightarrow> \<box> a \<in> A \<rightarrow> P a \<lbrakk> C \<rbrakk> \<sqinter> b \<in> B \<rightarrow> Q b = \<sqinter> b \<in> B \<rightarrow> (P b \<lbrakk> C \<rbrakk> Q b)\<close>
  by (subst (1 2) Sync_commute, simp add: Mndetprefix_Sync_Mprefix_strong_subset)


corollary Mndetprefix_Par_Mprefix_strong_subset:
  \<open>A \<subseteq> B \<Longrightarrow> \<sqinter> a \<in> A \<rightarrow> P a || \<box> b \<in> B \<rightarrow> Q b = \<sqinter> a \<in> A \<rightarrow> (P a || Q a)\<close>
  by (simp add: Mndetprefix_Sync_Mprefix_strong_subset) 

corollary Mprefix_Par_Mndetprefix_strong_subset:
  \<open>B \<subseteq> A \<Longrightarrow> \<box> a \<in> A \<rightarrow> P a || \<sqinter> b \<in> B \<rightarrow> Q b = \<sqinter> b \<in> B \<rightarrow> (P b || Q b)\<close>
  by (simp add: Mprefix_Sync_Mndetprefix_strong_subset) 



subsection \<open>Continuity\<close>

lemma mono_GlobalDet : \<open>(\<box>a \<in> A. P a) \<sqsubseteq> \<box>a \<in> A. Q a\<close> if \<open>\<And>x. x \<in> A \<Longrightarrow> P x \<sqsubseteq> Q x\<close>
proof (unfold le_approx_def, safe)
  show \<open>s \<in> \<D> (\<box>a \<in> A. Q a) \<Longrightarrow> s \<in> \<D> (\<box>a \<in> A. P a)\<close> for s
    using that[THEN le_approx1] by (auto simp add: D_GlobalDet)
next
  fix s X assume \<open>s \<notin> \<D> (\<box>a \<in> A. P a)\<close> \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. P a) s\<close>
  from \<open>s \<notin> \<D> (\<box>a \<in> A. P a)\<close> have * : \<open>\<forall>a\<in>A. s \<notin> \<D> (P a)\<close>
    by (simp add: D_GlobalDet)
  with that le_approx2
  have ** : \<open>a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (Q a) \<longleftrightarrow> (s, X) \<in> \<F> (P a)\<close> for a X by blast
  from \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. P a) s\<close> "*"
  consider \<open>s = []\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (P a)\<close>
    | e s' a where \<open>a \<in> A\<close> \<open>s = e # s'\<close> \<open>(s, X) \<in> \<F> (P a)\<close>
    | a r where \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>[\<checkmark>(r)] \<in> \<T> (P a)\<close>
    by (cases s) (auto simp add: Refusals_after_def F_GlobalDet)
  thus \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. Q a) s\<close>
  proof cases
    assume \<open>s = []\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (P a)\<close>
    from this(2) "**" have \<open>\<And>a. a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (Q a)\<close> by simp
    with \<open>s = []\<close> show \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. Q a) s\<close>
      by (simp add: Refusals_after_def F_GlobalDet)
  next
    fix e s' a assume \<open>a \<in> A\<close> \<open>s = e # s'\<close> \<open>(s, X) \<in> \<F> (P a)\<close>
    from \<open>(s, X) \<in> \<F> (P a)\<close> "**" have \<open>(s, X) \<in> \<F> (Q a)\<close> by (simp add: \<open>a \<in> A\<close>)
    with \<open>a \<in> A\<close> \<open>s = e # s'\<close> show \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. Q a) s\<close>
      by (auto simp add: Refusals_after_def F_GlobalDet)
  next
    fix a r assume \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>[\<checkmark>(r)] \<in> \<T> (P a)\<close>
    from \<open>a \<in> A\<close> \<open>[\<checkmark>(r)] \<in> \<T> (P a)\<close> have \<open>[\<checkmark>(r)] \<in> \<T> (Q a)\<close>
      by (fold T_F_spec, simp add: "**"[OF \<open>a \<in> A\<close>])
        (metis "*" \<open>s = []\<close> is_processT9 proc_ord2a self_append_conv2 that)
    with \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> show \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. Q a) s\<close>
      by (auto simp add: Refusals_after_def F_GlobalDet)
  qed
next
  fix s X assume \<open>s \<notin> \<D> (\<box>a \<in> A. P a)\<close> \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. Q a) s\<close>
  from \<open>s \<notin> \<D> (\<box>a \<in> A. P a)\<close> have * : \<open>\<forall>a\<in>A. s \<notin> \<D> (P a)\<close>
    by (simp add: D_GlobalDet)
  with that le_approx2
  have ** : \<open>a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (Q a) \<longleftrightarrow> (s, X) \<in> \<F> (P a)\<close> for a X by blast
  from \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. Q a) s\<close>
  consider \<open>s = []\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (Q a)\<close>
    | e s' a where \<open>a \<in> A\<close> \<open>s = e # s'\<close> \<open>(s, X) \<in> \<F> (Q a)\<close>
    | a where \<open>a \<in> A\<close> \<open>s = []\<close> \<open>s \<in> \<D> (Q a)\<close>
    | a r where \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>[\<checkmark>(r)] \<in> \<T> (Q a)\<close>
    by (cases s) (auto simp add: Refusals_after_def F_GlobalDet)
  thus \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. P a) s\<close>
  proof cases
    assume \<open>s = []\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (Q a)\<close>
    from this(2) "**" have \<open>\<And>a. a \<in> A \<Longrightarrow> (s, X) \<in> \<F> (P a)\<close> by simp
    with \<open>s = []\<close> show \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. P a) s\<close>
      by (simp add: Refusals_after_def F_GlobalDet)
  next
    fix e s' a assume \<open>a \<in> A\<close> \<open>s = e # s'\<close> \<open>(s, X) \<in> \<F> (Q a)\<close>
    from \<open>(s, X) \<in> \<F> (Q a)\<close> "**" have \<open>(s, X) \<in> \<F> (P a)\<close> by (simp add: \<open>a \<in> A\<close>)
    with \<open>a \<in> A\<close> \<open>s = e # s'\<close> show \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. P a) s\<close>
      by (auto simp add: Refusals_after_def F_GlobalDet)
  next
    show \<open>a \<in> A \<Longrightarrow> s = [] \<Longrightarrow> s \<in> \<D> (Q a) \<Longrightarrow> X \<in> \<R>\<^sub>a (\<box>a \<in> A. P a) s\<close> for a
      by (simp add: Refusals_after_def F_GlobalDet)
        (meson le_approx1 subsetD that)
  next
    fix a r assume \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>[\<checkmark>(r)] \<in> \<T> (Q a)\<close>
    from \<open>a \<in> A\<close> \<open>[\<checkmark>(r)] \<in> \<T> (Q a)\<close> have \<open>[\<checkmark>(r)] \<in> \<T> (P a)\<close>
      by (fold T_F_spec, simp add: "**"[OF \<open>a \<in> A\<close>])
        (metis "*" \<open>s = []\<close> is_processT9 proc_ord2a self_append_conv2 that)
    with \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> show \<open>X \<in> \<R>\<^sub>a (\<box>a \<in> A. P a) s\<close>
      by (auto simp add: Refusals_after_def F_GlobalDet)
  qed
next
  from that[THEN le_approx3]
  show \<open>s \<in> min_elems (\<D> (\<box>a \<in> A. P a)) \<Longrightarrow> s \<in> \<T> (\<box>a \<in> A. Q a)\<close> for s
    by (auto simp add: min_elems_def subset_iff less_list_def less_eq_list_def
        prefix_def D_GlobalDet T_GlobalDet) blast
qed


lemma chain_GlobalDet : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. \<box>a \<in> A. Y i a)\<close>
  by (simp add: ch2ch_monofun fun_belowD mono_GlobalDet monofunI)


lemma GlobalDet_cont [simp] : \<open>\<lbrakk>finite A; \<And>a. a \<in> A \<Longrightarrow> cont (P a)\<rbrakk> \<Longrightarrow> cont (\<lambda>y. \<box> z\<in>A. P z y)\<close>
  by (induct A rule: finite_induct)
    (simp_all add: GlobalDet_distrib_unit)



end
