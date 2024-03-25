(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Laws for architectural operators
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

chapter \<open>CSPM\<close>

theory CSPM
  imports MultiDet MultiNdet MultiSync MultiSeq GlobalNdet "HOL-CSP.Assertions"
begin

text \<open>From the binary laws of \<^session>\<open>HOL-CSP\<close>, we immediately obtain refinement results
      and lemmas about the combination of multi-operators.\<close>

section \<open>Refinements Results\<close>

lemma mono_MultiDet_F:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> MultiDet A P \<sqsubseteq>\<^sub>F MultiDet A Q\<close>
  apply (induct A rule: induct_subset_empty_single; simp)
  oops


lemma mono_MultiDet_D[simp, elim]:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> MultiDet A P \<sqsubseteq>\<^sub>D MultiDet A Q\<close>
  and mono_MultiDet_T[simp, elim]:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> MultiDet A P \<sqsubseteq>\<^sub>T MultiDet A Q\<close>
  and mono_MultiDet_DT[simp, elim]:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> MultiDet A P \<sqsubseteq>\<^sub>D\<^sub>T MultiDet A Q\<close>
  and mono_MultiDet_FD[simp, elim]:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F\<^sub>D Q x \<Longrightarrow> MultiDet A P \<sqsubseteq>\<^sub>F\<^sub>D MultiDet A Q\<close>
  by (induct A rule: induct_subset_empty_single; simp del: MultiDet_insert)+



lemma mono_MultiNdet_F[simp, elim]:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>F MultiNdet A Q\<close>
  and mono_MultiNdet_D[simp, elim]:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>D MultiNdet A Q\<close>
  and mono_MultiNdet_T[simp, elim]:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>T MultiNdet A Q\<close>
  and mono_MultiNdet_DT[simp, elim]:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>D\<^sub>T MultiNdet A Q\<close>
  and mono_MultiNdet_FD[simp, elim]:
  \<open>finite A \<Longrightarrow> \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F\<^sub>D Q x \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>F\<^sub>D MultiNdet A Q\<close>
  by (induct A rule: induct_subset_empty_single; simp)+



lemma  mono_MultiNdet_F_single:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> \<forall>a \<in> A. P \<sqsubseteq>\<^sub>F Q a  \<Longrightarrow> P \<sqsubseteq>\<^sub>F MultiNdet A Q\<close>
  and  mono_MultiNdet_D_single:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> \<forall>a \<in> A. P \<sqsubseteq>\<^sub>D Q a  \<Longrightarrow> P \<sqsubseteq>\<^sub>D MultiNdet A Q\<close>
  and  mono_MultiNdet_T_single:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> \<forall>a \<in> A. P \<sqsubseteq>\<^sub>T Q a  \<Longrightarrow> P \<sqsubseteq>\<^sub>T MultiNdet A Q\<close>
  and mono_MultiNdet_DT_single:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> \<forall>a \<in> A. P \<sqsubseteq>\<^sub>D\<^sub>T Q a \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T MultiNdet A Q\<close>
  and mono_MultiNdet_FD_single:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> \<forall>a \<in> A. P \<sqsubseteq>\<^sub>F\<^sub>D Q a \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D MultiNdet A Q\<close>
  by (subst MultiNdet_id[where A = A, symmetric], simp_all)+



lemma  
  assumes \<open>A \<noteq> {}\<close> and \<open>finite B\<close> and \<open>A \<subseteq> B\<close>
  shows   mono_MultiNdet_F_left_absorb_subset: 
          \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> MultiNdet B P \<sqsubseteq>\<^sub>F MultiNdet A Q\<close>
      and  mono_MultiNdet_D_left_absorb_subset:
          \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> MultiNdet B P \<sqsubseteq>\<^sub>D MultiNdet A Q\<close>
      and  mono_MultiNdet_T_left_absorb_subset:
          \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> MultiNdet B P \<sqsubseteq>\<^sub>T MultiNdet A Q\<close>
      and mono_MultiNdet_FD_left_absorb_subset:
          \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F\<^sub>D Q x \<Longrightarrow> MultiNdet B P \<sqsubseteq>\<^sub>F\<^sub>D MultiNdet A Q\<close>
      and mono_MultiNdet_DT_left_absorb_subset:
          \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> MultiNdet B P \<sqsubseteq>\<^sub>D\<^sub>T MultiNdet A Q\<close>
  supply finiteA = finite_subset[OF \<open>A \<subseteq> B\<close> \<open>finite B\<close>]
     and B_eq = Un_absorb1[OF \<open>A \<subseteq> B\<close>, symmetric,
                           simplified Un_Diff_cancel[of A B, symmetric]]
     and results = Diff_cancel MultiNdet_factorization_union Un_Diff_cancel assms(1, 2)
      apply (metis mono_MultiNdet_F mono_Ndet_F_left results finiteA B_eq)
     apply (metis mono_MultiNdet_D mono_Ndet_D_left results finiteA B_eq)
    apply (metis mono_MultiNdet_T mono_Ndet_T_left results finiteA B_eq)
   apply (metis mono_MultiNdet_FD mono_Ndet_FD_left results finiteA B_eq)
  by (metis mono_MultiNdet_DT mono_Ndet_DT_left results finiteA B_eq)


corollary  mono_MultiNdet_F_left_absorb[simp]:
          \<open>finite A \<Longrightarrow> x \<in> A \<Longrightarrow> P x \<sqsubseteq>\<^sub>F Q \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>F Q\<close>
      and  mono_MultiNdet_D_left_absorb[simp]:
          \<open>finite A \<Longrightarrow> x \<in> A \<Longrightarrow> P x \<sqsubseteq>\<^sub>D Q \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>D Q\<close>
      and  mono_MultiNdet_T_left_absorb[simp]:
          \<open>finite A \<Longrightarrow> x \<in> A \<Longrightarrow> P x \<sqsubseteq>\<^sub>T Q \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>T Q\<close>
      and mono_MultiNdet_FD_left_absorb[simp]:
          \<open>finite A \<Longrightarrow> x \<in> A \<Longrightarrow> P x \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
      and mono_MultiNdet_DT_left_absorb[simp]:
          \<open>finite A \<Longrightarrow> x \<in> A \<Longrightarrow> P x \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
      apply (rule trans_F [OF mono_MultiNdet_F_left_absorb_subset
                              [where A = \<open>{x}\<close>, simplified]]; simp) 
     apply (rule trans_D [OF mono_MultiNdet_D_left_absorb_subset
                             [where A = \<open>{x}\<close>, simplified]]; simp)
    apply (rule trans_T [OF mono_MultiNdet_T_left_absorb_subset
                            [where A = \<open>{x}\<close>, simplified]]; simp)
   apply (rule trans_FD[OF mono_MultiNdet_FD_left_absorb_subset
                           [where A = \<open>{x}\<close>, simplified]]; simp)
  by (rule trans_DT[OF mono_MultiNdet_DT_left_absorb_subset
                       [where A = \<open>{x}\<close>, simplified]]; simp)



lemma  mono_MultiNdet_MultiDet_F[simp, elim]:
      \<open>finite A \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>F MultiDet A P\<close>
  and  mono_MultiNdet_MultiDet_D[simp, elim]:
      \<open>finite A \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>D MultiDet A P\<close>
  and  mono_MultiNdet_MultiDet_T[simp, elim]:
      \<open>finite A \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>T MultiDet A P\<close>
  and mono_MultiNdet_MultiDet_FD[simp, elim]:
      \<open>finite A \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>F\<^sub>D MultiDet A P\<close>
  and mono_MultiNdet_MultiDet_DT[simp, elim]:
      \<open>finite A \<Longrightarrow> MultiNdet A P \<sqsubseteq>\<^sub>D\<^sub>T MultiDet A P\<close>
  by (induct A rule: induct_subset_empty_single;
      simp del: MultiDet_insert;
      meson idem_F  mono_Ndet_F  mono_Ndet_Det_F  trans_F
            idem_D  mono_Ndet_D  mono_Ndet_Det_D  trans_D
            idem_T  mono_Ndet_T  mono_Ndet_Det_T  trans_T 
            idem_FD mono_Ndet_FD mono_Ndet_Det_FD trans_FD
            idem_DT mono_Ndet_DT mono_Ndet_Det_DT trans_DT)+


lemma mono_MultiSync_F: \<open>\<forall>x \<in># M. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> MultiSync S M P \<sqsubseteq>\<^sub>F MultiSync S M Q\<close>
 apply (induct M rule: induct_subset_mset_empty_single; simp)
  oops


lemma mono_MultiSync_D: \<open>\<forall>x \<in># M. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> MultiSync S M P \<sqsubseteq>\<^sub>D MultiSync S M Q\<close>
  apply (induct M rule: induct_subset_mset_empty_single; simp)
  oops

lemma mono_MultiSync_T: \<open>\<forall>x \<in># M. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> MultiSync S M P \<sqsubseteq>\<^sub>T MultiSync S M Q\<close>
  apply (induct M rule: induct_subset_mset_empty_single; simp)
  oops

lemma mono_MultiSync_DT[simp, elim]:
  \<open>\<forall>x \<in># M. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> MultiSync S M P \<sqsubseteq>\<^sub>D\<^sub>T MultiSync S M Q\<close>
  and mono_MultiSync_FD[simp, elim]:
  \<open>\<forall>x \<in># M. P x \<sqsubseteq>\<^sub>F\<^sub>D Q x \<Longrightarrow> MultiSync S M P \<sqsubseteq>\<^sub>F\<^sub>D MultiSync S M Q\<close>
  by (induct M rule: induct_subset_mset_empty_single; simp)+


find_theorems name: mset name: ind
lemmas mono_MultiInter_DT[simp, elim] = mono_MultiSync_DT[where S = \<open>{}\<close>]
   and mono_MultiInter_FD[simp, elim] = mono_MultiSync_FD[where S = \<open>{}\<close>]
   and   mono_MultiPar_DT[simp, elim] = mono_MultiSync_DT[where S = \<open>UNIV\<close>]
   and   mono_MultiPar_FD[simp, elim] = mono_MultiSync_FD[where S = \<open>UNIV\<close>]



lemma mono_MultiSeq_F:
  \<open>\<forall>x \<in> set L. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> MultiSeq L P \<sqsubseteq>\<^sub>F MultiSeq L Q\<close>
  apply (induct L, fastforce) apply simp oops
 
lemma mono_MultiSeq_D:
  \<open>\<forall>x \<in> set L. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> MultiSeq L P \<sqsubseteq>\<^sub>D MultiSeq L Q\<close>
  apply (induct L, fastforce) apply simp oops

lemma mono_MultiSeq_T:
  \<open>\<forall>x \<in> set L. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> MultiSeq L P \<sqsubseteq>\<^sub>T MultiSeq L Q\<close>
  apply (induct L, fastforce) apply simp oops

lemma mono_MultiSeq_DT[simp, elim]:
  \<open>\<forall>x \<in> set L. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> MultiSeq L P \<sqsubseteq>\<^sub>D\<^sub>T MultiSeq L Q\<close>
  and mono_MultiSeq_FD[simp, elim]:
  \<open>\<forall>x \<in> set L. P x \<sqsubseteq>\<^sub>F\<^sub>D Q x \<Longrightarrow> MultiSeq L P \<sqsubseteq>\<^sub>F\<^sub>D MultiSeq L Q\<close>
  by (induct L) fastforce+




lemma mono_GlobalNdet[simp] : \<open>GlobalNdet A P \<sqsubseteq> GlobalNdet A Q\<close>
  if \<open>\<forall>x \<in> A. P x \<sqsubseteq> Q x\<close> 
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> GlobalNdet A P \<sqsubseteq> GlobalNdet A Q\<close> by simp
next
  assume \<open>A \<noteq> {}\<close>
  show \<open>GlobalNdet A P \<sqsubseteq> GlobalNdet A Q\<close>
    unfolding le_approx_def
  proof (intro conjI impI allI subsetI)
    show \<open>s \<in> \<D> (GlobalNdet A Q) \<Longrightarrow> s \<in> \<D> (GlobalNdet A P)\<close> for s
      using that[rule_format, THEN le_approx1] by (auto simp add: D_GlobalNdet \<open>A \<noteq> {}\<close>)
  next
    show \<open>s \<notin> \<D> (GlobalNdet A P) \<Longrightarrow> \<R>\<^sub>a (GlobalNdet A P) s = \<R>\<^sub>a (GlobalNdet A Q) s\<close> for s
      using that[rule_format, THEN le_approx2] 
      by (auto simp add: D_GlobalNdet Ra_def F_GlobalNdet \<open>A \<noteq> {}\<close>)
  next
    show \<open>s \<in> min_elems (\<D> (GlobalNdet A P)) \<Longrightarrow> s \<in> \<T> (GlobalNdet A Q)\<close> for s
      using that[rule_format, THEN le_approx3]
      by (simp add: D_GlobalNdet T_GlobalNdet \<open>A \<noteq> {}\<close> min_elems_def) blast
  qed
qed

lemma mono_GlobalNdet_F[simp, elim]:
  \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> GlobalNdet A P \<sqsubseteq>\<^sub>F GlobalNdet A Q\<close>
  and mono_GlobalNdet_D[simp, elim]:
  \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> GlobalNdet A P \<sqsubseteq>\<^sub>D GlobalNdet A Q\<close>
  and mono_GlobalNdet_T[simp, elim]:
  \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> GlobalNdet A P \<sqsubseteq>\<^sub>T GlobalNdet A Q\<close>
  and mono_GlobalNdet_DT[simp, elim]:
  \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> GlobalNdet A P \<sqsubseteq>\<^sub>D\<^sub>T GlobalNdet A Q\<close>
  and mono_GlobalNdet_FD[simp, elim]:
  \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F\<^sub>D Q x \<Longrightarrow> GlobalNdet A P \<sqsubseteq>\<^sub>F\<^sub>D GlobalNdet A Q\<close>
  unfolding failure_refine_def divergence_refine_def trace_refine_def
    trace_divergence_refine_def failure_divergence_refine_def le_ref_def
  by (auto simp add: F_GlobalNdet D_GlobalNdet T_GlobalNdet)


lemma GlobalNdet_refine_FD_subset:
  \<open>A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> GlobalNdet B P \<sqsubseteq>\<^sub>F\<^sub>D GlobalNdet A P\<close> 
  by (metis mono_Ndet_FD_left GlobalNdet_factorization_union
            bot.extremum_uniqueI idem_FD le_iff_sup)

lemma GlobalNdet_refine_F_subset:
  \<open>A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> GlobalNdet B P \<sqsubseteq>\<^sub>F GlobalNdet A P\<close>
  by (simp add: GlobalNdet_refine_FD_subset leFD_imp_leF)

lemma GlobalNdet_refine_FD: \<open>a \<in> A \<Longrightarrow> GlobalNdet A P \<sqsubseteq>\<^sub>F\<^sub>D P a\<close> 
  using GlobalNdet_refine_FD_subset[of \<open>{a}\<close> A] by simp

lemma GlobalNdet_refine_F: \<open>a \<in> A \<Longrightarrow> GlobalNdet A P \<sqsubseteq>\<^sub>F P a\<close>
  by (simp add: GlobalNdet_refine_FD leFD_imp_leF)

lemma mono_GlobalNdet_FD_const:
  \<open>A \<noteq> {} \<Longrightarrow> \<forall>x \<in> A. P \<sqsubseteq>\<^sub>F\<^sub>D Q x \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D GlobalNdet A Q\<close>
  by (metis GlobalNdet_id mono_GlobalNdet_FD)

lemma mono_GlobalNdet_F_const:
  \<open>A \<noteq> {} \<Longrightarrow> \<forall>x \<in> A. P \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> P \<sqsubseteq>\<^sub>F GlobalNdet A Q\<close>
  by (metis GlobalNdet_id mono_GlobalNdet_F)



section \<open>Combination of Multi-Operators Laws\<close>

lemma finite_Mprefix_is_MultiDet:
  \<open>finite A \<Longrightarrow> (\<box> p \<in> A \<rightarrow> P p) = \<^bold>\<box> p \<in> A. (p \<rightarrow> P p)\<close>
  by (induct rule: finite_induct, simp_all add: Mprefix_STOP)
     (metis Mprefix_Un_distrib Mprefix_singl insert_is_Un)

lemma finite_Mndetprefix_is_MultiNdet:
  \<open>finite A \<Longrightarrow> Mndetprefix A P = \<Sqinter> p \<in> A. (p \<rightarrow> P p)\<close>
  by (cases \<open>A = {}\<close>, simp, rotate_tac, induct rule: finite_set_induct_nonempty)
     (simp_all add: Mndetprefix_unit Mndetprefix_distrib_unit)


lemma \<open>Q \<box> (\<Sqinter> p \<in> {}. P p) = \<Sqinter> p \<in> {}. (Q \<box> P p) \<Longrightarrow> Q = STOP\<close>
  by (simp add: Det_STOP)

lemma Det_MultiNdet_distrib:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> M \<box> (\<Sqinter> p \<in> A. P p) = \<Sqinter> p \<in> A. M \<box> P p\<close>
  by (erule finite_set_induct_nonempty, simp_all add: Det_distrib)
 (* the nonempty hypothesis is necessary because 
     \<open>M \<box> (\<Sqinter> p \<in> {}. P p) = M \<box> STOP = M\<close> while \<open>\<Sqinter> p \<in> {}. (M \<box> P p) = STOP\<close> *)

lemma \<open>M \<sqinter> (\<^bold>\<box> p \<in> {}. P p) = \<^bold>\<box> p \<in> {}. (M \<sqinter> P p) \<Longrightarrow> M \<sqinter> STOP = STOP\<close> by simp

lemma Ndet_MultiDet_distrib:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> M \<sqinter> (\<^bold>\<box> p \<in> A. P p) = \<^bold>\<box> p \<in> A. M \<sqinter> P p\<close>
  by (erule finite_set_induct_nonempty, simp_all add: Ndet_distrib)
  (* the nonempty hypothesis is necessary because 
     \<open>M \<sqinter> (\<^bold>\<box> p \<in> {}. P p) = M \<sqinter> STOP\<close> while \<open>\<^bold>\<box> p \<in> {}. (M \<sqinter> P p) = STOP\<close> *)




lemma MultiNdet_Sync_left_distrib: 
  \<open>B \<noteq> {} \<Longrightarrow> finite B \<Longrightarrow> (\<Sqinter> a \<in> B. P a) \<lbrakk>S\<rbrakk> M = \<Sqinter> a \<in> B. (P a \<lbrakk>S\<rbrakk> M)\<close>
  by (induct rule: finite_set_induct_nonempty)
     (simp_all add: Sync_Ndet_left_distrib)

lemma MultiNdet_Sync_right_distrib:
  \<open>B \<noteq> {} \<Longrightarrow> finite B \<Longrightarrow> M \<lbrakk>S\<rbrakk> MultiNdet B P = \<Sqinter> a\<in>B. (M \<lbrakk>S\<rbrakk> P a)\<close>
  by (subst Sync_commute, subst MultiNdet_Sync_left_distrib)
     (simp_all add: Sync_commute)



lemma Sync_MultiNdet_cartprod:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> finite B \<Longrightarrow> 
   (\<Sqinter> (s, t) \<in> A \<times> B. (x s \<lbrakk>S\<rbrakk> y t)) = (\<Sqinter> s \<in> A. x s) \<lbrakk>S\<rbrakk> (\<Sqinter> t \<in> B. y t)\<close>
  apply (subst MultiNdet_cartprod, assumption+)
  apply (subst MultiNdet_Sync_left_distrib, assumption+)
  apply (subst MultiNdet_Sync_right_distrib, assumption+)
  by presburger


lemmas Inter_MultiNdet_cartprod = Sync_MultiNdet_cartprod[where S = \<open>{}\<close>]
   and   Par_MultiNdet_cartprod = Sync_MultiNdet_cartprod[where S = UNIV]
 

lemmas MultiNdet_Inter_left_distrib =
       MultiNdet_Sync_left_distrib[where S = \<open>{}\<close>]
   and   MultiNdet_Par_left_distrib =
       MultiNdet_Sync_left_distrib[where S = \<open>UNIV\<close>]



lemma Seq_MultiNdet_distribR:
  \<open>finite A \<Longrightarrow> (\<Sqinter> p \<in> A. P p) \<^bold>; S = (\<Sqinter> p \<in> A. (P p \<^bold>; S))\<close>
  by (induct A rule: finite_induct, simp add: STOP_Seq)
     (metis MultiNdet_insert' MultiNdet_rec1 Seq_Ndet_distrR)


lemma Seq_MultiNdet_distribL:
  \<open>A  \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> S \<^bold>; (\<Sqinter> p \<in> A. P p) = (\<Sqinter> p \<in> A. (S \<^bold>; P p))\<close>
  by (induct A rule: finite_set_induct_nonempty, simp_all add: Seq_Ndet_distrL)


lemma prefix_MultiNdet_distrib:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> (a \<rightarrow> (\<Sqinter> p \<in> A. P p) = \<Sqinter> p \<in> A. (a \<rightarrow> P p))\<close>
  by (induct A rule: finite_set_induct_nonempty, simp_all add: write0_Ndet)


lemma Mndetprefix_MultiNdet_distrib:
  \<open>(\<sqinter> q \<in> B \<rightarrow> (\<Sqinter> p \<in> A. P p q)) = \<Sqinter> p \<in> A. \<sqinter> q \<in> B \<rightarrow> P p q\<close>
  if finB: \<open>finite B\<close> and nonemptyA: \<open>A \<noteq> {}\<close> and finA: \<open>finite A\<close>
proof (cases \<open>B = {}\<close>)
  case True thus ?thesis by (simp add: MultiNdet_STOP_id finA)
next
  case False thus ?thesis
  proof (insert finB, induct B rule: finite_set_induct_nonempty)
    case (singleton a)
    thus ?case
      by (simp add: Mndetprefix_unit finA prefix_MultiNdet_distrib nonemptyA)
  next  
    case (insertion x F)
    show ?case
      apply (subst Mndetprefix_Un_distrib[of \<open>{x}\<close>, simplified, OF \<open>F \<noteq> {}\<close>])
      apply (subst Mndetprefix_unit,
             subst prefix_MultiNdet_distrib[OF nonemptyA finA])
      apply (subst insertion.hyps(5))
      apply (subst MultiNdet_Ndet[OF finA])
      by (insert \<open>F \<noteq> {}\<close> \<open>x \<notin> F\<close>, subst Mndetprefix_distrib_unit) force+
  qed
qed


lemma MultiDet_Mprefix:
  \<open>finite A \<Longrightarrow> (\<^bold>\<box>a \<in> A. \<box>x \<in> S a \<rightarrow> P a x) =
                \<box>x \<in> (\<Union>a \<in> A. S a) \<rightarrow> \<Sqinter> a \<in> {a \<in> A. x \<in> S a}. P a x\<close>
proof (induct A rule: induct_subset_empty_single)
  case 1
  show ?case by (simp add: Mprefix_STOP)
next
  case 2
  show ?case
    by (simp, intro ballI mono_Mprefix_eq)
       (simp add: Collect_conv_if) 
next
  case (3 F a)
  show ?case
    apply (simp del: MultiDet_insert add: \<open>finite F\<close>) 
    apply (subst "3.hyps")
    apply (subst Mprefix_Det_distr)
    apply (intro mono_Mprefix_eq ballI)
    using \<open>finite F\<close> by (auto simp add: Process_eq_spec F_MultiNdet F_Ndet D_MultiNdet D_Ndet)
qed
 

lemma MultiDet_prefix_is_MultiNdet_prefix:
  \<open>finite A \<Longrightarrow> (\<^bold>\<box> p \<in> A. (a \<rightarrow> P p)) = \<Sqinter> p \<in> A. (a \<rightarrow> P p)\<close>
  by (induct A rule: induct_subset_empty_single, simp, simp)
     (metis MultiDet_insert' MultiNdet_insert' prefix_MultiNdet_distrib write0_Det_Ndet)
 

lemma prefix_MultiNdet_is_MultiDet_prefix:
  \<open>A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> (a \<rightarrow> (\<Sqinter> p \<in> A. P p) = \<^bold>\<box> p \<in> A. (a \<rightarrow> P p))\<close>
  by (simp add: MultiDet_prefix_is_MultiNdet_prefix prefix_MultiNdet_distrib)



lemma Mprefix_MultiNdet_distrib':
  \<open>finite B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> 
   (\<box> q \<in> B \<rightarrow> \<Sqinter> p \<in> A. P p q) = \<^bold>\<box> p \<in> A. \<box> q \<in> B \<rightarrow> P p q\<close>
proof (induct B rule: finite_induct)
  case empty
  thus ?case by (simp add: Mprefix_STOP MultiDet_STOP_id)
next
  case (insert x F)
  show ?case
    apply (subst (1 2) Mprefix_Un_distrib[of \<open>{x}\<close> F, simplified])
    apply (subst Mprefix_singl, subst prefix_MultiNdet_distrib[OF insert.prems])
    apply (subst MultiDet_prefix_is_MultiNdet_prefix[symmetric, OF \<open>finite A\<close>])
    apply (subst insert.hyps(3)[OF insert.prems])
    apply (subst MultiDet_Det[OF \<open>finite A\<close>],
           rule mono_MultiDet_eq[OF \<open>finite A\<close>])
    by (subst Mprefix_singl) fast
qed


lemma MultiSync_Hiding_pseudo_distrib:
  \<open>finite B \<Longrightarrow> B \<inter> S = {} \<Longrightarrow> 
   (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. ((P p) \ B)) = (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. P p) \ B\<close>
  by (induct M, simp add: Hiding_set_STOP)
     (metis MultiSync_add MultiSync_rec1 Hiding_Sync)


lemma MultiSync_prefix_pseudo_distrib:
  \<open>M \<noteq> {#} \<Longrightarrow> a \<in> S \<Longrightarrow>
   ((\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. (a \<rightarrow> P p)) = (a \<rightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. P p)))\<close>
  by (induct M rule: mset_induct_nonempty) (simp_all add: prefix_Sync2)

lemmas MultiInter_Hiding_pseudo_distrib =
       MultiSync_Hiding_pseudo_distrib[where S = \<open>{}\<close>, simplified]
   and MultiPar_prefix_pseudo_distrib =
       MultiSync_prefix_pseudo_distrib[where S = \<open>UNIV\<close>, simplified]



lemma Hiding_MultiNdet_distrib:
  \<open>finite A \<Longrightarrow> (\<Sqinter> p \<in> A. P p) \ B = (\<Sqinter> p \<in> A. (P p \ B))\<close>
  by (cases \<open>A = {}\<close>, simp add: Hiding_set_STOP, rotate_tac)
     (induct A rule: finite_set_induct_nonempty, simp_all add: Hiding_Ndet)


lemma Mndetprefix_Hiding_is_MultiNdet_prefix_Hiding:
  \<open>finite A \<Longrightarrow> \<sqinter> p \<in> A - B \<rightarrow> ((P p) \ B) = \<Sqinter> p \<in> A - B. (p \<rightarrow> ((P p) \ B))\<close>
proof (induct A rule: finite_induct)
  case empty
  thus ?case by fastforce
next
  show \<open>finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> 
        \<sqinter> p \<in> F - B \<rightarrow>  (P p \ B) = \<Sqinter> p \<in> F - B.  (p \<rightarrow> (P p \ B)) \<Longrightarrow>
        \<sqinter> p \<in> insert x F - B \<rightarrow> (P p \ B) =
        \<Sqinter> p \<in> insert x F - B.  (p \<rightarrow> (P p \ B))\<close> for x F
    apply (cases \<open>x \<in> B\<close>, simp)
    apply (cases \<open>F - B = {}\<close>,
           metis (no_types, lifting) Mndetprefix_unit MultiNdet_rec1 insert_Diff_if)
    by (simp add: Mndetprefix_distrib_unit insert_Diff_if)
qed


lemma Hiding_Mndetprefix_is_MultiNdet_Hiding:
  \<open>finite A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<sqinter> a \<in> A \<rightarrow> P) \ B = \<Sqinter> a \<in> A. (P \ B)\<close>
  by (cases \<open>A = {}\<close>, simp add: Hiding_set_STOP, rotate_tac 2)
     (induct A rule: finite_set_induct_nonempty,
      simp_all add: Mndetprefix_unit Hiding_Ndet Hiding_write0
                    Mndetprefix_distrib_unit)



lemma MultiSync_Mprefix_pseudo_distrib:
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> B \<in># M. \<box> x \<in> B \<rightarrow> P B x) =
   \<box> x \<in> (\<Inter>B \<in> set_mset M. B) \<rightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> B \<in># M. P B x)\<close>
  if nonempty: \<open>M \<noteq> {#}\<close> and hyp: \<open>\<forall> B \<in># M. B \<subseteq> S\<close>
proof-
  from nonempty obtain b M' where \<open>b \<in># M - M'\<close>
                                  \<open> M = add_mset b M'\<close> \<open>M' \<subseteq># M\<close>
    by (metis add_diff_cancel_left' diff_subset_eq_self insert_DiffM
              insert_DiffM2 multi_member_last multiset_nonemptyE)
  show ?thesis
    apply (subst (1 2 3) \<open>M = add_mset b M'\<close>)
    using \<open>b \<in># M - M'\<close> \<open>M' \<subseteq># M\<close>
  proof (induct rule: msubset_induct_singleton')
    case m_singleton show ?case by fastforce
  next
    case (add x F) show ?case
      apply (simp, subst Mprefix_Sync_distr_subset[symmetric])
        apply (meson add.hyps(1) hyp in_diffD,
               metis \<open>b \<in># M - M'\<close> hyp in_diffD le_infI1)
      using add.hyps(3) by fastforce
  qed
qed



lemmas MultiPar_Mprefix_pseudo_distrib =
       MultiSync_Mprefix_pseudo_distrib[where S = \<open>UNIV\<close>, simplified]



text \<open>A result on Mndetprefix and Sync.\<close>

lemma Mndetprefix_Sync_distr: \<open>A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> 
       (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<sqinter> b \<in> B \<rightarrow> Q b) =
        \<sqinter> a\<in>A. \<sqinter> b\<in>B. (\<box>c \<in> {a} - S \<rightarrow> (P a \<lbrakk>S\<rbrakk> (b \<rightarrow> Q b))) \<box> 
                       (\<box>d \<in> {b} - S \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b)) \<box>
                       (\<box>c\<in>{a} \<inter> {b} \<inter> S \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q b))\<close>
  apply (subst (1 2) Mndetprefix_GlobalNdet) 
  apply (subst GlobalNdet_Sync_distr, assumption)
  apply (subst Sync_commute)
  apply (subst GlobalNdet_Sync_distr, assumption)
  apply (subst Sync_commute)
  apply (unfold write0_def)
  apply (subst Mprefix_Sync_distr_bis)
  by (fold write0_def) blast



text \<open>A result on \<^const>\<open>MultiSeq\<close> with \<^const>\<open>non_terminating\<close>.\<close>

lemma non_terminating_MultiSeq: 
  \<open>(SEQ a \<in>@ L. P a) =
   SEQ a \<in>@ take (Suc (first_elem (\<lambda>a. non_terminating (P a)) L)) L. P a\<close>
  by (induct L; simp add: non_terminating_Seq)



section \<open>Results on \<^const>\<open>Renaming\<close>\<close>

lemma Renaming_GlobalNdet:
  \<open>Renaming (\<sqinter> a \<in> A. P (f a)) f = \<sqinter> b \<in> f ` A. Renaming (P b) f\<close>
  by (subst Process_eq_spec)
     (auto simp add: F_Renaming D_Renaming F_GlobalNdet D_GlobalNdet)

lemma Renaming_GlobalNdet_inj_on:
  \<open>Renaming (\<sqinter> a \<in> A. P a) f =
   \<sqinter> b \<in> f ` A. Renaming (P (THE a. a \<in> A \<and> f a = b)) f\<close>
  if inj_on_f: \<open>inj_on f A\<close>
  apply (subst Renaming_GlobalNdet[symmetric])
  apply (intro arg_cong[where f = \<open>\<lambda>Q. Renaming Q f\<close>] mono_GlobalNdet_eq)
  by (metis inj_on_f the_inv_into_def the_inv_into_f_f)

corollary Renaming_GlobalNdet_inj:
  \<open>Renaming (\<sqinter> a \<in> A. P a) f =
   \<sqinter> b \<in> f ` A. Renaming (P (THE a. f a = b)) f\<close> if inj_f: \<open>inj f\<close>
  apply (subst Renaming_GlobalNdet_inj_on, metis inj_eq inj_onI inj_f)
  apply (rule mono_GlobalNdet_eq[rule_format])
  by (metis imageE inj_eq[OF inj_f])



lemma Renaming_MultiNdet: \<open>finite A \<Longrightarrow> Renaming (\<Sqinter> a \<in> A. P (f a)) f =
                                        \<Sqinter> b \<in> f ` A. Renaming (P b) f\<close>
  by (subst (1 2) finite_GlobalNdet_is_MultiNdet[symmetric])
     (simp_all add: Renaming_GlobalNdet)
  

lemma Renaming_MultiNdet_inj_on:
  \<open>finite A \<Longrightarrow> inj_on f A \<Longrightarrow>
   Renaming (\<Sqinter> a \<in> A. P a) f = 
   \<Sqinter> b \<in> f ` A. Renaming (P (THE a. a \<in> A \<and> f a = b)) f\<close> 
  by (subst (1 2) finite_GlobalNdet_is_MultiNdet[symmetric])
     (simp_all add: Renaming_GlobalNdet_inj_on)
 

corollary Renaming_MultiNdet_inj:
  \<open>finite A \<Longrightarrow> inj f \<Longrightarrow>
   Renaming (\<Sqinter> a \<in> A. P a) f = \<Sqinter> b \<in> f ` A. Renaming (P (THE a. f a = b)) f\<close>
  by (subst (1 2) finite_GlobalNdet_is_MultiNdet[symmetric])
     (simp_all add: Renaming_GlobalNdet_inj)



lemma Renaming_MultiDet:
  \<open>finite A \<Longrightarrow> Renaming (\<^bold>\<box> a \<in> A. P (f a)) f = 
                \<^bold>\<box> b \<in> f ` A. Renaming (P b) f\<close>
  apply (induct A rule: finite_induct)
  by (simp_all add: Renaming_STOP Renaming_Det del: MultiDet_insert)

lemma Renaming_MultiDet_inj_on:
  \<open>Renaming (\<^bold>\<box> a \<in> A. P a) f =
   \<^bold>\<box> b \<in> f ` A. Renaming (P (THE a. a \<in> A \<and> f a = b)) f\<close>
  if finite_A: \<open>finite A\<close> and inj_on_f: \<open>inj_on f A\<close>
  apply (subst Renaming_MultiDet[OF finite_A, symmetric])
  apply (intro arg_cong[where f = \<open>\<lambda>Q. Renaming Q f\<close>]
               mono_MultiDet_eq finite_A)
  by (metis inj_on_f the_inv_into_def the_inv_into_f_f)

corollary Renaming_MultiDet_inj:
  \<open>Renaming (\<^bold>\<box> a \<in> A. P a) f = \<^bold>\<box> b \<in> f ` A. Renaming (P (THE a. f a = b)) f\<close>
  if finite_A: \<open>finite A\<close> and inj_f: \<open>inj f\<close>
  apply (subst Renaming_MultiDet_inj_on[OF finite_A], metis inj_eq inj_onI inj_f)
  apply (rule mono_MultiDet_eq[rule_format], fact finite_imageI[OF finite_A])
  by (metis imageE inj_eq[OF inj_f])



lemma Renaming_MultiSeq:
  \<open>Renaming (SEQ l \<in>@ L. P (f l)) f = SEQ m \<in>@ map f L. Renaming (P m) f\<close>
  by (induct L, simp_all add: Renaming_SKIP Renaming_Seq)

lemma Renaming_MultiSeq_inj_on:
  \<open>Renaming (SEQ l \<in>@ L. P l) f =
   SEQ m \<in>@ map f L. Renaming (P (THE l. l \<in> set L \<and> f l = m)) f\<close>
  if inj_on_f: \<open>inj_on f (set L)\<close>
  apply (subst Renaming_MultiSeq[symmetric])
  apply (intro arg_cong[where f = \<open>\<lambda>Q. Renaming Q f\<close>] mono_MultiSeq_eq)
  by (metis that the_inv_into_def the_inv_into_f_f)

corollary Renaming_MultiSeq_inj:
  \<open>Renaming (SEQ l \<in>@ L. P l) f = 
   SEQ m \<in>@ map f L. Renaming (P (THE l. f l = m)) f\<close> if inj_f: \<open>inj f\<close>
  apply (subst Renaming_MultiSeq_inj_on, metis inj_eq inj_onI inj_f)
  apply (rule mono_MultiSeq_eq[rule_format])
  by (metis (mono_tags, opaque_lifting) inj_image_mem_iff list.set_map inj_f)



end