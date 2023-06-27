(*<*)
\<comment>\<open> ********************************************************************
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye, Benoît Ballenghien, Catherine Dubois
 *
 * This file       : A Normalization Theory
 *
 * Copyright (c) 2022 Université Paris-Saclay, France
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


chapter\<open> Generalisation of Normalisation of Non Deterministic CSP Processes \<close>

theory CSP
  imports CSP_Laws Process_Order (*Induction*)
begin





section \<open>Monotonicity\<close>

lemma mono_Det_D[simp]: \<open>\<lbrakk>P \<sqsubseteq>\<^sub>D P'; S \<sqsubseteq>\<^sub>D S'\<rbrakk> \<Longrightarrow> (P \<box> S) \<sqsubseteq>\<^sub>D (P' \<box> S')\<close>
  by (metis D_Det Un_mono divergence_refine_def)

lemma mono_Det_T[simp]: \<open>\<lbrakk>P \<sqsubseteq>\<^sub>T P'; S \<sqsubseteq>\<^sub>T S'\<rbrakk> \<Longrightarrow> (P \<box> S) \<sqsubseteq>\<^sub>T (P' \<box> S')\<close>
  by (metis T_Det Un_mono trace_refine_def)

corollary mono_Det_DT[simp]: \<open>\<lbrakk>P \<sqsubseteq>\<^sub>D\<^sub>T P'; S \<sqsubseteq>\<^sub>D\<^sub>T S'\<rbrakk> \<Longrightarrow> (P \<box> S) \<sqsubseteq>\<^sub>D\<^sub>T (P' \<box> S')\<close>
  by (simp_all add: trace_divergence_refine_def)

lemmas mono_Det_FD[simp]= mono_Det_FD[folded failure_divergence_refine_def]

\<comment>\<open>Deterministic choice monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>F\<close>\<close>



lemma mono_Ndet_F_left[simp]: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>F Q\<close>
  by (simp add: F_Ndet failure_refine_def order_trans) 

lemma mono_Ndet_D_left[simp]: \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>D Q\<close>
  by (simp add: D_Ndet divergence_refine_def order_trans) 

lemma mono_Ndet_T_left[simp]: \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>T Q\<close>
  by (simp add: T_Ndet trace_refine_def order_trans) 

section \<open>Monotonicity\<close>

lemma mono_Ndet_F[simp]: \<open>\<lbrakk>P \<sqsubseteq>\<^sub>F P'; S \<sqsubseteq>\<^sub>F S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>F (P' \<sqinter> S')\<close>
  by (metis F_Ndet Un_mono failure_refine_def) 

lemma mono_Ndet_D[simp]: \<open>\<lbrakk>P \<sqsubseteq>\<^sub>D P'; S \<sqsubseteq>\<^sub>D S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>D (P' \<sqinter> S')\<close>
  by (metis D_Ndet Un_mono divergence_refine_def)

lemma mono_Ndet_T[simp]: \<open>\<lbrakk>P \<sqsubseteq>\<^sub>T P'; S \<sqsubseteq>\<^sub>T S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>T (P' \<sqinter> S')\<close>
  by (metis T_Ndet Un_mono trace_refine_def) 


corollary mono_Ndet_DT[simp]: \<open>\<lbrakk>P \<sqsubseteq>\<^sub>D\<^sub>T P'; S \<sqsubseteq>\<^sub>D\<^sub>T S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>D\<^sub>T (P' \<sqinter> S')\<close>
  by (auto simp add: trace_divergence_refine_def)

lemmas mono_Ndet_FD[simp]= mono_Ndet_FD[folded failure_divergence_refine_def]


corollary  mono_Ndet_DT_left[simp]: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
      and  mono_Ndet_F_right[simp]: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> (S \<sqinter> P) \<sqsubseteq>\<^sub>F Q\<close>
      and  mono_Ndet_D_right[simp]: \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> (S \<sqinter> P) \<sqsubseteq>\<^sub>D Q\<close>
      and  mono_Ndet_T_right[simp]: \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> (S \<sqinter> P) \<sqsubseteq>\<^sub>T Q\<close>
      and mono_Ndet_DT_right[simp]: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> (S \<sqinter> P) \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (simp_all add: trace_divergence_refine_def Ndet_commute) 
  

lemmas mono_Ndet_FD_left[simp] = mono_Ndet_FD_left[folded failure_divergence_refine_def]
   and mono_Ndet_FD_right[simp] = mono_Ndet_FD_right[folded failure_divergence_refine_def]

lemma mono_Ndet_Det_FD[simp]: \<open>(P \<sqinter> S) \<sqsubseteq>\<^sub>F\<^sub>D (P \<box> S)\<close>
  by (metis Det_id failure_divergence_refine_def mono_Det_FD mono_Ndet_FD_left 
            mono_Ndet_FD_right order_refl) 


corollary  mono_Ndet_Det_F[simp]: \<open>(P \<sqinter> S) \<sqsubseteq>\<^sub>F (P \<box> S)\<close>
      and  mono_Ndet_Det_D[simp]: \<open>(P \<sqinter> S) \<sqsubseteq>\<^sub>D (P \<box> S)\<close>
      and  mono_Ndet_Det_T[simp]: \<open>(P \<sqinter> S) \<sqsubseteq>\<^sub>T (P \<box> S)\<close>
      and mono_Ndet_Det_DT[simp]: \<open>(P \<sqinter> S) \<sqsubseteq>\<^sub>D\<^sub>T (P \<box> S)\<close> 
  by (simp_all add: leFD_imp_leF leFD_imp_leD leF_imp_leT leD_leT_imp_leDT) 


lemma mono_Seq_F_right[simp]: \<open>S \<sqsubseteq>\<^sub>F S' \<Longrightarrow> (P \<^bold>; S) \<sqsubseteq>\<^sub>F (P \<^bold>; S')\<close>
  apply (auto simp: failure_refine_def F_Seq append_single_T_imp_tickFree)
  using NF_ND by fastforce+

lemma mono_Seq_D_right[simp]: \<open>S \<sqsubseteq>\<^sub>D S' \<Longrightarrow> (P \<^bold>; S) \<sqsubseteq>\<^sub>D (P \<^bold>; S')\<close>
  by (auto simp: divergence_refine_def D_Seq)

lemma  mono_Seq_T_right[simp]: \<open>S \<sqsubseteq>\<^sub>T S' \<Longrightarrow> (P \<^bold>; S) \<sqsubseteq>\<^sub>T (P \<^bold>; S')\<close>
  apply (auto simp: trace_refine_def T_Seq append_single_T_imp_tickFree)
  using D_T by fastforce+

corollary mono_Seq_DT_right[simp]: \<open>S \<sqsubseteq>\<^sub>D\<^sub>T S' \<Longrightarrow> (P \<^bold>; S)  \<sqsubseteq>\<^sub>D\<^sub>T (P \<^bold>; S')\<close>
  by (simp add: trace_divergence_refine_def)

lemma mono_Seq_DT_left[simp]: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> (P \<^bold>; S)  \<sqsubseteq>\<^sub>D\<^sub>T (P' \<^bold>; S)\<close>
  apply (auto simp: trace_divergence_refine_def divergence_refine_def trace_refine_def D_Seq T_Seq)
  by (metis (no_types, lifting) Nil_elem_T Process.F_T T_F append.right_neutral 
            is_processT5_S3 subset_eq) 

\<comment>\<open>left Sequence monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>F\<close>, \<open>\<sqsubseteq>\<^sub>D\<close> and \<open>\<sqsubseteq>\<^sub>T\<close>\<close>

corollary mono_Seq_DT[simp]: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> S \<sqsubseteq>\<^sub>D\<^sub>T S' \<Longrightarrow> (P \<^bold>; S)  \<sqsubseteq>\<^sub>D\<^sub>T (P' \<^bold>; S')\<close>
  using mono_Seq_DT_left mono_Seq_DT_right trans_DT by blast
  
lemmas mono_Seq_FD[simp]= mono_Seq_FD[folded failure_divergence_refine_def]


lemma mono_Mprefix_F[simp]: \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>F Mprefix A Q\<close>
  by (auto simp: failure_refine_def F_Mprefix) blast+

lemma mono_Mprefix_D[simp]: \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>D Mprefix A Q\<close>
  by (auto simp: divergence_refine_def D_Mprefix) blast+

lemma mono_Mprefix_T[simp]: \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>T Mprefix A Q\<close>
  by (auto simp: trace_refine_def T_Mprefix)

corollary mono_Mprefix_DT[simp]: \<open>\<forall>x \<in> A. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>D\<^sub>T Mprefix A Q\<close>
  by (simp add: trace_divergence_refine_def)

lemmas mono_Mprefix_FD[simp] = mono_Mprefix_FD[folded failure_divergence_refine_def]

lemma mono_Mprefix_DT_set[simp]: \<open>A \<subseteq> B \<Longrightarrow> Mprefix B P \<sqsubseteq>\<^sub>D\<^sub>T Mprefix A P\<close> (* rename this in mono_Mprefix_D_subset ? *)
  by (auto simp add:T_Mprefix D_Mprefix trace_divergence_refine_def 
                    trace_refine_def divergence_refine_def)

corollary mono_Mprefix_D_set[simp]: \<open>A \<subseteq> B \<Longrightarrow> Mprefix B P \<sqsubseteq>\<^sub>D Mprefix A P\<close>
      and mono_Mprefix_T_set[simp]: \<open>A \<subseteq> B \<Longrightarrow> Mprefix B P \<sqsubseteq>\<^sub>T Mprefix A P\<close>
  by (simp_all add: leDT_imp_leD leDT_imp_leT)

\<comment>\<open>Mprefix set monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>F\<close> and \<open>\<sqsubseteq>\<^sub>F\<^sub>D\<close> where it holds for deterministic choice\<close>


lemma mono_Hiding_F[simp]: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> (P \ A) \<sqsubseteq>\<^sub>F (Q \ A)\<close>
  apply(cases \<open>A = {}\<close>, simp_all add: Hiding_set_empty failure_refine_def F_Hiding, intro conjI, blast)
proof(subst (2) Un_commute, rule subsetI, rule UnCI, auto, goal_cases)
  case (1 b t u)
  then obtain a where a:\<open>a \<in> A\<close> by blast
  define f where A: \<open>f = rec_nat t (\<lambda>i t. t @ [ev a])\<close> 
  hence AA: \<open>f (Suc i) = (f i) @ [ev a]\<close> for i by simp
  hence B: \<open>strict_mono f\<close> by (simp add:strict_mono_def lift_Suc_mono_less_iff)
  from A have C: \<open>t \<in> range f\<close> by (metis (mono_tags, lifting) old.nat.simps(6) range_eqI)
  { fix i
    have \<open>f i \<in> \<D> Q \<and> tickFree (f i) \<and> trace_hide (f i) (ev ` A) = (trace_hide t (ev ` A))\<close>
    proof(induct i)
      case 0
      then show ?case by (simp add: 1(4) 1(7) A)
    next
      case (Suc i)
      then show ?case 
        apply (simp add:AA a) 
        using is_processT7[rule_format, of \<open>f i\<close> Q \<open>[ev a]\<close>] front_tickFree_single by blast 
    qed
  } 
  with B C have \<open>isInfHiddenRun f P A \<and> t \<in> range f\<close> 
    by (metis 1(1) D_T F_subset_imp_T_subset subsetD)
  with 1 show ?case by metis
next
  case (2 b u f x)
  then show ?case using F_subset_imp_T_subset by blast 
qed 

lemma mono_Hiding_T[simp]: \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> (P \ A) \<sqsubseteq>\<^sub>T (Q \ A)\<close>
  apply(cases \<open>A={}\<close>, simp add: Hiding_set_empty, 
                      simp add:trace_refine_def T_Hiding, intro conjI)
proof(goal_cases)
  case 1
  then show ?case
  proof(subst Un_commute, rule_tac subsetI, rule_tac UnCI, auto, goal_cases)
    case 11:(1 t a)
    hence tt: \<open>t \<in> \<T> P\<close> by (meson Process.F_T subset_eq) 
    with 11(1) inf_hidden[of A t P] obtain f where \<open>isInfHiddenRun f P A \<and> t \<in> range f\<close> by auto
    with 11(4)[rule_format, of t \<open>[]\<close>] show ?case
      by (metis 11(1) tt append_Nil2 front_tickFree_Nil is_processT2_TR 
                nonTickFree_n_frontTickFree tick_T_F)
  qed
next
  case 2
  then show ?case
  proof(subst Un_commute, auto, goal_cases)
    case 21:(1 t u a)
    define f where A: \<open>f = rec_nat t (\<lambda>i t. t @ [ev a])\<close> 
    hence AA: \<open>f (Suc i) = (f i) @ [ev a]\<close> for i by simp
    hence B: \<open>strict_mono f\<close> by (simp add:strict_mono_def lift_Suc_mono_less_iff)
    from A have C: \<open>t \<in> range f\<close> 
      by (metis (mono_tags, lifting) old.nat.simps(6) range_eqI)
    { fix i
      have \<open>f i \<in> \<D> Q \<and> tickFree (f i) \<and> trace_hide (f i) (ev ` A) = (trace_hide t (ev ` A))\<close>
      proof(induct i)
        case 0
        then show ?case by (simp add: 21(4) 21(7) A)
      next
        case (Suc i)
        then show ?case 
          apply (simp add:AA 21(6)) 
          using is_processT7[rule_format, of \<open>f i\<close> Q \<open>[ev a]\<close>] front_tickFree_single by blast 
      qed
    } 
    with B C have \<open>isInfHiddenRun f P A \<and> t \<in> range f\<close> by (metis 21(1) D_T subsetD)
    with 21 show ?case by metis
  next
    case 22:(2 b u f x)
    then show ?case by blast
  qed
qed

lemma mono_Hiding_DT[simp]: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> (P \ A) \<sqsubseteq>\<^sub>D\<^sub>T (Q \ A)\<close>
proof -
  assume as: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  then have \<open>(P \ A) \<sqsubseteq>\<^sub>D (Q \ A)\<close>
    apply(auto simp:trace_divergence_refine_def divergence_refine_def 
                    trace_refine_def D_Hiding T_Hiding)
    by blast+
  with leDT_imp_leT[THEN mono_Hiding_T, OF as] show ?thesis by (simp add: trace_divergence_refine_def) 
qed

lemmas mono_Hiding_FD[simp] = mono_Hiding_FD[folded failure_divergence_refine_def]

\<comment>\<open>Obviously, Hide monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>D\<close>\<close>


lemma mono_Sync_DT[simp]: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> (P \<lbrakk> A \<rbrakk> Q) \<sqsubseteq>\<^sub>D\<^sub>T (P' \<lbrakk> A \<rbrakk> Q')\<close>
  by (simp add:trace_divergence_refine_def divergence_refine_def trace_refine_def T_Sync D_Sync) 
     blast

lemmas mono_Sync_FD[simp] = mono_Sync_FD[folded failure_divergence_refine_def]

\<comment>\<open>Synchronization monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>F\<close>, \<open>\<sqsubseteq>\<^sub>D\<close> and \<open>\<sqsubseteq>\<^sub>T\<close>\<close>


(* choose between mono_Mndetprefix_F and mono_mndet_F *)
lemma mono_Mndetprefix_F[simp]: \<open>\<forall>x\<in>A. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>F Mndetprefix A Q\<close>
  by (cases \<open>A = {}\<close>, auto simp: failure_refine_def F_Mndetprefix write0_def F_Mprefix) 

lemma mono_Mndetprefix_D[simp]: \<open>\<forall>x\<in>A. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>D Mndetprefix A Q\<close>
  by (cases \<open>A = {}\<close>, auto simp: divergence_refine_def D_Mndetprefix write0_def D_Mprefix)

lemma mono_Mndetprefix_T[simp]: \<open>\<forall>x\<in>A. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>T Mndetprefix A Q\<close>
  by (cases \<open>A = {}\<close>, auto simp: trace_refine_def T_Mndetprefix write0_def T_Mprefix)

corollary mono_Mndetprefix_DT[simp]: \<open>\<forall>x\<in>A. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> Mndetprefix A P \<sqsubseteq>\<^sub>D\<^sub>T Mndetprefix A Q\<close>
  by (simp add: trace_divergence_refine_def)
  
lemmas mono_Mndetprefix_FD[simp] = mono_Mndetprefix_FD[folded failure_divergence_refine_def]

lemmas mono_Mndetprefix_FD_set[simp] = Mndetprefix_FD_subset[folded failure_divergence_refine_def]

corollary mono_Mndetprefix_F_set[simp] : \<open>A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Mndetprefix B P \<sqsubseteq>\<^sub>F Mndetprefix A P\<close>
      (* removed nonempty hypothesis in the 3 following propositions *)
      and mono_Mndetprefix_D_set[simp] : \<open>A \<subseteq> B \<Longrightarrow> Mndetprefix B P \<sqsubseteq>\<^sub>D  Mndetprefix A P\<close>
      and mono_Mndetprefix_T_set[simp] : \<open>A \<subseteq> B \<Longrightarrow> Mndetprefix B P \<sqsubseteq>\<^sub>T  Mndetprefix A P\<close>
      and mono_Mndetprefix_DT_set[simp]: \<open>A \<subseteq> B \<Longrightarrow> Mndetprefix B P \<sqsubseteq>\<^sub>D\<^sub>T Mndetprefix A P\<close>
  by (cases \<open>A = {}\<close>, simp_all add: leFD_imp_leF leFD_imp_leD leF_imp_leT leD_leT_imp_leDT)+

lemmas Mprefix_refines_Mndetprefix_FD[simp] = 
       Mprefix_refines_Mndetprefix[folded failure_divergence_refine_def]

corollary Mprefix_refines_Mndetprefix_F[simp] : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>F  Mprefix A P\<close>
      and Mprefix_refines_Mndetprefix_D[simp] : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>D  Mprefix A P\<close>
      and Mprefix_refines_Mndetprefix_T[simp] : \<open>Mndetprefix A P \<sqsubseteq>\<^sub>T  Mprefix A P\<close>
      and Mprefix_refines_Mndetprefix_DT[simp]: \<open>Mndetprefix A P \<sqsubseteq>\<^sub>D\<^sub>T Mprefix A P\<close>
  by (simp_all add: leFD_imp_leF leFD_imp_leD leF_imp_leT leD_leT_imp_leDT) 



(* see where we put this *)


lemma mono_read_FD[simp, elim]: "(\<And>x. P x \<sqsubseteq>\<^sub>F\<^sub>D Q x) \<Longrightarrow> (c\<^bold>?x \<rightarrow> (P x)) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>?x \<rightarrow> (Q x))"
  by (simp add: read_def)

lemma mono_write_FD[simp, elim]: "(P \<sqsubseteq>\<^sub>F\<^sub>D Q) \<Longrightarrow>  (c\<^bold>!x \<rightarrow> P) \<sqsubseteq>\<^sub>F\<^sub>D (c\<^bold>!x \<rightarrow> Q)"
  by (simp add: write_def)

lemma mono_write0_FD[simp, elim]: "P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> (a \<rightarrow> P) \<sqsubseteq>\<^sub>F\<^sub>D (a \<rightarrow> Q)"
  by (simp add: write0_def)

(* make this with \<sqsubseteq>\<^sub>D \<sqsubseteq>\<^sub>T and \<sqsubseteq>\<^sub>F ? *)
lemma mono_read_DT[simp, elim]: "(\<And>x. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x) \<Longrightarrow> (c\<^bold>?x \<rightarrow> (P x)) \<sqsubseteq>\<^sub>D\<^sub>T (c\<^bold>?x \<rightarrow> (Q x))"
  by (simp add: read_def)

lemma mono_write_DT[simp, elim]: "(P \<sqsubseteq>\<^sub>D\<^sub>T Q) \<Longrightarrow>  (c\<^bold>!x \<rightarrow> P) \<sqsubseteq>\<^sub>D\<^sub>T (c\<^bold>!x \<rightarrow> Q)"
  by (simp add: write_def)

lemma mono_write0_DT[simp, elim]: "P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> (a \<rightarrow> P) \<sqsubseteq>\<^sub>D\<^sub>T (a \<rightarrow> Q)"
  by (simp add: write0_def)



\<comment> \<open>The following result is very useful, but we are not sure about where is its place\<close>

lemma cont_process_rec: \<open>P = (\<mu> X. f X) \<Longrightarrow> cont f \<Longrightarrow> P = f P\<close> by (simp add: def_cont_fix_eq)



end