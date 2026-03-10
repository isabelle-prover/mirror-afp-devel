(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
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


chapter \<open>Advanced Properties of ProcOmata\<close>

(*<*)
theory Process_Normalization_Properties
  imports Process_Normalization Deterministic_Processes
begin
  (*<*)


section \<open>Determinism of deterministic ProcOmata\<close>

lemma deterministic_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d : \<open>deterministic (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>)\<close>
proof (induct A arbitrary: \<sigma> rule: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_induct)
  show \<open>adm\<^sub>\<down> (\<lambda>f. \<forall>x. deterministic (f x))\<close> by simp
next
  show \<open>deterministic STOP\<close> by simp
next
  show \<open>(\<And>\<sigma>. deterministic (X \<sigma>)) \<Longrightarrow>
        deterministic (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step (\<epsilon> A) (\<tau> A) (\<omega> A) X \<sigma>)\<close> for X \<sigma>
    by (simp add: deterministic_Mprefix_iff split: option.split)
qed

corollary deterministic_P_d : \<open>deterministic (P\<llangle>A\<rrangle>\<^sub>d \<sigma>)\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>) (fact deterministic_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_FD_imp_eq_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d : \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> P = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
  using deterministic_iff_maximal_for_leFD[THEN iffD1, OF deterministic_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d] by fast

corollary P_d_FD_imp_eq_P_d : \<open>P\<llangle>A\<rrangle>\<^sub>d \<sigma> \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> P = P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
  using deterministic_iff_maximal_for_leFD[THEN iffD1, OF deterministic_P_d] by fast



section \<open>No Divergence for ProcOmata\<close>

lemma div_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd : \<open>\<D> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) = {}\<close>
proof (induct A arbitrary: \<sigma> rule: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_induct)
  have \<open>adm\<^sub>\<down> (\<lambda>X. \<forall>\<sigma> t. t \<in> \<D> (X \<sigma>) \<longrightarrow> False)\<close>
    by (intro restriction_adm_all restriction_adm_imp) simp_all
  thus \<open>adm\<^sub>\<down> (\<lambda>X. \<forall>\<sigma>. \<D> (X \<sigma>) = {})\<close> by simp
next
  from D_STOP show \<open>\<D> STOP = {}\<close> .
next
  show \<open>(\<And>\<sigma>. \<D> (X \<sigma>) = {}) \<Longrightarrow> \<D> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) X \<sigma>) = {}\<close> for X \<sigma>
    by (simp add: D_Mprefix D_GlobalNdet D_SKIPS)
qed

corollary div_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d : \<open>\<D> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) = {}\<close>
  by (simp add: deterministic_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d deterministic_div_free)

corollary div_free_P_nd : \<open>\<D> (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d s) = {}\<close>
  by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega> div_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)

corollary div_free_P_d : \<open>\<D> (P\<llangle>A\<rrangle>\<^sub>d s) = {}\<close>
  by (simp add: deterministic_P_d deterministic_div_free)



section \<open>Reachability and Path\<close>

text \<open>We first need a preliminary result on \<^const>\<open>\<R>\<^sub>n\<^sub>d\<close>: a state \<^term>\<open>t\<close> is reachable
      from a state \<^term>\<open>s\<close> if and only if there exists a path between \<^term>\<open>s\<close> and \<^term>\<open>t\<close>\<close>

(* we may want to formalize the definition of a path, but not for the moment *)

lemma \<R>\<^sub>n\<^sub>d_iff_Ex_path:
  \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<longleftrightarrow> (\<exists>path. path \<noteq> [] \<and> hd path = \<sigma> \<and> last path = \<sigma>' \<and>
                            (\<forall>i < length path - 1. \<exists>a. path ! Suc i \<in> \<tau> A (path ! i) a))\<close>
  (is \<open>_ \<longleftrightarrow> (\<exists>path. path \<noteq> [] \<and> ?rhs path \<sigma> \<sigma>')\<close>)
proof (rule iffI)
  show \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> \<exists>path. path \<noteq> [] \<and> ?rhs path \<sigma> \<sigma>'\<close>
  proof (induct rule: \<R>\<^sub>n\<^sub>d.induct)
    case init
    have \<open>[\<sigma>] \<noteq> [] \<and> ?rhs [\<sigma>] \<sigma> \<sigma>\<close> by simp
    thus ?case ..
  next
    case (step \<sigma>' \<sigma>'' a)
    from this(2) obtain path where \<open>path \<noteq> [] \<and> ?rhs path \<sigma> \<sigma>'\<close> ..
    with step.hyps(3) have \<open>path @ [\<sigma>''] \<noteq> [] \<and> ?rhs (path @ [\<sigma>'']) \<sigma> \<sigma>''\<close>
      by (simp add: nth_append)
        (metis One_nat_def Suc_lessI diff_Suc_Suc diff_zero last_conv_nth)
    thus ?case ..
  qed
next
  assume \<open>\<exists>path. path \<noteq> [] \<and> ?rhs path \<sigma> \<sigma>'\<close>
  then obtain path where \<open>path \<noteq> []\<close> \<open>?rhs path \<sigma> \<sigma>'\<close> by blast
  thus \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>\<close>
  proof (induct path arbitrary: \<sigma> rule: list_nonempty_induct)
    case (single u)
    thus ?case using \<R>\<^sub>n\<^sub>d.init by fastforce
  next
    case (cons \<sigma>'' path)
    have \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A (hd path)\<close>
      by (rule cons.hyps(2))
        (use cons.hyps(1) cons.prems in simp,
          metis Suc_pred length_greater_0_conv not_less_eq nth_Cons_Suc)
    moreover have \<open>hd path \<in> \<R>\<^sub>n\<^sub>d A \<sigma>\<close>
      using \<R>\<^sub>n\<^sub>d.init \<R>\<^sub>n\<^sub>d.step cons.hyps(1) cons.prems hd_conv_nth by fastforce
    ultimately show ?case by (fact \<R>\<^sub>n\<^sub>d_trans)
  qed
qed

lemma \<R>\<^sub>d_iff_Ex_path: 
  \<open>\<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<longleftrightarrow> (\<exists>path. path \<noteq> [] \<and> hd path = \<sigma> \<and> last path = \<sigma>' \<and>
                            (\<forall>i < length path - 1. \<exists>a. Some (path ! Suc i) = \<tau> A (path ! i) a))\<close>
  by (subst \<R>\<^sub>n\<^sub>d_from_det_to_ndet[symmetric], subst \<R>\<^sub>n\<^sub>d_iff_Ex_path)
    (simp add: from_det_to_ndet_def split: option.split, metis option.inject)



section \<open>Deadlock Freeness and ProcOmata\<close>

lemma deadlock_free_P_nd_step_iff :
  \<open>deadlock_free (P_nd_step (\<epsilon> A) (\<tau> A) X \<sigma>) \<longleftrightarrow> 
      \<epsilon> A \<sigma> \<noteq> {} \<and> (\<forall>a \<in> \<epsilon> A \<sigma>. \<forall>\<sigma>' \<in> \<tau> A \<sigma> a. deadlock_free (X \<sigma>'))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P_nd_step_iff :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P_nd_step (\<epsilon> A) (\<tau> A) X \<sigma>) \<longleftrightarrow> 
      \<epsilon> A \<sigma> \<noteq> {} \<and> (\<forall>a \<in> \<epsilon> A \<sigma>. \<forall>\<sigma>' \<in> \<tau> A \<sigma> a. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (X \<sigma>'))\<close>
  and deadlock_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_iff :
  \<open>deadlock_free (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) X \<sigma>) \<longleftrightarrow>
      \<sigma> \<notin> \<rho> A \<and> \<epsilon> A \<sigma> \<noteq> {} \<and> (\<forall>a \<in> \<epsilon> A \<sigma>. \<forall>\<sigma>' \<in> \<tau> A \<sigma> a. deadlock_free (X \<sigma>'))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_iff :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) X \<sigma>) \<longleftrightarrow>
      \<sigma> \<in> \<rho> A \<or> \<epsilon> A \<sigma> \<noteq> {} \<and> (\<forall>a \<in> \<epsilon> A \<sigma>. \<forall>\<sigma>' \<in> \<tau> A \<sigma> a. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (X \<sigma>'))\<close>
  by (simp_all add: deadlock_free_Mprefix_iff deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mprefix_iff
      deadlock_free_GlobalNdet_iff deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GlobalNdet_iff
      non_deadlock_free_SKIPS deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIPS \<epsilon>_simps \<rho>_simps)


lemma deadlock_free_P_d_step_iff :
  \<open>deadlock_free (P_d_step (\<epsilon> A) (\<tau> A) X \<sigma>) \<longleftrightarrow> 
       \<epsilon> A \<sigma> \<noteq> {} \<and> (\<forall>a \<in> \<epsilon> A \<sigma>. deadlock_free (X \<lceil>\<tau> A \<sigma> a\<rceil>))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P_d_step_iff :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P_d_step (\<epsilon> A) (\<tau> A) X \<sigma>) \<longleftrightarrow> 
      \<epsilon> A \<sigma> \<noteq> {} \<and> (\<forall>a \<in> \<epsilon> A \<sigma>. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (X \<lceil>\<tau> A \<sigma> a\<rceil>))\<close>
  and deadlock_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_iff:
  \<open>deadlock_free (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step (\<epsilon> A) (\<tau> A) (\<omega> A) X \<sigma>) \<longleftrightarrow>
      \<sigma> \<notin> \<rho> A \<and> \<epsilon> A \<sigma> \<noteq> {} \<and> (\<forall>a \<in> \<epsilon> A \<sigma>. deadlock_free (X \<lceil>\<tau> A \<sigma> a\<rceil>))\<close>
  and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_iff:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step (\<epsilon> A) (\<tau> A) (\<omega> A) X \<sigma>) \<longleftrightarrow>
      \<sigma> \<in> \<rho> A \<or> \<epsilon> A \<sigma> \<noteq> {} \<and> (\<forall>a \<in> \<epsilon> A \<sigma>. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (X \<lceil>\<tau> A \<sigma> a\<rceil>))\<close>
  by (simp_all add: deadlock_free_Mprefix_iff deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Mprefix_iff
      non_deadlock_free_SKIP deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIP \<rho>_simps
      split: option.split)


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>(\<And>\<sigma>'. \<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> \<sigma>' \<in> \<rho> A \<or> \<epsilon> A \<sigma>' \<noteq> {}) \<Longrightarrow>
   deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
proof (induct A arbitrary: \<sigma> rule: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_induct)
  case adm
  show ?case by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def)  
next
  show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (SKIP undefined)\<close>
    by (fact deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIP)
next
  case (step X) thus ?case
    unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_iff
    by (meson \<R>\<^sub>n\<^sub>d.init \<R>\<^sub>n\<^sub>d.step \<R>\<^sub>n\<^sub>d_trans)
qed

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>(\<And>\<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<Longrightarrow> \<sigma>' \<in> \<rho> A \<or> \<epsilon> A \<sigma>' \<noteq> {}) \<Longrightarrow>
   deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>)\<close>
proof (induct A arbitrary: \<sigma> rule: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_induct)
  case adm
  show ?case by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def)  
next
  show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (SKIP undefined)\<close>
    by (fact deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIP)
next
  case (step X)
  thus ?case
    unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_iff
    by (simp add: \<epsilon>_simps) (metis \<R>\<^sub>d.init \<R>\<^sub>d.step \<R>\<^sub>d_trans option.sel)
qed


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_iff :
  assumes \<open>\<rho>_disjoint_\<epsilon> A\<close>
  shows \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<longleftrightarrow> (\<forall>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<sigma>' \<in> \<rho> A \<or> \<epsilon> A \<sigma>' \<noteq> {})\<close>
proof (intro iffI ballI)
  have \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<Longrightarrow>
        (\<sigma>' \<in> \<rho> A \<or> \<epsilon> A \<sigma>' \<noteq> {}) \<and> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>')\<close> for \<sigma>'
  proof (induct rule: \<R>\<^sub>n\<^sub>d.induct)
    case init
    thus ?case
      by (subst (asm) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_iff init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2)[OF step.prems] step.hyps(3) \<rho>_disjoint_\<epsilon>D[OF assms]
    show ?case
      by (subst (asm) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_iff \<epsilon>_simps,
          metis (mono_tags, lifting) Mprefix_is_STOP_iff P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec_notin_\<rho>
          SKIPS_empty \<epsilon>_simps(2) deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SKIPS empty_Collect_eq empty_iff)
  qed
  thus \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<Longrightarrow> \<sigma>' \<in> \<rho> A \<or> \<epsilon> A \<sigma>' \<noteq> {}\<close> for \<sigma>' ..
next
  show \<open>\<forall>\<sigma>'\<in>\<R>\<^sub>n\<^sub>d A \<sigma>. \<sigma>' \<in> \<rho> A \<or> \<epsilon> A \<sigma>' \<noteq> {} \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
    by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)
qed


lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_iff :
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow>
   deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) \<longleftrightarrow> (\<forall>\<sigma>' \<in> \<R>\<^sub>d A \<sigma>. \<sigma>' \<in> \<rho> A \<or> \<epsilon> A \<sigma>' \<noteq> {})\<close>
  by (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d, subst deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_iff)
    (simp_all add: \<rho>_disjoint_\<epsilon>_def \<R>\<^sub>n\<^sub>d_from_det_to_ndet)




lemma deadlock_free_P_nd :
  \<open>(\<And>\<sigma>'. \<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> \<epsilon> A \<sigma>' \<noteq> {}) \<Longrightarrow> deadlock_free (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
proof (induct A arbitrary: \<sigma> rule: P_nd_induct)
  case adm
  show ?case by (simp add: deadlock_free_def)  
next
  show \<open>deadlock_free (DF UNIV)\<close>
    by (simp add: deadlock_free_def)
next
  case (step X) thus ?case
    unfolding deadlock_free_P_nd_step_iff
    by (meson \<R>\<^sub>n\<^sub>d.init \<R>\<^sub>n\<^sub>d.step \<R>\<^sub>n\<^sub>d_trans)
qed

lemma deadlock_free_P_d :
  \<open>(\<And>\<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<Longrightarrow> \<epsilon> A \<sigma>' \<noteq> {}) \<Longrightarrow> deadlock_free (P\<llangle>A\<rrangle>\<^sub>d \<sigma>)\<close>
proof (induct A arbitrary: \<sigma> rule: P_d_induct)
  case adm
  show ?case by (simp add: deadlock_free_def)  
next
  show \<open>deadlock_free (DF UNIV)\<close>
    by (simp add: deadlock_free_def)
next
  case (step X) thus ?case
    unfolding deadlock_free_P_d_step_iff
    by (simp add: \<epsilon>_simps)
      (metis \<R>\<^sub>d.init \<R>\<^sub>d.step \<R>\<^sub>d_trans option.sel)
qed


lemma deadlock_free_P_nd_iff:
  \<open>deadlock_free (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<longleftrightarrow> (\<forall>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<epsilon> A \<sigma>' \<noteq> {})\<close>
proof (intro iffI ballI)
  have \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> deadlock_free (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<Longrightarrow>
        (\<epsilon> A \<sigma>' \<noteq> {}) \<and> deadlock_free (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>')\<close> for \<sigma>'
  proof (induct rule: \<R>\<^sub>n\<^sub>d.induct)
    case init
    thus ?case
      by (subst (asm) P_nd_rec)
        (auto simp add: deadlock_free_P_nd_step_iff init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2)[OF step.prems] step.hyps(3)
    show ?case
      by (subst (asm) P_nd_rec, unfold deadlock_free_P_nd_step_iff)
        (simp add: \<epsilon>_simps,
          metis (mono_tags, lifting) P_nd_rec \<epsilon>_simps(2)
          deadlock_free_Mprefix_iff empty_Collect_eq empty_iff)
  qed
  thus \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> deadlock_free (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<Longrightarrow> \<epsilon> A \<sigma>' \<noteq> {}\<close> for \<sigma>' ..
next
  show \<open>\<forall>\<sigma>'\<in>\<R>\<^sub>n\<^sub>d A \<sigma>. \<epsilon> A \<sigma>' \<noteq> {} \<Longrightarrow> deadlock_free (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
    by (simp add: deadlock_free_P_nd)
qed



lemma deadlock_free_P_d_iff :
  \<open>deadlock_free (P\<llangle>A\<rrangle>\<^sub>d \<sigma>) \<longleftrightarrow> (\<forall>\<sigma>' \<in> \<R>\<^sub>d A \<sigma>. \<epsilon> A \<sigma>' \<noteq> {})\<close>
  by (fold P_nd_from_det_to_ndet_is_P_d, unfold deadlock_free_P_nd_iff)
    (simp add: \<R>\<^sub>n\<^sub>d_from_det_to_ndet)



section \<open>Events and Ticks of ProcOmata\<close>

subsection \<open>Events\<close>

lemma events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset :
  \<open>\<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<subseteq> (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
proof (rule subsetI)
  fix a assume \<open>a \<in> \<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
  then obtain t where \<open>t \<noteq> []\<close> \<open>t \<in> \<T> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close> \<open>ev a \<in> set t\<close> 
    by (metis empty_iff empty_set events_of_memD)
  thus \<open>a \<in> (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  proof (induct t arbitrary: \<sigma> rule: list_nonempty_induct)
    case (single t\<^sub>0)
    thus ?case by (subst (asm) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: T_SKIPS T_Mprefix \<R>\<^sub>n\<^sub>d.init split: if_split_asm)
  next
    case (cons t\<^sub>0 t)
    from cons.prems(1) obtain b
      where \<open>b \<in> \<epsilon> A \<sigma>\<close> \<open>t\<^sub>0 = ev b\<close> \<open>t \<in> \<T> (\<sqinter>\<sigma>' \<in> \<tau> A \<sigma> b. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>')\<close>
      by (subst (asm) (3) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: T_Mprefix T_GlobalNdet T_SKIPS cons.hyps(1) \<epsilon>_simps split: if_split_asm)
    thus ?case
      by (simp add: T_GlobalNdet cons.hyps(1) split: if_split_asm)
        (metis (no_types, lifting) UN_iff \<R>\<^sub>n\<^sub>d.simps \<R>\<^sub>n\<^sub>d_trans cons.hyps(2)
          cons.prems(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) set_ConsD)
  qed
qed

corollary events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_subset :
  \<open>\<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) \<subseteq> (\<Union>\<sigma>' \<in> \<R>\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  by (metis P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d \<R>\<^sub>n\<^sub>d_from_det_to_ndet
      det_ndet_conv_\<epsilon>(1) events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset)


lemma events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>\<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) = (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  if \<rho>_disjoint_\<epsilon> : \<open>\<rho>_disjoint_\<epsilon> A\<close>
proof (intro subset_antisym subsetI)
  show \<open>a \<in> \<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<Longrightarrow> a \<in> \<Union> (\<epsilon> A ` \<R>\<^sub>n\<^sub>d A \<sigma>)\<close> for a
    by (meson events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset in_mono)
next
  fix a assume \<open>a \<in> (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  then obtain \<sigma>' where a1: \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>\<close> and a2: \<open>a \<in> \<epsilon> A \<sigma>'\<close> by blast
  from a1[simplified \<R>\<^sub>n\<^sub>d_iff_Ex_path] obtain path
    where \<open>path \<noteq> []\<close> \<open>hd path = \<sigma> \<and> last path = \<sigma>' \<and> 
           (\<forall>i<length path - 1. \<exists>e. path ! Suc i \<in> \<tau> A (path ! i) e)\<close> by blast
  from this a2 show \<open>a \<in> \<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
  proof (induct path arbitrary: \<sigma> rule: list_nonempty_induct)
    case (single p)
    with \<rho>_disjoint_\<epsilon>[THEN \<rho>_disjoint_\<epsilon>D] show ?case
      by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: events_of_Mprefix events_of_SKIPS \<rho>_simps)
  next
    case (cons p path)
    from cons(3) obtain b where \<open>b \<in> \<epsilon> A \<sigma>\<close> \<open>hd path \<in> \<tau> A \<sigma> b\<close>
      by (auto simp add: \<epsilon>_simps) (metis cons(1) empty_iff hd_conv_nth length_greater_0_conv nth_Cons_0)
    moreover have \<open>a \<in> \<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d (hd path))\<close>
      using a2 cons.hyps(1, 2) cons.prems(1) less_diff_conv by fastforce
    ultimately show ?case
      using \<rho>_disjoint_\<epsilon>[THEN \<rho>_disjoint_\<epsilon>D]
      by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: events_of_Mprefix events_of_GlobalNdet events_of_SKIPS \<rho>_simps)
  qed
qed

corollary events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d: \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow> \<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) = \<Union> (\<epsilon> A ` \<R>\<^sub>d A \<sigma>)\<close>
  by (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d, subst events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)
    (simp_all add: \<rho>_disjoint_\<epsilon>_def \<R>\<^sub>n\<^sub>d_from_det_to_ndet)



lemma events_of_P_nd: \<open>\<alpha>(P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) = \<Union> (\<epsilon> A ` \<R>\<^sub>n\<^sub>d A \<sigma>)\<close>
  by (unfold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>, subst events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)
    (auto simp add: \<rho>_disjoint_\<epsilon>_def \<rho>_simps \<epsilon>_simps)


lemma events_of_P_d: \<open>\<alpha>(P\<llangle>A\<rrangle>\<^sub>d \<sigma>) = \<Union> (\<epsilon> A ` \<R>\<^sub>d A \<sigma>)\<close>
  by (metis P_nd_from_det_to_ndet_is_P_d \<R>\<^sub>n\<^sub>d_from_det_to_ndet
      det_ndet_conv_\<epsilon>(1) events_of_P_nd)



subsection \<open>Strict Events\<close>

corollary strict_events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset :
  \<open>\<^bold>\<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<subseteq> (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  by (meson events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset order_trans strict_events_of_subset_events_of)

corollary strict_events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_subset :
  \<open>\<^bold>\<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) \<subseteq> (\<Union>\<sigma>' \<in> \<R>\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  by (meson events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_subset order_trans strict_events_of_subset_events_of)

lemma strict_events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow> \<^bold>\<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) = (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  by (metis div_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd events_of_is_strict_events_of_or_UNIV)

corollary strict_events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d:
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow> \<^bold>\<alpha>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) = (\<Union>\<sigma>' \<in> \<R>\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  by (metis div_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d events_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d events_of_is_strict_events_of_or_UNIV)

lemma strict_events_of_P_nd: \<open>\<^bold>\<alpha>(P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) = (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  by (metis div_free_P_nd events_of_P_nd events_of_is_strict_events_of_or_UNIV)

lemma strict_events_of_P_d: \<open>\<^bold>\<alpha>(P\<llangle>A\<rrangle>\<^sub>d \<sigma>) = (\<Union>\<sigma>' \<in> \<R>\<^sub>d A \<sigma>. \<epsilon> A \<sigma>')\<close>
  by (metis div_free_P_d events_of_P_d events_of_is_strict_events_of_or_UNIV)



subsection \<open>Ticks\<close>

lemma ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset :
  \<open>\<checkmark>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<subseteq> (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<omega> A \<sigma>')\<close>
proof (rule subsetI)
  fix r assume \<open>r \<in> \<checkmark>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
  then obtain t where \<open>t @ [\<checkmark>(r)] \<in> \<T> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
    by (blast dest: ticks_of_memD)
  thus \<open>r \<in> (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<omega> A \<sigma>')\<close>
  proof (induct t arbitrary: \<sigma>)
    case Nil thus ?case
      by (subst (asm) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: T_SKIPS \<R>\<^sub>n\<^sub>d.init split: if_split_asm)
  next
    case (Cons t\<^sub>0 t)
    from Cons.prems(1) obtain b
      where \<open>b \<in> \<epsilon> A \<sigma>\<close> \<open>t\<^sub>0 = ev b\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> (\<sqinter>\<sigma>' \<in> \<tau> A \<sigma> b. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>')\<close>
      by (subst (asm) (3) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: T_Mprefix T_GlobalNdet T_SKIPS Cons.hyps(1) \<epsilon>_simps split: if_split_asm)
    thus ?case
      by (simp add: T_GlobalNdet Cons.hyps(1) split: if_split_asm)
        (metis \<R>\<^sub>n\<^sub>d.init[of \<sigma> A] UN_iff[of r \<open>\<omega> A\<close> \<open>\<R>\<^sub>n\<^sub>d A _\<close>]
          \<R>\<^sub>n\<^sub>d_trans[of _ A _ \<sigma>] \<R>\<^sub>n\<^sub>d.step[of \<sigma> A \<sigma> _ b] Cons.hyps)
  qed
qed

corollary ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_subset :
  \<open>\<checkmark>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) \<subseteq> {\<lceil>\<omega> A \<sigma>'\<rceil> |\<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<and> \<omega> A \<sigma>' \<noteq> \<diamond>}\<close>
proof (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d,
    rule subset_trans[OF ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset])
  show \<open>(\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>. \<omega> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>') \<subseteq> {\<lceil>\<omega> A \<sigma>'\<rceil> |\<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<and> \<omega> A \<sigma>' \<noteq> \<diamond>}\<close>
    by (simp add: \<R>\<^sub>n\<^sub>d_from_det_to_ndet subset_iff)
      (simp add: from_det_to_ndet_def split: option.split, metis option.sel)
qed


lemma ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>\<checkmark>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) = (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<omega> A \<sigma>')\<close>
  if \<rho>_disjoint_\<epsilon> : \<open>\<rho>_disjoint_\<epsilon> A\<close>
proof (intro subset_antisym subsetI)
  show \<open>r \<in> \<checkmark>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<Longrightarrow> r \<in> (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<omega> A \<sigma>')\<close> for r
    by (meson in_mono ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset)
next
  fix r assume \<open>r \<in> (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<omega> A \<sigma>')\<close>
  then obtain \<sigma>' where a1: \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>\<close> and a2: \<open>r \<in> \<omega> A \<sigma>'\<close> by blast
  from a1[simplified \<R>\<^sub>n\<^sub>d_iff_Ex_path] obtain path
    where \<open>path \<noteq> []\<close> \<open>hd path = \<sigma> \<and> last path = \<sigma>' \<and> 
           (\<forall>i<length path - 1. \<exists>e. path ! Suc i \<in> \<tau> A (path ! i) e)\<close> by blast
  from this a2 show \<open>r \<in> \<checkmark>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
  proof (induct path arbitrary: \<sigma> rule: list_nonempty_induct)
    case (single p)
    thus ?case
      by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: ticks_of_SKIPS)
  next
    case (cons p path)
    from cons(3) obtain b where \<open>b \<in> \<epsilon> A \<sigma>\<close> \<open>hd path \<in> \<tau> A \<sigma> b\<close>
      by (auto simp add: \<epsilon>_simps) (metis cons(1) empty_iff hd_conv_nth length_greater_0_conv nth_Cons_0)
    moreover have \<open>r \<in> \<checkmark>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d (hd path))\<close>
      using a2 cons.hyps(1, 2) cons.prems(1) less_diff_conv by fastforce
    ultimately show ?case
      using \<rho>_disjoint_\<epsilon>[THEN \<rho>_disjoint_\<epsilon>D]
      by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
        (auto simp add: ticks_of_Mprefix ticks_of_GlobalNdet events_of_SKIPS \<rho>_simps)
  qed
qed

corollary ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow> \<checkmark>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) = {\<lceil>\<omega> A \<sigma>'\<rceil> |\<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<and> \<omega> A \<sigma>' \<noteq> \<diamond>}\<close>
  by (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d, subst ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd,
      simp_all add: \<rho>_disjoint_\<epsilon>_def \<R>\<^sub>n\<^sub>d_from_det_to_ndet)
    (auto simp add: from_det_to_ndet_def split: option.split_asm, metis option.sel)


lemma ticks_of_P_nd : \<open>\<checkmark>s(P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) = {}\<close>
  by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega> ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)

lemma ticks_of_P_d: \<open>\<checkmark>s(P\<llangle>A\<rrangle>\<^sub>d \<sigma>) = {}\<close>
  by (metis P_nd_from_det_to_ndet_is_P_d ticks_of_P_nd)



lemma non_terminating_iff_empty_ticks_of :
  \<open>non_terminating P \<longleftrightarrow> \<checkmark>s(P) = {}\<close>
  by (simp add: non_terminating_is_right tickFree_traces_iff_empty_ticks_of)



corollary non_terminating_P_nd : \<open>non_terminating (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
  by (simp add: non_terminating_iff_empty_ticks_of ticks_of_P_nd)

corollary non_terminating_P_d : \<open>non_terminating (P\<llangle>A\<rrangle>\<^sub>d \<sigma>)\<close>
  by (metis P_nd_from_det_to_ndet_is_P_d non_terminating_P_nd)

corollary non_terminating_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>\<rho> A \<inter> \<R>\<^sub>n\<^sub>d A \<sigma> = {} \<Longrightarrow> non_terminating (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
  by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_empty_\<rho>_inter_\<R>\<^sub>n\<^sub>d non_terminating_P_nd)

corollary non_terminating_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_iff :
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow> non_terminating (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<longleftrightarrow> \<rho> A \<inter> \<R>\<^sub>n\<^sub>d A \<sigma> = {}\<close>
  by (auto simp add: non_terminating_iff_empty_ticks_of ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd \<rho>_simps)

corollary non_terminating_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>\<rho> A \<inter> \<R>\<^sub>d A \<sigma> = {} \<Longrightarrow> non_terminating (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>)\<close>
  by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_empty_\<rho>_inter_\<R>\<^sub>d non_terminating_P_d)

corollary non_terminating_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_iff :
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow> non_terminating (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) \<longleftrightarrow> \<rho> A \<inter> \<R>\<^sub>d A \<sigma> = {}\<close>
  by (auto simp add: non_terminating_iff_empty_ticks_of ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d \<rho>_simps)



subsection \<open>Strict Ticks\<close>

corollary strict_ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset :
  \<open>\<^bold>\<checkmark>\<^bold>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<subseteq> (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<omega> A \<sigma>')\<close>
  by (metis div_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset ticks_of_is_strict_ticks_of_or_UNIV)

corollary strict_ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_subset :
  \<open>\<^bold>\<checkmark>\<^bold>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) \<subseteq> {\<lceil>\<omega> A \<sigma>'\<rceil> |\<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<and> \<omega> A \<sigma>' \<noteq> \<diamond>}\<close>
  by (metis (mono_tags, lifting) strict_ticks_of_subset_ticks_of subset_trans ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_subset)

lemma strict_ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow> \<^bold>\<checkmark>\<^bold>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) = (\<Union>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<omega> A \<sigma>')\<close>
  by (metis div_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd ticks_of_is_strict_ticks_of_or_UNIV)

corollary strict_ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow> \<^bold>\<checkmark>\<^bold>s(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) = {\<lceil>\<omega> A \<sigma>'\<rceil> |\<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<and> \<omega> A \<sigma>' \<noteq> \<diamond>}\<close>
  by (metis (mono_tags, lifting) div_free_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d ticks_of_is_strict_ticks_of_or_UNIV)

lemma strict_ticks_of_P_nd: \<open>\<^bold>\<checkmark>\<^bold>s(P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) = {}\<close>
  by (metis div_free_P_nd ticks_of_P_nd ticks_of_is_strict_ticks_of_or_UNIV)

lemma strict_ticks_of_P_d: \<open>\<^bold>\<checkmark>\<^bold>s(P\<llangle>A\<rrangle>\<^sub>d \<sigma>) = {}\<close>
  by (metis P_nd_from_det_to_ndet_is_P_d strict_ticks_of_P_nd)



subsection \<open>Ticks length\<close>

lemma is_ticks_length_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>\<lbrakk>\<And>\<sigma>' rs. \<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> rs \<in> \<omega> A \<sigma>' \<Longrightarrow> length rs = n\<rbrakk>
   \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
  by (auto simp add: is_ticks_length_def
      dest!: set_mp[OF strict_ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_subset])

lemma is_ticks_length_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_iff :
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow>
   length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) \<longleftrightarrow> (\<forall>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>. \<forall>rs \<in> \<omega> A \<sigma>'. length rs = n)\<close>
  by (simp add: is_ticks_length_def strict_ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)

lemma is_ticks_length_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>\<lbrakk>\<And>\<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<Longrightarrow> \<omega> A \<sigma>' \<noteq> \<diamond> \<Longrightarrow> length \<lceil>\<omega> A \<sigma>'\<rceil> = n\<rbrakk>
   \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>)\<close>
  by (auto simp add: is_ticks_length_def
      dest!: set_mp[OF strict_ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_subset])

lemma is_ticks_length_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_iff :
  \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow>
   length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) \<longleftrightarrow> (\<forall>\<sigma>' \<in> \<R>\<^sub>d A \<sigma>. \<omega> A \<sigma>' \<noteq> \<diamond> \<longrightarrow> length \<lceil>\<omega> A \<sigma>'\<rceil> = n)\<close>
  by (auto simp add: is_ticks_length_def strict_ticks_of_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)



(*<*)
end
  (*>*)