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


chapter\<open> Other Results similar to Compactification \<close>

(*<*)
theory Almost_Compactification
  imports Process_Normalization
begin
  (*>*)

text \<open>Unlike \<^const>\<open>Sync\<close> and \<^const>\<open>Seq\<close>, some operators like @{const [source] Det} do not enjoy
      a compactification result. Nevertheless, we still can prove some useful lemmas.\<close>


section \<open>Some preliminary Results\<close>

lemma Mprefix_Det_Mprefix_bis :
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<box> (\<box>b \<in> B \<rightarrow> Q b) = 
   (\<box>x \<in> (A \<inter> B) \<rightarrow> P x \<sqinter> Q x) \<box> (\<box>a \<in> (A - B) \<rightarrow> P a) \<box> (\<box>b \<in> (B - A) \<rightarrow> Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
    by (cases t) (auto simp add: F_Det F_Mprefix F_Ndet)
next
  show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
    by (cases t, simp_all add: F_Mprefix F_Ndet F_Det D_Det T_Det disjoint_iff) blast+
next
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (auto simp add: D_Det D_Mprefix image_iff D_Ndet)
next
  show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (auto simp add: D_Mprefix D_Ndet D_Det split: if_split_asm)
qed


lemma GlobalNdet_Ndet_GlobalNdet:
  \<open>A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> (\<sqinter>a \<in> A. P a) \<sqinter> (\<sqinter>b \<in> B. Q b) =
   \<sqinter>x \<in> (A \<union> B). (if x \<in> A \<inter> B then P x \<sqinter> Q x else if x \<in> A then P x else Q x)\<close>
  by (simp add: Process_eq_spec F_Ndet D_Ndet F_GlobalNdet D_GlobalNdet, safe)
    (auto simp add: F_Ndet D_Ndet split: if_splits)

lemma GlobalNdet_Ndet_GlobalNdet_bis:
  \<open>A \<inter> B \<noteq> {} \<Longrightarrow> A - B \<noteq> {} \<Longrightarrow> B - A \<noteq> {} \<Longrightarrow>
   (\<sqinter>a \<in> A. P a) \<sqinter> (\<sqinter>b \<in> B. Q b) = 
   (\<sqinter>x \<in> (A \<inter> B). P x \<sqinter> Q x) \<sqinter> (\<sqinter>a \<in> (A - B). P a) \<sqinter> (\<sqinter>b \<in> (B - A). Q b)\<close>
  by (auto simp add: Process_eq_spec F_Ndet D_Ndet F_GlobalNdet D_GlobalNdet)


lemma GlobalNdet_GlobalNdet:
  \<open>(\<sqinter>a \<in> A. \<sqinter>b \<in> B a. P b) =
   (if \<forall>a \<in> A. B a \<noteq> {} then \<sqinter>b \<in> (\<Union>a \<in> A. B a). P b else (\<sqinter>b \<in> (\<Union>a \<in> A. B a). P b) \<sqinter> STOP)\<close>
  by (auto simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet F_Ndet D_Ndet F_STOP D_STOP)




section \<open>Results for @{const [source] Det}\<close>

(* TODO: write results for SKIP, if possible *)

lemma P_nd_set_almost_compactification_Det :
  \<open>(\<box> (s, A) \<in> s_A_set. P\<llangle>A\<rrangle>\<^sub>n\<^sub>d s) =
   \<box>e \<in> (\<Union>(s, A) \<in> s_A_set. \<epsilon> A s) \<rightarrow>
   \<sqinter>(s, A) \<in> {(s, A) \<in> s_A_set. e \<in> \<epsilon> A s}.
   \<sqinter>s' \<in> \<tau> A s e. P\<llangle>A\<rrangle>\<^sub>n\<^sub>d s'\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  have \<open>?lhs = (\<box> (s, A) \<in> s_A_set. P_nd_step (\<epsilon> A) (\<tau> A) P\<llangle>A\<rrangle>\<^sub>n\<^sub>d s)\<close>
    by (auto intro: mono_GlobalDet_eq arg_cong[OF P_nd_rec])
  also have \<open>\<dots> = \<box>s_A \<in> s_A_set. P_nd_step (\<epsilon> (snd s_A)) (\<tau> (snd s_A)) P\<llangle>snd s_A\<rrangle>\<^sub>n\<^sub>d (fst s_A)\<close>
    by (simp only: case_prod_beta')
  also have \<open>\<dots> = \<box>e \<in> (\<Union>s_A \<in> s_A_set. \<epsilon> (snd s_A) (fst s_A)) \<rightarrow>
                  \<sqinter>s_A \<in> {s_A \<in> s_A_set. e \<in> \<epsilon> (snd s_A) (fst s_A)}. 
                  GlobalNdet (\<tau> (snd s_A) (fst s_A) e) P\<llangle>snd s_A\<rrangle>\<^sub>n\<^sub>d\<close>
    by (simp add: GlobalDet_Mprefix)
  also have \<open>\<dots> = ?rhs\<close> by (simp add: case_prod_beta')
  finally show \<open>?lhs = ?rhs\<close> .
qed



lemma P_nd_set_almost_compactification_Det_bis :
  \<open>(\<box> (s, A) \<in> s_A_set. P\<llangle>A\<rrangle>\<^sub>n\<^sub>d s) =
   \<box>e \<in> (\<Union>(s, A) \<in> s_A_set. \<epsilon> A s) \<rightarrow>
   \<sqinter>(s', A) \<in> {(s', A)| s' s A. (s, A) \<in> s_A_set \<and> e \<in> \<epsilon> A s \<and> s' \<in> \<tau> A s e}. P\<llangle>A\<rrangle>\<^sub>n\<^sub>d s'\<close>
  (is \<open>_ = ?rhs\<close>)
  by (subst P_nd_set_almost_compactification_Det, intro mono_Mprefix_eq)
    (auto simp add: Process_eq_spec GlobalNdet_projs \<epsilon>_simps split: if_split_asm, blast+)




lemma P_d_set_almost_compactification_Det:
  shows \<open>(\<box> (s, A) \<in> s_A_set. P\<llangle>A\<rrangle>\<^sub>d s) =
         \<box>e \<in> (\<Union>(s, A) \<in> s_A_set. \<epsilon> A s) \<rightarrow>
         \<sqinter>(s, A) \<in> {(s, A) \<in> s_A_set. e \<in> \<epsilon> A s}. P\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A s e\<rceil>\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  have \<open>?lhs = (\<box> (s, A) \<in> s_A_set. P_d_step (\<epsilon> A) (\<tau> A) P\<llangle>A\<rrangle>\<^sub>d s)\<close>
    by (auto intro: mono_GlobalDet_eq arg_cong[OF P_d_rec])
  also have \<open>\<dots> = \<box>s_A \<in> s_A_set. P_d_step (\<epsilon> (snd s_A)) (\<tau> (snd s_A)) P\<llangle>snd s_A\<rrangle>\<^sub>d (fst s_A)\<close>
    by (simp only: case_prod_beta')
  also have \<open>\<dots> = \<box>e \<in> (\<Union>s_A \<in> s_A_set. \<epsilon> (snd s_A) (fst s_A)) \<rightarrow>
                  \<sqinter>s_A \<in> {s_A \<in> s_A_set. e \<in> \<epsilon> (snd s_A) (fst s_A)}.
                  P\<llangle>snd s_A\<rrangle>\<^sub>d \<lceil>\<tau> (snd s_A) (fst s_A) e\<rceil>\<close>
    by (simp add: GlobalDet_Mprefix)
  also have \<open>\<dots> = ?rhs\<close> by (simp add: case_prod_beta')
  finally show \<open>?lhs = ?rhs\<close> .
qed




lemma P_d_set_almost_compactification_Det_bis:
  shows \<open>(\<box> (s, A) \<in> s_A_set. P\<llangle>A\<rrangle>\<^sub>d s) =
         \<box>e \<in> (\<Union>(s, A) \<in> s_A_set. \<epsilon> A s) \<rightarrow>
         \<sqinter>(s', A) \<in> {(\<lceil>\<tau> A s e\<rceil>, A)| s A. (s, A) \<in> s_A_set \<and> e \<in> \<epsilon> A s}. P\<llangle>A\<rrangle>\<^sub>d s'\<close>
  by (subst P_d_set_almost_compactification_Det, intro mono_Mprefix_eq)
    (auto simp add: Process_eq_spec GlobalNdet_projs \<epsilon>_simps, (metis option.sel)+)





section \<open>Results for @{const [source] Ndet}\<close>

\<comment> \<open>Possible ???\<close>



section \<open>Other Operators\<close>

subsection \<open>\<^const>\<open>initials\<close>\<close>

lemma initials_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<^sup>0 = (if \<sigma> \<in> \<rho> A then tick ` \<omega> A \<sigma> else ev ` \<epsilon> A \<sigma>)\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec) (simp add: initials_Mprefix \<rho>_simps)

lemma initials_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>(P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>)\<^sup>0 = (if \<sigma> \<in> \<rho> A then {\<checkmark>(\<lceil>\<omega> A \<sigma>\<rceil>)} else ev ` \<epsilon> A \<sigma>)\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec) (auto simp add: initials_Mprefix \<rho>_simps)

lemma initials_P_nd : \<open>(P\<llangle>A\<rrangle>\<^sub>n\<^sub>d s)\<^sup>0 = ev ` \<epsilon> A s\<close>
  by (subst P_nd_rec) (simp_all add: initials_Mprefix)

lemma initials_P_d : \<open>(P\<llangle>A\<rrangle>\<^sub>d s)\<^sup>0 = ev ` \<epsilon> A s\<close>
  by (subst P_d_rec) (simp add: initials_Mprefix)



subsection \<open>\<^const>\<open>Throw\<close>\<close>

lemma Throw_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> \<Theta> b \<in> B. Q b =
   (if \<sigma> \<in> \<rho> A then SKIPS (\<omega> A \<sigma>) else
    \<box>a\<in>\<epsilon> A \<sigma> \<rightarrow> (if a \<in> B then Q a else \<sqinter>\<sigma>' \<in> \<tau> A \<sigma> a. (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' \<Theta> b \<in> B. Q b)))\<close>
  by (auto simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec_in_\<rho> Throw_disjoint_events_of
      events_of_SKIPS P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec_notin_\<rho> Throw_Mprefix
      Throw_distrib_GlobalNdet_right
      intro: mono_Mprefix_eq)

lemma Throw_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> \<Theta> b \<in> B. Q b =
   (if \<sigma> \<in> \<rho> A then SKIP \<lceil>\<omega> A \<sigma>\<rceil> else
    \<box>a\<in>\<epsilon> A \<sigma> \<rightarrow> (if a \<in> B then Q a else P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil> \<Theta> b \<in> B. Q b))\<close>
  by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec_in_\<rho> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec_notin_\<rho> Throw_Mprefix)

lemma Throw_P_nd :
  \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> \<Theta> b \<in> B. Q b =
   \<box>a\<in>\<epsilon> A \<sigma> \<rightarrow> (if a \<in> B then Q a else \<sqinter>\<sigma>' \<in> \<tau> A \<sigma> a. (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' \<Theta> b \<in> B. Q b))\<close>
  by (subst P_nd_rec)
    (auto simp add: Throw_Mprefix Throw_distrib_GlobalNdet_right intro: mono_Mprefix_eq)

lemma Throw_P_d :
  \<open>P\<llangle>A\<rrangle>\<^sub>d \<sigma> \<Theta> b \<in> B. Q b =
   \<box>a\<in>\<epsilon> A \<sigma> \<rightarrow> (if a \<in> B then Q a else P\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil> \<Theta> b \<in> B. Q b)\<close>
  by (subst P_d_rec) (simp add: Throw_Mprefix)



subsection \<open>\<^const>\<open>Interrupt\<close>\<close>

lemma SKIPS_Interrupt_is_SKIPS_Det :
  \<open>SKIPS R \<triangle> P = SKIPS R \<box> P\<close>
  by (auto simp add: SKIPS_def Interrupt_distrib_GlobalNdet_right
      Det_distrib_GlobalNdet_right SKIP_Interrupt_is_SKIP_Det intro: mono_GlobalNdet_eq)

lemma Interrupt_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> \<triangle> Q =
   Q \<box> (if \<sigma> \<in> \<rho> A then SKIPS (\<omega> A \<sigma>) else \<box>a \<in> \<epsilon> A \<sigma> \<rightarrow> \<sqinter>\<sigma>' \<in> \<tau> A \<sigma> a. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' \<triangle> Q)\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
    (auto simp add: Interrupt_Mprefix SKIPS_Interrupt_is_SKIPS_Det Det_commute
      \<rho>_simps \<epsilon>_simps Interrupt_distrib_GlobalNdet_right
      intro!: arg_cong2[where f = \<open>(\<box>)\<close>] mono_Mprefix_eq split: if_split_asm)

lemma Interrupt_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> \<triangle> Q =
   Q \<box> (if \<sigma> \<in> \<rho> A then SKIP \<lceil>\<omega> A \<sigma>\<rceil> else \<box>a \<in> \<epsilon> A \<sigma> \<rightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil> \<triangle> Q)\<close>
  by (simp add: Det_commute Interrupt_Mprefix P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec_in_\<rho>
      P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec_notin_\<rho> SKIP_Interrupt_is_SKIP_Det)

lemma Interrupt_P_nd :
  \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> \<triangle> Q = Q \<box> (\<box>a \<in> \<epsilon> A \<sigma> \<rightarrow> \<sqinter>\<sigma>' \<in> \<tau> A \<sigma> a. P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' \<triangle> Q)\<close>
  by (subst P_nd_rec)
    (auto simp add: Interrupt_Mprefix Interrupt_distrib_GlobalNdet_right \<epsilon>_simps
      intro!: arg_cong2[where f = \<open>(\<box>)\<close>] mono_Mprefix_eq split: if_split_asm)

lemma Interrupt_P_d :
  \<open>P\<llangle>A\<rrangle>\<^sub>d \<sigma> \<triangle> Q = Q \<box> (\<box>a \<in> \<epsilon> A \<sigma> \<rightarrow> P\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil> \<triangle> Q)\<close>
  by (metis Interrupt_Mprefix P_d_rec)


(* TODO: see if we also write lemmas when Q is a procOmata *)


subsection \<open>After\<close>

context After
begin

lemma After_SKIPS : \<open>SKIPS R after a = \<Psi> (SKIPS R) a\<close>
  by (simp add: Process_eq_spec After_projs image_iff)

lemma After_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> after a =
   (if \<sigma> \<in> \<rho> A then \<Psi> (SKIPS (\<omega> A \<sigma>)) a else 
    if a \<in> \<epsilon> A \<sigma> then \<sqinter>\<sigma>' \<in> \<tau> A \<sigma> a. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' else \<Psi> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) a)\<close>
  by (subst (1 4) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
    (simp add: \<epsilon>_simps \<rho>_simps After_SKIPS After_Mprefix)

lemma After_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> after a =
   (if \<sigma> \<in> \<rho> A then \<Psi> (SKIP \<lceil>\<omega> A \<sigma>\<rceil>) a else 
    if a \<in> \<epsilon> A \<sigma> then P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil> else \<Psi> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) a)\<close>
  by (subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec)
    (auto simp add: \<epsilon>_simps \<rho>_simps After_SKIP After_Mprefix)

lemma After_P_nd :
  \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> after a = (if a \<in> \<epsilon> A \<sigma> then \<sqinter>\<sigma>' \<in> \<tau> A \<sigma> a. P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' else \<Psi> (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) a)\<close>
  by (subst (1 4) P_nd_rec) (simp add: \<epsilon>_simps After_Mprefix)

lemma After_P_d :
  \<open>P\<llangle>A\<rrangle>\<^sub>d \<sigma> after a = (if a \<in> \<epsilon> A \<sigma> then P\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil> else \<Psi> (P\<llangle>A\<rrangle>\<^sub>d \<sigma>) a)\<close>
  by (subst (1 2) P_d_rec)
    (simp add: \<epsilon>_simps After_SKIP After_Mprefix)

end


context AfterExt
begin

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS :
  \<open>SKIPS R after\<^sub>\<checkmark> e = (case e of ev a \<Rightarrow> \<Psi> (SKIPS R) a | \<checkmark>(r) \<Rightarrow> \<Omega> (SKIPS R) r)\<close>
  by (cases e) (simp_all add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_SKIPS)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> after\<^sub>\<checkmark> e =
   (case e of ev a \<Rightarrow> if \<sigma> \<in> \<rho> A then \<Psi> (SKIPS (\<omega> A \<sigma>)) a else 
                      if a \<in> \<epsilon> A \<sigma> then \<sqinter>\<sigma>' \<in> \<tau> A \<sigma> a. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' else \<Psi> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) a
            | \<checkmark>(r) \<Rightarrow> if \<sigma> \<in> \<rho> A then \<Omega> (SKIPS (\<omega> A \<sigma>)) r else \<Omega> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) r)\<close>
proof (cases e)
  show \<open>e = ev a \<Longrightarrow> ?thesis\<close> for a
    by (simp add: After_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
next
  show \<open>e = \<checkmark>(r) \<Longrightarrow> ?thesis\<close> for r
    by (subst (1 5) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec) (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def \<rho>_simps)
qed

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> after\<^sub>\<checkmark> e =
   (case e of ev a \<Rightarrow> if \<sigma> \<in> \<rho> A then \<Psi> (SKIP \<lceil>\<omega> A \<sigma>\<rceil>) a else 
                      if a \<in> \<epsilon> A \<sigma> then P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil> else \<Psi> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) a
            | \<checkmark>(r) \<Rightarrow> if \<sigma> \<in> \<rho> A then \<Omega> (SKIP \<lceil>\<omega> A \<sigma>\<rceil>) r else \<Omega> (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) r)\<close>
proof (cases e)
  show \<open>e = ev a \<Longrightarrow> ?thesis\<close> for a
    by (simp add: After_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
next
  show \<open>e = \<checkmark>(r) \<Longrightarrow> ?thesis\<close> for r
    by (subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec) (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def \<rho>_simps)
qed

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_P_nd :
  \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> after\<^sub>\<checkmark> e =
   (case e of ev a \<Rightarrow> if a \<in> \<epsilon> A \<sigma> then \<sqinter>\<sigma>' \<in> \<tau> A \<sigma> a. P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' else \<Psi> (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) a
            | \<checkmark>(r) \<Rightarrow> \<Omega> (P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) r)\<close>
proof (cases e)
  show \<open>e = ev a \<Longrightarrow> ?thesis\<close> for a
    by (simp add: After_P_nd After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
next
  show \<open>e = \<checkmark>(r) \<Longrightarrow> ?thesis\<close> for r
    by (subst (1 2) P_nd_rec) (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
qed


lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_P_d :
  \<open>P\<llangle>A\<rrangle>\<^sub>d \<sigma> after\<^sub>\<checkmark> e =
   (case e of ev a \<Rightarrow> if a \<in> \<epsilon> A \<sigma> then P\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil> else \<Psi> (P\<llangle>A\<rrangle>\<^sub>d \<sigma>) a
            | \<checkmark>(r) \<Rightarrow> \<Omega> (P\<llangle>A\<rrangle>\<^sub>d \<sigma>) r)\<close>
proof (cases e)
  show \<open>e = ev a \<Longrightarrow> ?thesis\<close> for a
    by (simp add: After_P_d After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
next
  show \<open>e = \<checkmark>(r) \<Longrightarrow> ?thesis\<close> for r
    by (subst (1 2) P_d_rec) (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
qed


end


section \<open>OpSem\<close>

context OpSemTransitions
begin

lemma SKIPS_\<tau>_trans_SKIP : \<open>r \<in> R \<Longrightarrow> SKIPS R \<leadsto>\<^sub>\<tau> SKIP r\<close>
  by (simp add: SKIPS_def \<tau>_trans_GlobalNdet)



text \<open>
In the ProcOmata, we will absorb the \<open>\<tau>\<close> transitions
that appear when we unfold the fixed-point operator.
\<close>

lemma \<tau>_trans_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>r \<in> \<omega> A \<sigma> \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> \<leadsto>\<^sub>\<tau> SKIP r\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec) (auto simp add: SKIPS_\<tau>_trans_SKIP)

lemma \<tau>_trans_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>\<sigma> \<in> \<rho> A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> \<leadsto>\<^sub>\<checkmark>\<^bsub>\<lceil>\<omega> A \<sigma>\<rceil>\<^esub> \<Omega> (SKIP \<lceil>\<omega> A \<sigma>\<rceil>) \<lceil>\<omega> A \<sigma>\<rceil>\<close>
  by (auto simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec SKIP_trans_tick_\<Omega>_SKIP \<rho>_simps)


lemma ev_trans_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>\<sigma> \<notin> \<rho> A \<Longrightarrow> \<sigma>' \<in> \<tau> A \<sigma> a \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> \<leadsto>\<^bsub>a\<^esub> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>'\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec)
    (auto simp add: \<rho>_simps \<epsilon>_simps
             intro: ev_trans_\<tau>_trans[OF ev_trans_Mprefix \<tau>_trans_GlobalNdet])

lemma ev_trans_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>\<sigma> \<notin> \<rho> A \<Longrightarrow> a \<in> \<epsilon> A \<sigma> \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> \<leadsto>\<^bsub>a\<^esub> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil>\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec)
    (auto simp add: \<rho>_simps intro: ev_trans_Mprefix)

lemma ev_trans_P_nd :
  \<open>\<sigma>' \<in> \<tau> A \<sigma> a \<Longrightarrow> P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> \<leadsto>\<^bsub>a\<^esub> P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>'\<close>
  by (subst P_nd_rec)
    (auto simp add: \<epsilon>_simps
             intro: ev_trans_\<tau>_trans[OF ev_trans_Mprefix \<tau>_trans_GlobalNdet])

lemma ev_trans_P_d :
  \<open>a \<in> \<epsilon> A \<sigma> \<Longrightarrow> P\<llangle>A\<rrangle>\<^sub>d \<sigma> \<leadsto>\<^bsub>a\<^esub> P\<llangle>A\<rrangle>\<^sub>d \<lceil>\<tau> A \<sigma> a\<rceil>\<close>
  by (subst P_d_rec) (auto intro: ev_trans_Mprefix)



end

(*<*)
end
  (*>*)
