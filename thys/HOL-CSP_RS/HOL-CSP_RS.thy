(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
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

section \<open>Higher-Order Rules\<close>

(*<*)
theory "HOL-CSP_RS"
  imports
    Prefixes_Constructive
    Choices_Non_Destructive
    Renaming_Non_Destructive
    Sequential_Composition_Non_Destructive
    Synchronization_Product_Non_Destructive
    Throw_Non_Destructive
    Interrupt_Non_Destructive
    Hiding_Destructive
    CSP_Restriction_Adm
begin
  (*>*)

text \<open>This is the main entry point.
      We configure the simplifier below.\<close>


named_theorems restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset

subsection \<open>Prefixes\<close>

lemma Mprefix_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>constructive (\<lambda>x. \<box>a \<in> A \<rightarrow> f a x)\<close> if \<open>(\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a))\<close>
proof -
  have * : \<open>\<box>a \<in> A \<rightarrow> f a x = \<box>a \<in> A \<rightarrow> (if a \<in> A then f a x else STOP)\<close> for x
    by (auto intro: mono_Mprefix_eq)
  show \<open>constructive (\<lambda>x. \<box>a \<in> A \<rightarrow> f a x)\<close>
    by (subst "*", rule constructive_comp_non_destructive
        [OF Mprefix_constructive, of \<open>\<lambda>x a. if a \<in> A then f a x else STOP\<close>])
      (auto intro: that)
qed

lemma Mndetprefix_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>constructive (\<lambda>x. \<sqinter>a \<in> A \<rightarrow> f a x)\<close> if \<open>(\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a))\<close>
proof -
  have * : \<open>\<sqinter>a \<in> A \<rightarrow> f a x = \<sqinter>a \<in> A \<rightarrow> (if a \<in> A then f a x else STOP)\<close> for x
    by (auto intro: mono_Mndetprefix_eq)
  show \<open>constructive (\<lambda>x. \<sqinter>a \<in> A \<rightarrow> f a x)\<close>
    by (subst "*", rule constructive_comp_non_destructive
        [OF Mndetprefix_constructive, of \<open>\<lambda>x a. if a \<in> A then f a x else STOP\<close>])
      (auto intro: that)
qed

corollary write0_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive f \<Longrightarrow> constructive (\<lambda>x. a \<rightarrow> f x)\<close>
  by (simp add: write0_def Mprefix_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

corollary write_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive f \<Longrightarrow> constructive (\<lambda>x. c\<^bold>!a \<rightarrow> f x)\<close>
  by (simp add: write_def Mprefix_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

corollary read_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)) \<Longrightarrow> constructive (\<lambda>x. c\<^bold>?a \<in> A \<rightarrow> f a x)\<close>
  by (simp add: read_def Mprefix_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inv_into_into)

corollary ndet_write_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)) \<Longrightarrow> constructive (\<lambda>x. c\<^bold>!\<^bold>!a \<in> A \<rightarrow> f a x)\<close>
  by (simp add: ndet_write_def Mndetprefix_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inv_into_into)


subsection \<open>Choices\<close>

lemma GlobalNdet_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)) \<Longrightarrow> non_destructive (\<lambda>x. \<sqinter>a \<in> A. f a x)\<close>
  \<open>(\<And>a. a \<in> A \<Longrightarrow> constructive (f a)) \<Longrightarrow> constructive (\<lambda>x. \<sqinter>a \<in> A. f a x)\<close>
proof -
  have * : \<open>\<sqinter>a \<in> A. f a x = \<sqinter>a \<in> A. (if a \<in> A then f a x else STOP)\<close> for x
    by (auto intro: mono_GlobalNdet_eq)

  show \<open>(\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)) \<Longrightarrow> non_destructive (\<lambda>x. \<sqinter>a \<in> A. f a x)\<close>
    by (subst "*", rule non_destructive_comp_non_destructive
        [OF GlobalNdet_non_destructive, of \<open>\<lambda>x a. if a \<in> A then f a x else STOP\<close>]) auto

  show \<open>(\<And>a. a \<in> A \<Longrightarrow> constructive (f a)) \<Longrightarrow> constructive (\<lambda>x. \<sqinter>a \<in> A. f a x)\<close>
    by (subst "*", rule non_destructive_comp_constructive
        [OF GlobalNdet_non_destructive, of \<open>\<lambda>x a. if a \<in> A then f a x else STOP\<close>]) auto
qed

lemma GlobalDet_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)) \<Longrightarrow> non_destructive (\<lambda>x. \<box>a \<in> A. f a x)\<close>
  \<open>(\<And>a. a \<in> A \<Longrightarrow> constructive (f a)) \<Longrightarrow> constructive (\<lambda>x. \<box>a \<in> A. f a x)\<close>
proof -
  have * : \<open>\<box>a \<in> A. f a x = \<box>a \<in> A. (if a \<in> A then f a x else STOP)\<close> for x
    by (auto intro: mono_GlobalDet_eq)

  show \<open>(\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)) \<Longrightarrow> non_destructive (\<lambda>x. \<box>a \<in> A. f a x)\<close>
    by (subst "*", rule non_destructive_comp_non_destructive
        [OF GlobalDet_non_destructive, of \<open>\<lambda>x a. if a \<in> A then f a x else STOP\<close>]) auto

  show \<open>(\<And>a. a \<in> A \<Longrightarrow> constructive (f a)) \<Longrightarrow> constructive (\<lambda>x. \<box>a \<in> A. f a x)\<close>
    by (subst "*", rule non_destructive_comp_constructive
        [OF GlobalDet_non_destructive, of \<open>\<lambda>x a. if a \<in> A then f a x else STOP\<close>]) auto
qed


lemma Ndet_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive f \<Longrightarrow> non_destructive g \<Longrightarrow> non_destructive (\<lambda>x. f x \<sqinter> g x)\<close>
  \<open>constructive f \<Longrightarrow> constructive g \<Longrightarrow> constructive (\<lambda>x. f x \<sqinter> g x)\<close>
  by (auto intro!: non_destructiveI constructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Ndet dest!: non_destructiveD constructiveD)

lemma Det_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive f \<Longrightarrow> non_destructive g \<Longrightarrow> non_destructive (\<lambda>x. f x \<box> g x)\<close>
  \<open>constructive f \<Longrightarrow> constructive g \<Longrightarrow> constructive (\<lambda>x. f x \<box> g x)\<close>
  by (auto intro!: non_destructiveI constructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det dest!: non_destructiveD constructiveD)

lemma Sliding_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive f \<Longrightarrow> non_destructive g \<Longrightarrow> non_destructive (\<lambda>x. f x \<rhd> g x)\<close>
  \<open>constructive f \<Longrightarrow> constructive g \<Longrightarrow> constructive (\<lambda>x. f x \<rhd> g x)\<close>
  by (auto intro!: non_destructiveI constructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sliding dest!: non_destructiveD constructiveD)


subsection \<open>Renaming\<close>

lemma Renaming_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive P \<Longrightarrow> non_destructive (\<lambda>x. Renaming (P x) f g)\<close>
  \<open>constructive P \<Longrightarrow> constructive (\<lambda>x. Renaming (P x) f g)\<close>
  by (auto intro!: non_destructiveI constructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Renaming dest!: non_destructiveD constructiveD)


subsection \<open>Sequential Composition\<close>

lemma Seq_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive f \<Longrightarrow> non_destructive g \<Longrightarrow> non_destructive (\<lambda>x. f x \<^bold>; g x)\<close>
  \<open>constructive f \<Longrightarrow> constructive g \<Longrightarrow> constructive (\<lambda>x. f x \<^bold>; g x)\<close>
  by (fact non_destructive_comp_non_destructive[OF Seq_non_destructive non_destructive_prod_codomain, simplified])
    (fact non_destructive_comp_constructive[OF Seq_non_destructive constructive_prod_codomain, simplified])


lemma MultiSeq_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> non_destructive (f l)) \<Longrightarrow> non_destructive (\<lambda>x. SEQ l \<in>@ L. f l x)\<close>
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> constructive (f l)) \<Longrightarrow> constructive (\<lambda>x. SEQ l \<in>@ L. f l x)\<close>
  by (induct L rule: rev_induct; simp add: Seq_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)+


corollary MultiSeq_non_destructive : \<open>non_destructive (\<lambda>P. SEQ l \<in>@ L. P l)\<close>
  by (simp add: MultiSeq_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(1)[of L \<open>\<lambda>l x. x l\<close>])



subsection \<open>Synchronization Product\<close>

lemma Sync_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive f \<Longrightarrow> non_destructive g \<Longrightarrow> non_destructive (\<lambda>x. f x \<lbrakk>S\<rbrakk> g x)\<close>
  \<open>constructive f \<Longrightarrow> constructive g \<Longrightarrow> constructive (\<lambda>x. f x \<lbrakk>S\<rbrakk> g x)\<close>
  by (fact non_destructive_comp_non_destructive[OF Sync_non_destructive non_destructive_prod_codomain, simplified])
    (fact non_destructive_comp_constructive[OF Sync_non_destructive constructive_prod_codomain, simplified])


lemma MultiSync_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>(\<And>m. m \<in># M \<Longrightarrow> non_destructive (f m)) \<Longrightarrow> non_destructive (\<lambda>x. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. f m x)\<close>
  \<open>(\<And>m. m \<in># M \<Longrightarrow> constructive (f m)) \<Longrightarrow> constructive (\<lambda>x. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. f m x)\<close>
  by (induct M rule: induct_subset_mset_empty_single;
      simp add: Sync_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)+


corollary MultiSync_non_destructive : \<open>non_destructive (\<lambda>P. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m)\<close>
  by (rule MultiSync_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(1)[of M \<open>\<lambda>m x. x m\<close>]) simp



subsection \<open>Throw\<close>

lemma Throw_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive f \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> non_destructive (g a)) \<Longrightarrow> non_destructive (\<lambda>x. f x \<Theta> a \<in> A. g a x)\<close>
  \<open>constructive f \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> constructive (g a)) \<Longrightarrow> constructive (\<lambda>x. f x \<Theta> a \<in> A. g a x)\<close>
proof -
  have * : \<open>f x \<Theta> a \<in> A. g a x = f x \<Theta> a \<in> A. (if a \<in> A then g a x else STOP)\<close> for x
    by (auto intro: mono_Throw_eq)

  show \<open>non_destructive f \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> non_destructive (g a)) \<Longrightarrow> non_destructive (\<lambda>x. f x \<Theta> a \<in> A. g a x)\<close>
    by (subst "*", erule non_destructive_comp_non_destructive
        [OF Throw_non_destructive non_destructive_prod_codomain, simplified]) auto

  show \<open>constructive f \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> constructive (g a)) \<Longrightarrow> constructive (\<lambda>x. f x \<Theta> a \<in> A. g a x)\<close>
    by (subst "*", erule non_destructive_comp_constructive
        [OF Throw_non_destructive constructive_prod_codomain, simplified]) auto
qed



subsection \<open>Interrupt\<close>

lemma Interrupt_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_destructive f \<Longrightarrow> non_destructive g \<Longrightarrow> non_destructive (\<lambda>x. f x \<triangle> g x)\<close>
  \<open>constructive f \<Longrightarrow> constructive g \<Longrightarrow> constructive (\<lambda>x. f x \<triangle> g x)\<close>
  by (fact non_destructive_comp_non_destructive[OF Interrupt_non_destructive non_destructive_prod_codomain, simplified])
    (fact non_destructive_comp_constructive[OF Interrupt_non_destructive constructive_prod_codomain, simplified])



subsection \<open>After\<close>

lemma (in After) After_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>non_too_destructive \<Psi> \<Longrightarrow> constructive f \<Longrightarrow> non_destructive (\<lambda>x. f x  after a)\<close>
  \<open>non_too_destructive \<Psi> \<Longrightarrow> non_destructive f \<Longrightarrow> non_too_destructive (\<lambda>x. f x  after a)\<close>
  by (auto intro!: non_too_destructive_comp_constructive[OF non_too_destructive_After]
      non_too_destructive_comp_non_destructive[OF non_too_destructive_After])

lemma (in AfterExt) After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset] :
  \<open>\<lbrakk>non_too_destructive \<Psi>; non_too_destructive \<Omega>; constructive f\<rbrakk>
   \<Longrightarrow> non_destructive (\<lambda>x. f x  after\<^sub>\<checkmark> e)\<close>
  \<open>\<lbrakk>non_too_destructive \<Psi>; non_too_destructive \<Omega>; non_destructive f\<rbrakk>
   \<Longrightarrow> non_too_destructive (\<lambda>x. f x  after\<^sub>\<checkmark> e)\<close>
  by (auto intro!: non_too_destructive_comp_constructive[OF non_too_destructive_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
      non_too_destructive_comp_non_destructive[OF non_too_destructive_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
      simp add: non_too_destructive_fun_iff)




subsection \<open>Illustration\<close>

declare restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset [simp]


notepad begin
  fix e f g :: 'a fix r s :: 'r
  fix A B C :: \<open>'a set\<close>
  fix S :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set\<close>
  define P where \<open>P \<equiv> \<upsilon> X. ((\<box>a \<in> A \<rightarrow> X \<sqinter> SKIP r) \<triangle> (f \<rightarrow> STOP))
                            \<box> (g \<rightarrow> X)
                            \<box> ((f \<rightarrow> e \<rightarrow> (\<bottom> \<sqinter> (e \<rightarrow> X))) \<Theta> b \<in> insert e B. (e \<rightarrow> SKIP s))\<close>  
    (is \<open>P \<equiv> \<upsilon> X. ?f X\<close>)
  have \<open>constructive ?f\<close> by simp
  have \<open>cont ?f\<close> by simp
  have \<open>P = ?f P\<close>
    unfolding P_def by (subst restriction_fix_eq) simp_all


  define Q where \<open>Q \<equiv> \<upsilon> X. (\<lambda>\<sigma> \<sigma>' \<sigma>'' . e \<rightarrow> \<sqinter> b \<in> S \<sigma> \<sigma>' \<sigma>''. X b b b \<sqinter> SKIP r)\<close> (is \<open>Q \<equiv> \<upsilon> X. ?g X\<close>)
  have \<open>constructive ?g\<close> by simp


  define R where \<open>R \<equiv> \<upsilon> (x, y). (e \<rightarrow> y \<sqinter> SKIP r, \<box>a \<in> A \<rightarrow> x)\<close>
    (is \<open>R \<equiv> \<upsilon> (x, y). (?h y, ?i x)\<close>)
  have \<open>snd R = \<box>a \<in> A \<rightarrow> fst R\<close>
    by (unfold R_def, subst restriction_fix_eq)
      (simp_all add: case_prod_beta')

end



end