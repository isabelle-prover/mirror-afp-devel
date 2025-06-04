(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 * Author: Benjamin Puyobro, Université Paris-Saclay,
           IRT SystemX, CNRS, ENS Paris-Saclay, LMF
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


section \<open>Induction in Restriction Space\<close>

(*<*)
theory  Restriction_Spaces_Induction
  imports Restriction_Spaces_Topology
begin
  (*>*)

subsection \<open>Admissibility\<close>

named_theorems restriction_adm_simpset \<comment> \<open>For future automation.\<close>

subsubsection \<open>Definition\<close>

text \<open>We start by defining the notion of admissible predicate.
      The idea is that if this predicates holds for each value
      of a convergent sequence, it also holds for its limit.\<close>

context restriction begin

definition restriction_adm :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (\<open>adm\<^sub>\<down>\<close>)
  where \<open>restriction_adm P \<equiv> \<forall>\<sigma> \<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longrightarrow> (\<forall>n. P (\<sigma> n)) \<longrightarrow> P \<Sigma>\<close>

lemma restriction_admI :
  \<open>(\<And>\<sigma> \<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<And>n. P (\<sigma> n)) \<Longrightarrow> P \<Sigma>) \<Longrightarrow> restriction_adm P\<close>
  by (simp add: restriction_adm_def)

lemma restriction_admD :
  \<open>\<lbrakk>restriction_adm P; \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>; \<And>n. P (\<sigma> n)\<rbrakk> \<Longrightarrow> P \<Sigma>\<close>
  by (simp add: restriction_adm_def)


subsubsection \<open>Properties\<close>

lemma restriction_adm_const [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. t)\<close>
  by (simp add: restriction_admI)

lemma restriction_adm_conj [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. P x) \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. Q x) \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. P x \<and> Q x)\<close>
  by (fast intro: restriction_admI elim: restriction_admD)

lemma restriction_adm_all [restriction_adm_simpset] :
  \<open>(\<And>y. adm\<^sub>\<down> (\<lambda>x. P x y)) \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. \<forall>y. P x y)\<close>
  by (fast intro: restriction_admI elim: restriction_admD)

lemma restriction_adm_ball [restriction_adm_simpset] :
  \<open>(\<And>y. y \<in> A \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. P x y)) \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. \<forall>y\<in>A. P x y)\<close>
  by (fast intro: restriction_admI elim: restriction_admD)

lemma restriction_adm_disj [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. P x \<or> Q x)\<close> if \<open>adm\<^sub>\<down> (\<lambda>x. P x)\<close> \<open>adm\<^sub>\<down> (\<lambda>x. Q x)\<close>
proof (rule restriction_admI)
  fix \<sigma> \<Sigma>
  assume * : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>\<And>n. P (\<sigma> n) \<or> Q (\<sigma> n)\<close>
  from "*"(2) have ** : \<open>(\<forall>i. \<exists>j\<ge>i. P (\<sigma> j)) \<or> (\<forall>i. \<exists>j\<ge>i. Q (\<sigma> j))\<close>
    by (meson nat_le_linear)

  { fix P assume $ : \<open>adm\<^sub>\<down> (\<lambda>x. P x)\<close> \<open>\<forall>i. \<exists>j\<ge>i. P (\<sigma> j)\<close>
    define f where \<open>f i = (LEAST j. i \<le> j \<and> P (\<sigma> j))\<close> for i 
    have f1: \<open>\<And>i. i \<le> f i\<close> and f2: \<open>\<And>i. P (\<sigma> (f i))\<close>
      using LeastI_ex [OF "$"(2)[rule_format]] by (simp_all add: f_def)
    have f3 : \<open>(\<lambda>n. \<sigma> (f n)) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
    proof (rule restriction_tendstoI)
      fix n
      from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> restriction_tendstoD obtain n0 where \<open>\<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> k \<down> n\<close> by blast
      hence \<open>\<forall>k\<ge>max n0 n. \<Sigma> \<down> n = \<sigma> (f k) \<down> n\<close> by (meson f1 le_trans max.boundedE)
      thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> (f k) \<down> n\<close> by blast
    qed
    have \<open>P \<Sigma>\<close> by (fact restriction_admD[OF "$"(1) f3 f2])
  }

  with "**" \<open>adm\<^sub>\<down> (\<lambda>x. P x)\<close> \<open>adm\<^sub>\<down> (\<lambda>x. Q x)\<close> show \<open>P \<Sigma> \<or> Q \<Sigma>\<close> by blast
qed

lemma restriction_adm_imp [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. \<not> P x) \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. Q x) \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. P x \<longrightarrow> Q x)\<close>
  by (subst imp_conv_disj) (rule restriction_adm_disj)


lemma restriction_adm_iff [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. P x \<longrightarrow> Q x) \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. Q x \<longrightarrow> P x) \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. P x \<longleftrightarrow> Q x)\<close>
  by (subst iff_conv_conj_imp) (rule restriction_adm_conj)

lemma restriction_adm_if_then_else [restriction_adm_simpset]:
  \<open>\<lbrakk>P \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. Q x); \<not> P \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. R x)\<rbrakk> \<Longrightarrow>
   adm\<^sub>\<down> (\<lambda>x. if P then Q x else R x)\<close>
  by (simp add: restriction_adm_def)

end



text \<open>The notion of continuity is of course strongly related to the notion of admissibility.\<close>

lemma restriction_adm_eq [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. f x = g x)\<close> if \<open>cont\<^sub>\<down> f\<close> and \<open>cont\<^sub>\<down> g\<close>
for f g :: \<open>'a :: restriction \<Rightarrow> 'b :: restriction_space\<close>
proof (rule restriction_admI)
  fix \<sigma> \<Sigma> assume \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> and \<open>\<And>n. f (\<sigma> n) = g (\<sigma> n)\<close>
  from restriction_contD[OF \<open>cont\<^sub>\<down> f\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>] have \<open>(\<lambda>n. f (\<sigma> n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close> .
  hence \<open>(\<lambda>n. g (\<sigma> n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close> by (unfold \<open>\<And>n. f (\<sigma> n) = g (\<sigma> n)\<close>)
  moreover from restriction_contD[OF \<open>cont\<^sub>\<down> g\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>] have \<open>(\<lambda>n. g (\<sigma> n)) \<midarrow>\<down>\<rightarrow> g \<Sigma>\<close> .
  ultimately show \<open>f \<Sigma> = g \<Sigma>\<close> by (fact restriction_tendsto_unique)
qed

lemma restriction_adm_subst [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. P (t x))\<close> if \<open>cont\<^sub>\<down> (\<lambda>x. t x)\<close> and \<open>adm\<^sub>\<down> P\<close>
proof (rule restriction_admI)
  fix \<sigma> \<Sigma> assume \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>\<And>n. P (t (\<sigma> n))\<close>
  from restriction_contD[OF \<open>cont\<^sub>\<down> (\<lambda>x. t x)\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>]
  have \<open>(\<lambda>n. t (\<sigma> n)) \<midarrow>\<down>\<rightarrow> t \<Sigma>\<close> .
  from restriction_admD[OF \<open>restriction_adm P\<close> \<open>(\<lambda>n. t (\<sigma> n)) \<midarrow>\<down>\<rightarrow> t \<Sigma>\<close> \<open>\<And>n. P (t (\<sigma> n))\<close>]
  show \<open>P (t \<Sigma>)\<close> .
qed



lemma restriction_adm_prod_domainD [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>x. P (x, y))\<close> and \<open>adm\<^sub>\<down> (\<lambda>y. P (x, y))\<close> if \<open>adm\<^sub>\<down> P\<close>
proof -
  show \<open>adm\<^sub>\<down> (\<lambda>x. P (x, y))\<close>
  proof (rule restriction_admI)
    show \<open>P (\<Sigma>, y)\<close> if \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>\<And>n. P (\<sigma> n, y)\<close> for \<sigma> \<Sigma>
    proof (rule restriction_admD[OF \<open>adm\<^sub>\<down> P\<close> _ \<open>\<And>n. P (\<sigma> n, y)\<close>])
      show \<open>(\<lambda>n. (\<sigma> n, y)) \<midarrow>\<down>\<rightarrow> (\<Sigma>, y)\<close>
        by (simp add: restriction_tendsto_prod_iff restriction_tendsto_const \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>)
    qed
  qed
next
  show \<open>adm\<^sub>\<down> (\<lambda>y. P (x, y))\<close>
  proof (rule restriction_admI)
    show \<open>P (x, \<Sigma>)\<close> if \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>\<And>n. P (x, \<sigma> n)\<close> for \<sigma> \<Sigma>
    proof (rule restriction_admD[OF \<open>adm\<^sub>\<down> P\<close> _ \<open>\<And>n. P (x, \<sigma> n)\<close>])
      show \<open>(\<lambda>n. (x, \<sigma> n)) \<midarrow>\<down>\<rightarrow> (x, \<Sigma>)\<close>
        by (simp add: restriction_tendsto_prod_iff restriction_tendsto_const \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>)
    qed
  qed
qed



lemma restriction_adm_restriction_shift_on [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>f. restriction_shift_on f k A)\<close>
proof (rule restriction_admI)
  fix \<sigma> :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'b\<close> and \<Sigma> :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> and hyp : \<open>restriction_shift_on (\<sigma> n) k A\<close> for n
  show \<open>restriction_shift_on \<Sigma> k A\<close>
  proof (rule restriction_shift_onI)
    fix x y n assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<down> n = y \<down> n\<close>
    from hyp[THEN restriction_shift_onD, OF this]
    have * : \<open>\<sigma> m x \<down> nat (int n + k) = \<sigma> m y \<down> nat (int n + k)\<close> for m .
    show \<open>\<Sigma> x \<down> nat (int n + k) = \<Sigma> y \<down> nat (int n + k)\<close>
    proof (rule restriction_tendsto_unique)
      show \<open>(\<lambda>m. \<sigma> m x \<down> nat (int n + k)) \<midarrow>\<down>\<rightarrow> \<Sigma> x \<down> nat (int n + k)\<close>
        by (simp add: \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> restriction_tendsto_const_restricted restriction_tendsto_fun_imp)
    next
      show \<open>(\<lambda>m. \<sigma> m x \<down> nat (int n + k)) \<midarrow>\<down>\<rightarrow> \<Sigma> y \<down> nat (int n + k)\<close>
        by (simp add: "*" \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> restriction_tendsto_const_restricted restriction_tendsto_fun_imp)
    qed
  qed
qed

lemma restriction_adm_constructive_on [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>f. constructive_on f A)\<close>
  by (simp add: constructive_on_def restriction_adm_restriction_shift_on)

lemma restriction_adm_non_destructive_on [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>f. non_destructive_on f A)\<close>
  by (simp add: non_destructive_on_def restriction_adm_restriction_shift_on)


lemma restriction_adm_restriction_cont_at [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>f. cont\<^sub>\<down> f at a)\<close>
proof (rule restriction_admI)
  fix \<sigma> :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'b\<close> and \<Sigma> :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> and hyp : \<open>cont\<^sub>\<down> (\<sigma> n) at a\<close> for n
  show \<open>cont\<^sub>\<down> \<Sigma> at a\<close>
  proof (rule restriction_cont_atI)
    fix \<gamma> assume \<open>\<gamma> \<midarrow>\<down>\<rightarrow> a\<close>
    from hyp[THEN restriction_cont_atD, OF this, THEN restriction_tendstoD]
    have \<open>\<exists>n0. \<forall>k\<ge>n0. \<sigma> m a \<down> n = \<sigma> m (\<gamma> k) \<down> n\<close> for m n .
    moreover from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>[THEN restriction_tendstoD]
    have \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> k \<down> n\<close> for n .
    ultimately show \<open>(\<lambda>n. \<Sigma> (\<gamma> n)) \<midarrow>\<down>\<rightarrow> \<Sigma> a\<close>
      by (intro restriction_tendstoI) (metis restriction_fun_def)
  qed
qed

lemma restriction_adm_restriction_cont_on [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>f. cont\<^sub>\<down> f on A)\<close>
  unfolding restriction_cont_on_def
  by (intro restriction_adm_ball restriction_adm_restriction_cont_at)



corollary restriction_adm_restriction_shift [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>f. restriction_shift f k)\<close>
  and    restriction_adm_constructive [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>f. constructive f)\<close>
  and    restriction_adm_non_destructive [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>f. non_destructive f)\<close>
  and    restriction_adm_restriction_cont [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>f. cont\<^sub>\<down> f)\<close>
  by (simp_all add: restriction_adm_simpset restriction_shift_def
      constructive_def non_destructive_def)



lemma (in restriction) restriction_adm_mem_restriction_closed [restriction_adm_simpset] :
  \<open>closed\<^sub>\<down> K \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. x \<in> K)\<close>
  by (auto intro!: restriction_admI dest: restriction_closed_sequentialD)

lemma (in restriction_space) restriction_adm_mem_restriction_compact [restriction_adm_simpset] :
  \<open>compact\<^sub>\<down> K \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. x \<in> K)\<close>
  by (simp add: restriction_adm_mem_restriction_closed restriction_compact_imp_restriction_closed)

lemma (in restriction_space) restriction_adm_mem_finite [restriction_adm_simpset] :
  \<open>finite S \<Longrightarrow> adm\<^sub>\<down> (\<lambda>x. x \<in> S)\<close>
  by (simp add: finite_imp_restriction_compact restriction_adm_mem_restriction_compact)


lemma restriction_adm_restriction_tendsto [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>\<sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close>
  by (intro restriction_admI restriction_tendstoI)
    (metis (no_types, opaque_lifting) restriction_fun_def restriction_tendsto_def)

lemma restriction_adm_lim [restriction_adm_simpset] :
  \<open>adm\<^sub>\<down> (\<lambda>\<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close>
  by (metis restriction_admI restriction_openD restriction_open_restriction_cball
      restriction_tendsto_iff_restriction_cball_characterization)


lemma restriction_restriction_cont_on [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f on A \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. f x \<down> n) on A\<close>
  by (rule restriction_cont_onI)
    (simp add: restriction_cont_onD restriction_tendsto_const_restricted)

lemma restriction_cont_on_id [restriction_cont_simpset] : \<open>cont\<^sub>\<down> (\<lambda>x. x) on A\<close>
  by (simp add: restriction_cont_onI)

lemma restriction_cont_on_const [restriction_cont_simpset] : \<open>cont\<^sub>\<down> (\<lambda>x. c) on A\<close>
  by (simp add: restriction_cont_onI restriction_tendstoI)

lemma restriction_cont_on_fun [restriction_cont_simpset] : \<open>cont\<^sub>\<down> (\<lambda>f. f x) on A\<close>
  by (rule restriction_cont_onI) (simp add: restriction_tendsto_fun_imp)

lemma restriction_cont2cont_on_fun [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f on A \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. f x y) on A\<close>
  by (rule restriction_cont_onI)
    (metis restriction_cont_onD restriction_tendsto_fun_imp)







subsection \<open>Induction\<close>

text \<open>Now that we have the concept of admissibility,
      we can formalize an induction rule for fixed points.
      Considering a \<^const>\<open>constructive\<close> function \<^term>\<open>f\<close> of type \<^typ>\<open>'a \<Rightarrow> 'a\<close>
      (where \<^typ>\<open>'a\<close> is instance of the class \<^class>\<open>complete_restriction_space\<close>)
      and a predicate \<^term>\<open>P\<close> which is admissible, and assuming that :
      \<^item> \<^term>\<open>P\<close> holds for a certain element \<^term>\<open>x\<close>
      \<^item> for any element \<^term>\<open>x\<close>, if \<^term>\<open>P\<close> holds for \<^term>\<open>x\<close> then it still holds for \<^term>\<open>f x\<close>
      
      we can have that \<^term>\<open>P\<close> holds for the fixed point \<^term>\<open>\<upsilon> x. P x\<close>.\<close>

lemma restriction_fix_ind' [case_names constructive adm steps] :
  \<open>constructive f \<Longrightarrow> adm\<^sub>\<down> P \<Longrightarrow> (\<And>n. P ((f ^^ n) x)) \<Longrightarrow> P (\<upsilon> x. f x)\<close>
  using restriction_admD funpow_restriction_tendsto_restriction_fix by blast

lemma restriction_fix_ind [case_names constructive adm base step] :
  \<open>P (\<upsilon> x. f x)\<close> if \<open>constructive f\<close> \<open>adm\<^sub>\<down> P\<close> \<open>P x\<close> \<open>\<And>x. P x \<Longrightarrow> P (f x)\<close>
proof (induct rule: restriction_fix_ind')
  show \<open>constructive f\<close> by (fact \<open>constructive f\<close>)
next
  show \<open>restriction_adm P\<close> by (fact \<open>restriction_adm P\<close>)
next
  show \<open>P ((f ^^ n) x)\<close> for n
    by (induct n) (simp_all add: \<open>P x\<close> \<open>\<And>x. P x \<Longrightarrow> P (f x)\<close>)
qed

lemma restriction_fix_ind2 [case_names constructive adm base0 base1 step] :
  \<open>P (\<upsilon> x. f x)\<close> if \<open>constructive f\<close> \<open>adm\<^sub>\<down> P\<close> \<open>P x\<close> \<open>P (f x)\<close>
  \<open>\<And>x. \<lbrakk>P x; P (f x)\<rbrakk> \<Longrightarrow> P (f (f x))\<close>
proof (induct rule: restriction_fix_ind')
  show \<open>constructive f\<close> by (fact \<open>constructive f\<close>)
next
  show \<open>restriction_adm P\<close> by (fact \<open>restriction_adm P\<close>)
next
  show \<open>P ((f ^^ n) x)\<close> for n
    by (induct n rule: induct_nat_012) (simp_all add: that(3-5))
qed


text \<open>We can rewrite the fixed point over a product to
      obtain this parallel fixed point induction rule. \<close>

lemma parallel_restriction_fix_ind [case_names constructiveL constructiveR adm base step] :
  fixes f :: \<open>'a :: complete_restriction_space \<Rightarrow> 'a\<close>
    and g :: \<open>'b :: complete_restriction_space \<Rightarrow> 'b\<close>
  assumes constructive : \<open>constructive f\<close> \<open>constructive g\<close>
    and adm  : \<open>restriction_adm (\<lambda>p. P (fst p) (snd p))\<close>
    and base : \<open>P x y\<close> and step : \<open>\<And>x y. P x y \<Longrightarrow> P (f x) (g y)\<close>
  shows \<open>P (\<upsilon> x. f x) (\<upsilon> y. g y)\<close>
proof -
  define F where \<open>F \<equiv> \<lambda>(x, y). (f x, g y)\<close>
  define Q where \<open>Q \<equiv> \<lambda>(x, y). P x y\<close>

  have \<open>P (\<upsilon> x. f x) (\<upsilon> y. g y) = Q (\<upsilon> p. F p)\<close>
    by (simp add: F_def Q_def constructive restriction_fix_indep_prod_is)
  also have \<open>Q (\<upsilon> p. F p)\<close> 
  proof (induct F rule : restriction_fix_ind)
    show \<open>constructive F\<close>
      by (simp add: F_def constructive_prod_codomain_iff constructive_prod_domain_iff constructive constructive_const)
  next
    show \<open>restriction_adm Q\<close>
      by (unfold Q_def) (metis (mono_tags, lifting) adm case_prod_beta restriction_adm_def)
  next
    show \<open>Q (x, y)\<close> by (simp add: Q_def base)
  next
    show \<open>Q p \<Longrightarrow> Q (F p)\<close> for p by (simp add: Q_def F_def step split_beta)
  qed
  finally show \<open>P (\<upsilon> x. f x) (\<upsilon> y. g y)\<close> .
qed


text \<open>k-steps induction\<close>

lemma restriction_fix_ind_k_steps [case_names constructive adm base_k_steps step] :
  assumes \<open>constructive f\<close>
    and \<open>adm\<^sub>\<down> P\<close>
    and \<open>\<forall>i < k. P ((f ^^ i) x)\<close>
    and \<open>\<And>x. \<forall>i < k. P ((f ^^ i) x) \<Longrightarrow> P ((f ^^ k) x)\<close>
  shows \<open>P (\<upsilon> x. f x)\<close>
proof (rule restriction_fix_ind')
  show \<open>constructive f\<close> by (fact \<open>constructive f\<close>)
next
  show \<open>adm\<^sub>\<down> P\<close> by (fact \<open>adm\<^sub>\<down> P\<close>)
next
  have nat_k_induct :
    \<open>P n\<close> if \<open>\<forall>i<k. P i\<close> and \<open>\<forall>n\<^sub>0. (\<forall>i<k. P (n\<^sub>0 + i)) \<longrightarrow> P (n\<^sub>0 + k)\<close> for k n :: nat and P
  proof (induct rule: nat_less_induct)
    fix n assume \<open>\<forall>m<n. P m\<close>
    show \<open>P n\<close>
    proof (cases \<open>n < k\<close>)
      from that(1) show \<open>n < k \<Longrightarrow> P n\<close> by blast
    next
      from \<open>\<forall>m<n. P m\<close> that(2)[rule_format, of \<open>n - k\<close>]
      show \<open>\<not> n < k \<Longrightarrow> P n\<close> by auto
    qed
  qed
  show \<open>P ((f ^^ i) x)\<close> for i
  proof (induct rule: nat_k_induct)
    show \<open>\<forall>i<k. P ((f ^^ i) x)\<close> by (simp add: assms(3))
  next
    show \<open>\<forall>n\<^sub>0. (\<forall>i<k. P ((f ^^ (n\<^sub>0 + i)) x)) \<longrightarrow> P ((f ^^ (n\<^sub>0 + k)) x)\<close>
      by (smt (verit, del_insts) add.commute assms(4) funpow_add o_apply)
  qed
qed



(*<*)
end
  (*>*)
