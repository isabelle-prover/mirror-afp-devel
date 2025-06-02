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


section \<open>Product over Restriction Spaces\<close>

(*<*)
theory Restriction_Spaces_Prod
  imports Restriction_Spaces_Classes
begin
  (*>*)

subsection \<open>Restriction Space\<close>

instantiation prod :: (restriction, restriction) restriction
begin

definition restriction_prod :: \<open>'a \<times> 'b \<Rightarrow> nat \<Rightarrow> 'a \<times> 'b\<close>
  where \<open>p \<down> n \<equiv> (fst p \<down> n, snd p \<down> n)\<close>

instance by intro_classes (simp add: restriction_prod_def)

end



instance prod :: (restriction_space, restriction_space) restriction_space
proof intro_classes
  show \<open>p \<down> 0 = q \<down> 0\<close> for p q :: \<open>'a \<times> 'b\<close>
    by (simp add: restriction_prod_def)
next
  show \<open>p \<noteq> q \<Longrightarrow> \<exists>n. p \<down> n \<noteq> q \<down> n\<close> for p q :: \<open>'a \<times> 'b\<close>
    by (simp add: restriction_prod_def)
      (meson ex_not_restriction_related prod.expand)
qed



instantiation prod :: (preorder_restriction_space, preorder_restriction_space) preorder_restriction_space
begin

text \<open>
We might want to use lexicographic order :
  \<^item> \<^term>\<open>p \<le> q \<equiv> fst p < fst q \<or> fst p = fst q \<and> snd p \<le> snd q\<close>
  \<^item> \<^term>\<open>p < q \<equiv> fst p < fst q \<or> (fst p = fst q \<and> snd p < snd q)\<close>

but this is wrong since it is incompatible with \<^term>\<open>p \<down> 0 \<le> q \<down> 0\<close>,
\<^term>\<open>\<not> p \<le> q \<Longrightarrow> \<exists>n. \<not> p \<down> n \<le> q \<down> n\<close> and \<^term>\<open>p \<le> q \<Longrightarrow> p \<down> n \<le> q \<down> n\<close>.\<close>

definition less_eq_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close>
  where \<open>p \<le> q \<equiv> fst p \<le> fst q \<and> snd p \<le> snd q\<close>

definition less_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close>
  where \<open>p < q \<equiv> fst p \<le> fst q \<and> snd p < snd q \<or> fst p < fst q \<and> snd p \<le> snd q\<close>

instance
proof intro_classes
  show \<open>p < q \<longleftrightarrow> p \<le> q \<and> \<not> q \<le> p\<close> for p q :: \<open>'a \<times> 'b\<close>
    by (auto simp add: less_eq_prod_def less_prod_def less_le_not_le)
next
  show \<open>p \<le> p\<close> for p :: \<open>'a \<times> 'b\<close>
    by (simp add: less_eq_prod_def)
next
  show \<open>p \<le> q \<Longrightarrow> q \<le> r \<Longrightarrow> p \<le> r\<close> for p q r :: \<open>'a \<times> 'b\<close>
    by (auto simp add: less_eq_prod_def intro: order_trans)
next
  show \<open>p \<down> 0 \<le> q \<down> 0\<close> for p q :: \<open>'a \<times> 'b\<close>
    by (simp add: less_eq_prod_def restriction_prod_def)
next
  show \<open>p \<le> q \<Longrightarrow> p \<down> n \<le> q \<down> n\<close> for p q :: \<open>'a \<times> 'b\<close> and n
    by (simp add: less_eq_prod_def restriction_prod_def mono_restriction_less_eq)
next
  show \<open>\<not> p \<le> q \<Longrightarrow> \<exists>n. \<not> p \<down> n \<le> q \<down> n\<close> for p q :: \<open>'a \<times> 'b\<close>
    by (simp add: less_eq_prod_def restriction_prod_def)
      (meson ex_not_restriction_less_eq)
qed

end


instance prod :: (order_restriction_space, order_restriction_space) order_restriction_space
  by intro_classes (simp add: less_eq_prod_def order_antisym prod.expand)



subsection \<open>Restriction shift Maps\<close>

subsubsection \<open>Domain is a Product\<close>

lemma restriction_shift_on_prod_domain_iff : 
  \<open>restriction_shift_on f k (A \<times> B) \<longleftrightarrow> (\<forall>x\<in>A. restriction_shift_on (\<lambda>y. f (x, y)) k B) \<and>
                                         (\<forall>y\<in>B. restriction_shift_on (\<lambda>x. f (x, y)) k A)\<close>
proof (intro iffI conjI ballI)
  show \<open>restriction_shift_on (\<lambda>y. f (x, y)) k B\<close>
    if \<open>restriction_shift_on f k (A \<times> B)\<close> and \<open>x \<in> A\<close> for x
  proof (rule restriction_shift_onI)
    show \<open>y1 \<in> B \<Longrightarrow> y2 \<in> B \<Longrightarrow> y1 \<down> n = y2 \<down> n \<Longrightarrow>
          f (x, y1) \<down> nat (int n + k) = f (x, y2) \<down> nat (int n + k)\<close> for y1 y2 n
      by (rule that(1)[THEN restriction_shift_onD])
        (use that(2) in \<open>simp_all add: restriction_prod_def\<close>)
  qed
next
  show \<open>restriction_shift_on (\<lambda>x. f (x, y)) k A\<close>
    if \<open>restriction_shift_on f k (A \<times> B)\<close> and \<open>y \<in> B\<close> for y
  proof (rule restriction_shift_onI)
    show \<open>x1 \<in> A \<Longrightarrow> x2 \<in> A \<Longrightarrow> x1 \<down> n = x2 \<down> n \<Longrightarrow>
          f (x1, y) \<down> nat (int n + k) = f (x2, y) \<down> nat (int n + k)\<close> for x1 x2 n
      by (rule that(1)[THEN restriction_shift_onD])
        (use that(2) in \<open>simp_all add: restriction_prod_def\<close>)
  qed
next
  assume assm : \<open>(\<forall>x\<in>A. restriction_shift_on (\<lambda>y. f (x, y)) k B) \<and>
                 (\<forall>y\<in>B. restriction_shift_on (\<lambda>x. f (x, y)) k A)\<close>
  show \<open>restriction_shift_on f k (A \<times> B)\<close>
  proof (rule restriction_shift_onI)
    fix p q n assume \<open>p \<in> A \<times> B\<close> \<open>q \<in> A \<times> B\<close> \<open>p \<down> n = q \<down> n\<close>
    then obtain x1 y1 x2 y2
      where \<open>p = (x1, y1)\<close> \<open>q = (x2, y2)\<close> \<open>x1 \<in> A\<close> \<open>y1 \<in> B\<close>
        \<open>x2 \<in> A\<close> \<open>y2 \<in> B\<close> \<open>x1 \<down> n = x2 \<down> n\<close> \<open>y1 \<down> n = y2 \<down> n\<close>
      by (cases p, cases q, simp add: restriction_prod_def)
    have \<open>p = (x1, y1)\<close> by (fact \<open>p = (x1, y1)\<close>)
    also have \<open>f (x1, y1) \<down> nat (int n + k) = f (x1, y2) \<down> nat (int n + k)\<close>
      by (rule assm[THEN conjunct1, rule_format, OF \<open>x1 \<in> A\<close>, THEN restriction_shift_onD])
        (fact \<open>y1 \<in> B\<close> \<open>y2 \<in> B\<close> \<open>y1 \<down> n = y2 \<down> n\<close>)+
    also have \<open>f (x1, y2) \<down> nat (int n + k) = f (x2, y2) \<down> nat (int n + k)\<close>
      by (rule assm[THEN conjunct2, rule_format, OF \<open>y2 \<in> B\<close>, THEN restriction_shift_onD])
        (fact \<open>x1 \<in> A\<close> \<open>x2 \<in> A\<close> \<open>x1 \<down> n = x2 \<down> n\<close>)+
    also have \<open>(x2, y2) = q\<close> by (simp add: \<open>q = (x2, y2)\<close>)
    finally show \<open>f p \<down> nat (int n + k) = f q \<down> nat (int n + k)\<close> .
  qed
qed

lemma restriction_shift_prod_domain_iff:
  \<open>restriction_shift f k \<longleftrightarrow> (\<forall>x. restriction_shift (\<lambda>y. f (x, y)) k) \<and>
                             (\<forall>y. restriction_shift (\<lambda>x. f (x, y)) k)\<close>
  unfolding restriction_shift_def
  by (metis UNIV_I UNIV_Times_UNIV restriction_shift_on_prod_domain_iff)


lemma non_too_destructive_on_prod_domain_iff :
  \<open>non_too_destructive_on f (A \<times> B) \<longleftrightarrow> (\<forall>x\<in>A. non_too_destructive_on (\<lambda>y. f (x, y)) B) \<and>
                                        (\<forall>y\<in>B. non_too_destructive_on (\<lambda>x. f (x, y)) A)\<close>
  by (simp add: non_too_destructive_on_def restriction_shift_on_prod_domain_iff)

lemma non_too_destructive_prod_domain_iff :
  \<open>non_too_destructive f \<longleftrightarrow> (\<forall>x. non_too_destructive (\<lambda>y. f (x, y))) \<and>
                             (\<forall>y. non_too_destructive (\<lambda>x. f (x, y)))\<close>
  unfolding non_too_destructive_def
  by (metis UNIV_I UNIV_Times_UNIV non_too_destructive_on_prod_domain_iff)


lemma non_destructive_on_prod_domain_iff :
  \<open>non_destructive_on f (A \<times> B) \<longleftrightarrow> (\<forall>x\<in>A. non_destructive_on (\<lambda>y. f (x, y)) B) \<and>
                                    (\<forall>y\<in>B. non_destructive_on (\<lambda>x. f (x, y)) A)\<close>
  by (simp add: non_destructive_on_def restriction_shift_on_prod_domain_iff)

lemma non_destructive_prod_domain_iff :
  \<open>non_destructive f \<longleftrightarrow> (\<forall>x. non_destructive (\<lambda>y. f (x, y))) \<and>
                         (\<forall>y. non_destructive (\<lambda>x. f (x, y)))\<close>
  unfolding non_destructive_def
  by (metis UNIV_I UNIV_Times_UNIV non_destructive_on_prod_domain_iff)


lemma constructive_on_prod_domain_iff :
  \<open>constructive_on f (A \<times> B) \<longleftrightarrow> (\<forall>x\<in>A. constructive_on (\<lambda>y. f (x, y)) B) \<and>
                                 (\<forall>y\<in>B. constructive_on (\<lambda>x. f (x, y)) A)\<close>
  by (simp add: constructive_on_def restriction_shift_on_prod_domain_iff)

lemma constructive_prod_domain_iff :
  \<open>constructive f \<longleftrightarrow> (\<forall>x. constructive (\<lambda>y. f (x, y))) \<and>
                      (\<forall>y. constructive (\<lambda>x. f (x, y)))\<close>
  unfolding constructive_def
  by (metis UNIV_I UNIV_Times_UNIV constructive_on_prod_domain_iff)



lemma restriction_shift_prod_domain [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. restriction_shift (\<lambda>y. f (x, y)) k;
    \<And>y. restriction_shift (\<lambda>x. f (x, y)) k\<rbrakk> \<Longrightarrow> restriction_shift f k\<close>
  and non_too_destructive_prod_domain [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. non_too_destructive (\<lambda>y. f (x, y));
    \<And>y. non_too_destructive (\<lambda>x. f (x, y))\<rbrakk> \<Longrightarrow> non_too_destructive f\<close>
  and non_destructive_prod_domain [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. non_destructive (\<lambda>y. f (x, y));
    \<And>y. non_destructive (\<lambda>x. f (x, y))\<rbrakk> \<Longrightarrow> non_destructive f\<close>
  and constructive_prod_domain [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. constructive (\<lambda>y. f (x, y));
    \<And>y. constructive (\<lambda>x. f (x, y))\<rbrakk> \<Longrightarrow> constructive f\<close>
  by (simp_all add: restriction_shift_prod_domain_iff non_too_destructive_prod_domain_iff
      non_destructive_prod_domain_iff constructive_prod_domain_iff)



subsubsection \<open>Codomain is a Product\<close>

lemma restriction_shift_on_prod_codomain_iff : 
  \<open>restriction_shift_on f k A \<longleftrightarrow> (restriction_shift_on (\<lambda>x. fst (f x)) k A) \<and>
                                  (restriction_shift_on (\<lambda>x. snd (f x)) k A)\<close>
  by (simp add: restriction_shift_on_def restriction_prod_def) blast


lemma restriction_shift_prod_codomain_iff:
  \<open>restriction_shift f k \<longleftrightarrow> (restriction_shift (\<lambda>x. fst (f x)) k) \<and>
                             (restriction_shift (\<lambda>x. snd (f x)) k)\<close>
  unfolding restriction_shift_def
  by (fact restriction_shift_on_prod_codomain_iff)


lemma non_too_destructive_on_prod_codomain_iff :
  \<open>non_too_destructive_on f A \<longleftrightarrow> (non_too_destructive_on (\<lambda>x. fst (f x)) A) \<and>
                                  (non_too_destructive_on (\<lambda>x. snd (f x)) A)\<close>
  by (simp add: non_too_destructive_on_def restriction_shift_on_prod_codomain_iff)

lemma non_too_destructive_prod_codomain_iff :
  \<open>non_too_destructive f \<longleftrightarrow> (non_too_destructive (\<lambda>x. fst (f x))) \<and>
                             (non_too_destructive (\<lambda>x. snd (f x)))\<close>
  by (simp add: non_too_destructive_def non_too_destructive_on_prod_codomain_iff)


lemma non_destructive_on_prod_codomain_iff :
  \<open>non_destructive_on f A \<longleftrightarrow> (non_destructive_on (\<lambda>x. fst (f x)) A) \<and>
                              (non_destructive_on (\<lambda>x. snd (f x)) A)\<close>

  by (simp add: non_destructive_on_def restriction_shift_on_prod_codomain_iff)

lemma non_destructive_prod_codomain_iff :
  \<open>non_destructive f \<longleftrightarrow> (non_destructive (\<lambda>x. fst (f x))) \<and>
                         (non_destructive (\<lambda>x. snd (f x)))\<close>
  by (simp add: non_destructive_def non_destructive_on_prod_codomain_iff)


lemma constructive_on_prod_codomain_iff :
  \<open>constructive_on f A \<longleftrightarrow> (constructive_on (\<lambda>x. fst (f x)) A) \<and>
                           (constructive_on (\<lambda>x. snd (f x)) A)\<close>
  by (simp add: constructive_on_def restriction_shift_on_prod_codomain_iff)

lemma constructive_prod_codomain_iff :
  \<open>constructive f \<longleftrightarrow> (constructive (\<lambda>x. fst (f x))) \<and>
                      (constructive (\<lambda>x. snd (f x)))\<close>
  by (simp add: constructive_def constructive_on_prod_codomain_iff)


lemma restriction_shift_prod_codomain [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>restriction_shift f k; restriction_shift g k\<rbrakk> \<Longrightarrow>
   restriction_shift (\<lambda>x. (f x, g x)) k\<close>
  and non_too_destructive_prod_codomain [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>non_too_destructive f; non_too_destructive g\<rbrakk> \<Longrightarrow> non_too_destructive (\<lambda>x. (f x, g x))\<close>
  and non_destructive_prod_codomain [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>non_destructive f; non_destructive g\<rbrakk> \<Longrightarrow> non_destructive (\<lambda>x. (f x, g x))\<close>
  and constructive_prod_codomain [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>constructive f; constructive g\<rbrakk> \<Longrightarrow> constructive (\<lambda>x. (f x, g x))\<close>
  by (simp_all add: restriction_shift_prod_codomain_iff non_too_destructive_prod_codomain_iff
      non_destructive_prod_codomain_iff constructive_prod_codomain_iff)



subsection \<open>Limits and Convergence\<close>

lemma restriction_chain_prod_iff :
  \<open>restriction_chain \<sigma> \<longleftrightarrow> restriction_chain (\<lambda>n. fst (\<sigma> n)) \<and>
                           restriction_chain (\<lambda>n. snd (\<sigma> n))\<close>
  by (simp add: restriction_chain_def restriction_prod_def)
    (metis fst_conv prod.collapse snd_conv)

lemma restriction_tendsto_prod_iff :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longleftrightarrow> (\<lambda>n. fst (\<sigma> n)) \<midarrow>\<down>\<rightarrow> fst \<Sigma> \<and> (\<lambda>n. snd (\<sigma> n)) \<midarrow>\<down>\<rightarrow> snd \<Sigma>\<close>
  by (simp add: restriction_tendsto_def restriction_prod_def)
    (meson nle_le order_trans)

lemma restriction_convergent_prod_iff :
  \<open>restriction_convergent \<sigma> \<longleftrightarrow> restriction_convergent (\<lambda>n. fst (\<sigma> n)) \<and>
                                restriction_convergent (\<lambda>n. snd (\<sigma> n))\<close>
  by (simp add: restriction_convergent_def restriction_tendsto_prod_iff)

lemma funpow_indep_prod_is :
  \<open>((\<lambda>(x, y). (f x, g y)) ^^ n) (x, y) = ((f ^^ n) x, (g ^^ n) y)\<close>
  for f g :: \<open>'a \<Rightarrow> 'a\<close>
  by (induct n) simp_all



subsection \<open>Completeness\<close>

instance prod :: (complete_restriction_space, complete_restriction_space) complete_restriction_space
proof intro_classes
  fix \<sigma> :: \<open>nat \<Rightarrow> 'a :: complete_restriction_space \<times> 'b :: complete_restriction_space\<close>
  assume \<open>chain\<^sub>\<down> \<sigma>\<close>
  hence \<open>chain\<^sub>\<down> (\<lambda>n. fst (\<sigma> n))\<close> \<open>chain\<^sub>\<down> (\<lambda>n. snd (\<sigma> n))\<close>
    by (simp_all add: restriction_chain_prod_iff)
  hence \<open>convergent\<^sub>\<down> (\<lambda>n. fst (\<sigma> n))\<close> \<open>convergent\<^sub>\<down> (\<lambda>n. snd (\<sigma> n))\<close>
    by (simp_all add: restriction_chain_imp_restriction_convergent)
  thus \<open>convergent\<^sub>\<down> \<sigma>\<close>
    by (simp add: restriction_convergent_prod_iff)
qed    



subsection \<open>Fixed Point\<close>

lemma restriction_fix_indep_prod_is :
  \<open>(\<upsilon> (x, y). (f x, g y)) = (\<upsilon> x. f x, \<upsilon> y. g y)\<close>
  if contructive : \<open>constructive f\<close> \<open>constructive g\<close>
  for f :: \<open>'a \<Rightarrow> 'a :: complete_restriction_space\<close>
    and g :: \<open>'b \<Rightarrow> 'b :: complete_restriction_space\<close>
proof (rule restriction_fix_unique)
  from contructive show \<open>constructive (\<lambda>(x, y). (f x, g y))\<close>
    by (simp add: constructive_prod_domain_iff constructive_prod_codomain_iff constructive_const)
next
  show \<open>(case (\<upsilon> x. f x, \<upsilon> y. g y) of (x, y) \<Rightarrow> (f x, g y)) = (\<upsilon> x. f x, \<upsilon> y. g y)\<close>
    by simp (metis restriction_fix_eq contructive)
qed



lemma non_destructive_fst : \<open>non_destructive fst\<close>
  by (rule non_destructiveI) (simp add: restriction_prod_def)

lemma non_destructive_snd : \<open>non_destructive snd\<close>
  by (rule non_destructiveI) (simp add: restriction_prod_def)




lemma constructive_restriction_fix_right :
  \<open>constructive (\<lambda>x. \<upsilon> y. f (x, y))\<close> if \<open>constructive f\<close>
for f :: \<open>'a :: complete_restriction_space \<times> 'b :: complete_restriction_space \<Rightarrow> 'b\<close>
proof (rule constructiveI)
  fix n and x x' :: 'a assume \<open>x \<down> n = x' \<down> n\<close>
  show \<open>(\<upsilon> y. f (x, y)) \<down> Suc n = (\<upsilon> y. f (x', y)) \<down> Suc n\<close>
  proof (subst (1 2) restriction_restriction_fix_is)
    show \<open>constructive (\<lambda>y. f (x', y))\<close> and \<open>constructive (\<lambda>y. f (x, y))\<close>
      using \<open>constructive f\<close> constructive_prod_domain_iff by blast+
  next
    from \<open>x \<down> n = x' \<down> n\<close> show \<open>((\<lambda>y. f (x, y)) ^^ Suc n) undefined \<down> Suc n =
                                ((\<lambda>y. f (x', y)) ^^ Suc n) undefined \<down> Suc n\<close>
      by (induct n, simp_all)
        (use \<open>constructive f\<close> constructiveD restriction_0_related in blast,
          metis (no_types, lifting) \<open>constructive f\<close> constructiveD prod.sel
          restriction_related_pred restriction_prod_def)
  qed
qed


lemma constructive_restriction_fix_left :
  \<open>constructive (\<lambda>y. \<upsilon> x. f (x, y))\<close> if \<open>constructive f\<close>
for f :: \<open>'a :: complete_restriction_space \<times> 'b :: complete_restriction_space \<Rightarrow> 'a\<close>
proof (rule constructiveI)
  fix n and y y' :: 'b assume \<open>y \<down> n = y' \<down> n\<close>
  show \<open>(\<upsilon> x. f (x, y)) \<down> Suc n = (\<upsilon> x. f (x, y')) \<down> Suc n\<close>
  proof (subst (1 2) restriction_restriction_fix_is)
    show \<open>constructive (\<lambda>x. f (x, y'))\<close> and \<open>constructive (\<lambda>x. f (x, y))\<close>
      using \<open>constructive f\<close> constructive_prod_domain_iff by blast+
  next
    from \<open>y \<down> n = y' \<down> n\<close> show \<open>((\<lambda>x. f (x, y)) ^^ Suc n) undefined \<down> Suc n =
                                ((\<lambda>x. f (x, y')) ^^ Suc n) undefined \<down> Suc n\<close>
      by (induct n, simp_all)
        (use restriction_0_related \<open>constructive f\<close> constructiveD in blast,
          metis (no_types, lifting) \<open>constructive f\<close> constructiveD prod.sel
          restriction_related_pred restriction_prod_def)
  qed
qed



\<comment> \<open>``Bekic's Theorem'' in HOLCF\<close>

lemma restriction_fix_prod_is :
  \<open>(\<upsilon> p. f p) = (\<upsilon> x. fst (f (x, \<upsilon> y. snd (f (x, y)))),
                 \<upsilon> y. snd (f (\<upsilon> x. fst (f (x, \<upsilon> y. snd (f (x, y)))), y)))\<close>
  (is \<open>(\<upsilon> p. f p) = (?x, ?y)\<close>) if \<open>constructive f\<close>
for f :: \<open>'a :: complete_restriction_space \<times> 'b :: complete_restriction_space \<Rightarrow> 'a \<times> 'b\<close>
proof (rule restriction_fix_unique[OF \<open>constructive f\<close>])
  have \<open>constructive (\<lambda>p. snd (f p))\<close>
    by (fact non_destructive_comp_constructive[OF non_destructive_snd \<open>constructive f\<close>])
  hence \<open>constructive (\<lambda>x. \<upsilon> y. snd (f (x, y)))\<close>
    by (fact constructive_restriction_fix_right)
  hence \<open>non_destructive (\<lambda>x. \<upsilon> y. snd (f (x, y)))\<close>
    by (fact constructive_imp_non_destructive)
  hence \<open>non_destructive (\<lambda>x. (x, \<upsilon> y. snd (f (x, y))))\<close>
    by (fact non_destructive_prod_codomain[OF non_destructive_id(2)])
  hence \<open>constructive (\<lambda>x. f (x, \<upsilon> y. snd (f (x, y))))\<close>
    by (fact constructive_comp_non_destructive[OF \<open>constructive f\<close>])
  hence * : \<open>constructive (\<lambda>x. fst (f (x, \<upsilon> y. snd (f (x, y)))))\<close>
    by (fact non_destructive_comp_constructive[OF non_destructive_fst])

  have \<open>non_destructive (\<lambda>x. \<upsilon> x. fst (f (x, \<upsilon> y. snd (f (x, y)))))\<close>
    by (fact constructive_imp_non_destructive[OF constructive_const])
  hence \<open>non_destructive (Pair (\<upsilon> x. fst (f (x, \<upsilon> y. snd (f (x, y))))))\<close>
    by (fact non_destructive_prod_codomain[OF _ non_destructive_id(2)])
  hence \<open>constructive (\<lambda>x. f (\<upsilon> x. fst (f (x, \<upsilon> y. snd (f (x, y)))), x))\<close>
    by (fact constructive_comp_non_destructive[OF \<open>constructive f\<close>])
  hence ** : \<open>constructive (\<lambda>x. snd (f (\<upsilon> x. fst (f (x, \<upsilon> y. snd (f (x, y)))), x)))\<close>
    by (fact non_destructive_comp_constructive[OF non_destructive_snd])

  have \<open>fst (f (?x, ?y)) = ?x\<close>
    by (rule trans [symmetric, OF restriction_fix_eq[OF "*"]]) simp
  moreover have \<open>snd (f (?x, ?y)) = ?y\<close>
    by (rule trans [symmetric, OF restriction_fix_eq[OF "**"]]) simp
  ultimately show \<open>f (?x, ?y) = (?x, ?y)\<close> by (cases \<open>f (?x, ?y)\<close>) simp
qed 


(*<*)
end
  (*>*)

