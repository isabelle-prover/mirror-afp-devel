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


section \<open>Class Implementation\<close>

(*<*)
theory Restriction_Spaces_Classes
  imports Restriction_Spaces_Locales
begin
  (*>*)


subsection \<open>Preliminaries\<close>

text \<open>Small lemma from \<^verbatim>\<open>HOL-Library.Infinite_Set\<close> to avoid dependency.\<close>

lemma INFM_nat_le: \<open>(\<exists>\<^sub>\<infinity>n :: nat. P n) \<longleftrightarrow> (\<forall>m. \<exists>n\<ge>m. P n)\<close>
  unfolding cofinite_eq_sequentially frequently_sequentially by simp

text \<open>We need to be able to extract a subsequence verifying a predicate.\<close>


fun extraction_subseq :: \<open>[nat \<Rightarrow> 'a, 'a \<Rightarrow> bool] \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>extraction_subseq \<sigma> P 0 = (LEAST k. P (\<sigma> k))\<close>
  | \<open>extraction_subseq \<sigma> P (Suc n) = (LEAST k. extraction_subseq \<sigma> P n < k \<and> P (\<sigma> k))\<close>


lemma exists_extraction_subseq :
  assumes \<open>\<exists>\<^sub>\<infinity>k. P (\<sigma> k)\<close>
  defines f_def : \<open>f \<equiv> extraction_subseq \<sigma> P\<close>
  shows \<open>strict_mono f\<close> and \<open>P (\<sigma> (f k))\<close>
proof -
  have \<open>f n < f (Suc n) \<and> P (\<sigma> (f n))\<close> for n
    by (cases n, simp_all add: f_def)
      (metis (mono_tags, lifting) \<open>\<exists>\<^sub>\<infinity>k. P (\<sigma> k)\<close>[unfolded INFM_nat_le] LeastI_ex Suc_le_eq)+
  thus \<open>strict_mono f\<close> and \<open>P (\<sigma> (f k))\<close>
    by (simp_all add: strict_mono_Suc_iff)
qed


lemma extraction_subseqD :
  \<open>\<exists>f :: nat \<Rightarrow> nat. strict_mono f \<and> (\<forall>k. P (\<sigma> (f k)))\<close> if \<open>\<exists>\<^sub>\<infinity>k. P (\<sigma> k)\<close>
proof (rule exI)
  show \<open>strict_mono (extraction_subseq \<sigma> P) \<and> (\<forall>k. P (\<sigma> ((extraction_subseq \<sigma> P) k)))\<close>
    by (simp add: \<open>\<exists>\<^sub>\<infinity>k. P (\<sigma> k)\<close> exists_extraction_subseq)
qed

lemma extraction_subseqE :
  \<comment> \<open>The idea is to abstract the concrete construction of this extraction function,
      we only need the fact that there is one.\<close>
  \<open>\<exists>\<^sub>\<infinity>k. P (\<sigma> k) \<Longrightarrow> (\<And>f :: nat \<Rightarrow> nat. strict_mono f \<Longrightarrow> (\<And>k. P (\<sigma> (f k))) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (blast dest: extraction_subseqD) 



subsection \<open>Basic Notions for Restriction\<close>

class restriction = 
  fixes restriction :: \<open>['a, nat] \<Rightarrow> 'a\<close>  (infixl \<open>\<down>\<close> 60)
  assumes [simp] : \<open>x \<down> n \<down> m = x \<down> min n m\<close>
begin

sublocale Restriction \<open>(\<down>)\<close> \<open>(=)\<close> by unfold_locales simp
    \<comment> \<open>Just to recover \<^const>\<open>restriction_related_set\<close> and \<^const>\<open>restriction_not_related_set\<close>.\<close>
end

class restriction_space = restriction +
  assumes [simp] : \<open>x \<down> 0 = y \<down> 0\<close>
    and ex_not_restriction_eq : \<open>x \<noteq> y \<Longrightarrow> \<exists>n. x \<down> n \<noteq> y \<down> n\<close>
begin

sublocale PreorderRestrictionSpace \<open>(\<down>)\<close> \<open>(=)\<close>
  by unfold_locales (simp_all add: ex_not_restriction_eq)



lemma restriction_related_set_commute :
  \<open>restriction_related_set x y = restriction_related_set y x\<close> by auto

lemma restriction_not_related_set_commute :
  \<open>restriction_not_related_set x y = restriction_not_related_set y x\<close> by auto

end

context restriction_space begin

sublocale Restriction_2_PreorderRestrictionSpace
  \<open>(\<down>) :: 'b :: restriction \<Rightarrow> nat \<Rightarrow> 'b\<close> \<open>(=)\<close>
  \<open>(\<down>) :: 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(=)\<close> ..

text \<open>With this we recover constants like \<^const>\<open>restriction_shift_on\<close>.\<close>

sublocale PreorderRestrictionSpace_2_PreorderRestrictionSpace
  \<open>(\<down>) :: 'b :: restriction_space \<Rightarrow> nat \<Rightarrow> 'b\<close> \<open>(=)\<close>
  \<open>(\<down>) :: 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(=)\<close> ..

text \<open>With that we recover theorems like @{thm constructive_restriction_restriction}.\<close>

sublocale Restriction_2_PreorderRestrictionSpace_2_PreorderRestrictionSpace
  \<open>(\<down>) :: 'c :: restriction \<Rightarrow> nat \<Rightarrow> 'c\<close> \<open>(=)\<close>
  \<open>(\<down>) :: 'b :: restriction_space \<Rightarrow> nat \<Rightarrow> 'b\<close> \<open>(=)\<close>
  \<open>(\<down>) :: 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(=)\<close> ..

text \<open>And with that we recover theorems like @{thm constructive_on_comp_non_destructive_on}.\<close>



lemma restriction_shift_const [restriction_shift_simpset] :
  \<open>restriction_shift (\<lambda>x. c) k\<close> by (simp add: restriction_shiftI)

lemma constructive_const [restriction_shift_simpset] :
  \<open>constructive (\<lambda>x. c)\<close> by (simp add: constructiveI)




end

lemma restriction_shift_on_restricted [restriction_shift_simpset] :
  \<open>restriction_shift_on (\<lambda>x. f x \<down> n) k A\<close> if \<open>restriction_shift_on f k A\<close>
proof (rule restriction_shift_onI)
  fix x y m assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<down> m = y \<down> m\<close>
  from restriction_shift_onD[OF \<open>restriction_shift_on f k A\<close> this]
  have \<open>f x \<down> nat (int m + k) = f y \<down> nat (int m + k)\<close> .
  hence \<open>f x \<down> nat (int m + k) \<down> n = f y \<down> nat (int m + k) \<down> n\<close> by argo
  thus \<open>f x \<down> n \<down> nat (int m + k) = f y \<down> n \<down> nat (int m + k)\<close>
    by (simp add: min.commute)
qed

lemma restriction_shift_restricted [restriction_shift_simpset] :
  \<open>restriction_shift f k \<Longrightarrow> restriction_shift (\<lambda>x. f x \<down> n) k\<close>
  using restriction_shift_def restriction_shift_on_restricted by blast

corollary constructive_restricted [restriction_shift_simpset] :
  \<open>constructive f \<Longrightarrow> constructive (\<lambda>x. f x \<down> n)\<close>
  by (simp add: constructive_def constructive_on_def restriction_shift_on_restricted)

corollary non_destructive_restricted [restriction_shift_simpset] :
  \<open>non_destructive f \<Longrightarrow> non_destructive (\<lambda>x. f x \<down> n)\<close>
  by (simp add: non_destructive_def non_destructive_on_def restriction_shift_on_restricted)


lemma non_destructive_id [restriction_shift_simpset] :
  \<open>non_destructive id\<close> \<open>non_destructive (\<lambda>x. x)\<close>
  by (simp_all add: id_def non_destructiveI)



interpretation less_eqRS : Restriction \<open>(\<down>)\<close> \<open>(\<le>)\<close> by unfold_locales
    \<comment> \<open>Just to recover \<^const>\<open>less_eqRS.restriction_related_set\<close> and
   \<^const>\<open>less_eqRS.restriction_not_related_set\<close>.\<close>


class preorder_restriction_space = restriction + preorder +
  assumes restriction_0_less_eq [simp] : \<open>x \<down> 0 \<le> y \<down> 0\<close>
    and mono_restriction_less_eq     : \<open>x \<le> y \<Longrightarrow> x \<down> n \<le> y \<down> n\<close>
    and ex_not_restriction_less_eq   : \<open>\<not> x \<le> y \<Longrightarrow> \<exists>n. \<not> x \<down> n \<le> y \<down> n\<close>
begin

sublocale less_eqRS : PreorderRestrictionSpace \<open>(\<down>) :: 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(\<le>)\<close>
proof unfold_locales
  show \<open>x \<down> 0 \<le> y \<down> 0\<close> for x y :: 'a by simp
next
  show \<open>x \<le> y \<Longrightarrow> x \<down> n \<le> y \<down> n\<close> for x y :: 'a and n
    by (fact mono_restriction_less_eq)
next
  show \<open>\<not> x \<le> y \<Longrightarrow> \<exists>n. \<not> x \<down> n \<le> y \<down> n\<close> for x y :: 'a
    by (simp add: ex_not_restriction_less_eq)
next
  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close> for x y z :: 'a by (fact order_trans)
qed

end


class order_restriction_space = preorder_restriction_space + order
begin

subclass restriction_space
proof unfold_locales
  show \<open>x \<down> 0 = y \<down> 0\<close> for x y :: 'a by (rule order_antisym) simp_all
next
  show \<open>x \<noteq> y \<Longrightarrow> \<exists>n. x \<down> n \<noteq> y \<down> n\<close> for x y :: 'a
    by (metis ex_not_restriction_less_eq order.eq_iff)
qed

end


context preorder_restriction_space begin

sublocale less_eqRS : Restriction_2_PreorderRestrictionSpace
  \<open>(\<down>) :: 'b :: {restriction, ord} \<Rightarrow> nat \<Rightarrow> 'b\<close> \<open>(\<le>)\<close>
  \<open>(\<down>) :: 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(\<le>)\<close> ..

text \<open>With this we recover constants like \<^const>\<open>less_eqRS.restriction_shift_on\<close>.\<close>

sublocale less_eqRS : PreorderRestrictionSpace_2_PreorderRestrictionSpace
  \<open>(\<down>) :: 'b :: preorder_restriction_space \<Rightarrow> nat \<Rightarrow> 'b\<close> \<open>(\<le>)\<close>
  \<open>(\<down>) :: 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(\<le>)\<close> ..

text \<open>With that we recover theorems like @{thm less_eqRS.constructive_restriction_restriction}.\<close>

sublocale less_eqRS : Restriction_2_PreorderRestrictionSpace_2_PreorderRestrictionSpace
  \<open>(\<down>) :: 'c :: restriction \<Rightarrow> nat \<Rightarrow> 'c\<close> \<open>(=)\<close>
  \<open>(\<down>) :: 'b :: preorder_restriction_space \<Rightarrow> nat \<Rightarrow> 'b\<close> \<open>(\<le>)\<close>
  \<open>(\<down>) :: 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(\<le>)\<close> ..

text \<open>And with that we recover theorems like @{thm less_eqRS.constructive_on_comp_non_destructive_on}.\<close>

end


context order_restriction_space begin

text \<open>From @{thm order_antisym} we can obtain stronger lemmas.\<close>

corollary order_restriction_shift_onI :
  \<open>(\<And>x y n. \<lbrakk>x \<in> A; y \<in> A; f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow>
             f x \<down> nat (int n + k) \<le> f y \<down> nat (int n + k))
   \<Longrightarrow> restriction_shift_on f k A\<close>
  by (simp add: order_antisym restriction_shift_onI)

corollary order_restriction_shiftI :
  \<open>(\<And>x y n. \<lbrakk>f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow>
             f x \<down> nat (int n + k) \<le> f y \<down> nat (int n + k))
   \<Longrightarrow> restriction_shift f k\<close>
  by (simp add: order_antisym restriction_shiftI)

corollary order_non_too_destructive_onI :
  \<open>(\<And>x y n. \<lbrakk>x \<in> A; y \<in> A; f x \<noteq> f y; x \<down> Suc n = y \<down> Suc n\<rbrakk> \<Longrightarrow>
             f x \<down> n \<le> f y \<down> n)
   \<Longrightarrow> non_too_destructive_on f A\<close>
  by (simp add: order_antisym non_too_destructive_onI)

corollary order_non_too_destructiveI :
  \<open>(\<And>x y n. \<lbrakk>f x \<noteq> f y; x \<down> Suc n = y \<down> Suc n\<rbrakk> \<Longrightarrow> f x \<down> n \<le> f y \<down> n)
   \<Longrightarrow> non_too_destructive f\<close>
  by (simp add: order_antisym non_too_destructiveI)

corollary order_non_destructive_onI :
  \<open>(\<And>x y n. \<lbrakk>n \<noteq> 0; x \<in> A; y \<in> A; f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow> f x \<down> n \<le> f y \<down> n)
   \<Longrightarrow> non_destructive_on f A\<close>
  by (simp add: order_antisym non_destructive_onI)

corollary order_non_destructiveI :
  \<open>(\<And>x y n. \<lbrakk>n \<noteq> 0; f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow> f x \<down> n \<le> f y \<down> n)
   \<Longrightarrow> non_destructive f\<close>
  by (simp add: order_antisym non_destructiveI)

corollary order_constructive_onI :
  \<open>(\<And>x y n. \<lbrakk>x \<in> A; y \<in> A; f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow> f x \<down> Suc n \<le> f y \<down> Suc n)
   \<Longrightarrow> constructive_on f A\<close>
  by (simp add: order_antisym constructive_onI)

corollary order_constructiveI :
  \<open>(\<And>x y n. \<lbrakk>f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow> f x \<down> Suc n \<le> f y \<down> Suc n)
   \<Longrightarrow> constructive f\<close>
  by (simp add: order_antisym constructiveI)


end




subsection \<open>Definition of the Fixed-Point Operator\<close>

subsubsection \<open>Preliminaries\<close>

paragraph \<open>Chain\<close>

context restriction begin

definition restriction_chain :: \<open>[nat \<Rightarrow> 'a] \<Rightarrow> bool\<close> (\<open>chain\<^sub>\<down>\<close>)
  where \<open>restriction_chain \<sigma> \<equiv> \<forall>n. \<sigma> (Suc n) \<down> n = \<sigma> n\<close>

lemma restriction_chainI : \<open>(\<And>n. \<sigma> (Suc n) \<down> n = \<sigma> n) \<Longrightarrow> restriction_chain \<sigma>\<close>
  and restriction_chainD : \<open>restriction_chain \<sigma> \<Longrightarrow> \<sigma> (Suc n) \<down> n = \<sigma> n\<close>
  by (simp_all add: restriction_chain_def)

end


context restriction_space begin

lemma (in restriction_space) restriction_chain_def_bis:
  \<open>restriction_chain \<sigma> \<longleftrightarrow> (\<forall>n m. n < m \<longrightarrow> \<sigma> m \<down> n = \<sigma> n)\<close>
proof (rule iffI)
  show \<open>\<forall>n m. n < m \<longrightarrow> \<sigma> m \<down> n = \<sigma> n \<Longrightarrow> restriction_chain \<sigma>\<close>
    by (simp add: restriction_chainI)
next
  show \<open>restriction_chain \<sigma> \<Longrightarrow> \<forall>n m. n < m \<longrightarrow> \<sigma> m \<down> n = \<sigma> n\<close>
  proof (intro allI impI)
    fix n m
    assume restriction : \<open>restriction_chain \<sigma>\<close>
    show \<open>n < m \<Longrightarrow> \<sigma> m \<down> n = \<sigma> n\<close>
    proof (induct \<open>m - n\<close> arbitrary: m)
      fix m
      assume \<open>0 = m - n\<close> and \<open>n < m\<close>
      hence False by simp
      thus \<open>\<sigma> m \<down> n = \<sigma> n\<close> by simp
    next
      fix x m
      assume prems : \<open>Suc x = m - n\<close> \<open>n < m\<close>
      assume hyp : \<open>x = m' - n \<Longrightarrow> n < m' \<Longrightarrow> \<sigma> m' \<down> n = \<sigma> n\<close> for m'
      obtain m' where \<open>m = Suc m'\<close> by (meson less_imp_Suc_add prems(2))
      from prems(2) \<open>m = Suc m'\<close> consider \<open>n = m'\<close> | \<open>n < m'\<close> by linarith
      thus \<open>\<sigma> m \<down> n = \<sigma> n\<close>
      proof cases
        show \<open>n = m' \<Longrightarrow> \<sigma> m \<down> n = \<sigma> n\<close> 
          by (simp add: \<open>m = Suc m'\<close> restriction restriction_chainD)
      next
        assume \<open>n < m'\<close>
        have * : \<open>\<sigma> (Suc m') \<down> n = \<sigma> (Suc m') \<down> m' \<down> n\<close> by (simp add: \<open>n < m'\<close>)
        from \<open>m = Suc m'\<close> prems(1) have ** : \<open>x = m' - n\<close> by linarith
        show \<open>\<sigma> m \<down> n = \<sigma> n\<close>
          by (simp add: "*" "**" \<open>m = Suc m'\<close> \<open>n < m'\<close> hyp restriction restriction_chainD)
      qed
    qed
  qed
qed


lemma restricted_restriction_chain_is :
  \<open>restriction_chain \<sigma> \<Longrightarrow> (\<lambda>n. \<sigma> n \<down> n) = \<sigma>\<close>
  by (rule ext) (metis min.idem restriction_chainD restriction_restriction)

lemma restriction_chain_def_ter:
  \<open>restriction_chain \<sigma> \<longleftrightarrow> (\<forall>n m. n \<le> m \<longrightarrow> \<sigma> m \<down> n = \<sigma> n)\<close>
  by (metis le_eq_less_or_eq restricted_restriction_chain_is restriction_chain_def_bis)

lemma restriction_chain_restrictions : \<open>restriction_chain ((\<down>) x)\<close>
  by (simp add: restriction_chainI)

end



paragraph \<open>Iterations\<close>

text \<open>The sequence of restricted images of powers of a constructive function
      is a \<^const>\<open>restriction_chain\<close>.\<close>

context fixes f :: \<open>'a \<Rightarrow> 'a :: restriction_space\<close> begin

lemma restriction_chain_funpow_restricted [simp]:
  \<open>restriction_chain (\<lambda>n. (f ^^ n) x \<down> n)\<close> if \<open>constructive f\<close>
proof (rule restriction_chainI)
  show \<open>(f ^^ Suc n) x \<down> Suc n \<down> n = (f ^^ n) x \<down> n\<close> for n
  proof (induct n)
    show \<open>(f ^^ Suc 0) x \<down> Suc 0 \<down> 0 = (f ^^ 0) x \<down> 0\<close> by simp
  next
    fix n assume \<open>(f ^^ Suc n) x \<down> Suc n \<down> n = (f ^^ n) x \<down> n\<close>
    from \<open>constructive f\<close>[THEN constructiveD, OF this[simplified]]
    show \<open>(f ^^ Suc (Suc n)) x \<down> Suc (Suc n) \<down> Suc n = (f ^^ Suc n) x \<down> Suc n\<close> by simp
  qed
qed

lemma constructive_imp_eq_funpow_restricted :
  \<open>n \<le> k \<Longrightarrow> n \<le> l \<Longrightarrow> (f ^^ k) x \<down> n = (f ^^ l) y \<down> n\<close> if \<open>constructive f\<close>
proof (induct n arbitrary: k l)
  show \<open>(f ^^ k) x \<down> 0 = (f ^^ l) y \<down> 0\<close> for k l by simp
next
  fix n k l assume hyp : \<open>n \<le> k \<Longrightarrow> n \<le> l \<Longrightarrow> (f ^^ k) x \<down> n = (f ^^ l) y \<down> n\<close> for k l
  assume \<open>Suc n \<le> k\<close> \<open>Suc n \<le> l\<close>
  then obtain k' l' where \<open>k = Suc k'\<close> \<open>n \<le> k'\<close> \<open>l = Suc l'\<close> \<open>n \<le> l'\<close>
    by (metis Suc_le_D not_less_eq_eq)
  from \<open>constructive f\<close>[THEN constructiveD, OF hyp[OF \<open>n \<le> k'\<close> \<open>n \<le> l'\<close>]]
  show \<open>(f ^^ k) x \<down> Suc n = (f ^^ l) y \<down> Suc n\<close>
    by (simp add: \<open>k = Suc k'\<close> \<open>l = Suc l'\<close>)
qed

end



paragraph \<open>Limits and Convergence\<close>

context restriction begin

definition restriction_tendsto :: \<open>[nat \<Rightarrow> 'a, 'a] \<Rightarrow> bool\<close> (\<open>((_)/ \<midarrow>\<down>\<rightarrow> (_))\<close> [59, 59] 59)
  where \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<equiv> \<forall>n. \<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> k \<down> n\<close>

lemma restriction_tendstoI : \<open>(\<And>n. \<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> k \<down> n) \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  by (simp add: restriction_tendsto_def)

lemma restriction_tendstoD : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> k \<down> n\<close>
  by (simp add: restriction_tendsto_def) 

lemma restriction_tendstoE :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<And>n0. (\<And>k. n0 \<le> k \<Longrightarrow> \<Sigma> \<down> n = \<sigma> k \<down> n) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  using restriction_tendstoD by blast

end


lemma (in restriction_space) restriction_tendsto_unique :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>' \<Longrightarrow> \<Sigma> = \<Sigma>'\<close>
  by (metis ex_not_restriction_eq restriction_tendstoD nat_le_linear)


context restriction begin

lemma restriction_tendsto_const_restricted :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<lambda>n. \<sigma> n \<down> k) \<midarrow>\<down>\<rightarrow> \<Sigma> \<down> k\<close>
  unfolding restriction_tendsto_def by metis

lemma restriction_tendsto_iff_eventually_in_restriction_eq_set :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longleftrightarrow> (\<forall>n. \<exists>n0. \<forall>k\<ge>n0. n \<in> restriction_related_set \<Sigma> (\<sigma> k))\<close>
  by (simp add: restriction_tendsto_def)


lemma restriction_tendsto_const : \<open>(\<lambda>n. \<Sigma>) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  by (simp add: restriction_tendstoI)

lemma (in restriction_space) restriction_tendsto_restrictions : \<open>(\<lambda>n. \<Sigma> \<down> n) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  by (metis restriction_tendstoI restriction_chain_def_ter restriction_chain_restrictions)

lemma restriction_tendsto_shift_iff : \<open>(\<lambda>n. \<sigma> (n + l)) \<midarrow>\<down>\<rightarrow> \<Sigma> \<longleftrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
proof (rule iffI)
  show \<open>(\<lambda>n. \<sigma> (n + l)) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> if \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  proof (rule restriction_tendstoI)
    from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>[THEN restriction_tendstoD]
    show \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> (k + l) \<down> n\<close> for n by (meson trans_le_add1)
  qed
next
  show \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> if \<open>(\<lambda>n. \<sigma> (n + l)) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  proof (rule restriction_tendstoI)
    fix n
    from \<open>(\<lambda>n. \<sigma> (n + l)) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>[THEN restriction_tendstoD]
    obtain n0 where \<open>\<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> (k + l) \<down> n\<close> ..
    hence \<open>\<forall>k\<ge>n0 + l. \<Sigma> \<down> n = \<sigma> k \<down> n\<close>
      by (metis add.commute add_leD2 add_le_imp_le_left le_iff_add)
    thus \<open>\<exists>n1. \<forall>k\<ge>n1. \<Sigma> \<down> n = \<sigma> k \<down> n\<close> ..
  qed
qed


lemma restriction_tendsto_shiftI : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<lambda>n. \<sigma> (n + l)) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  by (simp add: restriction_tendsto_shift_iff)

lemma restriction_tendsto_shiftD : \<open>(\<lambda>n. \<sigma> (n + l)) \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  by (simp add: restriction_tendsto_shift_iff)


lemma (in restriction_space) restriction_tendsto_restricted_iff_restriction_tendsto :
  \<open>(\<lambda>n. \<sigma> n \<down> n) \<midarrow>\<down>\<rightarrow> \<Sigma> \<longleftrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
proof (rule iffI)
  assume * : \<open>(\<lambda>n. \<sigma> n \<down> n) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  show \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  proof (rule restriction_tendstoI)
    fix n
    from "*" restriction_tendstoE obtain n0 where \<open>n0 \<le> k \<Longrightarrow> \<Sigma> \<down> n = \<sigma> k \<down> k \<down> n\<close> for k by blast
    hence \<open>max n0 n \<le> k \<Longrightarrow> \<Sigma> \<down> n = \<sigma> k \<down> n\<close> for k by auto
    thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> k \<down> n\<close> by blast
  qed
next
  assume * : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  show \<open>(\<lambda>n. \<sigma> n \<down> n) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  proof (rule restriction_tendstoI)
    fix n
    from "*" restriction_tendstoE obtain n0 where \<open>n0 \<le> k \<Longrightarrow> \<Sigma> \<down> n = \<sigma> k \<down> n\<close> for k by blast
    hence \<open>max n0 n \<le> k \<Longrightarrow> \<Sigma> \<down> n = \<sigma> k \<down> k \<down> n\<close> for k by auto
    thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> k \<down> k \<down> n\<close> by blast
  qed
qed

lemma restriction_tendsto_subseq :
  \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> if \<open>strict_mono f\<close> and \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
proof (rule restriction_tendstoI)
  fix n
  have \<open>n \<le> f n\<close> by (simp add: strict_mono_imp_increasing \<open>strict_mono f\<close>)
  moreover from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> restriction_tendstoE obtain n0 where \<open>n0 \<le> k \<Longrightarrow> \<Sigma> \<down> n = \<sigma> k \<down> n\<close> for k by blast
  ultimately have \<open>\<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> (f k) \<down> n\<close>
    by (metis le_trans strict_mono_imp_increasing that(1))
  thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = (\<sigma> \<circ> f) k \<down> n\<close> by auto
qed

end


context restriction begin

definition restriction_convergent :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> bool\<close> (\<open>convergent\<^sub>\<down>\<close>)
  where \<open>restriction_convergent \<sigma> \<equiv> \<exists>\<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>

lemma restriction_convergentI : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> restriction_convergent \<sigma>\<close>
  by (auto simp add: restriction_convergent_def)

lemma restriction_convergentD' : \<open>restriction_convergent \<sigma> \<Longrightarrow> \<exists>\<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  by (simp add: restriction_convergent_def)

end


context restriction_space begin

lemma restriction_convergentD :
  \<open>restriction_convergent \<sigma> \<Longrightarrow> \<exists>!\<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  unfolding restriction_convergent_def using restriction_tendsto_unique by blast

lemma restriction_convergentE : 
  \<open>restriction_convergent \<sigma> \<Longrightarrow>
   (\<And>\<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<And>\<Sigma>'. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>' \<Longrightarrow> \<Sigma>' = \<Sigma>) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  using restriction_convergentD by blast

lemma restriction_tendsto_of_restriction_convergent :
  \<open>restriction_convergent \<sigma> \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> (THE \<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close>
  by (simp add: restriction_convergentD the1I2)

end



context restriction begin

lemma restriction_convergent_const [simp] : \<open>convergent\<^sub>\<down> (\<lambda>n. \<Sigma>)\<close>
  unfolding restriction_convergent_def restriction_tendsto_def by blast

lemma (in restriction_space) restriction_convergent_restrictions [simp] :
  \<open>convergent\<^sub>\<down> (\<lambda>n. \<Sigma> \<down> n)\<close>
  using restriction_convergent_def restriction_tendsto_restrictions by blast

lemma restriction_convergent_shift_iff :
  \<open>convergent\<^sub>\<down> (\<lambda>n. \<sigma> (n + l)) \<longleftrightarrow> convergent\<^sub>\<down> \<sigma>\<close>
  by (simp add: restriction_convergent_def restriction_tendsto_shift_iff)


lemma restriction_convergent_shift_shiftI :
  \<open>convergent\<^sub>\<down> \<sigma> \<Longrightarrow> convergent\<^sub>\<down> (\<lambda>n. \<sigma> (n + l))\<close>
  by (simp add: restriction_convergent_shift_iff)

lemma restriction_convergent_shift_shiftD :
  \<open>convergent\<^sub>\<down> (\<lambda>n. \<sigma> (n + l)) \<Longrightarrow> convergent\<^sub>\<down> \<sigma>\<close>
  by (simp add: restriction_convergent_shift_iff)


lemma (in restriction_space) restriction_convergent_restricted_iff_restriction_convergent :
  \<open>convergent\<^sub>\<down> (\<lambda>n. \<sigma> n \<down> n) \<longleftrightarrow> convergent\<^sub>\<down> \<sigma>\<close>
  by (simp add: restriction_convergent_def
      restriction_tendsto_restricted_iff_restriction_tendsto)


lemma restriction_convergent_subseq :
  \<open>strict_mono f \<Longrightarrow> restriction_convergent \<sigma> \<Longrightarrow> restriction_convergent (\<sigma> \<circ> f)\<close>
  unfolding restriction_convergent_def using restriction_tendsto_subseq by blast

lemma (in restriction_space)
  convergent_restriction_chain_imp_ex1 : \<open>\<exists>!\<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n\<close>
  and restriction_tendsto_of_convergent_restriction_chain : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> (THE \<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n)\<close>
  if \<open>restriction_convergent \<sigma>\<close> and \<open>restriction_chain \<sigma>\<close>
proof -
  from \<open>restriction_convergent \<sigma>\<close> restriction_convergentE obtain \<Sigma>
    where \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>\<And>\<Sigma>'. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>' \<Longrightarrow> \<Sigma>' = \<Sigma>\<close> by blast

  have * : \<open>\<Sigma> \<down> n = \<sigma> n\<close> for n
  proof -
    from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> restriction_tendstoE obtain n0 where \<open>n0 \<le> k \<Longrightarrow> \<Sigma> \<down> n = \<sigma> k \<down> n\<close> for k by blast
    hence \<open>\<Sigma> \<down> n = \<sigma> (max n0 n) \<down> n\<close> by simp
    thus \<open>\<Sigma> \<down> n = \<sigma> n\<close>
      by (simp add: restriction_chain_def_ter[THEN iffD1, OF \<open>restriction_chain \<sigma>\<close>])
  qed
  have ** : \<open>\<forall>n. \<Sigma>' \<down> n = \<sigma> n \<Longrightarrow> \<Sigma>' = \<Sigma>\<close> for \<Sigma>'
    by (metis "*" ex_not_restriction_eq)
  from "*" "**" show \<open>\<exists>!\<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n\<close> by blast
  from theI'[OF this] "**" have \<open>\<Sigma> = (THE \<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n)\<close> by simp
  with \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> show \<open>\<sigma> \<midarrow>\<down>\<rightarrow> (THE \<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n)\<close> by simp
qed

end



subsubsection \<open>Fixed-Point Operator\<close>

text \<open>Our definition only makes sense if such a fixed point exists and is unique.
      We will therefore directly add a completeness assumption,
      and define the fixed-point operator within this context.
      It will only be valid when the function \<^term>\<open>f\<close> is \<^const>\<open>constructive\<close>.\<close>

class complete_restriction_space = restriction_space +
  assumes restriction_chain_imp_restriction_convergent : \<open>chain\<^sub>\<down> \<sigma> \<Longrightarrow> convergent\<^sub>\<down> \<sigma>\<close>

definition (in complete_restriction_space)
  restriction_fix :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> 'a\<close> (* (binder \<open>\<upsilon> \<close> 10) *)
  \<comment> \<open>We will use a syntax rather than a binder to be compatible with the product.\<close>
  where \<open>restriction_fix (\<lambda>x. f x) \<equiv> THE \<Sigma>. (\<lambda>n. (f ^^ n) undefined) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>

syntax "_restriction_fix" :: \<open>[pttrn, 'a \<Rightarrow> 'a] \<Rightarrow> 'a\<close>
  (\<open>(\<open>indent=3 notation=\<open>binder restriction_fix\<close>\<close>\<upsilon> _./ _)\<close> [0, 10] 10)
syntax_consts "_restriction_fix" \<rightleftharpoons> restriction_fix
translations "\<upsilon> x. f" \<rightleftharpoons> "CONST restriction_fix (\<lambda>x. f)"
print_translation \<open>
  [(\<^const_syntax>\<open>restriction_fix\<close>, fn ctxt => fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' ctxt abs
      in Syntax.const \<^syntax_const>\<open>_restriction_fix\<close> $ x $ t end)]
\<close>  \<comment> \<open>To avoid eta-contraction of body\<close>


context complete_restriction_space begin

text \<open>The following result is quite similar to the Banach's fixed point theorem.\<close>

lemma restriction_chain_imp_ex1 : \<open>\<exists>!\<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n\<close>
  and restriction_tendsto_of_restriction_chain : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> (THE \<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n)\<close>
  if \<open>restriction_chain \<sigma>\<close>
  by (simp_all add: convergent_restriction_chain_imp_ex1
      restriction_tendsto_of_convergent_restriction_chain
      restriction_chain_imp_restriction_convergent \<open>restriction_chain \<sigma>\<close>)



lemma restriction_chain_is :
  \<open>\<sigma> = (\<down>) (THE \<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close>
  \<open>\<sigma> = (\<down>) (THE \<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n)\<close> if \<open>restriction_chain \<sigma>\<close>
proof -
  from restriction_tendsto_of_restriction_chain[OF \<open>restriction_chain \<sigma>\<close>]
  have \<open>\<sigma> \<midarrow>\<down>\<rightarrow> (THE \<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n)\<close> .
  with restriction_tendsto_of_restriction_convergent
    restriction_convergentI restriction_tendsto_unique
  have * : \<open>(THE \<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n) = (THE \<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close> by blast

  from theI'[OF restriction_chain_imp_ex1, OF \<open>restriction_chain \<sigma>\<close>]
  show \<open>\<sigma> = (\<down>) (THE \<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n)\<close> by (intro ext) simp
  with "*" show \<open>\<sigma> = (\<down>) (THE \<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close> by auto
qed

end


context 
  fixes f :: \<open>'a \<Rightarrow> 'a :: complete_restriction_space\<close>
  assumes \<open>constructive f\<close>
begin

lemma ex1_restriction_fix :
  \<open>\<exists>!\<Sigma>. \<forall>x. (\<lambda>n. (f ^^ n) x) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
proof -
  let ?\<sigma> = \<open>\<lambda>x n. (f ^^ n) x \<down> n\<close>
  from constructive_imp_eq_funpow_restricted[OF \<open>constructive f\<close>]
  have \<open>?\<sigma> x = ?\<sigma> y\<close> for x y by blast
  moreover have \<open>restriction_chain (?\<sigma> x)\<close> for x by (simp add: \<open>constructive f\<close>)
  ultimately obtain \<Sigma> where \<open>\<forall>x. ?\<sigma> x \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
    by (metis (full_types) restriction_chain_is(1) restriction_tendsto_restrictions)
  with restriction_tendsto_unique have \<open>\<exists>!\<Sigma>. \<forall>x. ?\<sigma> x \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
  thus \<open>\<exists>!\<Sigma>. \<forall>x. (\<lambda>n. (f ^^ n) x) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
    by (simp add: restriction_tendsto_restricted_iff_restriction_tendsto)
qed

lemma ex1_restriction_fix_bis :
  \<open>\<exists>!\<Sigma>. (\<lambda>n. (f ^^ n) x) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  using ex1_restriction_fix restriction_tendsto_unique by blast


lemma restriction_fix_def_bis :
  \<open>(\<upsilon> x. f x) = (THE \<Sigma>. (\<lambda>n. (f ^^ n) x) \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close>
proof -
  have \<open>(\<lambda>\<Sigma>. (\<lambda>n. (f ^^ n) undefined) \<midarrow>\<down>\<rightarrow> \<Sigma>) = (\<lambda>\<Sigma>. (\<lambda>n. (f ^^ n) x) \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close>
    by (metis ex1_restriction_fix restriction_tendsto_unique)
  from arg_cong[where f = The, OF this, folded restriction_fix_def]
  show \<open>(\<upsilon> x. f x) = (THE \<Sigma>. (\<lambda>n. (f ^^ n) x) \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close> .
qed


lemma funpow_restriction_tendsto_restriction_fix : \<open>(\<lambda>n. (f ^^ n) x) \<midarrow>\<down>\<rightarrow> (\<upsilon> x. f x)\<close>
  by (metis ex1_restriction_fix restriction_convergentI
      restriction_fix_def_bis restriction_tendsto_of_restriction_convergent)


lemma restriction_restriction_fix_is : \<open>(\<upsilon> x. f x) \<down> n = (f ^^ n) x \<down> n\<close>
proof (rule restriction_tendsto_unique)
  from funpow_restriction_tendsto_restriction_fix
  show \<open>(\<lambda>k. (f ^^ k) x \<down> n) \<midarrow>\<down>\<rightarrow> (\<upsilon> x. f x) \<down> n\<close>
    by (simp add: restriction_tendsto_def)
next
  from restriction_tendsto_restrictions
  have \<open>(\<lambda>k. (f ^^ n) x \<down> n \<down> k) \<midarrow>\<down>\<rightarrow> (f ^^ n) x \<down> n\<close> .
  then obtain n0 where * : \<open>\<forall>k\<ge>n0. (f ^^ n) x \<down> n = (f ^^ n) x \<down> n \<down> k\<close>
    by (metis restriction_restriction min_def)
  show \<open>(\<lambda>k. (f ^^ k) x \<down> n) \<midarrow>\<down>\<rightarrow> (f ^^ n) x \<down> n\<close>
  proof (rule restriction_tendstoI)
    fix m
    from * have \<open>\<forall>k\<ge>n + n0 + m. (f ^^ n) x \<down> n \<down> m = (f ^^ k) x \<down> n \<down> m\<close>
      by (simp add: \<open>constructive f\<close> constructive_imp_eq_funpow_restricted)
    thus \<open>\<exists>n0. \<forall>k\<ge>n0. (f ^^ n) x \<down> n \<down> m = (f ^^ k) x \<down> n \<down> m\<close> ..
  qed
qed


lemma restriction_fix_eq : \<open>(\<upsilon> x. f x) = f (\<upsilon> x. f x)\<close>
proof (subst restriction_fix_def, intro the1_equality restriction_tendstoI)
  show \<open>\<exists>!\<Sigma>. (\<lambda>n. (f ^^ n) undefined) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
    by (simp add: ex1_restriction_fix_bis)
next
  have \<open>n \<le> k \<Longrightarrow> f (restriction_fix f) \<down> n = (f ^^ k) undefined \<down> n\<close> for n k
    by (cases n, simp, cases k, simp_all)
      (meson \<open>constructive f\<close>[THEN constructiveD] restriction_related_le
        restriction_restriction_fix_is)
  thus \<open>\<exists>n0. \<forall>k\<ge>n0. f (restriction_fix f) \<down> n = (f ^^ k) undefined \<down> n\<close> for n by blast
qed


lemma restriction_fix_unique : \<open>f x = x \<Longrightarrow> (\<upsilon> x. f x) = x\<close>
  by (metis (no_types, opaque_lifting) restriction_fix_eq \<open>constructive f\<close>
      constructiveD dual_order.refl take_lemma_restriction)


lemma restriction_fix_def_ter : \<open>(\<upsilon> x. f x) = (THE x. f x = x)\<close>
  by (metis (mono_tags, lifting) restriction_fix_eq restriction_fix_unique the_equality)




end



(*<*)
end
  (*>*)

