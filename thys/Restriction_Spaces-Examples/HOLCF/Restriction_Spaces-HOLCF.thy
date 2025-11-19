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

(*<*)
theory "Restriction_Spaces-HOLCF"
  imports HOLCF Restriction_Spaces
begin

default_sort type
  (*>*)


section \<open>Definitions\<close>

interpretation belowRS : Restriction \<open>(\<down>)\<close> \<open>(\<sqsubseteq>)\<close> by unfold_locales
    \<comment> \<open>Just to recover \<^const>\<open>belowRS.restriction_related_set\<close> and
   \<^const>\<open>belowRS.restriction_not_related_set\<close>.\<close>

class po_restriction_space = restriction + po +
  assumes restriction_0_below [simp] : \<open>x \<down> 0 \<sqsubseteq> y \<down> 0\<close>
    and mono_restriction_below     : \<open>x \<sqsubseteq> y \<Longrightarrow> x \<down> n \<sqsubseteq> y \<down> n\<close>
    and ex_not_restriction_below   : \<open>\<not> x \<sqsubseteq> y \<Longrightarrow> \<exists>n. \<not> x \<down> n \<sqsubseteq> y \<down> n\<close>

interpretation belowRS : PreorderRestrictionSpace \<open>(\<down>) :: 'a \<Rightarrow> nat \<Rightarrow> 'a :: po_restriction_space\<close> \<open>(\<sqsubseteq>)\<close>
proof unfold_locales
  show \<open>x \<down> 0 \<sqsubseteq> y \<down> 0\<close> for x y :: 'a by simp
next
  show \<open>x \<sqsubseteq> y \<Longrightarrow> x \<down> n \<sqsubseteq> y \<down> n\<close> for x y :: 'a and n
    by (fact mono_restriction_below)
next
  show \<open>\<not> x \<sqsubseteq> y \<Longrightarrow> \<exists>n. \<not> x \<down> n \<sqsubseteq> y \<down> n\<close> for x y :: 'a
    by (simp add: ex_not_restriction_below)
next
  show \<open>x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z\<close> for x y z :: 'a by (fact below_trans)
qed


subclass (in po_restriction_space) restriction_space
proof unfold_locales
  show \<open>x \<down> 0 = y \<down> 0\<close> for x y :: 'a by (rule below_antisym) simp_all
next
  show \<open>x \<noteq> y \<Longrightarrow> \<exists>n. x \<down> n \<noteq> y \<down> n\<close> for x y :: 'a
    by (metis ex_not_restriction_below po_eq_conv)
qed




class cpo_restriction_space = po_restriction_space +
  assumes cpo : \<open>chain S \<Longrightarrow> \<exists>x. range S <<| x\<close>


subclass (in cpo_restriction_space) cpo
  by unfold_locales (fact cpo)


class pcpo_restriction_space = cpo_restriction_space +
  assumes least : \<open>\<exists>x. \<forall>y. x \<sqsubseteq> y\<close>

subclass (in pcpo_restriction_space) pcpo
  by unfold_locales (fact least)


interpretation belowRS : Restriction_2_PreorderRestrictionSpace
  \<open>(\<down>) :: 'a :: {restriction, below} \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(\<sqsubseteq>)\<close>
  \<open>(\<down>) :: 'b :: po_restriction_space \<Rightarrow> nat \<Rightarrow> 'b\<close> \<open>(\<sqsubseteq>)\<close> ..

text \<open>With this we recover constants like \<^const>\<open>less_eqRS.restriction_shift_on\<close>.\<close>

interpretation belowRS : PreorderRestrictionSpace_2_PreorderRestrictionSpace
  \<open>(\<down>) :: 'a :: po_restriction_space \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(\<sqsubseteq>)\<close>
  \<open>(\<down>) :: 'b :: po_restriction_space \<Rightarrow> nat \<Rightarrow> 'b\<close> \<open>(\<sqsubseteq>)\<close> ..

text \<open>With that we recover theorems like @{thm belowRS.constructive_restriction_restriction}.\<close>

interpretation belowRS : Restriction_2_PreorderRestrictionSpace_2_PreorderRestrictionSpace
  \<open>(\<down>) :: 'a :: {restriction, below} \<Rightarrow> nat \<Rightarrow> 'a\<close> \<open>(\<sqsubseteq>)\<close>
  \<open>(\<down>) :: 'b :: po_restriction_space \<Rightarrow> nat \<Rightarrow> 'b\<close> \<open>(\<sqsubseteq>)\<close>
  \<open>(\<down>) :: 'c :: po_restriction_space \<Rightarrow> nat \<Rightarrow> 'c\<close> \<open>(\<sqsubseteq>)\<close>..

text \<open>And with that we recover theorems like @{thm less_eqRS.constructive_on_comp_non_destructive_on}.\<close>



context fixes f :: \<open>'a :: restriction \<Rightarrow> 'b :: po_restriction_space\<close> begin
text \<open>From @{thm below_antisym} we can obtain stronger lemmas.\<close>

corollary below_restriction_shift_onI :
  \<open>(\<And>x y n. \<lbrakk>x \<in> A; y \<in> A; f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow>
             f x \<down> nat (int n + k) \<sqsubseteq> f y \<down> nat (int n + k))
   \<Longrightarrow> restriction_shift_on f k A\<close>
  by (simp add: below_antisym restriction_shift_onI)

corollary below_restriction_shiftI :
  \<open>(\<And>x y n. \<lbrakk>f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow>
             f x \<down> nat (int n + k) \<sqsubseteq> f y \<down> nat (int n + k))
   \<Longrightarrow> restriction_shift f k\<close>
  by (simp add: below_antisym restriction_shiftI)

corollary below_non_too_destructive_onI :
  \<open>(\<And>x y n. \<lbrakk>x \<in> A; y \<in> A; f x \<noteq> f y; x \<down> Suc n = y \<down> Suc n\<rbrakk> \<Longrightarrow>
             f x \<down> n \<sqsubseteq> f y \<down> n)
   \<Longrightarrow> non_too_destructive_on f A\<close>
  by (simp add: below_antisym non_too_destructive_onI)

corollary below_non_too_destructiveI :
  \<open>(\<And>x y n. \<lbrakk>f x \<noteq> f y; x \<down> Suc n = y \<down> Suc n\<rbrakk> \<Longrightarrow> f x \<down> n \<sqsubseteq> f y \<down> n)
   \<Longrightarrow> non_too_destructive f\<close>
  by (simp add: below_antisym non_too_destructiveI)

corollary below_non_destructive_onI :
  \<open>(\<And>x y n. \<lbrakk>n \<noteq> 0; x \<in> A; y \<in> A; f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow> f x \<down> n \<sqsubseteq> f y \<down> n)
   \<Longrightarrow> non_destructive_on f A\<close>
  by (simp add: below_antisym non_destructive_onI)

corollary below_non_destructiveI :
  \<open>(\<And>x y n. \<lbrakk>n \<noteq> 0; f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow> f x \<down> n \<sqsubseteq> f y \<down> n)
   \<Longrightarrow> non_destructive f\<close>
  by (simp add: below_antisym non_destructiveI)

corollary below_constructive_onI :
  \<open>(\<And>x y n. \<lbrakk>x \<in> A; y \<in> A; f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow> f x \<down> Suc n \<sqsubseteq> f y \<down> Suc n)
   \<Longrightarrow> constructive_on f A\<close>
  by (simp add: below_antisym constructive_onI)

corollary below_constructiveI :
  \<open>(\<And>x y n. \<lbrakk>f x \<noteq> f y; x \<down> n = y \<down> n\<rbrakk> \<Longrightarrow> f x \<down> Suc n \<sqsubseteq> f y \<down> Suc n)
   \<Longrightarrow> constructive f\<close>
  by (simp add: below_antisym constructiveI)

end



section \<open>Equality of Fixed-Point Operators\<close>

lemma restriction_fix_is_fix :
  \<open>(\<upsilon> X. f X) = (\<mu> X. f X)\<close> if \<open>cont f\<close> \<open>constructive f\<close>
for f :: \<open>'a :: {pcpo_restriction_space, complete_restriction_space} \<Rightarrow> 'a\<close>
proof (rule restriction_fix_unique)
  show \<open>constructive f\<close> by (fact \<open>constructive f\<close>)
next
  show \<open>f (\<mu> x. f x) = (\<mu> x. f x)\<close> by (metis def_cont_fix_eq \<open>cont f\<close>)
qed



section \<open>Product\<close>

instance prod :: (po_restriction_space, po_restriction_space) po_restriction_space
proof intro_classes
  show \<open>p \<down> 0 \<sqsubseteq> q \<down> 0\<close> for p q :: \<open>'a \<times> 'b\<close>
    by (metis below_refl restriction_0_related)
next
  show \<open>p \<sqsubseteq> q \<Longrightarrow> p \<down> n \<sqsubseteq> q \<down> n\<close> for p q :: \<open>'a \<times> 'b\<close> and n
    by (simp add: below_prod_def restriction_prod_def mono_restriction_below)
next
  show \<open>\<not> p \<sqsubseteq> q \<Longrightarrow> \<exists>n. \<not> p \<down> n \<sqsubseteq> q \<down> n\<close> for p q :: \<open>'a \<times> 'b\<close>
    by (simp add: below_prod_def restriction_prod_def)
      (metis ex_not_restriction_below)
qed


instance prod :: (cpo_restriction_space, cpo_restriction_space) cpo_restriction_space
  using is_lub_prod by intro_classes blast

instance prod :: (pcpo_restriction_space, pcpo_restriction_space) pcpo_restriction_space
  by (intro_classes) (simp add: pcpo_class.least)


section \<open>Functions\<close>

instance \<open>fun\<close> :: (type, po_restriction_space) po_restriction_space
proof intro_classes
  show \<open>f \<down> 0 \<sqsubseteq> g \<down> 0\<close> for f g :: \<open>'a \<Rightarrow> 'b\<close>
    by (metis below_refl restriction_0_related)
next
  show \<open>f \<sqsubseteq> g \<Longrightarrow> f \<down> n \<sqsubseteq> g \<down> n\<close> for f g :: \<open>'a \<Rightarrow> 'b\<close> and n
    by (simp add: fun_below_iff mono_restriction_below restriction_fun_def)
next
  show \<open>\<not> f \<sqsubseteq> g \<Longrightarrow> \<exists>n. \<not> f \<down> n \<sqsubseteq> g \<down> n\<close> for f g :: \<open>'a \<Rightarrow> 'b\<close>
    by (metis belowRS.all_ge_restriction_related_iff_related fun_below_iff restriction_fun_def)
qed

instance \<open>fun\<close> :: (type, cpo_restriction_space) cpo_restriction_space
  by intro_classes (simp add: cpo_class.cpo)

instance \<open>fun\<close> :: (type, pcpo_restriction_space) pcpo_restriction_space
  by intro_classes (simp add: pcpo_class.least)


(*<*)
end
  (*>*)