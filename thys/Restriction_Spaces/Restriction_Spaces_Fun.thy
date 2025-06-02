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


section \<open>Functions towards a Restriction Space\<close>

subsection \<open>Restriction Space\<close>

(*<*)
theory Restriction_Spaces_Fun
  imports Restriction_Spaces_Classes
begin
  (*>*)

instantiation \<open>fun\<close> :: (type, restriction) restriction
begin

definition restriction_fun :: \<open>['a \<Rightarrow> 'b, nat, 'a] \<Rightarrow> 'b\<close>
  where \<open>f \<down> n \<equiv> (\<lambda>x. f x \<down> n)\<close>

instance by intro_classes (simp add: restriction_fun_def)

end 


instance \<open>fun\<close> :: (type, restriction_space) restriction_space
proof (intro_classes, unfold restriction_fun_def)
  show \<open>(\<lambda>x. f x \<down> 0) = (\<lambda>x. g x \<down> 0)\<close>
    for f g :: \<open>'a \<Rightarrow> 'b\<close> by (rule ext) simp
next
  fix f g :: \<open>'a \<Rightarrow> 'b\<close> assume \<open>f \<noteq> g\<close>
  then obtain x where \<open>f x \<noteq> g x\<close> by fast
  with ex_not_restriction_related obtain n
    where \<open>f x \<down> n \<noteq> g x \<down> n\<close> by blast
  hence \<open>(\<lambda>x. f x \<down> n) \<noteq> (\<lambda>x. g x \<down> n)\<close> by meson
  thus \<open>\<exists>n. (\<lambda>x. f x \<down> n) \<noteq> (\<lambda>x. g x \<down> n)\<close> ..
qed


instance \<open>fun\<close> :: (type, preorder_restriction_space) preorder_restriction_space
proof intro_classes
  show \<open>f \<down> 0 \<le> g \<down> 0\<close> for f g :: \<open>'a \<Rightarrow> 'b\<close>
    by (simp add: le_fun_def restriction_fun_def)
next
  show \<open>f \<le> g \<Longrightarrow> f \<down> n \<le> g \<down> n\<close> for f g :: \<open>'a \<Rightarrow> 'b\<close> and n
    by (simp add: restriction_fun_def le_fun_def mono_restriction_less_eq)
next
  show \<open>\<not> f \<le> g \<Longrightarrow> \<exists>n. \<not> f \<down> n \<le> g \<down> n\<close> for f g :: \<open>'a \<Rightarrow> 'b\<close>
    by (metis ex_not_restriction_less_eq le_funD le_funI restriction_fun_def)
qed

instance \<open>fun\<close> :: (type, order_restriction_space) order_restriction_space ..




subsection \<open>Restriction shift Maps\<close>

lemma restriction_shift_on_fun_iff :
  \<open>restriction_shift_on f k A \<longleftrightarrow> (\<forall>z. restriction_shift_on (\<lambda>x. f x z) k A)\<close>
proof (intro iffI allI)
  show \<open>restriction_shift_on (\<lambda>x. f x z) k A\<close> if \<open>restriction_shift_on f k A\<close> for z
  proof (rule restriction_shift_onI)
    fix x y n assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<down> n = y \<down> n\<close>
    from restriction_shift_onD[OF \<open>restriction_shift_on f k A\<close> this]
    show \<open>f x z \<down> nat (int n + k) = f y z \<down> nat (int n + k)\<close>
      by (unfold restriction_fun_def) (blast dest!: fun_cong)
  qed
next
  show \<open>restriction_shift_on f k A\<close> if \<open>\<forall>z. restriction_shift_on (\<lambda>x. f x z) k A\<close>
  proof (rule restriction_shift_onI)
    fix x y n assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<down> n = y \<down> n\<close>
    with \<open>\<forall>z. restriction_shift_on (\<lambda>x. f x z) k A\<close> restriction_shift_onD
    have \<open>f x z \<down> nat (int n + k) = f y z \<down> nat (int n + k)\<close> for z by blast
    thus \<open>f x \<down> nat (int n + k) = f y \<down> nat (int n + k)\<close>
      by (simp add: restriction_fun_def)
  qed
qed

lemma restriction_shift_fun_iff : \<open>restriction_shift f k \<longleftrightarrow> (\<forall>z. restriction_shift (\<lambda>x. f x z) k)\<close>
  by (unfold restriction_shift_def, fact restriction_shift_on_fun_iff)


lemma non_too_destructive_on_fun_iff:
  \<open>non_too_destructive_on f A \<longleftrightarrow> (\<forall>z. non_too_destructive_on (\<lambda>x. f x z) A)\<close>
  by (simp add: non_too_destructive_on_def restriction_shift_on_fun_iff)

lemma non_too_destructive_fun_iff:
  \<open>non_too_destructive f \<longleftrightarrow> (\<forall>z. non_too_destructive (\<lambda>x. f x z))\<close>
  by (unfold restriction_shift_def non_too_destructive_def)
    (fact non_too_destructive_on_fun_iff)


lemma non_destructive_on_fun_iff:
  \<open>non_destructive_on f A \<longleftrightarrow> (\<forall>z. non_destructive_on (\<lambda>x. f x z) A)\<close>
  by (simp add: non_destructive_on_def restriction_shift_on_fun_iff)

lemma non_destructive_fun_iff:
  \<open>non_destructive f \<longleftrightarrow> (\<forall>z. non_destructive (\<lambda>x. f x z))\<close>
  unfolding non_destructive_def by (fact non_destructive_on_fun_iff)


lemma constructive_on_fun_iff:
  \<open>constructive_on f A \<longleftrightarrow> (\<forall>z. constructive_on (\<lambda>x. f x z) A)\<close>
  by (simp add: constructive_on_def restriction_shift_on_fun_iff)

lemma constructive_fun_iff:
  \<open>constructive f \<longleftrightarrow> (\<forall>z. constructive (\<lambda>x. f x z))\<close>
  unfolding constructive_def by (fact constructive_on_fun_iff)



lemma restriction_shift_fun [restriction_shift_simpset, restriction_shift_introset] :
  \<open>(\<And>z. restriction_shift (\<lambda>x. f x z) k) \<Longrightarrow> restriction_shift f k\<close>
  and non_too_destructive_fun [restriction_shift_simpset, restriction_shift_introset] :
  \<open>(\<And>z. non_too_destructive (\<lambda>x. f x z)) \<Longrightarrow> non_too_destructive f\<close>
  and non_destructive_fun [restriction_shift_simpset, restriction_shift_introset] :
  \<open>(\<And>z. non_destructive (\<lambda>x. f x z)) \<Longrightarrow> non_destructive f\<close>
  and constructive_fun [restriction_shift_simpset, restriction_shift_introset] :
  \<open>(\<And>z. constructive (\<lambda>x. f x z)) \<Longrightarrow> constructive f\<close>
  by (simp_all add: restriction_shift_fun_iff non_too_destructive_fun_iff
      non_destructive_fun_iff constructive_fun_iff)



subsection \<open>Limits and Convergence\<close>

lemma reached_dist_funE :
  fixes f g :: \<open>'a \<Rightarrow> 'b :: restriction_space\<close> assumes \<open>f \<noteq> g\<close>
  obtains x where \<open>f x \<noteq> g x\<close> \<open>Sup (restriction_related_set f g) = Sup (restriction_related_set (f x) (g x))\<close>
    \<comment>\<open>Morally, we say here that the distance between two functions is reached.
   But we did not introduce the concept of distance.\<close>
proof -
  let ?n = \<open>Sup (restriction_related_set f g)\<close>
  from Sup_in_restriction_related_set[OF \<open>f \<noteq> g\<close>]
  have \<open>?n \<in> restriction_related_set f g\<close> .
  with restriction_related_le have \<open>\<forall>m\<le>?n. f \<down> m = g \<down> m\<close> by blast
  moreover have \<open>f \<down> Suc ?n \<noteq> g \<down> Suc ?n\<close>
    using cSup_upper[OF _ bdd_above_restriction_related_set_iff[THEN iffD2, OF \<open>f \<noteq> g\<close>], of \<open>Suc ?n\<close>]
    by (metis (mono_tags, lifting) dual_order.refl mem_Collect_eq not_less_eq_eq restriction_related_le)
  ultimately obtain x where * : \<open>\<forall>m\<le>?n. f x \<down> m = g x \<down> m\<close> \<open>f x \<down> Suc ?n \<noteq> g x \<down> Suc ?n\<close>
    unfolding restriction_fun_def by meson
  from "*"(2) have \<open>f x \<noteq> g x\<close> by auto
  moreover from "*" have \<open>?n = Sup (restriction_related_set (f x) (g x))\<close>
    by (metis (no_types, lifting) \<open>\<forall>m\<le>?n. f \<down> m = g \<down> m\<close>
        \<open>f \<down> Suc ?n \<noteq> g \<down> Suc ?n\<close> not_less_eq_eq restriction_related_le)
  ultimately show thesis using that by blast
qed


lemma reached_restriction_related_set_funE : 
  fixes f g :: \<open>'a \<Rightarrow> 'b :: restriction_space\<close>
  obtains x where \<open>restriction_related_set f g = restriction_related_set (f x) (g x)\<close>
proof (cases \<open>f = g\<close>)
  from that show \<open>f = g \<Longrightarrow> thesis\<close> by simp
next
  from that show \<open>f \<noteq> g \<Longrightarrow> thesis\<close>
    by (elim reached_dist_funE) (metis (full_types) restriction_related_set_is_atMost)
qed



lemma restriction_chain_fun_iff :
  \<open>restriction_chain \<sigma> \<longleftrightarrow> (\<forall>z. restriction_chain (\<lambda>n. \<sigma> n z))\<close>
proof (intro iffI allI)
  show \<open>restriction_chain \<sigma> \<Longrightarrow> restriction_chain (\<lambda>n. \<sigma> n z)\<close> for z
    by (auto simp add: restriction_chain_def restriction_fun_def dest!: fun_cong)
next
  show \<open>\<forall>z. restriction_chain (\<lambda>n. \<sigma> n z) \<Longrightarrow> restriction_chain \<sigma>\<close>
    by (simp add: restriction_chain_def restriction_fun_def)
qed



lemma restriction_tendsto_fun_imp : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<lambda>n. \<sigma> n z) \<midarrow>\<down>\<rightarrow> \<Sigma> z\<close>
  by (simp add: restriction_tendsto_def restriction_fun_def) meson


lemma restriction_convergent_fun_imp :
  \<open>restriction_convergent \<sigma> \<Longrightarrow> restriction_convergent (\<lambda>n. \<sigma> n z)\<close>
  by (metis restriction_convergent_def restriction_tendsto_fun_imp)


subsection \<open>Completeness\<close>

instance \<open>fun\<close> :: (type, complete_restriction_space) complete_restriction_space
proof intro_classes
  fix \<sigma> :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'b :: complete_restriction_space\<close>
  assume \<open>restriction_chain \<sigma>\<close>
  hence * : \<open>restriction_chain (\<lambda>n. \<sigma> n x)\<close> for x
    by (simp add: restriction_chain_fun_iff)
  from restriction_chain_imp_restriction_convergent[OF this]
  have ** : \<open>restriction_convergent (\<lambda>n. \<sigma> n x)\<close> for x .
  then obtain \<Sigma> where *** : \<open>(\<lambda>n. \<sigma> n x) \<midarrow>\<down>\<rightarrow> \<Sigma> x\<close> for x
    by (meson restriction_convergent_def)
  from "*" have **** : \<open>(\<lambda>n. \<sigma> n x \<down> n) = (\<lambda>n. \<sigma> n x)\<close> for x
    by (simp add: restricted_restriction_chain_is)
  have \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  proof (rule restriction_tendstoI)
    fix n
    have \<open>\<forall>k\<ge>n. \<Sigma> x \<down> n = \<sigma> k x \<down> n\<close> for x
      by (metis "*" "**" "***" "****" restriction_related_le restriction_chain_is(1)
          restriction_tendsto_of_restriction_convergent restriction_tendsto_unique)
    hence \<open>\<forall>k\<ge>n. \<Sigma> \<down> n = \<sigma> k \<down> n\<close> by (simp add: restriction_fun_def)
    thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<Sigma> \<down> n = \<sigma> k \<down> n\<close> by blast
  qed

  thus \<open>restriction_convergent \<sigma>\<close> by (fact restriction_convergentI)
qed



(*<*)
end
  (*>*)



