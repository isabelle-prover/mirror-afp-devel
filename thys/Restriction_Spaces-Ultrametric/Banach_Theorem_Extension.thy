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


section \<open>Definitions on Functions of Metric Space\<close>

(*<*)
theory  Banach_Theorem_Extension
  imports "HOL-Analysis.Elementary_Metric_Spaces"
begin
  (*>*)

text \<open>In this theory, we define the notion of lipschitz map, non-expanding map
      and contraction map. We also establish correspondences.\<close>


subsection \<open>Definitions\<close>

subsubsection \<open>Lipschitz Map\<close>

text \<open>This notion is a generalization of contraction map and non-expanding map.\<close>

definition lipschitz_with_on :: \<open>['a :: metric_space \<Rightarrow> 'b :: metric_space, real, 'a set] \<Rightarrow> bool\<close>
  where \<open>lipschitz_with_on f \<alpha> A \<equiv> 0 \<le> \<alpha> \<and> (\<forall>x\<in>A. \<forall>y\<in>A. dist (f x) (f y) \<le> \<alpha> * dist x y)\<close>

abbreviation lipschitz_with :: \<open>['a :: metric_space \<Rightarrow> 'b :: metric_space, real] \<Rightarrow> bool\<close>
  where \<open>lipschitz_with f \<alpha> \<equiv> lipschitz_with_on f \<alpha> UNIV\<close>


lemma lipschitz_with_onI :
  \<open>\<lbrakk>0 \<le> \<alpha>; \<And>x y. \<lbrakk>x \<in> A; y \<in> A; x \<noteq> y; f x \<noteq> f y\<rbrakk> \<Longrightarrow> dist (f x) (f y) \<le> \<alpha> * dist x y\<rbrakk> \<Longrightarrow>
   lipschitz_with_on f \<alpha> A\<close>
  unfolding lipschitz_with_on_def by (metis dist_eq_0_iff zero_le_dist zero_le_mult_iff)

lemma lipschitz_withI :
  \<open>\<lbrakk>0 \<le> \<alpha>; \<And>x y. x \<noteq> y \<Longrightarrow> f x \<noteq> f y \<Longrightarrow> dist (f x) (f y) \<le> \<alpha> * dist x y\<rbrakk> \<Longrightarrow> 
   lipschitz_with f \<alpha>\<close>
  by (rule lipschitz_with_onI)

lemma lipschitz_with_onD1 : \<open>lipschitz_with_on f \<alpha> A \<Longrightarrow> 0 \<le> \<alpha>\<close>
  unfolding lipschitz_with_on_def by simp

lemma lipschitz_withD1 : \<open>lipschitz_with f \<alpha> \<Longrightarrow> 0 \<le> \<alpha>\<close>
  by (rule lipschitz_with_onD1)

lemma lipschitz_with_onD2 :
  \<open>lipschitz_with_on f \<alpha> A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> dist (f x) (f y) \<le> \<alpha> * dist x y\<close>
  unfolding lipschitz_with_on_def by simp

lemma lipschitz_withD2 :
  \<open>lipschitz_with f \<alpha> \<Longrightarrow> dist (f x) (f y) \<le> \<alpha> * dist x y\<close>
  unfolding lipschitz_with_on_def by simp

lemma lipschitz_with_imp_lipschitz_with_on: \<open>lipschitz_with f \<alpha> \<Longrightarrow> lipschitz_with_on f \<alpha> A\<close>
  by (simp add: lipschitz_with_on_def)


lemma lipschitz_with_on_imp_lipschitz_with_on_ge : \<open>lipschitz_with_on f \<beta> A\<close>
  if \<open>\<alpha> \<le> \<beta>\<close> and \<open>lipschitz_with_on f \<alpha> A\<close>
proof (rule lipschitz_with_onI)
  show \<open>0 \<le> \<beta>\<close> by (meson order_trans lipschitz_with_onD1 that)
next
  fix x y assume \<open>x \<in> A\<close> and \<open>y \<in> A\<close>
  from \<open>lipschitz_with_on f \<alpha> A\<close>[THEN lipschitz_with_onD2, OF this]
  have \<open>dist (f x) (f y) \<le> \<alpha> * dist x y\<close> .
  from order_trans[OF this] show \<open>dist (f x) (f y) \<le> \<beta> * dist x y\<close>
    by (simp add: mult_right_mono \<open>\<alpha> \<le> \<beta>\<close>)
qed


theorem lipschitz_with_on_comp_lipschitz_with_on :
  \<open>lipschitz_with_on (\<lambda>x. g (f x)) (\<beta> * \<alpha>) A\<close>
  if \<open>f ` A \<subseteq> B\<close> \<open>lipschitz_with_on g \<beta> B\<close> \<open>lipschitz_with_on f \<alpha> A\<close>
proof (rule lipschitz_with_onI)
  show \<open>0 \<le> \<beta> * \<alpha>\<close> by (metis lipschitz_with_onD1 mult_nonneg_nonneg that(2, 3))
next
  fix x y assume \<open>x \<in> A\<close> and \<open>y \<in> A\<close>
  with \<open>f ` A \<subseteq> B\<close> have \<open>f x \<in> B\<close> and \<open>f y \<in> B\<close> by auto
  have \<open>dist (g (f x)) (g (f y)) \<le> \<beta> * dist (f x) (f y)\<close>
    by (fact that(2)[THEN lipschitz_with_onD2, OF \<open>f x \<in> B\<close> \<open>f y \<in> B\<close>])
  also have \<open>\<dots> \<le> \<beta> * (\<alpha> * dist x y)\<close>
    by (fact mult_left_mono[OF that(3)[THEN lipschitz_with_onD2, OF \<open>x \<in> A\<close> \<open>y \<in> A\<close>]
                               that(2)[THEN lipschitz_with_onD1]])
  also have \<open>\<dots> = \<beta> * \<alpha> * dist x y\<close> by simp
  finally show \<open>dist (g (f x)) (g (f y)) \<le> \<dots>\<close> .
qed

corollary lipschitz_with_comp_lipschitz_with : 
  \<open>\<lbrakk>lipschitz_with g \<beta>; lipschitz_with f \<alpha>\<rbrakk> \<Longrightarrow>
   lipschitz_with (\<lambda>x. g (f x)) (\<beta> * \<alpha>)\<close>
  using lipschitz_with_on_comp_lipschitz_with_on by blast



subsubsection \<open>Non-expanding Map\<close>

definition non_expanding_on :: \<open>['a :: metric_space \<Rightarrow> 'b :: metric_space, 'a set] \<Rightarrow> bool\<close>
  where \<open>non_expanding_on f A \<equiv> lipschitz_with_on f 1 A\<close>

abbreviation non_expanding :: \<open>['a :: metric_space \<Rightarrow> 'b :: metric_space] \<Rightarrow> bool\<close>
  where \<open>non_expanding f \<equiv> non_expanding_on f UNIV\<close>

lemma non_expanding_onI :
  \<open>\<lbrakk>\<And>x y. \<lbrakk>x \<in> A; y \<in> A; x \<noteq> y; f x \<noteq> f y\<rbrakk> \<Longrightarrow> dist (f x) (f y) \<le> dist x y\<rbrakk> \<Longrightarrow> 
   non_expanding_on f A\<close>
  by (simp add: lipschitz_with_onI non_expanding_on_def)

lemma non_expandingI :
  \<open>\<lbrakk>\<And>x y. x \<noteq> y \<Longrightarrow> f x \<noteq> f y \<Longrightarrow> dist (f x) (f y) \<le> dist x y\<rbrakk> \<Longrightarrow> non_expanding f\<close>
  by (rule non_expanding_onI)

lemma non_expanding_onD :
  \<open>non_expanding_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> dist (f x) (f y) \<le> dist x y\<close>
  by (metis lipschitz_with_onD2 mult_1 non_expanding_on_def)

lemma non_expandingD : \<open>non_expanding f \<Longrightarrow> dist (f x) (f y) \<le> dist x y\<close>
  by (simp add: non_expanding_onD)

lemma non_expanding_imp_non_expanding_on: \<open>non_expanding f \<Longrightarrow> non_expanding_on f A\<close>
  by (meson non_expandingD non_expanding_onI)


lemma non_expanding_on_comp_non_expanding_on :
  \<open>\<lbrakk>f ` A \<subseteq> B; non_expanding_on g B; non_expanding_on f A\<rbrakk> \<Longrightarrow>
   non_expanding_on (\<lambda>x. g (f x)) A\<close>
  unfolding non_expanding_on_def
  by (metis (no_types) lipschitz_with_on_comp_lipschitz_with_on mult_1)

corollary non_expanding_comp_non_expanding  :
  \<open>\<lbrakk>non_expanding g; non_expanding f\<rbrakk> \<Longrightarrow> non_expanding (\<lambda>x. g (f x))\<close>
  by (blast intro: non_expanding_on_comp_non_expanding_on)



subsubsection \<open>Contraction Map\<close>

definition contraction_with_on :: \<open>['a :: metric_space \<Rightarrow> 'b :: metric_space, real, 'a set] \<Rightarrow> bool\<close>
  where \<open>contraction_with_on f \<alpha> A \<equiv> \<alpha> < 1 \<and> lipschitz_with_on f \<alpha> A\<close>

abbreviation contraction_with :: \<open>['a :: metric_space \<Rightarrow> 'b :: metric_space, real] \<Rightarrow> bool\<close>
  where \<open>contraction_with f \<alpha> \<equiv> contraction_with_on f \<alpha> UNIV\<close>

definition contraction_on :: \<open>['a :: metric_space \<Rightarrow> 'b :: metric_space, 'a set] \<Rightarrow> bool\<close>
  where \<open>contraction_on f A \<equiv> \<exists>\<alpha>. contraction_with_on f \<alpha> A\<close>

abbreviation contraction :: \<open>['a :: metric_space \<Rightarrow> 'b :: metric_space] \<Rightarrow> bool\<close>
  where \<open>contraction f \<equiv> contraction_on f UNIV\<close>


lemma contraction_with_onI :
  \<open>\<lbrakk>0 \<le> \<alpha>; \<alpha> < 1; \<And>x y. \<lbrakk>x \<in> A; y \<in> A; x \<noteq> y; f x \<noteq> f y\<rbrakk> \<Longrightarrow> dist (f x) (f y) \<le> \<alpha> * dist x y\<rbrakk>
   \<Longrightarrow> contraction_with_on f \<alpha> A\<close>
  by (simp add: contraction_with_on_def lipschitz_with_onI)

lemma contraction_withI :
  \<open>\<lbrakk>0 \<le> \<alpha>; \<alpha> < 1; \<And>x y. x \<noteq> y \<Longrightarrow> f x \<noteq> f y \<Longrightarrow> dist (f x) (f y) \<le> \<alpha> * dist x y\<rbrakk> \<Longrightarrow>
   contraction_with f \<alpha>\<close>
  by (rule contraction_with_onI)

lemma contraction_with_onD1 : \<open>contraction_with_on f \<alpha> A \<Longrightarrow> 0 \<le> \<alpha>\<close>
  by (simp add: contraction_with_on_def lipschitz_with_on_def)

lemma contraction_withD1 : \<open>contraction_with f \<alpha> \<Longrightarrow> 0 \<le> \<alpha>\<close>
  by (simp add: contraction_with_onD1)

lemma contraction_with_onD2 : \<open>contraction_with_on f \<alpha> A \<Longrightarrow> \<alpha> < 1\<close>
  by (simp add: contraction_with_on_def lipschitz_with_on_def)

lemma contraction_withD2 : \<open>contraction_with f \<alpha> \<Longrightarrow> \<alpha> < 1\<close>
  by (simp add: contraction_with_onD2)

lemma contraction_with_onD3 :
  \<open>contraction_with_on f \<alpha> A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> dist (f x) (f y) \<le> \<alpha> * dist x y\<close>
  by (simp add: contraction_with_on_def lipschitz_with_on_def)

lemma contraction_withD3 : \<open>contraction_with f \<alpha> \<Longrightarrow> dist (f x) (f y) \<le> \<alpha> * dist x y\<close>
  by (simp add: contraction_with_on_def lipschitz_withD2)

lemma contraction_with_imp_contraction_with_on:
  \<open>contraction_with f \<alpha> \<Longrightarrow> contraction_with_on f \<alpha> A\<close>
  by (simp add: contraction_with_on_def lipschitz_with_imp_lipschitz_with_on)

lemma contraction_imp_contraction_on: \<open>contraction f \<Longrightarrow> contraction_on f A\<close>
  using contraction_on_def contraction_with_imp_contraction_with_on by blast


lemma contraction_with_on_imp_contraction_on :
  \<open>contraction_with_on f \<alpha> A \<Longrightarrow> contraction_on f A\<close>
  unfolding contraction_on_def by blast

lemma contraction_with_imp_contraction: \<open>contraction_with f \<alpha> \<Longrightarrow> contraction f\<close>
  by (simp add: contraction_with_on_imp_contraction_on)


lemma contraction_onE:
  \<open>\<lbrakk>contraction_on f A; \<And>\<alpha>. contraction_with_on f \<alpha> A \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  unfolding contraction_on_def by blast

lemma contractionE:
  \<open>\<lbrakk>contraction f; \<And>\<alpha>. contraction_with f \<alpha> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (elim contraction_onE)


lemma contraction_with_on_imp_contraction_with_on_ge :
  \<open>\<lbrakk>\<alpha> \<le> \<beta>; \<beta> < 1; contraction_with_on f \<alpha> A\<rbrakk> \<Longrightarrow> contraction_with_on f \<beta> A\<close>
  by (simp add: contraction_with_on_def lipschitz_with_on_imp_lipschitz_with_on_ge)



subsection \<open>Properties\<close>

lemma contraction_with_on_imp_lipschitz_with_on[simp] :
  \<open>contraction_with_on f \<alpha> A \<Longrightarrow> lipschitz_with_on f \<alpha> A\<close>
  by (simp add: contraction_with_on_def)

lemma non_expanding_on_imp_lipschitz_with_one_on[simp] :
  \<open>non_expanding_on f A \<Longrightarrow> lipschitz_with_on f 1 A\<close>
  by (simp add: non_expanding_on_def)

lemma contraction_on_imp_non_expanding_on[simp] :
  \<open>contraction_on f A \<Longrightarrow> non_expanding_on f A\<close> 
proof (elim contraction_onE, rule non_expanding_onI)
  fix \<alpha> x y assume \<open>x \<in> A\<close> and \<open>y \<in> A\<close> and contra : \<open>contraction_with_on f \<alpha> A\<close>
  show \<open>dist (f x) (f y) \<le> dist x y\<close>
    by (rule order_trans[OF contra[THEN contraction_with_onD3, OF \<open>x \<in> A\<close> \<open>y \<in> A\<close>]])
      (metis contra contraction_with_on_def mult_less_cancel_right1 nle_le order_less_le zero_le_dist)
qed


lemma contraction_with_on_comp_contraction_with_on :
  \<open>contraction_with_on (\<lambda>x. g (f x)) (\<beta> * \<alpha>) A\<close>
  if \<open>f ` A \<subseteq> B\<close> \<open>contraction_with_on g \<beta> B\<close> \<open>contraction_with_on f \<alpha> A\<close>
proof (unfold contraction_with_on_def, intro conjI)
  from that(2, 3)[THEN contraction_with_onD2] that(2)[THEN contraction_with_onD1]
  show \<open>\<beta> * \<alpha> < 1\<close> by (metis dual_order.strict_trans2 mult_less_cancel_left1 nle_le order_less_le)
next
  show \<open>lipschitz_with_on (\<lambda>x. g (f x)) (\<beta> * \<alpha>) A\<close>
    by (rule lipschitz_with_on_comp_lipschitz_with_on[OF \<open>f ` A \<subseteq> B\<close>])
      (simp_all add: that(2, 3))
qed

corollary contraction_with_comp_contraction_with :
  \<open>\<lbrakk>contraction_with g \<beta>; contraction_with f \<alpha>\<rbrakk> \<Longrightarrow> contraction_with (\<lambda>x. g (f x)) (\<beta> * \<alpha>)\<close>
  by (blast intro: contraction_with_on_comp_contraction_with_on)

corollary contraction_on_comp_contraction_on :
  \<open>\<lbrakk>f ` A \<subseteq> B; contraction_on g B; contraction_on f A\<rbrakk> \<Longrightarrow> contraction_on (\<lambda>x. g (f x)) A\<close>
proof (elim contraction_onE)
  fix \<alpha> \<beta> assume \<open>f ` A \<subseteq> B\<close> \<open>contraction_with_on g \<beta> B\<close> \<open>contraction_with_on f \<alpha> A\<close>
  from contraction_with_on_comp_contraction_with_on[OF this]
  show \<open>contraction_on (\<lambda>x. g (f x)) A\<close> by (fact contraction_with_on_imp_contraction_on)
qed

corollary contraction_comp_contraction :
  \<open>\<lbrakk>contraction g; contraction f\<rbrakk> \<Longrightarrow> contraction (\<lambda>x. g (f x))\<close>
  by (blast intro: contraction_on_comp_contraction_on)


lemma contraction_with_on_comp_non_expanding_on :
  \<open>contraction_with_on (\<lambda>x. g (f x)) \<beta> A\<close>
  if \<open>f ` A \<subseteq> B\<close> \<open>contraction_with_on g \<beta> B\<close> \<open>non_expanding_on f A\<close>
proof (unfold contraction_with_on_def, intro conjI)
  from that(2)[THEN contraction_with_onD2] show \<open>\<beta> < 1\<close> .
next
  show \<open>lipschitz_with_on (\<lambda>x. g (f x)) \<beta> A\<close>
    by (rule lipschitz_with_on_comp_lipschitz_with_on[OF \<open>f ` A \<subseteq> B\<close>, of g \<beta> 1, simplified])
      (simp_all add: that(2, 3))
qed

corollary contraction_with_comp_non_expanding  :
  \<open>\<lbrakk>contraction_with g \<beta>; non_expanding f\<rbrakk> \<Longrightarrow> contraction_with (\<lambda>x. g (f x)) \<beta>\<close>
  by (blast intro: contraction_with_on_comp_non_expanding_on)

corollary contraction_on_comp_non_expanding_on :
  \<open>\<lbrakk>f ` A \<subseteq> B; contraction_on g B; non_expanding_on f A\<rbrakk> \<Longrightarrow> contraction_on (\<lambda>x. g (f x)) A\<close>
  by (metis contraction_on_def contraction_with_on_comp_non_expanding_on)

corollary contraction_comp_non_expanding  :
  \<open>\<lbrakk>contraction g; non_expanding f\<rbrakk> \<Longrightarrow> contraction (\<lambda>x. g (f x))\<close>
  by (blast intro: contraction_on_comp_non_expanding_on)


lemma non_expanding_on_comp_contraction_with_on :
  \<open>contraction_with_on (\<lambda>x. g (f x)) \<alpha> A\<close>
  if \<open>f ` A \<subseteq> B\<close> \<open>non_expanding_on g B\<close> \<open>contraction_with_on f \<alpha> A\<close>
proof (unfold contraction_with_on_def, intro conjI)
  from that(3)[THEN contraction_with_onD2] show \<open>\<alpha> < 1\<close> .
next
  show \<open>lipschitz_with_on (\<lambda>x. g (f x)) \<alpha> A\<close>
    by (rule lipschitz_with_on_comp_lipschitz_with_on[OF \<open>f ` A \<subseteq> B\<close>, of g 1, simplified])
      (simp_all add: that(2, 3))
qed

corollary non_expanding_comp_contraction_with :
  \<open>\<lbrakk>non_expanding g; contraction_with f \<alpha>\<rbrakk> \<Longrightarrow> contraction_with (\<lambda>x. g (f x)) \<alpha>\<close>
  by (blast intro: non_expanding_on_comp_contraction_with_on)

corollary non_expanding_on_comp_contraction_on :
  \<open>\<lbrakk>f ` A \<subseteq> B; non_expanding_on g B; contraction_on f A\<rbrakk> \<Longrightarrow> contraction_on (\<lambda>x. g (f x)) A\<close>
  by (metis contraction_on_def non_expanding_on_comp_contraction_with_on)

corollary non_expanding_comp_contraction :
  \<open>\<lbrakk>non_expanding g; contraction f\<rbrakk> \<Longrightarrow> contraction (\<lambda>x. g (f x))\<close>
  by (blast intro: non_expanding_on_comp_contraction_on)



subsection \<open>Banach's fixed-point Theorems\<close>

text \<open>We rewrite the Banach's fixed-point theorems with our new definition.\<close>

theorem Banach_fix_type : \<open>contraction f \<Longrightarrow> \<exists>!x. f x = x\<close>
  for f :: \<open>'a :: complete_space \<Rightarrow> 'a\<close>
  by (elim contractionE)
    (metis banach_fix_type contraction_withD1 contraction_withD2 contraction_withD3)

theorem Banach_fix:
  \<open>contraction_on f s \<Longrightarrow> \<exists>!x. x \<in> s \<and> f x = x\<close> if \<open>complete s\<close> \<open>s \<noteq> {}\<close> \<open>f ` s \<subseteq> s\<close>
proof (elim contraction_onE, intro banach_fix[OF \<open>complete s\<close> \<open>s \<noteq> {}\<close> _ _ \<open>f ` s \<subseteq> s\<close>] ballI)
  show \<open>contraction_with_on f \<alpha> s \<Longrightarrow> 0 \<le> \<alpha>\<close> for \<alpha> by (fact contraction_with_onD1)
next
  show \<open>contraction_with_on f \<alpha> s \<Longrightarrow> \<alpha> < 1\<close> for \<alpha> by (fact contraction_with_onD2)
next
  show \<open>contraction_with_on f \<alpha> s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow>
        dist (f x) (f y) \<le> \<alpha> * dist x y\<close> for \<alpha> x y by (fact contraction_with_onD3)
qed


(*<*)
end
  (*>*)
