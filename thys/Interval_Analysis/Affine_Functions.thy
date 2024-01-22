(***********************************************************************************
 * Copyright (c) University of Exeter, UK
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
 * SPDX-License-Identifier: BSD-3-Clause
 ***********************************************************************************)

chapter\<open>Affine Functions\<close>

text\<open>
  In this theory, we provide formalisation of affine functions (sometimes also called linear 
  polynomial functions).
\<close>

theory
  Affine_Functions
  imports
  Complex_Main
begin

section\<open>Definition of Affine Functions, Alternative Definitions, and Special Cases\<close>

locale affine_fun =
  fixes f 
  assumes \<open>\<exists> b. linear (\<lambda> x. f x - b)\<close>

lemma affine_fun_alt: 
  \<open>affine_fun f = (\<exists> c g. (f = (\<lambda> x. g x + c)) \<and> linear g)\<close>
  unfolding affine_fun_def
  by(safe, force, simp add: Real_Vector_Spaces.linear_iff) 

lemma affine_fun_real_linfun: 
  \<open>affine_fun (f::(real \<Rightarrow> real)) = (\<exists> a b . f = (\<lambda> x. a * x + b))\<close>
  by(simp add: affine_fun_alt, metis real_linearD linear_times)

lemma linear_is_affine_fun: \<open>linear f \<Longrightarrow> affine_fun f\<close>
  by (standard, simp add: Real_Vector_Spaces.linear_iff)

lemma affine_zero_is_linear: assumes \<open>affine_fun f\<close> and \<open>f 0 = 0\<close> shows \<open>linear f\<close>
  apply(insert assms) 
  unfolding affine_fun_def 
  using linear_0 by fastforce

lemma affine_add: 
  assumes \<open>affine_fun f\<close> and \<open>affine_fun g\<close>
  shows \<open>affine_fun (\<lambda> x. f x + g x)\<close>
  using assms  linear_compose_add
  by(auto simp add: affine_fun_alt, force) 

lemma scaleR:
  assumes \<open>affine_fun f \<close> shows \<open>affine_fun (\<lambda> x. a *\<^sub>R (f x))\<close>
  using assms 
  apply(simp add: affine_fun_alt)
  by (metis linear_compose_scale_right scaleR_right_distrib) 
 
lemma real_affine_funD:
  fixes f :: "real \<Rightarrow> real"
  assumes "affine_fun f" obtains c b where "f = (\<lambda> x. c * x + b)"
  using assms  
  apply(simp add: affine_fun_alt)
  by (metis real_linearD) 


section\<open>Common Linear Polynomial Functions\<close>

lemma affine_fun_const[simp]: \<open>affine_fun (\<lambda> x. c)\<close>
  apply(simp add: affine_fun_alt)
  using module_hom_zero by force 

lemma affine_fun_id[simp]: \<open>affine_fun (\<lambda> x. x)\<close>
  by (simp add: linear_is_affine_fun module_hom_ident)

lemma affine_fun_mult[simp]: \<open>affine_fun (\<lambda> x. (c::'a::real_algebra) * x)\<close>
  by(simp add: linear_is_affine_fun)

lemma affine_fun_scaled[simp]: \<open>affine_fun (\<lambda> x. x /c )\<close>
  for c :: "'a::real_normed_field"
  using bounded_linear_divide[of c] linear_is_affine_fun[of " (\<lambda> x. x /c )"] bounded_linear.linear 
  by blast 

lemma affine_fun_add[simp]: \<open>affine_fun (\<lambda> x. x + c)\<close>
  apply(simp add: affine_fun_alt)
  using module_hom_ident by force 

lemma affine_fun_diff[simp]: \<open>affine_fun (\<lambda> x. x - c)\<close>
  apply(simp add: affine_fun_alt)
  using module_hom_ident by force 

lemma affine_fun_triv[simp]: \<open>affine_fun (\<lambda> x. a *\<^sub>R x + c)\<close>
  apply(simp add: affine_fun_alt)
  by fastforce 
 
lemma affine_fun_add_const[simp]: assumes \<open>affine_fun f\<close> shows \<open>affine_fun (\<lambda> x. (f x) + c)\<close>
  using assms apply(simp add:affine_fun_alt)
  by (metis add.commute add.left_commute)

lemma affine_fun_diff_const[simp]: assumes \<open>affine_fun f\<close> shows \<open>affine_fun (\<lambda> x. (f x) - c)\<close>
  using assms apply(simp add:affine_fun_alt) by force

lemma affine_fun_comp[simp]: assumes \<open>affine_fun (f)\<close>
and \<open>affine_fun (g)\<close> shows \<open>affine_fun (f \<circ> g)\<close>
  using assms 
  unfolding affine_fun_alt
  apply(simp add:o_def)
  using linear_add linear_compose[simplified o_def] add.assoc
  by metis 

lemma affine_fun_linear[simp]: assumes \<open>affine_fun f\<close> shows \<open>affine_fun (\<lambda> x. a *\<^sub>R (f x) + c)\<close>
  by(rule affine_fun_comp[of "\<lambda> x. a *\<^sub>R x + c" f, simplified o_def], simp_all add: assms)  


section\<open>Linear Polynomial Functions and Orderings\<close>

lemma affine_fun_leq_pos: 
assumes \<open>affine_fun (f::real \<Rightarrow> real)\<close> and \<open>affine_fun g\<close> 
and \<open>x\<in>{0..u}\<close>  and \<open>(f 0 \<le> g 0 )\<close>  and \<open>(f u \<le> g u)\<close> 
shows \<open>f x \<le> g x\<close>
  using assms 
  apply(auto simp add: linear_0 affine_fun_real_linfun)[1]
  by (smt (verit) left_diff_distrib mult_left_mono_neg mult_right_mono) 

lemma affine_fun_leq_neg:
assumes \<open>affine_fun (f::real \<Rightarrow> real)\<close> and \<open>affine_fun g\<close> 
and \<open>x\<in>{l..0}\<close>  and \<open>(f l \<le> g l )\<close>  and \<open>(f 0 \<le> g 0)\<close> 
shows \<open>f x \<le> g x\<close>
  using assms
  apply(auto simp add: linear_0 affine_fun_real_linfun)[1]
  using Groups.mult_ac(2) left_diff_distrib mult_right_mono
  by (smt (verit, ccfv_SIG))

lemma affine_fun_leq: 
assumes \<open>affine_fun (f::real \<Rightarrow> real)\<close> and \<open>affine_fun g\<close> 
and \<open>x\<in>{l..u}\<close>  and \<open>(f l \<le> g l )\<close>  and \<open>(f u \<le> g u)\<close> 
shows \<open>f x \<le> g (x::real)\<close>
  using assms affine_fun_leq_neg[of f g x l] affine_fun_leq_pos[of f g x u]
  apply(simp add: linear_0 affine_fun_real_linfun)
  by (smt (verit, ccfv_SIG) left_diff_distrib mult_left_mono_neg)


lemma affine_fun_le_pos: 
assumes \<open>affine_fun (f::real \<Rightarrow> real)\<close> and \<open>affine_fun g\<close> 
and \<open>x\<in>{0..u}\<close>  and \<open>(f 0 < g 0 )\<close>  and \<open>(f u < g u)\<close> 
shows \<open>f x < g (x::real)\<close>
  using assms  
  apply(auto simp add: linear_0 affine_fun_real_linfun)[1]
  using Groups.mult_ac(2) left_diff_distrib mult_right_mono 
  by (smt (verit, best))

lemma affine_fun_le_neg: 
assumes \<open>affine_fun (f::real \<Rightarrow> real)\<close> and \<open>affine_fun g\<close> 
and \<open>x\<in>{l..0}\<close>  and \<open>(f l < g l )\<close>  and \<open>(f 0 < g 0)\<close> 
shows \<open>f x < g (x::real)\<close>
  using assms  
  apply(auto simp add: linear_0 affine_fun_real_linfun)[1]
  using Groups.mult_ac(2) left_diff_distrib mult_right_mono 
  by (smt (verit, ccfv_SIG)) 

lemma affine_fun_le: 
assumes \<open>affine_fun (f::real \<Rightarrow> real)\<close> and \<open>affine_fun g\<close> 
and \<open>x\<in>{l..u}\<close>  and \<open>(f l < g l )\<close>  and \<open>(f u < g u)\<close> 
shows \<open>f x < g (x::real)\<close>
  using assms affine_fun_le_neg[of f g x l] affine_fun_le_pos[of f g x u]
  apply(simp add: linear_0 affine_fun_real_linfun)
  by (smt (verit, ccfv_SIG) left_diff_distrib mult_left_mono_neg)

end
