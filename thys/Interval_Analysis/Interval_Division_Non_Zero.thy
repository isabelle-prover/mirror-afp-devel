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

chapter\<open>Basic Properties of Interval Division\<close>

theory
  Interval_Division_Non_Zero
  imports
  Interval_Utilities
begin

text \<open>
  The theory @{theory "HOL-Library.Interval"} does not define a division operation on intervals.
  In the following we define a locale capturing the core properties of division by an interval that
  does not contain zero. \<close>

section\<open>Preliminaries\<close>

lemma division_leq_neg:
  fixes x :: "'a::{linordered_field}"
  assumes "0 < x" and "y < 0" and "z < 0" and "y \<le> z"
  shows "x / z \<le> x / y"
proof -
  have "x * y \<le> x * z" using assms by simp
  hence "(x * y) / (y * z) \<le> (x * z) / (y * z)" 
    using assms
    by (simp add: divide_right_mono zero_less_mult_iff neg_divide_le_eq)
  thus ?thesis using assms by auto[1]  
qed

lemma division_leq:
  fixes x :: "'a::{linordered_field}"
  assumes "0 < x" and "y \<le> z" and \<open>y \<noteq> 0 \<and> z \<noteq> 0\<close> and \<open>(y < 0 \<and> z < 0) \<or> (0 < y \<and> 0 < z) \<close>
  shows "x / z \<le> x / y"
proof (cases \<open>(y < 0 \<and> z < 0)\<close>)
  case True
  then show ?thesis using assms division_leq_neg by blast
next
  case False
  have \<open>(0 < y \<and> 0 < z)\<close> using assms False by blast
  then show ?thesis 
    using assms
    by (simp add: frac_le)
qed

lemma upper_leq_lower_div:
  fixes Y :: "'a::{linordered_field} interval"
  assumes \<open>lower Y \<le> upper Y\<close> and \<open>\<not> 0 \<in>\<^sub>i Y\<close>
  shows \<open>1 / upper Y \<le> 1 / lower Y\<close>
  using assms division_leq frac_le 
  by (metis atLeastAtMost_iff inverse_eq_divide le_imp_inverse_le 
            le_imp_inverse_le_neg linorder_not_less set_of_eq)

section\<open>A Locale for Interval Division Where the Quotient-Interval does not Contain Zero\<close>

locale interval_division = inverse +
  constrains inverse :: \<open>'a::{linordered_field, real_normed_algebra,linear_continuum_topology} interval \<Rightarrow> 'a interval\<close>
         and divide  :: \<open>'a::{linordered_field, real_normed_algebra,linear_continuum_topology} interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval\<close>
       assumes inverse_left: \<open>\<not> 0 \<in>\<^sub>i x \<Longrightarrow> 1 \<le> (inverse x) * x\<close>
           and divide:      \<open>\<not> 0 \<in>\<^sub>i y \<Longrightarrow> x \<le> (divide x y) * y\<close> 
begin 
end 

lemma interval_non_zero_eq:  
  \<open>\<not> 0 \<in>\<^sub>i (i::'a::{linorder, zero} interval) = (lower i < 0 \<and> upper i < 0) \<or> (lower i > 0 \<and> upper i > 0)\<close>
  by (metis in_bounds in_intervalI linorder_not_less lower_le_upper order_le_less_trans) 

lemma inverse_includes_one:
  assumes \<open>\<not> 0 \<in>\<^sub>i (i::'a::{division_ring,linordered_ring} interval)\<close>
  shows   \<open>1 \<in>\<^sub>i (mk_interval (1 / upper i, 1 / lower i)) * i\<close>
  using assms interval_non_zero_eq[of i] 
  apply(simp add: set_of_eq)
  apply(safe, simp_all)
  by (metis in_bounds lower_in_interval mk_interval_upper nonzero_eq_divide_eq times_in_intervalI 
            upper_in_interval)+ 
 
lemma inverse_includes_one': 
  assumes \<open>\<not> 0 \<in>\<^sub>i (i::'a::{division_ring,linordered_ring} interval)\<close>
  shows   \<open>1 \<le> (mk_interval (1 / upper i, 1 / lower i)) * i\<close>
  by (simp add: assms in_bounds inverse_includes_one less_eq_interval_def) 


locale interval_division_inverse = inverse + 
  constrains inverse :: \<open>'a::{linordered_field, real_normed_algebra,linear_continuum_topology} interval \<Rightarrow> 'a interval\<close>
         and divide  :: \<open>'a::{linordered_field, real_normed_algebra,linear_continuum_topology} interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval\<close>
       assumes inverse_non_zero_def: \<open>\<not> 0 \<in>\<^sub>i x \<Longrightarrow> (inverse x) = mk_interval(1 / (upper x), 1 / (lower x))\<close>
           and divide_non_zero_def:  \<open>\<not> 0 \<in>\<^sub>i y \<Longrightarrow> (divide x y) = inverse y * x\<close> 
begin 

sublocale interval_division divide inverse
  apply(standard)
  subgoal 
    by (simp add: inverse_includes_one' inverse_non_zero_def) 
  subgoal
    by (metis (no_types, opaque_lifting) divide_non_zero_def interval_mul_commute inverse_includes_one' inverse_non_zero_def mult.assoc one_times_ivl_right times_interval_right) 
  done 

lemma inverse_left_ge_one:
  assumes \<open>\<not> 0 \<in>\<^sub>i x\<close> 
  shows \<open>1 \<le> (inverse x) * x\<close>
proof - 
  have lower_ne_zero: \<open>lower x \<noteq> 0\<close>
    using assms lower_in_interval by metis 
  have upper_ne_zero: \<open>lower x \<noteq> 0\<close>
    using assms lower_in_interval by metis 
  have \<open>1 \<le> (mk_interval ( 1 / (upper x), 1 / (lower x))) * x\<close> 
  proof(cases "1 / upper x \<le> 1 / lower x")
    case True note * = this
    then show ?thesis 
    proof(cases "upper x = lower x")
      case True
      then show ?thesis 
        using upper_times[of "mk_interval (1 / upper x, 1 / lower x)" x] 
              lower_times[of "mk_interval (1 / upper x, 1 / lower x)" x] 
              interval_eq_iff[of "mk_interval (1 / upper x, 1 / lower x) * x" 1]
              lower_ne_zero upper_ne_zero
        unfolding mk_interval'
        by simp
    next
      case False
      then show ?thesis 
        using interval_eq_iff[of "mk_interval (1 / upper x, 1 / lower x) * x" 1]
              upper_times[of "mk_interval (1 / upper x, 1 / lower x)" x] 
              lower_times[of "mk_interval (1 / upper x, 1 / lower x)" x]
      proof -
        have "1 / lower x = upper (mk_interval (1 / upper x, 1 / lower x))"
          by (simp add: "*")
        then show ?thesis
          by (metis (no_types) in_bounds less_eq_interval_def lower_in_interval lower_one 
              nonzero_divide_eq_eq times_in_intervalI upper_in_interval upper_ne_zero upper_one)
      qed
    qed
  next
    case False
    then show ?thesis 
        using interval_eq_iff[of "mk_interval (1 / upper x, 1 / lower x) * x" 1]
              upper_times[of "mk_interval (1 / upper x, 1 / lower x)" x] 
              lower_times[of "mk_interval (1 / upper x, 1 / lower x)" x]
        using assms lower_le_upper upper_leq_lower_div by blast 
    qed
    then show ?thesis 
  by (simp add: assms inverse_non_zero_def) 
  qed

lemma division_right_ge_refl: 
  assumes \<open>\<not> 0 \<in>\<^sub>i y\<close>
  shows \<open>x \<le> x * ((inverse y) * y)\<close>
proof - 
  have a1: \<open>set_of 1 \<subseteq> set_of ((inverse y) * y)\<close>
    using inverse_left_ge_one[of y, simplified assms, simplified]
    by (simp add: interval_set_leq_eq) 
  show ?thesis
    using set_of_mul_inc_right[of 1 "mk_interval (1 / upper y, 1 / lower y) * y" x, 
              simplified one_times_ivl_right[of x] a1, simplified]
    by (metis a1 interval_set_leq_eq one_times_ivl_right times_interval_right)
qed

lemma division_right_ge_refl': 
  assumes \<open>\<not> 0 \<in>\<^sub>i y\<close> 
  shows \<open>x \<le> x * inverse y * y\<close>
  by (simp add: assms division_right_ge_refl mult.assoc) 

lemma interval_div_constant:
  assumes  \<open>0 \<notin> set_of Y\<close> and \<open>0 \<le> x\<close>
  shows \<open>divide (interval_of x)  Y = Interval( x / upper Y, x / lower Y)\<close>
proof -
  have l:  \<open>lower Y \<le> upper Y\<close> using lower_le_upper by simp
  have \<open>1 / upper Y \<le> 1 / lower Y\<close> using assms l
    by (metis divide_left_mono frac_le in_intervalI linorder_not_less mult_neg_neg order_less_le 
        zero_less_one_class.zero_le_one)
  then show ?thesis 
    using
    interval_of.abs_eq[of x]
    assms divide_non_zero_def[of Y "interval_of x", simplified assms, simplified] 
    inverse_non_zero_def[of Y, simplified assms, simplified]
    interval_times_scalar_pos_l interval_times_scalar_pos_r by fastforce
qed

lemma interval_of_width:  
  assumes \<open>\<not> 0 \<in>\<^sub>i Y\<close> 
  shows \<open>interval_of(width (divide (interval_of 1) Y)) = Interval( 1 / lower Y -  1 / upper Y,  1 / lower Y -  1 / upper Y) \<close>
proof(cases "Y" rule:interval_linorder_case_split[of _ 0 "\<lambda> Y. interval_of(width (divide (interval_of 1) Y)) 
                                                               = Interval( 1 / lower Y -  1 / upper Y,  1 / lower Y -  1 / upper Y)" ])
  case LeftOf
  have \<open>1 / upper Y \<le> 1 / lower Y\<close>
    using assms division_leq_neg LeftOf 
    by (simp add: le_divide_eq)  
  then show ?case 
    using interval_div_constant upper_bounds lower_bounds assms
    unfolding width_def interval_of_def by fastforce
next
  case Including
  then show ?case using assms by simp
next
  case RightOf
  have \<open>1 / upper Y \<le> 1 / lower Y\<close>
    by (simp add: assms upper_leq_lower_div) 
  then show ?case
    using interval_div_constant upper_bounds lower_bounds assms
    unfolding width_def interval_of_def by fastforce
qed

lemma abs_pos:
  assumes \<open>0 < lower Y \<close> and \<open>\<not> 0 \<in>\<^sub>i Y\<close>
  shows \<open>abs_interval(divide (interval_of 1) Y) = Interval( 1 / upper Y, 1 / lower Y)\<close>
proof -
  have l:  \<open>lower Y \<le> upper Y\<close> using lower_le_upper by simp
  have \<open>0 < 1 / upper Y \<close> 
    by (metis assms(1) l dual_order.strict_trans1 zero_less_divide_1_iff)
  moreover have \<open> 0 < 1 / lower Y\<close>
    by (metis assms(1) zero_less_divide_1_iff)
  moreover have \<open>1 / upper Y \<le> 1 / lower Y\<close>
    using assms by (simp add: frac_le)
  moreover have \<open>divide (interval_of 1) Y = Interval( 1 / upper Y, 1 / lower Y)\<close>
    using assms interval_div_constant[of Y 1] by simp
  ultimately show ?thesis 
    unfolding abs_interval_def by (simp add: bounds_of_interval_eq_lower_upper)
qed

lemma abs_neg:
  assumes \<open>upper Y < 0 \<close> and \<open>\<not> 0 \<in>\<^sub>i Y\<close>
  shows \<open>abs_interval(divide (interval_of 1) Y) = Interval(1 / \<bar>lower Y\<bar>, 1 / \<bar>upper Y\<bar>)\<close>
proof -
  have l:  \<open>lower Y \<le> upper Y\<close> using lower_le_upper by simp
  have i0: \<open> 1 / upper Y < 0 \<close> and i1: \<open> 1 / lower Y < 0\<close>
    using assms by (simp, meson assms(1) divide_less_0_1_iff lower_le_upper order_le_less_trans)
  moreover have i2: \<open>\<bar>upper Y\<bar> \<le> \<bar>lower Y\<bar>\<close>
    using assms l by linarith
  then have i3: \<open>\<bar>1 / lower Y\<bar> \<le> \<bar>1 / upper Y\<bar>\<close>
    using assms division_leq_neg i1 
    by (simp add: division_leq)
  moreover have \<open>divide (interval_of 1) Y = Interval( 1 / upper Y, 1 / lower Y)\<close>
    using assms interval_div_constant[of Y 1] by simp
  moreover have \<open>abs_interval(Interval( 1 / upper Y, 1 / lower Y)) = Interval(\<bar>1 / lower Y\<bar>, \<bar>1 / upper Y\<bar>)\<close>
    using assms i0 i1 i2 i3 unfolding abs_interval_def min_def max_def
    by (simp add: bounds_of_interval_eq_lower_upper)
  moreover have \<open>... = Interval(1 / \<bar>lower Y\<bar>, 1 / \<bar>upper Y\<bar>)\<close>
    by auto[1]
  ultimately show ?thesis 
    using assms interval_div_constant by force
qed


end 


end 
