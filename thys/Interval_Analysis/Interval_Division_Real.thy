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

chapter\<open>A Naive Interval Division for Real Intervals\<close>

theory
  Interval_Division_Real
imports
  Interval_Division_Non_Zero
begin

text \<open>
  The theory @{theory "HOL-Library.Interval"} does not define a division operation on intervals.
  Actually, 
In the following we define division in a straight forward way. This is possible, as in HOL, the 
property @{thm "division_ring_divide_zero"} holds. Therefore, we do not need to use, in the first 
instance, extended interval analysis (e.g., based on the type @{type "ereal"}. As a consequence, 
results obtained using this definition might differ from results obtained using definitions of 
divisions using extended reals (e.g., \<^cite>\<open>"moore.ea:introduction:2009"\<close>). \<close>

instantiation "interval" :: ("{linordered_field, real_normed_algebra,linear_continuum_topology}") inverse
begin 
  definition inverse_interval :: "'a interval \<Rightarrow> 'a interval"
    where "inverse_interval a = mk_interval ( 1 / (upper a), 1 / (lower a))"
  definition divide_interval :: "'a interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval"
    where "divide_interval a b = inverse b * a"
  instance ..
end

interpretation interval_division_inverse divide inverse
  apply (unfold_locales)
  subgoal by (simp add: inverse_interval_def) 
  subgoal by(simp add: divide_interval_def)
  done

lemma width_of_reciprocal_interval_bound_real: 
  fixes Y :: "real interval"
  assumes  \<open>\<not> 0 \<in>\<^sub>i Y\<close>
  shows \<open>interval_of(width ((interval_of 1) / Y)) \<le>  
         (abs_interval((interval_of 1) / Y) *  abs_interval((interval_of 1) / Y)) * interval_of(width Y)\<close>
proof(cases "Y" rule:interval_linorder_case_split[of _ 0 "\<lambda> Y. interval_of(width ((interval_of 1) / Y)) \<le>
         (abs_interval((interval_of 1) / Y)) *  (abs_interval((interval_of 1) / Y)) * interval_of(width Y)" ])
  case LeftOf
  have a0:  \<open>lower Y \<le> upper Y\<close> using lower_le_upper by simp
  have a1: \<open>interval_of(width ((interval_of 1) / Y)) = Interval( 1 / lower Y -  1 / upper Y,  1 / lower Y -  1 / upper Y) \<close> 
    using assms interval_of_width by blast
  have a2: \<open>(abs_interval((interval_of 1) / Y) *  abs_interval((interval_of 1) / Y)) * interval_of(width Y) = Interval((upper Y - lower Y) * 1 / \<bar>lower Y\<bar> * 1 / \<bar>lower Y\<bar>, (upper Y - lower Y) * 1 / \<bar>upper Y\<bar> * 1 / \<bar>upper Y\<bar>)\<close>
  proof - 
    have b0: \<open>1 / \<bar>lower Y\<bar> \<le> 1 / \<bar>upper Y\<bar>\<close> using assms a0 LeftOf 
        by (smt (verit, best) frac_le)
      have b1: \<open>0 \<le> upper Y - lower Y\<close>
      using assms LeftOf by simp
    moreover have b2: \<open>(abs_interval((interval_of 1) / Y) *  abs_interval((interval_of 1) / Y)) * interval_of(width Y) = Interval(1/\<bar>lower Y\<bar>, 1/\<bar>upper Y\<bar>) * Interval(1/\<bar>lower Y\<bar>, 1/\<bar>upper Y\<bar>) * Interval(upper Y - lower Y, upper Y - lower Y)\<close>
      using assms LeftOf abs_neg[of Y] width_expanded[of Y] by simp 
    moreover have b3: \<open>... = Interval(Min { (1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar>), (1 /\<bar>lower Y\<bar> * 1 /\<bar>upper Y\<bar>),  (1 /\<bar>upper Y\<bar> * 1 /\<bar>lower Y\<bar>), (1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>)}, Max  { (1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar>), (1 /\<bar>lower Y\<bar> * 1 /\<bar>upper Y\<bar>),  (1 /\<bar>upper Y\<bar> * 1 /\<bar>lower Y\<bar>), (1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>)}) * Interval(upper Y - lower Y, upper Y - lower Y) \<close>
      using assms a0 LeftOf  interval_interval_times[of "Interval(1/\<bar>lower Y\<bar>, 1/\<bar>upper Y\<bar>)"  "Interval(1/\<bar>lower Y\<bar>, 1/\<bar>upper Y\<bar>)"]
      using lower_bounds upper_bounds b0 by simp 
    have b4: \<open>Min {(1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar>), (1 /\<bar>lower Y\<bar> * 1 /\<bar>upper Y\<bar>),  (1 /\<bar>upper Y\<bar> * 1 /\<bar>lower Y\<bar>), (1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>)} = (1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar>)\<close>
      using assms a0 LeftOf upper_leq_lower_div 
      apply(simp add: min_def, safe) 
      apply (smt (z3) divide_divide_eq_left' divide_less_cancel divide_minus_right nonzero_minus_divide_divide)
        apply argo+
      by (smt (z3) a0 divide_divide_eq_left' divide_le_cancel divide_nonneg_neg frac_le minus_divide_right mult.commute mult_left_mono mult_minus_left)
    have b5: \<open>Max {(1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar>), (1 /\<bar>lower Y\<bar> * 1 /\<bar>upper Y\<bar>),  (1 /\<bar>upper Y\<bar> * 1 /\<bar>lower Y\<bar>), (1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>)} = (1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>)\<close>
      using assms a0 LeftOf upper_leq_lower_div 
      apply (simp add: max_def, safe)
      apply (smt (verit, del_insts) frac_le mult_mono_nonpos_nonpos mult_neg_neg)
      apply argo
          apply argo
      apply (smt (z3) b0 divide_divide_eq_left' divide_less_cancel minus_divide_right nonzero_minus_divide_divide) 
      apply (smt (verit, best) division_leq mult_mono_nonpos_nonpos not_real_square_gt_zero)
      by argo+
    moreover have \<open>(abs_interval((interval_of 1) / Y) *  abs_interval((interval_of 1) / Y)) * interval_of(width Y) = Interval(1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar>, 1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>) * Interval(upper Y - lower Y, upper Y - lower Y)\<close> 
      using b2 b3 b4 b5 by presburger
    moreover have \<open>... = Interval((upper Y - lower Y) * 1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar>, (upper Y - lower Y) * 1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>)\<close>
      using assms a0 LeftOf b4 b5 interval_times_scalar_pos_r[of "upper Y - lower Y" "Interval(1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar>, 1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>)"]
     unfolding interval_of_def by simp 
    ultimately show ?thesis by metis
  qed
  have a3: \<open>(upper Y - lower Y) * 1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar> \<le>  1 / lower Y -  1 / upper Y \<close> 
  proof -
    have "(1 / lower Y) - (1 / upper Y) = (upper Y - lower Y) / (lower Y * upper Y)" 
      using assms a0 LeftOf  
      by (smt (verit) diff_divide_distrib nonzero_divide_mult_cancel_left nonzero_divide_mult_cancel_right)  
    moreover have \<open>(upper Y - lower Y) * 1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar> = (upper Y - lower Y) / \<bar>lower Y\<bar>^2\<close>
      using assms  LeftOf  by (simp add: power2_eq_square) 
    moreover have \<open>((upper Y - lower Y) / \<bar>lower Y\<bar>^2) \<le> (upper Y - lower Y) / (lower Y * upper Y)\<close>
      using assms a0 LeftOf
      by (smt (verit) frac_le minus_mult_minus mult_left_mono_neg mult_neg_neg power2_eq_square)
    ultimately show ?thesis by metis
  qed
  have a4: \<open>1 / lower Y -  1 / upper Y \<le> (upper Y - lower Y) * 1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>\<close> 
  proof -
    have "(1 / lower Y) - (1 / upper Y) = (upper Y - lower Y) / (lower Y * upper Y)" 
      using assms a0 LeftOf
      by (smt (verit) diff_divide_distrib nonzero_divide_mult_cancel_left nonzero_divide_mult_cancel_right)  
    moreover have \<open>(upper Y - lower Y) * 1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar> = (upper Y - lower Y) / \<bar>upper Y\<bar>^2\<close>
      using assms LeftOf by (simp add: power2_eq_square) 
    moreover have \<open>(upper Y - lower Y) / (lower Y * upper Y) \<le> ((upper Y - lower Y) / \<bar>upper Y\<bar>^2) \<close>
      using assms LeftOf 
      by (simp add: frac_le power2_eq_square zero_less_mult_iff)
    ultimately show ?thesis by metis
  qed
  have \<open>Interval( 1 / lower Y -  1 / upper Y,  1 / lower Y -  1 / upper Y) \<le>  Interval((upper Y - lower Y) * 1 /\<bar>lower Y\<bar> * 1 /\<bar>lower Y\<bar>, (upper Y - lower Y) * 1 /\<bar>upper Y\<bar> * 1 /\<bar>upper Y\<bar>)\<close>
    using a3 a4 unfolding less_eq_interval_def by simp 
  then show ?case using a1 a2 a3 a4 by simp
next
  case Including
  then show ?case using assms by simp
next
  case RightOf
  have a0:  \<open>lower Y \<le> upper Y\<close> using lower_le_upper by simp
  have a1: \<open>interval_of(width ((interval_of 1) / Y)) = Interval( 1 / lower Y -  1 / upper Y,  1 / lower Y -  1 / upper Y) \<close> 
    using assms interval_of_width by blast
  have a2: \<open>(abs_interval((interval_of 1) / Y) *  abs_interval((interval_of 1) / Y)) * interval_of(width Y) = Interval((upper Y - lower Y) * 1 /upper Y * 1 /upper Y, (upper Y - lower Y) * 1 /lower Y * 1 /lower Y)\<close>
  proof -
    have b0: \<open>0 \<le> upper Y - lower Y\<close>
      using assms RightOf by simp
    moreover have b1: \<open>(abs_interval((interval_of 1) / Y) *  abs_interval((interval_of 1) / Y)) * interval_of(width Y) = Interval(1/upper Y, 1/lower Y) * Interval(1/upper Y, 1/lower Y) * Interval(upper Y - lower Y, upper Y - lower Y)\<close>
      using assms RightOf abs_pos[of Y] width_expanded[of Y] by simp
    moreover have b2: \<open>... = Interval(Min { (1 /upper Y * 1 /upper Y), (1 /upper Y * 1 /lower Y),  (1 /lower Y * 1 /upper Y), (1 /lower Y * 1 /lower Y)}, Max { (1 /upper Y * 1 /upper Y), (1 /upper Y * 1 /lower Y),  (1 /lower Y * 1 /upper Y), (1 /lower Y * 1 /lower Y)}) * Interval(upper Y - lower Y, upper Y - lower Y) \<close>
      using assms RightOf upper_leq_lower_div interval_interval_times[of "Interval(1 /upper Y, 1 / lower Y)"  "Interval(1 /upper Y, 1 / lower Y)"]
      by fastforce
    have b3: \<open>Min {(1 /upper Y * 1 /upper Y), (1 /upper Y * 1 /lower Y),  (1 /lower Y * 1 /upper Y), (1 /lower Y * 1 /lower Y)} = (1 /upper Y * 1 /upper Y)\<close>
      using assms a0 RightOf upper_leq_lower_div 
      apply(simp add: min_def, safe) 
      apply (smt (verit, ccfv_SIG) frac_le mult_less_cancel_left_pos zero_less_mult_iff)
      apply argo+
      by (simp add: frac_le)
     have b4: \<open>Max { (1 /upper Y * 1 /upper Y), (1 /upper Y * 1 /lower Y),  (1 /lower Y * 1 /upper Y), (1 /lower Y * 1 /lower Y)} = (1 /lower Y * 1 /lower Y)\<close>
       using assms a0 RightOf upper_leq_lower_div 
       apply (simp add: max_def, safe)
       subgoal 
         using frac_le le_numeral_extra(4) less_numeral_extra(3) linordered_nonzero_semiring_class.zero_le_one 
           mult_mono' not_real_square_gt_zero order_less_imp_le by metis 
       apply argo+
       apply (simp add: frac_le)
       subgoal 
         using frac_le linordered_nonzero_semiring_class.zero_le_one mult_mono' mult_pos_pos 
           order.refl order_less_imp_le by meson
       by argo+
    moreover have \<open>(abs_interval((interval_of 1) / Y) *  abs_interval((interval_of 1) / Y)) * interval_of(width Y) = Interval(1 /upper Y * 1 /upper Y, 1 /lower Y * 1 /lower Y) * Interval(upper Y - lower Y, upper Y - lower Y)\<close> 
      using b1 b2 b3 b4  by presburger
    moreover have \<open>... = Interval((upper Y - lower Y) * 1 /upper Y * 1 /upper Y, (upper Y - lower Y) * 1 /lower Y * 1 /lower Y)\<close>
      using assms RightOf b0 interval_times_scalar_pos_r[of "upper Y - lower Y" "Interval(1 /upper Y * 1 /upper Y, 1 /lower Y * 1 /lower Y)"]
      unfolding interval_of_def 
      by (smt (verit, del_insts) divide_cancel_left divide_nonneg_nonneg frac_le interval_times_scalar_pos_r lower_bounds nonzero_divide_mult_cancel_right times_divide_eq_right upper_bounds width_def width_expanded)
    ultimately show ?thesis by simp 
  qed
  have a3: \<open>1 /upper Y * 1 /upper Y * (upper Y - lower Y) \<le> 1 / lower Y -  1 / upper Y\<close>
    proof - 
      have b0: \<open>0 < upper Y\<close> using assms a0 RightOf by argo
      then have "(1 / lower Y) - (1 / upper Y) = (upper Y - lower Y) / (lower Y * upper Y)" 
        using assms RightOf b0 by (simp add: diff_divide_distrib) 
      then have b1: \<open>((1/ upper Y) * (1/ upper Y) * (upper Y - lower Y) * (lower Y * upper Y) \<le> (upper Y - lower Y)) = ((1/ upper Y) * (1/ upper Y) * (upper Y - lower Y) \<le> 1 / lower Y - 1 / upper Y)\<close> 
        using assms RightOf b0 by (simp add: pos_le_divide_eq)
      then have b2: \<open>((upper Y - lower Y) * lower Y / upper Y) \<le> upper Y - lower Y\<close> 
        using assms a0 RightOf b0 by (smt (verit) mult_left_less_imp_less pos_less_divide_eq)
      moreover have \<open>(upper Y - lower Y) * lower Y \<le> (upper Y - lower Y) * upper Y\<close> 
        using assms RightOf b0 calculation pos_divide_le_eq by blast
      show ?thesis using assms b0 b1 b2 by force
    qed
    have a4: \<open>1 / lower Y -  1 / upper Y \<le> 1 /lower Y * 1 /lower Y * (upper Y - lower Y)\<close> 
    proof -
      have b0: \<open>0 < upper Y\<close> using assms a0 RightOf by argo
      then have "(1 / lower Y) - (1 / upper Y) = (upper Y - lower Y) / (lower Y * upper Y)" 
        using assms RightOf b0 by (simp add: diff_divide_distrib) 
      then have b1: \<open>(upper Y - lower Y \<le> (1/ lower Y) * (1/ lower Y) * (upper Y - lower Y) * (lower Y * upper Y)) = (1 / lower Y - 1 / upper Y \<le> ((1/ lower Y) * (1/ lower Y) * (upper Y - lower Y) ))\<close> 
        using assms RightOf b0 by (simp add: pos_divide_le_eq)
      then have b2: \<open>upper Y - lower Y \<le> ((upper Y - lower Y) * upper Y / lower Y)\<close> 
        using assms a0 RightOf b0 by (smt (verit) division_leq mult_pos_pos nonzero_mult_div_cancel_right)
      moreover have \<open>(upper Y - lower Y) * lower Y \<le> (upper Y - lower Y) * upper Y\<close> 
        using calculation pos_divide_le_eq by (simp add: RightOf pos_le_divide_eq)
      show ?thesis using assms b0 b1 b2 RightOf by simp
    qed
    have \<open>Interval( 1 / lower Y -  1 / upper Y,  1 / lower Y -  1 / upper Y) \<le>  Interval((upper Y - lower Y) * 1 /upper Y * 1 /upper Y, (upper Y - lower Y) * 1 /lower Y * 1 /lower Y)\<close>
      using a3 a4 unfolding less_eq_interval_def by simp 
  then show ?case using a1 a2 a3 a4 by simp
qed

end 
