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

chapter\<open>Interval Utilities\<close>
theory
  Interval_Utilities
imports
  "HOL-Library.Interval"
  "HOL-Analysis.Analysis"
  "HOL-Library.Interval_Float"
begin

section\<open>Preliminaries\<close>

lemma compact_set_of: 
  fixes X::\<open>'a::{preorder,topological_space, ordered_euclidean_space} interval\<close>
  shows \<open>compact (set_of X)\<close>
  by(simp add:set_of_eq compact_interval[of "lower X" "upper X"]) 

lemma bounded_set_of:
  fixes X::\<open>'a::{preorder,topological_space, ordered_euclidean_space} interval\<close>
  shows \<open>bounded (set_of X)\<close>
  by(simp add:set_of_eq compact_interval[of "lower X" "upper X"]) 

lemma compact_img_set_of:
  fixes X :: \<open>real interval\<close> and f::\<open>real \<Rightarrow> real\<close>
  assumes \<open>continuous_on (set_of X) f\<close>
  shows \<open>compact (f ` set_of X)\<close>
  using compact_continuous_image[of "set_of X" f, simplified assms] compact_interval 
  unfolding set_of_eq 
  by simp  

lemma sup_inf_dist_bounded:
  fixes X::\<open>real set\<close> 
  shows \<open>bdd_below X \<Longrightarrow> bdd_above X ==>  \<forall> x \<in> X. \<forall> x' \<in> X. dist x  x' \<le> Sup X - Inf X\<close>  
  using cInf_lower[of _ X] cSup_upper[of _ X] 
  apply(auto simp add:dist_real_def)[1]
  by (smt (z3))

lemma set_of_nonempty[simp]: \<open>set_of X \<noteq> {}\<close>
  by(simp add:set_of_eq)

lemma lower_in_interval[simp]:\<open>lower X \<in>\<^sub>i X\<close>
  by(simp add: in_intervalI)

lemma upper_in_interval[simp]:\<open>upper X \<in>\<^sub>i X\<close>
  by(simp add: in_intervalI)

lemma bdd_below_set_of: \<open>bdd_below (set_of X)\<close>
  by (metis atLeastAtMost_iff bdd_below.unfold set_of_eq)

lemma bdd_above_set_of: \<open>bdd_above (set_of X)\<close> 
  by (metis atLeastAtMost_iff bdd_above.unfold set_of_eq)

lemma closed_set_of: \<open>closed (set_of (X::real interval))\<close>
  by (metis  closed_real_atLeastAtMost set_of_eq)

lemma set_f_nonempty: \<open>f ` set_of X \<noteq> {}\<close>
  apply(simp add:image_def set_of_eq)
  by fastforce

lemma interval_linorder_case_split[case_names LeftOf Including  RightOf]:
assumes \<open>(upper x < c \<Longrightarrow> P (x::('a::linorder interval)))\<close>
   \<open>( c \<in>\<^sub>i x \<Longrightarrow> P x)\<close> 
   \<open>( c < lower x \<Longrightarrow> P x)\<close> 
 shows\<open> P x\<close>
proof(insert assms, cases " upper x < c")
  case True
  then show ?thesis
    using assms(1) by blast 
next
  case False
  then show ?thesis 
  proof(cases "c \<in>\<^sub>i x")
    case True
    then show ?thesis
      using assms(2) by blast 
  next
    case False
    then show ?thesis 
      by (meson assms(1) assms(3) in_intervalI not_le_imp_less) 
  qed
qed

lemma foldl_conj_True:
\<open>foldl (\<and>) x xs = list_all (\<lambda> e. e = True)  (x#xs)\<close>
  by(induction xs rule:rev_induct, auto)
  
lemma foldl_conj_set_True:
\<open>foldl (\<and>) x xs = (\<forall> e \<in> set (x#xs) . e = True)\<close>
  by(induction xs rule:rev_induct, auto)


section "Interval Bounds and Set Conversion "

lemma sup_set_of:
  fixes X :: "'a::{conditionally_complete_lattice} interval"
  shows "Sup (set_of X) = upper X"
  unfolding set_of_def upper_def
  using cSup_atLeastAtMost lower_le_upper[of X]
  by (simp add: upper_def lower_def) 
 
lemma inf_set_of:
  fixes X :: "'a::{conditionally_complete_lattice} interval"
  shows "Inf (set_of X) = lower X" 
  unfolding set_of_def lower_def
  using cInf_atLeastAtMost lower_le_upper[of X]
  by (simp add: upper_def lower_def)

lemma inf_le_sup_set_of: 
  fixes X :: "'a::{conditionally_complete_lattice} interval"
  shows"Inf (set_of X) \<le> Sup (set_of X)"
  using sup_set_of inf_set_of lower_le_upper
  by metis   

lemma in_bounds: \<open>x \<in>\<^sub>i X \<Longrightarrow> lower X \<le> x \<and> x \<le> upper X\<close>
  by (simp add: set_of_eq)

lemma lower_bounds[simp]: 
  assumes \<open>L \<le> U\<close>
  shows \<open>lower (Interval(L,U)) = L \<close>
  using assms
  apply (simp add: lower.rep_eq)
  by (simp add: bounds_of_interval_eq_lower_upper lower_Interval upper_Interval)

lemma upper_bounds [simp]: 
  assumes \<open>L \<le> U\<close>
  shows \<open>upper (Interval(L,U)) = U\<close>
  using assms
  apply (simp add: upper.rep_eq)
  by (simp add: bounds_of_interval_eq_lower_upper lower_Interval upper_Interval)

lemma lower_point_interval[simp]: \<open>lower (Interval (x,x)) = x\<close>
  by (simp) 
lemma upper_point_interval[simp]: \<open>upper (Interval (x,x)) = x\<close>
  by (simp)

lemma map2_nth:
  assumes  \<open>length xs = length ys\<close>
      and      \<open>n < length xs\<close>
    shows \<open>(map2 f xs ys)!n = f (xs!n) (ys!n)\<close>
  using assms  by simp

lemma map_set: \<open>a \<in> set (map f X) \<Longrightarrow>  (\<exists> x \<in> set X . f x = a)\<close>
  by auto
lemma map_pair_set_left: \<open>(a,b) \<in> set (zip (map f X) (map f Y)) \<Longrightarrow> (\<exists> x \<in> set X . f x = a)\<close>
  by (meson map_set set_zip_leftD)
lemma map_pair_set_right: \<open>(a,b) \<in> set (zip (map f X) (map f Y)) \<Longrightarrow>  (\<exists> y \<in> set Y . f y = b)\<close>
  by (meson map_set set_zip_rightD) 
lemma map_pair_set: \<open>(a,b) \<in> set (zip (map f X) (map f Y)) \<Longrightarrow>  (\<exists> x \<in> set X . f x = a) \<and>  (\<exists> y \<in> set Y . f y = b)\<close>
  by (meson map_pair_set_left set_zip_rightD zip_same) 

lemma map_pair_f_all: 
  assumes \<open>length X = length Y\<close> 
  shows \<open>(\<forall>(x, y)\<in>set (zip (map f X) (map f Y)). x \<le> y) = (\<forall>(x, y)\<in>set (zip X Y ). f x \<le> f y)\<close>
  by(insert assms(1), induction X Y rule:list_induct2, auto)

definition   map_interval_swap :: \<open>('a::linorder \<times> 'a) list \<Rightarrow> 'a interval list\<close> where
\<open>map_interval_swap = map (\<lambda> (x,y). Interval (if x \<le> y then (x,y) else (y,x)))\<close>

definition  mk_interval :: \<open>('a::linorder \<times> 'a) \<Rightarrow> 'a interval \<close> where
\<open>mk_interval = (\<lambda> (x,y). Interval (if x \<le> y then (x,y) else (y,x)))\<close>

definition  mk_interval' :: \<open>('a::linorder \<times> 'a) \<Rightarrow> 'a interval \<close> where
\<open>mk_interval' = (\<lambda> (x,y). (if x \<le> y then Interval(x,y) else Interval(y,x)))\<close>

lemma map_interval_swap_code[code]:
  \<open> map_interval_swap = map (\<lambda> (x,y). the (if x \<le> y then Interval' x y else Interval' y x))\<close>  
  unfolding map_interval_swap_def by(rule ext, rule arg_cong, auto simp add: Interval'.abs_eq)

lemma  mk_interval_code[code]:
  \<open>mk_interval = (\<lambda> (x,y). the (if x \<le> y then Interval' x y else Interval' y x))\<close>
  unfolding mk_interval_def by(rule ext, rule arg_cong, auto simp add: Interval'.abs_eq)

lemma  mk_interval':
  \<open>mk_interval = (\<lambda> (x,y). (if x \<le> y then Interval(x, y) else Interval(y, x)))\<close>
  unfolding mk_interval_def by(rule ext, rule arg_cong, auto)

lemma mk_interval_lower[simp]: \<open> lower (mk_interval (x,y)) = (if x \<le> y then x else y)\<close>
  by(simp add: lower_def Interval_inverse mk_interval_def) 

lemma mk_interval_upper[simp]: \<open> upper (mk_interval (x,y)) = (if x \<le> y then y else x)\<close>
  by(simp add: upper_def Interval_inverse mk_interval_def) 

section\<open>Linear Order on List of Intervals\<close>

definition 
  le_interval_list :: \<open>('a::linorder) interval list \<Rightarrow> 'a interval list \<Rightarrow> bool\<close> ("(_/ \<le>\<^sub>I _)" [51, 51] 50)
  where 
    \<open>le_interval_list Xs Ys \<equiv> (length Xs = length Ys) \<and> (foldl (\<and>) True (map2 (\<le>) Xs Ys))\<close>

lemma le_interval_single: \<open>(x \<le> y) = ([x] \<le>\<^sub>I [y])\<close>
  unfolding le_interval_list_def by simp

lemma le_intervall_empty[simp]: \<open>[] \<le>\<^sub>I []\<close>
  unfolding le_interval_list_def by simp

lemma le_interval_list_rev: \<open>(is \<le>\<^sub>I js) = (rev is \<le>\<^sub>I rev js)\<close>
  unfolding le_interval_list_def 
  by(safe, simp_all add: foldl_conj_set_True zip_rev)

lemma le_interval_list_imp_length: 
  assumes \<open>Xs \<le>\<^sub>I Ys\<close> shows \<open>length Xs = length Ys\<close>
using assms unfolding le_interval_list_def
  by simp


lemma lsplit_left: assumes \<open>length (xs) = length (ys)\<close> 
  and \<open>(\<forall>n<length (x # xs). (x # xs) ! n \<le> (y # ys) ! n)\<close> shows \<open> 
      ((\<forall> n < length xs. xs!n \<le> ys!n) \<and> x \<le> y)\<close>
  using assms  by auto 

lemma lsplit_right: assumes \<open>length (xs) = length (ys)\<close>
  and  \<open>((\<forall> n < length xs. xs!n \<le> ys!n) \<and> x \<le> y)\<close>
shows \<open>(n<length (x # xs) \<longrightarrow> (x # xs) ! n \<le> (y # ys) ! n)\<close>
proof(cases "n=0")
  case True
  then show ?thesis using assms by(simp)
next
  case False
  then show ?thesis using assms by simp
qed

lemma lsplit: assumes \<open>length (xs) = length (ys)\<close>
  shows \<open>(\<forall>n<length (x # xs). (x # xs) ! n \<le> (y # ys) ! n) =  
      ((\<forall> n < length xs. xs!n \<le> ys!n) \<and> x \<le> y)\<close>
  using assms lsplit_left lsplit_right by metis 

lemma le_interval_list_all':
  assumes \<open>length Xs = length Ys\<close> and \<open>Xs \<le>\<^sub>I Ys\<close> shows \<open>\<forall> n < length Xs. Xs!n \<le> Ys!n\<close>
proof(insert assms, induction rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case  
    using lsplit[of xs ys x y] le_interval_list_def 
    unfolding le_interval_list_def
    by(auto simp add: foldl_conj_True) 
qed

lemma le_interval_list_all2:
  assumes \<open>length Xs = length Ys\<close>  
    and \<open>\<forall> n<length Xs . (Xs!n  \<le> Ys!n)\<close>
  shows  \<open>Xs \<le>\<^sub>I Ys\<close> 
proof(insert assms, induction rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case  
    using lsplit[of xs ys x y] le_interval_list_def 
    unfolding le_interval_list_def
    by(auto simp add: foldl_conj_True) 
qed

lemma le_interval_list_all:
  assumes \<open>Xs \<le>\<^sub>I Ys\<close> shows \<open>\<forall> n < length Xs. Xs!n \<le> Ys!n\<close>
  using assms le_interval_list_all' le_interval_list_imp_length
  by auto 

lemma le_interval_list_imp:
  assumes \<open>Xs \<le>\<^sub>I Ys\<close> shows \<open>n < length Xs \<longrightarrow>  Xs!n \<le> Ys!n\<close>
  using assms le_interval_list_all' le_interval_list_imp_length
  by auto

lemma  interval_set_leq_eq: \<open>(X \<le> Y) = (set_of X \<subseteq> set_of Y)\<close>
  for X :: \<open>'a::linordered_ring interval\<close>
  by (simp add: less_eq_interval_def set_of_eq) 

lemma times_interval_right:
  fixes X Y C ::\<open>'a::linordered_ring interval\<close>
  assumes \<open>X \<le> Y\<close> 
  shows \<open>C * X \<le> C * Y\<close>
  using assms[simplified interval_set_leq_eq]
  apply(subst interval_set_leq_eq) 
  by (simp add: set_of_mul_inc_right) 


lemma times_interval_left:
  fixes X Y C ::\<open>'a::{real_normed_algebra,linordered_ring,linear_continuum_topology} interval\<close>
  assumes \<open>X \<le> Y\<close> 
  shows \<open>X * C \<le> Y * C\<close>
  using assms[simplified interval_set_leq_eq]
  apply(subst interval_set_leq_eq) 
  by (simp add: set_of_mul_inc_left) 

section\<open>Support for Lists of Intervals \<close>

abbreviation in_interval_list::\<open>('a::preorder) list \<Rightarrow> 'a interval list \<Rightarrow> bool\<close> ("(_/ \<in>\<^sub>I _)" [51, 51] 50)
  where \<open>in_interval_list xs Xs \<equiv> foldl (\<and>) True (map2 (in_interval) xs Xs)\<close>

lemma interval_of_in_interval_list[simp]: \<open>xs \<in>\<^sub>I map interval_of xs\<close>
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
    by (simp add: in_interval_to_interval) 
qed

lemma interval_of_in_eq:  \<open>interval_of x \<le> X = (x \<in>\<^sub>i X)\<close>
  by (simp add: less_eq_interval_def set_of_eq) 

lemma interval_of_list_in: 
  assumes \<open>length inputs = length Inputs\<close>
shows \<open>(map interval_of inputs \<le>\<^sub>I Inputs) = (inputs \<in>\<^sub>I Inputs)\<close>
unfolding le_interval_list_def
proof(insert assms, induction inputs Inputs rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case 
  proof(cases "interval_of x \<le> y")
    case True
    then show ?thesis 
      using Cons by(simp add: interval_of_in_eq) 
  next
    case False
    then show ?thesis using foldl_conj_True interval_of_in_eq by auto  
  qed
qed

section \<open>Interval Width and Arithmetic Operations\<close>

lemma interval_width_addition:
  fixes A:: "'a::{linordered_ring} interval"
  shows \<open>width (A + B) = width A + width B\<close>
  by (simp add: width_def) 

lemma interval_width_times:
  fixes a :: "'a::{linordered_ring}" and A :: "'a interval"
  shows "width (interval_of a * A) = \<bar>a\<bar> * width A" 
proof -
  have "width (interval_of a * A) = upper (interval_of a * A) - lower (interval_of a * A)"
    by (simp add: width_def)
  also have "... = (if a > 0 then a * upper A - a * lower A else a * lower A - a * upper A)"
    proof -
      have "upper (interval_of a * A) = max (a * lower A) (a * upper A)"
        by (simp add: upper_times)
      moreover have "lower (interval_of a * A) = min (a * lower A) (a * upper A)"
        by (simp add: lower_times)
      ultimately show ?thesis 
        by (simp add: mult_left_mono mult_left_mono_neg)
    qed
  also have "... = \<bar>a\<bar> * (upper A - lower A)"
    by (simp add: right_diff_distrib)
  finally show ?thesis
    by (simp add: width_def)
qed

lemma interval_sup_width:
  fixes X Y :: "'a::{linordered_ring, lattice} interval"
  shows "width (sup X Y) = max (upper X) (upper Y) - min (lower X) (lower Y)"
proof -
  have a0: "\<forall>i ia. lower (sup i ia) = min (lower i::real) (lower ia)"
    by (simp add: inf_min)
  have a1: "\<forall>i ia. upper (sup i ia) = max (upper i::real) (upper ia)"
    by (simp add: sup_max)
  show ?thesis
    using a0 a1 by (simp add: inf_min sup_max width_def) 
qed

lemma width_expanded: \<open>interval_of (width Y) = Interval(upper Y - lower Y, upper Y - lower Y)\<close>
  unfolding width_def interval_of_def by simp

lemma interval_width_positive:
  fixes X :: \<open>'a::{linordered_ring} interval\<close>
  shows \<open>0 \<le> width X\<close>
  using lower_le_upper 
  by (simp add: width_def)

section \<open>Interval Multiplication\<close>

lemma interval_interval_times: 
\<open>X * Y = Interval(Min {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)}, 
                  Max {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)})\<close>
  by (simp add: times_interval_def bounds_of_interval_eq_lower_upper Let_def min_def)

lemma interval_times_scalar: \<open>interval_of a * A = mk_interval(a * lower A, a * upper A)\<close>
 proof -
    have "upper (interval_of a * A) = max (a * lower A) (a * upper A)"
      by (simp add: upper_times )
    moreover have "lower (interval_of a * A) = min (a * lower A) (a * upper A)"
      by (simp add: lower_times)
    ultimately show ?thesis 
      by (simp add: interval_eq_iff)
  qed

lemma interval_times_scalar_pos_l: 
  assumes \<open>0 \<le> a \<close> 
  shows \<open>interval_of a * A = Interval(a * lower A, a * upper A)\<close> 
 proof -
   have "upper (interval_of a * A) = a * upper A"
     using assms
     by (simp add: upper_times mult_left_mono)
   moreover have "lower (interval_of a * A) = a * lower A"
     using assms
     by (simp add: lower_times mult_left_mono)
   ultimately show ?thesis 
     using assms
     by (metis bounds_of_interval_eq_lower_upper bounds_of_interval_inverse lower_le_upper)
 qed

lemma interval_times_scalar_pos_r: 
  fixes a :: "'a::{linordered_idom}"
  assumes \<open>0 \<le> a\<close> 
  shows \<open>A * interval_of a = Interval(a * lower A, a * upper A)\<close>
 proof -
   have "upper (A * interval_of a) = a * upper A"
     using assms  
     by (simp add: mult.commute mult_left_mono upper_times)
   moreover have "lower (A * interval_of a ) = a * lower A"
     using assms
     by (simp add: lower_times mult_right_mono) 
   ultimately show ?thesis 
     using assms
     by (metis bounds_of_interval_eq_lower_upper bounds_of_interval_inverse lower_le_upper)
 qed


section \<open>Distance-based Properties of Intervals\<close>

text \<open>Given two real intervals @{term \<open>X\<close>} and @{term \<open>Y\<close>}, and two real numbers  @{term \<open>a\<close>} 
and @{term \<open>b\<close>}, the width of the sum of the scaled intervals is equivalent to the width of the 
two individual intervals.\<close>

lemma width_of_scaled_interval_sum:
  fixes  X :: "'a::{linordered_ring} interval"
  shows \<open>width (interval_of a * X + interval_of b * Y) = \<bar>a\<bar> * width X + \<bar>b\<bar> * width Y\<close>
  using interval_width_addition interval_width_times by metis

lemma width_of_product_interval_bound_real:
  fixes X :: "real interval"
  shows \<open>interval_of (width (X * Y)) \<le> abs_interval(X) * interval_of (width Y) + abs_interval(Y) * interval_of (width X)\<close>
proof -
  have a0: "lower X \<le> upper X" \<open>lower Y \<le> upper Y\<close> 
    using lower_le_upper by simp_all
  have a1: \<open>width Y \<ge> 0\<close> and a1': \<open>width X \<ge> 0\<close> 
    using a0 interval_width_positive by simp_all
  have a2: \<open>abs_interval(X) * interval_of (width Y) = Interval (width Y * lower (abs_interval X), width Y * upper (abs_interval X))\<close>
    using interval_times_scalar_pos_r a0 a1 by blast 
  have  a3: \<open>abs_interval(Y) * interval_of (width X) = Interval (width X * lower (abs_interval Y), width X * upper (abs_interval Y))\<close>
    using interval_times_scalar_pos_r a0 interval_width_positive by blast 
  have a4: \<open>abs_interval(X) * interval_of (width Y) + abs_interval(Y) * interval_of (width X) = Interval (width Y * lower (abs_interval X) + width X * lower (abs_interval Y), width Y * upper (abs_interval X) + width X * upper (abs_interval Y))\<close>
    using a0 a2 a3 unfolding plus_interval_def 
    apply (simp add:bounds_of_interval_eq_lower_upper mult_left_mono interval_width_positive)
    by (auto simp add:bounds_of_interval_eq_lower_upper mult_left_mono interval_width_positive)
  have a5: \<open>width(X * Y) = Max {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} - Min {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)}\<close>
    using lower_times upper_times unfolding  width_def by metis
  have a6: \<open>Max {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} - Min {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} \<le> width Y * upper (abs_interval X) + width X * upper (abs_interval Y)\<close>
    using a0 a1 a1' unfolding width_def
    by (simp, smt (verit) a0  mult.commute mult_less_cancel_left_pos mult_minus_left right_diff_distrib)  (* takes long *) 
    have a7: \<open>width Y * lower (abs_interval X) + width X * lower (abs_interval Y) \<le> Max {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} - Min {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)}\<close>
    using a0 a1 a1' unfolding width_def 
    by (simp, smt (verit) a0 mult.commute mult_less_cancel_left_pos mult_minus_left right_diff_distrib) (* takes long *)
  have \<open>interval_of (Max {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} -
                     Min {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)}) \<le> 
        Interval (width Y * lower (abs_interval X) + width X * lower (abs_interval Y), 
                  width Y * upper (abs_interval X) + width X * upper (abs_interval Y))\<close>
    using a6 a7 unfolding less_eq_interval_def 
    by (smt (verit, ccfv_threshold) lower_bounds lower_interval_of upper_bounds upper_interval_of) 
  then show ?thesis using a4 a5 a6 by presburger
qed


lemma width_of_product_interval_bound_int:
  fixes X :: "int interval"
  shows \<open>interval_of (width (X * Y)) \<le> abs_interval(X) * interval_of (width Y) + abs_interval(Y) * interval_of (width X)\<close>
proof -
  have a0: "lower X \<le> upper X" \<open>lower Y \<le> upper Y\<close> 
    using lower_le_upper by simp_all
  have a1: \<open>width Y \<ge> 0\<close> and \<open>width X \<ge> 0\<close> 
    using a0 interval_width_positive by simp_all
   have a2: \<open>abs_interval(X) * interval_of (width Y) = Interval (width Y * lower (abs_interval X), width Y * upper (abs_interval X))\<close>
    using interval_times_scalar_pos_r a0 a1 by blast 
  have  a3: \<open>abs_interval(Y) * interval_of (width X) = Interval (width X * lower (abs_interval Y), width X * upper (abs_interval Y))\<close>
    using interval_times_scalar_pos_r a0 interval_width_positive by blast 
  have a4: \<open>abs_interval(X) * interval_of (width Y) + abs_interval(Y) * interval_of (width X) = Interval (width Y * lower (abs_interval X) + width X * lower (abs_interval Y), width Y * upper (abs_interval X) + width X * upper (abs_interval Y))\<close>
    using a0 a2 a3 unfolding plus_interval_def 
    by (auto simp add:bounds_of_interval_eq_lower_upper mult_left_mono interval_width_positive) (* takes long *) 
  have a5: \<open>width(X * Y) = Max {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} - Min {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)}\<close>
    using lower_times upper_times unfolding  width_def by metis
  have a6: \<open>Max {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} - Min {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} \<le> width Y * upper (abs_interval X) + width X * upper (abs_interval Y)\<close>
    using a0 unfolding width_def 
    by (simp, smt (verit) a0  mult.commute mult_less_cancel_left_pos mult_minus_left right_diff_distrib)  (* takes long *) 
  have a7: \<open>width Y * lower (abs_interval X) + width X * lower (abs_interval Y) \<le> Max {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} - Min {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)}\<close>
    using a0 unfolding width_def 
    apply(auto)[1] 
    by (smt (verit) a0(1) a0(2) left_diff_distrib mult_less_cancel_left_pos int_distrib(3) 
        mult_less_cancel_left mult_minus_right mult.commute mult_le_0_iff right_diff_distrib' 
        mult_left_mono mult_le_cancel_right right_diff_distrib zero_less_mult_iff )+
  have \<open>interval_of (Max {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)} -
                     Min {(lower X * lower Y), (lower X * upper Y), (upper X * lower Y), (upper X * upper Y)}) \<le> 
        Interval (width Y * lower (abs_interval X) + width X * lower (abs_interval Y), 
                  width Y * upper (abs_interval X) + width X * upper (abs_interval Y))\<close>
    using a6 a7 unfolding less_eq_interval_def
    by (smt (verit, ccfv_threshold) lower_bounds lower_interval_of upper_bounds upper_interval_of)
  then show ?thesis using a4 a5 a6 by presburger
qed

end 
