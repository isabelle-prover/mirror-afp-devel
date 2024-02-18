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

chapter\<open>Interval Inclusion Isotonicity\<close>
theory
  Inclusion_Isotonicity
imports
  "Interval_Utilities"
  "Affine_Functions"
  Interval_Division_Non_Zero
begin

section\<open>Interval Extension\<close>

subsection \<open>Textbook Definition of Interval Extension\<close>
definition\<^marker>\<open>tag important\<close>
  is_interval_extension_of :: \<open>('a::preorder interval \<Rightarrow> 'b::preorder interval) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>  
                               (infix "(is'_interval'_extension'_of)" 50)
where 
  \<open>((F is_interval_extension_of f)) = (\<forall> x. (F (interval_of x)) = interval_of (f x))\<close>

definition\<open>extend_natural f = (\<lambda> X. mk_interval (f (lower X), f(upper X)))\<close>

lemma interval_extension_comp: 
  assumes interval_ext_F:  \<open>F is_interval_extension_of f\<close>
   and    interval_ext_G:  \<open>G is_interval_extension_of g\<close>
  shows \<open>(F o G) is_interval_extension_of (f o g)\<close>
  using assms unfolding is_interval_extension_of_def
  by simp 

lemma interval_extension_const: \<open>(\<lambda> x. interval_of c) is_interval_extension_of (\<lambda> x. c)\<close>
  unfolding is_interval_extension_of_def  
  by (simp add: interval_eq_iff) 

lemma interval_extension_id: \<open>(\<lambda> x. x) is_interval_extension_of (\<lambda> x. x)\<close>
  unfolding is_interval_extension_of_def  
  by (simp add: interval_eq_iff) 

subsection \<open>A Stronger Definition of Interval Extension\<close>
definition 
  is_natural_interval_extension_of :: \<open>('a::linorder interval \<Rightarrow> 'b::linorder interval) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>  
                               (infix \<open>(is'_natural'_interval'_extension'_of)\<close> 50)
where 
  \<open>((F is_natural_interval_extension_of f)) = (\<forall> l u. (F (mk_interval (l,u))) = mk_interval (f l, f u))\<close>

lemma \<open>(extend_natural f) is_interval_extension_of f\<close>  
  unfolding is_interval_extension_of_def extend_natural_def
  by(auto simp add: mk_interval' interval_of_def)

lemma \<open>(extend_natural f) is_natural_interval_extension_of f\<close>
  unfolding is_natural_interval_extension_of_def extend_natural_def
  by(auto simp add: mk_interval' interval_of_def)

lemma natural_interval_extension_implies_interval_extension:
  assumes \<open>F is_natural_interval_extension_of f\<close> shows \<open>F is_interval_extension_of f\<close>
  using assms unfolding is_natural_interval_extension_of_def is_interval_extension_of_def
  mk_interval_def interval_of_def
  by(auto split:if_splits)

lemma const_add_is_natural_interval_extensions: 
  \<open>(\<lambda> x. (interval_of c) + x) is_natural_interval_extension_of (\<lambda> x. c + x)\<close>
  unfolding is_natural_interval_extension_of_def mk_interval_def 
  by (simp add: add_mono_thms_linordered_semiring(1) antisym interval_eq_iff add_mono
           split:if_splits) 

lemma const_times_is_natural_interval_extensions:
  \<open>(\<lambda> x. (interval_of c) * x) is_natural_interval_extension_of (\<lambda> x. c * x)\<close>
  unfolding is_natural_interval_extension_of_def mk_interval_def 
  unfolding times_interval_def Let_def 
  by(simp add: interval_eq_iff Interval_inverse interval_of.rep_eq add_mono 
          split:if_splits)
 
lemma const_is_interval_extension: \<open>F is_natural_interval_extension_of (\<lambda> x. b) \<Longrightarrow> F = (\<lambda> x.(interval_of b))\<close>
  unfolding is_natural_interval_extension_of_def
  apply(auto simp add:mk_interval' interval_of_def split:if_splits)[1]
  by (metis bounds_of_interval_eq_lower_upper bounds_of_interval_inverse lower_le_upper) 

lemma id_is_interval_extension: \<open>F is_natural_interval_extension_of (\<lambda> x. x) \<Longrightarrow> F = (\<lambda> x. x)\<close>
  unfolding is_natural_interval_extension_of_def
  apply(auto simp add:mk_interval' interval_of_def split:if_splits)[1]
  by (metis bounds_of_interval_eq_lower_upper bounds_of_interval_inverse lower_le_upper) 

lemma extend_natural_is_interval_extension: 
  \<open>(extend_natural f) is_natural_interval_extension_of f\<close>
  unfolding extend_natural_def is_natural_interval_extension_of_def mk_interval'_def
  by (smt (z3) case_prod_conv mk_interval_def lower_bounds nle_le upper_bounds) 

lemma is_natural_interval_extension_implies_bounds: 
  fixes F :: \<open>real interval \<Rightarrow> real interval\<close>
   assumes \<open>F is_natural_interval_extension_of f\<close> and \<open>F x \<le> F x'\<close>
  shows
 \<open>((f (lower x')) \<le>   (f (lower x)) ) \<or>  ((f (upper x')) \<le>   (f (upper x)) )\<close>
  by (smt (verit) assms interval_eqI is_natural_interval_extension_of_def less_eq_interval_def 
          lower_le_upper mk_interval_lower mk_interval_upper)

lemma interval_extension_lower:
   \<open>((F is_interval_extension_of f)) \<Longrightarrow> lower (F (interval_of x)) = (f x)\<close>
  unfolding is_interval_extension_of_def by simp

lemma interval_extension_upper:
   \<open>((F is_interval_extension_of f)) \<Longrightarrow> upper (F (interval_of x)) = (f x)\<close>
  unfolding is_interval_extension_of_def by simp

lemma is_interval_extension_eq_upper_and_lower:
   \<open>((F is_interval_extension_of f)) 
        = (\<forall> x. lower (F (interval_of x)) = (f x) \<and> upper (F (interval_of x)) = (f x))\<close>
  unfolding is_interval_extension_of_def
  by (simp add: interval_eq_iff) 

lemma interval_extension_lower_simp[simp]: 
  assumes \<open>F is_interval_extension_of f\<close> and \<open>X = Interval(x,x)\<close> 
  shows \<open>lower (F X) = f x \<close>
  by (metis assms interval_extension_lower interval_of.abs_eq) 

lemma interval_extension_upper_simp[simp]: 
  assumes \<open>F is_interval_extension_of f\<close> and \<open>X = Interval(x,x)\<close> 
  shows \<open>upper (F X) = f x \<close>
  by (metis assms interval_extension_upper interval_of.abs_eq) 

section\<open>Interval Inclusion Isotonicity\<close>

text\<open>
  In this section, we introduce the concept of inclusion isotonicity. The formalization 
  in this theory generalises the definitions from~\<^cite>\<open>"ratz:inclusion:1997"\<close>:
\<close>
definition
  inclusion_isotonic :: \<open>('a::preorder interval \<Rightarrow> 'b::preorder interval) \<Rightarrow> bool\<close>
  where
 \<open>inclusion_isotonic f = (\<forall> x x'. x \<le> x' \<longrightarrow> (f x) \<le> (f x'))\<close>

text\<open>We can immediately show that any natural extension of an affine function of from 
type @{type \<open>real\<close>} to @{type \<open>real\<close>} is interval inclusion isotonic:
\<close>
lemma real_affine_fun_is_inclusion_isotonicM: 
      assumes \<open>affine_fun (f::real => real)\<close> 
      shows \<open>inclusion_isotonic (extend_natural f)\<close>
  using assms  
  unfolding inclusion_isotonic_def extend_natural_def Interval.less_eq_interval_def affine_fun_real_linfun
  by(auto, (metis lower_le_upper mult_le_cancel_left nle_le)+)

definition
  inclusion_isotonic_on :: \<open>('a interval \<Rightarrow> bool ) \<Rightarrow> ('a::preorder interval \<Rightarrow> 'b::preorder interval) \<Rightarrow> bool\<close>
  where
 \<open>inclusion_isotonic_on P f = (\<forall> x x'. P x \<and> P x' \<and> x \<le> x' \<longrightarrow> (f x) \<le> (f x'))\<close>

lemma inclusion_isotonic_eq: \<open>inclusion_isotonic_on (\<lambda> x . True) = inclusion_isotonic\<close>
  unfolding inclusion_isotonic_on_def inclusion_isotonic_def
  by simp

definition inclusion_isotonic_binary :: \<open>('a::preorder interval \<Rightarrow> 'a interval \<Rightarrow> 'b::preorder interval) \<Rightarrow> bool\<close>
  where
\<open>inclusion_isotonic_binary f = (\<forall> x x' y y'. x \<le> x' \<and> y \<le> y' \<longrightarrow> (f x y) \<le> (f x' y'))\<close>

definition inclusion_isotonic_binary_on :: \<open>('a interval \<Rightarrow> bool ) \<Rightarrow> ('a::preorder interval \<Rightarrow> 'a interval \<Rightarrow> 'b::preorder interval) \<Rightarrow> bool\<close>
  where
\<open>inclusion_isotonic_binary_on P f = (\<forall> x x' y y'. P x \<and> P x' \<and> P y \<and> P y' \<and> x \<le> x' \<and> y \<le> y' \<longrightarrow> (f x y) \<le> (f x' y'))\<close>

lemma inclusion_isotonic_binary_eq: \<open>inclusion_isotonic_binary_on (\<lambda> x . True) = inclusion_isotonic_binary\<close>
  unfolding inclusion_isotonic_binary_on_def inclusion_isotonic_binary_def
  by simp

definition inclusion_isotonicM_n :: \<open>nat \<Rightarrow> ('a::linorder interval list \<Rightarrow> 'a::linorder interval) \<Rightarrow> bool\<close> where
  \<open>inclusion_isotonicM_n n f = (\<forall> is js. (length is =  n \<and> length js = n  \<and> (is \<le>\<^sub>I js)) \<longrightarrow> f is \<le> f js)\<close>

definition inclusion_isotonicM_n_on :: \<open>('a interval \<Rightarrow> bool) \<Rightarrow>  nat \<Rightarrow> ('a::linorder interval list \<Rightarrow> 'a::linorder interval) \<Rightarrow> bool\<close> where
  \<open>inclusion_isotonicM_n_on P n f = (\<forall> is js. (\<forall> i \<in> set is. P i) \<and> (\<forall> j \<in> set js. P j) \<and> (length is =  n \<and> length js = n  \<and> (is \<le>\<^sub>I js)) \<longrightarrow> f is \<le> f js)\<close>


lemma inclusion_isotonicM_n_eq: \<open>inclusion_isotonicM_n_on (\<lambda> x . True) = inclusion_isotonicM_n\<close>
  unfolding inclusion_isotonicM_n_on_def inclusion_isotonicM_n_def
  by simp

text\<open>Finally, we extend the definition to functions over lists and show that the three definitions of 
interval inclusion isotonicity are, for their corresponding types, equivalent:\<close>

locale inclusion_isotonicM =
  fixes  n :: nat 
     and f :: \<open>('a::linorder) interval list \<Rightarrow> 'a interval list\<close>
  assumes inclusion_isotonicM :
  \<open>(\<forall> is js. (length is = n) \<and>(length js = n) \<and> (is \<le>\<^sub>I js) \<longrightarrow> f is \<le>\<^sub>I f js)\<close>
begin 
end

locale inclusion_isotonicM_on =
  fixes  P :: \<open>'a::linorder interval \<Rightarrow> bool\<close>
     and n :: nat 
     and f :: \<open>('a::linorder) interval list \<Rightarrow> 'a interval list\<close>
  assumes inclusion_isotonicM :
  \<open>(\<forall> is js. (\<forall> i \<in> set is. P i) \<and> (\<forall> j \<in> set js. P j) \<and> (length is = n) \<and>(length js = n) \<and> (is \<le>\<^sub>I js) \<longrightarrow> f is \<le>\<^sub>I f js)\<close>
begin 
end

lemma inclusion_isotonicM_on_eq: \<open>inclusion_isotonicM_on (\<lambda> x. True) = inclusion_isotonicM\<close>
  unfolding inclusion_isotonicM_on_def inclusion_isotonicM_def
  by simp  

lemma inclusion_isotonic_conv:
  \<open>inclusion_isotonic g = inclusion_isotonicM 1 (\<lambda> xs . case xs  of [x] \<Rightarrow>  [g x])\<close>
  unfolding inclusion_isotonic_def inclusion_isotonicM_def
  by(auto simp add: le_interval_single split:list.split)

lemma inclusion_isotonicM_n_conv1:
  \<open>inclusion_isotonicM_n n f = inclusion_isotonicM n (\<lambda> xs. [f xs])\<close>
  unfolding  inclusion_isotonicM_n_def inclusion_isotonicM_def le_interval_list_def 
  by(auto)

lemma inclusion_isotonicM_conv2:
  assumes \<open>inclusion_isotonicM n f\<close>
  and \<open>\<forall> xs. (length xs = n) \<longrightarrow> N = (length (f xs))\<close>  
shows \<open>inclusion_isotonicM n (\<lambda> xs. if n' < N then [(f xs)!n'] else [])\<close>
  using assms unfolding inclusion_isotonicM_def 
  apply(simp split:if_splits, safe)
  apply(subst le_interval_single[symmetric])
  apply(subst le_interval_list_all)
  subgoal by blast 
  subgoal by blast 
  subgoal by(rule TrueI)
done 

lemma inclusion_isotonicM_n_on_conv1:
  \<open>inclusion_isotonicM_n_on P n f = inclusion_isotonicM_on P n (\<lambda> xs. [f xs])\<close>
  unfolding  inclusion_isotonicM_n_on_def inclusion_isotonicM_on_def le_interval_list_def 
  by(auto)

lemma inclusion_isotonicM_on_conv2:
  assumes \<open>inclusion_isotonicM_on P n f\<close>
  and \<open>\<forall> xs. (length xs = n) \<longrightarrow> N = (length (f xs))\<close>  
shows \<open>inclusion_isotonicM_on P n (\<lambda> xs. if n' < N then [(f xs)!n'] else [])\<close>
  using assms unfolding inclusion_isotonicM_on_def 
  apply(simp split:if_splits, safe)
  apply(subst le_interval_single[symmetric])
  apply(subst le_interval_list_all)
  subgoal by blast 
  subgoal by blast 
  subgoal by(rule TrueI)
done 

lemma inclusion_isotonic_binary_conv1: 
  \<open>inclusion_isotonic_binary f = inclusion_isotonicM_n 2 (\<lambda> xs . case xs  of [x,y] \<Rightarrow>  f x y)\<close>
  unfolding inclusion_isotonic_binary_def inclusion_isotonicM_n_def le_interval_list_def
  by(auto simp add: le_interval_list_def split:list.split)

lemma inclusion_isotonic_binary_conv2: 
  \<open>inclusion_isotonic_binary f = inclusion_isotonicM 2 (\<lambda> xs . case xs  of [x,y] \<Rightarrow>  [f x y])\<close>
  apply(simp add: inclusion_isotonic_binary_conv1)
  apply(simp add: inclusion_isotonicM_n_conv1)
  unfolding inclusion_isotonicM_def 
  by(auto split:list.split)

lemma inclusion_isotonic_binary_on_conv1: 
  \<open>inclusion_isotonic_binary_on P f = inclusion_isotonicM_n_on P 2 (\<lambda> xs . case xs  of [x,y] \<Rightarrow>  f x y)\<close>
  unfolding inclusion_isotonic_binary_on_def inclusion_isotonicM_n_on_def le_interval_list_def
  by(auto simp add: le_interval_list_def split:list.split)

lemma inclusion_isotonic_binary_on_conv2: 
  \<open>inclusion_isotonic_binary_on P f = inclusion_isotonicM_on P 2 (\<lambda> xs . case xs  of [x,y] \<Rightarrow>  [f x y])\<close>
  apply(simp add: inclusion_isotonic_binary_on_conv1)
  apply(simp add: inclusion_isotonicM_n_on_conv1)
  unfolding inclusion_isotonicM_on_def 
  by(auto split:list.split)


subsection\<open>Compositionality of Interval Inclusion Isotonicy\<close>

lemma inclusion_isotonicM_comp: 
  assumes \<open>inclusion_isotonicM n f\<close> 
      and \<open>inclusion_isotonicM m g\<close>
      and \<open>\<forall> xs. length xs = n \<longrightarrow> length (f xs) = m\<close>
  shows \<open>inclusion_isotonicM n (g o f)\<close>
  using assms unfolding inclusion_isotonicM_def 
  by(simp)

lemma inclusion_isotonicM_on_comp: 
  assumes \<open>inclusion_isotonicM_on P n f\<close> 
      and \<open>inclusion_isotonicM_on Q m g\<close>
      and \<open>\<forall> xs. length xs = n \<longrightarrow> length (f xs) = m\<close>
      and \<open>\<forall> is. (\<forall> i \<in> set is. P i) \<longrightarrow> (\<forall>x\<in>set (f is). Q x)\<close>
shows \<open>inclusion_isotonicM_on P n (g o f)\<close>
  using assms  unfolding inclusion_isotonicM_on_def  o_def
  by(auto)

lemma inclusion_isotonic_comp: 
  assumes \<open>inclusion_isotonic f\<close> 
      and \<open>inclusion_isotonic g\<close>
  shows \<open>inclusion_isotonic (g o f)\<close>
  using assms unfolding inclusion_isotonic_def 
  by(simp)

lemma inclusion_isotonic_on_comp: 
  assumes \<open>inclusion_isotonic_on P f\<close> 
      and \<open>inclusion_isotonic_on Q g\<close>
      and \<open>\<forall> x. P x \<longrightarrow> Q (f x)\<close>
shows \<open>inclusion_isotonic_on P (g o f)\<close>
  using assms unfolding inclusion_isotonic_on_def 
  by(simp)

subsection\<open>Interval Inclusion Isontonicity of the Core Operator\<close>

subsubsection\<open>Unary Minus (Negation)\<close>

lemma inclusion_isotonicM_uminus[simp]: \<open>inclusion_isotonic uminus\<close>
  by (simp add: inclusion_isotonic_def less_eq_interval_def)

subsubsection\<open>Addition\<close>

lemma inclusion_isotonicM_plus[simp]: \<open>inclusion_isotonic_binary (+)\<close> 
  by (simp add: inclusion_isotonic_binary_def less_eq_interval_def add_mono) 

subsubsection\<open>Substraction\<close>

lemma inclusion_isotonicM_minus[simp]: \<open>inclusion_isotonic_binary (-)\<close> 
  by (simp add: inclusion_isotonic_binary_def less_eq_interval_def diff_mono) 

subsubsection\<open>Multiplication\<close>

lemma inclusion_isotonicM_times[simp]: 
  \<open>inclusion_isotonic_binary  (\<lambda> x y. (x::'a::{linordered_ring, real_normed_algebra, linear_continuum_topology} interval) * y)\<close>
  unfolding inclusion_isotonic_binary_def using set_of_mul_inc interval_set_leq_eq 
  by metis 


subsection\<open>Interval Inclusion Isotonicity of Various Functions\<close>

lemma inclusion_isotonicM_n_empty[simp]: \<open>inclusion_isotonicM n (\<lambda> xs. [])\<close>
unfolding inclusion_isotonicM_def by(simp)

lemma inclusion_isotonic_id[simp]: \<open>inclusion_isotonic id\<close>
  unfolding inclusion_isotonic_def le_interval_list_def 
  by(simp)

lemma inclusion_isotonicM_id[simp]: \<open>inclusion_isotonicM n id\<close>
  unfolding inclusion_isotonicM_def le_interval_list_def 
  by(simp)

lemma inclusion_isotonicM_hd[simp]: 
  assumes \<open>0 < n\<close> 
  shows \<open>inclusion_isotonicM_n n hd\<close>
unfolding inclusion_isotonicM_n_def le_interval_list_def 
proof(insert assms, induction n rule:nat_induct_non_zero)
  case 1
  then show ?case 
    by (auto, metis (no_types, lifting) Nil_eq_zip_iff case_prodD foldl_conj_set_True hd_zip insert_iff 
       length_0_conv list.map_disc_iff list.map_sel(1) list.set(2) list.set_sel(1) nat.distinct(1))
next
  case (Suc n)
  then show ?case
    by (auto, metis (no_types, lifting) Nil_eq_zip_iff Zero_not_Suc case_prodD foldl_conj_set_True hd_zip 
              insert_iff length_0_conv list.map_disc_iff list.map_sel(1) list.set(2) list.set_sel(1))
qed

lemma inclusion_isotonic_add_const1[simp]:
  \<open>inclusion_isotonic  (\<lambda> x. x + c)\<close>
  unfolding inclusion_isotonic_def
  by (simp add: add_mono_thms_linordered_semiring(3) less_eq_interval_def) 
  
lemma inclusion_isotonicM_1_add_const2[simp]: 
  \<open>inclusion_isotonic  (\<lambda> x. c + x)\<close>
  unfolding inclusion_isotonic_def
  by (simp add: add_mono_thms_linordered_semiring(2) less_eq_interval_def) 
 
lemma inclusion_isotonic_times_right[simp]: 
  \<open>inclusion_isotonic  (\<lambda> x. C* (x::'a::linordered_ring interval))\<close>
  unfolding inclusion_isotonic_def
  using times_interval_right by auto 

lemma inclusion_isotonic_times_left[simp]:
  \<open>inclusion_isotonic  (\<lambda> x. (x::'a::{real_normed_algebra,linordered_ring,linear_continuum_topology} interval) * C)\<close>
  unfolding inclusion_isotonic_def
  using times_interval_left by auto 

lemma map_inclusion_isotonicM:
  assumes \<open>inclusion_isotonic  f\<close>
  shows  \<open>inclusion_isotonicM n (map f)\<close>
  using assms map_set map_pair_set_left map_pair_set_right map_pair_set
  unfolding inclusion_isotonicM_def le_interval_list_def inclusion_isotonic_def 
  by(simp add: foldl_conj_set_True map_pair_f_all, blast)

lemma inclusion_isotonicM_fun_plus:
  assumes \<open>inclusion_isotonic f\<close> and \<open>inclusion_isotonic g\<close>
  shows \<open>inclusion_isotonic (\<lambda> x. f x + g x)\<close>
  using assms unfolding inclusion_isotonic_def
  by (simp add: add_mono_thms_linordered_semiring(1) less_eq_interval_def) 

lemma inclusion_isotonic_plus_const:
  assumes \<open>inclusion_isotonic f\<close> and \<open>inclusion_isotonic g\<close>
  shows \<open>inclusion_isotonic (\<lambda> x. g x + c)\<close>
  using assms unfolding inclusion_isotonic_def
  by (simp add: add_mono_thms_linordered_semiring(1) less_eq_interval_def) 

lemma inclusion_isotonic_times_const_real:
  assumes \<open>inclusion_isotonic f\<close>
  shows \<open>inclusion_isotonic (\<lambda> x. (c::real interval) * (f x))\<close>
  using inclusion_isotonic_comp  assms 
  unfolding inclusion_isotonic_def
  by (simp add: times_interval_right)  

lemma intervall_le_foldr: 
  assumes \<open>inclusion_isotonic_binary f\<close>
  shows \<open>length js = length is \<Longrightarrow> is \<le>\<^sub>I js \<Longrightarrow> (foldr f is e) \<le> (foldr f js e)\<close>
proof (induction rule:list_induct2)
  case Nil
  then show ?case 
    by (simp add: less_eq_interval_def)     
next
  case (Cons x xs y ys)
  then show ?case 
    unfolding le_interval_list_def
    by (simp, metis (no_types, lifting) assms foldl_conj_True inclusion_isotonic_binary_def 
        list_all_simps(1))
qed

lemma intervall_le_foldr_map: 
  assumes \<open>inclusion_isotonic_binary f\<close>
  and \<open>inclusion_isotonic g\<close>
  shows \<open>length js = length is \<Longrightarrow> is \<le>\<^sub>I js \<Longrightarrow> (foldr f (map g is) e) \<le> (foldr f (map g js) e)\<close>
proof (induction rule:list_induct2)
  case Nil
  then show ?case 
    by (simp add: less_eq_interval_def)
next
  case (Cons x xs y ys)
  then show ?case 
    using assms unfolding inclusion_isotonicM_n_def le_interval_list_def
    by(simp add: foldl_conj_True inclusion_isotonic_def inclusion_isotonic_binary_def) 
qed

lemma intervall_le_foldr_e: 
  assumes \<open>inclusion_isotonic_binary f\<close>
  and \<open>is \<le> js\<close>
  shows \<open>(foldr f xs is) \<le> (foldr f xs js)\<close>
proof (induction xs)
  case Nil
  then show ?case using assms by(simp)     
next
  case (Cons x)
  then show ?case
    using assms unfolding le_interval_list_def inclusion_isotonic_binary_def
    by (simp add: less_eq_interval_def) 
 qed

lemma foldr_inclusion_isotonicM_e:
  assumes \<open>inclusion_isotonic_binary f\<close>
  shows \<open>\<forall> x. inclusion_isotonic  (foldr f x)\<close>
  using assms 
  unfolding inclusion_isotonic_def
  by(simp add: intervall_le_foldr_e)

lemma foldr_inclusion_isotonicM:
  assumes \<open>inclusion_isotonic_binary f\<close>
  shows \<open>inclusion_isotonicM_n n (\<lambda> x. foldr f x e)\<close>
  using assms 
  unfolding inclusion_isotonicM_n_def using  intervall_le_foldr
  by auto 

lemma foldr_inclusion_isotonicM_g:
  assumes \<open>inclusion_isotonic_binary f\<close>
  and     \<open>inclusion_isotonicM n g\<close>
  shows \<open>inclusion_isotonicM_n n (\<lambda> x. foldr f ((g x)) e)\<close>
  using assms(2)
  unfolding inclusion_isotonicM_n_def inclusion_isotonicM_def  
  by (metis assms(1) intervall_le_foldr le_interval_list_imp_length)

lemma foldr_map_inclusion_isotonicM_g:
  assumes \<open>inclusion_isotonic_binary f\<close>
  and     \<open>inclusion_isotonic g \<close>  
  and     \<open>inclusion_isotonicM n P\<close>
  shows \<open>inclusion_isotonicM_n n (\<lambda> x. foldr f (map g (P x)) e)\<close>
  using intervall_le_foldr_map assms(3)
  unfolding inclusion_isotonicM_n_def  inclusion_isotonicM_def
  by (metis (no_types, lifting) assms(1) assms(2) intervall_le_foldr_map le_interval_list_imp_length) 

lemma foldl_inclusion_isotonicM:
  assumes \<open>inclusion_isotonic_binary f\<close>
  shows \<open>inclusion_isotonicM_n n (foldl f e)\<close>
  unfolding inclusion_isotonicM_n_def
  apply(subst foldl_conv_foldr)
  apply(subst foldl_conv_foldr)
  using assms foldr_inclusion_isotonicM[simplified inclusion_isotonicM_def]
        le_interval_list_rev length_rev
  unfolding inclusion_isotonicM_n_def inclusion_isotonic_binary_def
  by (metis)

lemma fold_inclusion_isotonicM:
  assumes \<open>inclusion_isotonic_binary f\<close>
  shows \<open>inclusion_isotonicM_n n (\<lambda> x. fold f x e)\<close>
  unfolding inclusion_isotonicM_n_def
  apply(subst foldl_conv_fold[symmetric])
  apply(subst foldl_conv_fold[symmetric])
  using assms foldl_inclusion_isotonicM[simplified inclusion_isotonicM_def]
  unfolding inclusion_isotonic_binary_def inclusion_isotonicM_n_def
  by (metis) 


lemma map2_inclusion_isotonicM_left: assumes  \<open>inclusion_isotonic_binary f\<close>
         shows \<open>inclusion_isotonicM n (map2 f xs)\<close>
  unfolding inclusion_isotonicM_def inclusion_isotonic_binary_def
  apply(safe,subst le_interval_list_all2, simp_all)
  using le_interval_list_imp le_interval_list_all 
  by (metis assms dual_order.refl inclusion_isotonic_binary_def less_eq_interval_def)

lemma map2_inclusion_isotonicM_right: assumes  \<open>inclusion_isotonic_binary f\<close>
         shows \<open>inclusion_isotonicM n (\<lambda> ys. map2 f ys xs)\<close>
  unfolding inclusion_isotonicM_def inclusion_isotonic_binary_def
  apply(safe,subst le_interval_list_all2, simp_all)
  using le_interval_list_imp le_interval_list_all 
  by (metis assms dual_order.refl inclusion_isotonic_binary_def less_eq_interval_def)
                           

lemma map2_inclusion_isotonicM_right_g: 
  assumes  \<open>inclusion_isotonic_binary f\<close>
   and \<open>\<forall> xs. length (g xs) = length xs\<close>
   and \<open>inclusion_isotonicM n  g\<close>
   and \<open>length xs = n\<close>
   and \<open>length is = n\<close> 
   and \<open>length js = n\<close> 
   and \<open>is \<le>\<^sub>I js\<close> 
  shows\<open>map2 f (g is) (h xs) \<le>\<^sub>I map2 f (g js) (h xs)\<close>
  using assms unfolding inclusion_isotonic_binary_def
  apply(subst le_interval_list_all2, simp_all)
  using assms unfolding inclusion_isotonic_binary_def  
  by (metis dual_order.refl inclusion_isotonicM_def
            le_interval_list_imp less_eq_interval_def) 

lemma inclusion_isotonicM_map: 
  assumes \<open>\<forall> x \<in> set xs . g x \<le> h x\<close>
  shows \<open>(map g xs) \<le>\<^sub>I (map h xs)\<close>
  using assms by(subst le_interval_list_all2, simp_all)

section \<open>Interval Extension and Inclusion Properties\<close>

lemma interval_extension_inclusion:
  assumes \<open>F is_interval_extension_of f\<close>
  shows \<open>\<forall> X . interval_of (f X) \<le> F (interval_of X)\<close>
  using assms
  unfolding is_interval_extension_of_def 
  by (simp add: in_interval_to_interval interval_of_in_eq)

lemma interval_extension_subset_const:
  assumes interval_ext_F: \<open>F is_interval_extension_of f\<close>
  shows \<open>\<forall> X . set_of (interval_of (f X)) \<subseteq> set_of (F (interval_of X))\<close>
  using assms
  unfolding is_interval_extension_of_def set_of_def by auto

lemma fundamental_theorem_of_interval_analysis:
  fixes F :: \<open>real interval \<Rightarrow> real interval\<close>
  assumes interval_ext_F: \<open>F is_interval_extension_of f\<close> 
   and   inc_isontonic_F: \<open>inclusion_isotonic F\<close> 
shows \<open>\<forall> X . f ` (set_of X) \<subseteq> set_of (F X)\<close>
proof
  fix X
  show \<open> f ` (set_of X) \<subseteq> set_of (F X)\<close>
  proof
    fix y
    assume \<open>y \<in> f ` (set_of X)\<close>
    then obtain x where i: \<open>x \<in> set_of X\<close> and \<open>y = f x\<close> by auto
    then have \<open>interval_of (f x) = F (interval_of x)\<close> using assms unfolding is_interval_extension_of_def by simp
    then have \<open>y \<in> set_of (F (interval_of x))\<close> using \<open>y = f x\<close> by (metis in_interval_to_interval)
    then have \<open>interval_of x \<le> X\<close> using \<open>x \<in> set_of X\<close> using interval_of_in_eq by blast
    then have \<open>F (interval_of x) \<le> F X\<close> using inc_isontonic_F unfolding inclusion_isotonic_def by simp 
    then show \<open>y \<in> set_of (F X)\<close> using \<open>y \<in> set_of(F (interval_of x))\<close> using set_of_subset_iff' by auto 
  qed
qed 

lemma interval_extension_bounds:
  assumes "inclusion_isotonic F"
  and "F is_interval_extension_of f"
  shows "(\<forall> x \<in> set_of X. lower (F X) \<le>  f x) \<or> (\<forall>x \<in> set_of X. f x \<le> lower (F X))"
  using assms 
  by (metis (no_types, lifting) in_bounds inclusion_isotonic_def interval_of_in_eq 
                                is_interval_extension_of_def) 

lemma inclusion_isotonic_extension_subset:
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows \<open>(f ` set_of X) \<subseteq> set_of (F X)\<close>
  using assms interval_of_in_eq   
  unfolding inclusion_isotonic_def set_of_eq is_interval_extension_of_def 
  by (metis (mono_tags, lifting) image_subsetI) 

lemma inclusion_isotonic_extension_includes:
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows \<open>\<forall> x \<in> set_of X. f x \<in> set_of (F X)\<close>
  using assms inclusion_isotonic_extension_subset
  by blast  

lemma inclusion_isotonic_extension_lower_bound:
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows \<open>\<forall> x \<in> set_of X. lower (F X) \<le> f x\<close>
  using assms inclusion_isotonic_extension_includes
  using in_bounds by blast 

lemma inclusion_isotonic_extension_upper_bound:
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows \<open>\<forall> x \<in> set_of X. f x \<le> upper (F X)\<close>
  using assms inclusion_isotonic_extension_includes
  using in_bounds by blast 


lemma inclusion_isotonic_inf:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows \<open>lower (F (X::real interval)) \<le> Inf (f ` set_of X)\<close>
  using inclusion_isotonic_extension_subset[of F f X, simplified assms]
  cInf_superset_mono[of "f ` set_of X"  "set_of (F X)"]
  by (simp add: bdd_below_set_of  inf_set_of)

lemma inclusion_isotonic_sup:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows \<open>Sup (f ` set_of X) \<le> upper (F X)\<close>
  using inclusion_isotonic_extension_subset[of F f X, simplified assms]  
        cSup_subset_mono[of "f ` set_of X" "set_of (F X)"]
  by (simp add: bdd_above_set_of sup_set_of)

lemma lower_inf:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows "Inf (f ` set_of X) \<le> f (lower X)"
  using cInf_superset_mono[of "{f (lower X)}" "f ` set_of X"]
  by (metis assms(1) assms(2) bdd_below_mono bdd_below_set_of bot.extremum 
                     cInf_singleton imageI insert_not_empty insert_subsetI 
                     fundamental_theorem_of_interval_analysis lower_in_interval) 
lemma upper_sup:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows "f (upper X) \<le> Sup (f ` set_of X)"
  using cSup_subset_mono[of "{f (upper X)}" "f ` set_of X"]
  by (meson assms(1) assms(2) bdd_above_mono bdd_above_set_of cSup_upper 
            imageI fundamental_theorem_of_interval_analysis upper_in_interval) 
  
lemma lower_F_f:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows "lower (F X) \<le> f (lower X)"
  by (simp add: assms(1) assms(2) inclusion_isotonic_extension_lower_bound) 
  
lemma upper_F_f:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  
  and "F is_interval_extension_of f"
  shows "f (upper X) \<le> upper (F X)"
  by (simp add: assms(1) assms(2) inclusion_isotonic_extension_upper_bound)

lemma inclusion_isotonic_interval_extension_le:
    assumes inclusion_isotonic: \<open>inclusion_isotonic F\<close>
  and       interval_extension: \<open>F is_interval_extension_of f\<close>
  and       adjacent: \<open>upper a = lower b\<close>
shows \<open>lower (F b) \<le> upper (F a)\<close>
  using inclusion_isotonic_extension_lower_bound[of F f, simplified assms, simplified]  
        inclusion_isotonic_extension_upper_bound[of F f, simplified assms, simplified]
        le_left_mono lower_in_interval upper_in_interval
  by(metis adjacent)


section\<open>Division\<close>

context interval_division_inverse
begin 
lemma inclusion_isotonic_on_inverse[simp]:
  \<open>inclusion_isotonic_on (\<lambda> x . \<not> 0 \<in>\<^sub>i x) ((inverse::('a interval \<Rightarrow> 'a interval)))\<close>
  using inverse_non_zero_def
  unfolding inclusion_isotonic_on_def less_eq_interval_def
  by (smt (z3) dual_order.trans in_bounds in_intervalI lower_le_upper mk_interval_lower 
      mk_interval_upper upper_leq_lower_div)

lemma inclusion_isotonic_on_division[simp]:
  \<open>inclusion_isotonic_binary_on (\<lambda> x . \<not> 0 \<in>\<^sub>i x)  (\<lambda> x y. divide x y)\<close>
  using inclusion_isotonicM_times  divide_non_zero_def inclusion_isotonic_on_inverse
  unfolding  o_def inclusion_isotonic_binary_on_def
            inclusion_isotonic_on_def inclusion_isotonic_binary_def
  by metis 

end 

end 
