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

chapter\<open>Subdivisions and Refinements\<close>

theory 
  Lipschitz_Subdivisions_Refinements
  imports 
  Lipschitz_Interval_Extension
  Multi_Interval_Preliminaries
begin

section \<open>Subdivisions\<close>

text \<open>A uniform subdivision of an interval @{term \<open>X\<close>} splits @{term \<open>X\<close>} into a vector of equal 
length, contiguous intervals.\<close>

definition uniform_subdivision :: "'a::linordered_field interval \<Rightarrow> nat \<Rightarrow> 'a interval list" where
"uniform_subdivision A n = map (\<lambda>i. let i' = of_nat i in 
                                     mk_interval (lower A + (upper A - lower A) *  i' /  of_nat n, 
                                                  lower A + (upper A - lower A) * (i' + 1) /  of_nat n)) [0..<n]"

text \<open>The definition @{term "uniform_subdivision"} refers to definition 6.2 
in~\<^cite>\<open>"moore.ea:introduction:2009"\<close>\<close>

definition overlapping_ordered :: "'a::{preorder} interval list \<Rightarrow> bool" where
"overlapping_ordered xs = (\<forall>i. i < length xs - 1 \<longrightarrow>  lower (xs ! (i + 1)) \<le> upper (xs ! i))"

definition overlapping_non_zero_width :: "'a::{preorder, minus, zero, ord} interval list \<Rightarrow> bool" where
"overlapping_non_zero_width xs = (\<forall> i < length xs - 1 . \<exists> e. e \<in>\<^sub>i (xs ! (i + 1)) \<and> e \<in>\<^sub>i (xs ! i) \<and> 0 < width (xs ! (i + 1)) \<and> 0 < width (xs ! i ) ) "

definition overlapping :: "'a::{preorder} interval list \<Rightarrow> bool" where
"overlapping xs = (\<forall> i < length xs - 1 . \<exists> e. e \<in>\<^sub>i (xs ! (i + 1)) \<and> e \<in>\<^sub>i (xs ! i)) "

definition check_is_uniform_subdivision :: "'a::linordered_field interval \<Rightarrow> 'a interval list \<Rightarrow> bool" where
"check_is_uniform_subdivision A xs = (let n = length xs in 
                                      if n = 0 then True 
                                      else 
                                        let d = width A / of_nat n in
                                        list_all (\<lambda> x. width x = d) xs \<and> 
                                        contiguous xs \<and>
                                        lower (hd xs) = lower A \<and> 
                                        upper (last xs) = upper A)"

lemma non_empty_subdivision:
  assumes "0 < n"
  shows "uniform_subdivision A n \<noteq> []"
  unfolding uniform_subdivision_def using assms by simp

lemma uniform_subdivision_id: "uniform_subdivision X 1 = [X]"
  unfolding uniform_subdivision_def by simp

lemma subdivision_length_n:
  assumes "0 < n"
  shows "length(uniform_subdivision A n) = n"
  using assms
proof(induction n rule:nat_induct_non_zero)
  case 1
  then show ?case unfolding uniform_subdivision_def by simp
next
  case (Suc n)
  then show ?case unfolding uniform_subdivision_def by simp
qed

lemma contiguous_uniform_subdivision: "contiguous (uniform_subdivision A n)"
proof -
  have a0: "\<forall>i<length (uniform_subdivision A n) - 1. 
            upper (uniform_subdivision A n ! i) = lower A + (upper A - lower A) * of_nat (i + 1) / of_nat n"
    by (simp add: uniform_subdivision_def divide_right_mono mult_left_mono) 
  have a1: "\<forall>i<length (uniform_subdivision A n) - 1.  
            lower A + (upper A - lower A) * of_nat (i + 1) / of_nat n = lower (uniform_subdivision A n ! (i + 1))"
    by (simp add: uniform_subdivision_def divide_right_mono mult_left_mono) 
  have a2: "\<forall>i<length (uniform_subdivision A n) - 1. 
            upper (uniform_subdivision A n ! i) = lower (uniform_subdivision A n ! (i + 1))"
    using a0 a1 by simp
  have a3: "contiguous (uniform_subdivision A n) = 
            (\<forall>i<length (uniform_subdivision A n) - 1. 
             upper (uniform_subdivision A n ! i) = lower (uniform_subdivision A n ! (i + 1)))"
    unfolding contiguous_def by simp
  show ?thesis using a0 a1 a2 a3 by simp
qed



lemma overlapping_ordered_uniform_subdivision:   
  assumes "0 < n"
  shows "overlapping_ordered (uniform_subdivision A n)"
proof - 
  have a0: "\<forall>i<length (uniform_subdivision A n) - 1. 
            upper (uniform_subdivision A n ! i) \<ge> lower A + (upper A - lower A) * of_nat (i + 1) / of_nat n"
    using assms 
    by (simp add: uniform_subdivision_def divide_right_mono mult_left_mono) 
  have a1: "\<forall>i<length (uniform_subdivision A n) - 1.  
            lower A + (upper A - lower A) * of_nat (i + 1) / of_nat n \<ge> lower (uniform_subdivision A n ! (i + 1))"
    using assms 
    by (simp add: uniform_subdivision_def divide_right_mono mult_left_mono) 
  have a2: "\<forall>i<length (uniform_subdivision A n) - 1. 
            upper (uniform_subdivision A n ! i) \<ge> lower (uniform_subdivision A n ! (i + 1))"
    using a0 a1 by force
  have a3: "overlapping_ordered (uniform_subdivision A n) = 
            (\<forall>i<length (uniform_subdivision A n) - 1. 
             upper (uniform_subdivision A n ! i) \<ge> lower (uniform_subdivision A n ! (i + 1)))"
    unfolding overlapping_ordered_def by simp
  show ?thesis using a0 a1 a2 a3 by simp
qed

lemma overlapping_uniform_subdivision:
  assumes "0 < N"
  shows "overlapping (uniform_subdivision X N)"
  using assms
proof - 
  let ?n = "length (uniform_subdivision X N) - 1"
  have a0: "\<forall> i < ?n . lower (uniform_subdivision X N ! (i + 1)) = upper (uniform_subdivision X N ! i)"
    using assms contiguous_uniform_subdivision unfolding contiguous_def by metis
  have a1: "\<forall> i < ?n. upper (uniform_subdivision X N ! i) \<in>\<^sub>i uniform_subdivision X N ! i
                    \<and> upper (uniform_subdivision X N ! i) \<in>\<^sub>i (uniform_subdivision X N ! (i + 1))"
    using a0 in_intervalI lower_le_upper order.refl
    by metis
  have a2: "\<forall>i< ?n. \<exists>e. e \<in>\<^sub>i uniform_subdivision X N ! (i + 1) \<and> e \<in>\<^sub>i uniform_subdivision X N ! i" 
    using a1 by auto[1]
  show ?thesis using a2 unfolding overlapping_def by simp
qed 

lemma hd_lower_uniform_subdivision:
  assumes "0 < n"
  shows "lower ( hd (uniform_subdivision A n)) = lower A"
proof -
  have "lower ( hd (uniform_subdivision A n)) = lower A + (upper A - lower A) * of_nat 0 / of_nat n"
    using assms
    by (simp add: uniform_subdivision_def mk_interval' hd_map)  
  also have "... = lower A"
    by simp
  finally show ?thesis .
qed

lemma last_upper_uniform_subdivision:
  assumes "0 < n"
  shows "upper ( last (uniform_subdivision A n)) = upper A"
proof -
  have "upper ( last (uniform_subdivision A n)) = lower A + (upper A - lower A) * of_nat n / of_nat n"
    using assms
    apply (auto simp add: uniform_subdivision_def mk_interval' last_map Let_def)[1] 
    using One_nat_def Suc_pred' add.commute le_add_diff_inverse lower_le_upper 
      nonzero_mult_div_cancel_right of_nat_0_less_iff of_nat_Suc order_less_irrefl apply metis
    by ( simp add: divide_right_mono mult_left_mono) 
    also have "... = upper A"
    using assms by simp
  finally show ?thesis .
qed

lemma uniform_subdivisions_width_single:
  fixes A ::"'a::linordered_field interval"
  shows \<open>width (Interval (lower A + (upper A - lower A) *  x / of_nat n,
                    lower A + (upper A - lower A) * (x + 1) /  of_nat n)) =  width A / of_nat n\<close>
proof - 
  have "lower A \<le> upper A " using lower_le_upper by simp
  then have leq: "lower A + (upper A - lower A) *  x /  of_nat n \<le> 
             lower A + (upper A - lower A) * ( x + 1) /  of_nat n"
    by (simp add: divide_le_cancel linorder_not_less mult_le_cancel_left)
  have U: \<open>upper (Interval (lower A + (upper A - lower A) *  x / of_nat n,
                            lower A + (upper A - lower A) * ( x + 1) /  of_nat n)) = 
           lower A + (upper A - lower A) * ( x + 1) / of_nat n\<close>
    using upper_bounds leq by blast 
  have L: \<open>lower (Interval (lower A + (upper A - lower A) *  x / of_nat n,
                            lower A + (upper A - lower A) * ( x + 1) / of_nat n)) = 
           lower A + (upper A - lower A) *  x / of_nat n\<close>
    using lower_bounds leq by blast
  then show ?thesis using U L add_diff_cancel_left add_diff_cancel_left' diff_divide_distrib 
      mult.comm_neutral vector_space_over_itself.scale_right_diff_distrib unfolding width_def  
    by metis
qed

lemma uniform_subdivisions_width:
  assumes "0 < n" 
  shows \<open>\<forall> A. A \<in> set (uniform_subdivision X n) \<longrightarrow> width A = width X / of_nat n\<close>
  apply (simp add: uniform_subdivision_def mk_interval' o_def image_def width_def Let_def split: if_split)
  apply auto[1]
  apply (metis add_diff_cancel_left' diff_divide_distrib mult.right_neutral right_diff_distrib)
  using assms uniform_subdivisions_width_single[simplified width_def] 
  by (simp add: divide_right_mono mult_left_mono) 

lemma uniform_subdivision_sum_width:
  assumes \<open>0 < n\<close>
  shows \<open>sum_list (map width (uniform_subdivision X n)) = width X\<close>
proof -
  have \<open>\<forall> a . a \<in> set (uniform_subdivision X n) \<longrightarrow> width a = width X / of_nat n \<close>
    using uniform_subdivisions_width using assms by blast
  then have width: "\<forall> a . a \<in> set (map width (uniform_subdivision X n)) \<longrightarrow> a = width X / of_nat n"
    unfolding width_def by auto[1]
  then have width_list: "list_all (\<lambda> a . a = width X / of_nat n) (map width (uniform_subdivision X n)) "
    unfolding width_def using list_all_iff by blast
  then have length: "length (map width (uniform_subdivision X n)) = n "
    unfolding uniform_subdivision_def by simp
  then have "sum_list (map width (uniform_subdivision X n)) = (width X / of_nat n) * of_nat n"
    using width_list by (metis list.map_ident_strong mult_of_nat_commute sum_list_triv width) 
  then show ?thesis by (simp add: assms)
qed

lemma uniform_subdivisions_distinct:
  assumes "0 < n" "0 < width A"
  shows "distinct (uniform_subdivision A n)"
proof -
  have "\<forall>i< n. \<forall>j< n. i \<noteq> j \<longrightarrow> (uniform_subdivision A n) ! i \<noteq> (uniform_subdivision A n) ! j"
  proof -
      have f1: "\<forall>i< n. \<forall>j< n. i \<noteq> j \<longrightarrow> (upper A - lower A) * of_nat i / of_nat n \<noteq> (upper A - lower A) * of_nat j / of_nat n"
        using assms(1) assms(2) divide_cancel_right less_numeral_extra(3) mult_cancel_left of_nat_eq_0_iff of_nat_eq_iff width_def 
        by metis
      have f2: "\<forall>i< n. \<forall>j< n. i \<noteq> j \<longrightarrow> lower A + (upper A - lower A) * of_nat (i + 1) / of_nat n \<noteq> lower A + (upper A - lower A) * of_nat (j + 1) / of_nat n"
        using  assms(1) assms(2) unfolding width_def by simp
      have f3: "\<forall>i<  n. lower ((uniform_subdivision A n) ! i) = lower A + (upper A - lower A) *  of_nat i / of_nat n"
        using assms by (simp add: uniform_subdivision_def divide_right_mono mult_left_mono Let_def) 
      have f5: "\<forall>i<n - 1. (upper ((uniform_subdivision A n) ! i)) = lower ((uniform_subdivision A n) ! Suc i)"
        using assms by (simp add: uniform_subdivision_def divide_right_mono mult_left_mono)
      have f6: "\<forall>j<n - 1. (upper ((uniform_subdivision A n) ! j)) = lower ((uniform_subdivision A n) ! Suc j)"
        using assms(1) f5 contiguous_uniform_subdivision unfolding contiguous_def subdivision_length_n by blast
      have "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> lower ((uniform_subdivision A n) ! i) \<noteq> lower ((uniform_subdivision A n) ! j)"
        using f1 f2 f3 by auto[1]
    then show ?thesis by metis
  qed
  then show ?thesis using assms(1) distinct_conv_nth subdivision_length_n by metis
qed

lemma uniform_subdivisions_non_overlapping:
  assumes "0 < n" 
  shows "non_overlapping_sorted (uniform_subdivision A n)"
proof -
  have "\<forall>i<n. \<forall>j<n. i < j \<longrightarrow> upper ((uniform_subdivision A n) ! i) \<le> lower ((uniform_subdivision A n) ! j)"
  proof -
    have f0: \<open>0 \<le> width A\<close> unfolding width_def lower_le_upper by simp 
      have f2: "\<forall>i<n. upper ((uniform_subdivision A n) ! i) = lower A + (upper A - lower A) * of_nat (i + 1) / of_nat n"
        using assms by (simp add: uniform_subdivision_def divide_right_mono mult_left_mono Let_def) 
      have f3: "\<forall>j<n. lower ((uniform_subdivision A n) ! j) = lower A + (upper A - lower A) * of_nat j / of_nat n"
        using assms by (simp add: uniform_subdivision_def divide_right_mono mult_left_mono Let_def) 
      have f4: "\<forall>i<n. \<forall>j<n. i < j \<longrightarrow> lower A + (upper A - lower A) * of_nat (i + 1) / of_nat n \<le> lower A + (upper A - lower A) * of_nat j / of_nat n"
        using assms divide_right_mono mult_left_mono Suc_eq_plus1 Suc_leI add_le_cancel_left 
          interval_width_positive of_nat_0_le_iff of_nat_le_iff width_def
        by metis
      have "\<forall>i<n. \<forall>j<n. i < j \<longrightarrow> upper ((uniform_subdivision A n) ! i) \<le> lower ((uniform_subdivision A n) ! j)"
        using f0 f2 f3 f4 by simp
    then show ?thesis by auto[1]
  qed
  then show ?thesis 
    unfolding non_overlapping_sorted_def cmp_non_overlapping_def 
    by (simp add: assms(1) sorted_wrt_iff_nth_less subdivision_length_n)
qed

text \<open>We prove that our uniform subdivision meets the multi-interval type\<close>

lemma uniform_subdivisions_valid_ainterval:
  assumes "0 < n" "0 < width A"
  shows "valid_mInterval_adj(uniform_subdivision A n)"
  using assms 
  unfolding valid_mInterval_adj_def 
  apply safe 
  subgoal using uniform_subdivisions_non_overlapping by blast
  subgoal using uniform_subdivisions_distinct by blast
  subgoal using non_empty_subdivision by blast
  done

lemma uniform_subdivisions_valid:
  assumes "0 < n"
  shows "check_is_uniform_subdivision A (uniform_subdivision A n)"
  unfolding check_is_uniform_subdivision_def Let_def
  apply (simp split: if_split) 
  apply safe
  subgoal using assms uniform_subdivisions_width subdivision_length_n 
    by (metis (mono_tags, lifting) Ball_set) 
  subgoal using assms contiguous_uniform_subdivision by blast
  subgoal using assms hd_lower_uniform_subdivision by blast
  subgoal using assms last_upper_uniform_subdivision by blast
  done

section \<open>Refinement\<close>

text \<open>Let @{term \<open>F(X)\<close>} be an inclusion isotonic, Lipschitz, interval extension for @{term \<open>X \<subseteq> Y\<close>}. 
A refinement @{term \<open>F\<^sub>N(X)\<close>} of @{term \<open>F(X)\<close>} is the union of interval values of @{term \<open>X\<close>} over 
the elements of a uniform subdivision of @{term \<open>X\<close>}\<close>

definition refinement :: "('a::{linordered_field,lattice} interval\<Rightarrow> 'a interval) \<Rightarrow> nat \<Rightarrow> 'a interval \<Rightarrow> 'a interval" where
\<open>refinement F N X = (interval_list_union (map F (uniform_subdivision X N)))\<close>

definition check_is_refinement where
\<open>check_is_refinement F n As B = (let I = refinement F n As in lower B \<le> lower I \<and> upper I \<le> upper B)\<close>

definition refinement_set :: "('a::{linordered_field,lattice} interval\<Rightarrow> 'a interval) \<Rightarrow> nat \<Rightarrow> 'a interval \<Rightarrow> 'a set" where
\<open>refinement_set F N X = (set_of_interval_list (map F (uniform_subdivision X N)))\<close>

text \<open>The definition @{term "refinement"} refers to definition 6.3 in~\<^cite>\<open>"moore.ea:introduction:2009"\<close>.\<close>

text \<open>The excess width of @{term "F(X)"} is  @{term "w(E(X)) = w(F(X)) - w(f(X))"}. The united 
extension @{term "f(x)"} for @{term "x \<in> X"} has zero excess width and we can compute @{term "f(x)"}
as closely as desired by computing refinements of an extension @{term "F(X)"}.\<close>

definition "width_set s = Sup s - Inf s"

lemma width_set_bounded:
  fixes X :: \<open>real set\<close>
  assumes  \<open>bdd_below X\<close> \<open>bdd_above X\<close> 
  shows \<open>\<forall> x \<in> X. \<forall> x' \<in> X. dist x x' \<le> width_set X\<close>
  using assms  sup_inf_dist_bounded
  unfolding width_set_def 
  by(simp)

lemma width_inclusion_isotonic_approx:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  "F is_interval_extension_of f"
  shows \<open>0 \<le> width (F X) - width_set (f ` set_of X)\<close>
  by (smt (verit, del_insts) assms(1) assms(2) inclusion_isotonic_inf 
          inclusion_isotonic_sup width_def width_set_def)

lemma diameter_width: 
  assumes \<open>a \<le> b\<close>
  shows \<open>diameter {a..b} = width_set {a..b}\<close>
  by (simp add: assms linorder_not_less diameter_Sup_Inf width_set_def)

lemma lipschitz_dist_diameter_limit:
  fixes S::\<open>'a::{metric_space, heine_borel} set\<close>
  and   f::\<open>'a::{metric_space, heine_borel} \<Rightarrow> 'b::{metric_space, heine_borel}\<close>
  assumes \<open>C-lipschitz_on S f\<close> and \<open>bounded S\<close> 
  shows \<open>x \<in> (f `S) \<Longrightarrow> y \<in> (f `S) \<Longrightarrow> dist x y \<le> diameter (f` S)\<close>
  using lipschitz_on_uniformly_continuous[of C S f, simplified assms]
        bounded_uniformly_continuous_image[of S f, simplified assms]
        diameter_bounded_bound[of "f ` S" x y]
  by simp 

definition excess_width_diameter :: "('a::preorder interval \<Rightarrow> real interval) \<Rightarrow> ('a \<Rightarrow> 'b::metric_space) \<Rightarrow> 'a interval \<Rightarrow> real" where
\<open>excess_width_diameter F f X = width(F X) - diameter (f ` set_of X)\<close>

definition excess_width_set :: "('a::{minus,linorder,Inf,Sup} interval \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a interval \<Rightarrow> 'a" where
\<open>excess_width_set F f X = width_set(F X) - width_set (f ` set_of X)\<close>

definition excess_width :: "('a::{minus,linorder,Inf,Sup} interval \<Rightarrow> 'a interval) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a interval \<Rightarrow> 'a" where
\<open>excess_width F f X = width(F X) - width_set (f ` set_of X)\<close>

text \<open>The definition @{term "excess_width"} refers to definition 6.4 in~\<^cite>\<open>"moore.ea:introduction:2009"\<close>\<close>

lemma  width_set_of: fixes X :: "real interval"
 shows width_set_upper_lower: \<open>width_set (set_of X) = \<bar>(lower X) - (upper X)\<bar>\<close>
  by (simp add: width_set_def set_of_eq)
 
lemma width_set_dist:
  fixes f :: "real \<Rightarrow> real"
  shows "width_set ( set_of X) =  (dist (lower X) (upper X))"
  by(simp add:set_of_eq width_set_def dist_real_def)

lemma  diameter_of: fixes X :: "real interval"
  shows diameter_upper_lower: \<open>diameter (set_of X) = \<bar>(lower X) - (upper X)\<bar>\<close>
  by (simp add: linorder_not_less set_of_eq) 

lemma diameter_dist:
  fixes X :: "real interval"
  shows "diameter ( set_of X) =  (dist (lower X) (upper X))"
  unfolding set_of_eq dist_real_def abs_real_def 
  using lower_le_upper[of X] diameter_closed_interval[of "lower X" "upper X"] 
  by argo 

lemma  bdd_below_f_set_of:
  fixes f :: "real \<Rightarrow> real"
  assumes "C-lipschitz_on X f"
  and \<open>bounded X\<close> and \<open>X \<noteq> {}\<close>
  shows \<open>bdd_below (f ` X)\<close>
  using assms atLeastAtMost_iff bdd_below.unfold bounded_imp_bdd_below image_def 
        lipschitz_bounded_image_real set_of_eq set_of_nonempty
  by simp

lemma  bdd_above_f_set_of:
  fixes f :: "real \<Rightarrow> real"
  assumes "C-lipschitz_on (X) f"  
  and \<open>bounded X\<close> and \<open>X \<noteq> {}\<close>
  shows \<open>bdd_above (f ` X)\<close>
  using assms atLeastAtMost_iff bdd_above.unfold bounded_imp_bdd_above image_def 
        lipschitz_bounded_image_real set_of_eq set_of_nonempty
  by simp

lemma diameter_image_dist: 
  fixes f::\<open>real \<Rightarrow> real\<close>
  assumes \<open>continuous_on (set_of X) f\<close>
  shows \<open>(\<exists> x\<in> set_of X.  \<exists> x'\<in> set_of X . diameter (f ` set_of X) =  dist (f x) (f x'))\<close>
  using assms compact_continuous_image[of "set_of X" f, simplified assms compact_set_of[of X]]  
        lower_le_upper[of X] diameter_closed_interval[of "f (lower X)" "f(upper X)", symmetric] 
        diameter_compact_attained[of "f ` set_of X"] set_f_nonempty[of f X] 
  by fastforce 

lemma excess_width_inf_diameter:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  "F is_interval_extension_of f" \<open> C-lipschitz_on (set_of X) f\<close>
  shows \<open>dist (Inf (f ` set_of X)) (lower (F X)) \<le> excess_width_diameter F f X\<close> 
      unfolding dist_real_def abs_real_def excess_width_diameter_def  width_def
      using inclusion_isotonic_inf[of F f X, simplified assms]
            inclusion_isotonic_sup[of F f X, simplified assms]
            diameter_Sup_Inf[of "f ` set_of X", simplified assms lipschitz_on_continuous_on[of C "(set_of X)" f]
                                                compact_img_set_of[of X f], simplified] 
      by simp 

lemma excess_width_inf:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  "F is_interval_extension_of f" \<open> C-lipschitz_on (set_of X) f\<close>
  shows \<open>dist (Inf (f ` set_of X)) (lower (F X)) \<le> excess_width F f X\<close> 
      unfolding dist_real_def abs_real_def excess_width_def  width_def
      using inclusion_isotonic_inf[of F f X, simplified assms]
            inclusion_isotonic_sup[of F f X, simplified assms]
      by (simp add: width_set_def)


lemma excess_width_sup_diameter:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  "F is_interval_extension_of f" \<open> C-lipschitz_on (set_of X) f\<close>
  shows \<open>dist (Sup (f ` set_of X)) (upper (F X)) \<le> excess_width F f X\<close> 
      unfolding dist_real_def abs_real_def excess_width_diameter_def  width_def
      using inclusion_isotonic_inf[of F f X, simplified assms]
            inclusion_isotonic_sup[of F f X, simplified assms]
            diameter_Sup_Inf[of "f ` set_of X", simplified assms lipschitz_on_continuous_on[of C "(set_of X)" f]
                                                compact_img_set_of[of X f], simplified] 
      by (simp add: excess_width_def width_def width_set_def) 

lemma excess_width_sup:
  fixes F::\<open>real interval \<Rightarrow> real interval\<close>
  assumes  "inclusion_isotonic F"  "F is_interval_extension_of f" \<open> C-lipschitz_on (set_of X) f\<close>
  shows \<open>dist (Sup (f ` set_of X)) (upper (F X)) \<le> excess_width F f X\<close> 
      unfolding dist_real_def abs_real_def excess_width_def  width_def
      using inclusion_isotonic_inf[of F f X, simplified assms]
            inclusion_isotonic_sup[of F f X, simplified assms]
      by (simp add: width_set_def) 

text \<open>If @{term "F(X)"} is an inclusion isotonic, Lipschitz, interval extension then the excess 
width of a refinement is of order @{term \<open>1/N\<close>}\<close>

text \<open>If @{term \<open>X\<close> } and @{term \<open>X\<close> } are intervals such that @{term \<open>X \<subseteq> Y\<close>}, then there is 
an interval @{term \<open>E\<close> } with @{term \<open>lower E \<le> 0 \<and> 0 \<le> upper E\<close> } such that 
@{term \<open>Y = X + E\<close>} and @{term \<open>w(Y) = w(X) + w(E)\<close>}.\<close>

lemma interval_subset_width:
  fixes X Y :: "'a::{linordered_ring, lattice} interval"
  assumes "X \<le> Y"
  and X_def: "X = Interval(a, b)" and x_valid: "a \<le> b"
  and Y_def: "Y = Interval(c, d)" and y_valid: "c \<le> d"
  shows "\<exists> E. 0 \<in>\<^sub>i E \<and> Y = X + E \<and> width Y = width X + width E"
proof -
  have "c \<le> a" "b \<le> d" 
  proof -
      have leq: "lower Y \<le> lower X \<and> upper X \<le> upper Y" using assms(1) unfolding less_eq_interval_def by simp
      have X_bounds: "lower X = a" "upper X = b" unfolding X_def by (simp add: x_valid bounds_of_interval_eq_lower_upper)+
      have Y_bounds: "lower Y = c" "upper Y = d" unfolding Y_def by (simp add: y_valid bounds_of_interval_eq_lower_upper)+
      show "c \<le> a" "b \<le> d" using assms(1) X_bounds Y_bounds unfolding less_eq_interval_def by simp_all
  qed
  define e where "e = c - a"
  define f where "f = d - b"
  define E where "E = Interval(e, f)"
  have "0 \<in>\<^sub>i E" unfolding E_def  e_def f_def using \<open>c \<le> a\<close>  \<open>b \<le> d\<close> set_of_subset_iff 
    by (smt (verit, ccfv_SIG) diff_ge_0_iff_ge in_intervalI le_iff_diff_le_0 lower_bounds order.trans upper_bounds) 
  have "Y = X + E" 
  proof -
    have X_bounds: "lower X = a" "upper X = b" 
      unfolding X_def by (simp add: x_valid bounds_of_interval_eq_lower_upper)+
    have Y_bounds: "lower Y = c" "upper Y = d" 
      unfolding Y_def by (simp add: y_valid bounds_of_interval_eq_lower_upper)+
    have E_bound_1: "lower E = c - a" 
      unfolding E_def e_def f_def 
      using \<open>b \<le> d\<close> \<open>c \<le> a\<close> diff_left_mono diff_self lower_bounds order_trans
      by metis
    have E_bound_2:"upper E = d - b" 
      unfolding E_def e_def f_def 
      using \<open>b \<le> d\<close> \<open>c \<le> a\<close>  E_bound_1 \<open>0 \<in>\<^sub>i E\<close> diff_ge_0_iff_ge dual_order.trans in_bounds upper_bounds
      by metis 
    have add: "Interval(a,b) + Interval(c-a,d-b) = Interval(c,d)" 
      using X_bounds Y_bounds E_bound_1 E_bound_2
      by (simp add: E_def X_def Y_def e_def f_def interval_eqI)
    show ?thesis unfolding E_def X_def Y_def e_def f_def using add by simp
  qed
  have "width Y = width X + width E" unfolding width_def using E_def X_def Y_def \<open>Y = X + E\<close> e_def f_def by force 
  from \<open>0 \<in>\<^sub>i E\<close> \<open>Y = X + E\<close> \<open>width Y = width X + width E\<close> show ?thesis by auto[1]
qed

lemma excess_width_incl:
  fixes F :: "real interval \<Rightarrow> real interval" and X :: "real interval"
  assumes int: \<open>F is_interval_extension_of f\<close>
  and iso: "inclusion_isotonic F" 
  and "L-lipschitz_on (set_of X) f"
shows \<open> \<exists> E . F X = Interval(Inf (f ` set_of X), Sup (f ` set_of X)) + E \<close>  
proof -
  have a0: \<open>f ` (set_of X) \<noteq> {}\<close> using in_intervalI by fastforce
  have a1: "Inf (f ` set_of X) \<le> Sup (f ` set_of X)" 
    using assms a0 inf_le_sup_image_real by simp
  have a2: \<open>f ` (set_of X) \<subseteq> set_of (F X)\<close> 
    using assms fundamental_theorem_of_interval_analysis by simp 
  have max: \<open>Sup (f ` (set_of X)) \<le> Sup (set_of (F X))\<close> 
    using assms(3) a0 a2 sup_image_le_real[of f X F] by blast   
  have max_interval: "Sup (f ` (set_of X)) \<le> upper (F X)" 
    using max sup_set_of by metis
  have min: \<open>Inf (set_of (F X)) \<le> Inf (f ` (set_of X))\<close>
    using assms(3) a0 a2 inf_image_le_real[of f X F] by blast 
  have min_interval: "lower (F X) \<le> Inf (f ` (set_of X))" 
    using min inf_set_of by metis
  have lower_min: "lower (Interval (Inf (f ` set_of X), Sup (f ` set_of X))) = Inf (f ` set_of X)" 
    using lower_bounds a1 by simp
  have upper_max: "upper (Interval (Inf (f ` set_of X), Sup (f ` set_of X))) = Sup (f ` set_of X)" 
    using upper_bounds a1 by simp
  have a3: "Interval(Inf (f ` set_of X), Sup (f ` set_of X)) \<le> F X" 
    using min_interval max_interval lower_min upper_max unfolding less_eq_interval_def by simp 
  have a4: "\<exists> E . Interval(Inf (f ` set_of X), Sup (f ` set_of X)) + E = F X" using a3 
    by (metis (no_types, opaque_lifting) bounds_of_interval_eq_lower_upper 
        bounds_of_interval_inverse interval_subset_width lower_le_upper)
  then show ?thesis by metis
qed  

lemma excess_interval_superset_interval:
  fixes F :: "real interval \<Rightarrow> real interval" and X :: "real interval"
  assumes int: \<open>F is_interval_extension_of f\<close>
  and iso: "inclusion_isotonic F" 
  and "L-lipschitz_on (set_of X) f"
  and ex: \<open> \<exists> E . F X = Interval(Inf (f ` set_of X), Sup (f ` set_of X)) + E \<close>
shows \<open>Interval(Inf (f ` set_of X), Sup (f ` set_of X)) \<le> F X\<close>
proof -
  have lhs: "lower (F X) \<le> lower (Interval(Inf (f ` set_of X), Sup (f ` set_of X)))"
    using assms(1,2,3)  inf_image_le_real inf_le_sup_image_real  inf_set_of 
          fundamental_theorem_of_interval_analysis lower_bounds 
    by metis 
 have rhs: "upper (Interval(Inf (f ` set_of X), Sup (f ` set_of X))) \<le> upper (F X)"
   using assms(1,2,3)  inf_le_sup_image_real  sup_image_le_real sup_set_of
          fundamental_theorem_of_interval_analysis upper_bounds 
   by metis
  show ?thesis using lhs rhs unfolding less_eq_interval_def by simp
qed

lemma each_subdivision_width_order:
  fixes X :: "'a::{linordered_field,lattice,metric_space} interval"
  assumes "inclusion_isotonic F" "lipschitzI_on C U F" "F is_interval_extension_of f"
  and "set (uniform_subdivision X N) \<subseteq> U"  "0 < N" "Xs \<in> set (uniform_subdivision X N)" 
shows "width(F Xs) \<le> C * width (X) / of_nat N"
proof -
  have a0: "\<forall>Xs \<in> set (uniform_subdivision X N). width (F Xs) \<le> C * width Xs"
    using assms(2) assms(4) lipschitzI_onD by blast
  have a1: "\<forall> Xs \<in> set (uniform_subdivision X N). width(F Xs) \<le> C * width (X) / of_nat N"
    using a0 assms(5) uniform_subdivisions_width[of N X] by simp 
  show ?thesis using a1 assms by simp
qed

lemma each_subdivision_excess_width_order:
  fixes X :: "real interval"
  assumes "inclusion_isotonic F" "lipschitzI_on C U F" "F is_interval_extension_of f"
  and "set (uniform_subdivision X N) \<subseteq> U"  "0 < N"
  and " L-lipschitz_on (set_of (interval_list_union (uniform_subdivision X N))) f " 
shows "\<forall> Xs \<in> set (uniform_subdivision X N) . excess_width F f Xs \<le> C * width (X) / of_nat N" 
proof -
  have a0: "\<forall>Xs \<in> set (uniform_subdivision X N). width (F Xs) \<le> C * width Xs"
    using assms lipschitzI_onD by blast
  have a1: "\<forall> Xs \<in> set (uniform_subdivision X N). width(F Xs) \<le> C * width (X) / of_nat N"
    using a0 assms uniform_subdivisions_width[of N X] by simp
  have a2: "\<forall> Xs \<in> set (uniform_subdivision X N). excess_width F f Xs \<le> C * width (X) / of_nat N"
  proof - 
    have b0: "set (uniform_subdivision X N) \<noteq> {}" 
      using assms non_empty_subdivision by simp
    have b1: "\<forall> Xs \<in> set (uniform_subdivision X N) . 0 \<le> width_set (f ` set_of Xs)" 
    proof - 
       have c0: "\<forall> Xs \<in> set (uniform_subdivision X N) . set_of Xs \<subseteq> set_of (interval_list_union (uniform_subdivision X N))" 
        using assms interval_list_union_correct in_set_conv_nth non_empty_subdivision
        by metis
      then have c1: "\<forall> Xs \<in> set (uniform_subdivision X N) . set_of Xs \<noteq> {}" using in_intervalI by fastforce
      then have c2: "\<forall> Xs \<in> set (uniform_subdivision X N) . Inf (f ` set_of Xs) \<le> Sup (f ` set_of Xs)"  
        using assms c0 c1 inf_le_sup_image_real lipschitz_on_subset 
        by (metis inf_le_sup_image_real)
      then have c3: "\<forall> Xs \<in> set (uniform_subdivision X N) . 0 \<le> width_set (f ` set_of Xs)"
        by (simp add: width_set_def) 
      then show ?thesis by simp
    qed 
    have b2: "\<forall> Xs \<in> set (uniform_subdivision X N) . width(F Xs) - width_set (f ` set_of Xs) \<le> width(F Xs)"
      using b0 b1 assms inf_set_of lower_le_upper sup_set_of inf_le_sup_image_real image_is_empty
      by (simp add: width_set_def)
    then show ?thesis
      using a1 unfolding excess_width_def width_set_def by fastforce
    qed
  show ?thesis using assms a0 a1 a2 by simp
qed

text \<open>The theorem @{thm "each_subdivision_width_order"} refers to Theorem 6.1 in~\<^cite>\<open>"moore.ea:introduction:2009"\<close>.\<close>

lemma sup_interval_max: 
  fixes X Y :: "'a::{linordered_ring, lattice} interval"
  shows "sup X Y = Interval(min (lower X) (lower Y), max (upper X) (upper Y))"
  using Interval.lower_sup Interval.upper_sup Interval_id inf_real_def sup_max
  by (metis inf_min)

lemma interval_inf_sup_lower: "inf (lower I1) (lower I2) = lower (sup I1 I2)" 
  unfolding sup_interval_def 
  by (metis (mono_tags, lifting) Interval.lower_sup sup_interval_def)

lemma interval_sup_sup_upper: "sup (upper I1) (upper I2) = upper (sup I1 I2)"
  unfolding sup_interval_def 
  by (metis (mono_tags, lifting) Interval.upper_sup sup_interval_def)

lemma interval_union_lower: 
  assumes "contiguous Xs" "Xs \<noteq> []"
  shows "lower (interval_list_union Xs) = lower (Xs!0)"
  using assms
proof(induction Xs rule:interval_list_union.induct)
  case 1
  then show ?case by simp
next
  case (2 I)
  then show ?case by simp
next
  case (3 I v va)
  have a0: "contiguous (v # va)" using 3 unfolding contiguous_def by auto
  have a1: "(v # va) \<noteq> []" by simp
  then show ?case
    unfolding sorted_wrt_lower_def 3 
  proof - 
    have b0: "lower ((I # v # va) ! 0) = lower I" by simp
    have b1: "lower I \<le> lower v" 
      using "3.prems" a1  
      unfolding contiguous_def 
      by (metis Suc_eq_plus1 add_diff_cancel_left' length_Cons less_Suc_eq_0_disj 
          lower_le_upper nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc)
    show "lower (interval_list_union (I # v # va)) = lower ((I # v # va) ! 0)" 
      using b0 b1 3(2) interval_list_union.simps(3) "3.IH" Interval.lower_sup a0 a1 inf.orderE 
        nth_Cons_0 
      unfolding sorted_wrt_lower_def 
      by metis
  qed 
qed

lemma interval_union_upper: 
  assumes "contiguous Xs" "Xs \<noteq> []"
  shows "upper (interval_list_union Xs) = upper (last Xs)"
  using assms
proof(induction Xs rule:interval_list_union.induct)
  case 1
  then show ?case by simp
next
  case (2 I)
  then show ?case by simp
next
  case (3 I v va)
  have a0: "contiguous (v # va)" using 3 unfolding contiguous_def by auto
  have a1: "(v # va) \<noteq> []" by simp
  then show ?case
  proof - 
    have b0: "upper ((I # v # va) ! (length (I # v # va) - 1)) = upper (last (I # v # va))" 
      using last_conv_nth by fastforce
    have b1: "upper I \<le> upper v" using "3.prems" unfolding contiguous_def by auto
    show "upper (interval_list_union (I # v # va)) = upper (last (I # v # va))" 
      using b0 b1 interval_list_union.simps(3) "3.IH" a0 a1 interval_list_union.simps(3) 
        Interval.upper_sup last.simps
      by (metis (no_types, opaque_lifting) dual_order.trans min_list.cases sup_absorb2 sup_ge1)
  qed 
qed

lemma union_set:
  assumes "0 < n" 
  shows "interval_list_union (uniform_subdivision X n) = X"
  using assms
proof (induction n rule:nat_induct_non_zero)
  case 1
  then show ?case using uniform_subdivision_id  interval_list_union.simps(2) by metis
next
  case (Suc n)
  then show ?case
  proof (induction "uniform_subdivision X (Suc n)" rule:interval_list_union.induct)
    case 1
    then show ?case by (metis less_Suc_eq non_empty_subdivision)  
  next
    case (2 I)
    then show ?case using One_nat_def interval_list_union.simps(2) subdivision_length_n uniform_subdivision_id zero_less_Suc
      by metis 
  next
    case (3 I v va)
    then have a0: "lower I = lower X"  
      using hd_lower_uniform_subdivision assms 
      by (metis list.collapse list.simps(3) nth_Cons_0 zero_less_Suc)
    then have a1: "upper (last ( I # v # va)) = upper X" 
      using last_upper_uniform_subdivision[of "Suc n" X] assms "3.hyps"(2) by simp
    then have a2: "contiguous ( I # v # va)" 
      using contiguous_uniform_subdivision assms zero_less_Suc "3.hyps"(2) by metis 
    then have a3: "overlapping_ordered ( I # v # va)"
      using overlapping_uniform_subdivision  assms zero_less_Suc "3.hyps"(2) 
      by (simp add: overlapping_ordered_uniform_subdivision)
    then have a4: "\<forall>i<length ( I # v # va) - 1. upper (( I # v # va) ! i) = lower (( I # v # va) ! (i + 1))"
        using a0 a2 unfolding contiguous_def by simp 
      have a5: "\<forall>i<length ( I # v # va) - 1. lower (( I # v # va) ! i) \<le> lower (( I # v # va) ! (i + 1))"
        using a0 a2 contiguous_def lower_le_upper by metis 
      have a6: "\<forall>i<length ( I # v # va) - 1. upper (( I # v # va) ! i) \<le> upper (( I # v # va) ! (i + 1))"
        using a0 a2 contiguous_def lower_le_upper by metis
      then show ?case 
      proof -
      have "lower (interval_list_union ( I # v # va)) = lower X" 
      proof -
        have c0: "lower (interval_list_union ( I # v # va)) = lower (sup I (interval_list_union (v # va)))"  
          using interval_list_union.simps(3) by metis     
        have c1: "lower (sup I (interval_list_union ( v # va))) = min (lower I) (lower (interval_list_union ( v # va)))"
          using inf_real_def sup_interval_def sup_interval_max sup_real_def 
          by (simp add: inf_min)
        have c2: "min (lower I) (lower (interval_list_union (v # va))) = lower I" 
          using 3 hd_lower_uniform_subdivision[of "Suc n" X] a0 
                contiguous_uniform_subdivision[of  X, simplified contiguous_def 3(2)[symmetric]] 
                interval_union_lower[of "( I # v # va)"] 
          by (metis a2 c0 c1 list.discI nth_Cons_0) 
        show ?thesis using a0 c0 c1 c2 by simp 
        qed
        moreover have "upper (interval_list_union ( I # v # va)) = upper X" 
        proof - 
          have c0: "upper (interval_list_union ( I # v # va)) = upper (sup I (interval_list_union ( v # va)))"
            using interval_list_union.simps(3) by metis
          have c1: "upper (sup I (interval_list_union (v # va))) = max (upper I) (upper (interval_list_union ( v # va)))"
            using inf_real_def sup_interval_def sup_interval_max sup_real_def 
            by (simp add: sup_max)
          have c2: "max (upper I) (upper (interval_list_union ( v # va))) = upper (last ( I # v # va))"
             using contiguous_uniform_subdivision[of  X, simplified contiguous_def 3(2)[symmetric]] 
                 interval_union_upper[of "( I # v # va)"] 
             by (metis a2 c0 c1 list.discI ) 
          show ?thesis using c0 c1 c2 "3.hyps"(2) last_upper_uniform_subdivision by auto[1]
        qed
      ultimately show ?thesis 
        using interval_eqI 3 by auto[1]
    qed
  qed
qed
 
lemma sum_list_less:
  assumes "list_all (\<lambda>n. n \<le> (y::real)) xs"
  shows "sum_list xs \<le> y * length xs"
proof -
  have "\<forall>x\<in>set xs. x \<le> y"
    using assms list_all_iff by metis
  hence "sum_list xs \<le> sum_list (replicate (length xs) y)"
    using sum_list_mono 
    by (simp add: order_less_imp_le sum_list_mono2)
  also have "... = y * length xs"
    by (simp add: sum_list_replicate)
  finally show ?thesis by simp
qed

lemma in_bounds2:
  fixes X Y :: "'a::{linordered_ring} interval"
  shows "x \<in>\<^sub>i X \<and> x \<in>\<^sub>i Y \<Longrightarrow>
     (lower Y \<le> lower X \<and> upper Y \<le> upper X \<and> lower X \<le> upper Y \<and> lower Y \<le> upper X) \<or>
     (lower X \<le> lower Y \<and> upper X \<le> upper Y \<and> lower X \<le> upper Y \<and> lower Y \<le> upper X) \<or>
     (lower Y \<le> lower X \<and> upper X \<le> upper Y \<and> lower Y \<le> lower X \<and> lower Y \<le> upper X) \<or> 
     (lower X \<le> lower Y \<and> upper Y \<le> upper X \<and> lower X \<le> upper Y \<and> lower Y \<le> upper X)"
  apply(clarify)
  by (metis (full_types) in_bounds nle_le order.trans) 

lemma overlapping_width_sum:
  fixes X Y :: "'a::{linordered_ring, lattice} interval"
  assumes "overlapping [X,Y]"
  shows "width (sup X Y) \<le> width X + width Y"
proof - 
  have a0: "\<forall>i<length [X, Y] - 1. \<exists>e. e \<in>\<^sub>i [X, Y] ! (i + 1) \<and> e \<in>\<^sub>i [X, Y] ! i"
    using assms unfolding overlapping_def by blast
  have a1: "(lower Y \<le> lower X \<and> upper Y \<le> upper X \<and> lower X \<le> upper Y \<and> lower Y \<le> upper X) \<or>
     (lower X \<le> lower Y \<and> upper X \<le> upper Y \<and> lower X \<le> upper Y \<and> lower Y \<le> upper X) \<or>
     (lower Y \<le> lower X \<and> upper X \<le> upper Y \<and> lower Y \<le> lower X \<and> lower Y \<le> upper X) \<or> 
     (lower X \<le> lower Y \<and> upper Y \<le> upper X \<and> lower X \<le> upper Y \<and> lower Y \<le> upper X)"
    using assms in_bounds2[of _  X Y] unfolding overlapping_def by auto
  have a2: "(lower Y \<le> lower X \<and> upper Y \<le> upper X \<and> lower X \<le> upper Y \<and> lower Y \<le> upper X) \<Longrightarrow> width (sup X Y) \<le> width X + width Y"
    by (simp add: inf_min width_def)
  have a3: "(lower X \<le> lower Y \<and> upper X \<le> upper Y \<and> lower X \<le> upper Y \<and> lower Y \<le> upper X) \<Longrightarrow> width (sup X Y) \<le> width X + width Y"
    by (simp add: inf_min width_def)
  have a4: "(lower Y \<le> lower X \<and> upper X \<le> upper Y \<and> lower Y \<le> lower X \<and> lower Y \<le> upper X) \<Longrightarrow> width (sup X Y) \<le> width X + width Y"
    by (simp add: inf_min sup_max width_def)
  have a5: "(lower X \<le> lower Y \<and> upper Y \<le> upper X \<and> lower X \<le> upper Y \<and> lower Y \<le> upper X) \<Longrightarrow> width (sup X Y) \<le> width X + width Y"
    by (metis interval_width_positive le_add_same_cancel1 less_eq_interval_def sup.order_iff)
  show ?thesis using assms a0 a1 a2 a3 a4 a5 by blast
qed

lemma interval_list_union_width:
  fixes xs :: "'a::{linordered_ring, lattice} interval list"
  assumes "overlapping xs" "xs \<noteq> []" 
  shows "overlapping xs \<Longrightarrow> width (interval_list_union xs) \<le> sum_list (map width xs)"
  using assms unfolding contiguous_def width_def
proof (induction xs rule: interval_list_union.induct)
  case 1
  then show ?case by simp
next
  case (2 I)
  then show ?case by simp
next
  case (3 I1 I2 Is)
  then show ?case unfolding overlapping_def
  proof -
    have a0: "width (interval_list_union (I1 # I2 # Is)) = width (sup I1 (interval_list_union (I2 # Is)))" 
      using interval_list_union.simps by simp
    have a1: "... \<le> width I1 + width (interval_list_union (I2 # Is))" 
    proof -
      have b0: "overlapping [I1, interval_list_union (I2 # Is)]" 
        using "3.prems" list.simps(3) list.size(3) list.size(4) interval_list_union_correct 
        unfolding overlapping_def 
        by (smt (verit, ccfv_threshold) One_nat_def Suc_eq_plus1 diff_add_inverse2  
            length_greater_0_conv less_one nth_Cons' subsetD) 
      show ?thesis 
        using overlapping_width_sum[of I1 "(interval_list_union (I2 # Is))", simplified b0] 
        by blast
    qed
    have a2: "... \<le> width I1 + sum_list (map width (I2 # Is))"
    proof -
      have b0: "(width I1 + width (interval_list_union (I2 # Is)) \<le> width I1 + sum_list (map width (I2 # Is))) = 
                (width (interval_list_union (I2 # Is)) \<le> sum_list (map width (I2 # Is)))" by simp
      have b1: "overlapping (I2 # Is)" using "3.prems" unfolding overlapping_def by force
      have b2: "I2 # Is \<noteq> []" by simp
      have b3: "width (interval_list_union (I2 # Is)) \<le> sum_list (map width (I2 # Is))" 
        using "3.IH" b1 b2 unfolding width_def by simp
      show ?thesis using b0 b3 by simp
    qed
    have a3: "... = sum_list (map width (I1 # I2 # Is))" by auto[1]
    show ?thesis using a0 a1 a2 a3 map_eq_conv width_def 
      by (smt (verit, ccfv_SIG) dual_order.trans)
  qed
qed

lemma map_non_zero_width:
  fixes U :: "'a::{linordered_idom} interval set"
  assumes "C-lipschitzI_on U F" "inclusion_isotonic F" "set xs \<subseteq> U"
  shows "\<forall>x \<in> set xs. 0 \<le> width x  \<longrightarrow> 0 \<le> width (F x)"
proof
  fix x
  assume a0: "x \<in> set xs"
  show "0 \<le> width x  \<longrightarrow> 0 \<le> width (F x)"
  proof
    assume a1: "0 \<le> width x" 
    have a2: "width (F x) \<le> C * width x" using assms(1,3) a0 unfolding lipschitzI_on_def by blast 
    have a4: "width (F x) \<le> C * width x + 1" using assms(1,3) a0 unfolding lipschitzI_on_def by fastforce
    have "0 \<le> C * width x" using assms(1) a1 unfolding lipschitzI_on_def by simp
    show "0 \<le> width (F x)" using assms(1) a0 interval_width_positive unfolding lipschitzI_on_def interval_width_positive by blast
  qed
qed


lemma inclusion_isotonic_preserves_overlapping:
  assumes "inclusion_isotonic F"  "xs \<noteq> []"  "F is_interval_extension_of f" 
  shows "contiguous xs \<Longrightarrow> overlapping (map F xs)" 
proof (induct xs rule: induct_list012)
  case 1
  then show ?case 
    unfolding overlapping_def by simp
next
  case (2 x)
  then show ?case 
    unfolding overlapping_def by simp
next
  case (3 x y zs)
  then show ?case 
  proof -
    have a0: "\<forall>i<length (map F (x # y # zs)) - 1. \<exists>e. e \<in>\<^sub>i map F (x # y # zs) ! (i + 1) \<and> e \<in>\<^sub>i map F (x # y # zs) ! i"
    proof -
      have b0: "length (map F (x # y # zs)) \<ge> 1" using "3.prems" by simp
      have b2: "\<forall>i<length (x # y # zs) - 1. upper ((x # y # zs) ! i) = lower ((x # y # zs) ! (i + 1))" 
        using "3.prems" unfolding contiguous_def by auto[1]
      have b3: "\<forall>i<length (x # y # zs) - 1. upper ((x # y # zs) ! i) \<le> upper ((x # y # zs) ! (i + 1))" 
        using "3.prems" unfolding contiguous_def by auto[1]
      have b4: "\<forall>i<length (x # y # zs) - 1. lower ((x # y # zs) ! i) \<le> lower ((x # y # zs) ! (i + 1)) "
        using "3.prems" lower_le_upper b2 unfolding contiguous_def by metis
      have b5: "\<forall>i<length (x # y # zs) - 1. f (upper ((x # y # zs) ! i)) = f (lower ((x # y # zs) ! (i + 1)))" 
        using b2 by simp
      have b6: "\<forall>i<length (x # y # zs) - 1. f (upper ((x # y # zs) ! i)) \<in>\<^sub>i F  ((x # y # zs) ! i)" 
        using assms b2 b4 in_intervalI interval_of_in_eq  
        unfolding is_interval_extension_of_def inclusion_isotonic_def 
        by (metis lower_interval_of lower_le_upper upper_interval_of) 
      have b7: "\<forall>i<length (x # y # zs) - 1. f (upper ((x # y # zs) ! i)) \<in>\<^sub>i F  ((x # y # zs) ! (i+1))" 
        using assms b2 b3 in_intervalI interval_of_in_eq  
        unfolding is_interval_extension_of_def inclusion_isotonic_def 
        by (metis lower_interval_of lower_le_upper upper_interval_of) 
      have b8: "\<forall>i<length (x # y # zs) - 1. f (upper ((x # y # zs) ! i)) \<in>\<^sub>i F  ((x # y # zs) ! (i+1)) \<and> f (upper ((x # y # zs) ! i)) \<in>\<^sub>i F  ((x # y # zs) ! i)"
        using b6 b7 by blast
      show ?thesis using b8 apply simp 
        by (metis One_nat_def Suc_eq_plus1 le_simps(2) list.map(2) list.size(4) nth_map order_less_le)
    qed
    show ?thesis using a0 unfolding overlapping_def by simp
  qed 
qed
  
lemma bounded_image_of:
  fixes f::\<open>real \<Rightarrow> real\<close>
  assumes \<open>L-lipschitz_on (set_of X) f\<close>
  shows \<open>bounded (f ` set_of X)\<close>
  using lipschitz_bounded_image_real[of "set_of X" L f] assms 
  using bounded_set_of set_of_nonempty by blast

lemma dist_le_diameter:   
  fixes f::\<open>real \<Rightarrow> real \<close>
  assumes  \<open> C-lipschitz_on (set_of X) f\<close>
  shows \<open>dist (f (upper X)) (f (lower X)) \<le> diameter (f ` set_of X)\<close>
  using diameter_bounded_bound[of "f` set_of X" "f (upper X)" "f (lower X)", 
        simplified  
        bounded_image_of[of C X f, simplified assms]]
  by simp 

lemma excess_width_inf_sup:
  fixes X :: "real interval" and f::\<open>real \<Rightarrow> real\<close>
  assumes \<open>continuous_on (set_of X) f\<close>
  shows "Inf (f ` set_of X) - lower (F X) + upper (F X) - Sup (f ` set_of X) \<le> excess_width F f X"
  using diameter_Sup_Inf[of "f ` set_of X", simplified compact_img_set_of set_f_nonempty assms]
  unfolding excess_width_def  width_def width_set_def set_of_eq 
  by simp
                                           
lemma excess_width_lower_bound:
  fixes X :: "real interval"
  assumes  "inclusion_isotonic F"  "F is_interval_extension_of f"  \<open>continuous_on (set_of X) f\<close>
  shows  "Inf (f ` set_of X) - lower (F X) \<le> excess_width F f X"
proof -
  have a0: "0 \<le> upper (F X) - Sup (f ` set_of X)" 
    using assms(1) assms(2) diff_ge_0_iff_ge inclusion_isotonic_sup
    by metis 
  show ?thesis using a0 excess_width_inf_sup assms
    by (smt (verit, ccfv_threshold)) 
qed

lemma excess_width_upper_bound:
  fixes X :: "real interval"
  assumes  "inclusion_isotonic F"  "F is_interval_extension_of f" \<open>continuous_on (set_of X) f\<close>
  shows  "upper (F X) - Sup (f ` set_of X) \<le> excess_width F f X"
proof -
  have a0: "0 \<le> Inf (f ` {lower X..upper X}) - lower (F X)" 
    using assms(1) assms(2) diff_ge_0_iff_ge inclusion_isotonic_sup set_of_eq 
      inclusion_isotonic_inf
    by metis 
  show ?thesis using a0 excess_width_inf_sup assms unfolding set_of_eq
    by (smt (verit, ccfv_threshold))   
qed

lemma lipschitz_excess_width_lower_bound:
  fixes X :: "real interval"
  assumes "inclusion_isotonic F" "lipschitzI_on C U F" "F is_interval_extension_of f"
  and "set (uniform_subdivision X N) \<subseteq> U"  "N = 1"
  and "L-lipschitz_on (set_of (interval_list_union (uniform_subdivision X N))) f "  
  shows  "Inf (f ` set_of X) - lower (F X) \<le> C * width X"
proof-
  have a0: "excess_width F f X \<le> C * width X"
    using each_subdivision_excess_width_order[of F C U f X N L, simplified assms] 
      assms(4) assms(5) assms(6) div_by_1 insert_iff less_numeral_extra(1) list.set(2) of_nat_1 
      uniform_subdivision_id
    by metis 
  have a1: "Inf (f ` set_of X) - lower (F X) \<le> excess_width F f X"
    using excess_width_lower_bound[of F f X, simplified assms]
    by (metis assms(5) assms(6) lipschitz_on_continuous_on union_set zero_less_one) 
  show ?thesis using a0 a1 by simp
qed

lemma lipschitz_excess_width_upper_bound:
  fixes X :: "real interval"
  assumes "inclusion_isotonic F" "lipschitzI_on C U F" "F is_interval_extension_of f"
  and "set (uniform_subdivision X N) \<subseteq> U"  "N = 1"
  and "L-lipschitz_on (set_of (interval_list_union (uniform_subdivision X N))) f "  
  shows  "upper (F X) - Sup (f ` set_of X) \<le> C * width X"
proof-
  have a0: "excess_width F f X \<le> C * width X"
    using each_subdivision_excess_width_order[of F C U f X N L, simplified assms] 
      assms(4) assms(5) assms(6) div_by_1 insert_iff less_numeral_extra(1) list.set(2) of_nat_1 
      uniform_subdivision_id
    by metis 
  have a1: "upper (F X) - Sup (f ` set_of X) \<le> excess_width F f X"
    using excess_width_upper_bound[of F f X, simplified assms] 
    by (metis assms(5) assms(6) lipschitz_on_continuous_on union_set zero_less_one) 
  show ?thesis using a0 a1 by simp
qed

lemma excess_width_bound_inf:
  fixes X :: "real interval"
  assumes excess_width_bound: \<open>excess_width F f X \<le> k\<close>
  and     inclusion_isotonic: \<open>inclusion_isotonic F\<close>
  and     interval_extension: \<open>F is_interval_extension_of f\<close>
  shows \<open>Inf (f ` set_of X) - k \<le> lower (F X)\<close>
  using excess_width_bound[simplified excess_width_def width_def width_set_def]
        inclusion_isotonic interval_extension
  by (smt (verit, best) inclusion_isotonic_sup) 

lemma excess_width_bound_sup:
  fixes X :: "real interval"
  assumes excess_width_bound: \<open>excess_width F f X \<le> k\<close>
  and     inclusion_isotonic: \<open>inclusion_isotonic F\<close>
  and     interval_extension: \<open>F is_interval_extension_of f\<close>
  shows \<open>upper (F X) \<le> Sup (f ` set_of X) + k\<close>
  using excess_width_bound[simplified excess_width_def width_def width_set_def]
        inclusion_isotonic interval_extension
  by (smt (verit, best) inclusion_isotonic_inf) 

lemma set_of_interval_list_subset_inf_sup:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
shows \<open>set_of_interval_list XS \<subseteq> {Min(set (map lower XS))..Max(set (map upper XS))}\<close>
  using assms unfolding set_of_interval_list_def  
proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case by(simp add:set_of_eq)
next
  case (cons x xs)
  then show ?case 
    apply(simp add:set_of_eq)
    by fastforce 
qed

lemma lower_bound_F_inf: 
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     inclusion_isotonic: \<open>inclusion_isotonic F\<close>
  and     interval_extension: \<open>F is_interval_extension_of f\<close>
  and     sorted_lower: \<open>sorted_wrt_lower XS\<close>
  and     lipschitz:  \<open>0 \<le> C\<close> \<open>C-lipschitz_on ((set_of_interval_list XS)) f\<close>
  and     excess_width_bounded: \<open>(Max (set ((map (excess_width F f)) XS))) \<le> k\<close>
shows \<open>(Inf (f ` (set_of_interval_list XS))) - k \<le> Inf (set_of_interval_list (map F XS))\<close>
 using assms proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case 
    using excess_width_bound_inf[of F f x k]
    unfolding set_of_interval_list_def
    by (simp add: inf_set_of)
next
  case (cons x xs)
  then show ?case 
    using excess_width_bound_inf[of F f x]
    unfolding set_of_interval_list_def 
    apply(simp)
    apply(fold set_of_interval_list_def)
    apply(subst image_Un)
    apply(subst cInf_union_distrib)
    subgoal 
      by simp
    subgoal 
      apply(simp add: set_of_eq)
      by (meson bounded_imp_bdd_below compact_Icc compact_continuous_image compact_imp_bounded 
                lipschitz_on_continuous_on lipschitz_on_subset sup_ge1) 
    subgoal 
      unfolding set_of_interval_list_def 
      by (metis image_is_empty set_of_interval_list_def set_of_interval_list_nonempty)
    subgoal 
      using compact_set_of_interval_list[of XS]
            compact_imp_bounded[of " (set_of_interval_list XS)"]
      by (meson bounded_imp_bdd_below compact_continuous_image compact_imp_bounded 
                compact_set_of_interval_list lipschitz_on_continuous_on lipschitz_on_mono sup_ge2) 
    subgoal  
      apply(subst cInf_union_distrib)
      subgoal 
        by simp 
      subgoal 
        by (meson bdd_below_set_of) 
      subgoal 
        by(simp add: set_of_interval_list_nonempty) 
      subgoal 
        using set_of_interval_list_bdd_below by simp
      subgoal 
      proof -
        assume a1: "xs \<noteq> []"
        assume a2: "\<lbrakk>sorted_wrt_lower xs; C-lipschitz_on (set_of_interval_list xs) f\<rbrakk> \<Longrightarrow> Inf (f ` set_of_interval_list xs) - k \<le> Inf (set_of_interval_list (map F xs))"
        assume a3: "sorted_wrt_lower (x # xs)"
        assume a4: "C-lipschitz_on (set_of x \<union> set_of_interval_list xs) f"
        assume a5: "excess_width F f x \<le> k \<and> (\<forall>a\<in>set xs. excess_width F f a \<le> k)"
        assume a6: "\<And>k. excess_width F f x \<le> k \<Longrightarrow> Inf (f ` set_of x) - k \<le> lower (F x)"
        have f7: "sorted_wrt_lower xs"
          using a3 a1 sorted_wrt_lower_unroll by blast
        have f8: "Inf (set_of (F x)) = lower (F x)"
          using inf_set_of by blast
        have f9: "C-lipschitz_on (set_of_interval_list xs) f"
          using a4 lipschitz_on_subset by blast
        have f10: "inf (Inf (f ` set_of x)) (Inf (f ` set_of_interval_list xs)) \<le> Inf (f ` set_of x)"
          using inf_le1 by blast
        have f11: "inf (Inf (f ` set_of x)) (Inf (f ` set_of_interval_list xs)) \<le> Inf (f ` set_of_interval_list xs)"
          using inf_le2 by blast
        have "Inf (f ` set_of x) - excess_width F f x \<le> lower (F x)"
          using a6 by blast
        have "inf (Inf (f ` set_of x)) (Inf (f ` set_of_interval_list xs)) - k \<le> Inf (set_of (F x)) 
            \<and> inf (Inf (f ` set_of x)) (Inf (f ` set_of_interval_list xs)) - k \<le> Inf (set_of_interval_list (map F xs))"
          using f11 f10 f9 f8 f7 a5 a2 
          using \<open>Inf (f ` set_of x) - excess_width F f x \<le> lower (F x)\<close> by linarith 
        then show ?thesis by simp 
      qed
      done
    done
qed

lemma upper_bound_F_sup: 
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     inclusion_isotonic: \<open>inclusion_isotonic F\<close>
  and     interval_extension: \<open>F is_interval_extension_of f\<close>
  and     sorted_upper: \<open>sorted_wrt_upper XS\<close>
  and     lipschitz:  \<open>0 \<le> C\<close> \<open>C-lipschitz_on ((set_of_interval_list XS)) f\<close>
  and     excess_width_bounded: \<open>(Max (set ((map (excess_width F f)) XS))) \<le> k\<close>
shows \<open>Sup (set_of_interval_list (map F XS)) \<le> (Sup (f ` (set_of_interval_list XS))) + k \<close>
 using assms proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case 
    using excess_width_bound_sup[of F f x k]
    unfolding set_of_interval_list_def   
    by (simp add: sup_set_of)
next
  case (cons x xs)
  then show ?case 
    using excess_width_bound_inf[of F f x]
    unfolding set_of_interval_list_def 
    apply(simp)
    apply(fold set_of_interval_list_def)
    apply(subst image_Un)
    apply(subst cSup_union_distrib)
    subgoal 
      by simp
    subgoal 
      by(simp add: set_of_eq)
    subgoal 
      by(simp add: set_of_interval_list_nonempty) 
    subgoal 
      using set_of_interval_list_bdd_above by simp 
    subgoal  
      apply(subst cSup_union_distrib)
      subgoal 
        by simp 
      subgoal  
        by (meson bdd_above_mono bdd_above_set_of fundamental_theorem_of_interval_analysis) 
      subgoal 
        by(simp add: set_of_interval_list_nonempty) 
      subgoal 
        using set_of_interval_list_bdd_above 
        by (meson bounded_imp_bdd_above compact_continuous_image compact_imp_bounded 
           compact_set_of_interval_list lipschitz_on_continuous_on lipschitz_on_subset sup_ge2) 
      subgoal  
        apply(auto)[1] 
        subgoal 
          by (smt (verit) excess_width_def inclusion_isotonic_inf sup_ge1 sup_set_of width_def width_set_def)
        subgoal 
          by (smt (verit, ccfv_threshold) lipschitz_on_subset sorted_wrt_upper_unroll sup_ge2)
        done 
      done
    done
qed

lemma Inf_interval_list_approx:  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     inclusion_isotonic: \<open>inclusion_isotonic F\<close>
  and     interval_extension: \<open>F is_interval_extension_of f\<close>
  and     sorted_upper: \<open>sorted_wrt_upper XS\<close>
  and     lipschitz:  \<open>0 \<le> C\<close> \<open>C-lipschitz_on ((set_of_interval_list XS)) f\<close>
  and     excess_width_bounded: \<open>(Max (set ((map (excess_width F f)) XS))) \<le> k\<close>
shows " Inf (set_of_interval_list (map F XS)) \<le> Inf (f ` set_of_interval_list XS) "
 using assms proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case 
    apply(simp add: set_of_interval_list_def set_of_eq)
    by (metis inclusion_isotonic_inf set_of_eq) 
next
  case (cons x xs)
  then show ?case 
    apply(simp add: set_of_interval_list_def set_of_eq)
    apply(subst image_Un)
    apply(subst cInf_union_distrib)
    subgoal 
      by simp
    subgoal 
      by simp
    subgoal 
      proof -
        assume "xs \<noteq> []"
        then have "set_of_interval_list (map F xs) \<noteq> {}"
          by (simp add: set_of_interval_list_nonempty)
        then show ?thesis
          by (simp add: set_of_eq set_of_interval_list_def)
      qed 
    subgoal 
    proof -
      have "\<forall>is. bdd_below (set_of_interval_list is::real set)"
        by (simp add: bounded_imp_bdd_below compact_imp_bounded compact_set_of_interval_list)
      then show ?thesis
        by (simp add: set_of_eq set_of_interval_list_def)
    qed 
    subgoal 
      apply(subst cInf_union_distrib)
      subgoal 
        by simp 
      subgoal 
        by (meson bounded_imp_bdd_below compact_Icc compact_continuous_image compact_imp_bounded 
                  lipschitz_on_continuous_on lipschitz_on_subset sup_ge1) 
      subgoal       
      proof -
        assume "xs \<noteq> []"
        then have "set_of_interval_list xs \<noteq> {}"
          by (simp add: set_of_interval_list_nonempty)
        then show ?thesis
          by (simp add: set_of_eq set_of_interval_list_def)
      qed
      subgoal       
      proof -
        assume "C-lipschitz_on ({lower x..upper x} \<union> foldr (\<lambda>x. (\<union>) {lower x..upper x}) xs {}) f"
        then have "C-lipschitz_on ({lower x..upper x} \<union> set_of_interval_list xs) f"
          by (simp add: set_of_eq set_of_interval_list_def)
        then have "bounded (f ` set_of_interval_list xs)"
          by (metis compact_imp_bounded compact_set_of_interval_list lipschitz_bounded_image_real lipschitz_on_subset sup_ge2)
        then show ?thesis
          by (simp add: bounded_imp_bdd_below set_of_eq set_of_interval_list_def)
      qed
      subgoal
        apply(simp, rule conjI)
        subgoal 
          using inclusion_isotonic_inf[of F f x, simplified assms set_of_eq, simplified]  
          by (smt (verit, ccfv_threshold) inclusion_isotonic_inf le_infI1 set_of_eq)     
        subgoal 
        proof -
          assume a1: "xs \<noteq> []"
          assume a2: "\<lbrakk>sorted_wrt_upper xs; C-lipschitz_on (foldr (\<lambda>x. (\<union>) {lower x..upper x}) xs {}) f\<rbrakk> \<Longrightarrow> Inf (foldr (\<lambda>x. (\<union>) {lower x..upper x}) (map F xs) {}) \<le> Inf (f ` foldr (\<lambda>x. (\<union>) {lower x..upper x}) xs {})"
          assume a3: "sorted_wrt_upper (x # xs)"
          assume "C-lipschitz_on ({lower x..upper x} \<union> foldr (\<lambda>x. (\<union>) {lower x..upper x}) xs {}) f"
          then have "C-lipschitz_on (foldr (\<lambda>i. (\<union>) {lower i..upper i}) xs {}) f"
            using lipschitz_on_mono by blast
          then show ?thesis
            using a3 a2 a1 by (meson le_infI2 sorted_wrt_upper_unroll)
        qed 
        done
      done 
    done 
qed

lemma Sup_interval_list_approx:  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     inclusion_isotonic: \<open>inclusion_isotonic F\<close>
  and     interval_extension: \<open>F is_interval_extension_of f\<close>
  and     sorted_lower: \<open>sorted_wrt_lower XS\<close>
  and     lipschitz:  \<open>0 \<le> C\<close> \<open>C-lipschitz_on ((set_of_interval_list XS)) f\<close>
  and     excess_width_bounded: \<open>(Max (set ((map (excess_width F f)) XS))) \<le> k\<close>
shows "Sup (f ` set_of_interval_list XS) \<le> Sup (set_of_interval_list (map F XS))"
 using assms proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case 
    apply(simp add: set_of_interval_list_def set_of_eq)
    by (metis inclusion_isotonic_sup set_of_eq) 
next
  case (cons x xs)
  then show ?case 
    apply(simp add: set_of_interval_list_def set_of_eq)
    apply(subst image_Un)
    apply(subst cSup_union_distrib)
    subgoal 
      by simp
    subgoal 
      by (meson bounded_imp_bdd_above compact_Icc compact_continuous_image compact_imp_bounded lipschitz_on_continuous_on lipschitz_on_subset sup_ge1) 
    subgoal 
    proof -
      assume a1: "xs \<noteq> []"
      have f2: "\<forall>R Ra is isa f fa. ((R::real set) \<noteq> Ra \<or> is \<noteq> isa \<or> (\<exists>R i. (i::real interval) \<in> set is \<and> f i R \<noteq> fa i R)) \<or> foldr f is R = foldr fa isa Ra"
        by (meson foldr_cong)
      obtain ii :: "(real interval \<Rightarrow> real set \<Rightarrow> real set) \<Rightarrow> (real interval \<Rightarrow> real set \<Rightarrow> real set) \<Rightarrow> real interval list \<Rightarrow> real interval" and RR :: "(real interval \<Rightarrow> real set \<Rightarrow> real set) \<Rightarrow> (real interval \<Rightarrow> real set \<Rightarrow> real set) \<Rightarrow> real interval list \<Rightarrow> real set" where
        "\<forall>x0 x1 x3. (\<exists>v6 v7. v7 \<in> set x3 \<and> x1 v7 v6 \<noteq> x0 v7 v6) = (ii x0 x1 x3 \<in> set x3 \<and> x1 (ii x0 x1 x3) (RR x0 x1 x3) \<noteq> x0 (ii x0 x1 x3) (RR x0 x1 x3))"
        by moura
      then have "\<forall>R Ra is isa f fa. (R \<noteq> Ra \<or> is \<noteq> isa \<or> ii fa f is \<in> set is \<and> f (ii fa f is) (RR fa f is) \<noteq> fa (ii fa f is) (RR fa f is)) \<or> foldr f is R = foldr fa isa Ra"
        using f2 by presburger
      then show ?thesis
        using a1 by (smt (z3) image_is_empty set_of_eq set_of_interval_list_def set_of_interval_list_nonempty)
    qed 
    subgoal 
    proof -
      assume "C-lipschitz_on ({lower x..upper x} \<union> foldr (\<lambda>x. (\<union>) {lower x..upper x}) xs {}) f"
      then have "C-lipschitz_on ({lower x..upper x} \<union> set_of_interval_list xs) f"
        by (simp add: set_of_eq set_of_interval_list_def)
      then have "bounded (f ` set_of_interval_list xs)"
        by (metis (no_types) compact_imp_bounded compact_set_of_interval_list lipschitz_bounded_image_real lipschitz_on_subset sup_ge2)
      then show ?thesis
        by (simp add: bounded_imp_bdd_above set_of_eq set_of_interval_list_def)
    qed 
    subgoal 
      apply(subst cSup_union_distrib)
      subgoal 
      by simp 
     subgoal 
       by (meson bdd_above_Icc)
      subgoal       
      proof -
        assume "xs \<noteq> []"
       then have "set_of_interval_list (map F xs) \<noteq> {}"
          by (simp add: set_of_interval_list_nonempty)
        then show ?thesis
          by (simp add: set_of_eq set_of_interval_list_def)
      qed 
      subgoal       
      proof -
        have "\<forall>is. bdd_above (set_of_interval_list is::real set)"
          by (simp add: bounded_imp_bdd_above compact_imp_bounded compact_set_of_interval_list)
        then show ?thesis
          by (simp add: set_of_eq set_of_interval_list_def)
      qed 
      subgoal
        apply(simp, rule conjI)
        subgoal 
          using inclusion_isotonic_sup[of F f x, simplified assms set_of_eq, simplified] le_supI1
          by auto
        subgoal
        proof -
          assume a1: "xs \<noteq> []"
          assume a2: "\<lbrakk>sorted_wrt_lower xs; C-lipschitz_on (foldr (\<lambda>x. (\<union>) {lower x..upper x}) xs {}) f\<rbrakk> \<Longrightarrow> Sup (f ` foldr (\<lambda>x. (\<union>) {lower x..upper x}) xs {}) \<le> Sup (foldr (\<lambda>x. (\<union>) {lower x..upper x}) (map F xs) {})"
          assume a3: "sorted_wrt_lower (x # xs)"
          assume a4: "C-lipschitz_on ({lower x..upper x} \<union> foldr (\<lambda>x. (\<union>) {lower x..upper x}) xs {}) f"
          have f5: "sorted_wrt_lower xs"
            using a3 a1 sorted_wrt_lower_unroll by blast
          have f6: "Sup (foldr (\<lambda>i. (\<union>) {lower i..upper i}) (map F xs) {}) \<le> sup (upper (F x)) (Sup (foldr (\<lambda>i. (\<union>) {lower i..upper i}) (map F xs) {}))"
            using sup_ge2 by blast
          have "C-lipschitz_on (foldr (\<lambda>i. (\<union>) {lower i..upper i}) xs {}) f"
            using a4 lipschitz_on_mono by blast
          then show ?thesis             
            using f6 f5 a2 by linarith
        qed 
        done
      done 
    done 
qed


lemma map_inclusion_isotonic_excess_width_bounded:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     inclusion_isotonic: \<open>inclusion_isotonic F\<close>
  and     interval_extension: \<open>F is_interval_extension_of f\<close>
  and     sorted_lower: \<open>sorted_wrt_lower XS\<close>   (* should not be required, relaxing this assumption requires updating several helper lemmata *)
  and     sorted_upper: \<open>sorted_wrt_upper XS\<close>(* should not be required, relaxing this assumption requires updating several helper lemmata *)
  and     lipschitz:  \<open>C-lipschitz_on ((set_of_interval_list XS)) f\<close>
  and     excess_width_bounded: \<open>(Max (set ((map (excess_width F f)) XS))) \<le> k\<close>
shows \<open>width_set (set_of_interval_list (map F XS)) - width_set (f ` (set_of_interval_list XS)) \<le> 2 * k\<close>
 and  \<open>width_set (set_of_interval_list (map F XS)) - width_set (f ` (set_of_interval_list XS)) \<ge> 0\<close>
  subgoal (* \<open>width_set (set_of_interval_list (map F XS)) - width_set (f ` (set_of_interval_list XS)) \<le> 2 * k\<close> *)
    unfolding width_set_def
    using lipschitz_on_nonneg[of C "((set_of_interval_list XS))" f, simplified assms, simplified]
          lower_bound_F_inf[of XS F f C k, simplified assms, simplified]
          upper_bound_F_sup[of XS F f C k, simplified assms, simplified]
    by(simp) 
  subgoal (* \<open>width_set (set_of_interval_list (map F XS)) - width_set (f ` (set_of_interval_list XS)) \<ge> 0\<close> *)    
    unfolding width_set_def
    using lipschitz_on_nonneg[of C "((set_of_interval_list XS))" f, simplified assms, simplified]
          Inf_interval_list_approx[of XS F f C k, simplified assms, simplified]
          Sup_interval_list_approx[of XS F f C k, simplified assms, simplified]
    by simp  
  done

lemma max_subdivision_excess_width_order:
  fixes X :: "real interval"
  assumes "inclusion_isotonic F" "lipschitzI_on C U F" "F is_interval_extension_of f"
  and "set (uniform_subdivision X N) \<subseteq> U"  "0 < N"
  and " L-lipschitz_on (set_of_interval_list (uniform_subdivision X N)) f " 
shows \<open>Max (set (map (excess_width F f) (uniform_subdivision X N))) \<le> C * width X / real N\<close>
proof(cases " (set (map (excess_width F f) (uniform_subdivision X N))) = {}")
  case True
  then show ?thesis 
   using non_empty_subdivision[of N X, simplified assms, simplified]
   by simp
next
  case False
  then show ?thesis 
    apply(subst set_map)   
    using each_subdivision_excess_width_order[of F C U f X N L, simplified assms, simplified]
          set_of_interval_list_set_eq_interval_list_union_contiguous[of "(uniform_subdivision X N)", simplified contiguous_uniform_subdivision[of X N] non_empty_subdivision[of N X, simplified assms, simplified], simplified]
    using assms(6) by auto[1] 
qed

lemma set_of_interval_list_set_eq_interval_list_union_contiguous:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     contiguous: \<open>contiguous XS\<close>
shows \<open>set_of_interval_list XS = set_of (interval_list_union XS)\<close>
  using interval_list_union_contiguous[of XS, simplified assms, simplified]
        set_of_interval_list_contiguous[of XS,simplified assms, simplified]
        contiguous_non_overlapping[of XS, simplified assms, simplified]
        non_overlapping_implies_sorted_wrt_upper[of XS]
        non_overlapping_implies_sorted_wrt_lower[of XS]
  interval_list_union_contiguous_lower[of XS] 
  interval_list_union_contiguous_upper[of XS]
  using set_of_eq non_empty by metis


lemma width_eq_wdith_set:
  fixes X :: \<open>('a::{conditionally_complete_lattice, minus, preorder}) interval\<close>
  shows  \<open>width X = width_set (set_of X)\<close>
  unfolding width_def set_of_eq width_set_def by(simp)

lemma width_zero_lower_upper:
  fixes X :: "real interval"
  assumes \<open>width X = 0\<close>
  shows \<open>lower X = upper X\<close>
  using assms width_def[of X]
  by simp

lemma width_zero_mk_interval:
  fixes X :: "real interval"
  assumes \<open>width X = 0\<close>
  shows \<open>\<exists> x. X = mk_interval(x,x)\<close>
  using assms width_def[of X]
  unfolding mk_interval'
  by (auto, metis Interval_id)

lemma width_zero_interval_of:
  fixes X :: "real interval"
  assumes \<open>width X = 0\<close>
  shows \<open>\<exists> x. X = interval_of x\<close>
  using assms width_def[of X]
  by (metis eq_iff_diff_eq_0 interval_eqI lower_interval_of upper_interval_of) 

lemma width_zero_interval_extension:
  fixes F :: "real interval \<Rightarrow> real interval"
  assumes \<open>F is_interval_extension_of f\<close>
  and     \<open>width X = 0\<close>
shows \<open>width (F X) = 0\<close>
  using assms width_zero_interval_of[of X, simplified assms, simplified]
  unfolding is_interval_extension_of_def
  by (metis add_0 add_diff_cancel lower_interval_of upper_interval_of width_def)

section \<open>Lipschitz Interval Inclusive\<close> 

text \<open>If @{term \<open>F\<close>} is a natural interval extension of a real valued rational function with 
@{term \<open>F(X)\<close>} defined for @{term \<open>X \<subseteq> Y\<close>} where @{term \<open>X\<close>} and @{term \<open>Y\<close>} are intervals or
n-dimentional interval vectors then @{term \<open>F\<close>} is Lipschitz in @{term \<open>Y\<close>}\<close>
 
lemma interval_extension_bounded:
  fixes F :: "real interval \<Rightarrow> real interval"
  assumes \<open>F is_interval_extension_of f\<close>
  and     \<open>(width (F X)) / (width X) \<le> L\<close>
shows "width (F X) \<le> L * width X"
proof(cases  "width X = 0")
  case True
  then show ?thesis 
    using width_zero_interval_extension[of F f X, simplified True assms, simplified]
    by auto
next
  case False
  then show ?thesis 
    using assms interval_width_positive[of X]
    by (metis mult.commute mult_right_mono nonzero_mult_div_cancel_left times_divide_eq_right) 
qed

lemma lipschitz_on_implies_lipschitzI_on:
  fixes F :: "real interval \<Rightarrow> real interval"
  assumes \<open>F is_interval_extension_of f\<close>
  and \<open>C-lipschitz_on X f\<close>
  and \<open>\<Union> (set_of ` Y) \<subseteq> X\<close>
  and \<open>0 \<le> L\<close>
  and \<open>\<forall> y \<in> Y. (width (F y)) / (width y) \<le> L\<close>
shows "L-lipschitzI_on Y F"
  unfolding lipschitzI_on_def
  using assms interval_extension_bounded
  by(auto)

lemma lipschitz_on_implies_lipschitzI_on2:
  fixes f :: \<open>real \<Rightarrow> real\<close>
  assumes \<open>S \<noteq> []\<close> and \<open>0 \<le> C\<close> 
   and \<open>F is_interval_extension_of f\<close>
   and \<open>0 \<le> L\<close>
   and \<open>\<forall> y \<in> (set S). (width (F y)) / (width y) \<le> L\<close>
   and \<open>C-lipschitz_on (set_of (interval_list_union (S))) f \<close>
  shows \<open>L-lipschitzI_on (set (S)) F\<close>
  apply(rule lipschitzI_onI)
  subgoal using assms interval_extension_bounded by blast  
  subgoal using assms by blast  
  done 


lemma width_img_Max:
  assumes \<open>finite S\<close>
  shows \<open>\<forall>x\<in>S. width (F x) \<le> Max (width ` F ` S)\<close>
  using assms by auto 
lemma width_Min:
  assumes \<open>finite S\<close>
  shows \<open>\<forall>x\<in>S. Min (width ` S) \<le> width x\<close>
  using assms by auto 

lemma lipschitzI_on_le_interval:
  fixes F  :: \<open>real interval \<Rightarrow> real interval\<close>
  assumes inc_isontonic_F: \<open>inclusion_isotonic F\<close>
      and lipschitzI_F:    \<open>C-lipschitzI_on {X} F\<close>
      and interval_inc:    \<open>x \<le> X\<close>
    shows \<open>width (F x) \<le> C * width X\<close>
  using assms
  unfolding inclusion_isotonic_def lipschitzI_on_def 
            width_def less_eq_interval_def
  by fastforce 

lemma lipschitzI_on_le_lipschitzI_on:
  fixes F  :: \<open>real interval \<Rightarrow> real interval\<close>
  assumes inc_isontonic_F: \<open>inclusion_isotonic F\<close>
      and lipschitzI_F:    \<open>C-lipschitzI_on {X} F\<close>
      and interval_inc:    \<open>x \<le> X\<close>
      and interval_ext:    \<open>F is_interval_extension_of f\<close>
    shows \<open>\<exists> L. L-lipschitzI_on {x} F\<close>
  apply(rule exI[of _ "C * (width X)/(width x)"]) 
  apply(subst lipschitzI_onI, simp_all add: assms)
  subgoal
    apply(rule conjI)
    subgoal 
      using width_zero_interval_extension[of F f x, simplified assms, simplified] 
      by simp 
    subgoal 
      using inc_isontonic_F interval_inc lipschitzI_F lipschitzI_on_le_interval by blast 
    done 
    using lipschitzI_on_le_interval[of F C X x, simplified assms , simplified]
  subgoal 
    using lipschitzI_on_nonneg assms
    by (metis divide_nonneg_nonneg interval_width_positive mult_nonneg_nonneg)  
  done 

lemma uniform_subdivision_le:
  fixes X  :: \<open>real interval\<close>
  assumes \<open>N>0\<close>
  shows \<open>\<forall> x \<in> set (uniform_subdivision X N). x \<le> X\<close>
  using last_upper_uniform_subdivision[of N X, simplified assms, simplified]
        hd_lower_uniform_subdivision[of N X, simplified assms, simplified]
        non_overlapping_implies_sorted_wrt_upper[of "(uniform_subdivision X N)", simplified uniform_subdivisions_non_overlapping assms, simplified]
        non_overlapping_implies_sorted_wrt_lower[of "(uniform_subdivision X N)", simplified uniform_subdivisions_non_overlapping assms, simplified]
  unfolding sorted_wrt_upper_def sorted_wrt_lower_def cmp_lower_width_def less_eq_interval_def
  by (metis (no_types, lifting) assms in_set_conv_nth interval_list_union_correct non_empty_subdivision set_of_subset_iff union_set)

lemma lipschitzI_on_uniform_subdivision:
  fixes F  :: \<open>real interval \<Rightarrow> real interval\<close>
  assumes inc_isontonic_F: \<open>inclusion_isotonic F\<close>
      and lipschitzI_F:    \<open>C-lipschitzI_on ({X}) F\<close>
      and \<open>N>0\<close>
    shows \<open>\<forall>x\<in>(set (uniform_subdivision X N)). width (F x) \<le> C * width X\<close>
  using lipschitzI_on_le_interval[of F C X, simplified assms, simplified]
        uniform_subdivision_le[of N X, simplified assms, simplified ]
  by simp 

lemma division_leq_pos:
  fixes x :: "'a::{linordered_field}"
  assumes "x > 0" and "y > 0" and "z > 0" and "y \<le> z"
  shows "x / z \<le> x / y"
proof -
  have "x * y \<le> x * z" using assms by simp
  hence "(x * y) / (y * z) \<le> (x * z) / (y * z)" 
    using assms 
    by (simp add: frac_le)
  thus ?thesis using assms by auto[1]  
qed

lemma each_subdivision_width_order':
  fixes X :: "real interval"
  assumes "F is_interval_extension_of f"
  and "0 < N"
  and "Xs \<in> set (uniform_subdivision X N)" 
shows "\<exists> L. width(F Xs) \<le> L * width (X) / of_nat N" 
  by (metis assms less_numeral_extra(3) mult_eq_0_iff nonzero_divide_eq_eq 
      of_nat_le_0_iff order_refl uniform_subdivisions_width width_zero_interval_extension) 

lemma uniform_subdivision_min_nonzero: 
  assumes \<open>N > 0\<close>
  and \<open>width X > 0\<close>
  shows \<open>0 < Min (width ` set (uniform_subdivision X N))\<close> 
  using assms unfolding image_set uniform_subdivision_def Let_def width_def
  by (simp, simp add: order_le_less) 

lemma uniform_subdivision_width_zero_replicate_eq: 
  fixes X::\<open>real interval\<close>
  assumes positive_N:  \<open>0 < N\<close> 
  and zero_width_X: \<open>0 = width X \<close>  
  shows\<open>replicate N X = (uniform_subdivision X N)\<close>
  using assms 
proof(induction N)
  case 0
  then show ?case 
    by simp
next
  case (Suc N)
  then show ?case 
    using width_zero_lower_upper[of X, simplified assms, simplified]
    unfolding uniform_subdivision_def
    by (simp, metis append.right_neutral map_replicate_trivial mk_interval_id replicate_app_Cons_same)
qed

lemma set_of_interval_list_zero_width:
  fixes X::\<open>real interval\<close>
  assumes positive_N:  \<open>0 < N\<close> 
  and zero_width_X: \<open>0 = width X \<close>  
  shows\<open>set_of_interval_list (uniform_subdivision X N) = {lower X..upper X}\<close>
proof(insert assms, simp add: uniform_subdivision_width_zero_replicate_eq[of N X, simplified assms, simplified, symmetric], induction N)
  case 0
  then show ?case 
    by(simp)
next
  case (Suc N)
  then show ?case 
    unfolding set_of_interval_list_def set_of_eq
    by(simp, fastforce)
qed

lemma  width_zero_subdivision: "width X = (0::real) ==> N > 0 \<Longrightarrow> set (uniform_subdivision X N) = {X}"
  using width_zero_lower_upper[of X]
  unfolding uniform_subdivision_def Let_def mk_interval'
  apply(auto simp add: image_def)[1]
  apply (metis Interval_id)
  apply (metis Interval_id)
  done 

lemma lipschitz_on_implies_lipschitzI_on_pre:
  fixes f :: \<open>real \<Rightarrow> real\<close>
 and F  :: \<open>real interval \<Rightarrow> real interval\<close>
  assumes \<open>finite S\<close>
   and \<open>0 < Min (width ` S)\<close>
 shows \<open>let max_F_width = Max (width ` (F ` S));
            min_f_width = Min (width ` S)
        in \<forall> x \<in> S. width (F x) \<le> (max_F_width/min_f_width) *  width x\<close>
  unfolding Let_def
  by (simp, smt (verit) assms division_leq_pos interval_width_positive mult_eq_0_iff 
          nonzero_mult_div_cancel_right width_Min width_img_Max zero_le_divide_iff) 

lemma lipschitz_on_implies_lipschitzI_on':
  fixes f :: \<open>real \<Rightarrow> real\<close>
    and F  :: \<open>real interval \<Rightarrow> real interval\<close>
  assumes   non_empty: \<open>S \<noteq> {}\<close>  
   and         finite: \<open>finite S\<close>
   and non_zero_width: \<open>0 < Min (width ` S)\<close>
   and interval_ext_F: \<open>F is_interval_extension_of f\<close>
 shows \<open>\<exists>  L. L-lipschitzI_on S F\<close>
  unfolding lipschitzI_on_def
  apply(rule exI[of _ "(Max (width ` (F ` S)))/(Min (width ` S))"])
  apply(rule conjI)
  subgoal 
    apply(rule divide_nonneg_nonneg)
    subgoal 
      using assms interval_width_positive
      by (metis (mono_tags, lifting) Max_in finite_imageI imageE image_is_empty) 
    subgoal 
      using assms interval_width_positive
      by(auto)[1]
    done 
  subgoal 
    by (meson assms lipschitz_on_implies_lipschitzI_on_pre) 
  done 


lemma natural_extension_transfer_lipschitz:
  assumes  positive_N: \<open>0 < N\<close> 
  and inc_isontonic_F: \<open>inclusion_isotonic F\<close>
  and  interval_ext_F: \<open>F is_natural_interval_extension_of f\<close>
  and     lipschitz_f: \<open>C-lipschitz_on (set_of X) f\<close> 
shows     \<open>C-lipschitzI_on (set (uniform_subdivision X N)) F\<close>
proof(cases "0 < width X")
  case True
  then show ?thesis    
  apply(subst lipschitzI_onI)
  subgoal 
    using assms
     each_subdivision_width_order'[of F f N _ X ]
     each_subdivision_width_order[of F C "set (uniform_subdivision X N)" f X N ]
     uniform_subdivision_le[of N X ]
    unfolding lipschitz_on_def is_natural_interval_extension_of_def 
              inclusion_isotonic_def 
    dist_real_def abs_real_def width_def mk_interval'
    apply(auto split:if_splits)[1]
    by (smt (z3) Interval_id interval_of.abs_eq interval_of_in_eq less_eq_interval_def lower_bounds lower_in_interval upper_bounds)
  subgoal 
    using assms lipschitz_on_nonneg by auto 
  subgoal by simp 
  done 
next
  case False
    have width_zero: \<open>width X = 0\<close>
    using False 
    by (meson interval_width_positive linorder_not_le nle_le) 
  have us_X: \<open>set (uniform_subdivision X N) = {X}\<close>
    using width_zero width_zero_subdivision
    using positive_N by blast 
  then show ?thesis
    using width_zero 
    apply(simp add:assms)
     apply(subst lipschitzI_onI)
    subgoal    using assms
     each_subdivision_width_order'[of F f N _ X ]
     each_subdivision_width_order[of F C "set (uniform_subdivision X N)" f X N ]
     uniform_subdivision_le[of N X ]
    unfolding lipschitz_on_def is_natural_interval_extension_of_def 
              inclusion_isotonic_def 
    dist_real_def abs_real_def width_def mk_interval'
    apply(auto split:if_splits)[1]
    by (meson interval_ext_F natural_interval_extension_implies_interval_extension) 
 subgoal 
    using assms lipschitz_on_nonneg by auto 
  subgoal by simp 
  done 
qed


lemma lipschitz_on_division_lipschitz_on:
  assumes lipschitz_f: "C-lipschitz_on (set_of X) f " 
    and non_empty: "uniform_subdivision  X N \<noteq> []" 
    and subdivision: "Xs \<in> set(uniform_subdivision (X::real interval) N)"
  shows "\<exists> L . L-lipschitz_on (set_of Xs) f"
proof - 
  fix L
  have subset: "Xs \<le> X" 
    using assms(3) uniform_subdivision_le[of N X] 
    by (metis (no_types, lifting) bot_nat_0.extremum_strict
        bot_nat_0.not_eq_extremum in_set_conv_nth length_map list.size(3) map_nth 
        uniform_subdivision_def)
  show ?thesis 
    by (meson assms(1) interval_set_leq_eq lipschitz_on_subset subset)
qed 

lemma lipschitz_on_lischitz_on_subdivisions:
 assumes lipschitz_f: "C-lipschitz_on (set_of X) f " 
    and non_empty: "uniform_subdivision  X N \<noteq> []" 
    and non_zero: "0 < N"
  shows "\<exists> L . \<forall> Xs \<in> set(uniform_subdivision (X::real interval) N). L-lipschitz_on (set_of Xs) f"
proof - 
  have subset: " \<forall> Xs \<in> set(uniform_subdivision (X::real interval) N) . Xs \<le> X" 
    using assms uniform_subdivision_le[of N X] by blast
  show  "\<exists> L. \<forall>Xs\<in>set (uniform_subdivision X N). L-lipschitz_on (set_of Xs) f"
  proof -
    obtain L where L: "L = C" using lipschitz_f by auto
    have "L-lipschitz_on (set_of Xs) f" if "Xs \<in> set (uniform_subdivision X N)" for Xs
    proof -
      show ?thesis using lipschitz_on_division_lipschitz_on[of C X f N Xs, simplified assms, simplified] L 
        by (meson interval_set_leq_eq lipschitz_f lipschitz_on_subset subset that) 
    qed
    thus ?thesis by auto
  qed
qed

lemma lipschitz_on_lischitz_on_subdivisions_n:
 assumes lipschitz_f: "C-lipschitz_on (set_of X) f " 
    and non_empty: "uniform_subdivision  X N \<noteq> []" 
    and non_zero: "0 < N"
  shows "\<exists> L . \<forall> N > 0 . \<forall> Xs \<in> set(uniform_subdivision (X::real interval) N). L-lipschitz_on (set_of Xs) f"
proof - 
  have subset: " \<forall> Xs \<in> set(uniform_subdivision (X::real interval) N) . Xs \<le> X" 
    using assms uniform_subdivision_le[of N X] by blast
  show  "\<exists> L.  \<forall> N > 0 . \<forall>Xs\<in>set (uniform_subdivision X N). L-lipschitz_on (set_of Xs) f"
  proof -
    obtain L where L: "L = C" using lipschitz_f by auto
    have "L-lipschitz_on (set_of Xs) f" if "Xs \<in> set (uniform_subdivision X N)" for Xs
    proof -
      show ?thesis using lipschitz_on_division_lipschitz_on[of C X f N Xs, simplified assms, simplified] L 
        by (meson interval_set_leq_eq lipschitz_f lipschitz_on_subset subset that) 
    qed
    thus ?thesis 
      by (meson interval_set_leq_eq lipschitz_f lipschitz_on_subset uniform_subdivision_le)
  qed
qed

lemma lipschitzI_on_division_lipschitzI_on:
  assumes lipschitz_f: "C-lipschitzI_on (set(uniform_subdivision X N)) F " 
    and non_empty: "uniform_subdivision  X N \<noteq> []" 
    and subdivision: "Xs \<in> set(uniform_subdivision (X::real interval) N)"
  shows "\<exists> L . L-lipschitzI_on {Xs} F"
proof - 
  fix L
  have subset: "Xs \<le> X" 
    using assms(3) uniform_subdivision_le[of N X] 
    by (smt (verit, del_insts) gr_zeroI list.map_disc_iff list.size(3) map_nth non_empty uniform_subdivision_def)
  show ?thesis 
    by (meson empty_subsetI insert_subset lipschitzI_on_le lipschitz_f subdivision)
qed 

lemma lipschitzI_on_lipschitzI_on_subdivisions:
  fixes X :: "real interval"
 assumes lipschitz_f: "C-lipschitzI_on (set(uniform_subdivision X N)) F "  
    and non_zero: "0 < N"
  shows "\<exists> L . \<forall> Xs \<in> set(uniform_subdivision X N). L-lipschitzI_on {Xs} F"
proof - 
  have subset: " \<forall> Xs \<in> set(uniform_subdivision (X::real interval) N) . Xs \<le> X" 
    using assms uniform_subdivision_le[of N X] by blast
  show  "\<exists>L. \<forall>Xs\<in>set (uniform_subdivision X N). L-lipschitzI_on {Xs} F"
  proof -
    obtain L where L: "L = C" using lipschitz_f by auto
    have "L-lipschitzI_on {Xs} F" if "Xs \<in> set (uniform_subdivision X N)" for Xs
    proof -
      show ?thesis using assms 
        by (simp add: L lipschitzI_on_def that) 
    qed
    thus ?thesis by auto
  qed
qed

section \<open>Lipschitz Convergence\<close>

lemma isotonic_lipschitz_refinement':
  assumes positive_N:  \<open>0 < N\<close> 
  and inc_isontonic_F: \<open>inclusion_isotonic F\<close>
  and interval_ext_F:  \<open>F is_interval_extension_of f\<close>
  and lipschitz_f:     \<open>C-lipschitz_on (set_of X) f\<close>
shows \<open>\<exists> L. width_set (set_of_interval_list (map F (uniform_subdivision X N))) - width_set (f ` (set_of X)) \<le> 2 * (L * width X / real N)\<close> 
proof (cases "0 < width X")
  case True
  have us_eq_set_of_X: \<open>(set_of_interval_list (uniform_subdivision X N)) = set_of X\<close>
    by (simp add: Lipschitz_Subdivisions_Refinements.set_of_interval_list_set_eq_interval_list_union_contiguous 
                 contiguous_uniform_subdivision non_empty_subdivision positive_N union_set)
  have lipschitz_f': \<open>C-lipschitz_on (set_of_interval_list (uniform_subdivision X N)) f\<close>
    by (simp add: lipschitz_f us_eq_set_of_X)
  have us_nonempty: \<open>uniform_subdivision  X N \<noteq> [] \<close>     
    by (simp add: assms(1) non_empty_subdivision)  
  have us_nonempty_set: \<open>set (uniform_subdivision X N) \<noteq> {}\<close>     
    by (simp add: us_nonempty)
  have us_finite: \<open>finite (set (uniform_subdivision X N))\<close>     
    by simp 
  have sorted_lower: \<open>sorted_wrt_lower (uniform_subdivision X N)\<close>
    by (simp add: contiguous_sorted_wrt_lower contiguous_uniform_subdivision) 
  have sorted_upper: \<open>sorted_wrt_upper (uniform_subdivision X N)\<close>
    by (simp add: contiguous_sorted_wrt_upper contiguous_uniform_subdivision) 
  have lipschitzI: \<open>\<exists>L. L-lipschitzI_on (set (uniform_subdivision X N)) F\<close>
    using lipschitz_on_implies_lipschitzI_on'[of "set (uniform_subdivision X N)" F f, simplified 
                                                 us_nonempty_set us_finite interval_ext_F]
          uniform_subdivision_min_nonzero[of N X, simplified positive_N True, simplified]
    by(simp)
  have set_of_interval_eq: \<open>(set_of_interval_list (uniform_subdivision X N)) = (set_of (interval_list_union (uniform_subdivision X N)))\<close>
    by (simp add: Lipschitz_Subdivisions_Refinements.set_of_interval_list_set_eq_interval_list_union_contiguous 
                  contiguous_uniform_subdivision us_nonempty) 
  have width_bounded: \<open>\<exists> L. Max (excess_width F f ` set (uniform_subdivision X N)) \<le> 2 * (L * width X / real N)\<close>
    using 
          each_subdivision_excess_width_order[of F _ "(set (uniform_subdivision X N))" f X N C, 
            simplified inc_isontonic_F interval_ext_F positive_N lipschitz_f'[simplified set_of_interval_eq], simplified] 
         max_subdivision_excess_width_order[of F _ "(set (uniform_subdivision X N))" f X N C, 
            simplified inc_isontonic_F interval_ext_F positive_N lipschitz_f', simplified] 
  proof -
    assume a1: "\<And>C. C-lipschitzI_on (set (uniform_subdivision X N)) F \<Longrightarrow> 
      Max (excess_width F f ` set (uniform_subdivision X N)) \<le> C * width X / real N"
    have "\<forall>r ra rb. (r::real) / rb * ra = r * ra / rb"
      by fastforce
    then show ?thesis
      using a1 by (metis \<open>\<exists>L. L-lipschitzI_on (set (uniform_subdivision X N)) F\<close> 
          divide_numeral_1 le_divide_eq_numeral1(1) mult_numeral_1 order_antisym_conv order_refl)
  qed 
 have width_limit:\<open>\<exists> L.    width_set (set_of_interval_list (map F (uniform_subdivision X N))) 
                          - width_set (f ` (set_of X))
                        \<le> 2 * (L * width X / real N)\<close>
    using width_bounded
          map_inclusion_isotonic_excess_width_bounded(1)[of "uniform_subdivision X N" F f C, 
             simplified us_nonempty interval_ext_F inc_isontonic_F sorted_lower sorted_upper lipschitz_f', simplified]
    by (metis (no_types, lifting) us_eq_set_of_X inc_isontonic_F interval_ext_F lipschitzI lipschitz_f' list.set_map 
              max_subdivision_excess_width_order order.refl positive_N)
  then show ?thesis
    by simp 
next
  case False
  have width_zero: \<open>width X = 0\<close>
    using False 
    by (meson interval_width_positive linorder_not_le nle_le) 
  have us_nonempty: \<open>uniform_subdivision X N \<noteq> [] \<close>     
    by (simp add: assms(1) non_empty_subdivision)  
  have set_of_interval_eq: \<open>(set_of (interval_list_union (uniform_subdivision X N))) = (set_of_interval_list (uniform_subdivision X N))\<close>
    by (simp add: Lipschitz_Subdivisions_Refinements.set_of_interval_list_set_eq_interval_list_union_contiguous 
                  contiguous_uniform_subdivision us_nonempty) 
  have w_zero_1: \<open>width_set (set_of_interval_list (map F (uniform_subdivision X N))) = 0\<close>
    by (metis (full_types) Lipschitz_Subdivisions_Refinements.set_of_interval_list_set_eq_interval_list_union_contiguous 
        contiguous_uniform_subdivision interval_ext_F map_replicate non_empty_subdivision positive_N 
        uniform_subdivision_width_zero_replicate_eq union_set width_eq_wdith_set width_zero width_zero_interval_extension)
  have w_zero_2: \<open> width_set (f ` (set_of X)) = 0\<close>
    using set_of_interval_list_zero_width[of N X, simplified positive_N width_zero, simplified]
          width_zero width_zero_lower_upper[of X, simplified width_zero, simplified]
    by (metis diff_ge_0_iff_ge inc_isontonic_F inf_le_sup_image_real interval_ext_F lipschitz_f nle_le 
              width_inclusion_isotonic_approx width_set_def width_zero_interval_extension) 
  then show ?thesis
    using width_zero w_zero_1 w_zero_2  
    by simp 
qed

lemma isotonic_lipschitz_refinementI:
  assumes positive_N:  \<open>0 < N\<close> 
  and inc_isontonic_F: \<open>inclusion_isotonic F\<close>
  and interval_ext_F:  \<open>F is_interval_extension_of f\<close>
  and lipschitz_f:     \<open>L-lipschitz_on (set_of X) f\<close> 
  and lipschitz_F:     \<open>C-lipschitzI_on (set (uniform_subdivision X N)) F\<close>
shows \<open>width_set (set_of_interval_list (map F (uniform_subdivision X N))) - width_set (f ` (set_of X)) \<le> 2 * (C * width X / real N)\<close> 
proof (cases "0 < width X")
  case True
  have us_eq_set_of_X: \<open>(set_of_interval_list (uniform_subdivision X N)) = set_of X\<close>
    by (simp add: Lipschitz_Subdivisions_Refinements.set_of_interval_list_set_eq_interval_list_union_contiguous 
                 contiguous_uniform_subdivision non_empty_subdivision positive_N union_set)
  have lipschitz_f': \<open>L-lipschitz_on (set_of_interval_list (uniform_subdivision X N)) f\<close>
    by (simp add: lipschitz_f us_eq_set_of_X)
  have us_nonempty: \<open>uniform_subdivision  X N \<noteq> [] \<close>     
    by (simp add: assms(1) non_empty_subdivision)  
  have us_nonempty_set: \<open>set (uniform_subdivision X N) \<noteq> {}\<close>     
    by (simp add: us_nonempty)
  have us_finite: \<open>finite (set (uniform_subdivision X N))\<close>     
    by simp 
  have sorted_lower: \<open>sorted_wrt_lower (uniform_subdivision X N)\<close>
    by (simp add: contiguous_sorted_wrt_lower contiguous_uniform_subdivision) 
  have sorted_upper: \<open>sorted_wrt_upper (uniform_subdivision X N)\<close>
    by (simp add: contiguous_sorted_wrt_upper contiguous_uniform_subdivision) 
  have lipschitzI: \<open>C-lipschitzI_on (set (uniform_subdivision X N)) F\<close>
    using lipschitz_F by blast
  have set_of_interval_eq: \<open>(set_of_interval_list (uniform_subdivision X N)) = (set_of (interval_list_union (uniform_subdivision X N)))\<close>
    by (simp add: Lipschitz_Subdivisions_Refinements.set_of_interval_list_set_eq_interval_list_union_contiguous 
                  contiguous_uniform_subdivision us_nonempty) 
  have width_bounded: \<open>Max (excess_width F f ` set (uniform_subdivision X N)) \<le> 2 * (C * width X / real N)\<close>
    using 
          each_subdivision_excess_width_order[of F C "(set (uniform_subdivision X N))" f X N _, 
            simplified inc_isontonic_F interval_ext_F positive_N lipschitz_f'[simplified set_of_interval_eq], simplified] 
         max_subdivision_excess_width_order[of F C "(set (uniform_subdivision X N))" f X N _, 
            simplified inc_isontonic_F interval_ext_F positive_N lipschitz_f', simplified]
    by (smt (verit) divide_nonneg_nonneg interval_width_positive lipschitzI_on_def lipschitz_F lipschitz_f' of_nat_0_less_iff positive_N split_mult_pos_le) 
 have width_limit:\<open>width_set (set_of_interval_list (map F (uniform_subdivision X N))) 
                          - width_set (f ` (set_of X))
                        \<le> 2 * (C * width X / real N)\<close>
    using width_bounded
    by (metis assms(3) inc_isontonic_F lipschitz_F lipschitz_f' map_inclusion_isotonic_excess_width_bounded(1) max_subdivision_excess_width_order order_le_less positive_N sorted_lower sorted_upper us_eq_set_of_X us_nonempty) 
    then show ?thesis
    by simp 
next
  case False
  have width_zero: \<open>width X = 0\<close>
    using False 
    by (meson interval_width_positive linorder_not_le nle_le) 
  have us_nonempty: \<open>uniform_subdivision X N \<noteq> [] \<close>     
    by (simp add: assms(1) non_empty_subdivision)  
  have set_of_interval_eq: \<open>(set_of (interval_list_union (uniform_subdivision X N))) = (set_of_interval_list (uniform_subdivision X N))\<close>
    by (simp add: Lipschitz_Subdivisions_Refinements.set_of_interval_list_set_eq_interval_list_union_contiguous 
                  contiguous_uniform_subdivision us_nonempty) 
  have w_zero_1: \<open>width_set (set_of_interval_list (map F (uniform_subdivision X N))) = 0\<close>
    by (metis (full_types) Lipschitz_Subdivisions_Refinements.set_of_interval_list_set_eq_interval_list_union_contiguous 
        contiguous_uniform_subdivision interval_ext_F map_replicate non_empty_subdivision positive_N 
        uniform_subdivision_width_zero_replicate_eq union_set width_eq_wdith_set width_zero width_zero_interval_extension)
  have w_zero_2: \<open> width_set (f ` (set_of X)) = 0\<close>
    using set_of_interval_list_zero_width[of N X, simplified positive_N width_zero, simplified]
          width_zero width_zero_lower_upper[of X, simplified width_zero, simplified]
    by (simp add: set_of_eq width_set_def) 
  then show ?thesis 
    using width_zero w_zero_1 w_zero_2  
    by simp 
qed

lemma isotonic_lipschitz_refinement:
  assumes positive_N:  \<open>0 < N\<close> 
  and inc_isontonic_F: \<open>inclusion_isotonic F\<close>
  and interval_ext_F:  \<open>F is_interval_extension_of f\<close>
  and lipschitz_f:     \<open>L-lipschitz_on (set_of X) f\<close> 
  and lipschitz_F:     \<open>C-lipschitzI_on (set (uniform_subdivision X N)) F\<close>
shows \<open>excess_width_set (refinement_set F N) f X \<le> 2 * (C * width X / real N)\<close>
  using isotonic_lipschitz_refinementI[of N F f L X C, simplified assms, simplified] 
  unfolding excess_width_set_def refinement_set_def by simp
       
end
