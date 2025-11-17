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
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

section\<open>Desirable Properties of Neural Networks Predictions\<close>

theory Properties
imports 
  Prediction_Utils 
  "HOL-Library.Interval"
  "HOL-Library.Interval_Float"
begin 

subsection\<open>Approximate Comparison of Results\<close>
definition \<open>approx a \<epsilon> b = (\<bar>a-b\<bar> \<le> \<epsilon>)\<close>
notation approx ("((_)/ \<approx>[(_)]\<approx> (_))" [60, 60] 60)

fun checkget_result_list where
   \<open>checkget_result_list _ None None           = (None,True)\<close> 
 | \<open>checkget_result_list \<epsilon> (Some xs) (Some ys) = (Some xs, fold (\<and>) (map2 (\<lambda> x y. x \<approx>[\<epsilon>]\<approx> y)  xs ys) True)\<close>
 | \<open>checkget_result_list _ r _ = (r,False)\<close>

definition \<open>check_result_list r \<epsilon> s = snd (checkget_result_list \<epsilon> r s)\<close>
notation check_result_list ("((_)/ \<approx>[(_)]\<approx>\<^sub>l (_))" [60, 60] 60)

fun checkget_result_singleton where
   \<open>checkget_result_singleton _ None None         = (None,True)\<close> 
 | \<open>checkget_result_singleton \<epsilon> (Some x) (Some y) = (Some x, x \<approx>[\<epsilon>]\<approx> y)\<close>
 | \<open>checkget_result_singleton _ r _ = (r,False)\<close>

definition \<open>check_result_singleton r \<epsilon> s = snd (checkget_result_singleton \<epsilon> r s)\<close>
notation check_result_singleton ("((_)/ \<approx>[(_)]\<approx>\<^sub>s (_))" [60, 60] 60)

definition 
  ensure_testdata_range_list :: \<open>real \<Rightarrow> real list list \<Rightarrow> (real list \<rightharpoonup> real list) \<Rightarrow> real list list \<Rightarrow> bool\<close> 
  where
 \<open>ensure_testdata_range_list delta inputs P outputs
   =  foldl (\<and>) True
      (map (\<lambda> e. (P (fst e))  \<approx>[delta]\<approx>\<^sub>l Some (snd e))
           (zip inputs outputs))\<close>     
notation ensure_testdata_range_list ("(_) \<Turnstile>\<^sub>l {(_)} (_) {(_)}" [61, 3, 90, 3] 60)


subsubsection\<open>Interval Arithmetic\<close>
definition interval_distance :: \<open>'a::{preorder,minus, zero, ord} interval \<Rightarrow> 'a interval \<Rightarrow> 'a\<close> where
          \<open>interval_distance a b = (let (la, ua) = bounds_of_interval a;
                                        (lb, ub) = bounds_of_interval b
                                    in if ua \<le> lb then lb - ua
                                                   else if ub \<le> la then la -ub
                                                                    else 0)\<close>

fun intervals_of_list where 
   \<open>intervals_of_list _ [] = []\<close>
 | \<open>intervals_of_list \<delta> (x#xs) = (Interval (x- \<bar>\<delta>\<bar>, x+\<bar>\<delta>\<bar>))#(intervals_of_list \<delta> xs)\<close>

definition \<open>intervals_of_l \<delta> = map (intervals_of_list \<delta>)\<close>

lemma intervall_in_implies_set: " (x \<in> {a..b}) \<Longrightarrow> (x \<in> set_of (Interval (a,b))) "
  by (metis atLeastAtMost_iff dual_order.trans fst_conv lower_Interval set_of_eq snd_conv upper_Interval) 

lemma in_set_interval: "a \<le>b \<Longrightarrow> (x \<in> set_of (Interval (a,b))) = (x \<in> {a..b})"
  by (simp add: lower_Interval set_of_eq upper_Interval) 

fun check_result_list_interval_list :: \<open>'a::preorder list option \<Rightarrow> 'a interval list option \<Rightarrow> bool\<close> where
   \<open>check_result_list_interval_list None None           = True\<close> 
 | \<open>check_result_list_interval_list (Some xs) (Some ys) = fold (\<and>) (map2 (\<lambda> x y. x \<in> set_of y)  xs ys) True\<close> 
 | \<open>check_result_list_interval_list _ _ = False\<close>

notation check_result_list_interval_list ("((_)/ \<approx>\<^sub>l (_))" [60, 60] 60)

text \<open>We define @{term "check_result_list_interval"} for checking that two lists are approximatively 
equal (we need the error interval due to possible rounding errors in IEEE754 arithmetic in python 
compared to mathematical reals in Isabelle).\<close>

definition
  ensure_testdata_interval_list :: \<open>real list list \<Rightarrow> (real list \<rightharpoonup> real list) \<Rightarrow> real interval list list \<Rightarrow> bool\<close> 
  where
 \<open>ensure_testdata_interval_list inputs P outputs
   =  foldl (\<and>) True
      (map (\<lambda> e. let a = (P (fst e)) in let b = Some (snd e) in (a \<approx>\<^sub>l b))
           (zip inputs outputs))\<close>     

notation ensure_testdata_interval_list ("\<Turnstile>\<^sub>i\<^sub>l {(_)} (_) {(_)}" [3, 90, 3] 60)

text \<open>Using @{term "check_result_list_interval"} we now define the property 
@{term "ensure_testdata_interval"} to check that the (symbolically) computed predictions of a neural 
network meet our expectations.\<close>

subsection\<open>Maximum Classifiers\<close>
definition
  ensure_testdata_max_list :: \<open>real list list \<Rightarrow> (real list \<rightharpoonup> real list) \<Rightarrow> real list list \<Rightarrow> bool\<close> 
  where
 \<open>ensure_testdata_max_list inputs P outputs 
   =  foldl (\<and>) True
      (map (\<lambda> e. case P (fst e) of 
                   None \<Rightarrow> False 
                 | Some p \<Rightarrow> pos_of_max p = pos_of_max (snd e)) 
           (zip inputs outputs))\<close>
notation ensure_testdata_max_list ("\<Turnstile>\<^sub>l {(_)} (_) {(_)}" [3, 90, 3] 60)

text \<open>Many classification networks use the maximum output as the result, without normalisation 
(e.g., to values between 0 and 1). In such cases, a weaker form of ensuring compliance to 
predictions might be used that only checks that checks for the maximum output of each given input, 
this can be tested using @{term "ensure_testdata_max"}\<close>

definition ensure_delta_min :: \<open>real \<Rightarrow> (real list \<rightharpoonup> real list) \<Rightarrow> bool\<close> where 
          \<open>ensure_delta_min \<delta> P = (\<forall> xs \<in> ran P. \<delta> \<le> \<delta>\<^sub>m\<^sub>i\<^sub>n xs)\<close>
notation ensure_delta_min ("(_) \<Turnstile> (_)" [61, 90] 60)

lemma ensure_delta_min_dom: \<open>ensure_delta_min \<delta> P = (\<forall> x \<in> dom P. \<delta> \<le> \<delta>\<^sub>m\<^sub>i\<^sub>n (the (P x)))\<close>
  by(auto simp add:ensure_delta_min_def dom_def ran_def)

text \<open>
Further properties that we formalised can increase the confidence in the predictions of a neural 
network by reducing the likelihood of ambiguous classification results. This includes, e.g., the
requirement that for a given input, the classification outputs have at least a
given minimum distance (e.g., avoiding situations where all classification
outputs show nearly identical values) shown in @{term "ensure_delta_min"}.\<close>

subsection\<open>Distance-based Properties\<close>

subsubsection\<open>Distance and Measurements\<close>

locale distance = 
  fixes d::\<open>'a list \<Rightarrow> 'a list \<Rightarrow> ('b::{linordered_ab_group_add})\<close>
  assumes identity: \<open>\<lbrakk>length x = length y\<rbrakk> \<Longrightarrow> (d x y = 0) = (x = y)\<close>
  and symmetry:     \<open>(d x y = d y x)\<close>
  and triangle_inequality: \<open>\<lbrakk>length x = length y ; length z = length y\<rbrakk> \<Longrightarrow> (d x z \<le> d x y + d y z)\<close>
begin

lemma zero: \<open>(d x y = 0) = (x = y) \<or> (length x \<noteq> length y)\<close>
  using distance_axioms distance_def by fastforce 

lemma \<open>\<lbrakk>length x = length y ; length z = length y\<rbrakk> \<Longrightarrow> d x y + d y x \<ge> d x x\<close>
  using distance.triangle_inequality distance_axioms by blast

lemma  \<open>length x = length y \<Longrightarrow> 0 \<le> d x y\<close>
  using distance_axioms distance_def
        linordered_ab_group_add_class.zero_le_double_add_iff_zero_le_single_add
  by (metis (mono_tags, opaque_lifting))

end 


definition mapfoldr :: \<open>('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'c\<close> where 
\<open>mapfoldr map_f fold_f e xs ys = foldr fold_f (map2 (\<lambda> e0 e1 . map_f e0 e1) xs ys) e\<close>

definition hamming::\<open>'a list \<Rightarrow> 'a list \<Rightarrow> nat\<close> where
          \<open>hamming x y = mapfoldr (=) (\<lambda> e a. if e then a else a + 1) 0 x y\<close>



lemma hamming_identity: \<open>length x = length y \<Longrightarrow> (hamming x y = 0) = (x = y)\<close>
proof(induction rule:list_induct2)
  case Nil
  then show ?case 
    by (simp add: hamming_def mapfoldr_def) 
next
  case (Cons x xs y ys) note * = this
  then show ?case 
    by (simp add: hamming_def mapfoldr_def) 
qed

lemma hamming_symmetry: \<open>hamming x y = hamming y x\<close>
  apply(simp add: hamming_def mapfoldr_def)
  using list_all2_all_nthI[where P="(=)", unfolded list.rel_eq]
  by (smt (verit, best) map2_map_map map_eq_conv zip_commute zip_map_fst_snd)

lemma hamming_unroll: "\<lbrakk>length xs = length ys\<rbrakk> 
      \<Longrightarrow> hamming (x#xs) (y#ys) = (if x = y then hamming xs ys else 1 + hamming xs ys)"
proof(cases "x = y")
  case True
  then show ?thesis by(simp add: hamming_def mapfoldr_def)
next
  case False
  then show ?thesis by(simp add: hamming_def mapfoldr_def)
qed

lemma hamming_triangle_inequality: 
    \<open>\<lbrakk>length xs = length ys ; length ys = length zs\<rbrakk> 
\<Longrightarrow> hamming xs zs \<le> hamming xs ys + (hamming ys zs)\<close>
proof(induction rule:list_induct3)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys z zs)
  then show ?case
    by (simp add: hamming_unroll)
qed

global_interpretation hamming_distance: distance hamming
  apply(unfold_locales)
  subgoal by(simp add: hamming_identity)  
  subgoal by(simp add: hamming_symmetry)  
  subgoal by (metis hamming_triangle_inequality of_nat_add of_nat_le_iff)
  done

definition manhattan::\<open>real list \<Rightarrow> real list \<Rightarrow> real\<close> where
          \<open>manhattan = mapfoldr (\<lambda> x y . \<bar>x-y\<bar>) (+)  0\<close>

  lemma manhattan_unroll: "\<lbrakk>length xs = length ys\<rbrakk> 
        \<Longrightarrow> manhattan (x#xs) (y#ys) = \<bar>x - y\<bar> + manhattan xs ys"
    by(simp add: manhattan_def mapfoldr_def)
  
  
  lemma manhattan_positive: \<open>length x = length y \<Longrightarrow> 0 \<le> manhattan x y\<close>
  proof(induction rule:list_induct2)
    case Nil
    then show ?case by (simp add: manhattan_def mapfoldr_def)
  next
    case (Cons x xs y ys) note * = this
    then show ?case 
      using manhattan_unroll[of xs ys x y] by simp 
  qed
  
  lemma manhattan_identity: \<open>length x = length y \<Longrightarrow> (manhattan x y = 0) = (x = y)\<close>
  proof(induction rule:list_induct2)
    case Nil
    then show ?case by (simp add: manhattan_def mapfoldr_def)
  next
    case (Cons x xs y ys) note * = this
    then show ?case 
      proof(cases "x = y")
        case True
        then show ?thesis 
      using manhattan_unroll[of xs ys x y]
      by (simp add: Cons.IH Cons.hyps)
      next
        case False
        then show ?thesis 
        using manhattan_unroll[of xs ys x y] * manhattan_positive
        by (simp add: add_nonneg_eq_0_iff) 
      qed
  qed

lemma manhattan_symmetry: \<open>manhattan x y = manhattan y x\<close>
  apply (induct x y rule:list_induct2')
  subgoal by(simp add: manhattan_def mapfoldr_def) 
  subgoal by(simp add: manhattan_def mapfoldr_def) 
  subgoal by(simp add: manhattan_def mapfoldr_def) 
  subgoal by(simp add: manhattan_def mapfoldr_def) 
  done

lemma manhattan_triangle_inequality: 
    \<open>\<lbrakk>length xs = length ys ; length ys = length (zs::real list)\<rbrakk> 
\<Longrightarrow> manhattan xs zs \<le> manhattan xs ys + (manhattan ys zs)\<close>
proof(induction rule:list_induct3)
  case Nil
  then show ?case by(simp add:manhattan_def mapfoldr_def)   
next
  case (Cons x xs y ys z zs)
  then show ?case
    by (simp add: manhattan_unroll)
qed

global_interpretation manhattan_distance: distance manhattan
  apply(unfold_locales)
  subgoal by(simp add: manhattan_identity)
  subgoal by(simp add: manhattan_symmetry)  
  subgoal by(simp add: manhattan_triangle_inequality)
  done

definition avg_difference::\<open>real list \<Rightarrow> real list \<Rightarrow> real\<close> where
          \<open>avg_difference xs ys = (manhattan xs ys) / (min (length xs) (length ys))\<close>

global_interpretation avg_difference_distance: distance avg_difference
  apply(unfold_locales)
  subgoal using avg_difference_def distance_def manhattan_distance.distance_axioms
    by fastforce
  subgoal using avg_difference_def distance_def manhattan_distance.distance_axioms
    by (metis min.commute)
  subgoal unfolding avg_difference_def distance_def manhattan_distance.distance_axioms
    by (metis add_divide_distrib divide_right_mono manhattan_distance.triangle_inequality of_nat_0_le_iff)
  done


definition euclidean::\<open>real list \<Rightarrow> real list \<Rightarrow> real\<close> where
          \<open>euclidean X Y = sqrt (mapfoldr (\<lambda> x y . (x-y)\<^sup>2) (+)  0 X Y)\<close>

lemma euclidean_positive: \<open>length x = length y \<Longrightarrow> 0 \<le> euclidean x y\<close>
  proof(induction rule:list_induct2)
    case Nil
    then show ?case 
      by(simp add: euclidean_def mapfoldr_def)
  next
    case (Cons x xs y ys)
    then show ?case 
      by(simp add: euclidean_def mapfoldr_def)
  qed

lemma euclidean_identity: \<open>length x = length y \<Longrightarrow> (euclidean x y = 0) = (x = y)\<close>
proof(induction rule:list_induct2)
  case Nil
  then show ?case by(simp add: euclidean_def mapfoldr_def)
next
  case (Cons x xs y ys) note * = this
  then show ?case  
  proof(cases "x = y")
    case True
    then show ?thesis using * by(simp add: euclidean_def mapfoldr_def)
  next
    case False note ** = this
    then have ***: \<open> x \<noteq> y \<Longrightarrow> 0 \<noteq> (x - y)\<^sup>2\<close> by simp
    then show ?thesis apply(simp add: euclidean_def euclidean_positive * ** *** mapfoldr_def)
      using ** euclidean_positive[unfolded euclidean_def mapfoldr_def, simplified]
      by (simp add: Cons.hyps add_nonneg_eq_0_iff)  
  qed
qed 


lemma euclidean_symmetry: \<open>euclidean x y = euclidean y x\<close>
  apply (induct x y rule:list_induct2')
  subgoal by(simp add: euclidean_def mapfoldr_def) 
  subgoal by(simp add: euclidean_def mapfoldr_def) 
  subgoal by(simp add: euclidean_def mapfoldr_def) 
  subgoal by(simp add: euclidean_def mapfoldr_def power2_commute) 
  done

definition 
  check :: \<open>('a list \<Rightarrow> 'a list \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list \<rightharpoonup> 'a list) 
             \<Rightarrow> ('a list option \<Rightarrow>  'a list option \<Rightarrow> bool) \<Rightarrow> bool\<close> where
 \<open>check d P input\<^sub>r\<^sub>e\<^sub>f prediction P' 
        = (\<forall> x \<in> dom prediction. P(d input\<^sub>r\<^sub>e\<^sub>f x) \<longrightarrow> P' (prediction x) (prediction input\<^sub>r\<^sub>e\<^sub>f))\<close>


lemma " ((\<forall> l \<in> dom prediction. P(dist i l) \<longrightarrow> P' (prediction l) (prediction i)))
      = ((\<forall> l \<in> {l \<in> dom prediction .  P (dist i l)}.  P' (prediction l)  (prediction i)))"
  by auto 


lemma hamming_update_1: 
  "length xs = length ys \<Longrightarrow> hamming xs ys \<le> 1 \<Longrightarrow> (\<exists> i. xs = ys[i := xs!i])"
proof(induction rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x' xs' y' ys')
  then show ?case unfolding hamming_def mapfoldr_def
  proof(cases "x' = y'") 
    case True note * = this
    then have h: "hamming xs' ys' \<le> 1" using hamming_unroll by (metis Cons.hyps Cons.prems) 
    then show ?thesis 
    proof -
      obtain i where xs'_eq: "xs' = ys'[i := xs'!i]" using Cons.IH h by blast
      show ?thesis
      proof (cases i)
        case 0
        then show ?thesis 
          apply (intro exI[of _ "Suc 0"])
          apply simp
          using xs'_eq * by simp
      next
        case (Suc j)
        then show ?thesis
          apply (intro exI[of _ "Suc (Suc j)"])
          apply (simp split: nat.splits)
          using xs'_eq * Suc by simp
      qed
    qed
  next
    case False note ** = this
    then show ?thesis proof(cases " hamming xs' ys' = 0")
      case True
      then show ?thesis using hamming_identity 
        by (metis Cons.hyps list_update_code(2) nth_Cons_0)
    next
      case False
      then have h: \<open>hamming xs' ys' = 1\<close> using ** Cons.hyps Cons.prems hamming_unroll 
        by fastforce 
      then show ?thesis
        apply(intro exI[of _ "0"])
        apply simp
        using h Cons.hyps Cons.prems hamming_unroll **
        by (metis add_le_same_cancel1 not_one_le_zero)
    qed
  qed
qed

lemma hamming_cases1:
  assumes l: \<open>length xs = length ys\<close>
  and h: \<open>hamming xs ys \<le> 1\<close>
  and p: \<open>P xs\<close>
  and u: \<open>\<And> i. i  < length xs \<and> ys = xs[i := (ys!i)] \<Longrightarrow> P ys\<close>
shows \<open>P ys\<close>
proof(insert assms, induct "xs")
  case Nil
  then show ?case by simp
next
  case (Cons x' xs')
  then show ?case  
    using hamming_update_1[of "x'#xs'" "ys"]
          hamming_update_1 One_nat_def linorder_not_le list_update_beyond
    by (metis hamming_symmetry) 
qed


lemma hamming_update_2: 
  "length xs = length ys \<Longrightarrow> hamming xs ys \<le> 2 \<Longrightarrow> (\<exists> i j. xs = (ys[i := xs!i])[j:= xs!j])"
proof(induction rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case 
    by (metis Suc_1 Suc_eq_plus1_left Suc_le_mono hamming_unroll hamming_update_1 
              list_update_code(2) list_update_code(3) nth_Cons_0 nth_Cons_Suc) 
qed

lemma hamming_cases2:
  assumes l: \<open>length xs = length ys\<close>
  and h: \<open>hamming xs ys \<le> 2\<close>
  and p: \<open>P xs\<close>
  and u: \<open>\<And> i j. i < length xs \<and> j < length xs \<and> ys = xs[i := ys!i,j := ys!j] \<Longrightarrow> P ys\<close>
shows \<open>P ys\<close>
proof(insert assms, induct "xs")
  case Nil
  then show ?case by simp
next
  case (Cons x' xs')
  then show ?case  
    using  hamming_update_2[of "x'#xs'" "ys"]
    by (metis  hamming_symmetry hamming_update_2 length_list_update list_update_beyond
               list_update_id verit_comp_simplify1(3))
  qed

lemma hamming_update_n:
  "length xs = length ys \<Longrightarrow> hamming xs ys = Suc n \<Longrightarrow> (\<exists> i. hamming xs (ys[i := xs!i]) = n)"
proof(induction rule:list_induct2)
  case Nil
  then show ?case unfolding hamming_def mapfoldr_def by simp 
next
  case (Cons x xs y ys)
  then show ?case 
  by (metis Suc_eq_plus1_left diff_Suc_1 hamming_unroll length_list_update list_update_code(2) 
            list_update_code(3) nth_Cons_0 nth_Cons_Suc)
qed

lemma hamming_update_3: 
  "length xs = length ys \<Longrightarrow> hamming xs ys \<le> 3 \<Longrightarrow> (\<exists> i j k. xs = ys[i := xs!i,j:= xs!j,k:=xs!k])"
proof(induction rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case proof(cases "hamming xs ys =3")
    case True
    then show ?thesis 
          using  hamming_update_n hamming_update_2
          by (metis (mono_tags, opaque_lifting) Cons.hyps Cons.prems One_nat_def Suc_1 le_Suc_eq 
                     length_Cons length_list_update list_update_id numeral_3_eq_3)
  next
    case False note * = this
    then show ?thesis 
    proof(cases "hamming xs ys < 3")
      case True
      then show ?thesis 
        by (metis Cons.hyps One_nat_def Suc_1 hamming_update_2 less_Suc_eq_le list_update_code(2) 
                  list_update_code(3) nth_Cons_0 nth_Cons_Suc numeral_3_eq_3)
    next
      case False
      then show ?thesis 
        using * Cons.prems Cons.hyps hamming_unroll[of "xs" "ys" "x" "y"] 
        by(simp split:if_splits) 
    qed
  qed
qed

lemma hamming_cases3:
  assumes l: \<open>length xs = length ys\<close>
  and h: \<open>hamming xs ys \<le> 3\<close>
  and p: \<open>P xs\<close>
  and u: \<open>\<And> i j k. i < length xs \<and> j < length xs \<and> k < length xs \<and> ys = xs[i := ys!i,j := ys!j,k := ys!k] \<Longrightarrow> P ys\<close>
shows \<open>P ys\<close>
proof(insert assms, induct "xs")
  case Nil
  then show ?case by simp
next
  case (Cons x' xs')
  then show ?case proof(cases "hamming (x'#xs') ys = 3")
    case True
    then show ?thesis 
      using hamming_symmetry hamming_update_2 hamming_update_3 Cons.prems linorder_not_le 
            length_list_update length_Cons list_update_id list_update_beyond
      apply(simp)
      by (smt (verit, del_insts) Cons.prems(2) Cons.prems(4) hamming_symmetry hamming_update_3 
              length_Cons length_list_update linorder_not_le list_update_beyond list_update_id) 
  next
    case False
    then have h: "hamming (x'#xs') ys \<le> 2" using Cons.prems by simp
    then show ?thesis 
        using hamming_cases2 Cons.prems
        by (metis list_update_id)
  qed
qed

end
