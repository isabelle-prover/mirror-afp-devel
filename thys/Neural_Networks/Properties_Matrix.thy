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

subsection\<open>Desirable Properties of Neural Networks Predictions (\thy)\<close>

theory Properties_Matrix
  imports
  Properties
  Prediction_Utils_Matrix
  Jordan_Normal_Form.Matrix
begin

definition zip_vec :: "'a Matrix.vec \<Rightarrow> 'b Matrix.vec \<Rightarrow> ('a \<times> 'b) Matrix.vec" where
  "zip_vec A B \<equiv> Matrix.vec (dim_vec A) (\<lambda> i. ((A $ i), (B $ i)))"

fun map_vec2 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c ) \<Rightarrow> 'a Matrix.vec \<Rightarrow> 'b Matrix.vec \<Rightarrow> 'c Matrix.vec \<close>
  where
"map_vec2 f xs ys = map_vec ( \<lambda> (x,y). f x y) (zip_vec xs ys)"

fun checkget_result_mat where
  \<open>checkget_result_mat _ None None           = (None, True)\<close>
 |\<open>checkget_result_mat \<epsilon> (Some xs) (Some ys) = (Some xs, fold (\<and>) (list_of_vec (map_vec2 (\<lambda> x y. x \<approx>[\<epsilon>]\<approx> y) xs ys)) True)\<close>
 |\<open>checkget_result_mat _ r _ = (r, False)\<close>

definition \<open>check_result_mat r \<epsilon> s = snd (checkget_result_mat \<epsilon> r s)\<close>
notation check_result_mat ("((_)/ \<approx>[(_)]\<approx>\<^sub>m (_))" [60, 60] 60)

definition ensure_testdata_range_mat :: \<open>real \<Rightarrow> real Matrix.vec list \<Rightarrow> (real Matrix.vec \<rightharpoonup> real Matrix.vec) \<Rightarrow> real Matrix.vec list \<Rightarrow> bool\<close>
  where
 \<open>ensure_testdata_range_mat delta inputs P outputs 
      = foldl (\<and>) True 
        (map (\<lambda> e. (P (fst e))  \<approx>[delta]\<approx>\<^sub>m Some (snd e)) 
             (zip inputs outputs))\<close>
notation ensure_testdata_range_mat ("(_) \<Turnstile>\<^sub>m {(_)} (_) {(_)}" [61, 3, 90, 3] 60)

paragraph\<open>Interval Arithmetic\<close>

definition \<open>intervals_of_mat \<delta> A = Matrix.vec (dim_vec A) (\<lambda> i. Interval((A$i)-\<bar>\<delta>\<bar>,(A$i)+\<bar>\<delta>\<bar>)) \<close>

definition \<open>intervals_of_m \<delta> = map (intervals_of_mat \<delta>) \<close>

fun check_result_mat_interval_mat :: \<open>'a::preorder Matrix.vec option \<Rightarrow> 'a interval Matrix.vec option \<Rightarrow> bool\<close> where
   \<open>check_result_mat_interval_mat None None           = True\<close> 
 | \<open>check_result_mat_interval_mat (Some xs) (Some ys) = fold (\<and>) (list_of_vec (map_vec2 (\<lambda> x y. x \<in> set_of y) xs ys)) True\<close> 
 | \<open>check_result_mat_interval_mat _ _ = False\<close>

notation check_result_mat_interval_mat ("((_)/ \<approx>\<^sub>m (_))" [60, 60] 60)

text \<open>We define @{term "check_result_mat_interval"} for checking that two matrices are approximatively 
equal (we need the error interval due to possible rounding errors in IEEE754 arithmetic in python 
compared to mathematical reals in Isabelle).\<close>

definition ensure_testdata_interval_mat :: \<open>real Matrix.vec list \<Rightarrow> (real Matrix.vec \<rightharpoonup> real Matrix.vec) \<Rightarrow> real interval Matrix.vec list \<Rightarrow> bool\<close> 
  where 
 \<open>ensure_testdata_interval_mat inputs P outputs 
      = foldl (\<and>) True 
        (map (\<lambda> e . let a = (P  (fst e)) in let b = Some (snd e) in (a \<approx>\<^sub>m b))
             (zip inputs outputs)) \<close>
notation ensure_testdata_interval_mat ("\<Turnstile>\<^sub>i\<^sub>m {(_)} (_) {(_)}" [3, 90, 3] 60)


text \<open>Using @{term "check_result_mat_interval"} we now define the property 
@{term "ensure_testdata_interval"} to check that the (symbolically) computed predictions of a neural 
network meet our expectations.\<close>

subsubsection\<open>Maximum Classifiers\<close>

definition
  ensure_testdata_max_mat :: \<open>real Matrix.vec list \<Rightarrow> (real Matrix.vec \<rightharpoonup> real Matrix.vec) \<Rightarrow> real Matrix.vec list \<Rightarrow> bool\<close> 
  where
 \<open>ensure_testdata_max_mat inputs P outputs 
   = foldl (\<and>) True
      (map (\<lambda> e. case P (fst e) of 
                   None \<Rightarrow> False 
                 | Some p \<Rightarrow> pos_of_max p = pos_of_max (snd e))
           (zip inputs outputs))\<close>
notation ensure_testdata_max_mat ("\<Turnstile>\<^sub>m {(_)} (_) {(_)}" [3, 90, 3] 60)

text \<open>Many classification networks use the maximum output as the result, without normalisation 
(e.g., to values between 0 and 1). In such cases, a weaker form of ensuring compliance to 
predictions might be used that only checks that checks for the maximum output of each given input, 
this can be tested using @{term "ensure_testdata_max"}\<close>
end
