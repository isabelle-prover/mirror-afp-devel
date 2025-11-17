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

section \<open>Proofs and Definitions that Enrich the Matrix Formalization\<close>

theory
  Matrix_Utils
  imports
    Jordan_Normal_Form.Matrix
    "HOL-Combinatorics.Permutations"
begin

text\<open>
  This theory provides additional definition and lemmas that are useful when working with vectors 
  and matrices as provided @{theory "Jordan_Normal_Form.Matrix"}. Furthermore, this theory contains
  additional theorems over lists, in particular of properties of @{const "map2"} (and,hence, 
  @{const "zip"}.
\<close>

subsection\<open>List Properties\<close>



lemma map2_to_map_idx_eq: 
  \<open>length xs = length ys \<Longrightarrow> (map2 (*) xs (ys)) = map (\<lambda> i. xs!i * ys!i) [0..< length xs]\<close>
  using map2_map_map map_nth
  by metis 

lemma map2_to_map_idx: 
  \<open>(map2 (*) xs (ys)) = map (\<lambda> i. xs!i * ys!i) [0..< min (length xs) (length ys)]\<close>
  by (rule nth_equalityI, auto)

lemma map2_mult_commute: 
  \<open>map2 (*) (xs::'a::comm_ring list) ys = map2 (*) ys xs\<close>
  by (induction xs ys rule:list_induct2', simp_all add: mult.commute)

subsection\<open>Vector and Matrix Properties\<close>

definition mult_vec_mat :: " 'a Matrix.vec \<Rightarrow> 'a :: semiring_0 Matrix.mat \<Rightarrow> 'a Matrix.vec" (infixl "\<^sub>v*" 70)
  where "v \<^sub>v* A \<equiv> vec (dim_col A) (\<lambda> i. col A i \<bullet> v)"

lemma dim_mult_vec_mat: \<open>dim_vec (v \<^sub>v* A) = dim_col A\<close>
  by (auto simp add: mult_vec_mat_def)

lemma index_mult_vec_mat: \<open> i < dim_col A \<Longrightarrow> (v \<^sub>v* A) $ i = col A i \<bullet> v\<close>
  by (auto simp add: mult_vec_mat_def)

lemma dim_col_mat_list: \<open>\<forall> m \<in> set (mat_to_list M). dim_col M = length m \<close>
  unfolding mat_to_list_def dim_col_def o_def
  by simp

lemma dim_col_mat_list': \<open>mat_to_list M \<noteq> [] \<Longrightarrow> dim_col M = length (hd (mat_to_list M))\<close>
  using dim_col_mat_list by fastforce 

lemma scalar_prod_list: 
  \<open>((vec_of_list v) \<bullet> (vec_of_list w)) = (\<Sum> i \<in> {0 ..< length w}. v!i *  w!i)\<close>
  unfolding scalar_prod_def vec_of_list_def 
  by (simp, metis (no_types, lifting) dim_vec sum.cong vec.abs_eq vec_of_list.abs_eq vec_of_list_index) 

lemma dim_col_mat_of_col_list: \<open>dim_col (mat_of_cols_list n As) = length As\<close>
  unfolding mat_of_cols_list_def by simp

lemma dim_row_mat_of_col_list: \<open>dim_row (mat_of_cols_list n As) = n\<close>
  unfolding mat_of_cols_list_def by simp

lemma dim_col_mat_of_row_list: \<open>dim_col (mat_of_rows_list n As) = n\<close>
  unfolding mat_of_rows_list_def by simp

lemma dim_row_mat_of_row_list: \<open>dim_row (mat_of_rows_list n As) = length As\<close>
  unfolding mat_of_rows_list_def by simp

lemma vec_of_list_ext: \<open>vec_of_list xs = vec_of_list ys \<Longrightarrow> xs = ys\<close>
  by (metis list_vec) 

lemma list_of_vec_ext: \<open>list_of_vec xs = list_of_vec ys \<Longrightarrow> xs = ys\<close>
  by (metis vec_list) 

lemma map_if_lam:
  \<open>map (\<lambda> i. if i < n then P(i) else Q(i)) [0..<n] = map (\<lambda> i. P(i)) [0..<n]\<close>
  by simp 

lemma map_if_lam':
  \<open>map (\<lambda> i. if p \<and> i < n then (P i) else (Q i)) [0..<n] = map (\<lambda> i. if p then (P i) else (Q i)) [0..<n]\<close>
  by simp 

lemma map_if_lam'':
  \<open>map (\<lambda>i. map (\<lambda>ia. if i < n then P i ia else Q i ia) [0..<m]) [0..<n] 
  =map (\<lambda>i. map (\<lambda>ia. P i ia) [0..<m]) [0..<n]\<close>
  by simp

lemma vec_add_list: 
  assumes \<open>length v = length w\<close> 
  shows \<open>list_of_vec ((vec_of_list v) + (vec_of_list w)) = map2 (+) v w\<close>
  unfolding plus_vec_def
  apply(simp add:vec_of_list_index)      
  using assms map2_map_map [of "(+)"]  map_nth
  by metis 

lemma vec_add_list': 
  assumes \<open>length v = length w\<close> 
  shows \<open>((vec_of_list v) + (vec_of_list w)) = vec_of_list (map2 (+) v w)\<close>
  apply(rule list_of_vec_ext, simp only: list_vec)
  using vec_add_list assms by blast 

lemma mat_col_list: 
  assumes \<open>i < length As\<close> 
    and \<open>\<forall> a \<in> set As. \<forall> a' \<in> set As. length a = length a' \<and> a \<noteq> []\<close>
    and \<open>d = length (hd As)\<close> 
  shows \<open>list_of_vec ( col (mat_of_cols_list d As) i ) =  As!i\<close> 
  apply (intro nth_equalityI)
  subgoal using assms by simp 
      (metis dim_row_mat_of_col_list list.set_sel(1) list.size(3) not_less_zero nth_mem)
  subgoal for j using assms unfolding list_of_vec_index length_list_of_vec
    by (auto simp: mat_of_cols_list_def)
  done

lemma mult_vec_mat_col_list: 
  assumes \<open>length vs=n\<close>
    and \<open>\<forall> a \<in> set As. \<forall> a' \<in> set As. length a = length a' \<and> a \<noteq> []\<close>
    and \<open>length (hd As)=d\<close> 
    and \<open>length As=n\<close> 
    and \<open>As \<noteq> []\<close> 
  shows    \<open>list_of_vec ((vec_of_list vs) \<^sub>v* (mat_of_cols_list d As)) = map  (\<lambda>i. \<Sum>ia = 0..<length vs. As ! i ! ia * vs ! ia) [0..<n] \<close>
  apply (intro nth_equalityI)
  subgoal using assms by (simp add: mult_vec_mat_def mat_of_cols_list_def)
  subgoal for i using assms unfolding list_of_vec_index mult_vec_mat_def mat_of_cols_list_def
    by (auto simp: scalar_prod_def vec_of_list_index intro!: sum.cong arg_cong2[of _ _ _ _ "(*)"])
      (metis list.set_sel(1) list_of_vec_index list_of_vec_vec map_nth nth_mem)
  done

lemma mult_vec_mat_row_list: 
  assumes \<open>length vs=d\<close>
    and \<open>\<forall> a \<in> set As. \<forall> a' \<in> set As. length a = length a' \<and> a \<noteq> []\<close>
    and \<open>length (hd As)=d\<close> 
    and \<open>length As=n\<close> 
    and \<open>As \<noteq> []\<close>                                
  shows \<open>list_of_vec ((vec_of_list vs) \<^sub>v* (mat_of_rows_list d As)) = map (\<lambda>i. \<Sum>ia = 0..<length vs. map (\<lambda>ia. As ! ia ! i) [0..<length As] ! ia * vs ! ia) [0..<d]\<close>
  apply (intro nth_equalityI)
  subgoal using assms by (simp add: mult_vec_mat_def mat_of_rows_list_def)
  subgoal for i using assms unfolding list_of_vec_index mult_vec_mat_def mat_of_rows_list_def
    by (auto simp: scalar_prod_def vec_of_list_index intro!: sum.cong arg_cong2[of _ _ _ _ "(*)"])
     (metis list_of_vec_index list_of_vec_vec)
  done
  
lemma mult_vec_mat_row_list': 
  assumes \<open>length vs=d\<close>
    and \<open>\<forall> a \<in> set As. \<forall> a' \<in> set As. length a = length a' \<and> a \<noteq> []\<close>
    and \<open>length (hd As)=d\<close> 
    and \<open>length As=n\<close> 
    and \<open>As \<noteq> []\<close>                                
  shows    \<open>((vec_of_list vs) \<^sub>v* (mat_of_rows_list d As)) = vec_of_list (map (\<lambda>i. \<Sum>ia = 0..<length vs. map (\<lambda>ia. As ! ia ! i) [0..<length As] ! ia * vs ! ia) [0..<d])\<close>
  apply(rule list_of_vec_ext, simp only:list_vec)
  using assms mult_vec_mat_row_list by blast

lemma col_of_rows_list:
  assumes \<open>d = Min (set (map length As))\<close>
    and \<open>i < d\<close>
  shows   \<open>list_of_vec (col (mat_of_rows_list d As) i) = map (\<lambda> as. (as!i)) As\<close>
  apply (intro nth_equalityI)
  subgoal by (simp add: mat_of_rows_list_def)
  subgoal for j using assms unfolding list_of_vec_index
    by (auto simp: mat_of_rows_list_def)
  done

lemma col_of_rows_list':
  assumes \<open>\<forall> as \<in> set As. length as = d\<close>
    and \<open>As \<noteq> []\<close>
  shows \<open>(col (mat_of_rows_list d As) i) = vec_of_list (map (\<lambda> as. (as!i)) As)\<close>
proof (cases "i < d")
  case True
  then show ?thesis 
    apply (subst list_of_vec_ext) 
    by (auto simp add: vec_list vec_of_list_ext assms col_of_rows_list)
next
  case False
  then show ?thesis
  proof -
    have "list_of_vec (col (mat_of_rows_list d As) i) = 
          list_of_vec (vec_of_list (map (\<lambda>as. as ! i) As))"
    proof (rule nth_equalityI)
      show "length (list_of_vec (col (mat_of_rows_list d As) i)) = 
            length (list_of_vec (vec_of_list (map (\<lambda>as. as ! i) As)))"
        by (simp add: mat_of_rows_list_def)
    next
      fix j
      assume j_bound: "j < length (list_of_vec (col (mat_of_rows_list d As) i))"
      then have j_lt: "j < length As"
        by (simp add: mat_of_rows_list_def)
       have lhs: "list_of_vec (col (mat_of_rows_list d As) i) ! j = 
                 mat (length As) d (\<lambda>(r, c). As ! r ! c) $$ (j, i)"
        unfolding list_of_vec_index mat_of_rows_list_def col_def
        using j_lt by simp
      have rhs: "list_of_vec (vec_of_list (map (\<lambda>as. as ! i) As)) ! j = 
                 (map (\<lambda>as. as ! i) As) ! j"
        unfolding list_of_vec_index
        using j_lt  vec_of_list_index by blast 
      have "(map (\<lambda>as. as ! i) As) ! j = As ! j ! i"
        using j_lt by simp
      moreover have "mat (length As) d (\<lambda>(r, c). As ! r ! c) $$ (j, i) = As ! j ! i"
        using j_lt False 
        apply (simp add: mat_def assms index_mat_def)
        apply (subst Abs_mat_inverse)
        apply blast
        apply(simp add: mk_mat_def undef_mat_def)
      using  assms(1) map_nth nth_mem  
      by metis
      ultimately show "list_of_vec (col (mat_of_rows_list d As) i) ! j = 
                       list_of_vec (vec_of_list (map (\<lambda>as. as ! i) As)) ! j"
        using lhs rhs by simp
    qed
    then show ?thesis
      by (rule list_of_vec_ext)
  qed
qed

lemma list_mat: \<open>mat_of_rows_list (dim_col A) (mat_to_list A) = A\<close>
  unfolding mat_to_list_def mat_of_rows_list_def
  by(auto)

lemma list_mat_transpose_transpose: \<open>(mat_of_rows_list (dim_col x\<^sup>T) (mat_to_list x\<^sup>T))\<^sup>T = x\<close>
  using transpose_transpose[of "x", symmetric] list_mat by metis 

lemma mat_list:
  \<open>\<forall> r \<in> set(rs). length r = dimc \<Longrightarrow>mat_to_list (mat_of_rows_list dimc rs) = rs\<close>
  unfolding mat_of_rows_list_def mat_to_list_def
  by (intro nth_equalityI, auto)

lemma dim_row_list:  \<open>dim_row m = length (mat_to_list m)\<close>
  by (metis dim_row_mat_of_row_list list_mat) 

lemma dim_col_list: \<open>\<forall> c \<in> set (mat_to_list m). length c = dim_col m\<close>
  by (simp add: mat_to_list_def) 

lemma scalar_prod_sum_list_lv_eq: 
  assumes same_dim: \<open>dim_vec (x::'a::comm_ring Matrix.vec) = dim_vec y\<close> 
  shows \<open>x \<bullet> y \<equiv> sum_list (map2 (*) (list_of_vec x) (list_of_vec y))\<close>
proof(unfold scalar_prod_def, insert assms,induction "dim_vec x" )
  case 0
  then show ?case by simp
next
  case (Suc xa) note * = this 
  then show ?case 
    apply(simp add:list_of_vec_map sum_def)
    by (simp add: comm_monoid_add_class.sum_def interv_sum_list_conv_sum_set_nat map2_map_map) 
qed

lemma scalar_prod_sum_list_vl_eq:
  assumes same_dim: \<open>length (x::'a::comm_ring list) = length y\<close> 
  shows \<open>(vec_of_list x) \<bullet> (vec_of_list y) \<equiv> sum_list (map2 (*) x y)\<close>
proof(unfold scalar_prod_def, insert assms,induction "length x" )
  case 0
  then show ?case by simp
next
  case (Suc xa) note * = this 
  then show ?case 
    apply(simp add:list_of_vec_map sum_def)
    using comm_monoid_add_class.sum_def interv_sum_list_conv_sum_set_nat 
    by (metis (mono_tags, lifting) atLeastLessThan_upt map2_to_map_idx_eq map_eq_conv vec_of_list_index)
qed


end
