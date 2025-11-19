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

subsection\<open>Useful Definitions for Analysing Matrix Predictions (\thy)\<close>

theory
  Prediction_Utils_Matrix 
  imports 
    Complex_Main
    Jordan_Normal_Form.Matrix
begin


definition max\<^sub>m\<^sub>a\<^sub>t :: \<open>'a::linorder Matrix.mat \<Rightarrow> 'a\<close> where 
  \<open>max\<^sub>m\<^sub>a\<^sub>t =  Max o elements_mat\<close>

definition min\<^sub>m\<^sub>a\<^sub>t :: \<open>'a::linorder Matrix.mat \<Rightarrow> 'a\<close> where 
  \<open>min\<^sub>m\<^sub>a\<^sub>t  =  Min o elements_mat\<close>


lemma finite_elements_mat: "finite (elements_mat A)"
  unfolding elements_mat_def by blast

lemma max\<^sub>m\<^sub>a\<^sub>t_is_element:
  shows \<open>elements_mat m \<noteq> {} \<Longrightarrow> max\<^sub>m\<^sub>a\<^sub>t m \<in> elements_mat m\<close>
  by (simp add: finite_elements_mat max\<^sub>m\<^sub>a\<^sub>t_def)

lemma min\<^sub>m\<^sub>a\<^sub>t_is_element:
  \<open>elements_mat m \<noteq> {} \<Longrightarrow> min\<^sub>m\<^sub>a\<^sub>t m \<in> elements_mat m\<close>
  by (simp add: finite_elements_mat min\<^sub>m\<^sub>a\<^sub>t_def)

definition max_list :: "'a::linorder list \<Rightarrow> 'a" where
  "max_list xs = fold max xs (hd xs)"

definition min_list :: "'a::linorder list \<Rightarrow> 'a" where
  "min_list xs = fold min xs (hd xs)"

definition max\<^sub>v\<^sub>e\<^sub>c :: \<open>'a::linorder Matrix.vec \<Rightarrow> 'a\<close> where 
  \<open>max\<^sub>v\<^sub>e\<^sub>c =  max_list  o list_of_vec\<close>

definition min\<^sub>v\<^sub>e\<^sub>c :: \<open>'a::linorder Matrix.vec \<Rightarrow> 'a\<close> where 
  \<open>min\<^sub>v\<^sub>e\<^sub>c  =  min_list o list_of_vec\<close>

lemma max\<^sub>v\<^sub>e\<^sub>c_is_element:
  shows \<open>list_of_vec m \<noteq> [] \<Longrightarrow> max\<^sub>v\<^sub>e\<^sub>c m \<in> set(list_of_vec m)\<close>
  apply (simp add: max\<^sub>v\<^sub>e\<^sub>c_def max_list_def) 
  by (metis List.finite_set Max.set_eq_fold Max_eq_iff hd_in_set list.discI set_ConsD set_empty2)

lemma min\<^sub>v\<^sub>e\<^sub>c_is_element:
  shows \<open>list_of_vec m \<noteq> [] \<Longrightarrow> min\<^sub>v\<^sub>e\<^sub>c m \<in> set(list_of_vec m)\<close>
  apply (simp add: min\<^sub>v\<^sub>e\<^sub>c_def min_list_def) 
  by (metis List.finite_set Min.set_eq_fold Min_in empty_iff insert_absorb list.set_sel(1) list.simps(15))


lemma max\<^sub>v\<^sub>e\<^sub>c_vCons_append_eq: \<open>max\<^sub>v\<^sub>e\<^sub>c (vCons x xs) = max\<^sub>v\<^sub>e\<^sub>c xs \<or> max\<^sub>v\<^sub>e\<^sub>c (vCons x xs) = x\<close>
proof(cases "max\<^sub>v\<^sub>e\<^sub>c (vCons x xs) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis apply(simp add: max\<^sub>v\<^sub>e\<^sub>c_def max_list_def Max_eq_iff insertCI insertE ) 
    by (smt (verit) List.finite_set Max.in_idem Max.set_eq_fold Max_insert comp_apply 
        fold_simps(1) list.simps(15) list.simps(3) list_of_vec_vCons max.right_idem max\<^sub>v\<^sub>e\<^sub>c_def
        max\<^sub>v\<^sub>e\<^sub>c_is_element max_list_def set_ConsD set_empty2) (*takes long*)

qed

lemma max\<^sub>v\<^sub>e\<^sub>c_append_eq: \<open>max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x])) = max\<^sub>v\<^sub>e\<^sub>c (vec_of_list xs) \<or> max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x])) = x\<close>
proof(cases "max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x])) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis 
    apply(simp add: max\<^sub>v\<^sub>e\<^sub>c_def max\<^sub>v\<^sub>e\<^sub>c_is_element max_list_def) 
    by (metis (no_types, lifting) append_self_conv2 comp_apply fold.simps(1) 
        fold_append fold_simps(2) hd_append2 id_apply list.sel(1) list_vec max_def)
qed

lemma min\<^sub>v\<^sub>e\<^sub>c_vCons_append_eq: \<open>min\<^sub>v\<^sub>e\<^sub>c (vCons x xs) = min\<^sub>v\<^sub>e\<^sub>c xs \<or> min\<^sub>v\<^sub>e\<^sub>c (vCons x xs) = x\<close>
proof(cases "min\<^sub>v\<^sub>e\<^sub>c (vCons x xs) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis 
    apply(simp add: min\<^sub>v\<^sub>e\<^sub>c_def min_list_def Min_eq_iff insertCI insertE ) 
    by (metis (no_types, lifting) List.finite_set Min.in_idem Min.insert 
        Min.semilattice_set_axioms Min_def fold_simps(1) list.set_sel(1) list.simps(15) 
        min_def semilattice_set.set_eq_fold set_empty)
qed

lemma min\<^sub>v\<^sub>e\<^sub>c_append_eq: \<open>min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x])) = min\<^sub>v\<^sub>e\<^sub>c (vec_of_list xs) \<or> min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x])) = x\<close>
proof(cases "min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x])) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
    apply(simp add: min\<^sub>v\<^sub>e\<^sub>c_def min\<^sub>v\<^sub>e\<^sub>c_is_element min_list_def)
    by (metis (no_types, lifting) append_self_conv2 comp_apply fold.simps(1) 
        fold_append fold_simps(2) hd_append2 id_apply list.sel(1) list_vec min_def)
qed

lemma max\<^sub>v\<^sub>e\<^sub>c_vec_cons_eq: \<open>max\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs) = max\<^sub>v\<^sub>e\<^sub>c xs \<or> max\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs) = x\<close>
proof(cases "max\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
    apply(simp add: max\<^sub>v\<^sub>e\<^sub>c_def max_list_def)
    using  max_def 
    by (metis (no_types, lifting) comp_apply fold_simps(2) list.sel(1) 
        list_of_vec_vCons max\<^sub>v\<^sub>e\<^sub>c_def max\<^sub>v\<^sub>e\<^sub>c_vCons_append_eq max_list_def)
qed

lemma max\<^sub>v\<^sub>e\<^sub>c_cons_eq: \<open>max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs)) = max\<^sub>v\<^sub>e\<^sub>c (vec_of_list xs) \<or> max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs)) = x\<close>
proof(cases "max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs)) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
    apply(simp add: max\<^sub>v\<^sub>e\<^sub>c_def max\<^sub>v\<^sub>e\<^sub>c_is_element max_list_def) 
    by (metis (no_types, lifting) comp_apply fold_simps(2) list.sel(1) 
        list_of_vec_vCons max.idem max\<^sub>v\<^sub>e\<^sub>c_def max\<^sub>v\<^sub>e\<^sub>c_vCons_append_eq max_list_def)
qed

lemma min\<^sub>v\<^sub>e\<^sub>c_vec_cons_eq: \<open>min\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs) = min\<^sub>v\<^sub>e\<^sub>c xs \<or> min\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs) = x\<close>
proof(cases "min\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
    apply(simp add: max\<^sub>v\<^sub>e\<^sub>c_def) 
    using min\<^sub>v\<^sub>e\<^sub>c_vCons_append_eq by blast
qed

lemma min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_cons_eq: \<open>min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs)) = min\<^sub>v\<^sub>e\<^sub>c (vec_of_list xs) \<or> min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs)) = x\<close>
proof(cases "min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs)) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
    apply (simp add: min\<^sub>v\<^sub>e\<^sub>c_def min\<^sub>v\<^sub>e\<^sub>c_is_element min_list_def)
    by (metis (no_types, lifting) comp_apply fold_simps(2) list.sel(1) 
        list_of_vec_vCons min.idem min\<^sub>v\<^sub>e\<^sub>c_def min\<^sub>v\<^sub>e\<^sub>c_vCons_append_eq min_list_def)
qed

lemma max\<^sub>v\<^sub>e\<^sub>c_vec_append_limit: assumes \<open>xs \<noteq> vNil\<close> shows \<open>max\<^sub>v\<^sub>e\<^sub>c xs \<le> max\<^sub>v\<^sub>e\<^sub>c (vCons x xs)\<close>
proof(cases "max\<^sub>v\<^sub>e\<^sub>c (vCons x xs) = x")
  case True 
  then show ?thesis using assms 
    apply (simp add: max\<^sub>v\<^sub>e\<^sub>c_def max_list_def) 
    by (metis List.finite_set Max.set_eq_fold Max_insert hd_in_set insert_absorb 
        list.simps(15) max.orderI set_empty2 vec_list vec_of_list_Nil)
next
  case False
  then show ?thesis
    using dual_order.order_iff_strict max\<^sub>v\<^sub>e\<^sub>c_vCons_append_eq by auto
qed 

lemma max\<^sub>v\<^sub>e\<^sub>c_append_limit: assumes \<open>xs \<noteq> []\<close> shows \<open>max\<^sub>v\<^sub>e\<^sub>c (vec_of_list xs) \<le> max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x]))\<close>
proof(cases "max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x])) = x")
  case True 
  then show ?thesis using assms
    apply (simp add: max\<^sub>v\<^sub>e\<^sub>c_def  max\<^sub>v\<^sub>e\<^sub>c_is_element max_list_def )
    by (metis List.finite_set Max.set_eq_fold Max_ge comp_apply list.set_intros(2) 
        list_vec max\<^sub>v\<^sub>e\<^sub>c_def max\<^sub>v\<^sub>e\<^sub>c_is_element max_list_def rotate1.simps(2) set_rotate1)
next
  case False
  then show ?thesis 
    by (metis dual_order.refl max\<^sub>v\<^sub>e\<^sub>c_append_eq)
qed 

lemma min\<^sub>v\<^sub>e\<^sub>c_vec_append_limit: assumes \<open>xs \<noteq> vNil\<close> shows \<open>min\<^sub>v\<^sub>e\<^sub>c xs \<ge> min\<^sub>v\<^sub>e\<^sub>c (vCons x xs)\<close>
proof(cases " min\<^sub>v\<^sub>e\<^sub>c (vCons x xs) = x")
  case True 
  then show ?thesis using assms 
    apply (simp add: min\<^sub>v\<^sub>e\<^sub>c_def min_list_def)
    by (metis List.finite_set Min.insert Min.set_eq_fold 
        Orderings.order_eq_iff hd_in_set insert_absorb list.simps(15) 
        min_def set_empty2 vec_list vec_of_list_Nil)
next
  case False
  then show ?thesis 
    by (metis dual_order.refl min\<^sub>v\<^sub>e\<^sub>c_vCons_append_eq)
qed 

lemma min\<^sub>v\<^sub>e\<^sub>c_append_limit: assumes \<open>xs \<noteq> []\<close> shows \<open>min\<^sub>v\<^sub>e\<^sub>c (vec_of_list xs) \<ge>  min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x]))\<close>
proof(cases "min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (xs @ [x])) = x")
  case True 
  then show ?thesis using assms
    apply (simp add: min\<^sub>v\<^sub>e\<^sub>c_def  min\<^sub>v\<^sub>e\<^sub>c_is_element min_list_def )
    by (metis (no_types, lifting) append.right_neutral comp_apply 
        fold_append fold_simps(2) hd_append2 linorder_linear list_vec min_def)
next
  case False
  then show ?thesis
    by (metis dual_order.refl min\<^sub>v\<^sub>e\<^sub>c_append_eq)
qed 

lemma max\<^sub>v\<^sub>e\<^sub>c_vec_cons_limit: assumes \<open>xs \<noteq> vNil\<close> shows \<open>max\<^sub>v\<^sub>e\<^sub>c xs \<le> max\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs)\<close>
proof(cases "max\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs) = x")
  case True 
  then show ?thesis using assms
    by (metis append_vec_vCons append_vec_vNil max\<^sub>v\<^sub>e\<^sub>c_vec_append_limit vec_of_list_Cons 
        vec_of_list_Nil)
next
  case False
  then show ?thesis
    by (simp add: assms max\<^sub>v\<^sub>e\<^sub>c_vec_append_limit)
qed 

lemma max\<^sub>v\<^sub>e\<^sub>c_cons_limit: assumes \<open>xs \<noteq> []\<close> shows \<open>max\<^sub>v\<^sub>e\<^sub>c (vec_of_list xs) \<le> max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs))\<close>
proof(cases "max\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs)) = x")
  case True 
  then show ?thesis using assms
    by (metis list_vec max\<^sub>v\<^sub>e\<^sub>c_vec_append_limit vec_of_list_Cons vec_of_list_Nil)
next
  case False
  then show ?thesis
    by (metis dual_order.refl max\<^sub>v\<^sub>e\<^sub>c_cons_eq) 
qed 

lemma min\<^sub>v\<^sub>e\<^sub>c_vec_cons_limit: assumes \<open>xs \<noteq> vNil\<close> shows \<open>min\<^sub>v\<^sub>e\<^sub>c xs \<ge> min\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs)\<close>
proof(cases "min\<^sub>v\<^sub>e\<^sub>c ((vec_of_list [x]) @\<^sub>v xs) = x")
  case True 
  then show ?thesis using assms
    by (metis append_vec_vCons append_vec_vNil min\<^sub>v\<^sub>e\<^sub>c_vec_append_limit vec_of_list_Cons 
        vec_of_list_Nil)
next
  case False
  then show ?thesis
    by (simp add: assms min\<^sub>v\<^sub>e\<^sub>c_vec_append_limit)
qed 

lemma min\<^sub>v\<^sub>e\<^sub>c_cons_limit: assumes \<open>xs \<noteq> []\<close> shows \<open>min\<^sub>v\<^sub>e\<^sub>c (vec_of_list xs) \<ge>  min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs))\<close>
proof(cases "min\<^sub>v\<^sub>e\<^sub>c (vec_of_list (x#xs)) = x")
  case True 
  then show ?thesis using assms
    by (metis list_vec min\<^sub>v\<^sub>e\<^sub>c_vec_append_limit vec_of_list_Cons vec_of_list_Nil)
next
  case False
  then show ?thesis 
    by (metis min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_cons_eq order_refl) 
qed

paragraph\<open>Converting Predictions to Percentages\<close>

definition prediction2percentage :: \<open>real Matrix.vec \<Rightarrow> real Matrix.vec\<close> where
  \<open>prediction2percentage m = (let m' = max\<^sub>v\<^sub>e\<^sub>c m in map_vec (\<lambda> e. e / m' *  100.0) m)\<close>


lemma prediction2percentage_id: 
  assumes \<open>max\<^sub>v\<^sub>e\<^sub>c p = 100\<close> 
  shows \<open>prediction2percentage p = p\<close>
  using assms unfolding prediction2percentage_def
  by auto


paragraph\<open>Maximum Prediction\<close>

definition posmax_of :: \<open>'a::linorder Matrix.vec \<Rightarrow> (nat \<times> 'a) option\<close> where
  \<open>posmax_of l = (let m = max\<^sub>v\<^sub>e\<^sub>c l in find (\<lambda> e. snd e = m) (enumerate 0 (list_of_vec l)))\<close>
definition pos_of_max :: \<open>'a::linorder Matrix.vec \<Rightarrow> nat option\<close> where
  \<open>pos_of_max l = map_option fst (posmax_of l)\<close>

definition posmax_of' :: \<open>'a::linorder Matrix.vec \<Rightarrow> (nat \<times> 'a) option\<close> where
  \<open>posmax_of' l = (let l' = list_of_vec l in 
                          (if l' = [] then None
                                      else Some ((hd o rev o (sort_key snd) o (enumerate 0)) l')))\<close>
definition pos_of_max' :: \<open>'a::linorder Matrix.vec \<Rightarrow> nat option\<close> where
  \<open>pos_of_max' l = map_option fst (posmax_of' l)\<close>

lemma find_append_eq: \<open>find P (xs@[x]) = (if find P xs = None then find P [x] else find P xs)\<close>
proof (induction xs)
  case Nil
  then show ?case by simp 
next
  case (Cons a xs)
  then show ?case by simp 
qed

paragraph\<open>Distance of Maximum Prediction to Next Highest Prediction\<close>

definition \<delta>\<^sub>m\<^sub>i\<^sub>n :: "real mat \<Rightarrow> real" where 
  \<open>\<delta>\<^sub>m\<^sub>i\<^sub>n m = (let m'  = max\<^sub>m\<^sub>a\<^sub>t m; m'' = Max (elements_mat m - {m'})
                    in \<bar>m' - m''\<bar> )\<close>

end