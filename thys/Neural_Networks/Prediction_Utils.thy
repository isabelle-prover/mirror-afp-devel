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

section\<open>Useful Definitions for Analyzing Predictions\<close>

theory
  Prediction_Utils 
imports 
  Complex_Main
begin 


paragraph\<open>Utilities\<close>

definition max\<^sub>l\<^sub>i\<^sub>s\<^sub>t :: \<open>'a::linorder list \<Rightarrow> 'a\<close> where 
          \<open>max\<^sub>l\<^sub>i\<^sub>s\<^sub>t = Max o set\<close>

definition min\<^sub>l\<^sub>i\<^sub>s\<^sub>t :: \<open>'a::linorder list \<Rightarrow> 'a\<close> where 
          \<open>min\<^sub>l\<^sub>i\<^sub>s\<^sub>t = Min o set\<close>

lemma max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element: \<open>l \<noteq> [] \<Longrightarrow>  max\<^sub>l\<^sub>i\<^sub>s\<^sub>t l \<in> set l \<close> 
  by (metis List.finite_set comp_eq_dest_lhs eq_Max_iff max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def set_empty) 
lemma min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element: \<open>l \<noteq> [] \<Longrightarrow>  min\<^sub>l\<^sub>i\<^sub>s\<^sub>t l \<in> set l \<close> 
  by (metis List.finite_set comp_eq_dest_lhs eq_Min_iff min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def set_empty) 

lemma max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_eq: \<open>max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x]) = max\<^sub>l\<^sub>i\<^sub>s\<^sub>t xs \<or> max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x]) = x\<close>
proof(cases "max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x]) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
    by (metis (no_types, lifting) List.finite_set Max.subset_imp Max_eq_iff comp_def insertE 
               list.discI list.set(1) list.simps(15) max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element order_antisym 
               rotate1.simps(2) set_rotate1 set_subset_Cons singletonD)
qed
lemma min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_eq: \<open>min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x]) = min\<^sub>l\<^sub>i\<^sub>s\<^sub>t xs \<or> min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x]) = x\<close>
proof(cases "min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x]) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
    by (metis (no_types, lifting) List.finite_set Min.subset_imp Min_eq_iff comp_def insertE 
               list.discI list.set(1) list.simps(15) min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element order_antisym 
               rotate1.simps(2) set_rotate1 set_subset_Cons singletonD)
qed

lemma max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_cons_eq: \<open>max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs) = max\<^sub>l\<^sub>i\<^sub>s\<^sub>t xs \<or> max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs) = x\<close>
proof(cases "max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
    by (metis (no_types, lifting) List.finite_set Max.subset_imp Max_eq_iff comp_def insertE 
               list.discI list.set(1) list.simps(15) max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element order_antisym 
               set_subset_Cons singletonD)
qed
lemma min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_cons_eq: \<open>min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs) = min\<^sub>l\<^sub>i\<^sub>s\<^sub>t xs \<or> min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs) = x\<close>
proof(cases "min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs) = x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis
    by (metis (no_types, lifting) List.finite_set Min.subset_imp Min_eq_iff comp_def insertE 
               list.discI list.set(1) list.simps(15) min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element order_antisym 
               set_subset_Cons singletonD)
qed

lemma max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_limit: assumes \<open>xs \<noteq> []\<close> shows \<open>max\<^sub>l\<^sub>i\<^sub>s\<^sub>t xs \<le> max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x])\<close>
proof(cases "max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x]) = x")
  case True 
  then show ?thesis using assms
    by (metis List.finite_set Max_ge comp_eq_dest_lhs list.set_intros(2) max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def 
              max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element rotate1.simps(2) set_rotate1)
next
  case False
  then show ?thesis 
    by (metis dual_order.refl max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_eq)
qed 
lemma min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_limit: assumes \<open>xs \<noteq> []\<close> shows \<open>min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x]) \<le> min\<^sub>l\<^sub>i\<^sub>s\<^sub>t xs\<close>
proof(cases "min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (xs @ [x]) = x")
  case True 
  then show ?thesis using assms
    by (metis List.finite_set Min_antimono comp_eq_dest_lhs min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def rotate1.simps(2) set_empty 
             set_rotate1 set_subset_Cons)
next
  case False
  then show ?thesis 
    by (metis dual_order.refl min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_eq)
qed 

lemma max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_cons_limit: assumes \<open>xs \<noteq> []\<close> shows \<open>max\<^sub>l\<^sub>i\<^sub>s\<^sub>t xs \<le> max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs)\<close>
proof(cases "max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs) = x")
  case True 
  then show ?thesis using assms
    by (metis List.finite_set Max_ge comp_eq_dest_lhs list.set_intros(2) max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def 
              max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element)
next
  case False
  then show ?thesis
    by (metis dual_order.refl max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_cons_eq) 
qed 
lemma min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_cons_limit: assumes \<open>xs \<noteq> []\<close> shows \<open>min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs) \<le> min\<^sub>l\<^sub>i\<^sub>s\<^sub>t xs\<close>
proof(cases "min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (x#xs) = x")
  case True 
  then show ?thesis using assms
    by (metis comp_eq_dest_lhs min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_limit min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def rotate1.simps(2) set_rotate1)
next
  case False
  then show ?thesis
    by (metis dual_order.refl min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_cons_eq) 
qed 


paragraph\<open>Converting Predictions to Percentages\<close>

definition prediction2percentage :: \<open>real list \<Rightarrow> real list\<close> where
          \<open>prediction2percentage l = (let m = max\<^sub>l\<^sub>i\<^sub>s\<^sub>t l in map (\<lambda> e. e / m *  100.0) l)\<close>

lemma prediction2percentage_is_percentage:
  assumes \<open>0 < max\<^sub>l\<^sub>i\<^sub>s\<^sub>t l\<close> 
  shows \<open>\<forall> x \<in> set (prediction2percentage l). x \<le> 100.0\<close>
proof(insert assms, induction "l" rule: rev_induct)
  case Nil
  then show ?case 
    unfolding prediction2percentage_def Let_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def o_def 
    by(simp)
next
  case (snoc x xs)
  then show ?case 
    unfolding prediction2percentage_def Let_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def o_def 
    by(simp add: divide_le_eq) 
qed
  
lemma prediction2percentage_id: assumes \<open>max\<^sub>l\<^sub>i\<^sub>s\<^sub>t p = 100\<close> shows \<open>prediction2percentage p = p\<close>
  unfolding prediction2percentage_def 
  using assms by(simp)

lemma prediction2percentage_min_id: 
  assumes \<open>0 < max\<^sub>l\<^sub>i\<^sub>s\<^sub>t p\<close> 
  shows \<open>(0 \<le> min\<^sub>l\<^sub>i\<^sub>s\<^sub>t (prediction2percentage p))= (0 \<le> min\<^sub>l\<^sub>i\<^sub>s\<^sub>t p)\<close>
proof(insert assms, induction "p" rule: rev_induct)
  case Nil
  then show ?case
  using assms unfolding prediction2percentage_def Let_def min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def o_def 
  by(simp)
next
  case (snoc x xs)
  then show ?case 
  using assms unfolding prediction2percentage_def Let_def min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def o_def 
    apply(simp,safe) 
    subgoal 
      by (metis linorder_not_le not_numeral_le_zero zero_le_divide_iff zero_le_mult_iff)
    subgoal
      by (metis linorder_not_le not_numeral_le_zero zero_le_divide_iff zero_le_mult_iff)
    subgoal by simp
    subgoal by simp 
    done
qed

paragraph\<open>Maximum Prediction\<close>

definition posmax_of :: \<open>'a::linorder list \<Rightarrow> (nat \<times> 'a) option\<close> where
          \<open>posmax_of l = (let m = max\<^sub>l\<^sub>i\<^sub>s\<^sub>t l in find (\<lambda> e. snd e = m) (enumerate 0 l))\<close>
definition pos_of_max :: \<open>'a::linorder list \<Rightarrow> nat option\<close> where
          \<open>pos_of_max l = map_option fst (posmax_of l)\<close>

definition posmax_of' :: \<open>'a::linorder list \<Rightarrow> (nat \<times> 'a) option\<close> where
          \<open>posmax_of' l = (if l = [] then None else Some ((hd o rev o (sort_key snd) o (enumerate 0)) l))\<close>
definition pos_of_max' :: \<open>'a::linorder list \<Rightarrow> nat option\<close> where
          \<open>pos_of_max' l = map_option fst (posmax_of' l)\<close>

paragraph\<open>Minimum Prediction\<close>

definition posmin_of :: \<open>'a::linorder list \<Rightarrow> (nat \<times> 'a) option\<close> where
          \<open>posmin_of l = (let m = min\<^sub>l\<^sub>i\<^sub>s\<^sub>t l in find (\<lambda> e. snd e = m) (enumerate 0 l))\<close>
definition pos_of_min :: \<open>'a::linorder list \<Rightarrow> nat option\<close> where
          \<open>pos_of_min l = map_option fst (posmin_of l)\<close>

definition posmin_of' :: \<open>'a::linorder list \<Rightarrow> (nat \<times> 'a) option\<close> where
          \<open>posmin_of' l = (if l = [] then None else Some ((hd o rev o (sort_key snd) o (enumerate 0)) l))\<close>
definition pos_of_min' :: \<open>'a::linorder list \<Rightarrow> nat option\<close> where
          \<open>pos_of_min' l = map_option fst (posmin_of' l)\<close>

lemma find_append_eq: \<open>find P (xs@[x]) = (if find P xs = None then find P [x] else find P xs)\<close>
proof (induction xs)
  case Nil
  then show ?case by simp 
next
  case (Cons a xs)
  then show ?case by simp 
qed

lemma posmax_of_split: \<open>posmax_of (xs @ [x]) = posmax_of (xs) \<or> posmax_of (xs @ [x]) = Some (length xs,x)\<close> 
proof(cases "posmax_of (xs @ [x]) = Some (length xs,x)")
  case True
  then show ?thesis by simp 
next
  case False note * = this
  then show ?thesis 
    apply(simp)
    unfolding posmax_of_def Let_def o_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def
    apply clarsimp
    apply (simp add: * max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_eq enumerate_append_eq find_append_eq)
    apply(cases "xs=[]", simp) 
    apply (cases " find (\<lambda>e. snd e = Max (insert x (set xs))) (enumerate 0 xs)" , simp_all)
    subgoal by (metis max_def)
    subgoal using  comp_def list.simps(15) max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_eq max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def rotate1.simps(2) set_rotate1 
      by (smt (verit) List.finite_set Max.in_idem enumerate_eq_zip find_None_iff find_cong in_set_conv_nth in_set_zip max_def
          option.discI) 
    done
qed

lemma posmin_of_split: \<open>posmin_of (xs @ [x]) = posmin_of (xs) \<or> posmin_of (xs @ [x]) = Some (length xs,x)\<close> 
proof(cases "posmin_of (xs @ [x]) = Some (length xs,x)")
  case True
  then show ?thesis by simp 
next
  case False note * = this
  then show ?thesis 
  apply(simp)
    unfolding posmin_of_def Let_def o_def min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def
    apply (simp add: *  min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_eq enumerate_append_eq find_append_eq)
    apply (cases "xs = []")
     apply simp
    apply (cases " find (\<lambda>e. snd e = Min (insert x (set xs))) (enumerate 0 xs)", simp_all )
    subgoal
      by (metis linorder_not_le min.absorb4 min.orderE) 
    subgoal using 
       List.finite_set Min.insert Min.insert_remove Min.remove  enumerate_eq_zip
          find_None_iff find_cong in_set_conv_nth in_set_zip length_append length_map 
          list.size(3) map_nth min.orderE min_def option.simps(3) set_append set_empty 
      by (smt (verit) insort_insert_triv set_insort_insert)  
    done 
qed

lemma pos_of_max_split: 
  \<open>pos_of_max (xs @ [x]) = pos_of_max (xs) \<or> pos_of_max (xs @ [x]) = Some (length xs)\<close>
  using  pos_of_max_def posmax_of_split
  by (metis fst_eqD option.simps(9))

lemma pos_of_min_split: 
  \<open>pos_of_min (xs @ [x]) = pos_of_min (xs) \<or> pos_of_min (xs @ [x]) = Some (length xs)\<close>
  using  pos_of_min_def posmin_of_split
  by (metis fst_eqD option.simps(9))

lemma posmax_of_none: \<open>(posmax_of xs = None) = (xs = []) \<close>
proof(induction "xs" rule:List.rev_induct)
  case Nil
  then show ?case 
    by (simp add: posmax_of_def)
next
  case (snoc x xs) note * = this
  then show ?case 
    unfolding posmax_of_def Let_def
    apply(clarsimp simp add:enumerate_append_eq find_append_eq)
    subgoal using  max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_eq
      by (metis append_is_Nil_conv in_set_conv_decomp_last list.discI max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element 
          not_Some_eq old.prod.exhaust self_append_conv2 set_ConsD)
    done
qed

lemma posmin_of_none: \<open>(posmin_of xs = None) = (xs = []) \<close>
proof(induction "xs" rule:List.rev_induct)
  case Nil
  then show ?case 
    by (simp add: posmin_of_def)
next
  case (snoc x xs) note * = this
  then show ?case 
    unfolding posmin_of_def Let_def
    apply(clarsimp simp add:enumerate_append_eq find_append_eq)[1]
    using min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_append_eq
    by (metis append_Nil eq_snd_iff in_set_conv_nth list.distinct(1) list.size(3) min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element 
        not_less_zero option.exhaust set_ConsD)
qed

lemma posmax_of_in_snd: \<open>(posmax_of xs) = Some p \<Longrightarrow> snd p \<in> set xs\<close>
  by (metis (mono_tags, lifting) List.finite_set comp_def eq_Max_iff find_Some_iff max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def 
                                 option.discI posmax_of_def posmax_of_none set_empty) 

lemma posmin_of_in_snd: \<open>(posmin_of xs) = Some p \<Longrightarrow> snd p \<in> set xs\<close>
  by (metis (mono_tags, lifting) find_Some_iff min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_is_element option.discI 
                                 posmin_of_def posmin_of_none)

lemma pos_of_max_none: \<open>(pos_of_max xs = None) = (xs = []) \<close>
  by(simp add:pos_of_max_def posmax_of_none)

lemma pos_of_min_none: \<open>(pos_of_min xs = None) = (xs = []) \<close>
  by(simp add:pos_of_min_def posmin_of_none)

lemma take_nth_drop_eq:
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
shows \<open>xs = ((take n xs)@[xs!n]@(drop (n+1) xs))\<close>
  by (simp add: Cons_nth_drop_Suc assms(2))

lemma max_in: 
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). xs!n > x\<close>
shows \<open>Max (set ((take n xs)@[xs!n]@(drop (n+1) xs))) = ((take n xs)@[xs!n]@(drop (n+1) xs))!n\<close>
  using assms 
  apply(simp)
  by (metis List.finite_set Max_insert2 id_take_nth_drop order_le_less set_append) 

lemma min_in: 
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). xs!n < x\<close>
shows \<open>Min (set ((take n xs)@[xs!n]@(drop (n+1) xs))) = ((take n xs)@[xs!n]@(drop (n+1) xs))!n\<close>
  using assms 
  apply(simp)
  by (metis List.finite_set Min_insert2 id_take_nth_drop nless_le set_append)

lemma max_in':
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). xs!n > x\<close>
shows \<open>Max (set xs) = xs!n\<close>
  using assms max_in take_nth_drop_eq by metis

lemma min_in':
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). xs!n < x\<close>
shows \<open>Min (set xs) = xs!n\<close>
  using assms min_in take_nth_drop_eq by metis

lemma snd_numerate_eq: 
  "xs \<noteq> [] \<Longrightarrow> n < length xs  \<Longrightarrow>  j < n \<Longrightarrow> snd (List.enumerate 0 xs ! j) = xs!j"
  by (simp add: nth_enumerate_eq) 

lemma nth_lower_max: 
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). x < xs!n\<close>
shows \<open>\<forall> j < n. xs!j < xs!n\<close>
proof - 
  have  x1: \<open>\<forall> x \<in> set ((take n xs)). x < xs!n\<close> using assms by simp 
  then have x2: "(\<forall> j < n . (xs!j) \<in> set ((take n xs)))" 
    using assms(2) in_set_conv_nth by fastforce
  then show ?thesis 
    using x1 assms nth_take[of _ "n" "xs"]  by simp 
qed

lemma nth_higher_min: 
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). x > xs!n\<close>
shows \<open>\<forall> j < n. xs!j > xs!n\<close>
proof - 
  have  x1: \<open>\<forall> x \<in> set ((take n xs)). x > xs!n\<close> using assms by simp 
  then have x2: "(\<forall> j < n . (xs!j) \<in> set ((take n xs)))" 
    using assms(2) in_set_conv_nth by fastforce
  then show ?thesis 
    using x1 assms nth_take[of _ "n" "xs"]  by simp 
qed

lemma posmax_of_le: 
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). x < xs!n\<close>
shows \<open>posmax_of xs = Some (n,xs!n)\<close>
unfolding posmax_of_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def o_def Let_def
  apply(simp add: List.find_Some_iff)  
  apply(rule exI[of _ "n"])
  apply(simp add: max_in' assms nth_enumerate_eq)
  apply(rule conjI)
  subgoal using assms max_in' by metis  
  subgoal
    apply(simp add: assms max_in'[of "xs" "n"])      
    apply(simp add: assms snd_numerate_eq[of "xs" "n"])  
    using assms nth_lower_max[of "xs" "n"] by auto 
  done 

lemma posmin_of_le: 
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). x > xs!n\<close>
shows \<open>posmin_of xs = Some (n,xs!n)\<close>
unfolding posmin_of_def min\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def o_def Let_def
  apply(simp add: List.find_Some_iff)  
  apply(rule exI[of _ "n"])
  apply(simp add: min_in' assms nth_enumerate_eq)
  apply(rule conjI)
  subgoal using assms min_in' by metis  
  subgoal
    apply(simp add: assms min_in'[of "xs" "n"])      
    apply(simp add: assms snd_numerate_eq[of "xs" "n"])  
    using assms nth_higher_min[of "xs" "n"] by auto 
  done 
     
lemma pos_max_le: 
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). x < xs!n\<close>
shows \<open>(pos_of_max xs = Some n)\<close>
  using posmax_of_le[of "xs" "n"] assms unfolding pos_of_max_def 
  by simp 

lemma pos_min_le: 
  assumes \<open>xs \<noteq> []\<close>
  and \<open>n < length xs\<close>
  and \<open>\<forall> x \<in> set ((take n xs)@(drop (n+1) xs)). x > xs!n\<close>
shows \<open>(pos_of_min xs = Some n)\<close>
  using posmin_of_le[of "xs" "n"] assms unfolding pos_of_min_def 
  by simp 

paragraph\<open>Distance of Maximum Prediction to Next Highest Prediction\<close>
definition \<delta>\<^sub>m\<^sub>i\<^sub>n :: "real list \<Rightarrow> real" where 
          \<open>\<delta>\<^sub>m\<^sub>i\<^sub>n l = (let m = max\<^sub>l\<^sub>i\<^sub>s\<^sub>t l in let m' = max\<^sub>l\<^sub>i\<^sub>s\<^sub>t (remove1 m l) in \<bar>m - m'\<bar>)\<close>

lemma leq_linear_real:
  assumes b_bound: \<open>(b::real) \<in> {lb..up}\<close> 
  and is_leq_at_bounds: \<open>((c\<^sub>1 * lb + c\<^sub>0 \<le> c\<^sub>1' * lb + c\<^sub>0') \<and> (c\<^sub>1 * up + c\<^sub>0 \<le> c\<^sub>1' * up + c\<^sub>0'))\<close>
shows \<open>c\<^sub>1 * b + c\<^sub>0 \<le> c\<^sub>1' * b + c\<^sub>0'\<close>
proof(cases \<open>lb \<le> up\<close>)
  case True
  then show ?thesis 
    using assms 
    by auto (smt (verit, best) Groups.mult_ac(2) left_diff_distrib mult_right_mono) 
next
  case False
  then show ?thesis using assms by(simp)
qed
  
lemma leq_linear_real':
  assumes b_bound: \<open>(b::real) \<in> {lb..up}\<close> 
  and is_leq_at_bounds: \<open>((c\<^sub>1 * up + c\<^sub>0 \<le> c\<^sub>1' * up + c\<^sub>0') \<and> (c\<^sub>1 * lb + c\<^sub>0 \<le> c\<^sub>1' * lb + c\<^sub>0'))\<close>
shows \<open>c\<^sub>1 * b + c\<^sub>0 \<le> c\<^sub>1' * b + c\<^sub>0'\<close>
proof(cases \<open>lb \<le> up\<close>)
  case True
  then show ?thesis using assms 
    using leq_linear_real by blast
next
  case False
  then show ?thesis using assms by(simp)
qed
lemma le_linear_real:
  assumes b_bound: \<open>(b::real) \<in> {lb..up}\<close> 
  and is_leq_at_bounds: \<open>((c\<^sub>1 * lb + c\<^sub>0 < c\<^sub>1' * lb + c\<^sub>0') \<and> (c\<^sub>1 * up + c\<^sub>0 < c\<^sub>1' * up + c\<^sub>0'))\<close>
shows \<open>c\<^sub>1 * b + c\<^sub>0 < c\<^sub>1' * b + c\<^sub>0'\<close>
proof(cases \<open>lb < up\<close>)
  case True
  then show ?thesis 
    using assms 
    by auto (smt (verit, best) Groups.mult_ac(2) left_diff_distrib mult_right_mono) 
next
  case False
  then show ?thesis using assms
    by (metis atLeastAtMost_iff nless_le order_le_less_trans)
qed
  
lemma le_linear_real':
  assumes b_bound: \<open>(b::real) \<in> {lb..up}\<close> 
  and is_leq_at_bounds: \<open>((c\<^sub>1 * up + c\<^sub>0 < c\<^sub>1' * up + c\<^sub>0') \<and> (c\<^sub>1 * lb + c\<^sub>0 < c\<^sub>1' * lb + c\<^sub>0'))\<close>
shows \<open>c\<^sub>1 * b + c\<^sub>0 < c\<^sub>1' * b + c\<^sub>0'\<close>
proof(cases \<open>lb \<le> up\<close>)
  case True
  then show ?thesis using assms 
    using le_linear_real by blast
next
  case False
  then show ?thesis using assms by(simp)
qed

lemma  pos_max_leq': \<open>(pos_of_max xs = Some n) \<Longrightarrow> \<forall> x \<in> set xs. x \<le> xs!n\<close>
  apply(simp add: pos_of_max_def posmax_of_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def) 
  by (smt (verit) List.finite_set Max_ge add_0 find_Some_iff fst_conv length_enumerate 
                  nth_enumerate_eq snd_conv)

end 
