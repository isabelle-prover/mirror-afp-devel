(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Runs_To_VCG_StackPointer
  imports
    HeapLift
    Refines_Spec
begin

definition "distinct_span xs \<equiv>
  distinct_prop (\<lambda>(v1, s1) (v2, s2). disjnt {v1 ..+ s1} {v2 ..+ s2}) xs"

definition "distinct_spans xs \<equiv>
  distinct_prop (\<lambda>(v1, n1, s1) (v2, n2, s2). disjnt {v1 ..+ n1 * s1} {v2 ..+ n2 * s2}) xs"

lemma distinct_span_spans_conv:
  "distinct_span xs \<longleftrightarrow> distinct_spans (map (\<lambda>(v, s). (v, 1, s)) xs)"
  unfolding distinct_span_def distinct_spans_def
  by (clarsimp simp: distinct_prop_map case_prod_beta intro!: distinct_prop_iff)
  
definition "lvp_distinct xs \<equiv>
  distinct_spans (map (\<lambda>(d, v, n, s). (v, n, s)) xs) \<and>
  distinct (map (\<lambda>(d, v, n, s). (d, v)) xs) \<and>
  sorted_wrt (\<lambda>(d1, _) (d2, _). stack_free d1 \<subseteq> stack_free d2) xs \<and>
 (\<forall>(d, v, n, s)\<in>set xs.
    disjnt {v ..+ n * s} (stack_free d) \<and> s > 0)"

lemma lvp_distinct_pairwise_disjnt:
  "\<lbrakk> lvp_distinct xs; xs ! m1 = (d1, v1, n1, s1); xs ! m2 = (d2, v2, n2, s2); m1 < m2; m2 < length xs \<rbrakk> \<Longrightarrow>
      disjnt {v1 ..+ n1 * s1} {v2 ..+ n2 * s2}"
  unfolding lvp_distinct_def
  apply (clarsimp)+
  apply (simp add: distinct_spans_def distinct_prop_map case_prod_beta)
  apply (drule(2) distinct_prop_nth)
  by auto

lemma lvp_distinct_spansD: "lvp_distinct xs \<Longrightarrow>
  distinct_spans (map (\<lambda>(d, v, n, s). (v, n, s)) xs)"
  by (simp add: lvp_distinct_def)

named_theorems stack_ptr_simps


context stack_simulation_heap_typing begin

lemmas [stack_ptr_simps] = 
  stack_ptr_acquire_def 
  stack_ptr_release_def
  write_same_ZERO
  stack_releases_stack_allocs_inverse
  root_ptr_valid_ptr_valid 

lemma runs_to_guard_with_fresh_stack_ptr[runs_to_vcg]:
  assumes f[runs_to_vcg]: "\<And>d ptr vs. 
    (ptr, d) \<in> stack_allocs n \<S> TYPE('a) (heap_typing s) \<Longrightarrow>
    vs \<in> init s \<Longrightarrow> 
    length vs = n \<Longrightarrow>
    (\<forall>i\<in>{0..<n}. r s (ptr +\<^sub>p int i) = ZERO('a)) \<Longrightarrow>
    (\<forall>i\<in>{0..<n}. root_ptr_valid d (ptr +\<^sub>p int i)) \<Longrightarrow>
    (f ptr) \<bullet> (stack_ptr_acquire n vs ptr d s) 
      \<lbrace>\<lambda>r u. (\<forall>i<n. root_ptr_valid (heap_typing u) (ptr +\<^sub>p int i)) \<and> Q r (stack_ptr_release n ptr u)\<rbrace>"
  shows
    "(guard_with_fresh_stack_ptr n init f) \<bullet> s \<lbrace> Q \<rbrace>"
  apply (unfold guard_with_fresh_stack_ptr_def assume_stack_alloc_def)
  apply runs_to_vcg
  apply (auto elim: stack_allocs_cases)
  done


lemma runs_to_with_fresh_stack_ptr[runs_to_vcg]:
  assumes f[runs_to_vcg]:"\<And>d ptr vs. 
    (ptr, d) \<in> stack_allocs n \<S> TYPE('a) (heap_typing s) \<Longrightarrow>
    vs \<in> init s \<Longrightarrow> 
    length vs = n \<Longrightarrow>
    (\<forall>i\<in>{0..<n}. r s (ptr +\<^sub>p int i) = ZERO('a)) \<Longrightarrow>
    (\<forall>i\<in>{0..<n}. root_ptr_valid d (ptr +\<^sub>p int i)) \<Longrightarrow>
    (f ptr) \<bullet> (stack_ptr_acquire n vs ptr d s) \<lbrace>\<lambda>r u. Q r (stack_ptr_release n ptr u)\<rbrace>"
  shows 
    "(assume_with_fresh_stack_ptr n init f) \<bullet> s \<lbrace> Q \<rbrace>"
    "(with_fresh_stack_ptr        n init f) \<bullet> s \<lbrace> Q \<rbrace>"
  subgoal
    apply (unfold assume_with_fresh_stack_ptr_def assume_stack_alloc_def)
    apply (runs_to_vcg)
    apply (auto elim: stack_allocs_cases simp add: singleton_iff)
    done
  subgoal
    apply (unfold with_fresh_stack_ptr_def on_exit_def assume_stack_alloc_def)  
    apply (runs_to_vcg)
    apply (auto elim: stack_allocs_cases simp add: singleton_iff)
    done
  done

lemma lvp_distinct_singleton_local_with_params:
  fixes p::"'a ptr"
  assumes "(p, d') \<in> stack_allocs n \<S> TYPE('a) d"
  assumes "root_ptr_valid d' p"
  assumes "distinct_span params"
  assumes "\<forall>(v, s) \<in> set params. disjnt {v ..+ s} (stack_free d)"
  assumes "\<forall>(v, s) \<in> set params. s > 0"
  shows "lvp_distinct ((d', ptr_val p, n, size_td (typ_uinfo_t TYPE('a)))#(map (\<lambda>(v, s). (d, v, 1, s)) params))"
  unfolding lvp_distinct_def
  apply (clarsimp simp: case_prod_beta distinct_spans_def assume_stack_alloc_def)
  apply (intro conjI, clarsimp simp: distinct_prop_map)
  subgoal for v t
    using assms(4) apply clarsimp
    apply (rule disjnt_subset1 [where X="stack_free d"])
    apply (auto simp: disjnt_comm [simplified disjnt_def] disjnt_def)[1]
    apply (simp add: size_of_fold)
    by (rule stack_allocs_stack_subset_stack_free [OF assms(1), simplified])
  subgoal
    apply (clarsimp simp: distinct_prop_map)
    apply (rule distinct_prop_iff [THEN iffD1, OF _ assms(3) [simplified distinct_span_def]])
    by clarsimp
  subgoal
    apply (clarsimp)
    by (contradiction, rule stack_allocs_neq [OF assms(1)], erule sym)
  subgoal
    apply (rule distinct_iff_distinct_prop_ne [THEN iffD2])
    apply (clarsimp simp: distinct_prop_map)
    apply (rule distinct_prop_impl [OF _ assms(3) [simplified distinct_span_def]])
    using assms(5) apply clarsimp
    subgoal for t v t'
      apply (frule(1) bspec [where x="(v, t)"], drule(1) bspec [where x="(v, t')"])
      by (auto simp: intvl_start_inter disjnt_def)
    done
  subgoal
    apply (rule ssubst [OF stack_free_stack_allocs [OF assms(1)]])
    by clarsimp
  subgoal apply (clarsimp simp: sorted_wrt_map)
    apply (rule sorted_wrt_mono_rel [where P="\<lambda>x y. stack_free d \<subseteq> stack_free d"])
    apply (clarsimp)
    by (simp)
  subgoal
    apply (simp add: size_of_fold disjnt_def)
    by (rule fresh_ptrs_stack_free_disjunct [OF assms(1), simplified])
  subgoal
    by (simp add: size_of_fold)
  subgoal
    using assms(4,5) by (auto simp: disjnt_def dest!: bspec)
  done

lemma runs_to_init_local_variables_and_parameters:
  assumes
    "n > 0"
    "distinct_span params"
    "\<forall>(v, sz)\<in>set params. disjnt {v..+sz} (stack_free (heap_typing s))"
    "\<forall>(v, sz)\<in>set params. 0 < sz"
    "\<And>d ptr vs.
        (ptr, d) \<in> stack_allocs n \<S> TYPE('a) (heap_typing s) \<Longrightarrow>
        vs \<in> init s \<Longrightarrow>
        length vs = n \<Longrightarrow>
        \<forall>i\<in>{0..<n}. r s (ptr +\<^sub>p int i) = ZERO('a) \<Longrightarrow>
        \<forall>i\<in>{0..<n}. root_ptr_valid d (ptr +\<^sub>p int i) \<Longrightarrow>
        lvp_distinct ((d, ptr_val ptr, n, size_td (typ_uinfo_t TYPE('a)))#(map (\<lambda>(v, sz). (heap_typing s, v, 1, sz)) params)) \<Longrightarrow>
        f ptr \<bullet> (stack_ptr_acquire n vs ptr d s) \<lbrace> \<lambda>r u. Q r (stack_ptr_release n ptr u) \<rbrace>"
  shows "assume_with_fresh_stack_ptr n init f \<bullet> s \<lbrace> Q \<rbrace>"
  apply (rule runs_to_with_fresh_stack_ptr)
  apply (rule assms(5))
  apply (assumption)+
  apply (rule lvp_distinct_singleton_local_with_params)
  apply (simp add: assms)
  by (drule bspec [where x=0], simp, rule assms(1), simp add: ptr_add_def) (rule assms)+

lemma lvp_distinct_add_stack_allocs:
  fixes p::"'a ptr"
  assumes "(p, d') \<in> stack_allocs n \<S> TYPE('a) (fst (hd xs))"
  assumes "n > 0"
  assumes "root_ptr_valid d' p"
  assumes "lvp_distinct xs"
  shows "lvp_distinct ((d', ptr_val p, n, size_td (typ_uinfo_t TYPE('a)))#xs)"
  unfolding lvp_distinct_def
  apply (clarsimp simp: case_prod_beta distinct_spans_def)
  apply (intro conjI, clarsimp)
  subgoal for d v n t
    using assms(4) apply (clarsimp simp: lvp_distinct_def)
    apply (rule disjnt_subset1 [where X="stack_free d"])
    subgoal by (auto simp: disjnt_comm [simplified disjnt_def] disjnt_def)[1]
    apply (rule subset_trans)
     apply (simp add: size_of_fold)
     apply (rule stack_allocs_stack_subset_stack_free [OF assms(1), simplified])
    apply (drule sorted_wrt_hd_min [rotated], clarsimp)
    by (drule(1) bspec, auto)
  subgoal using assms(4) by (auto simp: lvp_distinct_def distinct_spans_def)
  subgoal 
    using assms(4) apply (clarsimp simp: lvp_distinct_def)
    apply (drule(1) bspec, clarsimp)
    apply (rule disjoint_no_subset)
    apply (rule fresh_ptrs_stack_free_disjunct [OF assms(1)], simp add: assms(2) intvl_non_zero_non_empty)     
    apply (rule subset_trans)
     apply (rule stack_allocs_stack_subset_stack_free [OF assms(1)])
    apply (drule sorted_wrt_hd_min [rotated], clarsimp)
    by (drule (1) bspec, auto)
  subgoal
    using assms(4) by (clarsimp simp: lvp_distinct_def)
  apply (rule ballI)
  subgoal for x
    apply (cases x; simp)
    subgoal for d v' t'
      apply (rule subset_trans)
       apply (rule ssubst [OF stack_free_stack_allocs [OF assms(1)]])
       apply (rule Diff_subset)
      using assms(4) apply (clarsimp simp: lvp_distinct_def)
      apply (drule sorted_wrt_hd_min [rotated], clarsimp)
      by (drule(1) bspec, auto)
    done
  subgoal using assms(4) by (auto simp: lvp_distinct_def)
  subgoal 
    apply (simp add: size_of_fold disjnt_def)
    by (rule fresh_ptrs_stack_free_disjunct [OF assms(1), simplified])
  subgoal by (simp add: size_of_fold)
  subgoal using assms(4) by (auto simp: lvp_distinct_def case_prod_beta)
  done

lemma runs_to_add_local_variable:
  assumes
    "lvp_distinct xs"
    "heap_typing s = fst (hd xs)"
    "n > 0"
    "\<And>d ptr vs.
        (ptr, d) \<in> stack_allocs n \<S> TYPE('a) (heap_typing s) \<Longrightarrow>
        vs \<in> init s \<Longrightarrow>
        length vs = n \<Longrightarrow>
        \<forall>i\<in>{0..<n}. r s (ptr +\<^sub>p int i) = ZERO('a) \<Longrightarrow>
        \<forall>i\<in>{0..<n}. root_ptr_valid d (ptr +\<^sub>p int i) \<Longrightarrow>
        lvp_distinct ((d, ptr_val ptr, n, size_td (typ_uinfo_t TYPE('a)))#xs) \<Longrightarrow>
        (f ptr) \<bullet> (stack_ptr_acquire n vs ptr d s) \<lbrace> \<lambda>r u. Q r (stack_ptr_release n ptr u) \<rbrace>"
  shows "(assume_with_fresh_stack_ptr n init f) \<bullet> s \<lbrace> Q \<rbrace>"
  apply (rule runs_to_with_fresh_stack_ptr)
  apply (rule assms(4))
  apply (assumption)+
  apply (rule lvp_distinct_add_stack_allocs)
  apply (simp add: assms)
  apply (rule assms(3))
  by (drule bspec [where x=0], simp, rule assms(3), simp add: ptr_add_def) (rule assms(1))

end

end
