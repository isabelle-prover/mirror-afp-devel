(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>More Stack Typing\<close>

theory Stack_Typing
imports L2Defs Runs_To_VCG
begin

definition equal_upto:: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
 "equal_upto S f g = (\<forall>x. x \<notin> S \<longrightarrow> f x = g x)"

lemma equal_upto_refl[simp, intro]: "equal_upto S f f"
  by (simp add: equal_upto_def)

lemma symp_equal_upto: "symp (equal_upto S)"
  by (simp add: equal_upto_def symp_def)

lemma equal_upto_commute: "equal_upto S f g \<longleftrightarrow> equal_upto S g f"
  using symp_equal_upto
  by (metis sympE)

lemma equal_upto_trans[trans]: "equal_upto S f g \<Longrightarrow> equal_upto S g h \<Longrightarrow> equal_upto S f h"
  by (simp add: equal_upto_def)

lemma equal_upto_mono: "S \<subseteq> T \<Longrightarrow> equal_upto S f g \<Longrightarrow> equal_upto T f g"
  by (meson equal_upto_def subset_iff)

definition equal_on:: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
 "equal_on S f g = (\<forall>x. x \<in> S \<longrightarrow> f x = g x)"

lemma equal_on_UNIV_iff[simp]: "equal_on UNIV f g \<longleftrightarrow> f = g"
  by (auto simp add: equal_on_def)

lemma equal_on_refl [simp, intro]: "equal_on S f f"
  by (auto simp add: equal_on_def)

lemma symp_equal_on: "symp (equal_on S)"
  by (simp add: equal_on_def symp_def)

lemma equal_on_commute: "equal_on S f g \<longleftrightarrow> equal_on S g f"
  using symp_equal_on
  by (metis sympE)

lemma equal_on_trans[trans]: "equal_on S f g \<Longrightarrow> equal_on S g h \<Longrightarrow> equal_on S f h"
  by (simp add: equal_on_def)

lemma equal_on_mono: "S \<subseteq> T \<Longrightarrow> equal_on T f g \<Longrightarrow> equal_on S f g"
  by (meson equal_on_def subset_iff)

lemma equal_on_equal_upto_eq: "equal_on S f g \<Longrightarrow> equal_upto S f g \<Longrightarrow> f = g"
  by (auto simp add: equal_on_def equal_upto_def)

named_theorems unchanged_typing_on_simps and unchanged_typing

declare mex_def [unchanged_typing_on_simps] 
declare meq_def [unchanged_typing_on_simps] 

ML \<open>
structure Unchanged_Typing =
struct
fun unchanged_typing_tac splitter ctxt =
  let
    val unchanged_typing_on_simps = Named_Theorems.get ctxt @{named_theorems unchanged_typing_on_simps}
    val unchanged_typing = Named_Theorems.get ctxt @{named_theorems unchanged_typing}
    val vcg_attrs = map (Attrib.attribute ctxt) @{attributes [runs_to_vcg]}
    val (_, ctxt) = ctxt |> fold_map (Thm.proof_attributes vcg_attrs) unchanged_typing
    val ctxt = ctxt addsimps unchanged_typing_on_simps

    val trace_tac = Runs_To_VCG.no_trace_tac
    fun solver_tac ctxt = ALLGOALS (asm_full_simp_tac ctxt)
  in
    Runs_To_VCG.runs_to_vcg_tac splitter (~1) trace_tac  
          {do_nosplit = false, no_unsafe_hyp_subst = false} solver_tac ctxt
  end
end
\<close>


lemma stack_allocs_releases_equal_on_stack: 
"(p, d2) \<in> stack_allocs n \<S> TYPE('a::mem_type) d1 \<Longrightarrow>
   equal_on \<S> d2 d3 \<Longrightarrow> equal_on \<S> d1 (stack_releases n p d3)"
  by (smt (verit, best) equal_on_def stack_releases_footprint stack_releases_other 
      stack_releases_stack_allocs_inverse)

lemma stack_allocs_releases_equal_on_typing: 
"(p, d2) \<in> stack_allocs n \<S> TYPE('a::mem_type) d1 \<Longrightarrow>
   equal_on X d2 d3 \<Longrightarrow> equal_on X d1 (stack_releases n p d3)"
  by (smt (verit, best) equal_on_def stack_releases_footprint stack_releases_other 
      stack_releases_stack_allocs_inverse)

lemma stack_allocs_releases_equal_on_typing': 
"(p, d2) \<in> stack_allocs n \<S> TYPE('a::mem_type) d1 \<Longrightarrow> 
   equal_on X' d2 d3 \<Longrightarrow>  X \<subseteq> X' \<Longrightarrow> equal_on X d1 (stack_releases n p d3)"
  using stack_allocs_releases_equal_on_typing
  using equal_on_mono by blast
    
context heap_typing_state
begin

definition unchanged_typing_on:: "addr set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
"unchanged_typing_on S s t = equal_on S (htd s) (htd t)"

lemma unchanged_typing_on_UNIV_iff: "unchanged_typing_on UNIV s t \<longleftrightarrow> htd s = htd t"
  by (auto simp add: unchanged_typing_on_def)

lemma unchanged_typing_on_UNIV_I: "htd s = htd t \<Longrightarrow> unchanged_typing_on UNIV s t"
  by (simp add: unchanged_typing_on_UNIV_iff)

lemma typing_eq_unchanged_typing_on: "htd s = htd t \<Longrightarrow> unchanged_typing_on S s t"
  by (auto simp add: unchanged_typing_on_def equal_on_def)

lemma unchanged_typing_on_relf[simp]: "unchanged_typing_on S s s"
  by (auto simp add: unchanged_typing_on_def equal_on_def)

lemma unchanged_typing_on_conv[unchanged_typing_on_simps]: "unchanged_typing_on S s t \<longleftrightarrow> (\<forall>a \<in> S. htd s a = htd t a)"
  by (auto simp add: unchanged_typing_on_def equal_on_def)

lemma unchanged_typing_on_cong: "(\<And>a. a \<in> S \<Longrightarrow> htd s a = htd s' a) \<Longrightarrow>
  (\<And>a. a \<in> S \<Longrightarrow> htd t a = htd t' a)
  \<Longrightarrow> unchanged_typing_on S s t \<longleftrightarrow> unchanged_typing_on S s' t"
  by (simp add: unchanged_typing_on_def equal_on_def)

lemma typing_eq_left_unchanged_typing_on: "htd s1 = htd s2 \<Longrightarrow> 
  unchanged_typing_on S s1 t \<longleftrightarrow> unchanged_typing_on S s2 t"
  by (auto simp add: unchanged_typing_on_def equal_on_def)


lemma symp_unchanged_typing_on: "symp (unchanged_typing_on S)"
  using symp_equal_on
  by (metis symp_def unchanged_typing_on_def)

lemma unchanged_typing_on_commute: "unchanged_typing_on S s t \<longleftrightarrow> unchanged_typing_on S t s"
  using symp_unchanged_typing_on
  by (metis sympE)

lemma unchanged_typing_on_trans[trans]: 
  assumes s_t: "unchanged_typing_on S s t" 
  assumes t_u: "unchanged_typing_on S t u" 
  shows "unchanged_typing_on S s u"
  by (meson equal_on_trans s_t t_u unchanged_typing_on_def)

lemma unchanged_typing_on_mono: "S \<subseteq> T \<Longrightarrow> unchanged_typing_on T s t \<Longrightarrow> unchanged_typing_on S s t"
  using equal_on_mono
  by (smt (verit) unchanged_typing_on_def)

lemma unchanged_typing_on_root_ptr_valid_preservation:
  fixes p::"'a::mem_type ptr"
  assumes "unchanged_typing_on S s t" 
  assumes "ptr_span p \<subseteq> S"
  assumes "root_ptr_valid (htd s) p"
  shows "root_ptr_valid (htd t) p"
  using assms
  by (simp add: equal_on_def root_ptr_valid_domain subset_iff unchanged_typing_on_def)


simproc_setup unchanged_typing_nondet (\<open>c \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on \<S> s t\<rbrace>\<close>) = \<open>
  let
    val prop_to_meta_eq = @{lemma \<open>P \<Longrightarrow> (P \<equiv> True)\<close> for P by auto}
    fun try_prove ctxt prop  = try (Goal.prove_internal ctxt [] prop) 
          (fn _ => Unchanged_Typing.unchanged_typing_tac NONE ctxt) 
  in
    fn phi => fn ctxt => fn ct =>
      let
        val _ = Utils.verbose_msg 3 ctxt (fn _ => "unchanged_typing_nondet invoked on: " ^ @{make_string} ct)
      in
        try_prove ctxt \<^instantiate>\<open>P = ct in cterm \<open>Trueprop P\<close> for P\<close> 
        |> Option.map (fn thm => prop_to_meta_eq OF [thm])
      end
     
  end
\<close>
declare [[simproc del: unchanged_typing_nondet]]
end

context stack_heap_state
begin
lemma with_fresh_stack_ptr_unchanged_typing[unchanged_typing]: 
  assumes f[runs_to_vcg]:"\<And>p s. (f p) \<bullet> s ?\<lbrace>\<lambda>r t. typing.unchanged_typing_on \<S> s t\<rbrace>"
  shows "(with_fresh_stack_ptr n I (L2_VARS f nm)) \<bullet> s ?\<lbrace>\<lambda>r t. typing.unchanged_typing_on \<S> s t\<rbrace>"
  unfolding with_fresh_stack_ptr_def on_exit_def on_exit'_def L2_VARS_def
  apply (runs_to_vcg)
  subgoal for x d vs r t
    thm typing.typing_eq_left_unchanged_typing_on
    thm typing.typing_eq_left_unchanged_typing_on [of _ "(htd_upd (\<lambda>_. d) s)"]
    apply (subst (asm) typing.typing_eq_left_unchanged_typing_on [of _ "(htd_upd (\<lambda>_. d) s)"])
     apply simp
    apply (simp add: typing.unchanged_typing_on_def stack_allocs_releases_equal_on_stack)
    done
  done
end

lemma override_on_merge: "override_on (override_on f g B) g A = override_on f g (A \<union> B)"
  by (auto simp add: override_on_def fun_eq_iff)

lemma override_on_id [simp]: "override_on f f A = f"
  by (auto simp add: override_on_def)

lemma override_cancel_snd [simp]: "override_on f (override_on g1 g0 A) A = override_on f g0 A"
  by (auto simp add: override_on_def)

lemma override_cancel_subset_snd : "A \<subseteq> B \<Longrightarrow> override_on f (override_on g1 g0 B) A = override_on f g0 A"
 by (auto simp add: override_on_def fun_eq_iff)

lemma override_cancel_fst[simp] : "override_on (override_on f1 f0 A) g A = override_on f1 g A"
  by (auto simp add: override_on_def fun_eq_iff)

lemma override_cancel_subset_fst : "A \<subseteq> B \<Longrightarrow> override_on (override_on f1 f0 A) g B = override_on f1 g B"
  by (auto simp add: override_on_def fun_eq_iff)

lemma equal_on_stack_free_preservation:
  assumes eq: "equal_on S d2 d1"
  assumes "stack_free d1 \<subseteq> S"
  assumes "stack_free d2 \<subseteq> S"
  shows "stack_free d2 = stack_free d1"
  using assms
  by (smt (verit, best) Abs_fnat_hom_0 Collect_cong One_nat_def add.right_neutral equal_on_def less_Suc0 mem_Collect_eq ptr_val.simps 
      root_ptr_valid_def size_of_stack_byte(3) stack_free_def subsetD valid_root_footprint_def)


lemma equal_upto_disjoint_h_val: "equal_upto P h' h \<Longrightarrow>
  ptr_span p \<inter> P = {} \<Longrightarrow> 
  h_val h' (p::'a::mem_type ptr) = h_val h p"
  by (smt (verit, best) disjoint_iff equal_upto_def h_val_def heap_list_h_eq2)

context heap_state 
begin


definition equal_upto_heap_on:: "addr set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
"equal_upto_heap_on S s t = (\<exists>T H. 
    t = hmem_upd (\<lambda>_. H) (htd_upd (\<lambda>_. T) s) \<and> 
    equal_upto S (hmem s) H \<and>
    equal_upto S (htd s) T)"

definition zero_heap_on:: "addr set \<Rightarrow> 's \<Rightarrow> 's" where
  "zero_heap_on A s = hmem_upd (\<lambda>h. override_on h zero_heap A) (htd_upd (\<lambda>htd. override_on htd stack_byte_typing A) s)"

lemma equal_upto_heap_on_equal_upto_htd: "equal_upto_heap_on S s t \<Longrightarrow> equal_upto S (htd s) (htd t)"
  by (auto simp add: equal_upto_heap_on_def)

lemma equal_upto_heap_on_equal_upto_hmem: "equal_upto_heap_on S s t \<Longrightarrow> equal_upto S (hmem s) (hmem t)"
  by (auto simp add: equal_upto_heap_on_def)

lemma zero_heap_on_empty[simp]: "zero_heap_on {} s = s"
  by (auto simp add: zero_heap_on_def)

lemma equal_upto_heap_on_zero_heap_on_subset: "A \<subseteq> B \<Longrightarrow> equal_upto_heap_on B s (zero_heap_on A s)"
  apply (clarsimp simp add: zero_heap_on_def equal_upto_heap_on_def override_on_def)
  by (smt (verit, best) equal_upto_def equal_upto_mono heap.upd_cong hmem_htd_upd typing.upd_cong)

lemma equal_upto_heap_on_zero_heap_on[simp]: "equal_upto_heap_on A s (zero_heap_on A s)"
  by (simp add: equal_upto_heap_on_zero_heap_on_subset)

lemma equal_upto_heap_on_refl[simp, intro]: "equal_upto_heap_on S s s"
  by (force simp add: equal_upto_heap_on_def)

lemma override_on_heap_update_other:
  fixes p::"'a::mem_type ptr"
  shows "ptr_span p \<subseteq> A \<Longrightarrow> override_on (heap_update p v h) f A = override_on h f A"
  apply (clarsimp simp add: override_on_def fun_eq_iff)
  by (smt (verit, ccfv_SIG) CTypes.mem_type_simps(2) heap_list_length heap_update_def heap_update_nmem_same subsetD)

lemma override_on_heap_update_commute:
  fixes p::"'a::mem_type ptr"
  shows "ptr_span p \<inter> A = {} \<Longrightarrow>  
  override_on (heap_update p v h) f A = heap_update p v (override_on h f A)"
  apply (clarsimp simp add: override_on_def fun_eq_iff heap_update_def heap_update_nmem_same orthD2)
  by (smt (verit, best) disjoint_iff heap_list_h_eq2 heap_list_length heap_update_list_value len max_size)

lemma override_on_heap_update_padding_other:
  fixes p::"'a::mem_type ptr"
  shows "ptr_span p \<subseteq> A \<Longrightarrow> length bs = size_of TYPE('a) \<Longrightarrow> override_on (heap_update_padding p v bs h) f A = override_on h f A"
  apply (clarsimp simp add: override_on_def fun_eq_iff)
  by (smt (verit) CTypes.mem_type_simps(2) heap_update_nmem_same heap_update_padding_def subsetD)

lemma zero_heap_on_heap_update_other: 
  fixes p::"'a::mem_type ptr"
  shows "ptr_span p \<subseteq> A \<Longrightarrow> zero_heap_on A (hmem_upd (heap_update p v) s) = zero_heap_on A s"
  by (simp add: zero_heap_on_def heap_commute comp_def override_on_heap_update_other)


lemma override_on_stack_byte_typing_stack_allocs:    
  assumes alloc: "(p, d) \<in> stack_allocs n \<S> TYPE('a::mem_type) d0"
  assumes subset: "stack_free d0 \<subseteq> A"
  shows "override_on d stack_byte_typing A = override_on d0 stack_byte_typing A"
  using alloc subset
  apply (simp add: override_on_def fun_eq_iff)
  by (meson in_mono stack_allocs_other stack_allocs_stack_subset_stack_free)



lemma zero_heap_on_stack_allocs: 
  assumes alloc: "(p, d) \<in> stack_allocs n \<S> TYPE('a::mem_type) (htd s)"
  assumes subset: "stack_free (htd s) \<subseteq> A"
  shows "zero_heap_on A (htd_upd (\<lambda>_. d) s) = zero_heap_on A s"
  apply (simp add: zero_heap_on_def comp_def)
  using override_on_stack_byte_typing_stack_allocs [OF alloc subset]
  by (metis (no_types, lifting) typing.upd_cong)


lemma zero_heap_on_stack_releases:
  fixes p:: "'a::mem_type ptr"
  assumes subset: "{ptr_val p..+n * size_of TYPE('a::mem_type)} \<subseteq> A"
  shows "zero_heap_on A (htd_upd (stack_releases n p) s) = zero_heap_on A s"
  using subset
  by (simp add: zero_heap_on_def comp_def stack_releases_def override_on_merge Un_absorb2  )

lemma zero_heap_on_stack_releases':
  fixes p:: "'a::mem_type ptr"
  assumes guard: "(\<And>i. i < n \<Longrightarrow> c_null_guard (p +\<^sub>p int i))"
  shows "zero_heap_on (stack_free (stack_releases n p (htd s)) \<union> A) (htd_upd (stack_releases n p) s) = 
           zero_heap_on (stack_free (htd s) \<union> {ptr_val p..+n * size_of TYPE('a)} \<union> A) s"
  apply (subst stack_free_stack_releases)
   apply (simp add: guard)
  apply (subst zero_heap_on_stack_releases)
   apply blast
  apply (simp add: sup_commute)
  done



  
text \<open>We want to express that certain portions of the heap (typing and values) are 'irrelevant',
in particular regarding (free) stack space. The notion of 'irrelevant' is a bit vague, it means
that the behaviour of the program does not depend on those locations and also that it does not 
modify those locations. Moreover, we prefer an abstraction function rather than an 
relation between states to avoid admissibility issues for refinement.\<close>
definition frame:: "addr set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "frame A s\<^sub>0 s =
     hmem_upd (\<lambda>h. override_on h (hmem s\<^sub>0) (A \<union> stack_free (htd s))) 
      (htd_upd (\<lambda>d. override_on d (htd s\<^sub>0) (A - stack_free (htd s))) s)"
text \<open>The standard use case we have in mind is @{term "A \<inter> stack_free (htd s) = {}"}, hence
@{prop "A - stack_free (htd s) = A"}, but nevertheless the intuition is:
\<^item> stack free typing from \<^term>\<open>s\<close> is preserved, the framed sate has at least as many stack free
  addresses as the original one. So we can simulate any stack allocation.
\<^item> heap values for stack free and \<^term>\<open>A\<close> are taken from reference state \<^term>\<open>s\<^sub>0\<close>, this
  captures that we do not depend on the original values in \<^term>\<open>s\<close> for those addresses.
\<^item> typing for allocations in \<^term>\<open>A\<close> is taken from reference state \<^term>\<open>s\<^sub>0\<close>, this captures
  that we do not depend on the original typing in \<^term>\<open>s\<close> for those addresses.

By taking the same reference state \<^term>\<open>s\<^sub>0\<close> to frame two states \<^term>\<open>s\<close> and \<^term>\<open>s'\<close>,
we can express that the 'irrelevant' parts of the heap did not change in the respective
framed states \<^term>\<open>frame A s\<^sub>0 s\<close> and \<^term>\<open>frame A s\<^sub>0 s'\<close>.
\<close>

definition raw_frame:: "addr set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "raw_frame A s\<^sub>0 s =
     hmem_upd (\<lambda>h. override_on h (hmem s\<^sub>0) A) 
      (htd_upd (\<lambda>d. override_on d (htd s\<^sub>0) A) s)"

lemma frame_heap_independent_selector: 
  "(\<And>f s. sel (hmem_upd f s) = sel s) \<Longrightarrow> (\<And>f s. sel (htd_upd f s) = sel s) \<Longrightarrow>  
  sel (frame A s\<^sub>0 s) = sel s"
  by (auto simp add: frame_def)

lemma frame_id[simp]: "frame A s s = s"
  unfolding frame_def 
  by (simp add: heap.upd_same typing.upd_same)

lemma frame_hmem_UNIV[simp]: "hmem (frame UNIV s\<^sub>0 s) = hmem s\<^sub>0"
  unfolding frame_def
  by simp


lemma hmem_frame: "hmem (frame A s\<^sub>0 s) = (\<lambda>a. if a \<in> A \<union> stack_free (htd s) then hmem s\<^sub>0 a else hmem s a)"
  unfolding frame_def
  by (auto simp add: fun_eq_iff)

lemma htd_frame: "htd (frame A s\<^sub>0 s) = (\<lambda>a. if a \<in> (A - stack_free (htd s)) then htd s\<^sub>0 a else htd s a)"
  unfolding frame_def
  by (auto simp add: fun_eq_iff)

lemma stack_free_htd_frame: "stack_free (htd s) \<subseteq> stack_free (htd (frame A s\<^sub>0 s))"
  apply (clarsimp simp add: htd_frame stack_free_def root_ptr_valid_def)
  by (smt (verit) One_nat_def add.right_neutral less_Suc0 mem_Collect_eq orthD2 semiring_1_class.of_nat_0 size_of_stack_byte(3) valid_root_footprint_def)

lemma stack_free_htd_frame': "stack_free (htd s\<^sub>0) \<inter> A = {} \<Longrightarrow> stack_free (htd (frame A s\<^sub>0 s)) = stack_free (htd s)"
  by (auto simp add: htd_frame stack_free_def root_ptr_valid_def valid_root_footprint_def)

lemma equal_on_hmem_frame: "equal_on (A \<union> stack_free (htd s)) (hmem (frame A s\<^sub>0 s)) (hmem s\<^sub>0)"
  by (auto simp add: equal_on_def frame_def equal_upto_def override_on_def fun_eq_iff)

lemma equal_upto_hmem_frame: "equal_upto (A \<union> stack_free (htd s)) (hmem (frame A s\<^sub>0 s)) (hmem s)"
  by (auto simp add: equal_on_def frame_def equal_upto_def override_on_def fun_eq_iff)

lemma equal_on_htd_frame: "stack_free (htd s) \<inter> A = {} \<Longrightarrow> equal_on A (htd (frame A s\<^sub>0 s)) (htd s\<^sub>0)"
  by (auto simp add: equal_on_def frame_def equal_upto_def override_on_def fun_eq_iff)

lemma equal_on_htd_stack_free_frame: "stack_free (htd s) \<inter> A = {} \<Longrightarrow> 
  equal_on (stack_free (htd s)) (htd (frame A s\<^sub>0 s)) (htd s)"
  by (auto simp add: equal_on_def frame_def equal_upto_def override_on_def fun_eq_iff)

lemma equal_upto_htd_frame: "equal_upto A (htd (frame A s\<^sub>0 s)) (htd s)"
  by (auto simp add: equal_on_def frame_def equal_upto_def override_on_def fun_eq_iff)

lemma equal_upto_heap_on_frame: "equal_upto_heap_on (A \<union> stack_free (htd s)) (frame A s\<^sub>0 s) s"
  apply (clarsimp simp add: equal_upto_heap_on_def frame_def equal_upto_def override_on_def fun_eq_iff)
  by (smt (verit, ccfv_threshold) K_record_comp heap.upd_compose heap.upd_same heap_commute typing.upd_compose typing.upd_same)

lemma frame_heap_update: 
  fixes p::"'a::mem_type ptr"
  shows "ptr_span p \<subseteq> A \<Longrightarrow> frame A s\<^sub>0 (hmem_upd (heap_update p v) s) = frame A s\<^sub>0 s"
  apply (clarsimp simp add: frame_def)
  apply (subst heap_commute [symmetric])
  apply (simp add: comp_def )
  apply (subst override_on_heap_update_other)
   apply auto
  done

lemma frame_heap_update_disjoint: 
  fixes p::"'a::mem_type ptr"
  shows "ptr_span p \<inter> A = {} \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {} \<Longrightarrow> 
  frame A s\<^sub>0 (hmem_upd (heap_update p v) s) = hmem_upd (heap_update p v) (frame A s\<^sub>0 s)"
  apply (clarsimp simp add: frame_def)
  apply (subst heap_commute [symmetric])
  apply (simp add: comp_def)
  apply (subst override_on_heap_update_commute)
   apply blast
  apply blast
  done

lemma h_val_frame_disjoint': 
  fixes p::"'a::mem_type ptr"
  shows "ptr_span p \<inter> A = {} \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {} \<Longrightarrow>
  ptr_span p = ptr_span p' \<Longrightarrow>
  h_val (hmem (frame A s\<^sub>0 s)) p' = h_val (hmem s) p'"
  apply (clarsimp simp add: frame_def override_on_def)
  by (smt (verit, del_insts) disjoint_iff h_val_def heap_list_h_eq2 hmem_htd_upd)

lemma h_val_frame_disjoint: 
  fixes p::"'a::mem_type ptr"
  shows "ptr_span p \<inter> A = {} \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {} \<Longrightarrow> 
  h_val (hmem (frame A s\<^sub>0 s)) p = h_val (hmem s) p"
  apply (erule (1) h_val_frame_disjoint')
  by (rule refl)

lemma h_val_frame_disjoint_globals: 
  fixes p::"'a::mem_type ptr"
  assumes "\<G> \<inter> A = {}" "\<G> \<inter> stack_free (htd s) = {}" 
  assumes "ptr_span p \<subseteq> \<G>"
  shows "h_val (hmem (frame A s\<^sub>0 s)) p = h_val (hmem s) p"
  apply (rule h_val_frame_disjoint)
  subgoal using assms by blast
  subgoal using assms by blast
  done

lemma frame_heap_update_padding: 
  fixes p::"'a::mem_type ptr"
  shows "ptr_span p \<subseteq> A \<Longrightarrow> length bs = size_of TYPE('a) ==> frame A s\<^sub>0 (hmem_upd (heap_update_padding p v bs) s) = frame A s\<^sub>0 s"
  apply (clarsimp simp add: frame_def)
  apply (subst heap_commute [symmetric])
  apply (simp add: comp_def )
  apply (subst override_on_heap_update_padding_other)
   apply auto
  done

lemma frame_stack_alloc: 
  fixes p::"'a::mem_type ptr"
  assumes subset: "ptr_span p \<subseteq> stack_free (htd s)" 
  assumes disjoint: "stack_free (htd s) \<inter> A = {}"
  assumes alloc: "stack_free (ptr_force_type p (htd s)) = stack_free (htd s) - ptr_span p"
  shows  
  "frame (ptr_span p \<union> A) (htd_upd (\<lambda>d. override_on d stack_byte_typing (ptr_span p)) t\<^sub>0)
     (htd_upd (\<lambda>_. ptr_force_type p (htd s)) s) = frame A t\<^sub>0 s"
proof -
  from alloc subset disjoint 
  have *: "ptr_span p \<union> A \<union> stack_free (ptr_force_type p (htd s)) = A \<union> stack_free (htd s)"
    by auto
  from subset disjoint alloc
  have **:"override_on (ptr_force_type p (htd s))
             (override_on (htd t\<^sub>0) stack_byte_typing (ptr_span p)) (ptr_span p \<union> A - stack_free (ptr_force_type p (htd s))) = override_on (htd s) (htd t\<^sub>0) (A  - stack_free (htd s))"
    apply (clarsimp simp add: override_on_def fun_eq_iff  ptr_force_type_d)
    by (smt (verit, ccfv_threshold) add.right_neutral mem_Collect_eq old.prod.exhaust 
        prod.sel(1) prod.sel(2) ptr_val.ptr_val_def root_ptr_valid_def semiring_1_class.of_nat_0 stack_byte_typing_footprint stack_free_def subset_iff valid_root_footprint_def)
   show ?thesis
     apply (clarsimp simp add: frame_def comp_def * **) 
     by (metis (no_types, lifting) typing.upd_cong)
qed


lemma frame_stack_release:
  fixes p::"'a::mem_type ptr"
  assumes disjoint_free: "ptr_span p \<inter> stack_free (htd s) = {}" 
  assumes disjoint_old: "ptr_span p \<inter> A = {}"
  assumes c_null_guard: "c_null_guard p"
  assumes lbs: "length bs = size_of TYPE ('a)"
  shows "frame (ptr_span p \<union> A) (htd_upd (\<lambda>d. override_on d stack_byte_typing (ptr_span p)) t\<^sub>0) s =
          frame A t\<^sub>0 (hmem_upd (heap_update_list (ptr_val p) bs) (htd_upd (stack_releases (Suc 0) p) s))"
proof -
  from disjoint_free c_null_guard
  have *: "(ptr_span p \<union> A \<union> stack_free (htd s)) = A \<union> stack_free (stack_releases (Suc 0) p (htd s))"
    by (metis (no_types, opaque_lifting) Un_assoc add.right_neutral mult_0 stack_free_stack_release 
        stack_release_def stack_releases_def sup_commute times_nat.simps(2))

  from disjoint_free disjoint_old c_null_guard
  have **: "override_on (htd s) (override_on (htd t\<^sub>0) stack_byte_typing (ptr_span p)) (ptr_span p \<union> A - stack_free (htd s)) = 
            override_on (stack_releases (Suc 0) p (htd s)) (htd t\<^sub>0) (A - stack_free (stack_releases (Suc 0) p (htd s)))"
    apply (clarsimp simp add: override_on_def fun_eq_iff stack_byte_typing_footprint stack_releases_footprint stack_releases_other,
        intro conjI impI)
    subgoal by auto 
    subgoal by auto
    subgoal by auto
    subgoal by (metis UnE add.right_neutral mult_is_0 stack_free_stack_release stack_release_def stack_releases_def times_nat.simps(2))
    using stack_free_stack_releases_mono by blast

  have ***: "override_on (heap_update_list (ptr_val p) bs (hmem s)) (hmem t\<^sub>0) (A \<union> stack_free (stack_releases (Suc 0) p (htd s)))  
         = 
        override_on (hmem s) (hmem t\<^sub>0) (A \<union> stack_free (stack_releases (Suc 0) p (htd s)))"
    using disjoint_old lbs *
    apply (clarsimp simp add: override_on_def fun_eq_iff stack_byte_typing_footprint stack_releases_footprint stack_releases_other)
    by (metis  Un_iff heap_update_nmem_same lbs)


  show ?thesis
    apply (simp add: frame_def comp_def * )
    apply (simp add: heap_commute)
    using ** ***
    by (metis (no_types, lifting) heap.get_upd heap.upd_compose heap.upd_cong htd_hmem_upd 
        typing.get_upd typing.upd_compose typing.upd_cong)
qed

lemma frame_stack_release_keep:
  fixes p::"'a::mem_type ptr"
  assumes disjoint_free: "ptr_span p \<inter> stack_free (htd s) = {}" 
  assumes disjoint_old: "ptr_span p \<inter> A = {}"
  assumes c_null_guard: "c_null_guard p"
  assumes lbs: "length bs = size_of TYPE('a)"
  shows "hmem_upd (heap_update_list (ptr_val p) (heap_list (hmem t\<^sub>0) (size_of TYPE('a)) (ptr_val p))) 
              ( htd_upd (stack_releases (Suc 0) p) (frame A t\<^sub>0 s)) =
          frame A t\<^sub>0 
             (hmem_upd (heap_update_list (ptr_val p) bs) 
               (htd_upd (stack_releases (Suc 0) p) s))"
proof -
  from disjoint_free c_null_guard
  have *: "(ptr_span p \<union> A \<union> stack_free (htd s)) = A \<union> stack_free (stack_releases (Suc 0) p (htd s))"
    by (metis (no_types, opaque_lifting) Un_assoc add.right_neutral mult_0 stack_free_stack_release 
        stack_release_def stack_releases_def sup_commute times_nat.simps(2))

  from disjoint_free disjoint_old c_null_guard
  have **: "stack_releases (Suc 0) p (override_on (htd s) (htd t\<^sub>0) (A - stack_free (htd s))) = 
            override_on (stack_releases (Suc 0) p (htd s)) (htd t\<^sub>0) (A - stack_free (stack_releases (Suc 0) p (htd s)))"
    apply (clarsimp simp add: override_on_def fun_eq_iff stack_byte_typing_footprint stack_releases_footprint stack_releases_other,
        intro conjI impI)
    subgoal by (smt (verit, del_insts) Un_iff add.right_neutral mult_is_0 stack_free_stack_release 
        stack_release_def stack_release_other stack_releases_def times_nat.simps(2))
    subgoal by (smt (verit, best) UnE less_Suc0 ptr_add_0_id semiring_1_class.of_nat_0 stack_free_stack_releases 
        stack_releases_footprint stack_releases_other)
    done

  have ***: "heap_update_list (ptr_val p) (heap_list (hmem t\<^sub>0) (size_of TYPE('a)) (ptr_val p))
              (override_on (hmem s) (hmem t\<^sub>0) (A \<union> stack_free (htd s))) =
           override_on (heap_update_list (ptr_val p) bs (hmem s)) (hmem t\<^sub>0) 
              (A \<union> stack_free (stack_releases (Suc 0) p (htd s)))"
    using lbs disjoint_old disjoint_free *
    apply (clarsimp simp add: override_on_def fun_eq_iff heap_update_nmem_same orthD2 heap_update_list_value )
    apply (smt (verit, ccfv_SIG) Un_iff heap_list_length heap_update_list_id' heap_update_list_value max_size)
    done
  show ?thesis
    apply (simp add: frame_def comp_def * heap_commute )
    using ** ***
    by (metis (no_types, lifting) heap.upd_cong htd_hmem_upd lense.upd_cong typing.lense_axioms)
  qed


lemma symp_equal_upto_heap_on: "symp (equal_upto_heap_on S)"
proof 
  fix s t
  assume "equal_upto_heap_on S s t"
  then obtain T H where 
    t: "t = hmem_upd (\<lambda>_. H) (htd_upd (\<lambda>_. T) s)" and
    eq_H: "equal_upto S (hmem s) H" and
    eq_T: "equal_upto S (htd s) T"
    by (auto simp add: equal_upto_heap_on_def)
  show "equal_upto_heap_on S t s"
  proof -
    define H' where "H' = hmem s"
    define T' where "T' = htd s"
    have "s = hmem_upd (\<lambda>_. H') (htd_upd (\<lambda>_. T') t)"
      unfolding H'_def T'_def
      apply (subst t)
      apply (simp add: heap_commute heap.upd_same typing.upd_same)
      done
    moreover
    from eq_H have "equal_upto S (hmem t) H'" 
      by (simp add: H'_def equal_upto_commute t)
    moreover
    from eq_T have "equal_upto S (htd t) T'" 
      by (simp add: T'_def equal_upto_commute t)
    ultimately show ?thesis
      by (auto simp add: equal_upto_heap_on_def)
  qed
qed

lemma equal_upto_heap_on_commute: "equal_upto_heap_on S s t \<longleftrightarrow> equal_upto_heap_on S s t"
  using symp_equal_upto_heap_on
  by (metis sympE)

lemma equal_upto_heap_on_trans[trans]: 
  assumes s_t: "equal_upto_heap_on S s t" 
  assumes t_u: "equal_upto_heap_on S t u" 
  shows "equal_upto_heap_on S s u"
proof -
  from s_t obtain T H where
    t: "t = hmem_upd (\<lambda>_. H) (htd_upd (\<lambda>_. T) s)" and
    eq_H: "equal_upto S (hmem s) H" and
    eq_T: "equal_upto S (htd s) T"
     by (auto simp add: equal_upto_heap_on_def)

  from t_u obtain T' H' where
    u: "u = hmem_upd (\<lambda>_. H') (htd_upd (\<lambda>_. T') t)" and
    eq_H': "equal_upto S (hmem t) H'" and
    eq_T': "equal_upto S (htd t) T'"
    by (auto simp add: equal_upto_heap_on_def)

  have "u = hmem_upd (\<lambda>_. H') (htd_upd (\<lambda>_. T') s)"
    apply (subst u)
    apply (subst t)
    apply (simp add: heap_commute comp_def)
    done

  moreover 
  from eq_H'
  have "equal_upto S (hmem s) H'"
    apply -
    apply (subst (asm) t)
    apply simp
    using eq_H equal_upto_trans by blast

  moreover 
  from eq_T'
  have "equal_upto S (htd s) T'"
    apply -
    apply (subst (asm) t)
    apply simp
    using eq_T equal_upto_trans by blast

  ultimately show ?thesis
    by (auto simp add: equal_upto_heap_on_def)
qed

lemma equal_upto_heap_on_mono: "S \<subseteq> T \<Longrightarrow> equal_upto_heap_on S s t \<Longrightarrow> equal_upto_heap_on T s t"
  using equal_upto_mono
  by (smt (verit) equal_upto_heap_on_def)

end


lemma runs_to_partial_L2_modify[runs_to_vcg]:
  "(L2_modify f) \<bullet> s ?\<lbrace>\<lambda>r t. r = Result () \<and> t = f s\<rbrace>"
  unfolding L2_defs
  apply runs_to_vcg
  done


lemma runs_to_partial_L2_unknown[runs_to_vcg]:
  "(\<And>x. P (Result x) s) \<Longrightarrow> (L2_unknown ns) \<bullet> s ?\<lbrace>P\<rbrace>"
  unfolding L2_defs
  apply runs_to_vcg
  apply simp
  done

lemma runs_to_partial_L2_seq[runs_to_vcg]:
  "f \<bullet> s ?\<lbrace> \<lambda>r t. (\<forall>a. r = Result a \<longrightarrow> g a \<bullet> t ?\<lbrace> Q \<rbrace>) \<and> (\<forall>e. r = Exn e \<longrightarrow> Q (Exn e) t) \<rbrace> \<Longrightarrow>
    (L2_seq f g) \<bullet> s ?\<lbrace> Q \<rbrace>"
  unfolding L2_defs
  apply runs_to_vcg
  done

lemma (in heap_typing_state) runs_to_partial_L2_seq[unchanged_typing]:
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  assumes [runs_to_vcg]: "\<And>r s. (g r) \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  shows  "(L2_seq f g) \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  by (runs_to_vcg) (auto simp add: unchanged_typing_on_simps)

lemma runs_to_partial_L2_gets[runs_to_vcg]:
  "P (Result (f s)) s \<Longrightarrow> (L2_gets f ns) \<bullet> s ?\<lbrace> P \<rbrace>"
  unfolding L2_defs
  apply runs_to_vcg
  done

lemma runs_to_partial_L2_condition[runs_to_vcg]:
  "(P s \<Longrightarrow> f \<bullet> s ?\<lbrace>Q\<rbrace>) \<Longrightarrow> (\<not> P s \<Longrightarrow> g \<bullet> s ?\<lbrace>Q\<rbrace>) \<Longrightarrow> (L2_condition P f g) \<bullet> s ?\<lbrace>Q\<rbrace>"
  unfolding L2_defs
  apply runs_to_vcg
   apply auto
  done

lemma runs_to_partial_L2_catch[runs_to_vcg]:
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace> \<lambda>r t. (\<forall>e. r = Exn e \<longrightarrow> ((g e) \<bullet> t ?\<lbrace> P \<rbrace>)) \<and> (\<forall>v'. r = Result v' \<longrightarrow> P (Result v') t) \<rbrace>"
  shows "(L2_catch f g) \<bullet> s ?\<lbrace>P \<rbrace>"
  unfolding L2_defs
  using assms
  apply runs_to_vcg
  done

lemma (in heap_typing_state) runs_to_partial_L2_catch[unchanged_typing]:
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  assumes [runs_to_vcg]: "\<And>r s. (g r) \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  shows  "(L2_catch f g) \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  by (runs_to_vcg) (auto simp add: unchanged_typing_on_simps)

lemma runs_to_partial_L2_try[runs_to_vcg]:
  assumes [runs_to_vcg]:
    "f \<bullet> s ?\<lbrace> \<lambda>r. Q (unnest_exn r)  \<rbrace>"
  shows "(L2_try f) \<bullet> s ?\<lbrace> Q \<rbrace>"
  unfolding L2_defs
  apply runs_to_vcg
  done


lemma (in heap_typing_state) runs_to_partial_L2_try[unchanged_typing]:
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  shows  "(L2_try f) \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  by (runs_to_vcg)

lemma runs_to_partial_L2_while:
  assumes B: "\<And>r s. I (Result r) s \<Longrightarrow> C r s \<Longrightarrow> (B r) \<bullet> s ?\<lbrace>I\<rbrace>"
  assumes Qr: "\<And>r s. I (Result r) s \<Longrightarrow> \<not> C r s \<Longrightarrow> Q (Result r) s"
  assumes Ql: "\<And>e s. I (Exn e) s \<Longrightarrow> Q (Exn e) s"
  assumes I: "I (Result r) s"
  shows "(L2_while C B r ns) \<bullet> s ?\<lbrace> Q \<rbrace>"
  unfolding L2_defs
  by (rule runs_to_partial_whileLoop_exn [where I=I, OF I Qr Ql B])
 

lemma runs_to_partial_L2_while_same_post:
  assumes B: "\<And>r s. Q (Result r) s \<Longrightarrow> C r s \<Longrightarrow> (B r) \<bullet> s ?\<lbrace>Q\<rbrace>"
  assumes I: "Q (Result r) s"
  shows "(L2_while C B r ns) \<bullet> s ?\<lbrace> Q \<rbrace>"
  using assms
  by - (rule runs_to_partial_L2_while)

lemma (in heap_typing_state) runs_to_partial_L2_while_unchanged_typing[unchanged_typing]:
  assumes B[runs_to_vcg]: "\<And>r s. C r s \<Longrightarrow> (B r) \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  shows "(L2_while C B r ns) \<bullet> s ?\<lbrace>\<lambda>r t. unchanged_typing_on S s t\<rbrace>"
  supply runs_to_partial_L2_while_same_post [runs_to_vcg]
  apply (runs_to_vcg) 
  apply (auto simp add: unchanged_typing_on_simps)
  done

lemma runs_to_partial_L2_throw[runs_to_vcg]:
  assumes "P (Exn e) s"
  shows "(L2_throw e ns) \<bullet> s ?\<lbrace> P \<rbrace>"
  unfolding L2_defs
  using assms
  by (rule runs_to_partial_yield)


lemma runs_to_partial_L2_spec[runs_to_vcg]: "(L2_spec R) \<bullet> s ?\<lbrace>\<lambda>r t. (s, t) \<in> R\<rbrace>"
  unfolding L2_defs 
  by runs_to_vcg

lemma runs_to_partial_state_L2_assume[runs_to_vcg]: 
  "(L2_assume R) \<bullet> s ?\<lbrace>\<lambda>r t. \<exists>x. r = Result x \<and> (x, t) \<in> R s\<rbrace>"
  unfolding L2_defs
  apply (runs_to_vcg)
  done

lemma runs_to_partial_L2_guard[runs_to_vcg]:
  shows "(L2_guard P) \<bullet> s ?\<lbrace> \<lambda>r t. r = Result () \<and> s = t \<and> P s\<rbrace>"
  unfolding L2_defs
  apply (runs_to_vcg)
  done

definition GUARDED_ASSM :: "bool \<Rightarrow> bool" where [remove_ASSMs]: "GUARDED_ASSM P \<longleftrightarrow> P"
lemma GUARDED_ASSM_D: "GUARDED_ASSM P \<Longrightarrow> P" by (simp add: GUARDED_ASSM_def)

lemma runs_to_partial_L2_guarded[runs_to_vcg]:
  "(GUARDED_ASSM (P s) \<Longrightarrow> c \<bullet> s ?\<lbrace>Q\<rbrace>) \<Longrightarrow> (L2_guarded P c) \<bullet> s ?\<lbrace>Q\<rbrace>"
  unfolding L2_guarded_def GUARDED_ASSM_def
  by runs_to_vcg 

lemma runs_to_partial_L2_fail_conv[simp]: "L2_fail \<bullet> s ?\<lbrace> R \<rbrace> \<longleftrightarrow> True"
  by (simp add: L2_fail_def)

lemma runs_to_partial_L2_fail[runs_to_vcg]: "L2_fail \<bullet> s ?\<lbrace> R \<rbrace>"
  by simp

lemma runs_to_partial_L2_call[runs_to_vcg]:
  assumes [runs_to_vcg]: "m \<bullet> s ?\<lbrace> \<lambda>r. Q (case r of Exn e \<Rightarrow> Exn (f e) | Result r \<Rightarrow> Result r) \<rbrace>"
  shows "(L2_call m f ns) \<bullet> s ?\<lbrace> Q \<rbrace>"
  unfolding L2_call_def
  apply runs_to_vcg
  apply (simp add: map_exn_def)
  done

end