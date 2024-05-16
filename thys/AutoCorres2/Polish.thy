(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter "Polishing the Final Outcome"

theory Polish
imports HeapLift WordPolish TypeStrengthen
begin

context heap_typing_state
begin

lemma unchanged_typing_bind[unchanged_typing]: 
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s \<rbrace>"  "(\<And>r s. g r \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s \<rbrace>)" 
  shows "(bind f g) \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s \<rbrace>"
  apply (runs_to_vcg)
  using unchanged_typing_on_trans by blast
  
lemma unchanged_typing_while[unchanged_typing]:
    assumes B: "\<And>r s. C r s \<Longrightarrow> (B r) \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s\<rbrace>"
    shows "(whileLoop C B i) \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s\<rbrace>"
  apply (rule runs_to_partial_whileLoop [where I = "\<lambda>_. unchanged_typing_on S s"])
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal 
    apply (rule runs_to_partial_weaken [OF B])
     apply (simp)
    by (rule unchanged_typing_on_trans)
  done

lemma unchanged_typing_finally[unchanged_typing]: 
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s\<rbrace>"
  shows "finally f \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s\<rbrace>"
  by (runs_to_vcg)

lemma unchanged_typing_try[unchanged_typing]: 
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s\<rbrace>"
  shows "try f \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s\<rbrace>"
  by (runs_to_vcg)

lemma runs_to_partial_catch[unchanged_typing]:
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace>\<lambda>r. unchanged_typing_on S s\<rbrace>"
  assumes [runs_to_vcg]: "\<And>r s. (g r) \<bullet> s ?\<lbrace>\<lambda>r. unchanged_typing_on S s\<rbrace>"
  shows  "(catch f g) \<bullet> s ?\<lbrace>\<lambda>r. unchanged_typing_on S s\<rbrace>"
  by (runs_to_vcg) (auto simp add: unchanged_typing_on_simps)

lemma runs_to_partial_bind_handle[unchanged_typing]:
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace>\<lambda>r. unchanged_typing_on S s\<rbrace>"
  assumes [runs_to_vcg]: "\<And>r s. (g r) \<bullet> s ?\<lbrace>\<lambda>r. unchanged_typing_on S s\<rbrace>"
  assumes [runs_to_vcg]: "\<And>r s. (h r) \<bullet> s ?\<lbrace>\<lambda>r. unchanged_typing_on S s\<rbrace>"
  shows  "(bind_handle f g h) \<bullet> s ?\<lbrace>\<lambda>r. unchanged_typing_on S s\<rbrace>"
  by (runs_to_vcg) (auto simp add: unchanged_typing_on_simps)

lemma unchanged_typing_liftE[unchanged_typing]: 
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s\<rbrace>"
  shows "liftE f \<bullet> s ?\<lbrace> \<lambda>r. unchanged_typing_on S s\<rbrace>"
  by (runs_to_vcg)

end

context open_types_heap_typing_state 
begin


lemma unchanged_typing_ptr_valid_preserved:
  "ptr_valid (heap_typing t1) p \<Longrightarrow> unchanged_typing_on UNIV t1 t2 \<Longrightarrow> ptr_valid (heap_typing t2) p"
  by (simp add: unchanged_typing_on_UNIV_iff)


lemma reaches_unchanged_typing_ptr_valid_preserved:
  "reaches f s r t \<Longrightarrow> ptr_valid (heap_typing s) p \<Longrightarrow> f \<bullet> s ?\<lbrace>\<lambda>_ t. unchanged_typing_on UNIV s t\<rbrace> \<Longrightarrow> 
 ptr_valid (heap_typing t) p"
  using unchanged_typing_ptr_valid_preserved
  by (simp add: runs_to_partial_def_old reaches_succeeds unchanged_typing_on_UNIV_iff)
thm unchanged_typing [no_vars]
end

locale typ_heap_simulation_open_types_stack =
  typ_heap_simulation_open_types \<T> st r w v t_hrs t_hrs_update heap_typing heap_typing_upd
  for
    \<T> and
    st:: "'s \<Rightarrow> 't" and
    r:: "'t \<Rightarrow> ('a::{xmem_type, stack_type}) ptr \<Rightarrow> 'a" and
    w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't" and
    v:: "'t \<Rightarrow> 'a ptr \<Rightarrow> bool" and
    t_hrs :: "'s \<Rightarrow> heap_raw_state" and
    t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" and
    heap_typing :: "'t \<Rightarrow> heap_typ_desc" and
    heap_typing_upd :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 't \<Rightarrow> 't" +
  fixes \<S>:: "addr set" 
begin
  sublocale typ_heap_typing r w heap_typing heap_typing_upd \<S>
    by intro_locales

lemma unchanged_typing_on_with_fresh_stack_ptr[unchanged_typing]: 
  fixes f::"'a ptr \<Rightarrow> ('e::default, 'b, 't) spec_monad"
  assumes [runs_to_vcg]:"\<And>p t. (f p) \<bullet> t ?\<lbrace>\<lambda>_ t'. unchanged_typing_on A t t'\<rbrace>" 
  shows "(with_fresh_stack_ptr n init f) \<bullet> t ?\<lbrace>\<lambda>_ t'. unchanged_typing_on A t t'\<rbrace>"
  unfolding with_fresh_stack_ptr_def on_exit_def stack_ptr_acquire_def assume_stack_alloc_def
  apply runs_to_vcg
  subgoal for x d vs t'
    apply (subst (asm) typing_eq_left_unchanged_typing_on [of _ "(heap_typing_upd (\<lambda>_. d) t)"])
     apply (simp add: heap_typing_fold_upd_write)
    apply (simp add: unchanged_typing_on_def stack_ptr_release_def heap_typing_fold_upd_write stack_allocs_releases_equal_on_typing)
    done
  done

lemma unchanged_typing_on_assume_with_fresh_stack_ptr[unchanged_typing]: 
  fixes f::"'a ptr \<Rightarrow> ('e::default, 'b, 't) spec_monad"
  assumes [runs_to_vcg]:"\<And>p t. (f p) \<bullet> t ?\<lbrace>\<lambda>_ t'. unchanged_typing_on A t t'\<rbrace>" 
  shows "(assume_with_fresh_stack_ptr n init f) \<bullet> t ?\<lbrace>\<lambda>_ t'. unchanged_typing_on A t t'\<rbrace>"
  unfolding assume_with_fresh_stack_ptr_def stack_ptr_acquire_def assume_stack_alloc_def
  apply runs_to_vcg
  subgoal for x d vs t'
    apply (subst (asm) typing_eq_left_unchanged_typing_on [of _ "(heap_typing_upd (\<lambda>_. d) t)"])
     apply (simp add: heap_typing_fold_upd_write)
    apply (simp add: unchanged_typing_on_def stack_ptr_release_def heap_typing_fold_upd_write stack_allocs_releases_equal_on_typing)
    done
  done

lemma unchanged_typing_on_guard_with_fresh_stack_ptr[unchanged_typing]: 
  fixes f::"'a ptr \<Rightarrow> ('e::default, 'b, 't) spec_monad"
  assumes [runs_to_vcg]:"\<And>p t. (f p) \<bullet> t ?\<lbrace>\<lambda>_ t'. unchanged_typing_on A t t'\<rbrace>" 
  shows "(guard_with_fresh_stack_ptr n init f) \<bullet> t ?\<lbrace>\<lambda>_ t'. unchanged_typing_on A t t'\<rbrace>"
  unfolding guard_with_fresh_stack_ptr_def stack_ptr_acquire_def assume_stack_alloc_def
  apply runs_to_vcg
  subgoal for x d vs t'
    apply (subst (asm) typing_eq_left_unchanged_typing_on [of _ "(heap_typing_upd (\<lambda>_. d) t)"])
     apply (simp add: heap_typing_fold_upd_write)
    apply (simp add: unchanged_typing_on_def stack_ptr_release_def heap_typing_fold_upd_write stack_allocs_releases_equal_on_typing)
    done
  done


end

(* Final simplification after type strengthening. *)
named_theorems polish
named_theorems polish_cong

declare map_value_id[polish]

(* Remove the Hoare modifies constants after heap abstraction, as they have
 * very buggy print translations.
 * In particular, applying abs_spec_modify_global replaces the bound variable by "x"
 * and confuses the print translation into producing "may_only_modify_globals [x]". *)
lemmas [polish] = mex_def meq_def

declare WORD_values_fold [polish]
(* Clean up "WORD_MAX TYPE(32)", etc. after word abstraction. *)
lemmas WORD_bound_simps [polish] =
  WORD_MAX_simps
  WORD_MIN_simps
  UWORD_MAX_simps
  WORD_signed_to_unsigned
  INT_MIN_MAX_lemmas

declare singleton_iff [polish]
declare the_Nonlocal.simps [polish]
declare map_exn_id [polish]
declare prod.case [polish]

declare mem_Collect_eq [polish]

lemma L2_VARS_polish [polish]: "L2_VARS x ns = x"
  by (simp add: L2_VARS_def)


lemmas liftE_atomic [polish] =
  liftE_unknown
  liftE_top
  liftE_bot
  liftE_fail
  liftE_yield_Exception
  liftE_return
  liftE_throw_exception_or_result
  liftE_get_state
  liftE_set_state
  liftE_select
  liftE_assert
  liftE_assume
  liftE_gets
  liftE_guard
  liftE_assert_opt
  liftE_gets_the
  liftE_modify

lemma map_value_map_exn_id[simp, polish]: 
  "map_value (map_exn (\<lambda>e'. e')) f = f"
  by (rule spec_monad_ext) (simp add: run_map_value)

lemma gets_to_return [polish]:
  "gets (\<lambda>x. a) = return a"
  by (rule spec_monad_ext) simp

lemma select_UNIV_unknown [polish]: "select UNIV = unknown"
  by (clarsimp simp: unknown_def)

lemma unknown_unit [polish, simp]: "(unknown :: (unit,'s) res_monad) = skip"
  apply (rule spec_monad_ext)
  apply (auto)
  done

lemma condition_to_when [polish]:
  "condition (\<lambda>s. C) A skip = when C A"
  by (simp add: when_def)

lemma condition_to_unless [polish]:
  "condition (\<lambda>s. C) skip A = unless C A"
  apply (simp add: when_def )
  apply (rule condition_swap)
  done

lemma bind_skip [simp, polish]:
  "(x >>= (\<lambda>_. skip)) = x"
  by simp

lemma skip_bind [simp, polish]:
  "(skip >>= P) = (P ())"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind)
  done

lemma catch_skip[simp, polish]: "catch skip f = skip"
  by (rule spec_monad_ext) (simp add: run_catch)

lemma ogets_to_oreturn [polish]: "ogets (\<lambda>s. P) = oreturn P"
  apply (clarsimp simp: ogets_def oreturn_def K_def)
  done

lemma ocondition_ret_ret [polish]:
  "ocondition P (oreturn A) (oreturn B) = ogets (\<lambda>s. if P s then A else B)"
  by (auto simp: ocondition_def ogets_def)

lemma ocondition_gets_ret [polish]:
  "ocondition P (ogets A) (oreturn B) = ogets (\<lambda>s. if P s then A s else B)"
  by (auto simp: ocondition_def ogets_def)

lemma ocondition_ret_gets [polish]:
  "ocondition P (oreturn A) (ogets B) = ogets (\<lambda>s. if P s then A else B s)"
  by (auto simp: ocondition_def ogets_def)

lemma ocondition_gets_gets [polish]:
  "ocondition P (ogets A) (ogets B) = ogets (\<lambda>s. if P s then A s else B s)"
  by (auto simp: ocondition_def ogets_def)

lemma case_prod_trivial[]: "NO_MATCH (g::('e::default, 'a, 's) spec_monad) f \<Longrightarrow>  (\<lambda>(x,y). f) = (\<lambda>_. f)" 
\<comment> \<open>We avoid this rule during polish to keep brittle tuple structure ( \<^const>\<open>case_prod\<close> ) and
     bound variable names in eg. \<^const>\<open>bind\<close>. With the \<^const>\<open>NO_MATCH\<close> setup the 
     simplification might still trigger e.g. on conditions of while loops\<close>
  by auto

(* Avoid things like \<lambda>(x,y,z). f x \<rightarrow> \<lambda>(x, _). f x *)
lemma bind_case_prod_trivial[polish]: "bind f (\<lambda>(x, y). g) = bind f (\<lambda>_. g)"
  by (rule spec_monad_ext) (simp add: run_bind)

lemma condition_to_if [polish]:
  "condition (\<lambda>s. C) (return a) (return b) = return (if C then a else b)"
  by (rule spec_monad_ext) (simp add: run_condition)


lemma guard_merge_bind:
"guard P >>= (\<lambda>_. guard Q >>= M) = guard (P and Q) >>= M"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma guard_merge_bind':
"guard P >>= (\<lambda>_. guard Q >>= M) = guard (\<lambda>s. P s \<and> Q s) >>= M"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma guard_merge:
"guard P >>= (\<lambda>_. guard Q) = guard (P and Q)"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma guard_merge':
"guard P >>= (\<lambda>_. guard Q) = guard (\<lambda>s. P s \<and> Q s)"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma pred_conj_commute: "(P and Q) = (Q and P)"
  by (auto simp add: pred_conj_def)

lemma guard_True_skip[polish, simp]: "guard (\<lambda>_. True) = skip"
  apply (rule spec_monad_ext)
  apply (simp add: run_guard)
  done

lemma guard_True_bind: \<comment> \<open>subsumed by @{thm skip_bind} and @{thm guard_True_skip}\<close>
    "(guard (\<lambda>_. True) >>= M) = M ()"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

declare assert_simps(1) [polish]
declare assume_simps(1) [polish]

lemma simple_bind_fail [simp]:
  "(guard P >>= (\<lambda>_. fail)) = fail"
  "(modify f >>= (\<lambda>_. fail)) = fail"
  "(return x >>= (\<lambda>_. fail)) = fail"
  "(gets f >>= (\<lambda>_. fail)) = fail"
     apply (rule spec_monad_ext, simp add: run_bind run_guard)+
  done

declare condition_fail_rhs [polish]
declare condition_fail_lhs [polish]
declare simple_bind_fail [polish]
declare condition_bind_fail [polish]


lemma whileLoop_fail:
    "(whileLoop C (\<lambda>_. fail) i) = (guard (\<lambda>s. \<not> C i s) >>= (\<lambda>_. return i))"
  apply (subst whileLoop_unroll)
  apply (rule spec_monad_ext)
  apply (simp add: run_condition run_bind run_guard)
  done

lemma owhile_fail:
    "(owhile C (\<lambda>_. ofail) i) = (oguard (\<lambda>s. \<not> C i s) |>> (\<lambda>_. oreturn i))"
  apply (rule ext)
  apply (subst owhile_unroll)
  apply (clarsimp simp: obind_def oguard_def ocondition_def split: option.splits)
  done

declare whileLoop_fail [polish]
declare owhile_fail [polish]

lemma oguard_True [simp, polish]: "oguard (\<lambda>_. True) = oreturn ()"
  by (clarsimp simp: oreturn_def oguard_def K_def)

lemma oguard_False [simp, polish]: "oguard (\<lambda>_. False) = ofail"
  by (clarsimp simp: ofail_def oguard_def K_def)

declare oreturn_bind [polish]
declare obind_return [polish]
lemma infinite_option_while': "(Some x, Some y) \<notin> option_while' (\<lambda>_. True) B"
  apply (rule notI)
  apply (induct "Some x :: 'a option" "Some y :: 'a option"
      arbitrary: x y rule: option_while'.induct)
  apply auto
  done


lemma expand_guard_conj [polish]:
  "guard (\<lambda>s. A s \<and> B s) = (do {guard (\<lambda>s. A s); guard (\<lambda>s. B s) })"
  apply (rule spec_monad_ext)
  apply (simp add: run_guard run_bind)
  done


lemma oguard_K_bind_cong [polish_cong]: "g = g' \<Longrightarrow> (\<And>s. g' s \<Longrightarrow> c s = c' s) 
  \<Longrightarrow> (oguard g >>= (\<lambda>_. c)) = (oguard g' >>= (\<lambda>_. c')) "
  apply (rule ext)
  apply (auto simp add: oguard_def obind_def)
  done

lemma oguard_obind_cong: "g = g' \<Longrightarrow> (\<And>s. g' s \<Longrightarrow> c s = c' s) \<Longrightarrow> 
  do {_ <- oguard g ; c} = do {_ <- oguard g';  c'}"
  by (auto simp add: oguard_def obind_def)

lemma guard_bind_cong:
  "g = g' \<Longrightarrow> (\<And>s. g' s \<Longrightarrow> run c s = run c' s) \<Longrightarrow> 
    do {_ <- guard g;
       c
    } =
    do {_ <- guard g';
       c'
    }"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma modify_guard_swap:
"(\<And>s. P (f s) = P s) \<Longrightarrow>
  do { 
    _ <- modify f;
    guard P 
  } = 
  do { 
    _ <- guard P;
    modify f
  }"
 apply (rule spec_monad_ext)
 apply (simp add: run_bind run_guard)
 done

lemma modify_guard_bind_swap:
"(\<And>s. P (f s) = P s) \<Longrightarrow>
  do { 
    _ <- modify f;
    _ <- guard P;
    X
  } = 
  do { 
    _ <- guard P;
    _ <- modify f;
    X
  }"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done



lemma when_throw_cong: "P = P' \<Longrightarrow> (\<And>s. P' \<Longrightarrow> run Y s = run Y' s) \<Longrightarrow> 
  do { _ <- when (\<not> P) (throw x); Y  } =
  do {_ <- when (\<not> P') (throw x); Y' }"
  apply (rule spec_monad_ext)
  apply (auto simp add: run_bind run_when)
  done

lemma condition_throw:
  "condition (\<lambda>s. P) (throw e) B = do { when P (throw e); B }"
  apply (auto simp add: spec_monad_eq_iff runs_to_iff Exn_def default_option_def)
  done

lemma map_value_map_lift_result_bind[simp]: 
  "map_value (map_exception_or_result (\<lambda>x::unit. undefined) f) (bind m g) = 
   bind m (\<lambda>x. map_value (map_exception_or_result (\<lambda>x. undefined) f) (g x))"
  by (simp add: spec_monad_eq_iff runs_to_iff)

lemma map_value_map_result_bind[simp]: 
  "map_value (map_exception_or_result id f) (bind m g) = 
   bind m (\<lambda>x. map_value (map_exception_or_result id f) (g x))"
  apply (auto simp add: spec_monad_eq_iff runs_to_iff)
  done

lemma map_value_yield[simp]: "map_value f (yield x) = yield (f x)"
  apply (rule spec_monad_ext)
  apply (simp add: run_map_value)
  done

lemma map_result_return[simp]: "map_value (map_exception_or_result id f) (return x) = return (f x)"
  apply (rule spec_monad_ext)
  apply (simp add: run_map_value)
  done

lemma map_result_throw[simp]: "map_value (map_exception_or_result id f) (throw x) = throw x"
  apply (rule spec_monad_ext)
  apply (simp add: run_map_value)
  done

lemma map_value_compose[simp]: "map_value f (map_value g m) = (map_value (f \<circ> g) m)"
  apply (auto simp add: runs_to_iff spec_monad_eq_iff)
  done

lemma map_result_compose[simp]:
  "map_exception_or_result id f o map_exception_or_result id g = map_exception_or_result id (f o g)"
  by (simp add: map_exception_or_result_comp fun_eq_iff)

lemma map_value_condition: 
  "map_value f (condition c g h) = condition c (map_value f g) (map_value f h)"
  apply (auto simp add: runs_to_iff spec_monad_eq_iff)
  done

lemma oguard_True_K_bind [polish]: "(oguard (\<lambda>_. True) >>= (\<lambda>_. c)) = c"
  apply (rule ext)
  apply (auto simp add: oguard_def obind_def)
  done

lemma oguard_False_bind [polish]: "(oguard (\<lambda>_. False) >>= c) = ofail"
  apply (rule ext)
  apply (auto simp add: oguard_def obind_def)
  done

lemma guard_False_bind [polish]: "(guard (\<lambda>_. False) >>= c) = fail"
  apply (rule spec_monad_ext)
  apply (simp add: run_guard run_bind)
  done

lemma expand_oguard_conj [polish]:
  "oguard (\<lambda>s. A s \<and> B s) = (obind (oguard (\<lambda>s. A s)) (\<lambda>_. oguard (\<lambda>s. B s)) )"
  by (rule ext) (clarsimp simp: oguard_def obind_def split: option.splits)

lemma owhile_infinite_loop [simp, polish]:
    "owhile (\<lambda>r s. C) B x = (oguard (\<lambda>s. \<not> C) |>> (\<lambda>_. oreturn x))"
  apply (cases C)
   apply (rule ext)
   apply (clarsimp simp: owhile_def option_while_def obind_def split: option.splits)
   apply (metis infinite_option_while' None_not_eq option_while'_THE)
  apply (subst owhile_unroll)
  apply (clarsimp simp: obind_def oreturn_def K_def split: option.splits)
  done

declare obind_return [polish]
declare bind_return [polish]

lemma fail_bind [simp]:
  "fail >>= f = fail"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind)
  done

declare fail_bind [polish]

declare ofail_bind [polish]
declare obind_fail [polish]

declare singleton_iff [polish]
declare when_True [polish]
declare when_False [polish]

lemma let_triv [polish]: "(let x = y in x) = y"
  apply (clarsimp simp: Let_def)
  done

lemma ucast_scast_same [polish, L2opt, simp]:
    "ucast ((scast x :: ('a::len) word)) = (x :: 'a word)"
  apply (clarsimp simp: ucast_def scast_def)
  done

lemma word_of_int_of_nat [polish, L2opt, simp]:
    "word_of_int (int x) = of_nat x"
  by (rule of_int_of_nat_eq)

(* Optimising "if" constructs. *)

lemma return_if_P_1_0_bind [polish]:
    "(return (if P then 1 else 0) >>= (\<lambda>x. Q x))
        = (return P >>= (\<lambda>x. Q (if x then 1 else 0)))"
  apply simp
  done


lemma gets_if_P_1_0_bind [polish]:
    "(gets (\<lambda>s. if P s then 1 else 0) >>= (\<lambda>x. Q x))
        = (gets P >>= (\<lambda>x. Q (if x then 1 else 0)))"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind)
  done

lemma if_P_1_0_neq_0 [polish, simp]:
    "((if P then 1 else (0::('a::{zero_neq_one}))) \<noteq> 0) = P"
  apply simp
  done

lemma if_P_1_0_eq_0 [polish, simp]:
    "((if P then 1 else (0::('a::{zero_neq_one}))) = 0) = (\<not> P)"
  apply simp
  done

lemma if_if_same_output [polish]:
  "(if a then if b then x else y else y) = (if a \<and> b then x else y)"
  "(if a then x else if b then x else y) = (if a \<or> b then x else y)"
  by auto

(* C-parser turns a C expression into a chain of guarded statements
   if some of the subexpressions can fail. This gets annoying when
   the expression was being used as a condition.

   Here we try to rewrite the statements to one big guard followed by
   the actual expression.
   TODO: this should be in L2Opt or something *)
lemma collect_guarded_conj[polish]:
  "condition C1 (do { guard G; gets (\<lambda>s. if C2 s then 1 else 0) })
                (return 0)
    = do { guard (\<lambda>s. C1 s \<longrightarrow> G s);
         gets (\<lambda>s. if C1 s \<and> C2 s then 1 else 0) }"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard run_condition)
  done


lemma collect_guarded_disj[polish]:
  "condition C1 (return 1)
                (do {guard G; gets (\<lambda>s. if C2 s then 1 else 0) })
    = do {guard (\<lambda>s. \<not> C1 s \<longrightarrow> G s);
         gets (\<lambda>s. if C1 s \<or> C2 s then 1 else 0) }"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard run_condition)
  done

(* Need this to merge the new statements into the program *)
lemmas [polish] = bind_assoc obind_assoc



(* Need this because collect_guarded_disj generates nots *)
declare not_not [polish]

(* Normally the boolean result from above is used in a condition,
   simplify that as well. *)
lemma collect_then_cond_1_0[polish]:
   "do {cond \<leftarrow> gets (\<lambda>s. if P s then (1::('a::{zero_neq_one})) else 0);
       condition (\<lambda>_. cond \<noteq> 0) L R }
    = condition P L R"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard run_condition)
  done

lemma collect_then_cond_1_0_assoc[polish]:
   "(do {cond \<leftarrow> gets (\<lambda>s. if P s then (1::('a::{zero_neq_one})) else 0);
        condition (\<lambda>_. cond \<noteq> 0) L R
        >>= f })
    = (condition P L R >>= f)"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard run_condition)
  done

lemma bind_return_bind [polish]:
    "(A >>= (\<lambda>x. (return x >>= (\<lambda>y. B x y)))) = (A >>= (\<lambda>x. B x x))"
  by simp


lemma obind_oreturn_obind [polish]:
    "(A |>> (\<lambda>x. (oreturn x |>> (\<lambda>y. B x y)))) = (A |>> (\<lambda>x. B x x))"
  by simp

declare obind_assoc [polish]

declare if_distrib [where f=scast, polish, simp]
declare if_distrib [where f=ucast, polish, simp]
declare if_distrib [where f=unat, polish, simp]
declare if_distrib [where f=uint, polish, simp]
declare if_distrib [where f=sint, polish, simp]

declare cast_simps [polish]

lemma Suc_0_eq_1 [polish]: "Suc 0 = 1"
  by simp

(*
 * Return / case_prod combinations.
 *
 * These can probably be improved to avoid duplication.
 *)

lemma bind_return_case_prod [polish, simp]:
  "(do {() \<leftarrow> A0; return () }) = A0"
  "(do {(a) \<leftarrow> A1; return (a) }) = A1"
  "(do {(a, b) \<leftarrow> A2; return (a, b) }) = A2"
  "(do {(a, b, c) \<leftarrow> A3; return (a, b, c) }) = A3"
  "(do {(a, b, c, d) \<leftarrow> A4; return (a, b, c, d) }) = A4"
  "(do {(a, b, c, d, e) \<leftarrow> A5; return (a, b, c, d, e) }) = A5"
  "(do {(a, b, c, d, e, f) \<leftarrow> A6; return (a, b, c, d, e, f) }) = A6"
  by (auto simp: split_beta'  case_unit_Unity[abs_def])

lemma bind_return_case_prod' [polish, simp]:
  "(A1 \<bind> return \<bind> g1) = (A1 \<bind> g1)"
  "(A2 \<bind> (\<lambda>(a, b). (return (a, b) \<bind> g2))) = (A2 \<bind> g2)"
  "(A3 \<bind> (\<lambda>(a, b, c). (return (a, b, c) \<bind> g3))) = (A3 \<bind> g3)"
  "(A4 \<bind> (\<lambda>(a, b, c, d). (return (a, b, c, d) \<bind> g4))) = (A4 \<bind> g4)"
  "(A5 \<bind> (\<lambda>(a, b, c, d, e). (return (a, b, c, d, e) \<bind> g5))) = (A5 \<bind> g5)"
  "(A6 \<bind> (\<lambda>(a, b, c, d, e, f). (return (a, b, c, d, e, f) \<bind> g6))) = (A6 \<bind> g6)"
  by (auto simp: split_beta' case_unit_Unity[abs_def])

lemma obind_returnOk_prodE_case [polish, simp]:
  "(A1 |>> (\<lambda>a. oreturn (a))) = A1"
  "(A2 |>> (\<lambda>(a, b). oreturn (a, b))) = A2"
  "(A3 |>> (\<lambda>(a, b, c). oreturn (a, b, c))) = A3"
  "(A4 |>> (\<lambda>(a, b, c, d). oreturn (a, b, c, d))) = A4"
  "(A5 |>> (\<lambda>(a, b, c, d, e). oreturn (a, b, c, d, e))) = A5"
  "(A6 |>> (\<lambda>(a, b, c, d, e, f). oreturn (a, b, c, d, e, f))) = A6"
  by auto

lemma obind_returnOk_prodE_case' [polish, simp]:
  "(A1 |>> (\<lambda>a. (oreturn (a) |>> g1))) = A1 |>> g1"
  "(A2 |>> (\<lambda>(a, b). (oreturn (a, b) |>> g2))) = A2 |>> g2"
  "(A3 |>> (\<lambda>(a, b, c). (oreturn (a, b, c) |>> g3))) = A3 |>> g3"
  "(A4 |>> (\<lambda>(a, b, c, d). (oreturn (a, b, c, d) |>> g4))) = A4 |>> g4"
  "(A5 |>> (\<lambda>(a, b, c, d, e). (oreturn (a, b, c, d, e) |>> g5))) = A5 |>> g5"
  "(A6 |>> (\<lambda>(a, b, c, d, e, f). (oreturn (a, b, c, d, e, f) |>> g6))) = A6 |>> g6"
  by auto

lemma bind_fixup_1:
  "(bind A (\<lambda>x. case y of (a, b) \<Rightarrow> B a b x)) =
           (case y of (a, b) \<Rightarrow> bind A (\<lambda>x. B a b x))"
       by (auto simp: split_def)
lemma bind_fixup_2:
  "(bind (case y of (a, b) \<Rightarrow> B a b) A) =
           (case y of (a, b) \<Rightarrow> bind (B a b) A)"
  by (auto simp: split_def)
lemma finally_fixup: "(\<lambda>x. finally (case x of (a, b) \<Rightarrow> f a b)) = (\<lambda>(a,b). finally (f a b))"
  by (simp add: fun_eq_iff split: prod.splits)
lemma try_fixup: "(\<lambda>x. try (case x of (a, b) \<Rightarrow> f a b)) = (\<lambda>(a,b). try (f a b))"
  by (simp add: fun_eq_iff split: prod.splits)
lemma liftE_fixup: "(\<lambda>x. liftE (case x of (a, b) \<Rightarrow> f a b)) = (\<lambda>(a,b). liftE (f a b))"
  by (simp add: fun_eq_iff split: prod.splits)



lemmas spec_monad_split_fixup [polish]= \<comment> \<open>should we even take more from @{thm L2_split_fixups} ?\<close>
  bind_fixup_1 
  bind_fixup_2 
  finally_fixup
  try_fixup
  liftE_fixup

(* Word simplifications *)

lemma scast_1_simps [simp, L2opt, polish]:
  "scast (1 :: ('a::len) bit1 word) = 1"
  "scast (1 :: ('a::len) bit0 word) = 1"
  "scast (1 :: ('a::len) bit1 signed word) = 1"
  "scast (1 :: ('a::len) bit0 signed word) = 1"
  by auto

lemma scast_1_simps_direct [simp, L2opt, polish]:
   "scast (1 :: sword64) = (1 :: word64)"
   "scast (1 :: sword64) = (1 :: word32)"
   "scast (1 :: sword64) = (1 :: word16)"
   "scast (1 :: sword64) = (1 :: word8)"
   "scast (1 :: sword32) = (1 :: word32)"
   "scast (1 :: sword32) = (1 :: word16)"
   "scast (1 :: sword32) = (1 :: word8)"
   "scast (1 :: sword16) = (1 :: word16)"
   "scast (1 :: sword16) = (1 :: word8)"
   "scast (1 :: sword8) = (1 :: word8)"
  by auto

declare scast_0 [L2opt, polish]

declare Word.sint_0 [polish]
declare More_Word.sint_0 [polish]

lemma sint_1_eq_1_x [polish, simp]:
    "sint (1 :: (('a::len) bit0) word) = 1"
    "sint (1 :: (('a::len) bit1) word) = 1"
    "sint (1 :: (('a::len) bit0) signed word) = 1"
    "sint (1 :: (('a::len) bit1) signed word) = 1"
  by auto

lemma if_P_then_t_else_f_eq_t [L2opt, polish]:
    "((if P then t else f) = t) = (P \<or> t = f)"
  by auto

lemma if_P_then_t_else_f_eq_f [L2opt, polish]:
    "((if P then t else f) = f) = (\<not> P \<or> t = f)"
  by auto

lemma sint_1_ne_sint_0: "sint 1 \<noteq> sint 0"
  by simp

lemmas if_P_then_t_else_f_eq_f_simps [L2opt, polish] =
  if_P_then_t_else_f_eq_f [where t = "sint 1" and f = "sint 0", simplified sint_1_ne_sint_0 simp_thms]
  if_P_then_t_else_f_eq_t [where t = "sint 1" and f = "sint 0", simplified sint_1_ne_sint_0 simp_thms]
  if_P_then_t_else_f_eq_f [where t = "1 :: int" and f = "0 :: int", simplified zero_neq_one_class.one_neq_zero simp_thms]
  if_P_then_t_else_f_eq_t [where t = "1 :: int" and f = "0 :: int", simplified zero_neq_one_class.one_neq_zero simp_thms]

lemma boring_bind_K_bind [simp, polish]:
    "(gets X >>= (\<lambda>_. M)) = M"
    "(return Y >>= (\<lambda>_. M)) = M"
   apply (rule spec_monad_ext, simp add: run_bind)+
  done


(* Misc *)

lemma pred_and_true_var[simp]: "((\<lambda>_. True) and P) = P"
  by(simp add:pred_conj_def)
lemma pred_and_true[simp]: "(P and (\<lambda>_. True)) = P"
  by(simp add:pred_conj_def)

declare pred_and_true_var [L2opt, polish]
declare pred_and_true [L2opt, polish]

lemmas [polish] = rel_simps eq_numeral_extra

declare ptr_add_0_id[polish]
declare ptr_coerce.simps[polish]

(* simplify constructs like "p +\<^sub>p int (unat k)" to "p +\<^sub>p uint k",
 * generated by unsigned word abstraction *)
declare uint_nat[symmetric, polish]


lemma finally_throw: "finally (throw x) = return x"
  apply (rule spec_monad_ext)
  apply (simp add: run_finally)
  done

lemma finally_liftE: "finally (liftE m) = m"
  apply (auto simp add: runs_to_iff spec_monad_eq_iff intro!: runs_to_cong_pred_only)
  done


lemma bind_post_state_map_post_state:
  "bind_post_state (map_post_state f g) h = bind_post_state g (\<lambda>x. h (f x))"
  by (simp flip: bind_post_state_pure_post_state2)

lemma map_post_state_case_exception_or_result_distrib: 
  "map_post_state f (case_exception_or_result g h v) = 
  (case_exception_or_result (\<lambda>x. map_post_state f (g x)) (\<lambda>x. map_post_state f (h x)) v)"
  by (auto simp add: map_post_state_def split: exception_or_result_splits)

lemma map_post_state_case_exception_or_result_prod_distrib:
 "map_post_state f 
          ((case v of (Exception e, t) \<Rightarrow> g e t
            | (Result v, t) \<Rightarrow> h v t)) =  
          ((case v of (Exception e, t) \<Rightarrow> map_post_state f (g e t)
            | (Result v, t) \<Rightarrow> map_post_state f (h v t)))"
  by (auto simp add: map_post_state_def split: prod.splits exception_or_result_splits)

lemma finally_liftE_bind: "(finally ((liftE L) >>= (\<lambda>r. R r))) = (L >>= (\<lambda>r. (finally (R r))))" 
  by (auto simp add: spec_monad_eq_iff runs_to_iff intro!: runs_to_cong_pred_only)

lemma finally_guardE: "finally (do { r <- guard X; Y }) = do {r <- guard X; finally Y }"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_finally run_guard)
  done

lemma finally_condition_distrib: "finally (condition c X Y) = condition c (finally X) (finally Y)"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_finally run_liftE run_guard run_condition map_post_state_bind_post_state)
  done


lemma unite_Exception_option:
  "unite (Exception (v::'a option)) = Result (the v)"
  apply (cases v)
   apply (simp add: unite_def case_xval_def default_option_def option.the_def)
  by (metis Exn_def option.sel unite_simps(1))


lemma finally_bindE_liftE_throw: "finally (X >>= (\<lambda>v. L2_VARS (throw v) ns)) = finally X"
  by (auto simp add: spec_monad_eq_iff runs_to_iff L2_VARS_def intro!: runs_to_cong_cases)


lemmas finally_simps = 
 finally_throw finally_liftE
 finally_liftE_bind
 finally_guardE
 finally_condition_distrib
 condition_fail_rhs condition_fail_lhs 

 bind_assoc 

thm finally_simps
declare finally_simps [polish]

declare finally_bindE_liftE_throw [simplified L2_VARS_def, polish]

lemma nested_bind[polish, simp]: 
  "do { y <- f;
      return (g y)
   } >>= h =
   do { y <- f;
      h (g y)
   } "
  apply (auto simp add: spec_monad_eq_iff runs_to_iff)
  done

lemma select_UNIV_bind_const[simp]: "select UNIV >>= (\<lambda>_. g) = g"
  apply (auto simp add: spec_monad_eq_iff runs_to_iff)
  done

lemma do_bind_assoc:
  "\<And>f fa fb. do { u <- f::(unit, _) res_monad; 
              fa::(unit, _) res_monad } >>= fb = do {u <- f; fa >>= 
              fb::(unit, _) res_monad }"
  using bind_assoc by blast


section "Support to normalise guards and array index expressions"

method simp_guards =
  (simp
    add:
      guard_merge' guard_merge_bind' conj_commute
      array_ptr_index_field_lvalue_conv
      addressable_field_exec find_array_fields_Some
      unat_less_helper
    cong:
      HOL.conj_cong)

simproc_setup field_lvalue_unfold (\<open>&(p::'a::mem_type ptr\<rightarrow>f#g#gs)\<close>) = \<open>
let
  fun check @{term_pat \<open>&(_\<rightarrow>?fs)\<close>} = is_some (try UMM_Proofs.dest_fields fs) orelse raise Pattern.MATCH
    | check _ = raise Pattern.MATCH
in
  fn _ => fn ctxt => fn ct =>
  let
    val _ = check (Thm.term_of ct)
    val {p, f, g, ...} = @{cterm_match \<open>&(?p\<rightarrow>?f#?g)\<close>} ct
    val thm0 = Drule.infer_instantiate ctxt [(("p", 0), p), (("f", 0), f), (("g", 0), g)]
          @{thm field_lvalue_cons_unfold}
    val thm1 = Utils.solve_sideconditions ctxt thm0 (
          ALLGOALS (asm_full_simp_tac ctxt))
    val _ = Utils.verbose_msg 6 ctxt (fn _ => "field_lvalue_unfold:\n " ^ Thm.string_of_thm ctxt thm1)
  in
    SOME thm1
  end
  handle THM _ => 
          (Utils.verbose_msg 6 ctxt (fn _ => "field_lvalue_unfold proof failed:\n " ^ string_of_cterm ctxt ct); 
          NONE)
       | Pattern.MATCH => NONE
end\<close>
declare [[simproc del: field_lvalue_unfold]] \<comment> \<open>loops with @{thm field_lvalue_append}\<close>

attribute_setup array_bound_mksimps = \<open>
  Scan.succeed (Thm.declaration_attribute 
    (fn _ => (Context.map_proof (UMM_Proofs.set_array_bound_mksimps))))\<close>



lemmas whileLoop_congs_tupled =
whileLoop_cong
whileLoop_cong [split_tuple C and C' and B and B' arity: 2]
whileLoop_cong [split_tuple C and C' and B and B' arity: 3]
whileLoop_cong [split_tuple C and C' and B and B' arity: 4]
whileLoop_cong [split_tuple C and C' and B and B' arity: 5]
whileLoop_cong [split_tuple C and C' and B and B' arity: 6]
whileLoop_cong [split_tuple C and C' and B and B' arity: 7]
whileLoop_cong [split_tuple C and C' and B and B' arity: 8]
whileLoop_cong [split_tuple C and C' and B and B' arity: 9]
whileLoop_cong [split_tuple C and C' and B and B' arity: 10]
whileLoop_cong [split_tuple C and C' and B and B' arity: 11]
whileLoop_cong [split_tuple C and C' and B and B' arity: 12]
whileLoop_cong [split_tuple C and C' and B and B' arity: 13]

lemma finally_condition_throw_conv: "finally (condition c (throw x) g) = condition c (return x) (finally g)"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_unless_throw_conv: "finally (do {unless c (throw x); g}) = condition (\<lambda>_. \<not> c) (return x) (finally g)"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_condition_throw_conv: "finally (do {condition c (throw x) skip; h}) = condition c (return x) (finally h) "
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_return_conv: "finally (return x) = return x"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_guard_conv: "finally (do {guard g; f}) = do {guard g; finally f}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_modify_conv: "finally (do {modify g; f}) = do {modify g; finally f}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_gets_conv: "finally ((gets g) \<bind> f) = do {r \<leftarrow> gets g;  finally (f r)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_gets_the_conv: "finally (gets_the g \<bind> f) = do {r \<leftarrow> gets_the g;  finally (f r)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_unknown_conv: "finally (unknown \<bind> f) = do {r \<leftarrow> unknown;  finally (f r)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_get_state_conv: "finally (get_state \<bind> f) = do {r \<leftarrow> get_state;  finally (f r)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_set_state_conv: "finally (set_state s \<bind> f) = do {r \<leftarrow> set_state s;  finally (f r)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_select_conv: "finally (select S \<bind> f) = do {r \<leftarrow> select S;  finally (f r)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_assert_conv: "finally (assert P \<bind> f) = do {r \<leftarrow> assert P;  finally (f r)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_assume_conv: "finally (assume P \<bind> f) = do {r \<leftarrow> assume P;  finally (f r)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma finally_bind_assert_opt_conv: "finally (assert_opt v \<bind> f) = do {r \<leftarrow> assert_opt v;  finally (f r)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemmas finally_convs =
  finally_liftE finally_liftE_bind
  finally_condition_throw_conv 
  finally_unless_throw_conv 
  finally_bind_condition_throw_conv
  finally_return_conv
  finally_bind_guard_conv
  finally_bind_modify_conv
  finally_bind_gets_conv
  finally_bind_gets_the_conv
  finally_bind_unknown_conv
  finally_bind_get_state_conv
  finally_bind_set_state_conv
  finally_bind_select_conv
  finally_bind_assert_conv
  finally_bind_assume_conv
  finally_bind_assert_opt_conv
  finally_throw

lemma try_bind_liftE_conv: "(try (liftE f \<bind> g)) = (liftE f \<bind> (\<lambda>x. try (g x)))"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma try_bind_guard_conv: "try (do {guard g; f}) = do {guard g; try f}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma try_unless_throw_Inr_conv: 
  "try (do {unless c (throw (Inr x)); g}) = condition (\<lambda>_. \<not> c) (return x) (try g)"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff unnest_exn_def)
  done

lemma try_unless_throw_Inl_conv: 
  "try (do {unless c (throw (Inl x)); g}) = condition (\<lambda>_. \<not> c) (throw x) (try g)"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff unnest_exn_def)
  done

lemma try_when_throw_Inr_conv: 
  "try (do {when c (throw (Inr x)); g}) = condition (\<lambda>_. c) (return x) (try g)"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff unnest_exn_def)
  done

lemma try_when_throw_Inl_conv: 
  "try (do {when c (throw (Inl x)); g}) = condition (\<lambda>_. c) (throw x) (try g)"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff unnest_exn_def)
  done



lemma try_bind_condition_throw_Inr_conv: "try (do {condition c (throw (Inr x)) skip; h}) = condition c (return x) (try h) "
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff unnest_exn_def)
  done

lemma try_bind_condition_throw_Inl_conv: "try (do {condition c (throw (Inl x)) skip; h}) = condition c (throw x) (try h) "
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff unnest_exn_def)
  done

lemma try_condition_conv: "try (condition c f g) = condition c (try f) (try g)"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemmas try_convs =
  try_bind_liftE_conv
  try_bind_guard_conv
  try_unless_throw_Inr_conv
  try_unless_throw_Inl_conv
  try_when_throw_Inr_conv
  try_when_throw_Inl_conv
  try_bind_condition_throw_Inr_conv
  try_bind_condition_throw_Inl_conv
  try_condition_conv

lemma runs_to_partial_case_prod : "(\<And>a b. (f a b) \<bullet> s ?\<lbrace>Q\<rbrace> ) \<Longrightarrow> 
  (case x of (a, b) \<Rightarrow> f a b) \<bullet> s ?\<lbrace>Q\<rbrace>"
  by (cases x) simp

section "Monad simplification with custom congruence rules"

context open_types
begin
text \<open>We supply a custom simplification method for spec monad expressions that gathers and propagates
information from conditions and guards while descending into the term. The core motivation is
to clean up repeated occurrences of @{term "ptr_valid (heap_typing s) p"}. Allthough this is a
state dependent predicate it stays invariant as long as the typing does not change. So the goal
of the simplification method is to prove preservation of such predicates while descending into
the term. Supplying congruence rules to the simplifier is unfortunately not enough as we want to
keep control over what kind of invariants are propagated. Unfortunately the simplifier has no
concept of a \<open>congprocs\<close> that are triggered when descending into the term only the \<open>simprocs\<close> which are
triggered by the usual bottom up simplifier strategy. 
To work around this limitation we implement \<open>congprocs\<close> by \<open>simprocs\<close>:
\<^item> We block the simplifier to descend into compound terms by adding trivial congruence rules to the
  simplifier, like @{prop "bind f g \<equiv> bind f g"}
\<^item> We add a simproc that then triggers on the @{term "bind f g"} and manually extends the context
and invokes the simplifier on the subterms.
\<close>
end

definition ADD_FACT:: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "ADD_FACT P s = P s"
definition PRESERVED_FACTS:: "('e::default, 'a, 's) spec_monad \<Rightarrow> 's \<Rightarrow> ('e, 'a) exception_or_result \<Rightarrow> 's \<Rightarrow> bool " where
  "PRESERVED_FACTS f s r t = (reaches f s r t)"
definition  PRESERVED_FACTS_WHILE :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('e::default, 'a, 's) spec_monad) \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" where
  "PRESERVED_FACTS_WHILE C B i s r t = whileLoop_unroll_reachable C B i s r t"

definition RUN_CASE_PROD ::
    "('a \<Rightarrow> 'b \<Rightarrow> ('c::default, 'd, 'e) spec_monad) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'e \<Rightarrow> 
     ('f \<Rightarrow> 'g \<Rightarrow> ('c, 'd, 'e) spec_monad) \<Rightarrow> 'f \<times> 'g \<Rightarrow> bool" where 
    "RUN_CASE_PROD f x s f' x' \<longleftrightarrow> run (case_prod f x) s = run (case_prod f' x') s"


lemma ADD_FACT_D: "ADD_FACT P s \<Longrightarrow> P s"
  by (simp add: ADD_FACT_def)

lemma RUN_CASE_PROD_I:"x \<equiv> x' \<Longrightarrow> run (case_prod f x') s \<equiv> run (case_prod f' x') s \<Longrightarrow> RUN_CASE_PROD f x s f' x'"
  by (auto simp add: RUN_CASE_PROD_def)

named_theorems 
  monad_simp_simp "simplification rules to derive facts" and 
  monad_simp_split_tuple_cong "congruence rules to control tuple expansion"


lemma PRESERVED_FACTS_runs_to_partial: "PRESERVED_FACTS f s r t \<Longrightarrow> f \<bullet> s ?\<lbrace>Q\<rbrace> \<Longrightarrow> Q r t"
  by (auto simp add: runs_to_partial_def_old PRESERVED_FACTS_def reaches_succeeds)


lemma STOPI: "x \<equiv> y \<Longrightarrow> x \<equiv> STOP y" by (simp add: STOP_def)

lemma eq_TrueD: "P \<equiv> True \<Longrightarrow> P"
  by blast
lemma eq_FalseD: "P \<equiv> False \<Longrightarrow> \<not> P"
  by blast


lemma expand_unused_case_prod: 
  "(\<lambda>(x,y::('c * 'd)). f x) = (\<lambda>(x, y1, y2). f x)"
  by auto


ML \<open>

structure Monad_Cong_Simp =
struct
type rule = {apply_thm: thm, stop_thm: thm, split_vars: string list, name: binding}
type rules = rule Net.net

type cond_rule = {thm: thm, name: binding}
type cond_rules = cond_rule Net.net


fun rule_eq ({apply_thm = thm1, ...}:rule, {apply_thm = thm2, ...}:rule) = Thm.eq_thm_prop (thm1, thm2)
fun cond_rule_eq ({thm = thm1, ...}:cond_rule, {thm = thm2, ...}:cond_rule) = Thm.eq_thm_prop (thm1, thm2)

fun transfer_rule ctxt {apply_thm, stop_thm, split_vars, name}:rule =
  {apply_thm = Thm.transfer' ctxt apply_thm,
   stop_thm = Thm.transfer' ctxt stop_thm,
   split_vars = split_vars, name = name}

fun merge_rules (n1, n2) =
  if pointer_eq (n1, n2) then n1
  else if Net.is_empty n2 then n1
  else if Net.is_empty n1 then n2
  else Net.merge rule_eq (n1, n2)

fun merge_cond_rules (n1, n2) =
  if pointer_eq (n1, n2) then n1
  else if Net.is_empty n2 then n1
  else if Net.is_empty n1 then n2
  else Net.merge cond_rule_eq (n1, n2)

type monad_cong_data = {rules: rules, derive_rules: cond_rules, 
  stop_congs: thm list, simprocs: string list}

structure Data = Generic_Data (
  type T = monad_cong_data;
  val empty = {rules = Net.empty, derive_rules = Net.empty, stop_congs = [], simprocs = []}
  fun merge ({rules = rules1, derive_rules = d1, stop_congs = congs1, simprocs = simprocs1}, 
             {rules = rules2, derive_rules = d2, stop_congs = congs2, simprocs = simprocs2}) =
       {rules = merge_rules (rules1, rules2), derive_rules = merge_cond_rules (d1, d2),
        stop_congs = Library.merge (Thm.eq_thm_prop) (congs1, congs2),
        simprocs = Ord_List.merge fast_string_ord (simprocs1, simprocs2)}
)

fun map_rules f = Data.map (fn {rules, derive_rules, stop_congs, simprocs}:monad_cong_data => 
  {rules = f rules, derive_rules = derive_rules, stop_congs = stop_congs, simprocs = simprocs})
fun map_derive_rules f = Data.map (fn {rules, derive_rules, stop_congs, simprocs}:monad_cong_data => 
  {rules = rules, derive_rules = f derive_rules, stop_congs = stop_congs, simprocs = simprocs})
fun map_stop_congs f = Data.map (fn {rules, derive_rules, stop_congs, simprocs}:monad_cong_data => 
  {rules = rules, derive_rules = derive_rules, stop_congs = f stop_congs, simprocs = simprocs})
fun map_simprocs f = Data.map (fn {rules, derive_rules, stop_congs, simprocs}:monad_cong_data => 
  {rules = rules, derive_rules = derive_rules, stop_congs = stop_congs, simprocs = f simprocs})


fun add_simproc p = map_simprocs (Ord_List.insert fast_string_ord p)

type fact = {pred: cterm, thms: thm list}

type proof_data = {states: cterm list, facts: fact list, 
  start: (Timing.start * string) option,
  cache: thm Net.net Unsynchronized.ref }

structure Prf_Data = Proof_Data (
  type T = proof_data;
  val init = (K {states = [], facts = [], start = NONE, cache = Unsynchronized.ref Net.empty});
)

fun map_states f = Prf_Data.map (fn {states, facts, start, cache}:proof_data => 
  {states = f states, facts = facts, start = start, cache = cache})
fun map_facts f = Prf_Data.map (fn {states, facts, start, cache}:proof_data => 
  {states = states, facts = f facts, start = start, cache = cache})
fun map_start f = Prf_Data.map (fn {states, facts, start, cache}:proof_data => 
  {states = states, facts = facts, start = f start, cache = cache})
fun map_cache f = Prf_Data.map (fn {states, facts, start, cache}:proof_data => 
  {states = states, facts = facts, start = start, cache = f cache})

val facts_of = #facts o Prf_Data.get
val states_of = #states o Prf_Data.get
val start_of = #start o Prf_Data.get
val cache_of = #cache o Prf_Data.get


val reset_cache = map_cache (fn _ => Unsynchronized.ref Net.empty)

fun add_to_cache ctxt thm =
  let
    val cache_ref = cache_of ctxt
    val cache' = Net.insert_term (Thm.eq_thm_prop ) (Thm.prop_of thm, thm) (!cache_ref)
    val _ = cache_ref := cache'
    val _ = Utils.verbose_msg 4 ctxt (fn _ => "cache add: " ^ Thm.string_of_thm ctxt thm)
  in
    ctxt
  end

fun lookup_cache ctxt ct =
  Net.match_term (!(cache_of ctxt)) (Thm.term_of ct)

fun start str = map_start (K (SOME (Timing.start (), str)))

fun stop str ctxt = ctxt |> map_start (Option.mapPartial (fn (start, str0) =>
  let
    val _ = Utils.timing_msg' 3 ctxt (fn _ => str0 ^ " -> " ^ str) start
  in
    NONE
  end))

fun monad_simp_active ctxt = not (null (states_of ctxt))
 
val lhs_of = Thm.dest_equals_lhs o Thm.cconcl_of
val rhs_of = Thm.dest_equals_rhs o Thm.cconcl_of

val lhs_of_rule = #apply_thm #> lhs_of


fun cong_lhs rule =
  let
    val lhs = lhs_of rule
    val {f, ...} = @{cterm_match (fo) "run ?f ?s"} lhs
  in
    f
  end

fun stop_cong rule =
  Thm.reflexive (cong_lhs rule)

fun mk_rule ctxt name split_vars thm =
  let
    val eq = Simpdata.mk_meta_cong ctxt thm
    val apply_thm = eq |> Drule.zero_var_indexes
    val lhs = lhs_of apply_thm
    val stop_thm = stop_cong apply_thm
    val rule = {apply_thm = Thm.trim_context apply_thm, stop_thm = Thm.trim_context stop_thm, split_vars = split_vars, name = name}
  in
    (Thm.term_of lhs, rule)
  end

fun mk_cond_rule name thm =
  let
    val prem = Thm.major_prem_of thm
    val rule = {thm = Thm.trim_context thm, name = name}
  in
    (prem, rule)
  end

fun compare_congs (thm1, thm2) =
  let
    val maxidx1 = Thm.maxidx_of thm1
    val lhs1 = lhs_of thm1
    val lhs2 = lhs_of thm2 |> Thm.incr_indexes_cterm (maxidx1 + 1)
    val result =
      if is_some (try Thm.match (lhs1, lhs2)) then
        SOME GREATER
      else if is_some (try Thm.match (lhs2, lhs1)) then
        SOME LESS
      else NONE
  in
   result
  end

fun equiv_congs (thm1, thm2) = 
  compare_congs (thm1, thm2) = SOME GREATER andalso compare_congs (thm2, thm1) = SOME GREATER

fun more_general thm1 thm2 =
  (case compare_congs (thm1, thm2) of
     SOME GREATER => SOME thm1
   | SOME LESS => SOME thm2
   | NONE => NONE)

fun more_specific thm1 thm2 =
  (case compare_congs (thm1, thm2) of
     SOME GREATER => SOME thm2
   | SOME LESS => SOME thm1
   | NONE => NONE)

fun insert_cong thm [] = [Thm.trim_context thm]
  | insert_cong thm (thms as (thm1::thms')) =
     (case compare_congs (thm1, thm) of
        SOME GREATER => thms
      | SOME LESS => insert_cong thm thms'
      | NONE => thm1 :: insert_cong thm thms')

fun rules_of ctxt = Data.get (Context.Proof ctxt)

fun build_congs stop_thms =
  [] |> fold (insert_cong) stop_thms

fun rebuild_stop_congs context =
  let
    val stop_thms = Data.get context |> #rules |> Net.entries |> map (Thm.transfer'' context o #stop_thm)
    val congs = build_congs stop_thms |> map Thm.trim_context
  in context |> (map_stop_congs (K congs)) end

val rebuild_stop_congs' = Context.proof_map rebuild_stop_congs

fun add_rule split_vars thm context =
  let
     val concl = Thm.concl_of thm
     val concl_vars = Term.add_vars concl [] |> map (#1 o #1)
     val unused = filter_out (member (op =) concl_vars) split_vars
     val _ = null unused orelse error ("split variables do not occur in conclusion: " ^ @{make_string} unused)
     val ctxt = Context.proof_of context
     val name = Utils.guess_binding_of_thm ctxt thm
     val rule = mk_rule ctxt name split_vars thm
     val cong = #stop_thm (snd rule) |> Thm.transfer' ctxt
  in
    context 
    |> map_rules (Net.insert_term_safe rule_eq rule)
    |> map_stop_congs (insert_cong cong)
  end

fun add_rule' split_vars thm =
  Context.proof_map (add_rule split_vars thm)

fun del_rule thm context =
  let
    val ctxt = Context.proof_of context
  in
    context
    |> map_rules (Net.delete_term_safe rule_eq (mk_rule ctxt Binding.empty [] thm))
    |> rebuild_stop_congs
  end

fun del_rule' thm = Context.proof_map (del_rule thm)

fun add_derive_rule thm0 context =
  let
     val ctxt = Context.proof_of context
     val thm = Simplifier.simplify ctxt thm0
     val name = Utils.guess_binding_of_thm ctxt thm
     val rule = mk_cond_rule name thm
  in
    context |> map_derive_rules (Net.insert_term_safe (* (K true) *)  cond_rule_eq rule)
  end

fun del_derive_rule thm0 context =
  let
     val ctxt = Context.proof_of context
     val thm = Simplifier.simplify ctxt thm0
  in
    context
    |> map_derive_rules (Net.delete_term_safe cond_rule_eq (mk_cond_rule Binding.empty thm))
  end

fun add_global_stop_cong thm =
  map_stop_congs (fn congs => (build_congs (thm :: congs)))

fun del_global_stop_cong thm =
  map_stop_congs (fn congs => (build_congs (remove Thm.eq_thm_prop thm congs)))

fun pretty_binding b = Pretty.str (More_Binding.here b)
fun pretty_entry label p = Pretty.block [(Pretty.str (suffix ": " label)), p]

fun pretty_rule ctxt (rule:rule) =
 Pretty.item (
 [pretty_entry "rule" (pretty_binding (#name rule)), Pretty.brk 1,
  Pretty.indent 2 (Thm.pretty_thm ctxt (#apply_thm rule) |> Pretty.cartouche), Pretty.brk 1])

fun pretty_rules ctxt (rules: rule list) = Pretty.big_list ("rules") (map (pretty_rule ctxt) rules)

fun print_rules context =
  Data.get context |> #rules |> Net.entries 
  |> pretty_rules (Context.proof_of context)
  |> Pretty.string_of |> writeln

fun pretty_cond_rule ctxt (rule:cond_rule) =
 Pretty.item (
 [pretty_entry "cond_rule" (pretty_binding (#name rule)), Pretty.brk 1,
  Pretty.indent 2 (Thm.pretty_thm ctxt (#thm rule) |> Pretty.cartouche), Pretty.brk 1])

fun pretty_derive_rules ctxt (rules: cond_rule list) = 
  Pretty.big_list ("derive rules") (map (pretty_cond_rule ctxt) rules)

fun print_derive_rules context =
  Data.get context |> #derive_rules |> Net.entries 
  |> pretty_derive_rules (Context.proof_of context)
  |> Pretty.string_of |> writeln

fun pretty_stop_cong ctxt thm =
  Pretty.item [Thm.pretty_thm ctxt thm]

fun pretty_stop_congs ctxt thms = Pretty.big_list ("stop_congs") (map (pretty_stop_cong ctxt) thms)

fun print_stop_congs context =
  Data.get context |> #stop_congs
  |> pretty_stop_congs (Context.proof_of context)
  |> Pretty.string_of |> writeln

fun map_theory_rules f thy =
  let
    val ctxt' = f (Proof_Context.init_global thy);
    val thy' = Proof_Context.theory_of ctxt';
  in
    Context.theory_map (Data.map (K (rules_of ctxt'))) thy'
  end

fun mk_fact thm =
  let
     val {P, ... } = @{cterm_match \<open>Trueprop (ADD_FACT ?P ?s)\<close>} (Thm.cconcl_of thm)
  in 
    {pred = P, thms = [@{thm ADD_FACT_D} OF [thm]]}:fact
  end

fun derive_facts ctxt thm =
  let
    val derive_rules = Net.match_term (#derive_rules (Data.get (Context.Proof ctxt))) (Thm.concl_of thm)
    val derived = map_filter (try (fn rule => rule OF [thm])) (map (Thm.transfer' ctxt o #thm) derive_rules)
  in
    map mk_fact derived
  end

fun get_more_specific [] = NONE           
  | get_more_specific [rule] = SOME rule
  | get_more_specific (rule1::rules) =
     let
        fun get_more_specific' (lhs0, rule0) [] = SOME rule0
          | get_more_specific' (lhs0, rule0) (rule1::rules) =
          let
            val lhs1 = lhs_of_rule rule1
          in
            if is_some (try Thm.match (lhs0, lhs1)) then
              get_more_specific' (lhs1, rule1) rules
            else
              get_more_specific' (lhs0, rule0) rules
          end
     in
       get_more_specific' (lhs_of_rule rule1, rule1) rules
     end

fun matching_rule ctxt trm =
  let
    val rules = Data.get (Context.Proof ctxt) |> #rules
    val matches = Net.match_term rules trm
  in get_more_specific matches |> Option.map (transfer_rule ctxt) end

fun lookup_by_name tvars x =
  let
    val xs = Vars.dest tvars |> map (apfst fst)
  in
    AList.lookup (op =) xs (x, 0)
  end

fun lhs_concl_conv cv thm = 
  let
    val n = Thm.nprems_of thm
  in
     Conv.fconv_rule 
      (Conv.concl_conv n 
         (Conv.arg1_conv cv)) thm
  end

(* Plain Conv.rewr_conv did not work in our setting. The matching of lhs and ct fails. 
   But Simplifier.simplify would work. 
   So Conv.rewr_conv seems to do "too much" for our exact match but not as much as simplifier.
   (Maybe some kind of weired eta-conversion stuff?)
   But as we have an exact match anyway there is no need to match again.
*)
fun rewr_exact_conv eq ct =
  let
    val eq2 =
      if Thm.lhs_of eq aconvc ct then eq
      else
        let val ceq = Thm.dest_fun2 (Thm.cprop_of eq)
        val eq1 = Thm.trivial (Thm.mk_binop ceq ct (Thm.rhs_of eq))
        in eq COMP eq1 end;
  in Thm.transitive eq2 (Thm.beta_conversion true (Thm.rhs_of eq2)) end;

fun inst_split_rule ctxt ({apply_thm, split_vars, ...}:rule) ct =
  let
    val lhs_rule = lhs_of apply_thm
    val env as (Tvars, tvars) = Thm.match (lhs_rule, ct)
  in
    if null split_vars then
      (Thm.instantiate env apply_thm, 0, [])
    else
      let
        val orig_var = hd split_vars
        val bdy = the (lookup_by_name tvars orig_var)
        val domT = Thm.typ_of_cterm bdy |> domain_type
        val arity =  domT |> HOLogic.flatten_tupleT |> length
        val names = Tuple_Tools.strip_case_prod' (Thm.term_of bdy)
        val split_ctxt = Proof_Context.init_global (Proof_Context.theory_of ctxt)
        val (no_split, splitted_thm) = 
              if length names = 1 andalso arity > 1 then
                (true, apply_thm) (* corner case of trivial  \<open>\<lambda>(_::('a *  ...)). f\<close> *)
              else
                (false, Tuple_Tools.split_rule split_ctxt split_vars apply_thm arity)
        
        val tvars_eta = Vars.map (fn _ => Tuple_Tools.eta_expand_tuple ctxt) tvars
        val eta_inst_rule = Thm.instantiate (Tvars, tvars_eta) apply_thm
        val lhs_eta_inst_rule = lhs_of eta_inst_rule
        val (inst_rule, names') = 
          if arity <= 1  then (eta_inst_rule, names)
          else
            let
              val env1 = Thm.match (lhs_of splitted_thm, lhs_eta_inst_rule)
              val inst_thm1 = Thm.instantiate env1 splitted_thm
              val inst_thm2 = 
                if Utils.cterm_eq (lhs_eta_inst_rule, ct) then inst_thm1
                else
                  let
                    val _ = warning ("eta expanding case prod from:\n " ^ string_of_cterm ctxt ct ^ " to:\n " ^
                              string_of_cterm ctxt lhs_eta_inst_rule) 
                    val eta_eq_prop = \<^infer_instantiate>\<open>eta_lhs = lhs_eta_inst_rule and orig_lhs = ct 
                      in cterm \<open>eta_lhs \<equiv> orig_lhs\<close>\<close> ctxt
                    val eta_eq = Goal.prove_internal ctxt [] eta_eq_prop 
                      (fn _ => asm_full_simp_tac ((Simplifier.clear_simpset ctxt) addsimps 
                         @{thms case_prod_eta bind_case_prod_trivial case_prod_beta 
                            case_prod_beta' prod.sel prod.collapse}) 1)
                    val obj = Thm.term_of (Thm.lhs_of eta_eq)
                    val pat = Thm.term_of (Utils.clhs_of (Thm.cconcl_of inst_thm1))
                    val inst_thm' = lhs_concl_conv (rewr_exact_conv eta_eq) inst_thm1
                    (* Preserve bound names  *)
                    val inst_thm'' = Thm.rename_boundvars pat obj inst_thm'
                  in inst_thm'' end
              val bdy' = the (lookup_by_name tvars_eta orig_var)
              val names' = if no_split then names else Tuple_Tools.strip_case_prod' (Thm.term_of bdy')
          in 
            (inst_thm2, names')
          end
        
        val names'' = if arity = 1 andalso null names' then 
                       [("r", domT)] (* make up name for eta-contracted corner case*)
                     else names'  
       in
        (inst_rule, arity, names'')
      end
  end

fun strip_all_fix names ct ctxt =
  let
     val n = length names
     val (bounds, _) = Utils.strip_all_open [] (Thm.term_of ct) |> apfst rev
     val _ = if n <> length bounds then raise CTERM ("strip_all_fix: unequal length: " ^ @{make_string} (names, bounds), [ct]) else ()
     val vars = names ~~ (map snd (take n bounds))
     val (fixes, ctxt') = Utils.fix_variant_cfrees vars ctxt
     val thm = Goal.prove_internal ctxt [] ct (fn _ =>  ALLGOALS (Skip_Proof.cheat_tac ctxt))
     val thm' = thm |> fold Thm.forall_elim fixes
     val ct' = Thm.cprop_of thm'
  in
    ((fixes, ct'), ctxt')
  end

fun fix_import_state_and_names ctxt names ct =
  let
    val states = Prf_Data.get ctxt |> #states
    val nstates = length states
    val ((fixes, ct'), ctxt') = strip_all_fix (("s" ^ string_of_int nstates)::names) ct ctxt
  in ((fixes, ct'), ctxt') end

fun match_preserved_facts ctxt names ct =
 let
   val ((fixes, ct'), ctxt') = fix_import_state_and_names ctxt names ct
       handle CTERM _ => raise Match
   val {f, s, r, t, lhs, rhs, ... } = @{cterm_match \<open>PRESERVED_FACTS ?f ?s ?r ?t \<Longrightarrow> ?lhs \<equiv> ?rhs\<close>} ct'
   val {g', ...} = @{cterm_match \<open>run ?g' ?s\<close>} rhs
 in
   {f = f, s = s, t = t, r = r, results = tl fixes, lhs = lhs, g' = g', ctxt' = ctxt'}
 end

fun match_preserved_facts_while ctxt names ct =
  let
    val ((fixes, ct'), ctxt') = fix_import_state_and_names ctxt names ct
        handle CTERM _ => raise Match
    val {C, B, i, s, r, t, C_lhs, C_rhs, B_lhs, B_rhs, ... } = 
          @{cterm_match \<open>PRESERVED_FACTS_WHILE ?C ?B ?i ?s ?r ?t \<Longrightarrow> 
             ((?C_lhs \<equiv> ?C_rhs) &&& (?C_rhs \<Longrightarrow> (?B_lhs \<equiv> ?B_rhs)))\<close>} ct'
    val C' = fst (Utils.strip_comb_cterm C_rhs)
    val {B', ...} = @{cterm_match \<open>run ?B' ?t\<close>} B_rhs
  in
    {C = C, C' = C', B = B, B' = B', i = i, s = s, r = r, t =t, results = tl fixes, 
      C_lhs = C_lhs, B_lhs = B_lhs, ctxt' = ctxt' }
  end

fun rule_by_tactic_schematic ctxt thm tac =
  Utils.check_solve_sideconditions (K true) ctxt tac thm

fun rhs_conv conv = Conv.fconv_rule (Conv.arg_conv conv)
fun STOP_conv ctxt eq = 
  let
  in 
    Utils.timeit_msg 4 ctxt (fn _ => "STOP_conv: ") 
      (fn _ => rhs_conv (Conv.try_conv (Conv.rewr_conv @{thm STOP_def})) eq)
  end


fun rewr_conv rules ct =
  let
    val thms = Net.match_term rules (Thm.term_of ct)
  in
    Conv.rewrs_conv thms ct
  end

fun mk_rewr_conv eqs =
  let
    fun prep eq = 
      let val eq' = safe_mk_meta_eq eq
      in (Utils.rhs_of_eq (Thm.prop_of eq'), eq') end

    val rules = Net.empty |> fold (Net.insert_term (Thm.eq_thm) o prep) eqs
  in
    rewr_conv rules
  end

fun dest_bool_eq eq =
  (try (fn eq => (@{thm eq_TrueD} OF [eq])) eq |> the_list) @
  (try (fn eq => (@{thm eq_FalseD} OF [eq])) eq |> the_list)

val dest_bool_eqs = maps dest_bool_eq

val is_iarith = Match_Cterm.switch [
  @{cterm_match "Trueprop ((?m::'a::linordered_idom) < ?n)" } #> (fn _ => true),
  @{cterm_match "Trueprop ((?m::'a::linordered_idom) \<le> ?n)" } #> (fn _ => true),
  @{cterm_match "Trueprop ((?m::'a::linordered_idom) = ?n)" } #> (fn _ => true),
  @{cterm_match "Trueprop (\<not> (?m::'a::linordered_idom) < ?n)" } #> (fn _ => true),
  @{cterm_match "Trueprop (\<not> (?m::'a::linordered_idom) \<le> ?n)" } #> (fn _ => true),
  @{cterm_match "Trueprop (\<not> (?m::'a::linordered_idom) = ?n)" } #> (fn _ => true),
  fn _ => false
]

val iariths_of_eqs = dest_bool_eqs #> filter (is_iarith o Thm.cprop_of)

fun add_ariths thms ctxt = 
  let
    val _ = Utils.verbose_msg 5 ctxt (fn _ => ("adding ariths:\n "  ^ string_of_thms ctxt thms))
  in
    ctxt |> Context.proof_map (
      fold (Named_Theorems.add_thm @{named_theorems arith}) thms)
  end

fun dest_abs_fresh (n, x) f = 
  snd (Thm.dest_abs_fresh n f) handle CTERM _ => Thm.apply f x

fun strip_case_prod_cterm ctxt ct =
 let
   val args = Tuple_Tools.strip_case_prod' (Thm.term_of ct)
   val (fixes, ctxt1) = Utils.fix_variant_cfrees args ctxt
   val orig_names = map fst args
   val names = map (fst o dest_Free o Thm.term_of) fixes
   val named_fixes = names ~~ fixes
   fun strip [x, y] ct = 
         let
           val {f, ...} = @{cterm_match (fo) "case_prod ?f"} ct  
         in dest_abs_fresh y (dest_abs_fresh x f) end
     | strip [x] ct = dest_abs_fresh x ct
     | strip [] ct = ct
     | strip (x::xs) ct = 
         let
           val {f, ...} = @{cterm_match (fo) "case_prod ?f"} ct
           val ct' = dest_abs_fresh x f
         in strip xs ct' end 
   val bdy = strip named_fixes ct
 in
   ((names ~~ fixes, orig_names, bdy), ctxt1)
 end


fun case_prod_bdy_conv ctxt ct =
  let
     val ((fixes, orig_names,  bdy), ctxt') = strip_case_prod_cterm ctxt ct
     val bdy_eq = Simplifier.rewrite ctxt' bdy
     val lhs = bdy_eq |> Thm.lhs_of
     val rhs = bdy_eq |> Thm.rhs_of
     val fixes' = map2 (fn (_, x) => fn n => (n, x)) fixes orig_names
     val f = Utils.lambdas_tupled fixes' lhs
     val g = Utils.lambdas_tupled fixes' rhs
     val eq_prop = \<^infer_instantiate>\<open>f = f and g = g in cprop "f \<equiv> g"\<close> ctxt
     val simps = if (Thm.term_of f) aconv (Thm.term_of g)  then [] else (Proof_Context.export ctxt' ctxt [bdy_eq])
     val simp_ctxt = Simplifier.clear_simpset ctxt addsimps (@{thms fun_eq_iff} @ simps)  
     val eq = Goal.prove_internal simp_ctxt [] eq_prop 
            (fn _ => simp_tac simp_ctxt 1)
  in 
     eq
  end

val case_prod_cong = @{lemma "x \<equiv> x' \<Longrightarrow> case_prod f \<equiv> g \<Longrightarrow> case_prod f x = g x'" for x x' f g by auto }
fun case_prod_apply_conv ctxt = Match_Cterm.switch [
  @{cterm_match "case_prod ?f ?x"} #> (fn {f, x, ct_, ...} => 
     let
       val x_eq = Simplifier.rewrite ctxt x
       val cp = \<^infer_instantiate>\<open>f = f in cterm \<open>case_prod f\<close>\<close> ctxt
       val cp_eq = case_prod_bdy_conv ctxt cp
     in case_prod_cong OF [x_eq, cp_eq] end)]

(* e.g. avoid substition with \<open>n = global_variable s\<close> *)
fun state_dependent_rhs ctxt thm =
  case states_of ctxt of
    [] => false
  | (s::_) => 
    let val s' = Thm.term_of s 
    in exists_subterm (fn t => t = s') (Utils.rhs_of (Thm.concl_of thm)) end
 
fun gen_mksimps do_simp ctxt thm =
  let
    val thm' = if do_simp then Simplifier.asm_full_simplify ctxt thm else thm
  in
    thm' |> Simplifier.mksimps ctxt |> filter_out ( Utils.trivial_meta_eq_thm orf (state_dependent_rhs ctxt)) (* avoid loops *)
  end

val mksimps = gen_mksimps false


fun params_of prem = prem |> Thm.term_of |> Utils.strip_all_open [] |> fst

fun timeit_export str inner outer thms =
  Utils.timeit_msg 3 outer (fn _ => "export " ^ str) (fn _  => Proof_Context.export inner outer thms)

fun monad_state_conv (rule as {split_vars, ...}) ctxt ct =
  let
    val _ = Utils.verbose_msg 4 ctxt (fn _ => ("rule:\n " ^ Thm.string_of_thm ctxt (#apply_thm rule)))

    val (inst_rule, arity, names) = Utils.timeit_msg 3 ctxt (fn _ => "inst_split_rule: ") 
      (fn _ =>inst_split_rule ctxt rule ct)
    val _ = Utils.verbose_msg 7 ctxt (fn _ => ("inst_rule:\n " ^ Thm.string_of_thm ctxt inst_rule))

    fun simp_rule rule =
      let
      in
      (case Thm.cprems_of rule of
         [] => rule
       | (prem::_) => 
         let val _ = Utils.verbose_msg 7 ctxt (fn _ => "prem: " ^ string_of_cterm ctxt prem)
         in prem
         |> Match_Cterm.switch [
            @{cterm_match (fo) "Trueprop (RUN_CASE_PROD ?f ?x ?s ?f' ?x')"} #> (fn {f, x, s, f', x',...} =>
               let
                 val ctxt = stop "RUN_CASE_PROD" ctxt
                 val x_eq = Utils.timeit_msg 4 ctxt (fn _ => "eq (0) x: ") 
                  (fn _  => Simplifier.asm_full_rewrite ctxt x)
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("eq (0) x:\n "  ^ Thm.string_of_thm ctxt x_eq))
                 val start0 = Timing.start ();
                 val x'_inst = rhs_of x_eq
                 val f1 = \<^infer_instantiate>\<open>f = f in cterm \<open>case_prod f\<close>\<close> ctxt
                 val ((fixes, orig_names, f_bdy), ctxt') = strip_case_prod_cterm ctxt f1
                 val run_f = \<^infer_instantiate>\<open>f = f_bdy and s = s in cterm\<open>run f s\<close> \<close> ctxt'
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "case_prod (0)") start0

                 val run_f_eq = Utils.timeit_msg 4 ctxt (fn _ => "eq (1) x: ") 
                   (fn _  => Simplifier.asm_full_rewrite (start "eq (1) x" ctxt') run_f |> STOP_conv ctxt')
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("eq (1) f:\n "  ^ Thm.string_of_thm ctxt run_f_eq))
                 val start1 = Timing.start ();
                 val {f = f1', ...} = @{cterm_match \<open>run ?f ?s\<close>} (rhs_of run_f_eq)
                 val fixes' = map2 (fn (_, x) => fn n => (n, x)) fixes orig_names
                 val f_tupled = Utils.lambdas_tupled fixes' f_bdy
                 val f'_tupled = Utils.lambdas_tupled fixes' f1'
                 val eq_prop = \<^infer_instantiate>\<open>f = f_tupled and f' = f'_tupled and x = x'_inst and s = s in 
                       cprop \<open>run (f x) s \<equiv> run (f' x) s\<close>\<close> ctxt
                 val simps = if Utils.trivial_meta_eq_thm run_f_eq then [] else (timeit_export "RUN_CASE_PROD" ctxt' ctxt [run_f_eq])
                           @ @{thms Spec_Monad.run_case_prod_distrib}
                 val simp_ctxt = Simplifier.clear_simpset ctxt addsimps (@{thms fun_eq_iff} @ simps)  
                 val eq = Goal.prove_internal simp_ctxt [] eq_prop
                    (fn _ => simp_tac simp_ctxt 1)
                 val thm = @{thm RUN_CASE_PROD_I} OF [x_eq, eq]
                 val rule1 = rule OF [thm]
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "case_prod (1)") start1
               in simp_rule rule1 end),
            @{cterm_match (fo) "?lhs \<equiv> run ?f ?s"} #> (fn {lhs, f, s, ...} =>
               let
                 val ctxt = stop "lhs = run f s" ctxt
                 val fN = fst (dest_Var (Thm.term_of f))
                 val eq = Utils.timeit_msg 4 ctxt (fn _ => "eq (1): ") 
                  (fn _  => Simplifier.asm_full_rewrite (start "eq (1)" ctxt) lhs |> STOP_conv ctxt)
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("eq (1):\n "  ^ Thm.string_of_thm ctxt eq))
                 val start0 = Timing.start ();
                 val {f', ...} = @{cterm_match \<open>run ?f' ?s\<close>} (rhs_of eq)
                 val rule1 = Drule.infer_instantiate ctxt [(fN, f')] rule
                 val rule2 = rule1 OF [eq]
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "lhs = run f s (0)") start0
               in simp_rule rule2 end),
            @{cterm_match (fo) "?lhs \<equiv> ?f ?s"} #> (fn {lhs, f, s, ct_,...} =>
               let
                 val ctxt = stop "lhs = f s" ctxt
                 val fN = fst (dest_Var (Thm.term_of f))
                 val eq = Utils.timeit_msg 4 ctxt (fn _ => "eq (2): ") 
                   (fn _  => Simplifier.asm_full_rewrite (start "eq (2)" ctxt) lhs)
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("eq (2):\n "  ^ Thm.string_of_thm ctxt eq))
                 val start0 = Timing.start ();
                 val rhs_eq = rhs_of eq
                 val f' = Thm.lambda_name ("s", s) rhs_eq
                 val rule1 = Drule.infer_instantiate ctxt [(fN, f')] rule
                 val rule2 = rule1 OF [eq]
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "lhs = f s (0)") start0
               in simp_rule rule2 end),
            @{cterm_match (fo) "?lhs \<equiv> ?f"} #> (fn {lhs, f,...} =>
               let
                 val ctxt = stop "lhs = f" ctxt
                 val fN = fst (dest_Var (Thm.term_of f))
                 val eq = Utils.timeit_msg 4 ctxt (fn _ => "eq (3): ") 
                   (fn _  => Simplifier.asm_full_rewrite (start "eq (3)" ctxt) lhs)
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("eq (3):\n "  ^ Thm.string_of_thm ctxt eq))
                 val start0 = Timing.start ();
                 val rhs_eq = rhs_of eq
                 val f' = rhs_eq
                 val rule1 = Drule.infer_instantiate ctxt [(fN, f')] rule
                 val rule2 = rule1 OF [eq]
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "lhs = f (0)") start0
               in simp_rule (rule2) end),
            @{cterm_match (fo) "ADD_FACT ?P ?s \<Longrightarrow> ?lhs \<equiv> run ?f ?s"} #> (fn {P, s, lhs, f, ...} => 
               let
                 val ctxt = stop "ADD_FACT" ctxt
                 val start0 = Timing.start ();
                 val fN = fst (dest_Var (Thm.term_of f))
                 val fact_prop = \<^infer_instantiate>\<open>P = P and s = s in cprop \<open>ADD_FACT P s\<close>\<close> ctxt
                 val ([fact], ctxt1) = Assumption.add_assumes [fact_prop] ctxt
                 val fact0 = Utils.apply_beta_conv P s
                   |> Utils.Trueprop_cterm
                 val fact1 = Goal.prove_internal ctxt1 [] fact0 (fn _ => 
                       Method.insert_tac ctxt1 [fact] 1 THEN 
                       asm_full_simp_tac (ctxt1 addsimps @{thms ADD_FACT_def}) 1)
                 val fact_eqs = gen_mksimps true ctxt1 fact1
                 val fact_ariths = iariths_of_eqs fact_eqs
                 val ctxt2 = (ctxt1 |> map_facts (cons {pred = P, thms = fact_eqs})) 
                       addsimps fact_eqs
                       |> add_ariths fact_ariths
                       |> Simplifier.add_prems fact_eqs
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "ADD_FACT (0)") start0
                 val _ = Utils.verbose_msg 4 ctxt (fn _ => ("adding:\n "  ^ string_of_thms ctxt1 fact_eqs))
                 val eq = Utils.timeit_msg 4 ctxt (fn _ => "eq (4): ") 
                   (fn _  => Simplifier.asm_full_rewrite (start "eq (4)" ctxt2) lhs 
                     |> STOP_conv ctxt2 |> singleton (timeit_export ("eq (4): ") ctxt2 ctxt))
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("eq (4):\n "  ^ Thm.string_of_thm ctxt eq))
                 val start1 = Timing.start ();
                 val {f', ...} = @{cterm_match \<open>run ?f' ?s\<close>} (rhs_of eq)
                 val rule1 = Utils.timeit_msg 4 ctxt (fn _ => "ADD_FACT rule1: ") 
                   (fn _ => Drule.infer_instantiate ctxt [(fN, f')] rule)
                 val rule2 = Utils.timeit_msg 4 ctxt (fn _ => "ADD_FACT rule2: ") 
                   (fn _ =>  eq COMP rule1)
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "ADD_FACT (1)") start1
               in simp_rule rule2 end),
            match_preserved_facts ctxt (map fst names) #> (fn {f, s, t, r, results, lhs, g'=g'0, ctxt'} => 
               let
                 val ctxt' = stop "preserved" ctxt' |> reset_cache
                 val facts = facts_of ctxt'
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => "facts (1):\n " ^ string_of_thms ctxt'  (maps #thms facts))
                 val start0 = Timing.start ();
                 val s_eqs = maps #thms facts
                 val gN = fst (dest_Var (Thm.term_of (fst (Utils.strip_comb_cterm g'0))))
                 val preserved_prop = \<^infer_instantiate>\<open>f = f and s = s and r = r and t = t in
                      cprop "PRESERVED_FACTS f s r t"\<close> ctxt'
                 val ([preserved], ctxt1) = Assumption.add_assumes [preserved_prop] ctxt'
                 val derived_props = map #pred facts |> map (fn pred =>
                       (pred, Thm.apply pred t |> Utils.Trueprop_cterm))
                 val derived_facts0 = derive_facts ctxt' preserved
                 fun prover ctxt =
                   let
                      val ctxt = ctxt (*|> Config.put Simplifier.simp_trace true*)
                   in
                       Method.insert_tac ctxt [preserved] 1 THEN
                       (SOLVED_DETERM_verbose "preserved" ctxt 
                         (asm_full_simp_tac (ctxt 
                           addsimps @{thms PRESERVED_FACTS_def} @ s_eqs))) 1 
                   end
                 val derived_facts1 = derived_props |> map_filter (fn (pred, prop) => 
                       try (fn prop => Goal.prove_internal ctxt1 [] prop (fn _ => prover ctxt1)) prop |> 
                       Option.map (fn thm => ({pred = pred, thms = mksimps ctxt1 thm})))
                 val derived_facts = derived_facts0 @ derived_facts1
                 val derived_eqs = maps #thms derived_facts
                 val derived_ariths = iariths_of_eqs (maps #thms derived_facts)
                 val ctxt2 = ctxt1 
                   addsimps derived_eqs
                   |> Simplifier.add_prems derived_eqs
                   |> map_states (cons t)
                   |> map_facts (K derived_facts)
                   |> add_ariths derived_ariths
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "preserved (0)") start0
                 val _ = Utils.verbose_msg 4 ctxt (fn _ => "derived_facts (1):\n " ^ string_of_thms ctxt1  (maps #thms derived_facts))
                 val eq1 = Utils.timeit_msg 4 ctxt (fn _ => "eq (5): ") 
                   (fn _  =>  Simplifier.asm_full_rewrite (start "eq (5)" ctxt2) lhs 
                     |> STOP_conv ctxt2 |> singleton (timeit_export "eq (5): " ctxt2 ctxt'))
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("eq (5):\n "  ^ Thm.string_of_thm ctxt' eq1))
                 val start1 = Timing.start ();
                 val eq = eq1 |> singleton (Proof_Context.export ctxt' ctxt)
                 val {g', ...} = @{cterm_match \<open>run ?g' ?s\<close>} (rhs_of eq1)
                 val _ = if length names <> length results then 
                    error ("match_preserved_facts: unequal length" ^ @{make_string} (names, results)) else ()
                 val results' = map fst names ~~ results
                 val g' = Utils.timeit_msg 4 ctxt (fn _ => "preserved lambdas: ") 
                   (fn _ => Utils.lambdas (results') g')
                 val rule1 =  Utils.timeit_msg 4 ctxt (fn _ => "preserved rule1: ") 
                   (fn _ => Drule.infer_instantiate ctxt [(gN, g')] rule)
                 val rule2 = Utils.timeit_msg 4 ctxt (fn _ => "preserved rule2: ") 
                   (fn _ => (rule1 OF [eq]) 
                      |> rule_by_tactic_schematic ctxt (Method.assm_tac ctxt 1))
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "preserved (1)") start1
               in
                 simp_rule rule2
               end),
            match_preserved_facts_while ctxt (map fst names) #> (fn {C, C'=C'0, B, B'=B'0, i, s, t, r, results,  C_lhs, B_lhs, ctxt'} => 
               let
                 val ctxt' = stop "while" ctxt' |> reset_cache
                 val start0 = Timing.start ();
                 (* Generalize and merge code with previous case *)
                 val facts = facts_of ctxt'
                 val s_eqs = maps #thms facts
                 val CN = fst (dest_Var (Thm.term_of (fst (Utils.strip_comb_cterm C'0))))
                 val BN = fst (dest_Var (Thm.term_of (fst (Utils.strip_comb_cterm B'0))))
                 val preserved_prop = \<^infer_instantiate>\<open>C = C and B = B  and i = i and s = s and r = r and t = t in
                      cprop "PRESERVED_FACTS_WHILE C B i s r t"\<close> ctxt'
                 val ([preserved], ctxt1) = Assumption.add_assumes [preserved_prop] ctxt'
                 val derived_props = map #pred facts |> map (fn pred =>
                       (pred, Thm.apply pred t |> Utils.Trueprop_cterm))
                 fun prover ctxt =
                      Method.insert_tac ctxt [preserved] 1 THEN
                      asm_full_simp_tac (ctxt addsimps @{thms PRESERVED_FACTS_WHILE_def} @ s_eqs) 1
                 val derived_facts = derived_props |> map_filter (fn (pred, prop) => 
                       try (fn prop => Goal.prove_internal ctxt1 [] prop (fn _ => prover ctxt1)) prop |> 
                       Option.map (fn thm => ({pred = pred, thms = mksimps ctxt1 thm})))
                 val derived_eqs = maps #thms derived_facts
                 val derived_ariths = iariths_of_eqs (maps #thms derived_facts)

                 val ctxt2 = ctxt1
                   addsimps derived_eqs
                   |> Simplifier.add_prems derived_eqs
                   |> map_states (cons t)
                   |> map_facts (K derived_facts)
                   |> add_ariths derived_ariths
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "while (0)") start0
                 val _ = Utils.verbose_msg 4 ctxt (fn _ => "derived_facts (2):\n " ^ string_of_thms ctxt1  (maps #thms derived_facts))
                 val C_eq1 = Utils.timeit_msg 3 ctxt (fn _ => "eq (6): ") 
                   (fn _  =>  Simplifier.asm_full_rewrite (start "eq (6)" ctxt2) C_lhs 
                     |> STOP_conv ctxt2|> singleton (timeit_export "eq (6): " ctxt2 ctxt'))
                 val start1 = Timing.start ();
                 val C'1 = (rhs_of C_eq1)
                 val _ = if length names <> length results then 
                    error ("match_preserved_facts_while: unequal length" ^ @{make_string} (names, results)) else ()
                 val results' = map fst names ~~ results
                 val C' = Utils.lambdas (results' @ [("s", t)]) C'1
                 val C'_pred = Utils.lambdas [("s", t)] C'1
                 val ([C'_thm], ctxt3) = Assumption.add_assumes [Utils.Trueprop_cterm C'1] ctxt2
                 val C'_eqs = mksimps ctxt3 C'_thm
                 val C'_ariths = iariths_of_eqs C'_eqs
                 val ctxt4 = (ctxt3 |> map_facts (cons {pred = C'_pred, thms = C'_eqs}))
                       addsimps C'_eqs
                       |> Simplifier.add_prems C'_eqs
                       |> add_ariths C'_ariths
                 val _ = Utils.timing_msg' 3 ctxt (fn _ => "while (1)") start1
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("adding:\n "  ^ string_of_thms ctxt1 C'_eqs))
                 val B_eq1 = Utils.timeit_msg 4 ctxt (fn _ => "eq (7): ") 
                   (fn _  =>  Simplifier.asm_full_rewrite (start "eq (7)" ctxt4) B_lhs 
                     |> STOP_conv ctxt4 |> singleton (timeit_export "eq (7): " ctxt4 ctxt'))
                 val start2 = Timing.start ();
                 val {B', ...} = @{cterm_match \<open>run ?B' ?t\<close>} (rhs_of B_eq1)
                 val B' = Utils.lambdas (results') B'
                 val rule1 = Drule.infer_instantiate ctxt [(CN, C'), (BN, B')] rule
                 val [C_eq, B_eq] = [C_eq1, B_eq1] |> Proof_Context.export ctxt' ctxt
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("eq (6):\n "  ^ Thm.string_of_thm ctxt C_eq))
                 val _ = Utils.verbose_msg 5 ctxt (fn _ => ("eq (7):\n "  ^ Thm.string_of_thm ctxt B_eq))
                 val rule2 = Utils.solve_sideconditions ctxt rule1 (
                       resolve_tac ctxt [Conjunction.conjunctionI] 1 THEN
                       resolve_tac ctxt [C_eq] 1 THEN
                       Method.assm_tac ctxt 1 THEN
                       resolve_tac ctxt [B_eq] 1 THEN
                       Method.assm_tac ctxt 1 THEN
                       Method.assm_tac ctxt 1 
                       )
                val _ = Utils.timing_msg' 3 ctxt (fn _ => "while (2)") start2
               in simp_rule rule2
               end),
            fn ct => raise TERM ("monad_state_conv: unexpected: ",  [Thm.term_of ct])] end )
      end
  in
    simp_rule inst_rule
  end
  handle Option.Option => Thm.reflexive ct

fun monad_state_conv' (rules: rules) ctxt ct =
  let
    val matches0 = Net.match_term rules (Thm.term_of ct)
  in
    case get_more_specific matches0 of
      NONE => Thm.reflexive ct
    | SOME rule => monad_state_conv rule ctxt ct
  end

fun monad_run_simproc rule ctxt ct =
  let
    val eq = monad_state_conv rule ctxt ct
  in
    if Utils.is_reflexive ctxt eq then
      NONE
    else
      SOME (Utils.timeit_msg 3 ctxt (fn _ => "STOPI: ") (fn _ => @{thm STOPI} OF [eq]))
  end

end
\<close>


attribute_setup monad_simp_global_stop_cong = \<open>
  Scan.lift (Scan.option Args.add) >> (fn _ => Thm.declaration_attribute (Monad_Cong_Simp.add_global_stop_cong))
  || Scan.lift Args.del >> (fn _ => Thm.declaration_attribute (Monad_Cong_Simp.del_global_stop_cong))
\<close> "Global 'stop' congruence rule for monad simplification" 

attribute_setup monad_simp_cong = \<open>
let
  val split = Args.$$$ "split" |-- Args.colon |-- Parse.and_list Parse.short_ident
  val opt_split = Scan.optional (Scan.lift (split)) []
  fun pos_here [] = (Position.none, [])
    | pos_here ts = (Token.pos_of (hd ts), ts)
in
  Scan.lift Args.add |-- (Scan.lift pos_here -- opt_split) >> (fn (pos, splits) => 
      Thm.declaration_attribute (Monad_Cong_Simp.add_rule splits)) 
  || Scan.lift Args.del >> (K (Thm.declaration_attribute (Monad_Cong_Simp.del_rule)))
  || opt_split >> (fn splits => 
      Thm.declaration_attribute (Monad_Cong_Simp.add_rule splits))
end\<close> "Monad congruence theorems"

attribute_setup monad_simp_derive_rule = \<open>
  Scan.lift (Scan.option Args.add) >> (fn _ => Thm.declaration_attribute (Monad_Cong_Simp.add_derive_rule))
  || Scan.lift Args.del >> (fn _ => Thm.declaration_attribute (Monad_Cong_Simp.del_derive_rule))
\<close> "Conditional rules to derive facts in monad simplification" 

simproc_setup monad_run_simproc (\<open>run f s\<close>) = \<open>fn _ => fn ctxt => fn ct => 
  Monad_Cong_Simp.matching_rule ctxt (Thm.term_of ct) |> Option.mapPartial (fn rule => 
   let
     val _ = Utils.verbose_msg 7 ctxt (fn _ => "monad_run_simproc:\n " ^ string_of_cterm ctxt ct)
   in
     Monad_Cong_Simp.monad_run_simproc rule ctxt ct
   end)\<close>
declare [[simproc del: monad_run_simproc]]

lemma spec_monad_ext': "(\<And>s. run f s \<equiv> run f' s) \<Longrightarrow> f \<equiv> f'"
  by (smt (verit) spec_monad_ext)

ML \<open>
structure Monad_Cong_Simp =
struct
  open Monad_Cong_Simp

fun dest_spec_monadT \<^Type>\<open>spec_monad E A S\<close> = {exnT = E, regT = A, stateT = S}
  | dest_spec_monadT T = raise TYPE("dest_spec_monadT: ", [T], [])

fun gen_monad_conv {stop} ctxt ct =
  let
    val cT = Thm.ctyp_of_cterm ct
    val {stateT, exnT, regT} = Thm.typ_of_cterm ct |> dest_spec_monadT
    val {rules, ...} = Data.get (Context.Proof ctxt)
    val ([s], ctxt1) = Utils.fix_variant_cfrees [("s", stateT)] ctxt
    val ctxt2 = map_states (K [s]) ctxt1  
    val lhs = \<^infer_instantiate>\<open>f = ct and s = \<open>s\<close>  
         in cterm \<open>run f s\<close> for f::\<open>('e::default, 'a, 's) spec_monad\<close>\<close> ctxt
    val eq = monad_state_conv' rules ctxt2 lhs
    val eq' = singleton (Proof_Context.export ctxt2 ctxt) eq
    val eq' = @{thm spec_monad_ext'} OF [eq']
  in
    if stop then (@{thm STOPI} OF [eq']) |> Drule.zero_var_indexes else eq'
  end

end
\<close>



text \<open>
We make a global setup here, as the locale one within @{locale heap_typing_state} fails.
The reason is that the pattern is not taken into account in simproc equality when inserted into
the net. Hence multiple instances (e.g. for \<open>globals\<close> and \<open>lifted_globals\<close>) are considered a duplicate
when adding them both to the net but the simplifier does not match the pattern for \<open>globals\<close> on a
\<open>lifted_globals\<close> instance. In the upcoming Isabelle2024 this issue should be resolved.
\<close>

simproc_setup unchanged_typing_spec_monad (\<open>c \<bullet> s ?\<lbrace>\<lambda>r. heap_typing_state.unchanged_typing_on htd \<S> s\<rbrace>\<close>  ) = \<open>
  let
    val is_assume_stack_alloc = Match_Cterm.switch [
            @{cterm_match (fo) "typ_heap_typing.assume_stack_alloc ?r ?w ?ht ?ht_upd ?S ?n ?X \<bullet> ?s ?\<lbrace>?Q\<rbrace>"} #> 
               (fn _ => true),
            (fn _ => false)]

    val active = Config.declare_bool ("active", Position.none) (K false);
    val prop_to_meta_eq = @{lemma \<open>P \<Longrightarrow> (P \<equiv> True)\<close> for P by auto}
    fun try_prove ctxt prop =
      case Monad_Cong_Simp.lookup_cache ctxt prop of
        [] =>
        let
          val ctxt' = Context.proof_map (Named_Rules.add_thm @{named_rules runs_to_vcg} @{thm runs_to_partial_case_prod}) ctxt 
        in
          case try (Goal.prove_internal ctxt' [] prop) (fn _ => Unchanged_Typing.unchanged_typing_tac NONE ctxt' ) of
            NONE => (warning ("unchanged_typing proof failed: " ^ string_of_cterm ctxt prop); NONE)
          | SOME thm => (Monad_Cong_Simp.add_to_cache ctxt thm; SOME thm)
        end
      | (thm::_) => (Utils.verbose_msg 4 ctxt (fn _ => "cache hit: " ^ Thm.string_of_thm ctxt thm); SOME thm)
  in
    fn phi => fn ctxt => fn ct =>
      if Config.get ctxt active orelse (is_assume_stack_alloc ct) then NONE else
      let
        val _ = Utils.verbose_msg 4 ctxt (fn _ => "unchanged_typing_spec_monad invoked on:\n " ^ @{make_string} ct)
      in
        try_prove (Config.put active true ctxt) \<^instantiate>\<open>P = ct in cterm \<open>Trueprop P\<close> for P\<close> 
        |> Option.map (fn thm => prop_to_meta_eq OF [thm])
      end
     
  end
\<close>
declare [[simproc del: unchanged_typing_spec_monad]]

setup \<open>
let
  val (unchanged_typing_simproc_name, _) = 
    Simplifier.check_simproc @{context} ("unchanged_typing_spec_monad", \<^here>)
in
  Context.theory_map (Monad_Cong_Simp.add_simproc unchanged_typing_simproc_name)
end
\<close>

(*
Here the localized version.

context heap_typing_state
begin                                                              

simproc_setup unchanged_typing_spec_monad (\<open>c \<bullet> s ?\<lbrace>\<lambda>r. unchanged_typing_on \<S> s\<rbrace>\<close>  ) = \<open>
  let
    val prop_to_meta_eq = @{lemma \<open>P \<Longrightarrow> (P \<equiv> True)\<close> for P by auto}
    fun try_prove ctxt prop  = try (Goal.prove_internal ctxt [] prop) 
          (fn _ => Unchanged_Typing.unchanged_typing_tac NONE ctxt) 
  in
    fn phi => fn ctxt => fn ct =>
      let
        val _ = Utils.verbose_msg 4 ctxt (fn _ => "unchanged_typing_spec_monad invoked on:\n " ^ @{make_string} ct)
      in
        try_prove ctxt \<^instantiate>\<open>P = ct in cterm \<open>Trueprop P\<close> for P\<close> 
        |> Option.map (fn thm => prop_to_meta_eq OF [thm])
      end
     
  end
\<close>
declare [[simproc del: unchanged_typing_spec_monad]]

text \<open>There seems to be no infrastructure to handle simprocs and morphisms outside 
  of the simpset. We help ourselves by storing the qualified names of the simproc interpretations 
  instead.\<close>

declaration \<open>
let
  val (unchanged_typing_simproc_name, _) = 
    Simplifier.check_simproc @{context} ("unchanged_typing_spec_monad", \<^here>)
  val b = Binding.make (Long_Name.base_name unchanged_typing_simproc_name, \<^here>)
in

fn phi =>
  let
    val b' = Morphism.binding phi b
    val long_name = Long_Name.implode ((map fst (Binding.prefix_of b')) @ [ Binding.name_of b'])
  in
    Monad_Cong_Simp.add_simproc (long_name)
  end


end

\<close>
end

*)


simproc_setup spec_monad_simproc (\<open>f::('a, 'b, 'c) spec_monad\<close>) = \<open>fn _ => fn ctxt => 
  if Monad_Cong_Simp.monad_simp_active ctxt then K NONE else
  Match_Cterm.switch [
   @{cterm_match "STOP _"} #> (fn _ => NONE),
   fn ct => 
     let
       val _ = Utils.verbose_msg 7 ctxt (fn _ => ("spec_monad_simproc:\n " ^ string_of_cterm ctxt ct))
       val eq = Monad_Cong_Simp.gen_monad_conv {stop=true} ctxt ct
       val _ = Utils.verbose_msg 7 ctxt (fn _ => ("spec_monad_simproc eq:\n " ^ Thm.string_of_thm ctxt eq))
     in
        SOME eq
     end]\<close>
declare [[simproc del: spec_monad_simproc]]

ML \<open>
structure Monad_Cong_Simp =
struct
  open Monad_Cong_Simp

fun prepare_simpset max_depth ctxt =
  let
    val {stop_congs, simprocs, ...} = Monad_Cong_Simp.Data.get (Context.Proof ctxt)
    val simprocs' = map (snd o Simplifier.check_simproc ctxt o rpair Position.none) simprocs
    val visible = Context_Position.is_visible ctxt
    val monad_cong_simps = Named_Theorems.get ctxt @{named_theorems monad_simp_simp}
    val run_spec_monad =  Named_Theorems.get ctxt @{named_theorems run_spec_monad}

    val ctxt' = (ctxt |> Context_Position.set_visible false
      |> Simplifier.add_cong @{thm STOP_cong}
      |> fold Simplifier.add_cong stop_congs)
      addsimprocs [@{simproc spec_monad_simproc}, @{simproc monad_run_simproc}] @ simprocs'
      delsimps @{thms return_bind bind_return Spec_Monad.run_case_prod_distrib} @ run_spec_monad
      addsimps monad_cong_simps
      |> Context_Position.set_visible visible
      |> Config.map simp_depth_limit (K (max_depth + 20))
   in ctxt' end

fun monad_simp_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val depth = strip_comb_depth_of_term goal
    val ctxt' = prepare_simpset depth ctxt
  in
    (asm_full_simp_tac ctxt' THEN_ALL_NEW  
     full_simp_tac (Simplifier.clear_simpset ctxt addsimps @{thms STOP_def polish})) i
  end)

fun monad_asm_full_simplify ctxt thm = 
  let
    val depth = strip_comb_depth_of_term (Thm.prop_of thm)
    val ctxt' = prepare_simpset depth ctxt
  in
    thm |> asm_full_simplify ctxt' |>
    full_simplify (Simplifier.clear_simpset ctxt addsimps @{thms STOP_def polish})
  end

fun monad_asm_full_rewrite ctxt ct = 
  let
    val depth = strip_comb_depth_of_term (Thm.term_of ct)
    val ctxt' = prepare_simpset depth ctxt
  in
    ct |> (Simplifier.asm_full_rewrite ctxt' then_conv
    Simplifier.full_rewrite (Simplifier.clear_simpset ctxt addsimps @{thms STOP_def polish}))
  end

fun monad_simplify_def ctxt def_eq =
  let
    val ctxt' = Variable.declare_thm def_eq ctxt
    val ((_, [eq']), ctxt'') = Variable.import true [Thm.transfer' ctxt def_eq] ctxt'
  in
    eq' |> monad_asm_full_simplify ctxt'' |> singleton (Variable.export ctxt'' ctxt') 
    |> zero_var_indexes
  end

end
\<close>

method_setup monad_simp = \<open>Method.sections Simplifier.simp_modifiers >>
    (K (fn ctxt => METHOD (fn facts => HEADGOAL (
        Method.insert_tac ctxt facts THEN' (CHANGED_PROP oo Monad_Cong_Simp.monad_simp_tac) ctxt))))\<close>
  "Simplification for Spec Monad with custom congruence rules"



context open_types_heap_typing_state 
begin
lemma PRESERVED_FACTS_unchanged_typing_ptr_valid_preserved[monad_simp_simp]:
  "reaches f s r t \<Longrightarrow> ptr_valid (heap_typing s) p \<Longrightarrow> f \<bullet> s ?\<lbrace>\<lambda>_ t. unchanged_typing_on UNIV s t\<rbrace> \<Longrightarrow> 
 ptr_valid (heap_typing t) p"
  by (rule reaches_unchanged_typing_ptr_valid_preserved)

lemma PRESERVED_FACTS_WHILE_unchanged_typing_ptr_valid_preserved[monad_simp_simp]:
  assumes reach: "whileLoop_unroll_reachable C B i s r t" 
  assumes valid: "ptr_valid (heap_typing s) p" 
  assumes B: "\<And>r t. C r t \<Longrightarrow> (B r) \<bullet> t ?\<lbrace>\<lambda>_. unchanged_typing_on UNIV t\<rbrace>" 
  shows "ptr_valid (heap_typing t) p"
proof -
  have "unchanged_typing_on UNIV s t"
    using reach
  proof induction
    case (step b t X c u)
    with B[of b t] unchanged_typing_on_trans[of UNIV s t u]
    show ?case
      by (auto simp add: runs_to_partial_holds_partial_def )
  qed simp

  with valid show ?thesis
    by (simp add: unchanged_typing_on_UNIV_iff)
qed

end

lemma PRESERVED_FACTS_run_bind_cong[monad_simp_cong split: g and g']:
  "run f s = run f' s \<Longrightarrow> (\<And>t r. PRESERVED_FACTS f' s (Result r) t \<Longrightarrow> run (g r) t = run (g' r) t) \<Longrightarrow>
  (run (bind f g) s) = (run (bind f' g') s)"
  apply (rule Spec_Monad.run_bind_cong)
   apply (auto simp add:  PRESERVED_FACTS_def runs_to_partial_def_old reaches_def)
  done

lemma ADD_FACT_run_bind_guard_cong[monad_simp_cong]: 
  "P s = P' s \<Longrightarrow> (ADD_FACT P' s \<Longrightarrow> run f s = run f' s) \<Longrightarrow> 
  (run (bind (guard P) (\<lambda>_. f)) s) = (run (bind (guard P') (\<lambda>_. f')) s)"
  apply (simp add: ADD_FACT_def)
  apply (rule run_bind_cong)
   apply (simp add: run_guard)
   apply (auto simp add: run_guard if_split_asm runs_to_partial_def_old)
  done

lemma PRESERVED_FACTS_WHILE_run_whileLoop_cong[monad_simp_cong split: B and B' and C and C']:
  assumes i: "i = i'"
  assumes C_B[unfolded PRESERVED_FACTS_WHILE_def]: 
    "\<And>t r. PRESERVED_FACTS_WHILE C B i s r t  \<Longrightarrow> (C r t \<equiv> C' r t) &&& (C' r t \<Longrightarrow> (run (B r) t \<equiv> run (B' r) t))"
  shows "run (whileLoop C B i) s = run (whileLoop C' B' i') s"
proof -
  from C_B 
  have C: "\<And>r s'. whileLoop_unroll_reachable C B i s r s' \<Longrightarrow> C r s' = C' r s'" by blast
  from C_B
  have B: "\<And>r s'. whileLoop_unroll_reachable C B i s r s' \<Longrightarrow> C' r s' \<Longrightarrow> run (B r) s' = run (B' r) s'"
    by blast
  with C have "\<And>r s'. whileLoop_unroll_reachable C B i s r s' \<Longrightarrow> C r s' \<Longrightarrow> run (B r) s' = run (B' r) s'"
    by simp
  from run_whileLoop_unroll_reachable_cong [OF C this]
  show ?thesis by (simp add: i)
qed

lemma whileLoop_condition_only_cong[monad_simp_split_tuple_cong]: 
  "C = C' \<Longrightarrow> whileLoop C B I = whileLoop C' B I" 
  by simp

lemma PRESERVED_FACTS_run_bind_exception_or_result_cong[monad_simp_cong split: g and g']:
  "run f s = run f' s \<Longrightarrow> (\<And>t r. PRESERVED_FACTS f' s r t \<Longrightarrow> run (g r) t = run (g' r) t) \<Longrightarrow>
  (run (bind_exception_or_result f g) s) = (run (bind_exception_or_result f' g') s)"
  apply (rule Spec_Monad.run_bind_exception_or_result_cong)
   apply (auto simp add:  PRESERVED_FACTS_def runs_to_partial_def_old reaches_def)
  done

lemma PRESERVED_FACTS_run_on_exit'_cong[monad_simp_cong split: g and g']:
  "run f s = run f' s \<Longrightarrow> (\<And>t r. PRESERVED_FACTS f' s r t \<Longrightarrow> run g t = run g' t) \<Longrightarrow>
  (run (on_exit' f g) s) = (run (on_exit' f' g') s)"
  unfolding on_exit'_def
  apply (rule PRESERVED_FACTS_run_bind_exception_or_result_cong)
   apply assumption
  apply (rule PRESERVED_FACTS_run_bind_cong)
   apply assumption
  apply simp
  done

lemma PRESERVED_FACTS_run_on_exit_cong[monad_simp_cong split: g and g']:
  "run f s = run f' s \<Longrightarrow> 
  (\<And>t r. PRESERVED_FACTS f' s r t \<Longrightarrow> run ((state_select g::('e::default, unit, 's) spec_monad)) t = run (state_select g') t) \<Longrightarrow>
  (run (on_exit f g::('e::default, 'a, 's) spec_monad) s) = (run (on_exit f' g') s)"
  unfolding on_exit_def
  apply (rule PRESERVED_FACTS_run_on_exit'_cong)
   apply assumption
  apply simp
  done

lemma ADD_FACT_run_condition_cong [monad_simp_cong]:  
  assumes "c s = c' s"
  assumes "ADD_FACT c' s \<Longrightarrow> run f s = run f' s"
  assumes "ADD_FACT (\<lambda>s. \<not> c' s) s \<Longrightarrow> run g s = run g' s"
  shows "run (condition c f g) s  = run (condition c' f' g') s"
  using assms
  by (auto simp add: ADD_FACT_def run_condition)

lemma ADD_FACT_run_when [monad_simp_cong]:
  assumes "c = c'"
  assumes "ADD_FACT (\<lambda>_. c') s \<Longrightarrow> run f s = run f' s"
  shows "run (when c f) s  = run (when c' f') s"
  using assms
  by (auto simp add: ADD_FACT_def when_def run_condition)

lemma PRESERVED_FACTS_run_catch_cong [monad_simp_cong split: g and g']:
  "run f s = run f' s \<Longrightarrow> (\<And>t e. PRESERVED_FACTS f' s (Exn e) t \<Longrightarrow> run (g e) t = run (g' e) t) \<Longrightarrow>
  (run (catch f g) s) = (run (catch f' g') s)"
  apply (simp add: run_catch PRESERVED_FACTS_def reaches_def)
  apply (rule bind_post_state_cong)
  apply (auto split: xval_splits)
  done

lemma run_finally_cong [monad_simp_cong]:
  assumes "run f s = run f' s"
  shows "run (finally f) s = run (finally f') s"
  using assms
  by (simp add: run_finally)

lemma run_liftE_cong [monad_simp_cong]:
  assumes "run f s = run f' s"
  shows "run (liftE f) s = run (liftE f') s"
  using assms
  by (simp add: run_liftE)

lemma run_guard_cong [monad_simp_cong]:
  assumes "P s = P' s"
  shows "run (guard P) s = run (guard P') s"
  using assms
  by (simp add: run_guard)

lemma run_try_cong [monad_simp_cong]:
  assumes "run f s = run f' s"
  shows "run (try f) s = run (try f') s"
  using assms
  by (simp add: run_try)

lemma run_case_prod_cong[monad_simp_cong]: "RUN_CASE_PROD f x s f' x' \<Longrightarrow>  
     (run (case_prod f x) s) = (run (case_prod f' x') s)"
  by (cases x) (auto simp add: RUN_CASE_PROD_def)

lemma run_bind_when_throw_cong [monad_simp_cong]: 
  "c = c' \<Longrightarrow> e = e' \<Longrightarrow> (ADD_FACT (\<lambda>_. \<not> c') s \<Longrightarrow> run f s = run f' s) \<Longrightarrow> 
  run (bind (when c (throw e)) (\<lambda>_. f)) s = run (bind (when c' (throw e')) (\<lambda>_. f')) s"
  by (auto simp add: ADD_FACT_def)

ML \<open>
Monad_Cong_Simp.print_rules (Context.Proof @{context})
\<close>


lemma with_fresh_stack_ptr_stop_cong [monad_simp_global_stop_cong]: 
  "typ_heap_typing.with_fresh_stack_ptr r w heap_typing heap_typing_upd \<S> n init f \<equiv>
      typ_heap_typing.with_fresh_stack_ptr r w heap_typing heap_typing_upd \<S> n init f"
  by (simp)

lemma assume_with_fresh_stack_ptr_stop_cong [monad_simp_global_stop_cong]: 
  "typ_heap_typing.assume_with_fresh_stack_ptr r w heap_typing heap_typing_upd \<S> n init f \<equiv>
      typ_heap_typing.assume_with_fresh_stack_ptr r w heap_typing heap_typing_upd \<S> n init f"
  by (simp)

lemma guard_with_fresh_stack_ptr_stop_cong [monad_simp_global_stop_cong]: 
  "typ_heap_typing.guard_with_fresh_stack_ptr r w heap_typing heap_typing_upd \<S> n init f \<equiv>
      typ_heap_typing.guard_with_fresh_stack_ptr r w heap_typing heap_typing_upd \<S> n init f"
  by (simp)

context typ_heap_simulation_open_types_stack
begin

lemma PRESERVED_FACTS_assume_stack_alloc_ptr_valid_preserved[monad_simp_simp]:
  "reaches (assume_stack_alloc n init) s x t \<Longrightarrow> ptr_valid (heap_typing s) (p::'b::mem_type ptr) \<Longrightarrow> 
   typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte) \<Longrightarrow>
  ptr_valid (heap_typing t) p"
  apply (clarsimp simp add: stack_ptr_acquire_def heap_typing_fold_upd_write reaches_def 
      assume_stack_alloc_def)
  using stack_allocs_ptr_valid_cases2 by blast

lemma PRESERVED_FACTS_with_fresh_stack_ptr_cong[monad_simp_cong split: f and f' (* rename bound variable *)]:
  fixes f::"'a ptr \<Rightarrow> ('e::default, 'd, 't) spec_monad"
  assumes "\<And>t p. PRESERVED_FACTS (assume_stack_alloc n init::('e::default, 'a ptr, 't) spec_monad) s (Result p) t \<Longrightarrow> 
     run (f p) t = run (f' p) t"
  shows "run (with_fresh_stack_ptr n init f) s = run (with_fresh_stack_ptr n init f') s"
  apply (simp add: with_fresh_stack_ptr_def PRESERVED_FACTS_def ADD_FACT_def)
  apply (rule run_bind_cong)
  subgoal by simp
  subgoal 
    apply (clarsimp simp add: runs_to_partial_def_old on_exit_def on_exit'_def)
    apply (rule run_bind_exception_or_result_cong)
    subgoal
      apply (rule assms)
      apply (simp add: PRESERVED_FACTS_def ADD_FACT_def)
      done 
    subgoal by simp
    done
  done

lemma PRESERVED_FACTS_assume_with_fresh_stack_ptr_cong[monad_simp_cong split: f and f' (* rename bound variable *)]:
  fixes f::"'a ptr \<Rightarrow> ('e::default, 'd, 't) spec_monad"
  assumes "\<And>t p. PRESERVED_FACTS (assume_stack_alloc n init::('e::default, 'a ptr, 't) spec_monad) s (Result p) t \<Longrightarrow> 
     run (f p) t = run (f' p) t"
  shows "run (assume_with_fresh_stack_ptr n init f) s = run (assume_with_fresh_stack_ptr n init f') s"
  apply (simp add: assume_with_fresh_stack_ptr_def PRESERVED_FACTS_def ADD_FACT_def)
  apply (rule run_bind_cong)
  subgoal by simp
  subgoal 
    apply (clarsimp simp add: runs_to_partial_def_old on_exit_def on_exit'_def)
    apply (rule run_bind_exception_or_result_cong)
    subgoal
      apply (rule assms)
      apply (simp add: PRESERVED_FACTS_def ADD_FACT_def)
      done 
    subgoal by simp
    done
  done

lemma PRESERVED_FACTS_guard_with_fresh_stack_ptr_cong[monad_simp_cong split: f and f' (* rename bound variable *)]:
  fixes f::"'a ptr \<Rightarrow> ('e::default, 'd, 't) spec_monad"
  assumes "\<And>t p. PRESERVED_FACTS (assume_stack_alloc n init::('e::default, 'a ptr, 't) spec_monad) s (Result p) t \<Longrightarrow> 
     run (f p) t = run (f' p) t"
  shows "run (guard_with_fresh_stack_ptr n init f) s = run (guard_with_fresh_stack_ptr n init f') s"
  apply (simp add: guard_with_fresh_stack_ptr_def PRESERVED_FACTS_def ADD_FACT_def)
  apply (rule run_bind_cong)
  subgoal by simp
  subgoal 
    apply (clarsimp simp add: runs_to_partial_def_old on_exit_def on_exit'_def)
    apply (rule run_bind_exception_or_result_cong)
    subgoal
      apply (rule assms)
      apply (simp add: PRESERVED_FACTS_def ADD_FACT_def)
      done 
    subgoal by simp
    done
  done

lemma ptr_valid_assume_stack_alloc [monad_simp_derive_rule]:
  "PRESERVED_FACTS (assume_stack_alloc n init::('e::default, 'a ptr, 't) spec_monad) s (Result p) t  \<Longrightarrow> 
   ADD_FACT (\<lambda>t. PTR_VALID('a) (heap_typing t) p) t"
        apply (simp add: PRESERVED_FACTS_def ADD_FACT_def)
        apply (auto simp add: stack_ptr_acquire_def heap_typing_fold_upd_write reaches_def 
            assume_stack_alloc_def root_ptr_valid_ptr_valid elim!: stack_allocs_cases)
        done

end

method array_index_to_ptr_arith_simp uses simp cong =
   (use TrueI[array_bound_mksimps, simproc add: field_lvalue_unfold]
     in \<open>monad_simp 
          simp add:field_lvalue_array_index' simp 
          simp del: field_lvalue_append 
          cong: if_cong cong\<close>)

end
