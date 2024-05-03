(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Nested Exceptions"

theory L2ExceptionRewrite
  imports
  L2Defs
  ExceptionRewrite
begin

synthesize_rules L2_rel_spec_monad

section "Transformations from single level exceptions to nested exceptions"

lemma catch_yield_map_value_conv: "(f <catch> (\<lambda>e. yield (g e))) = 
  (map_value (\<lambda>x. case x of Exn e \<Rightarrow> g e | Result v \<Rightarrow> Result v) f)"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff elim!: runs_to_weaken split: xval_splits)
  done

lemma rel_spec_monad_rel_xval_try_catch:
  assumes bdy: "rel_spec_monad Q (rel_xval (\<lambda>e e'. (rel_sum L R) (from_xval (f e)) e') R) B B'"
  shows "rel_spec_monad Q (rel_xval L R) (L2_catch B (\<lambda>e. yield (f e))) (L2_try B')"
  apply (clarsimp simp add: rel_spec_monad_iff_refines)
  apply (intro conjI)
  subgoal for s t
    using bdy
    apply (clarsimp simp add: rel_spec_monad_iff_refines)
    apply (erule_tac x=s in allE)
    apply (erule_tac x=t in allE)
    apply safe
    unfolding L2_defs try_def catch_yield_map_value_conv
    apply (erule refines_map_value)
    apply (auto simp add: rel_xval.simps rel_sum_simps unnest_exn_def rel_sum.simps)
    done
  subgoal for s t
    using bdy
    apply (clarsimp simp add: rel_spec_monad_iff_refines)
    apply (erule_tac x=s in allE)
    apply (erule_tac x=t in allE)
    apply safe
    unfolding L2_defs try_def catch_yield_map_value_conv
    apply (erule refines_map_value)
    apply (auto simp add: rel_xval.simps rel_sum_simps unnest_exn_def rel_sum.simps)
    done
  done

lemma rel_spec_monad_L2_seq_rel_xval_result_eq:
  assumes f_f': "rel_spec_monad S (rel_xval L (=)) f f'"
  assumes Res_Res: "\<And>v. rel_spec_monad S (rel_xval L (=)) (g v) (g' v)"
  shows "rel_spec_monad S (rel_xval L (=)) (L2_seq f g) (L2_seq f' g')"
  unfolding L2_defs using assms
  by (rule rel_spec_monad_rel_xval_result_eq_bind)

lemma rel_spec_monad_rel_xval_L2_unknown:
 "rel_spec_monad (=) (rel_xval L (=)) (L2_unknown ns) (L2_unknown ns)"
  unfolding L2_unknown_def
  by (auto simp add: rel_spec_monad_def rel_set_def)

lemma rel_spec_monad_rel_xval_L2_modify:
 "rel_spec_monad (=) (rel_xval L (=)) (L2_modify f) (L2_modify f)"
  unfolding L2_modify_def
  by (auto simp add: rel_spec_monad_def rel_set_def)

lemma rel_spec_monad_rel_xval_L2_gets:
 "rel_spec_monad (=) (rel_xval L (=)) (L2_gets f ns) (L2_gets f ns)"
  unfolding L2_gets_def
  by (auto simp add: rel_spec_monad_def rel_set_def)

lemma rel_spec_monad_eq_rel_xval_L2_condition:
  assumes f: "rel_spec_monad (=) (rel_xval L (=)) f f'"
    and g: "rel_spec_monad (=) (rel_xval L (=)) g g'"
  shows "rel_spec_monad (=) (rel_xval L (=)) (L2_condition P f g) (L2_condition P f' g')"
  unfolding L2_condition_def
  apply (rule rel_spec_monad_condition [OF _ f g])
  apply (auto simp add: rel_fun_def)
  done

lemma rel_spec_monad_L2_throw_sanitize_names:
  assumes xy: "R (Exn x) (Exn y)"
  assumes ns': "SANITIZE_NAMES y ns ns'"
  shows "rel_spec_monad (=) R (L2_throw x ns) (L2_throw y ns')"
  unfolding L2_throw_def
  using xy
  by (auto simp add: rel_spec_monad_def rel_set_def)

lemma rel_spec_monad_rel_xval_L2_spec:
 "rel_spec_monad (=) (rel_xval L (=)) (L2_spec r) (L2_spec r)"
  unfolding L2_spec_def
  apply (rule rel_spec_monad_rel_xval_bind [where P="(=)"])
  subgoal by (auto simp add: rel_spec_monad_def rel_set_def run_assert_result_and_state)
  subgoal by (auto simp add: rel_spec_monad_def rel_set_def)
  done

lemma rel_spec_monad_rel_xval_L2_assume:
 "rel_spec_monad (=) (rel_xval L (=)) (L2_assume r) (L2_assume r)"
  unfolding L2_assume_def
  by (auto simp add: rel_spec_monad_def rel_set_def split: prod.splits )

lemma rel_spec_monad_rel_xval_L2_guard:
 "rel_spec_monad (=) (rel_xval L (=)) (L2_guard c) (L2_guard c)"
  unfolding L2_guard_def
  by (auto simp add: rel_spec_monad_def rel_set_def run_guard)

lemma rel_spec_monad_rel_xval_L2_guarded:
  assumes c_c': "rel_spec_monad (=) (rel_xval L (=)) c c'"
  shows "rel_spec_monad (=) (rel_xval L (=)) (L2_guarded g c) (L2_guarded g c')"
  unfolding L2_guarded_def
  apply (rule rel_spec_monad_L2_seq_rel_xval_result_eq)
   apply (rule rel_spec_monad_rel_xval_L2_guard)
  apply (rule c_c')
  done

lemma rel_spec_monad_L2_fail:
 "rel_spec_monad Q R (L2_fail) (L2_fail)"
  unfolding L2_fail_def
  by (rule rel_spec_monad_fail)

lemma rel_spec_monad_rel_xval_L2_call:
  assumes emb: "\<And>e. L (emb e) (emb' e)"
  assumes ns': "SANITIZE_NAMES emb' ns ns'"
  shows "rel_spec_monad (=) (rel_xval L (=)) (L2_call f emb ns) (L2_call f emb' ns')"
  unfolding L2_call_def
  using emb
  by (auto simp: rel_spec_monad_iff_rel_spec rel_spec_map_value_right_iff
                 rel_spec_map_value_left_iff map_exn_def
           split: xval_split
           intro!: rel_spec_refl)

lemma rel_fun_eq_refl: "rel_fun (=) (=) f f"
  by (rule rel_funI) simp


lemma rel_spec_monad_result_exec_concrete:
  assumes m_m': "rel_spec_monad (=) R m m'"
  shows "rel_spec_monad (=) R (exec_concrete st m) (exec_concrete st m')"
  apply (clarsimp simp add: rel_spec_monad_iff_refines, intro conjI)
  subgoal for s
    using m_m' 
    by (fastforce simp add: rel_spec_monad_iff_refines refines_def_old succeeds_exec_concrete_iff reaches_exec_concrete)
  subgoal for s
    using m_m' 
    by (fastforce simp add: rel_spec_monad_iff_refines refines_def_old succeeds_exec_concrete_iff reaches_exec_concrete)
  done

lemma rel_spec_monad_result_exec_abstract:
  assumes m_m': "rel_spec_monad (=) R m m'"
  shows "rel_spec_monad (=) R (exec_abstract st m) (exec_abstract st m')"
  apply (clarsimp simp add: rel_spec_monad_iff_refines, intro conjI)
  subgoal for s
    using m_m' 
    by (auto simp add: rel_spec_monad_iff_refines refines_def_old succeeds_exec_abstract_iff reaches_exec_abstract)
  subgoal for s
    using m_m' 
    by (auto simp add: rel_spec_monad_iff_refines refines_def_old succeeds_exec_abstract_iff reaches_exec_abstract)
  done

lemma rel_spec_monad_rel_project_L2_unknown':
  assumes surj_prj: "surj prj"
  assumes names: "SANITIZE_NAMES prj ns ns'"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_unknown ns) (L2_unknown ns')"
  unfolding L2_unknown_def
  using surj_prj
  by (auto simp add: rel_spec_monad_def rel_set_def rel_project_def)
 

text \<open>Note that @{term prj} is the identity function on unit here\<close>
lemma rel_spec_monad_rel_project_L2_modify:
 "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_modify f) (L2_modify f)"
  unfolding L2_modify_def
  by (auto simp add: rel_spec_monad_def rel_set_def rel_project_def)

lemma rel_spec_monad_rel_project_L2_gets':
  assumes g: "\<And>x. g x = prj (f x)"
  assumes names: "SANITIZE_NAMES prj ns ns'"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_gets f ns) (L2_gets g ns')"
  unfolding L2_gets_def g
  by (auto simp add: rel_spec_monad_def rel_set_def rel_project_def)

lemma rel_spec_monad_rel_project_L2_condition:
  assumes f: "rel_spec_monad (=) (rel_xval L (rel_project prj)) f f'"
  assumes g: "rel_spec_monad (=) (rel_xval L (rel_project prj)) g g'"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_condition c f g) (L2_condition c f' g')"
  unfolding L2_condition_def
  apply (rule rel_spec_monad_condition [OF _ f g])
  apply (auto simp add: rel_fun_def)
  done

lemma rel_spec_monad_rel_project_L2_throw:
  assumes x_xs: "L x y"
  assumes names: "SANITIZE_NAMES (L, x) ns ns'"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_throw x ns) (L2_throw y ns')"
  unfolding L2_throw_def using x_xs
  by (auto simp add: rel_spec_monad_def rel_set_def rel_project_def)

lemma rel_spec_monad_rel_project_L2_spec:
  assumes prj_surj: "surj prj"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_spec r) (L2_spec r)"
  unfolding L2_spec_def
  apply (rule rel_spec_monad_rel_xval_bind [where P="(=)"])
  subgoal by (auto simp add: rel_spec_monad_def rel_set_def run_assert_result_and_state)
  subgoal using prj_surj by (auto simp add: rel_spec_monad_def rel_set_def rel_project_def)
  done

lemma rel_spec_monad_rel_project_L2_assume:
  shows "rel_spec_monad (=) (rel_xval L (=)) (L2_assume r) (L2_assume r)"
  unfolding L2_assume_def
  by (auto simp add: rel_spec_monad_def rel_set_def split: prod.splits)

lemma rel_spec_monad_rel_project_L2_guard:
 "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_guard c) (L2_guard c)"
  unfolding L2_guard_def
  by (auto simp add: rel_spec_monad_def rel_set_def run_guard rel_project_def)

lemma rel_spec_monad_rel_project_L2_seq:
  assumes m_n: "rel_spec_monad (=) (rel_xval L (rel_project prj')) m n"
  assumes f_g: "\<And>x. rel_spec_monad (=) (rel_xval L (rel_project prj)) (f x) (g (prj' x))"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_seq m f) (L2_seq n g)"
  unfolding L2_seq_def
  apply (rule rel_spec_monad_rel_xval_bind [OF m_n])
  using f_g
  by (simp add: rel_project_conv)


lemma rel_spec_monad_rel_project_L2_guarded:
  assumes c_c': "rel_spec_monad (=) (rel_xval L (rel_project prj)) c c'"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_guarded g c) (L2_guarded g c')"
  unfolding L2_guarded_def L2_seq_def
  apply (rule rel_spec_monad_rel_xval_bind [where P="(=)"])
   apply (rule  rel_spec_monad_rel_xval_L2_guard)
  apply (rule c_c')
  done

lemma rel_spec_monad_rel_project_L2_try:
  assumes fg: "rel_spec_monad (=) (rel_xval (rel_sum L (rel_project prj)) (rel_project prj)) f g"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_try f) (L2_try g)"
  unfolding L2_try_def
  apply (clarsimp simp add: rel_spec_monad_iff_refines, intro conjI)
  subgoal for s
    using fg 
    apply (clarsimp simp add: rel_spec_monad_iff_refines refines_def_old succeeds_try reaches_try )
    apply (erule_tac x=s in allE)
    apply clarsimp
    subgoal for s' r'
      apply (erule_tac x=r' in allE)
      apply (erule_tac x=s' in allE)
      apply clarsimp
      subgoal for x
        apply (cases x)
        subgoal apply (clarsimp simp add: Exn_def [symmetric] default_option_def)
          by (smt (verit, best) Exn_neq_Result rel_sum.simps rel_xval.simps 
              unnest_exn_simps(1) unnest_exn_simps(2))
        subgoal 
          apply (clarsimp simp add: Exn_def [symmetric] default_option_def)
          by (smt (verit, best) Result_neq_Exn rel_xval.simps unnest_exn_simps(3))
        done
      done
    done
  subgoal for s
    using fg 
    apply (clarsimp simp add: rel_spec_monad_iff_refines refines_def_old succeeds_try reaches_try)
    apply (erule_tac x=s in allE)
    apply clarsimp
    subgoal for s' r'
      apply (erule_tac x=r' in allE)
      apply (erule_tac x=s' in allE)
      apply clarsimp
      subgoal for x
        apply (cases x)
        subgoal apply (clarsimp simp add: Exn_def [symmetric] default_option_def)
          by (smt (verit, best) Exn_neq_Result rel_sum.simps rel_xval.simps 
              unnest_exn_simps(1) unnest_exn_simps(2))
        subgoal 
          apply (clarsimp simp add: Exn_def [symmetric] default_option_def)
          by (smt (verit, best) Result_neq_Exn rel_xval.simps unnest_exn_simps(3))
        done
      done
    done
  done

text \<open>Tailored projection for local handler functions that may emerge in IO phase to handle exit case.
These handlers are composed from liftE functions followed by rethrowing the exception. We do
not attempt to optimise projections for the handlers.\<close>
lemma rel_spec_monad_rel_project_L2_catch:
  assumes f: "rel_spec_monad (=) (rel_xval (=) (rel_project prj)) f f'"
  assumes g: "\<And>v. (rel_spec_monad (=) (rel_xval L (\<lambda>_ _. False))) (g v) (g v)"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_catch f g) (L2_catch f' g)"
  unfolding L2_catch_def
  apply (rule rel_spec_monad_rel_xval_catch [OF f])
  using g using rel_fun_def rel_spec_monad_mono
  by (smt (verit, del_insts) Exn rel_xval.cases)


lemma rel_spec_monad_rel_project_liftE:
  assumes f: "rel_spec_monad (=) (rel_map the_Res OO rel_project prj OO rel_map Result) f f'"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (liftE f) (liftE f')"
  using assms
  apply (clarsimp simp add: rel_spec_monad_iff_refines, intro conjI)
  subgoal for s
    using f
    apply (clarsimp simp add: rel_spec_monad_iff_refines refines_def_old  reaches_liftE )
    apply (erule_tac x=s in allE)
    apply clarsimp
    subgoal for s' r'
      apply (erule_tac x=r' in allE)
      apply (erule_tac x=s' in allE)
      by (metis rel_map_def rel_xval.Result relcomppE the_Result_simp)
    done
  subgoal for s
    using f
    apply (clarsimp simp add: rel_spec_monad_iff_refines refines_def_old  reaches_liftE )
    apply (erule_tac x=s in allE)
    apply clarsimp
    subgoal for s' r'
      apply (erule_tac x=r' in allE)
      apply (erule_tac x=s' in allE)
      by (metis rel_map_def rel_xval.Result relcomppE the_Result_simp)
    done
  done

lemma rel_project_Res_conv: 
  "(rel_map the_Res OO rel_project prj OO rel_map Result) = (rel_project (Result o prj o the_Res))"
  apply (intro ext)
  apply (simp add: rel_map_def rel_project_def relcompp.simps)
  done


lemma rel_spec_monad_rel_project_id:
  shows "rel_spec_monad (=) (rel_project (\<lambda>v. v)) f f"
  by (simp add: rel_project_id(2) rel_spec_monad_eq_conv)


lemma rel_spec_monad_rel_project_unit:
  fixes f:: "(unit, 's) res_monad"
  shows "rel_spec_monad (=) (rel_project (\<lambda>v. Result ())) f f"
  using rel_spec_monad_rel_project_id
  by (metis Result_unit_eq rel_projectI rel_spec_monad_mono)

lemma rel_spec_monad_rel_project_liftE_unit_id: 
  shows "rel_spec_monad (=) (rel_xval L (rel_project (prj::unit \<Rightarrow> unit))) (liftE f) (liftE f)"
  apply (rule rel_spec_monad_rel_project_liftE)
  apply (simp add: rel_project_Res_conv comp_def rel_spec_monad_rel_project_unit)
  done

lemma rel_project_unit_eq: "(rel_project (prj::unit \<Rightarrow> unit)) = (=)"
  apply (rule ext)+
  apply (auto simp add: rel_project_def)
  done

lemma rel_spec_monad_L2_seq_rel_xval_same_split:
  assumes mn:  "rel_spec_monad R (rel_xval L (=)) m n"
    and fg: "\<And>x. (rel_spec_monad R (rel_xval L (=))) (f x) (g x)"
  shows "rel_spec_monad R (rel_xval L (=)) (L2_seq m f) (L2_seq n g)"
  using assms
  by (rule rel_spec_monad_L2_seq_rel_xval_result_eq)


lemma rel_spec_monad_L2_while_rel_xval_same_split:
assumes B: "\<And>x. (rel_spec_monad (=) (rel_xval L (=))) (B x) (B' x)"
shows "rel_spec_monad (=) (rel_xval L (=)) (L2_while C' B I' ns) (L2_while C' B' I' ns)"
  unfolding L2_while_def
  apply (rule rel_spec_monad_whileLoop_exn)
    apply (auto simp add: B)
  done

lemma rel_spec_monad_rel_project_L2_call_adapt_emb:
  assumes L: "\<And>x. L (emb x) (emb' x)"
  assumes prj: "\<And>v. prj v = v"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_call x emb ns) (L2_call x emb' ns)"
  unfolding L2_call_def
  using prj L
  apply (auto simp: map_exn_def rel_project_def
        rel_spec_monad_iff_rel_spec rel_spec_map_value_left_iff rel_spec_map_value_right_iff 
      split: xval_splits
      intro!: rel_spec_refl)
  done

lemma rel_spec_monad_liftE_id:  "rel_spec_monad (=) (rel_xval (\<lambda>_ _. False) (=)) (liftE f) (liftE f)"
  by (auto simp add: rel_spec_monad_iff_refines refines_def_old reaches_liftE rel_xval.simps)


lemma rel_spec_monad_L2_seq_exit_handler:
  assumes "\<And>v. rel_spec_monad (=) (rel_xval L (\<lambda>_ _. False)) (g v) (g' v)"
  shows "rel_spec_monad (=) (rel_xval L (\<lambda>_ _. False)) (L2_seq (liftE f) g) (L2_seq (liftE f) g')"
  unfolding L2_defs
  apply (rule rel_spec_monad_bind_strong_exn [OF rel_spec_monad_liftE_id])
     apply (auto simp add: assms)
  done

lemma rel_spec_monad_rel_project_L2_while':
  assumes C_C': "\<And>v s. C v s = C' (prj v) s"
  assumes I': "I' = prj I"
  assumes names: "SANITIZE_NAMES prj ns ns'"
  assumes B_B': "\<And>v. rel_spec_monad (=) (rel_xval L (rel_project prj)) (B v) (B' (prj v))"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (L2_while C B I ns) (L2_while C' B' I' ns')"
  unfolding L2_while_def
  apply (rule rel_spec_monad_whileLoop_exn)
  subgoal using I' by (auto simp add: rel_project_def)
  subgoal using C_C' by (auto simp add: rel_fun_def rel_project_def)
  subgoal using B_B' by (auto simp add: rel_project_def)
  done

lemma rel_spec_monad_rel_xval_on_exit:
  assumes c_c': "rel_spec_monad (=) (rel_xval L (=)) c c'"
  shows "rel_spec_monad (=) (rel_xval L (=)) (on_exit c cleanup) (on_exit c' cleanup)"
  unfolding on_exit_bind_exception_or_result_conv thm rel_spec_monad_bind_exception_or_result_strong
  apply (rule rel_spec_monad_bind_exception_or_result_strong [OF c_c'] )
  apply (rule rel_spec_monad_bind_strong_exn [where P="rel_xval (\<lambda>_ _. False) (=)"])
  subgoal 
    apply (subst (1 2) liftE_state_select [symmetric])
    apply (rule rel_spec_monad_liftE_id)
    done
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp add: rel_spec_monad_yield)
  done

lemma (in stack_heap_raw_state) rel_spec_monad_rel_xval_with_fresh_stack_ptr:
  assumes c: "\<And>p. rel_spec_monad (=) (rel_xval L (=)) (c p) (c' p)"
  shows "rel_spec_monad (=) (rel_xval L (=)) (with_fresh_stack_ptr n init (L2_VARS c nm)) (with_fresh_stack_ptr n init (L2_VARS c' nm))"
  unfolding with_fresh_stack_ptr_def L2_VARS_def
  apply (rule rel_spec_monad_bind_strong_exn [where P="rel_xval (\<lambda>_ _. False) (=)"])
  subgoal 
    apply (subst (1 2) liftE_assume_result_and_state [symmetric])
    apply (rule rel_spec_monad_liftE_id)
    done
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (simp add: rel_spec_monad_rel_xval_on_exit c)
  done

lemma rel_spec_monad_rel_project_on_exit:
  assumes c_c': "rel_spec_monad (=) (rel_xval L (rel_project prj)) c c'"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (on_exit c cleanup) (on_exit c' cleanup)"
  unfolding on_exit_bind_exception_or_result_conv  unfolding on_exit_def
  apply (rule rel_spec_monad_bind_exception_or_result_strong [OF c_c'] )
  apply (rule rel_spec_monad_bind_strong_exn [where P="rel_xval (\<lambda>_ _. False) (=)"])
  subgoal 
    apply (subst (1 2) liftE_state_select [symmetric])
    apply (rule rel_spec_monad_liftE_id)
    done
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp add: rel_spec_monad_yield)
  done

lemma (in stack_heap_raw_state) rel_spec_monad_rel_project_with_fresh_stack_ptr:
  assumes c: "\<And>p. rel_spec_monad (=) (rel_xval L (rel_project prj)) (c p) (c' p)"
  shows "rel_spec_monad (=) (rel_xval L (rel_project prj)) (with_fresh_stack_ptr n init (L2_VARS c nm)) (with_fresh_stack_ptr n init (L2_VARS c' nm))"
  unfolding with_fresh_stack_ptr_def L2_VARS_def
  apply (rule rel_spec_monad_bind_strong_exn [where P="rel_xval (\<lambda>_ _. False) (=)"])
  subgoal 
    apply (subst (1 2) liftE_assume_result_and_state [symmetric])
    apply (rule rel_spec_monad_liftE_id)
    done
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (simp add: rel_spec_monad_rel_project_on_exit c)
  done

lemma rel_spec_monad_L2_VARS:
  assumes f_f': "rel_spec_monad P Q f f'"
  shows "rel_spec_monad P Q (L2_VARS f ns) (L2_VARS f' ns)"
  unfolding L2_VARS_def
  by (rule f_f')

lemma cond_return1: "(\<lambda>a.
            L2_condition (\<lambda>s. P a) (L2_gets (\<lambda>s. f a) ns)
               (L2_throw (g a) xs)) =
(\<lambda>a. yield (if P a then Result (f a ) else (Exn (g a))))"
  unfolding L2_defs
  apply (rule ext)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


lemma cond_return2: "(\<lambda>(a, b).
            L2_condition (\<lambda>s. P a b) (L2_gets (\<lambda>s. f a b) ns)
               (L2_throw (g a b) xs)) =
(\<lambda>(a, b). yield (if P a b then Result (f a b) else (Exn (g a b))))"
  unfolding L2_defs
  apply (rule ext)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


lemma rel_spec_monad_rel_xvalI:
"rel_spec_monad R (rel_xval (=) (=)) f g \<Longrightarrow> rel_spec_monad R (=) f g"
  by (simp add: rel_xval_eq)

(* *********************************************************************** *)


lemma is_local_split: "((is_local a \<longrightarrow> e = Result b) \<and> (\<not> is_local a \<longrightarrow> e = Exn (the_Nonlocal a)))
 =
 (case a of Nonlocal x \<Rightarrow> e = Exn x | _ \<Rightarrow> e = Result b)"
  by (cases a) auto

lemma is_local_splitI :
  "(case a of Nonlocal x \<Rightarrow> e = Exn x | _ \<Rightarrow> e = Result b) \<Longrightarrow>
  ((is_local a \<longrightarrow> e = Result b) \<and> (\<not> is_local a \<longrightarrow> e = Exn (the_Nonlocal a)))"
  apply (simp add: is_local_split)
  done

lemma if_is_local_cases: "(if is_local e then f else g) = (case e of Nonlocal x \<Rightarrow> g | _ \<Rightarrow> f)"
  by (cases e) auto

lemma if_Break_cases: "(if e = Break then f else g) = (case e of Break \<Rightarrow> f | _ \<Rightarrow> g)"
  by (cases e) auto

lemma if_Continue_cases: "(if e = Continue then f else g) = (case e of Continue \<Rightarrow> f | _ \<Rightarrow> g)"
  by (cases e) auto

lemma if_Return_cases: "(if e = Return then f else g) = (case e of Return \<Rightarrow> f | _ \<Rightarrow> g)"
  by (cases e) auto


lemmas if_c_exntype_cases =
  if_is_local_cases if_Break_cases if_Continue_cases if_Return_cases


lemmas  case_sum_c_exntype_swap = c_exntype.case_distrib


lemma ex_c_enxtype_cases_distrib:  "(\<exists>a. P a \<and>
               (case e of Break \<Rightarrow> brk a | Continue \<Rightarrow> cnt a | Return \<Rightarrow> ret a | Goto l \<Rightarrow> goto l a
                |  Nonlocal gx \<Rightarrow> nonlocal gx a)) =
(case e of Break \<Rightarrow> \<exists>a. P a \<and> brk a | Continue \<Rightarrow> \<exists>a. P a \<and> cnt a | Return \<Rightarrow> \<exists>a. P a \<and> ret a
                | Goto l \<Rightarrow> \<exists>a. P a \<and> goto l a

                |  Nonlocal gx \<Rightarrow> \<exists>a. P a \<and> nonlocal gx a)
"
  by (auto split: c_exntype.splits)




section \<open>Transformations for procedure local exceptions\<close>

text \<open>Introduce constant for relations to avoid higher order patterns in term net for rules\<close>




subsection "Transformations for @{const try} and @{const finally}"

section \<open>Transformations on global exceptions\<close>
definition
  lift_exit_status :: "('e, 'a, 's) exn_monad \<Rightarrow> ('e c_exntype, 'a, 's) exn_monad"
where
  "lift_exit_status f \<equiv> map_value (map_exn Nonlocal) f"



subsection \<open>Removing unused tuple components\<close>


lemma rel_project_eqI: "rel_spec_monad (=) (rel_xval (=) (rel_project (ETA_TUPLED (\<lambda>v. v)))) f g \<Longrightarrow> f = g"
  by (simp add: rel_project_id rel_xval_eq rel_spec_monad_eq_conv ETA_TUPLED_def)



subsection \<open>Setup basic rules\<close>


lemma rel_xval_case_Nonlocal_sameI:
  assumes L: "\<And>v. e = Nonlocal v \<Longrightarrow> L (Nonlocal v) (Nonlocal v)"
  assumes R: "is_local e \<Longrightarrow>  R v v'"
  shows "rel_xval L R (case e of Nonlocal x \<Rightarrow> Exn (Nonlocal x) | _ \<Rightarrow> Result v)
          (case e of Nonlocal x \<Rightarrow> Exn (Nonlocal x) | _ \<Rightarrow> Result v')"
  using L R
  by (auto split: c_exntype.splits)

lemma  rel_sum_map_sum_InlI: "L (l x) v \<Longrightarrow> rel_sum L R (map_sum l r (Inl x)) (Inl v)"
  by (auto)

lemma  rel_sum_map_sum_InrI: "R (r x) v \<Longrightarrow> rel_sum L R (map_sum l r (Inr x)) (Inr v)"
  by (auto)

lemma  rel_map_xval_xval_ExnI: "L (l x) v \<Longrightarrow> rel_xval L R (map_xval l r (Exn x)) (Exn v)"
  by (auto)

lemma  rel_map_xval_xval_ResultI: "R (r x) v \<Longrightarrow> rel_xval L R (map_xval l r (Result x)) (Result v)"
  by (auto)

ML \<open>
structure Rel_Spec_Monad_Synthesize_Rules =
struct

fun gen_number_bounds len [] = []
  | gen_number_bounds len (x::xs) = ((len, []), x):: gen_number_bounds (len - 1) xs;

fun number_bounds xs = gen_number_bounds (length xs - 1) xs

exception Incompatible_Use
(* Note that we only perform inner procedural analysis. Hence an global exception (i.e.
 * all constructors are Inl and there is no final Inr) are irrelevant for the analysis
 *)
datatype result = Inl of result | Inr of int (* position in tuple, from left to right, starting with 1 *)
datatype uses = Unused | Used | Propagated of result list

local
fun inc_bound n (i, aliases) = (i + n, map (fn i => i + n) aliases)
fun inc_bounds n = map (fn (b, x) => (inc_bound n b, x))
fun add_alias i (b, aliases) = (b, i::aliases)

fun gen_number_pos n [] = []
  | gen_number_pos n (x::xs) = (n, x)::gen_number_pos (n + 1) xs
val number_pos = gen_number_pos 1

fun eq_bound (b, aliases) i = member (op =) (b::aliases) i
fun same_bound (b1, aliases1) (b2, aliases2) = not (null (inter (op =) (b1::aliases1) (b2::aliases2)))

fun propagation (Propagated _) = true
  | propagation _ = false

fun merge_result (Inr x) (Inr y) = if x = y then [Inr x] else [Inr x, Inr y]
  | merge_result (Inl x) (Inl y) = map Inl (merge_result x y)
  | merge_result x y = [x, y]

fun pop_result (Inl x) = [x]
  | pop_result _ = []

fun merge_uses Unused x = x
  | merge_uses x Unused = x
  | merge_uses Used x = Used
  | merge_uses x Used = Used
  | merge_uses (Propagated rs) (Propagated rs') =
     Propagated (fold (fn res => fn rsx => flat (map (merge_result res) rsx)) rs' rs)

fun returned (Propagated rs) = get_first (fn Inr x => SOME x | _ => NONE) rs
  | returned _ = NONE

fun remove_return (Propagated rs) =
     let val rs' = filter_out (fn Inr x => true  | _ => false) rs
     in if null rs' then Unused else Propagated rs' end
  | remove_return x = x

fun return_to_used (Propagated rs) =
     if exists (fn Inr x => true  | _ => false) rs then Used else Propagated rs
  | return_to_used x = x

fun handled (Propagated rs) = Propagated (flat (map pop_result rs))
  | handled x = x

fun analyse_result bounds constr pos propagate t =
  case t of
    (Bound i) => map (fn (b, _) =>
       if eq_bound b i
       then if propagate then Propagated [constr pos] else Used
       else Unused) bounds
  | (t1 $ t2) =>
      let
        val rs1 = analyse_result bounds constr pos false t1
        val rs2 = analyse_result bounds constr pos false t2
      in map2 merge_uses rs1 rs2 end
  | _ => map (K Unused) bounds

fun analyse_used bounds = analyse_result bounds Inr 0 false

fun merge_results uss = foldl1 (uncurry (map2 merge_uses)) uss

fun merge_results_default d uss = if null uss then d else merge_results uss

fun propagate_returns off = map2 (fn (b, x) => fn r =>
   (case returned r of SOME p => inc_bound off b |> add_alias (off - p) | _ => inc_bound off b, x))

fun merge_while_cond_bdy new_pos cond_uses bdy_uses = bdy_uses |> map (fn r =>
  case returned r of
    SOME p => merge_uses (nth cond_uses (new_pos p)) r
  | NONE => r)

datatype exn_constr = L | R
fun dest_throw_value (Const (@{const_name "Inl"}, _) $ x) =
      let val (constrs, bdy) = dest_throw_value x in (L :: constrs, bdy) end
  | dest_throw_value (Const (@{const_name "Inr"}, _) $ x) =
      let val (constrs, bdy) = dest_throw_value x in (R :: constrs, bdy) end
  | dest_throw_value x = ([], x)

fun local_exn cs = (List.last cs = R)
fun mk_exn [R] x = Inr x
  | mk_exn (c::cs) x = ((case c of L => Inl | _ => raise Incompatible_Use) o mk_exn cs) x

fun extend_bounds xs base =
  let
    fun ext x base = if not (member (fn (x, y) => same_bound (fst x) (fst y)) base x) then base @ [x] else base
  in
    fold ext xs base
  end

exception Done of uses list

fun fold_done done f xs a =
  fold (fn x => fn a =>
    let
      val res = f x a
    in
      if done res then raise Done res else res
    end) xs a


fun fold_sup inf f xs =
  fold_done (forall (fn u => u = Used)) f xs inf

fun fold_merge inf bounds f = fold_sup (inf bounds) (fn x => fn a => merge_results [a, f bounds x])

in
(*
analyse_uses bounds t: returns the list of usages corresponding to the list of input bounds.
each input bound is represented as ((de bruijn index, [aliases]), (name, type))
The position in the list corresponds to the position in the tuple of the binding.
Special care has to be taken to handle L2_while as this may shuffle the tuple and introduce
various aliases in the initalisation expression, the condition and the body.
*)
fun analyse_uses bounds t =
  let
    val sup = map (K Used) bounds
    val inf = map (K Unused)
    val done = forall (fn u => u = Used)
    fun fastpath uses = if done uses then raise Done uses else ()
    val fold_merge = fold_merge inf
    fun analyse bounds t =
       \<comment> \<open>We do not handle @{const L2_catch} only @{const L2_try} as this analysis is supposed to
          happen after replacing @{const L2_catch} by @{const L2_try}. After phase IO the freshly
          emerging @{const L2_catch} are only very local handler functions which we do not attempt to optimise\<close>
      case t of
        Const (@{const_name "L2_gets"}, _) $ Abs (_, _, bdy) $ _ =>
          let
            val bounds = inc_bounds 1 bounds
            val vars = HOLogic.strip_tuple bdy |> number_pos
            val uss = map (fn (pos, t) => analyse_result bounds Inr pos true t) vars
          in
            merge_results_default (inf bounds) (* i.e. () is returned *) uss
          end
      | Const (@{const_name "L2_throw"}, _) $ t1 $ _ =>
          let
            val (constrs, bdy) = dest_throw_value t1
            val vars = HOLogic.strip_tuple bdy |> number_pos
            val uss = map (fn (pos, t) => analyse_result bounds (mk_exn (L::constrs)) pos (local_exn (L::constrs)) t) vars
          in
            merge_results_default (inf bounds) (* e.g. if Inr () is thrown *) uss
          end
      | Const (@{const_name "L2_seq"}, _) $ t1 $ t2 =>
          let
            val uses1 = analyse bounds t1
            val _ = fastpath uses1
            val (off, bdy) = (Synthesize_Rules.strip_abs_prod t2) |>> length
            val bounds' = propagate_returns off bounds uses1
            val uses2 = analyse bounds' bdy
          in
            merge_results [map remove_return uses1, uses2]
          end
      | Const (@{const_name "L2_try"}, _) $ t1  =>
          let
            val uses1 = analyse bounds t1
            val handled_uses = map handled uses1
          in
            handled_uses
          end
      | Const (@{const_name "L2_while"}, _) $ c $ bdy $ vars $ _ =>
          let
            val n = length bounds
            val vars = HOLogic.strip_tuple vars |> number_pos
            val off = length vars
            val uses_vars = map (fn (pos, t) => analyse_result bounds Inr pos true t) vars
              |> merge_results_default (inf bounds)
            val (cond_bounds, cond_bdy) = Synthesize_Rules.strip_abs_prod c |>> number_bounds
                (* extend bounds to cover at least the arity of cond and body, strip in the end *)
            val bounds' = propagate_returns off bounds uses_vars |> extend_bounds cond_bounds
            val uses_cond = analyse bounds' cond_bdy
            val _ = @{assert} (forall (not o propagation) uses_cond)
            fun new_pos p =
              let val i = nth cond_bounds (p - 1) |> #1 |> #1
              in find_index (fn (b, _) => eq_bound b i) bounds' end
            val _ = fastpath uses_cond
            val (_, bdy) = Synthesize_Rules.strip_abs_prod bdy
            val uses_bdy = analyse bounds' bdy
            val cond_bdy = merge_while_cond_bdy new_pos uses_cond uses_bdy
            val res = merge_results [uses_vars, take n uses_cond, take n cond_bdy]
          in
            res
          end
      | Const (@{const_name "L2_unknown"}, _) $ _ => inf bounds
      | Const (@{const_name "L2_call"}, _) $ f $ emb $ _ =>
          fold_merge bounds analyse [f, emb]
      | t1 $ t2 =>
          fold_merge bounds analyse [t1, t2]
      | Abs (_, _, bdy) => analyse_uses (inc_bounds 1 bounds) bdy
      | leaf => analyse_used bounds leaf;
  in
    analyse bounds t
    handle Done _ => sup
  end

fun mk_tuple [] = (HOLogic.unit, HOLogic.unitT)
  | mk_tuple [((i, _), (_, T))] = (Bound i, T)
  | mk_tuple (((i, _), (_, T)):: xs) =
    let
      val (t, T') = mk_tuple xs
    in (HOLogic.pair_const T T' $ Bound i $ t, HOLogic.mk_prodT (T, T')) end

fun result_from_rel prj_rel res =
  case (res, prj_rel) of
    (Inr p, @{term_pat "rel_sum _ (rel_project ?prj)"}) =>
        ((nth (Synthesize_Rules.arity_from_projection prj) (p - 1))
        handle Subscript  => raise TERM ("prj_from_rel: cannot infer projection " ^ @{make_string} (p, prj),  [prj, prj_rel]))
  | (Inr _, @{term_pat "rel_sum _ (=)"}) => true
  | (Inr _, @{term_pat "(=)"}) => true
  | (Inl l, @{term_pat "rel_sum ?L1 _"}) => result_from_rel L1 l
  | _ => raise TERM ("prj_from_rel: result '" ^ @{make_string} res ^ "' cannot be extracted", [prj_rel])



fun prj_of_uses prj_rel us = us |> map (fn u =>
  case u of
    Used => true
  | Unused => false
  | Propagated rs => exists (result_from_rel prj_rel) rs) (* Value propagated until end but still used as a result *)

local
val merge_prj = map2 (fn b1 => fn b2 => b1 orelse b2)
in
(*
A while loop in itself might have dependencies of the bound variables between the body and
the condition. These dependencies should not be optimised away even if the value is no longer used
after the while loop.
*)
fun constrain_projection prj_rel prj t =
  case t of
    Const (@{const_name "L2_seq"},_) $ t1 $ t2 => constrain_projection prj_rel prj t2
  | Const (@{const_name "L2_call"},_) $ _ $ _ $ _ => map (K true) prj
        (* As we don't recurse into body, preserve result type of call *)
  | Const (@{const_name "L2_condition"},_) $ _ $ t1 $ t2  => 
      let
         val prj1 = constrain_projection prj_rel prj t1
         val prj2 = constrain_projection prj_rel prj t2
         val merge = merge_prj prj1 prj2
      in
        merge
      end
  | Const (@{const_name "L2_while"}, wT) $ c $ bdy $ vars $ names =>
       let
         val vars' = HOLogic.strip_tupleT (fastype_of vars) |> number_bounds
           |> map (fn ((i, aliases),T) => ((i, aliases), ("x" ^ string_of_int i,T)))
         val (bounds, _) = mk_tuple vars'
         val w = Const (@{const_name "L2_while"}, wT) $ c $ bdy $ bounds $ names
         val uses = analyse_uses vars' w
         val uses = if null uses (* vars is unit *) then map (K Unused) prj else uses
         val relevant_uses = map remove_return uses
         val uses_needed = prj_of_uses prj_rel relevant_uses
         val merge = merge_prj prj uses_needed
       in
         merge
       end
  | _ => prj
end
end

fun analyse_uses' ctxt prj_rel t =
  let
    val (bounds, bdy) = Synthesize_Rules.strip_abs_prod t
    val uses = analyse_uses (number_bounds bounds) bdy
    val _ = Utils.verbose_msg 2 ctxt (fn _ => "analysed uses: " ^  @{make_string} (map fst bounds ~~ uses))
  in
    prj_of_uses prj_rel uses
  end

fun mk_case_prod (bdy, bT) [] = (bdy, bT)
  | mk_case_prod (bdy, bT) [(x,T)] = (Abs (x, T, bdy), bT)
  | mk_case_prod (bdy, bT) [(x,xT), (y,yT)] = (HOLogic.case_prod_const (xT, yT, bT) $ (Abs (x, xT, Abs (y, yT, bdy))), HOLogic.mk_prodT (xT, yT))
  | mk_case_prod (bdy, bT) ((x,xT)::xs) =
    let
      val (bdy', bT') = mk_case_prod (bdy, bT) xs
    in (HOLogic.case_prod_const (xT, bT', bT) $ (Abs (x, xT, bdy')), HOLogic.mk_prodT (xT, bT')) end

fun gen_mk_projection Ts prj_enc =
  let
    val n = length prj_enc
    val tagged_bounds = prj_enc |> gen_number_bounds (n - 1)
      |> map (fn ((i, aliases),t) => ((i, aliases),t, (Tuple_Tools.mk_el_name (n - i), Tuple_Tools.mk_elT' Ts (n - i))))
    val proj_bounds = map_filter (fn (i, t, xT) => if t then SOME (i, xT) else NONE) tagged_bounds
    val vars = map #3 tagged_bounds
    val (bdy, bT) = mk_tuple proj_bounds
    val prj = mk_case_prod (bdy, bT) vars
  in
    fst prj
  end

fun mk_projection prj_enc = gen_mk_projection (map Tuple_Tools.mk_elT (1 upto length prj_enc)) prj_enc

val _ = Tuple_Tools.assert_cterm (mk_projection [true,false,false,true])
  @{cterm "\<lambda>(x1, x2, x3, x4). (x1, x4)"}

val _ = Tuple_Tools.assert_cterm (mk_projection [false,false])
  @{cterm "\<lambda>(x1, x2). ()"}

fun split_project_rule ctxt prj_var orig_names new_names rule =
  let val rule = Thm.trim_context rule
  in fn prj_arity => if null prj_arity then rule else
    let
      val orig_arity = length prj_arity
      val new_arity = prj_arity |> filter I |> length
      val name_arities = map (rpair orig_arity) orig_names @ map (rpair new_arity) new_names
      val prj = mk_projection prj_arity
      val ctxt' = Variable.declare_term prj ctxt
      val prj = Thm.cterm_of ctxt' prj
      val [rule'] = rule
        |> Drule.infer_instantiate ctxt' [(prj_var, prj)]
        |> single |> Proof_Context.export ctxt' ctxt
    in
      Tuple_Tools.gen_split_rule ctxt name_arities rule'
    end
  end

\<comment> \<open>Tailored for case @{const L2_seq}, will it ever by used for other cases?\<close>
fun infer_projection_arity benv ctxt pattern [arity_var, constrain_var, prjL_var, prjR_var] concl =
  case Synthesize_Rules.match_rule_vars benv ctxt pattern [arity_var, constrain_var, prjL_var, prjR_var] concl of
    [arity_stmt, constrain_stmt, prjL, prjR] =>
      let
        val prj_rel = \<^infer_instantiate>\<open>L = prjL and prj = prjR in term \<open>rel_sum L (rel_project prj)\<close>\<close> ctxt
        val tagged_used = analyse_uses' ctxt prj_rel arity_stmt
        val _ = Utils.verbose_msg 2 ctxt (fn _ => "derived projection (raw): " ^ @{make_string} tagged_used)
        val constrained_used = constrain_projection prj_rel tagged_used constrain_stmt
        val _ = Utils.verbose_msg 2 ctxt (fn _ => "constrained projection: " ^ @{make_string} constrained_used)
      in constrained_used end
  | _ => []


fun mk_rel_spec_monad_pattern ctxt _ (@{term_pat "Trueprop (rel_spec_monad ?Q ?R ?f ?g)"}) =
  let
    val mi = fold (curry Int.max) (map maxidx_of_term [Q, R, f, g]) 0
    val gT = Logic.incr_tvar (mi + 1) (fastype_of g) (* FIXME: do I need incr_tvar? *)
    val pat = \<^infer_instantiate>\<open>Q = Q and R = R and f = f and g = \<open>Var (("_g", mi + 1), gT)\<close>
                in prop \<open>rel_spec_monad Q R f g\<close>\<close> ctxt
  in
    pat
  end
  | mk_rel_spec_monad_pattern _ _ _ = raise Match


fun add_rel_spec_monad_split_rule rules_name = Synthesize_Rules.gen_add_split_rule rules_name {only_schematic_goal = false} mk_rel_spec_monad_pattern
fun add_rel_spec_monad_split_rules rules_name = fold_map (fn (name, priority, names, thm) => add_rel_spec_monad_split_rule rules_name name priority names thm)

val add_rel_spec_monad_infer_project_split_rule =
  Synthesize_Rules.gen_add_infer_project_split_rule mk_rel_spec_monad_pattern infer_projection_arity

fun add_rel_spec_monad_infer_project_split_rules rules_name rs context =
  context |> fold_map (fn (name, priority, names, new_names, prj_name, constrain_name, prjL_name, prjR_name, thm) =>
   let
     fun get_var name = Term.add_vars (Thm.prop_of thm) [] |> filter (fn ((n, _),_) => n = name)
       |> distinct (op =) |> the_single |> fst
     val prj_var = get_var prj_name
     val split = split_project_rule (Context.proof_of context) prj_var names new_names thm
   in
     add_rel_spec_monad_infer_project_split_rule split rules_name {only_schematic_goal = false} name priority names [constrain_name, prjL_name, prjR_name] thm
   end) rs

fun add_rel_spec_monad_project_split_rule split rules_name name priority prj_name thm context =
  Synthesize_Rules.gen_add_project_split_rule mk_rel_spec_monad_pattern split
    rules_name {only_schematic_goal = false} name priority prj_name thm context

fun add_rel_spec_monad_project_split_rules rules_name rs context =
  context |> fold_map (fn (name, priority, names, new_names, prj_name, thm) =>
    let
      val _ = assert (not (null names)) "add_rel_spec_monad_project_split_rules: expecting at least one variable name"
      fun get_var name = Term.add_vars (Thm.prop_of thm) [] |> filter (fn ((n, _),_) => n = name)
        |> distinct (op =) |> the_single |> fst
      val prj_var = get_var prj_name
      val split = split_project_rule (Context.proof_of context) prj_var names new_names thm
    in
      add_rel_spec_monad_project_split_rule split rules_name name priority prj_name thm
    end) rs

fun add_rel_spec_monad_rule rules_name = Synthesize_Rules.gen_add_rule rules_name {only_schematic_goal = false} NONE mk_rel_spec_monad_pattern
fun add_rel_spec_monad_rules rules_name = fold (fn (name, priority, thm) => add_rel_spec_monad_rule rules_name name priority thm)


(* solve trivial leftover vars like "?f x y" of type unit *)
fun smash_unit_vars ctxt = SUBGOAL (fn (t, i) =>
 let
    fun make_inst (v,T) =
      let
        val (argTs, @{typ unit}) = strip_type T
        fun abs T bdy = Abs ("",T, bdy)
      in ((v,T), Thm.cterm_of ctxt (fold_rev abs argTs @{term "()"})) end

    val unit_vars = Term.add_vars t []
      |> filter (fn (_,T) => body_type T = @{typ unit})

    val insts = map (make_inst) unit_vars
 in
   if null insts then no_tac
   else PRIMITIVE (Thm.instantiate (TVars.empty, Vars.make insts))
 end)

local
  val ss = simpset_of (put_simpset HOL_basic_ss @{context}
             addsimps @{thms HOL.simp_thms
               surj_def rel_project_conv rel_Nonlocal_conv Product_Type.prod.case c_exntype.case
               rel_liftE_apply rel_sum_eq_apply
               if_True if_False
               Product_Type.prod.inject c_exntype.inject List.list.inject String.char.inject c_exntype.distinct
               sum.map_ident  unit_convs}
             |> Simplifier.add_cong @{thm if_cong})
in
fun clarsimp_solve_tac ctxt i =
  let
    val more_simps = Named_Theorems.get ctxt @{named_theorems rel_spec_monad_rewrite_simps}
  in
    CHANGED (TRY (smash_unit_vars ctxt i)
      THEN clarsimp_tac (put_simpset ss ctxt addsimps more_simps) i
      THEN (REPEAT (resolve_tac ctxt @{thms TrueI refl gen_unit_eq conjI} i)))
  end
end

fun get_prj_sum @{term_pat "rel_sum ?L ?R"} @{term_pat "Inl ?x"} = get_prj_sum L x
  | get_prj_sum @{term_pat "rel_sum ?L ?R"} @{term_pat "Inr ?x"} = get_prj_sum R x
  | get_prj_sum @{term_pat "rel_project ?prj"} _  = prj
  | get_prj_sum t _  = t

fun get_prj @{term_pat "(?R, ?x)"} = get_prj_sum R x
  | get_prj t = t

fun sanitize_names_tac ctxt = SUBGOAL (fn (t, i) =>
  if not (member (op =) (Term.add_const_names t []) @{const_name SANITIZE_NAMES}) then no_tac else
  let
    fun mk_abs [] t = t
      | mk_abs (T::Ts) t = Abs (Name.uu_, T, mk_abs Ts t)

    val concl = Utils.concl_of_subgoal_open t
    val @{term_pat \<open>Trueprop (SANITIZE_NAMES ?prj ?ns ?ns')\<close>} = concl
    val (ns', _) = strip_comb ns'
  in
    if is_Var ns' then
      let
        val Var (ns',T) = ns'
        val names = Utils.decode_isa_list ns
        val prj' = get_prj prj
        val bs = Synthesize_Rules.arity_from_projection prj'

        val names' = (if length bs <= 1
                  then filter_out (member (op =) [\<^const>\<open>global_exn_var_clocal\<close>]) names
                  else if length bs = length names then filter (fn (b, _) => b) (bs ~~ names) |> map snd 
                  else (warning ("sanitize_names_tac: unexpected number of names in: " ^ Syntax.string_of_term ctxt concl ^ "\n" ^ 
                         " (bs, names): " ^ @{make_string} (bs, names))
                        ; names))
          |> Utils.encode_isa_list @{typ nat} |> mk_abs (binder_types T) |> Thm.cterm_of ctxt
      in
       PRIMITIVE (Thm.instantiate (TVars.empty, Vars.make [((ns',T), names')])) THEN
       resolve_tac ctxt @{thms sanitize_namesI} i
      end
    else
      resolve_tac ctxt @{thms sanitize_namesI} i
  end
  handle Bind => no_tac
  )

(* Avoid superflouous dependency of variable on constant terms, e.g. '?x ()'. Otherwise resolution results in
 *  non eta-contracted terms which make Net.match_term fail later on.
 *)
fun norm_synthesis_var ctxt = SUBGOAL (fn (t,i) => fn st =>
 let
    val concl = Utils.concl_of_subgoal_open t
    val @{term_pat "Trueprop (rel_spec_monad ?P ?Q ?f ?g)"} = concl
    val (Var ((g, i), gT), args as (_::_)) = strip_comb g
    val (argTs, resT) = strip_type gT
    val n = length args
    val (appliedTs, unappliedTs) = chop n argTs
    val tagged_args = (args ~~ appliedTs) |> map (fn (arg, T) => (null (loose_bnos arg), (arg, T)))
    val (args', appliedTs') = tagged_args |> filter_out fst |> map snd |> split_list
    val _ = if length args' = n then raise Bind else () (* avoid trivial identity instantiations *)
    val g' = Var ((g, Thm.maxidx_of st + 1), appliedTs' @ unappliedTs ---> resT)
    fun mk_inst [] g' b = g'
      | mk_inst ((tag, (t, T))::args) g' b =
          let
            val g' = if tag then g' else  (g'$Bound b)
          in Abs ("", T, mk_inst args g' (b - 1)) end
    val insts = [(((g,i), gT), Thm.cterm_of ctxt (mk_inst tagged_args g' (length tagged_args - 1)))]
 in
   if null insts then no_tac st
   else PRIMITIVE (Thm.instantiate (TVars.empty, Vars.make insts)) st
 end
 handle Bind => no_tac st
)

fun norm_resolve_split_thm rules_name ctxt =
  let 
    val simp_ctxt = Simplifier.put_simpset HOL_basic_ss ctxt
         addsimps @{thms 
            HOL.simp_thms if_True if_False
            c_exntype.case_distrib [where h=from_xval] 
            Product_Type.prod.case_distrib[where h=from_xval] 
            Product_Type.prod.case c_exntype.case from_xval_simps}
         |> Simplifier.add_cong @{thm if_weak_cong}
         |> Simplifier.add_cong @{thm c_exntype.case_cong}
  in
    TRY' (norm_synthesis_var ctxt) THEN' Synthesize_Rules.resolve_split_thm rules_name ctxt
    THEN_ALL_NEW (Simplifier.simp_tac simp_ctxt)
 end
end
\<close>


declare [[verbose=3]]
setup \<open>
Context.theory_map (
  Rel_Spec_Monad_Synthesize_Rules.add_rel_spec_monad_rules @{synthesize_rules_name L2_rel_spec_monad} [
    (@{binding "L2_unknown - rel_xval"}, 10, @{thm rel_spec_monad_rel_xval_L2_unknown}),
    (@{binding "L2_modify - rel_xval"}, 10, @{thm rel_spec_monad_rel_xval_L2_modify}),
    (@{binding "L2_gets - rel_xval"}, 10, @{thm rel_spec_monad_rel_xval_L2_gets}),
    (@{binding "L2_condition - rel_xval"}, 10, @{thm rel_spec_monad_eq_rel_xval_L2_condition}),
    (@{binding "L2_throw - rel_xval"}, 10, @{thm rel_spec_monad_L2_throw_sanitize_names}),
    (@{binding "L2_spec - rel_xval"}, 10, @{thm rel_spec_monad_rel_xval_L2_spec}),
    (@{binding "L2_assume - rel_xval"}, 10, @{thm rel_spec_monad_rel_xval_L2_assume}),
    (@{binding "L2_guard - rel_xval"}, 10, @{thm rel_spec_monad_rel_xval_L2_guard}),
    (@{binding "L2_guarded - rel_xval"}, 10, @{thm rel_spec_monad_rel_xval_L2_guarded}),
    (@{binding "L2_fail"}, 10, @{thm rel_spec_monad_L2_fail}),
    (@{binding "L2_call - rel_xval"}, 10, @{thm rel_spec_monad_rel_xval_L2_call}),


    (@{binding "exec_concrete"}, 10, @{thm rel_spec_monad_result_exec_concrete}),
    (@{binding "exec_abstract"}, 10, @{thm rel_spec_monad_result_exec_abstract}),

    (@{binding "L2_unknown - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_unknown'}),
    (@{binding "L2_modify - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_modify}),
    (@{binding "L2_gets - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_gets'}),
    (@{binding "L2_condition - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_condition}),
    (@{binding "L2_throw - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_throw}),
    (@{binding "L2_spec - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_spec}),
    (@{binding "L2_assume - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_assume}),
    (@{binding "L2_guard - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_guard}),
    (@{binding "L2_guarded - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_guarded}),
    (@{binding "L2_try - rel_project"}, 20, @{thm rel_spec_monad_rel_project_L2_try}),
    (@{binding "L2_catch - rel_project"}, 10, @{thm rel_spec_monad_rel_project_L2_catch}),
    (@{binding "liftE unit - rel_project"}, 10, @{thm rel_spec_monad_rel_project_liftE_unit_id})
    ]

  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad}  {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_sum ?L ?R (Inl ?l) ?V)"}))) @{binding "rel_sum_Inl"} 10 @{thm rel_sum.intros(1)}
  #> Synthesize_Rules.gen_add_rule  @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_sum ?L ?R (Inr ?r) ?V)"}))) @{binding "rel_sum_Inr"}  10 @{thm rel_sum.intros(2)}
  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false}
       NONE (K (K (K @{pattern "Trueprop (rel_sum ?L ?R (map_sum ?l ?r (Inl ?x)) ?v)"}))) @{binding "rel_sum_map_sum_InlI"} 10 @{thm rel_sum_map_sum_InlI}
  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_sum ?L ?R (map_sum ?l ?r (Inr ?x)) ?v)"}))) @{binding "rel_sum_map_sum_InrI"} 10 @{thm rel_sum_map_sum_InrI}

  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad}  {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_xval ?L ?R (Exn ?l) ?V)"}))) @{binding "rel_xval_Exn"} 10 @{thm rel_xval.intros(1)}
  #> Synthesize_Rules.gen_add_rule  @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_xval ?L ?R (Result ?r) ?V)"}))) @{binding "rel_xval_Result"}  10 @{thm rel_xval.intros(2)}
  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false}
       NONE (K (K (K @{pattern "Trueprop (rel_xval ?L ?R (map_xval ?l ?r (Exn ?x)) ?v)"}))) @{binding "rel_map_xval_xval_ExnI"} 10 @{thm rel_map_xval_xval_ExnI}
  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_xval ?L ?R (map_xval ?l ?r (Result ?x)) ?v)"}))) @{binding "rel_map_xval_xval_ResultI"} 10 @{thm rel_map_xval_xval_ResultI}

  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_xval rel_Nonlocal ?R (case ?e of Nonlocal v \<Rightarrow> Exn (Nonlocal v) | _ \<Rightarrow> Result ?x) (Exn ?v'))"})))
       @{binding "rel_xval_rel_Nonlocal_case_ExnI"} 10 @{thm rel_xval_rel_Nonlocal_case_ExnI}
  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_xval rel_Nonlocal ?R (case ?e of Nonlocal v \<Rightarrow> Exn (Nonlocal v) | _ \<Rightarrow> Result ?x) (Result ?v'))"})))
       @{binding "rel_xval_rel_Nonlocal_case_ResultI"} 10 @{thm rel_xval_rel_Nonlocal_case_ResultI}
  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_xval rel_Nonlocal (=) (map_xval Nonlocal ?f (case ?e of Nonlocal x \<Rightarrow> Exn x | _ \<Rightarrow> Result ?x)) ?v)"})))
       @{binding "rel_xval_rel_Nonlocal_map_xvalI"} 10 @{thm rel_xval_rel_Nonlocal_map_xvalI}
  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_xval ?L ?R (case ?e of Nonlocal x \<Rightarrow> Exn (Nonlocal x) | _ \<Rightarrow> Result ?v)
                      (case ?e of Nonlocal x \<Rightarrow> Exn (Nonlocal x) | _ \<Rightarrow> Result ?v'))"})))
       @{binding "rel_xval_case_Nonlocal_sameI"} 10 @{thm rel_xval_case_Nonlocal_sameI}
  #> Synthesize_Rules.gen_add_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false} NONE
       (K (K (K @{pattern "Trueprop (rel_project ?prj ?x ?y)"}))) @{binding "rel_project"} 10 @{thm rel_projectI}

  #> Rel_Spec_Monad_Synthesize_Rules.add_rel_spec_monad_split_rules @{synthesize_rules_name L2_rel_spec_monad} [
    (@{binding "L2_seq - rel_xval"}, 10, ["f", "g"], @{thm rel_spec_monad_L2_seq_rel_xval_same_split}),
    (@{binding "L2_while - rel_xval"}, 10, ["B", "B'"], @{thm rel_spec_monad_L2_while_rel_xval_same_split}),
    (@{binding "L2_call - rel_project"}, 10, ["emb", "emb'"], @{thm rel_spec_monad_rel_project_L2_call_adapt_emb}),
    (@{binding "L2_seq - rel_project (exit handler)"}, 20, ["g", "g'"], @{thm rel_spec_monad_L2_seq_exit_handler})
    ]
  ##>> Synthesize_Rules.gen_add_split_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false}
    (K (K (K @{pattern "Trueprop (rel_spec_monad ?R (rel_xval ?L (=)) (L2_catch ?m ?f) ?g)"})))
    @{binding "L2_catch_try - rel_xval"}  10 ["f"] @{thm rel_spec_monad_rel_xval_try_catch}
  ##>> Synthesize_Rules.gen_add_split_rule @{synthesize_rules_name L2_rel_spec_monad} {only_schematic_goal = false}
    (K (K (K @{pattern "Trueprop (rel_fun ?A ?B ?f ?g)"})))
    @{binding "rel_funI"}  10 ["f", "g"] @{thm rel_funI}
  ##>> Rel_Spec_Monad_Synthesize_Rules.add_rel_spec_monad_infer_project_split_rules @{synthesize_rules_name L2_rel_spec_monad} [
    (@{binding "L2_seq - rel_project"}, 10, ["f"], ["g"], "prj'","m", "L", "prj", @{thm rel_spec_monad_rel_project_L2_seq})
   ]
  ##>> Rel_Spec_Monad_Synthesize_Rules.add_rel_spec_monad_project_split_rules @{synthesize_rules_name L2_rel_spec_monad} [
    (@{binding "L2_while - rel_project"}, 10, ["B","C","I"], ["B'","C'", "I'"] , "prj", @{thm rel_spec_monad_rel_project_L2_while'})
   ]
  #> snd)
\<close>

context stack_heap_raw_state
begin
declaration \<open>
fn phi =>
  Rel_Spec_Monad_Synthesize_Rules.add_rel_spec_monad_rules @{synthesize_rules_name L2_rel_spec_monad} [
    (@{binding "with_fresh_stack_ptr - rel_sum"}, 10, Morphism.thm phi @{thm rel_spec_monad_rel_xval_with_fresh_stack_ptr}),
    (@{binding "with_fresh_stack_ptr - rel_project"}, 10, Morphism.thm phi @{thm rel_spec_monad_rel_project_with_fresh_stack_ptr})]
\<close>
end
declare [[verbose=0]]

lemma map_sum_right: "(map_sum l r v = Inr x) = (\<exists>v'. v = Inr v' \<and> x = r v')"
  by (cases v) auto

lemma map_sum_left: "(map_sum l r v = Inl x) = (\<exists>v'. v = Inl v' \<and> x = l v')"
  by (cases v) auto

lemma case_Nonlocal_Inr: "((case e of Nonlocal x \<Rightarrow> Inl x | _ \<Rightarrow> Inr v) = Inr y) = (is_local e \<and> (v = y))"
  by (cases e) auto

lemma case_Nonlocal_Inl: "((case e of Nonlocal x \<Rightarrow> Inl x | _ \<Rightarrow> Inr v) = Inl y) = (e = Nonlocal y)"
  by (cases e) auto


method_setup resolve_split = \<open>
  Scan.succeed (fn ctxt => 
    let
      val simp_ctxt = (ctxt |> Simplifier.clear_simpset) addsimps @{thms 
        from_xval_simps 
        if_distrib [where f = from_xval]}
    in
    SIMPLE_METHOD'
      (Rel_Spec_Monad_Synthesize_Rules.norm_resolve_split_thm @{synthesize_rules_name L2_rel_spec_monad} ctxt 
       THEN_ALL_NEW (simp_tac simp_ctxt))
    end)\<close>
  "resolve with rel_spec_monad rules of right arity"

method_setup sanitize_names = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Rel_Spec_Monad_Synthesize_Rules.sanitize_names_tac ctxt))\<close>
  "sanitize name annotations for L2_throw"

method_setup verbose_msg =
  \<open>Scan.lift (Parse.embedded >>
    (fn msg => fn ctxt => SIMPLE_METHOD (fn st => (Utils.verbose_msg 1 ctxt (fn _ => msg); all_tac st))))\<close>
  "print a message (if flag autocorres_verbose is turned on)"

method_setup clarsimp_solve = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Rel_Spec_Monad_Synthesize_Rules.clarsimp_solve_tac ctxt))\<close>
  "clarsimp and then solve, instantiating variables"

method_setup trace =
  \<open>Scan.lift ((Parse.embedded_input -- Parse.embedded) >> (fn (method_src, msg) => fn ctxt =>
    let
      val (m, tok) = Method.read_closure_input ctxt method_src
      val msg_m = Method.Basic (fn ctxt => SIMPLE_METHOD (fn st => (Utils.verbose_msg 1 ctxt (fn _ => msg); all_tac st)))
      val trace_meth = Method.Combinator (Method.no_combinator_info, Method.Then, [m, msg_m])
    in
      Utils.timeap_method 3 ctxt (fn _ => msg) (Method.evaluate trace_meth ctxt)
    end))\<close>
  "trace a method application (if flag autocorres_verbose is turned on)"

method rel_spec_monad_L2_step uses more_intro_thms =
  ((rule_tac more_intro_thms, verbose_msg "applied: rule_tac") |
   trace resolve_split "applied: resolve_split" |
   trace assumption "applied: assumption" |
   trace sanitize_names "applied: sanitize_names" |
   trace clarsimp_solve "applied: clarsimp_solve"
 )

method rel_spec_monad_L2_rewrite =
  (use in \<open>rel_spec_monad_L2_step more_intro_thms: method_facts\<close>)+


ML \<open>
structure L2_Exception_Rewrite =
struct

fun rhs_conv conv eq_thm =
  Conv.fconv_rule (Conv.arg_conv conv) eq_thm

  val rel_spec_monad_L2_rewrite_tac = UMM_Tools.tactic_from_src @{context} \<open>rel_spec_monad_L2_rewrite\<close>



fun abstract_try_catch ctxt t =
  let
    val goal = \<^infer_instantiate>\<open>t = t in prop (schematic) \<open>t = a\<close>\<close> ctxt
    val thm = Goal.prove ctxt [] [] goal (fn {prems, context,...}  =>
        simp_tac ((Simplifier.add_cong @{thm c_exntype.case_cong} (put_simpset HOL_basic_ss context))
           addsimps @{thms cond_return1 cond_return2 if_c_exntype_cases rel_spec_monad_eq_conv [symmetric]}) 1 THEN
        resolve_tac context @{thms rel_spec_monad_rel_xvalI} 1 THEN
        rel_spec_monad_L2_rewrite_tac context [] THEN
        print_unsolved_tac "abstract_try_catch: unfinished goal" ctxt
      )
  in
    SOME thm
  end
  handle ERROR _ => raise TERM ("abstract_try_catch failed", [t])

fun abstract_try_catch_conv ctxt ct =
  case abstract_try_catch ctxt (Thm.term_of ct) of
    SOME eq => mk_meta_eq (Simplifier.simplify (Simplifier.clear_simpset ctxt addsimps @{thms from_xval_simps}) eq)
  | NONE => (warning ("abstract_try_catch_conv: failed to convert to nested exceptions." ^
     @{make_string} ct); Conv.all_conv ct)

fun rel_spec_monad_conv trace_unfinshed eq_intro ctxt lhs =
  let
     val  ([lhs'], ctxt') = Variable.import_terms false [lhs] ctxt
     val goal = \<^infer_instantiate>\<open>lhs = lhs' in prop (schematic) \<open>lhs = A\<close>\<close> ctxt'
     val thm = Goal.prove ctxt' [] [] goal (fn {context, ...} =>
       resolve_tac context [eq_intro] 1 THEN
       simp_tac (Simplifier.clear_simpset context addsimprocs [@{simproc ETA_TUPLED}]) 1 THEN
       rel_spec_monad_L2_rewrite_tac context [] THEN
       trace_unfinshed context)
     val [eq] = Variable.export ctxt' ctxt [mk_meta_eq thm]
     val eq = Thm.instantiate (Thm.match (Thm.lhs_of eq, Thm.cterm_of ctxt lhs)) eq
  in
    SOME eq
  end
  handle ERROR x => NONE

fun project_used_components_conv ctxt ct =
  let
    val trace = print_unsolved_tac "project_used_components_conv: unfinished goal"
  in
    case rel_spec_monad_conv trace @{thm rel_project_eqI} ctxt (Thm.term_of ct) of
      SOME eq => eq |> rhs_conv (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps
        (Utils.get_rules ctxt @{named_theorems L2opt}))) \<comment>\<open>get rid of now unused result values, e.g. \<open>L2_unknown\<close>\<close>
    | NONE => (warning ("project_used_components failed on: " ^ @{make_string} ct); Conv.all_conv ct)
  end

end
\<close>

end

