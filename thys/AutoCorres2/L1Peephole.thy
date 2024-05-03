(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Peep-hole L1 optimisations\<close>

theory L1Peephole
imports L1Defs
begin

(* Simplification rules run after L1. *)
named_theorems L1opt

lemma L1_seq_assoc [L1opt]: "(L1_seq (L1_seq X Y) Z) = (L1_seq X (L1_seq Y Z))"
  apply (clarsimp simp: L1_seq_def bind_assoc)
  done

lemma L1_seq_skip [L1opt]:
  "L1_seq A L1_skip = A"
  "L1_seq L1_skip A = A"
  apply (clarsimp simp: L1_seq_def L1_skip_def)+
  done

lemma L1_condition_true [L1opt]: "L1_condition (\<lambda>_. True) A B = A"
  apply (clarsimp simp: L1_condition_def condition_def)
  done

lemma L1_condition_false [L1opt]: "L1_condition (\<lambda>_. False) A B = B"
  apply (clarsimp simp: L1_condition_def condition_def)
  done

lemma L1_condition_same [L1opt]: "L1_condition C A A = A"
  apply (clarsimp simp: L1_defs condition_def spec_monad_ext run_bind)
  done

lemma L1_fail_seq [L1opt]: "L1_seq L1_fail X = L1_fail"
  apply (clarsimp simp: L1_seq_def L1_fail_def spec_monad_ext run_bind)
  done

lemma L1_throw_seq [L1opt]: "L1_seq L1_throw X = L1_throw"
  apply (clarsimp simp: L1_seq_def L1_throw_def)
  done


lemma L1_fail_propagates [L1opt]:
  "L1_seq L1_skip L1_fail = L1_fail"
  "L1_seq (L1_modify M) L1_fail = L1_fail"
  "L1_seq (L1_spec S) L1_fail = L1_fail"
  "L1_seq (L1_guard G) L1_fail = L1_fail"
  "L1_seq (L1_init I) L1_fail = L1_fail"
  "L1_seq L1_fail L1_fail = L1_fail"
   apply (unfold L1_defs)
   apply (rule spec_monad_eqI; auto simp add: runs_to_iff)+
   done

lemma L1_condition_distrib:
  "L1_seq (L1_condition C L R) X = L1_condition C (L1_seq L X) (L1_seq R X)"
  apply (unfold L1_defs)
  apply (rule spec_monad_eqI; auto simp add: runs_to_iff)
  done

lemmas L1_fail_propagate_condition [L1opt] = L1_condition_distrib [where X=L1_fail]

lemma L1_fail_propagate_catch [L1opt]:
  "(L1_seq (L1_catch L R) L1_fail) = (L1_catch (L1_seq L L1_fail) (L1_seq R L1_fail))"
  apply (unfold L1_defs)
  apply (rule spec_monad_eqI; auto simp add: runs_to_iff)
   apply (fastforce simp add: runs_to_def_old Exn_def)+
  done


lemma L1_guard_false [L1opt]:
  "L1_guard (\<lambda>_. False) = L1_fail"
  unfolding L1_defs
  by (simp add: guard_False_fail)


lemma L1_guard_true [L1opt]:
  "L1_guard (\<lambda>_. True) = L1_skip"
  unfolding L1_defs
  by (simp add: spec_monad_ext run_guard)

lemma L1_condition_fail_lhs [L1opt]:
  "L1_condition C L1_fail A = L1_seq (L1_guard (\<lambda>s. \<not> C s)) A"
  apply (unfold L1_defs)
  apply (rule spec_monad_eqI; auto simp add: runs_to_iff)
  done


lemma L1_condition_fail_rhs [L1opt]:
  "L1_condition C A L1_fail = L1_seq (L1_guard C) A"
  apply (unfold L1_defs)
  apply (rule spec_monad_eqI; auto simp add: runs_to_iff)
  done

lemma L1_catch_fail [L1opt]: "L1_catch L1_fail A = L1_fail"
  unfolding L1_defs
  apply (rule spec_monad_eqI; auto simp add: runs_to_iff)
  done

lemma L1_while_fail [L1opt]: "L1_while C L1_fail = L1_guard (\<lambda>s. \<not> C s)"
  unfolding L1_defs
  apply (subst whileLoop_unroll)
  apply (rule spec_monad_ext)
  apply (auto simp add: run_condition run_bind run_guard)
  done

lemma whileLoop_succeeds_terminates_infinite: 
  assumes "run (whileLoop (\<lambda>_. C) (\<lambda>_. skip) ()) s \<noteq> \<top>"
  shows "C s \<Longrightarrow> False"
  using assms by (induct rule: whileLoop_ne_top_induct) auto


lemma run_whileLoop_infinite: "run (whileLoop (\<lambda>_. C) (\<lambda>_. skip) ()) s = run (guard (\<lambda>s. \<not> C s)) s"
proof (cases "C s")
  case True
  show ?thesis 
    apply (rule antisym)
    subgoal 
      apply (subst whileLoop_unroll)
      apply (simp add: run_guard)
      done
    subgoal
    proof -
      have "run (whileLoop (\<lambda>_. C) (\<lambda>_. skip) ()) s = \<top>"
        using True whileLoop_succeeds_terminates_infinite[of C s] by auto
      hence "\<not> succeeds (whileLoop  (\<lambda>_. C)  (\<lambda>_. skip) ()) s"
        by (simp add: succeeds_def)
      then show ?thesis
        by (simp add: run_guard succeeds_def True top_post_state_def)
    qed
    done
 next
  case False
  then show ?thesis apply (subst whileLoop_unroll) by (simp add: run_guard)
qed

lemma whileLoop_infinite: "whileLoop (\<lambda>_. C) (\<lambda>_. skip) () = guard (\<lambda>s. \<not> C s)"
  apply (rule spec_monad_ext)
  apply (rule run_whileLoop_infinite)
  done

lemma L1_while_infinite [L1opt]: "L1_while C L1_skip = L1_guard (\<lambda>s. \<not> C s)"
  unfolding L1_defs
  apply (rule whileLoop_infinite)
  done



lemma L1_while_false [L1opt]:
  "L1_while (\<lambda>_. False) B = L1_skip"
  apply (clarsimp simp: L1_while_def L1_skip_def)
  apply (subst whileLoop_unroll)
  apply clarsimp
  done

declare ucast_id [L1opt]
declare scast_id [L1opt]
declare L1_set_to_pred_def [L1opt]
declare L1_rel_to_fun_def [L1opt]

(*
 * The following sets of rules are used to simplify conditionals,
 * removing set notation (converting into predicate notation) and
 * generally removing logical cruft without being too aggressive in our
 * simplification.
 *)

lemma in_set_to_pred [L1opt]: "(\<lambda>s. s \<in> {x. P x}) = P"
  apply simp
  done

lemma in_set_if_then [L1opt]: "(s \<in> (if P then A else B)) = (if P then (s \<in> A) else (s \<in> B))"
  apply simp
  done

lemma Pair_unit_Image[L1opt]: "Pair () ` S `` {x} = {(u, x'). (x, x') \<in> S}"
  by auto


lemmas if_simps =
  if_x_Not if_Not_x if_cancel if_True if_False if_bool_simps

declare empty_iff [L1opt]
declare UNIV_I [L1opt]
declare singleton_iff [L1opt]
declare if_simps [L1opt]
declare simp_thms [L1opt]

lemma L1_call_stop_cong: "(L1_call f n g r) = (L1_call f n g r)"
  by simp

lemma L1_merge_assignments (*[L1opt]*): " (L1_seq (L1_modify f)
                               (L1_seq (L1_modify g) X)) \<equiv> L1_seq (L1_modify (\<lambda>s. g (f s))) X"
  apply (subst atomize_eq)
  apply (unfold L1_defs)
  apply (rule spec_monad_eqI; auto simp add: runs_to_iff)
  done

end
