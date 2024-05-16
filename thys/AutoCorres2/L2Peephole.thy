(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open> Peep-hole optimisations applied to L2 \<close>

theory L2Peephole
imports L2Defs Tuple_Tools
begin

definition STOP :: "'a::{} \<Rightarrow> 'a"  
  where "STOP P  \<equiv> P"

lemma STOP_cong: "STOP P \<equiv> STOP P"
  by simp

lemma do_STOP: "P \<equiv> STOP P"
  by (simp add: STOP_def)

lemmas id_def [L2opt]

lemma L2_seq_skip [L2opt]:
  "L2_seq (L2_gets (\<lambda>_. ()) n) X = (X ())"
  "L2_seq Y (\<lambda>_. (L2_gets (\<lambda>_. ()) n)) = Y"
  apply (clarsimp simp: L2_seq_def L2_gets_def gets_return )+
  done

lemma L2_seq_L2_gets [L2opt]: "L2_seq X (\<lambda>x. L2_gets (\<lambda>_. x) n) = X"
  apply (clarsimp simp: L2_defs gets_return)
  done

lemma L2_seq_L2_gets_unit[L2opt]: "L2_seq (L2_gets g ns) (\<lambda>x:: unit. f x) = f ()"
  apply (clarsimp simp: L2_defs)
  by (rule spec_monad_eqI) (auto simp add: runs_to_iff)



lemma L2_seq_L2_gets_const: "L2_seq (L2_gets (\<lambda>_. c) n) X = X c" 
  apply (clarsimp simp: L2_defs liftE_def gets_return)
  done
 
(* Constant propagation weak *)
lemma const_propagation_cong: "X c = X' c \<Longrightarrow> (L2_seq (L2_gets (\<lambda>_. c) n) X) = (L2_seq (L2_gets (\<lambda>_. c) n) X')"
  by (clarsimp simp: L2_seq_L2_gets_const)

lemma L2_seq_const':
  assumes bdy_eq: "f c \<equiv> g c"
  shows "L2_seq (L2_gets (\<lambda>_. c) n) f \<equiv> L2_seq (L2_gets (\<lambda>_. c) n) g"
  apply (rule eq_reflection)
  unfolding L2_defs
  apply (rule spec_monad_eqI) 
  apply (auto simp add: bdy_eq runs_to_iff)
  done

lemma L2_seq_const:
  assumes bdy_eq: "f' \<equiv> g'"
  assumes f_app: "f c \<equiv> f'" 
  assumes g_app: "g c \<equiv> g'"
  shows "L2_seq (L2_gets (\<lambda>_. c) n) f \<equiv>  L2_seq (L2_gets (\<lambda>_. c) n) g"
proof -
  from bdy_eq f_app g_app have "f c \<equiv> g c"
    by simp
  then show "PROP ?thesis"
    by (rule L2_seq_const')
qed

lemma L2_seq_const_stop:
  assumes bdy_eq: "f' \<equiv> g'"
  assumes f_app: "f c \<equiv> f'" 
  assumes g_app: "g c \<equiv> g'"
  shows "L2_seq (L2_gets (\<lambda>_. c) n) f \<equiv>  STOP (L2_seq (L2_gets (\<lambda>_. c) n) g)"
  unfolding STOP_def using bdy_eq f_app g_app
  by (rule L2_seq_const)

lemma L2_seq_const_stop':
  assumes bdy_eq: "f c \<equiv> g'"
  assumes g_app: "g c \<equiv> g'"
  shows "L2_seq (L2_gets (\<lambda>_. c) n) f \<equiv>  STOP (L2_seq (L2_gets (\<lambda>_. c) n) g)"
  apply (rule L2_seq_const_stop)
    apply (rule bdy_eq)
   apply simp
  apply (rule g_app)
  done

lemma L2_seq_const_stop'':
  assumes bdy_eq: "f c \<equiv> g c"
  shows "L2_seq (L2_gets (\<lambda>_. c) n) f \<equiv>  STOP (L2_seq (L2_gets (\<lambda>_. c) n) g)"
  apply (rule L2_seq_const_stop')
    apply (rule bdy_eq)
   apply simp
  done

lemma L2_seq_const_stop''':
  assumes bdy_eq: "f c \<equiv> g"
  shows "L2_seq (L2_gets (\<lambda>_. c) n) f \<equiv>  STOP (L2_seq (L2_gets (\<lambda>_. c) n) (\<lambda>_. g))"
  apply (rule L2_seq_const_stop')
    apply (rule bdy_eq)
   apply simp
  done

lemma L2_marked_seq_gets_cong:
 "c=c' \<Longrightarrow> L2_seq_gets c n A \<equiv> L2_seq_gets c' n A"
  by simp

lemma L2_marked_seq_gets_stop:
  assumes bdy_eq: "f c \<equiv> g"
  shows "L2_seq_gets c n f \<equiv> STOP (L2_seq_gets c n (\<lambda>_. g))"
  unfolding L2_seq_gets_def using bdy_eq
  by (rule  L2_seq_const_stop''')


lemma L2_guarded_block_cong: "L2_guarded g c = L2_guarded g c"
  by simp

lemma L2_guarded_cong_stop': 
assumes guard_eq: "\<And>s. g s \<equiv> g' s"
assumes bdy_eq: "\<And>s. g' s \<Longrightarrow> run c s \<equiv> run c' s"
shows "L2_guarded g c \<equiv> STOP (L2_guarded g' c')"
  unfolding L2_guarded_def L2_defs STOP_def
  apply (rule eq_reflection)
  apply (rule spec_monad_ext)
  using guard_eq bdy_eq
  apply (auto simp add: run_guard run_bind)
  done

lemma L2_seq_guard_cong_stop0: 
assumes guard_eq: "\<And>s. g s \<equiv> g' s"
assumes bdy_eq: "\<And>s. g' s \<Longrightarrow> run c s \<equiv> run c' s"
shows "L2_seq_guard g (\<lambda>_. c) \<equiv> STOP (L2_seq_guard g' (\<lambda>_. c'))"
  unfolding L2_seq_guard_def
  using assms
  by (rule L2_guarded_cong_stop'[simplified L2_guarded_def])


lemma L2_guarded_cong_stop: 
assumes guard_eq: "g \<equiv> g'"
assumes bdy_eq: "\<And>s. g' s \<Longrightarrow> run c s \<equiv> run c' s"
shows "L2_guarded g c \<equiv> STOP (L2_guarded g' c')"
  unfolding L2_guarded_def L2_defs STOP_def
  apply (rule eq_reflection)
  apply (rule spec_monad_ext)
  using guard_eq bdy_eq
  apply (auto simp add: run_guard run_bind)
  done

lemma L2_seq_assoc (*[L2opt]*):
  "L2_seq (L2_seq A (\<lambda>x. B x)) C = L2_seq A (\<lambda>x. L2_seq (B x) C)"
  apply (clarsimp simp: L2_seq_def bind_assoc)
  done


lemma L2_seq_assoc' [L2opt]:
  "L2_seq (L2_seq A B) C = L2_seq A (\<lambda>x. L2_seq (B x) C)"
  apply (clarsimp simp: L2_seq_def bind_assoc)
  done

lemma L2_trim_after_throw [L2opt]:
  "L2_seq (L2_throw x n) Z = (L2_throw x n)"
  apply (clarsimp simp: L2_seq_def L2_throw_def)
  done

lemma L2_guard_true [L2opt]: "L2_guard (\<lambda>_. True) = L2_gets (\<lambda>_. ()) []"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_guard)
  done

text \<open>This rule can be too expensive in simplification as it might invoke 
the arithmetic solver\<close>
lemma L2_guard_solve_true: "\<lbrakk> \<And>s. P s \<rbrakk> \<Longrightarrow> L2_guard P = L2_gets (\<lambda>_. ()) []"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_guard)
  done

lemma L2_guard_false [L2opt]: "L2_guard (\<lambda>_. False) = L2_fail"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_guard)
  done

text \<open>This rule can be too expensive in simplification as it might invoke the 
arithmetic solver\<close>
lemma L2_guard_solve_false: "\<lbrakk> \<And>s. \<not> P s \<rbrakk> \<Longrightarrow> L2_guard P = L2_fail"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_guard)
  done

lemma L2_spec_empty [L2opt]:
  (* fixme: do we need both? *)
  "L2_spec {} = L2_fail"
  "\<lbrakk> \<And>s t. \<not> C s t \<rbrakk> \<Longrightarrow> L2_spec {(s, t). C s t} = L2_fail"
  unfolding L2_defs
   apply (rule spec_monad_ext; simp add: run_bind run_assert_result_and_state)+
  done

lemma L2_unknown_bind_unbound[L2opt]:
 "L2_seq (L2_unknown ns) (\<lambda>x. f) = f"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_bind)
  done

lemma L2_seq_L2_unknown_unit[L2opt]: "L2_seq (L2_unknown ns) (\<lambda>x:: unit. f x) = f ()"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

text \<open>The following rule can cause some exponential blowup, especially when rewriting is not
successful. Note that @{term f} is duplicated in the premise. The more restricted
 @{thm L2_unknown_bind_unbound} should also do the job, in case of properly initialised
variables. Maybe we should remove it entirely from "L2opt".\<close>
lemma L2_unknown_bind [(*L2opt*)]:
  "(\<And>a b. f a = f b) \<Longrightarrow> (L2_seq (L2_unknown ns) f) = f undefined"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (clarsimp simp add: runs_to_def_old)
  apply metis
  done



(* N.S. Seems to be unused in current setup. Maybe give it a try as cong rule.*)
lemma L2_seq_guard_cong:
  "\<lbrakk> P = P'; \<And>s. P' s \<Longrightarrow> run X s = run X' s \<rbrakk> \<Longrightarrow> L2_seq (L2_guard P) (\<lambda>_. X) = L2_seq (L2_guard P') (\<lambda>_. X')"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma L2_seq_guard_cong':
  "\<lbrakk> P \<equiv> P'; \<And>s. P' s \<Longrightarrow> run X s \<equiv> run X' s \<rbrakk> \<Longrightarrow> L2_seq (L2_guard P) (\<lambda>_. X) \<equiv> L2_seq (L2_guard P') (\<lambda>_. X')"
  apply (rule eq_reflection)
  apply (rule L2_seq_guard_cong)
  by auto

lemma L2_seq_guard_cong_stop:
  "\<lbrakk> P = P'; \<And>s. P' s \<Longrightarrow> run X s = run X' s \<rbrakk> \<Longrightarrow> L2_seq (L2_guard P) (\<lambda>_. X) = STOP (L2_seq (L2_guard P') (\<lambda>_. X'))"
  unfolding STOP_def
  by (rule L2_seq_guard_cong, auto)

lemma L2_seq_guard_cong_stop':
  "\<lbrakk> P \<equiv> P'; \<And>s. P' s \<Longrightarrow> run X s \<equiv> run X' s \<rbrakk> \<Longrightarrow> L2_seq (L2_guard P) (\<lambda>_. X) \<equiv> STOP (L2_seq (L2_guard P') (\<lambda>_. X'))"
  apply (rule eq_reflection)
  apply (rule L2_seq_guard_cong_stop)
  by auto

lemma L2_seq_guard_cong_stop'':
  "\<lbrakk>\<And>s. P s \<Longrightarrow> run X s \<equiv> run X' s \<rbrakk> \<Longrightarrow> L2_seq (L2_guard P) (\<lambda>_. X) \<equiv> STOP (L2_seq (L2_guard P) (\<lambda>_. X'))"
  apply (rule eq_reflection)
  apply (rule L2_seq_guard_cong_stop)
  by auto

lemma L2_seq_guard_cong_stop''':
  "\<lbrakk>\<And>s. P s \<Longrightarrow> run (X ()) s \<equiv> run X' s \<rbrakk> \<Longrightarrow> L2_seq (L2_guard P) X \<equiv> STOP (L2_seq (L2_guard P) (\<lambda>_. X'))"
  unfolding STOP_def L2_defs
  apply (rule eq_reflection)
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma L2_marked_seq_guard_cong:
 "\<lbrakk>P = P'; \<And>s. P' s \<Longrightarrow> run (X ()) s = run X' s\<rbrakk>  \<Longrightarrow> L2_seq_guard P X = L2_seq_guard P' (\<lambda>_. X')"
  unfolding L2_seq_guard_def L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma L2_gaurded_keep_guard_cong: 
"(\<And>s. g s \<Longrightarrow> run c s = run c' s) \<Longrightarrow> L2_guarded g c = L2_guarded g c'"
  unfolding L2_guarded_def L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma gets_guard_move_before [L2opt]:
  "L2_seq (L2_gets f ns) (\<lambda>r. L2_seq (L2_guard P) (\<lambda>_. X r)) =
   L2_seq (L2_guard P) (\<lambda>_. L2_seq (L2_gets f ns) X)"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L2_seq_guard_cong'':
  "\<lbrakk> \<And>s. P s = P' s; \<And>s. P' s \<Longrightarrow> run X s = run X' s \<rbrakk> \<Longrightarrow> L2_seq (L2_guard P) (\<lambda>_. X) = L2_seq (L2_guard P') (\<lambda>_. X')"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma guard_triv [L2opt]: "L2_seq (L2_guard (\<lambda>s. True)) (\<lambda>_. X) = X"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_bind run_guard)
  done

lemma L2_condition_cong:
  "\<lbrakk> C = C'; \<And>s. C' s \<Longrightarrow> run A s = run A' s;\<And>s. \<not> C' s \<Longrightarrow> run B s = run B' s \<rbrakk> \<Longrightarrow> L2_condition C A B = L2_condition C' A' B'"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_condition)
  done

lemma L2_condition_cong_stop:
  "\<lbrakk> C = C'; \<And>s. C' s \<Longrightarrow> run A s = run A' s;\<And>s. \<not> C' s \<Longrightarrow> run B s = run B' s \<rbrakk> \<Longrightarrow> L2_condition C A B = STOP (L2_condition C' A' B')"
  unfolding STOP_def
  by (rule L2_condition_cong)

lemma L2_condition_cong':
  "\<lbrakk> \<And>s. C s = C' s; \<And>s. C' s \<Longrightarrow> run A s = run A' s;\<And>s. \<not> C' s \<Longrightarrow> run B s = run B' s \<rbrakk> \<Longrightarrow> L2_condition C A B = L2_condition C' A' B'"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_condition)
  done

lemma L2_condition_true [L2opt]: "\<lbrakk> \<And>s. C s \<rbrakk> \<Longrightarrow> L2_condition C A B = A"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_condition)
  done

lemma L2_condition_false [L2opt]: "\<lbrakk> \<And>s. \<not> C s \<rbrakk> \<Longrightarrow> L2_condition C A B = B"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_condition)
  done

lemma L2_condition_true' [simp]: "L2_condition (\<lambda>s. True) A B = A"
  unfolding L2_defs
  by simp

lemma L2_condition_false' [simp]: "L2_condition (\<lambda>s. False) A B = B"
  unfolding L2_defs
  by simp

lemma L2_condition_same [L2opt]: "L2_condition C A A = A"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_condition)
  done

lemma L2_fail_seq [L2opt]: "L2_seq L2_fail X = L2_fail"
  unfolding L2_defs
  by simp

lemma bind_fail_propagates: "\<lbrakk> no_throw (\<lambda>_. True) A; always_progress A \<rbrakk> \<Longrightarrow> A >>= (\<lambda>_. fail) = fail"
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (clarsimp simp add: no_throw_def runs_to_def_old runs_to_partial_def_old)
  by (meson always_progressD)



lemma state_select_select_fail: 
  "state_select S \<bind> (\<lambda>_. select UNIV) \<bind> (\<lambda>_. fail) = fail"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done
(* FIXME: make always progress rules for atomics to simpset *)

lemma L2_fail_propagates [L2opt]:
  "L2_seq (L2_gets V n) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq (L2_modify M) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq (L2_spec S) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq (L2_guard G) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq (L2_unknown ns) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq L2_fail (\<lambda>_. L2_fail) = L2_fail"
  unfolding L2_defs
       apply (simp_all add: bind_fail_propagates always_progress_intros
      state_select_select_fail)
  done

lemma L2_condition_distrib:
  "L2_seq (L2_condition C L R) X = L2_condition C (L2_seq L X) (L2_seq R X)"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemmas L2_fail_propagate_condition [L2opt] = L2_condition_distrib [where X="\<lambda>_. L2_fail"]

lemma L2_seq_condition_skip_throw [L2opt]: "L2_seq
            (L2_condition c (L2_gets (\<lambda>_. ()) ns)
               (L2_throw x ms))
            (\<lambda>r. y) = 
       (L2_condition c y
               (L2_throw x ms))"
  by (simp add: L2_condition_distrib L2_seq_skip L2_trim_after_throw)

lemma L2_fail_propagate_catch [L2opt]:
  "(L2_seq (L2_catch L R) (\<lambda>_. L2_fail)) = (L2_catch (L2_seq L (\<lambda>_. L2_fail)) (\<lambda>e. L2_seq (R e) (\<lambda>_. L2_fail)))"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff default_option_def Exn_def, safe )
   apply (auto simp add: runs_to_def_old)
  done
  
lemma L2_condition_fail_lhs [L2opt]:
  "L2_condition C L2_fail A = L2_seq (L2_guard (\<lambda>s. \<not> C s)) (\<lambda>_. A)"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff default_option_def Exn_def)
  done

lemma L2_condition_fail_rhs [L2opt]:
  "L2_condition C A L2_fail = L2_seq (L2_guard (\<lambda>s. C s)) (\<lambda>_. A)"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff default_option_def Exn_def)
  done

lemma L2_catch_fail [L2opt]: "L2_catch L2_fail A = L2_fail"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff default_option_def Exn_def)
  done

lemma L2_try_fail [L2opt]: "L2_try L2_fail = L2_fail"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff default_option_def Exn_def)
  done

lemma L2_while_fail [L2opt]: "L2_while C (\<lambda>_. L2_fail) i n = (L2_seq (L2_guard (\<lambda>s. \<not> C i s)) (\<lambda>_. L2_gets (\<lambda>s. i) n))"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (subst whileLoop_unroll)
  apply (auto simp add: run_condition run_bind run_guard)
  done

lemma unit_bind: "(\<lambda>x. f (x::unit)) = (\<lambda>_. f ())"
  apply (rule ext)
  subgoal for x by (cases x, auto)
  done

lemma unit_bind': "f \<equiv> (\<lambda>_. f ())"
  by (simp add:  unit_bind)


lemma L2_while_cong: 
  assumes c_eq: "\<And>r s. c r s = c' r s" 
  assumes bdy_eq: "\<And>r s. c' r s \<Longrightarrow> run (A r) s = run (A' r) s" 
  shows "L2_while c A  = L2_while c' A'"
  apply (rule ext)+
  unfolding L2_while_def
  using whileLoop_cong c_eq bdy_eq
  apply metis
  done



lemma L2_while_simp_cong: 
  assumes c_eq: "\<And>r s. c r s = c' r s" 
  assumes bdy_eq[simplified simp_implies_def]: "\<And>r s. c' r s =simp=> run (A r) s = run (A' r) s" 
  shows "L2_while c A  = L2_while c' A' "
  apply (rule L2_while_cong)
   apply (simp add: c_eq)
  apply (simp add: bdy_eq)
  done

lemma L2_while_cong': 
  assumes c_eq: "c = c'" 
  assumes bdy_eq: "\<And>r s. c' r s \<Longrightarrow> run (A r) s = run (A' r) s"  
  shows "L2_while c A = L2_while c' A'"
  apply (rule L2_while_cong)
   apply (simp add: c_eq)
  apply (simp add: bdy_eq)
  done

lemma L2_while_simp_cong': 
  assumes c_eq: "c = c'" 
  assumes bdy_eq[simplified simp_implies_def]: "\<And>r s. c' r s =simp=> run (A r) s = run (A' r) s"  
  shows "L2_while c A = L2_while c' A'"
  apply (rule L2_while_cong)
   apply (simp add: c_eq)
  apply (simp add: bdy_eq)
  done


lemma L2_while_cong_split: 
  assumes c_eq: "c = c'" 
  assumes bdy_eq: "PROP SPLIT (\<And>r s. c' r s \<Longrightarrow>run (A r) s = run (A' r) s)"  
  shows "L2_while c A = L2_while c' A'"
  apply (rule L2_while_simp_cong' [OF c_eq])
  using bdy_eq 
  by (simp add: SPLIT_def simp_implies_def)

lemma L2_while_cong_simp_split: 
  assumes c_eq: "c = c'" 
  assumes bdy_eq: "PROP SPLIT (\<And>r s. c' r s =simp=> run (A r) s = run (A' r) s)"  
  shows "L2_while c A = L2_while c' A'"
  apply (rule L2_while_simp_cong' [OF c_eq])
  using bdy_eq 
  by (simp add: SPLIT_def simp_implies_def)


lemma L2_while_cong_split_stop: 
  assumes c_eq: "c = c'" 
  assumes bdy_eq: "PROP SPLIT (\<And>r s. c' r s \<Longrightarrow> run (A r) s = run (A' r) s)"  
  shows "L2_while c A = STOP (L2_while c' A')"
  apply (simp add: STOP_def)
  apply (rule L2_while_simp_cong' [OF c_eq])
  using bdy_eq 
  by (simp add: SPLIT_def simp_implies_def)

lemma L2_while_cong_simp_split_stop: 
  assumes c_eq: "c = c'" 
  assumes bdy_eq: "PROP SPLIT (\<And>r s. c' r s =simp=> run (A r) s = run (A' r) s)"  
  shows "L2_while c A = STOP (L2_while c' A')"
  apply (simp add: STOP_def)
  apply (rule L2_while_simp_cong' [OF c_eq])
  using bdy_eq 
  by (simp add: SPLIT_def simp_implies_def)

lemma L2_while_cong'': 
  assumes c_eq: "c = c'" 
  assumes bdy_eq: "\<And>r s. c' r s \<Longrightarrow> run (A r) s = run (A' r) s"  
  assumes i_eq: "i = i'"
  shows "L2_while c A i ns = L2_while c' A' i' ns"
  apply (simp add: i_eq)
  using c_eq bdy_eq L2_while_cong
  by metis
  

lemma L2_returncall_trivial [L2opt]:
  "\<lbrakk> \<And>s v. f v s = v \<rbrakk> \<Longrightarrow> L2_returncall x f = L2_call x"
  unfolding L2_defs L2_call_def L2_returncall_def
  apply (rule ext)+
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  by (auto simp add: runs_to_def_old map_exn_def Exn_def default_option_def split:xval_splits )
 

(*
 * Trim "L2_gets" commands where the value is never actually used.
 *
 * This would be nice to apply automatically, but in practice causes
 * everything to slow down significantly. This suffers from the same exponential blowup as L2_unknown_bind
 * Introduced L2_gets_unbound as a weaker variant.
 *)
lemma L2_gets_unused:
  "\<lbrakk> \<And>x y s. run (B x) s = run (B y) s \<rbrakk> \<Longrightarrow> L2_seq (L2_gets A n) B = (B undefined)"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_bind)
  done

lemma L2_gets_unbound[L2opt]:
 "L2_seq (L2_gets A n) (\<lambda>x. f) = f"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_bind)
  done

lemma L2_gets_bind:
  "L2_seq (L2_gets (\<lambda>_. x :: 'var_type) n) f = f x"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (simp add: run_bind)
  done

lemma L2_gets_bind_stop_cong:
"L2_seq (L2_gets (\<lambda>_. x) n) f = L2_seq (L2_gets (\<lambda>_. x) n) f"
  by simp

lemma L2_seq_stop_cong:
 "L2_seq x y = L2_seq x y"
  by simp

lemma L2_marked_seq_gets_apply:
 "L2_seq_gets c n A \<equiv> A c"
  unfolding L2_seq_gets_def
  apply (rule eq_reflection)
  by  (rule L2_gets_bind )


(* N.S.: Why not propagate split to G, G (a, b) instead of G x? *)
(* fixme: do we still need this? *)
lemma split_seq_assoc [L2opt]:
     "(\<lambda>x. L2_seq (case x of (a, b) \<Rightarrow> B a b) (G x)) = (\<lambda>x. case x of (a, b) \<Rightarrow> (L2_seq (B a b) (G x)))"
  by (rule ext) clarsimp

lemma whileLoop_succeeds_terminates_infinite': 
  assumes "run (whileLoop (\<lambda>_. C) (\<lambda>x. gets (\<lambda>s. B s x)) i) s \<noteq> \<top>"
  shows "C s \<Longrightarrow> False"
  using assms
  by (induct rule: whileLoop_ne_top_induct) (auto simp: runs_to_iff)

lemma run_whileLoop_infinite': "run (whileLoop (\<lambda>i. C)
                (\<lambda>x. gets (\<lambda>s. B s x))
               i)
          s =
         run (guard (\<lambda>s. \<not> C s) \<bind> (\<lambda>_. gets (\<lambda>_. i))) s"
proof (cases "C s")
  case True
  show ?thesis 
    apply (rule antisym)
    subgoal 
      apply (subst whileLoop_unroll)
      apply (simp add: run_guard True run_bind)
      done
    subgoal
    proof -
      have "\<not> run (whileLoop (\<lambda>_. C) (\<lambda>x. gets (\<lambda>s. B s x)) i) s \<noteq> top"
        using True whileLoop_succeeds_terminates_infinite'[of C B i s] by auto
      hence "\<not> succeeds (whileLoop  (\<lambda>_. C) (\<lambda>x. gets (\<lambda>s. B s x)) i) s"
        by (simp add: succeeds_def)
      then show ?thesis
        by (simp add: run_guard run_bind succeeds_def True top_post_state_def)
    qed
    done
 next
  case False
  then show ?thesis apply (subst whileLoop_unroll) by (simp add: run_bind run_guard)
qed

lemma whileLoop_infinite':
  "whileLoop (\<lambda>i. C)
                (\<lambda>x. gets (\<lambda>s. B s x))
               i
           =
         guard (\<lambda>s. \<not> C s) \<bind> (\<lambda>_. gets (\<lambda>_. i))"
  apply (rule spec_monad_ext)
  apply (rule run_whileLoop_infinite')
  done

lemma L2_while_infinite [L2opt]:
        "L2_while (\<lambda>i s. C s) (\<lambda>x. L2_gets (\<lambda>s. B s x) n') i n
                  = (L2_seq (L2_guard (\<lambda>s. \<not> C s)) (\<lambda>_. L2_gets (\<lambda>_. i) n))"
  unfolding L2_defs
  by (rule whileLoop_infinite')


(*
 * We are happy to collapse away automatically generated constructs.
 *
 * In particular, anything of type "c_exntype" (which is used to track
 * what the current exception represents at the C level) is
 * autogenerated, and hence can be collapsed.
 *)
lemmas L2_gets_bind_c_exntype [L2opt] = L2_gets_bind [where 'var_type="'gx c_exntype"]

lemmas L2_gets_bind_unit [L2opt] = L2_gets_bind [where 'var_type=unit]

declare L2_voidcall_def [L2opt]
declare L2_modifycall_def [L2opt]
declare ucast_id [L2opt]
declare scast_id [L2opt]

(* Other misc lemmas. *)
declare singleton_iff [L2opt]

(* Optimising "if" structres. *)

lemma L2_gets_L2_seq_if_P_1_0 [L2opt]:
    "L2_seq (L2_gets (\<lambda>s. if P s then 1 else 0) n) (\<lambda>x. Q x)
        = (L2_seq (L2_gets P n) (\<lambda>x. Q (if x then 1 else 0)))"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


(* Join up guards, so that we can potentially solve some just by using
 * HOL.conj_cong. We will split them out again during the polish phase. *)

lemma L2_guard_join_simple [L2opt]: 
  "L2_seq (L2_guard A) (\<lambda>_. L2_guard B) = L2_guard (\<lambda>s. A s \<and> B s)"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L2_guard_join_nested [L2opt]:
      "L2_seq (L2_guard A) (\<lambda>_. L2_seq (L2_guard B) (\<lambda>_. C))
            = L2_seq (L2_guard (\<lambda>s. A s \<and> B s)) (\<lambda>_. C)"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

end
