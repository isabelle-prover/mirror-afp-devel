(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ExceptionRewrite
imports L1Defs L1Peephole
begin


(* The given block of code always fails. *)
definition "always_fail P A \<equiv> \<forall>s. P s \<longrightarrow> run A s = Failure"

lemma always_fail_fail [simp]: "always_fail P fail"
  by (clarsimp simp: always_fail_def top_post_state_def)

lemma bindE_alwaysfail_lhs: "\<lbrakk> always_fail (\<lambda>_. True) L \<rbrakk> \<Longrightarrow> always_fail (\<lambda>_. True) (L >>= R)"
  apply (clarsimp simp: always_fail_def run_bind)
  done

lemma bindE_alwaysfail_rhs: "\<lbrakk> always_progress L; no_throw (\<lambda>_. True) L; \<And>x. always_fail (\<lambda>_. True) (R x) \<rbrakk> \<Longrightarrow> always_fail (\<lambda>_. True) (L >>= R)"
  apply (clarsimp simp: always_fail_def no_throw_def always_progress_def)
  apply (clarsimp simp add: run_bind runs_to_partial.rep_eq
      bind_post_state_eq_top[unfolded top_post_state_def])
  subgoal premises prems for s
    using prems(1,2)[rule_format, of s] prems(4)
    apply (cases "run L s")
    subgoal by (auto simp: Ball_def split: prod.splits exception_or_result_splits)
    subgoal by force
    done
  done
 

lemma handleE'_alwaysfail_lhs: "\<lbrakk> always_fail (\<lambda>_. True) L \<rbrakk> \<Longrightarrow> always_fail (\<lambda>_. True) (L <catch> R)"
  by (clarsimp simp: always_fail_def run_catch)


lemma handleE'_alwaysfail_rhs: "\<lbrakk> always_progress L; no_return (\<lambda>_. True) L; \<And>r. always_fail (\<lambda>_. True) (R r) \<rbrakk> \<Longrightarrow> always_fail (\<lambda>_. True) (L <catch> R)"
  apply (clarsimp simp: always_fail_def no_return_def always_progress_def)
  subgoal premises prems for s
  proof (cases "run L s")
    case Failure
    then show ?thesis by (auto simp add: run_catch)
  next
    case (Success x2)
    then show ?thesis using prems 
      apply (clarsimp simp add: run_catch runs_to_partial_def_old reaches_def )
      apply (erule_tac x=s in allE)+
      apply (simp add: succeeds_def)
      apply (clarsimp simp add: bot_post_state_def Exn_def default_option_def)
      using image_iff by fastforce
  qed
  done

lemma alwaysfail_noreturn: "always_fail P A \<Longrightarrow> no_return P A"
  by (clarsimp simp: always_fail_def no_return_def runs_to_partial_def_old succeeds_def 
      top_post_state_def)

lemma alwaysfail_nothrow: "always_fail P A \<Longrightarrow> no_throw P A"
  by (clarsimp simp: always_fail_def no_throw_def runs_to_partial_def_old succeeds_def 
      top_post_state_def)


lemma no_return_Success_distrib_aux1:
  assumes "\<forall>(a ,b) \<in> X. \<exists>e. a = Exception e \<and> e \<noteq> default"  
  shows "X = apfst (Exception o the_Exception) ` X \<and> (\<forall>a \<in> fst ` X. the_Exception a \<noteq> default)"
  using assms
  by (force simp add: image_def apfst_def map_prod_def)

lemma no_return_Success_distrib_aux2:
  assumes "\<forall>(a ,b) \<in> X. \<exists>e. a = Exception e \<and> e \<noteq> default"  
  shows "P (\<Squnion>x\<in>X.
               case x of (Exception e, t) \<Rightarrow> f e t
               | (Result v, t) \<Rightarrow> g v t) \<longleftrightarrow>
         (P (\<Squnion>(e, t) \<in> apfst (the_Exception) ` X.
               f e t))"
  apply (subst no_return_Success_distrib_aux1 [OF assms])
  by (smt (verit, ccfv_SIG) apfst_conv assms case_exception_or_result_Exception 
      case_prodE case_prod_conv comp_apply image_cong image_image the_Exception_simp)

lemma no_return_Success_distrib_aux3:
  assumes "\<forall>(a ,b) \<in> X. \<exists>e. a = Exception e \<and> e \<noteq> default"  
  shows "P (\<Squnion>x\<in>X.
               case x of (Exception e, t) \<Rightarrow> f e t
               | (Result v, t) \<Rightarrow> g v t) \<longleftrightarrow>
         (X = apfst (Exception o the_Exception) ` X \<and> P (\<Squnion>(e, t) \<in> apfst (the_Exception) ` X.
               f e t))"
  using no_return_Success_distrib_aux1 [OF assms] no_return_Success_distrib_aux2 [OF assms, where P=P]
  apply simp
  done

lemma no_return_bindE:
  "no_return (\<lambda>_. True) A \<Longrightarrow> (A >>= B) = A"
  apply (rule spec_monad_ext)
  subgoal for s
    apply (cases "run A s")
    subgoal
      by (auto simp add: run_bind)
    subgoal for x2
      apply (cases "x2 = {}")
       apply (force simp: run_bind )
      apply (clarsimp simp add: run_bind no_return_def runs_to_partial_def_old 
          reaches_def succeeds_def top_post_state_def bot_post_state_def)
      apply (erule_tac x=s in allE)
      apply (clarsimp, safe)
      apply (subst (asm) no_return_Success_distrib_aux2 [where P = "\<lambda>X. X \<noteq> Success x2"])
      subgoal
        apply auto
        done
      subgoal
        apply (force simp: image_image split_beta' pure_post_state_def Sup_Success)
        done
      done
    done
  done

(*
 * "empty_fail" lemmas
 *)

lemma L1_skip_always_progress [simp, L1except, always_progress_intros]: 
  "always_progress L1_skip"
  unfolding L1_defs by (simp add: always_progress_intros)



lemma L1_modify_always_progress [simp, L1except, always_progress_intros]: 
  "always_progress (L1_modify m)"
  unfolding L1_defs by (simp add: always_progress_intros)


lemma L1_guard_always_progress [simp,L1except, always_progress_intros]: 
  "always_progress (L1_guard g)"
  unfolding L1_defs by (simp add: always_progress_intros)


lemma L1_init_always_progress [simp,L1except, always_progress_intros]: 
  "always_progress (L1_init v)"
  unfolding L1_defs by (simp add: always_progress_intros)

lemma L1_spec_always_progress [simp,L1except, always_progress_intros]: "always_progress (L1_spec s)"
  unfolding L1_defs by (simp add: always_progress_intros)

lemma L1_throw_always_progress [simp,L1except,always_progress_intros]: "always_progress L1_throw"
  unfolding L1_defs by (simp add: always_progress_intros)

lemma L1_fail_always_progress [simp,L1except, always_progress_intros]: "always_progress L1_fail"
  unfolding L1_defs by (simp add: always_progress_intros)


lemma L1_condition_always_progress[always_progress_intros]: 
  "\<lbrakk> always_progress L; always_progress R \<rbrakk> \<Longrightarrow> always_progress (L1_condition C L R)"
  unfolding L1_defs by (simp add: always_progress_intros)

lemma L1_seq_always_progress[always_progress_intros]: 
  "\<lbrakk> always_progress L; always_progress R \<rbrakk> \<Longrightarrow> always_progress (L1_seq L R)"
  unfolding L1_defs by (simp add: always_progress_intros)

lemma L1_catch_always_progress[always_progress_intros]: 
  "\<lbrakk> always_progress L; always_progress R \<rbrakk> \<Longrightarrow> always_progress (L1_catch L R)"
  unfolding L1_defs by (simp add: always_progress_intros)


lemma L1_while_always_progress[always_progress_intros]: 
  "always_progress B \<Longrightarrow> always_progress (L1_while C B)"
  unfolding L1_defs by (simp add: always_progress_intros)

lemma L1_call_always_progress[always_progress_intros]: "\<lbrakk> always_progress b \<rbrakk> \<Longrightarrow> always_progress (L1_call a b c d e)"
  unfolding L1_call_def by (simp add: always_progress_intros)

(*
 * no_throw lemmas.
 *)

lemma L1_skip_nothrow [simp,L1except]: "no_throw (\<lambda>_. True) L1_skip"
  by (clarsimp simp: L1_defs no_throw_def)

lemma L1_modify_nothrow [simp,L1except]: "no_throw (\<lambda>_. True) (L1_modify m)"
  by (clarsimp simp: L1_defs no_throw_def; runs_to_vcg)

lemma L1_guard_nothrow [simp,L1except]: "no_throw (\<lambda>_. True) (L1_guard g)"
  by (clarsimp simp: L1_defs no_throw_def; runs_to_vcg)

lemma L1_init_nothrow [simp,L1except]: "no_throw (\<lambda>_. True) (L1_init a)"
  by (clarsimp simp: L1_defs no_throw_def; runs_to_vcg)

lemma L1_spec_nothrow [simp,L1except]: "no_throw (\<lambda>_. True) (L1_spec a)"
  by (clarsimp simp: L1_defs no_throw_def; runs_to_vcg)

lemma L1_assume_nothrow [simp,L1except]: "no_throw (\<lambda>_. True) (L1_assume a)"
  by (clarsimp simp: L1_defs no_throw_def; runs_to_vcg)

lemma L1_fail_nothrow [simp,L1except]: "no_throw (\<lambda>_. True) L1_fail"
  by (clarsimp simp: L1_defs no_throw_def; runs_to_vcg)

lemma L1_while_nothrow [L1except]: "no_throw (\<lambda>_. True) B \<Longrightarrow> no_throw (\<lambda>_. True) (L1_while C B)"
  apply (clarsimp simp: L1_while_def)
  apply (clarsimp simp: no_throw_def)
  apply (rule runs_to_partial_whileLoop_exn [where I="\<lambda>r _. case r of Exn e \<Rightarrow> False | _ \<Rightarrow> True"])
     apply simp
    apply simp
  apply simp
  apply (fastforce simp add: runs_to_partial_def_old)
  done


lemma L1_catch_nothrow_lhs: "\<lbrakk> no_throw (\<lambda>_. True) L \<rbrakk> \<Longrightarrow> no_throw (\<lambda>_. True) (L1_catch L R)"
  apply (clarsimp simp: L1_defs no_return_def no_throw_def)
  apply (runs_to_vcg)
  apply (fastforce simp add: runs_to_partial_def_old)
  done

lemma L1_catch_nothrow_rhs: "\<lbrakk> no_throw (\<lambda>_. True) R \<rbrakk> \<Longrightarrow> no_throw (\<lambda>_. True) (L1_catch L R)"
  apply (clarsimp simp: L1_defs no_return_def no_throw_def)
  apply (runs_to_vcg)
  apply (fastforce simp add: runs_to_partial_def_old)
  done

lemma L1_catch_nothrow_both [L1except]: "no_throw (\<lambda>_. True) L \<or> no_throw (\<lambda>_. True) R \<Longrightarrow> no_throw (\<lambda>_. True) (L1_catch L R)"
  by (auto simp add: L1_catch_nothrow_lhs L1_catch_nothrow_rhs)

lemma bind_nothrow_simple: "\<lbrakk> no_throw (\<lambda>_. True) L; (\<And>x. no_throw (\<lambda>_. True) (R x)) \<rbrakk> \<Longrightarrow> no_throw (\<lambda>_. True) (bind L R)"
  apply (clarsimp simp: no_throw_def)
  apply (runs_to_vcg)
  apply (fastforce simp add: runs_to_partial_def_old)
  done

lemma L1_seq_nothrow [L1except]: "\<lbrakk> no_throw (\<lambda>_. True) L; no_throw (\<lambda>_. True) R \<rbrakk> \<Longrightarrow> no_throw (\<lambda>_. True) (L1_seq L R)"
  apply (clarsimp simp: L1_defs no_throw_def)
  apply (runs_to_vcg)
  apply (fastforce simp add: runs_to_partial_def_old)
  done

lemma L1_condition_nothrow [L1except]: 
  "\<lbrakk> no_throw (\<lambda>_. True) L; no_throw (\<lambda>_. True) R \<rbrakk> \<Longrightarrow> no_throw (\<lambda>_. True) (L1_condition C L R)"
  apply (clarsimp simp: L1_defs no_throw_def)
  apply (runs_to_vcg)
   apply (fastforce simp add: runs_to_partial_def_old)+
  done

lemma L1_call_nothrow[L1except]: "no_throw (\<lambda>_. True) y \<Longrightarrow> no_throw (\<lambda>_. True) (L1_call x y z q r)"
  apply (clarsimp simp: L1_call_def L1_defs no_throw_def)
  apply (runs_to_vcg)
  by (auto simp add: runs_to_partial_def_old)  
    (fastforce simp add: succeeds_bind reaches_bind)+


lemma no_throw_state_assumeE: "no_throw (\<lambda>_. True) (assume_result_and_state p)"
  apply (clarsimp simp: L1_defs no_throw_def)
  apply (runs_to_vcg)
  done

lemma no_throw_on_exit: 
  assumes c: "no_throw (\<lambda>_. True) c"
  shows "no_throw (\<lambda>_. True) (on_exit c cleanup)"
  using c
  apply (clarsimp simp: L1_defs no_throw_def on_exit'_def on_exit_def)
  apply (runs_to_vcg)
  apply (fastforce simp add: runs_to_partial_def_old  succeeds_bind reaches_bind)
  done

named_theorems no_throw_with_fresh_stack_ptr
lemma (in stack_heap_raw_state) no_throw_with_fresh_stack_ptr[no_throw_with_fresh_stack_ptr]:
  assumes c: "\<And>p. no_throw (\<lambda>_. True) (c p)"
  shows "no_throw (\<lambda>_. True) (with_fresh_stack_ptr n init c)"
  apply (simp add: with_fresh_stack_ptr_def)
  apply (rule bind_nothrow_simple)
   apply (rule no_throw_state_assumeE)
  apply (rule no_throw_on_exit)
  apply (rule c)
  done

lemmas L1_nothrows = 
  L1_seq_nothrow
  L1_skip_nothrow
  L1_modify_nothrow
  L1_condition_nothrow
  L1_catch_nothrow_both
  L1_while_nothrow
  L1_spec_nothrow
  L1_assume_nothrow
  L1_guard_nothrow
  L1_init_nothrow
  L1_call_nothrow
  L1_fail_nothrow


(*
 * no_return lemmas
 *)

lemma L1_throw_noreturn [simp,L1except]: "no_return (\<lambda>_. True) L1_throw"
  apply (clarsimp simp: L1_defs no_return_exn_def)
  done

lemma L1_fail_noreturn [simp,L1except]: "no_return (\<lambda>_. True) L1_fail"
  apply (clarsimp simp: L1_defs no_return_exn_def)
  done

lemma L1_seq_noreturn_lhs: "no_return (\<lambda>_. True) L \<Longrightarrow> no_return (\<lambda>_. True) (L1_seq L R)"
  apply (clarsimp simp: L1_defs no_return_exn_def)
  apply runs_to_vcg
  apply (fastforce simp add: runs_to_partial_def_old)
  done

lemma L1_seq_noreturn_rhs: "\<lbrakk> no_return (\<lambda>_. True) R \<rbrakk> \<Longrightarrow> no_return (\<lambda>_. True) (L1_seq L R)"
  apply (clarsimp simp: L1_defs no_return_exn_def)
  apply runs_to_vcg
  apply (fastforce simp add: runs_to_partial_def_old)
  done

lemma L1_catch_noreturn: "\<lbrakk> no_return (\<lambda>_. True) L; no_return (\<lambda>_. True) R \<rbrakk> \<Longrightarrow> no_return (\<lambda>_. True) (L1_catch L R)"
  apply (clarsimp simp: L1_defs no_return_exn_def)
  apply runs_to_vcg
  apply (fastforce simp add: runs_to_partial_def_old)
  done

lemma L1_condition_noreturn: "\<lbrakk> no_return (\<lambda>_. True) L; no_return (\<lambda>_. True) R \<rbrakk> \<Longrightarrow> no_return (\<lambda>_. True) (L1_condition C L R)"
  apply (clarsimp simp: L1_defs no_return_exn_def)
  apply runs_to_vcg
  apply (fastforce simp add: runs_to_partial_def_old)+
  done


lemma bindE_noreturn_lhs: "\<lbrakk>no_return (\<lambda>_. True) L \<rbrakk> \<Longrightarrow> no_return (\<lambda>_. True) (L >>= R)"
  apply (clarsimp simp: L1_defs no_return_def)
  apply runs_to_vcg
  apply (fastforce simp add: runs_to_partial_def_old)
  done

lemma bindE_noreturn_rhs: "\<lbrakk>\<And>x. no_return (\<lambda>_. True) (R x) \<rbrakk> \<Longrightarrow> no_return (\<lambda>_. True) (L >>= R)"
  apply (clarsimp simp: L1_defs no_return_def)
  apply runs_to_vcg
  apply (fastforce simp add: runs_to_partial_def_old)
  done


lemma on_exit_noreturn:  
  assumes c: "no_return (\<lambda>_. True) c"
  shows "no_return (\<lambda>_. True) (on_exit c cleanup)"
  using c
  unfolding on_exit_def on_exit'_def
  apply (clarsimp simp add: no_return_def)
  apply runs_to_vcg
  apply (fastforce simp add: runs_to_partial_def_old succeeds_bind reaches_bind)
  done


named_theorems no_return_with_fresh_stack_ptr
lemma (in stack_heap_raw_state) no_return_with_fresh_stack_ptr[no_return_with_fresh_stack_ptr]:
  assumes c: "\<And>p. no_return (\<lambda>_. True) (c p)"
  shows "no_return (\<lambda>_. True) (with_fresh_stack_ptr n init c)"
  apply (simp add: with_fresh_stack_ptr_def)
  apply (rule bindE_noreturn_rhs)
  apply (rule on_exit_noreturn)
  apply (rule c)
  done

(*
 * always_fail lemmas
 *)

lemma L1_fail_alwaysfail [simp,L1except]: "always_fail (\<lambda>_. True) L1_fail"
  by (clarsimp simp: L1_defs)

lemma L1_seq_alwaysfail_lhs: "\<lbrakk> always_fail (\<lambda>_. True) L \<rbrakk> \<Longrightarrow> always_fail (\<lambda>_. True) (L1_seq L R)"
  by (auto intro!: bindE_alwaysfail_lhs simp: L1_defs)

lemma L1_seq_alwaysfail_rhs: "\<lbrakk> always_progress L; no_throw (\<lambda>_. True) L; always_fail (\<lambda>_. True) R \<rbrakk> \<Longrightarrow> always_fail (\<lambda>_. True) (L1_seq L R)"
  by (auto intro!: bindE_alwaysfail_rhs simp: L1_defs)

lemma L1_catch_alwaysfail_lhs: "\<lbrakk> always_fail (\<lambda>_. True) L \<rbrakk> \<Longrightarrow> always_fail (\<lambda>_. True) (L1_catch L R)"
  by (clarsimp simp add: L1_defs always_fail_def run_catch)

lemma L1_catch_alwaysfail_rhs: "\<lbrakk> always_progress L; no_return (\<lambda>_. True) L; always_fail (\<lambda>_. True) R \<rbrakk> 
  \<Longrightarrow> always_fail (\<lambda>_. True) (L1_catch L R)"
  apply (clarsimp simp add: L1_defs always_fail_def always_progress_def no_return_def run_catch
      bind_post_state_eq_top[unfolded top_post_state_def] prod_eq_iff runs_to_partial.rep_eq
      split: prod.splits xval_splits)
  subgoal premises prems for s
    using prems(1,2)[rule_format, of s] prems(4)
    apply (cases "run L s")
    apply (auto simp: split_beta' Exn_def default_option_def) 
    done
  done

lemma L1_condition_alwaysfail: "\<lbrakk> always_fail (\<lambda>_. True) L; always_fail (\<lambda>_. True) R \<rbrakk> \<Longrightarrow> always_fail (\<lambda>_. True) (L1_condition C L R)"
  by (auto simp add: L1_defs always_fail_def run_condition)

(*
 * Rewrite rules.
 *)

lemma L1_catch_nothrow [(*L1except*)]:
  "no_throw (\<lambda>_. True) A \<Longrightarrow> L1_catch A E = A"
  unfolding L1_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (fastforce simp add: no_throw_def runs_to_partial_def_old runs_to_def_old)+
  done

lemma L1_seq_noreturn [L1except]:
  "no_return (\<lambda>_. True) A \<Longrightarrow> L1_seq A B = A"
  unfolding L1_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (fastforce simp add: no_return_def runs_to_partial_def_old runs_to_def_old)+
  done


lemma L1_catch_throw [L1except]:
  "L1_catch L1_throw E = E"
  unfolding L1_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


lemma anything_to_L1_fail [L1except]:
  "always_fail (\<lambda>_. True) A \<Longrightarrow> A = L1_fail"
  unfolding L1_defs
  apply (rule spec_monad_ext)
  apply (auto simp add: always_fail_def top_post_state_def)
  done

lemmas L1_is_local_simps [L1except] = is_local_simps

lemma L1_catch_return [L1except]: "(\<And>s. is_local (get_exn (upd_exn s))) \<Longrightarrow> 
       (L1_seq
         (L1_modify (upd_exn))
         (L1_condition (\<lambda>s. is_local (get_exn s))
           L1_skip L1_throw)) 
       = L1_modify (upd_exn)"
  unfolding L1_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


(*
lemma L1_seq_fail [L1except]:
  "\<lbrakk> empty_fail L; no_throw (\<lambda>_. True) L; always_fail (\<lambda>_. True) R \<rbrakk> \<Longrightarrow> L1_seq L R = L1_fail"
  apply (subst (2) anything_to_L1_fail)
   apply (rule L1_seq_alwaysfail_rhs)
     apply auto
  done
*)

lemma L1_catch_L1_seq_nothrow [L1except]:
  "\<lbrakk>no_throw (\<lambda>_. True) A \<rbrakk> \<Longrightarrow> L1_catch (L1_seq A B) C = L1_seq A (L1_catch B C)"
  unfolding L1_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (fastforce simp add: no_throw_def runs_to_partial_def_old runs_to_def_old)+
  done


lemma L1_catch_simple_seq [L1except]:
  "L1_catch (L1_seq L1_skip B) E = (L1_seq L1_skip (L1_catch B E))"
  "L1_catch (L1_seq L1_fail B) E = (L1_seq L1_fail (L1_catch B E))"
  "L1_catch (L1_seq (L1_modify m) B) E = (L1_seq (L1_modify m) (L1_catch B E))"
  "L1_catch (L1_seq (L1_spec s) B) E = (L1_seq (L1_spec s) (L1_catch B E))"
  "L1_catch (L1_seq (L1_assume f) B) E = (L1_seq (L1_assume f) (L1_catch B E))"
  "L1_catch (L1_seq (L1_guard g) B) E = (L1_seq (L1_guard g) (L1_catch B E))"
  "L1_catch (L1_seq (L1_init i) B) E = (L1_seq (L1_init i) (L1_catch B E))" 
  apply (subst L1_catch_seq_join | rule L1_nothrows | clarsimp simp: L1_defs | rule bind_nothrow_simple)+
  done


declare L1_catch_simple_seq(6) [L1opt]
lemma L1_catch_L1_init_seq'[L1opt, L1except]: "L1_catch (L1_seq (L1_seq (L1_init i) A) B) E = (L1_seq (L1_init i) (L1_catch (L1_seq A B) E))"
  apply (subst L1_catch_seq_join)
  apply simp 
  apply (subst L1_seq_assoc)
  apply simp
  done

lemma L1_catch_call_simple_seq [L1except]: 
 "no_throw (\<lambda>_. True) b \<Longrightarrow> L1_catch (L1_seq (L1_call a b c d e) B) E = (L1_seq (L1_call a b c d e) (L1_catch B E))"
  apply (subst L1_catch_seq_join)
   apply (rule L1_call_nothrow)
   apply (assumption)
  apply simp
  done 

lemma L1_catch_single [L1except]:
  "L1_catch (L1_skip) E = L1_skip"
  "L1_catch (L1_fail) E =  L1_fail"
  "L1_catch (L1_modify m) E = L1_modify m"
  "L1_catch (L1_spec s) E = L1_spec s"
  "L1_catch (L1_assume f) E = L1_assume f"
  "L1_catch (L1_guard g) E = L1_guard g"
  "L1_catch (L1_init i) E = L1_init i"
  apply (subst L1_catch_nothrow | rule L1_nothrows | clarsimp simp: L1_defs  | rule bind_nothrow_simple)+
  done

lemma  L1_catch_call_single [L1except]: "no_throw (\<lambda>_. True) b \<Longrightarrow> L1_catch (L1_call a b c d e) E = L1_call a b c d e"
  apply (subst L1_catch_nothrow)
   apply (rule L1_call_nothrow)
   apply assumption
  apply simp
  done

lemma L1_catch_single_while [L1except]:
  "\<lbrakk> no_throw (\<lambda>_. True) B \<rbrakk> \<Longrightarrow> L1_catch (L1_while C B) E = L1_while C B"
  apply (rule L1_catch_nothrow)
  apply (rule L1_while_nothrow)
  apply assumption
  done


lemma L1_catch_seq_while [L1except]:
  "\<lbrakk> no_throw (\<lambda>_. True) B \<rbrakk> \<Longrightarrow> L1_catch (L1_seq (L1_while C B) X) E = L1_seq (L1_while C B) (L1_catch X E)"
  apply (rule L1_catch_seq_join [symmetric])
  apply (rule L1_while_nothrow)
  apply assumption
  done

lemma L1_catch_single_cond [L1except]:
  "L1_catch (L1_condition C L R) E = L1_condition C (L1_catch L E) (L1_catch R E)"
  unfolding L1_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


(* Exponential: can only apply in certain circumstances. *)
lemma L1_catch_cond_seq:
  "L1_catch (L1_seq (L1_condition C L R) B) E = L1_condition C (L1_catch (L1_seq L B) E) (L1_catch (L1_seq R B) E)"
  apply (subst L1_condition_distrib)
  apply (rule L1_catch_single_cond)
  done

(* This exciting lemma lets up break up a L1_catch into two parts in
 * the exciting circumstance that "E" never returns. *)
lemma L1_catch_seq_cond_noreturn_ex:
  "\<lbrakk> no_return (\<lambda>_. True) E \<rbrakk> \<Longrightarrow> (L1_catch (L1_seq (L1_condition c A B) C) E) = (L1_seq (L1_catch (L1_condition c A B) E) (L1_catch C E))"
  unfolding L1_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  by (auto simp add: no_return_def runs_to_partial_def_old runs_to_def_old Exn_def)
     (metis  Exception_eq_Result reaches_succeeds  default_option_def )+


lemmas L1_catch_seq_cond_nothrow = L1_catch_L1_seq_nothrow [OF L1_condition_nothrow]

end
