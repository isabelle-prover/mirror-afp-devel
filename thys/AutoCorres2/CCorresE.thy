(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * A simple CCorres framework extension supporting exceptions on the monadic side.
 *)

theory CCorresE
  imports 
    SimplBucket
begin



(*
 * A special form of "ccorres" where either side may throw an
 * exception if the other also throws an exception.
 *)
definition
  ccorresE :: "('t \<Rightarrow> 's) \<Rightarrow> bool \<Rightarrow> 'ee set \<Rightarrow> ('p \<Rightarrow> ('t, 'p, 'ee) com option)
                        \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('t set)
                        \<Rightarrow> (unit, unit, 's) exn_monad \<Rightarrow> ('t, 'p, 'ee) com \<Rightarrow> bool"
where
  "ccorresE st check_term AF \<Gamma> G G' \<equiv>
   \<lambda>m c. \<forall>s. G (st s) \<and> (s \<in> G') \<and> succeeds m (st s) \<longrightarrow>
  ((\<forall>t. \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
   (case t of
         Normal s' \<Rightarrow> reaches m (st s) (Result ()) (st s')
       | Abrupt s' \<Rightarrow> reaches m (st s) (Exn ()) (st s')
       | Fault e \<Rightarrow> e \<in> AF
       | _ \<Rightarrow> False))
   \<and> (check_term \<longrightarrow> \<Gamma> \<turnstile> c \<down> Normal s))"

lemma ccorresE_cong:
  "\<lbrakk> \<And>s. P s = P' s;
     \<And>s. (s \<in> Q) = (s \<in> Q');
     \<And>s. P' s \<Longrightarrow> run f s = run f' s;
     \<And>s x. s \<in> Q' \<Longrightarrow> \<Gamma>\<turnstile> \<langle>g, Normal s\<rangle> \<Rightarrow> x = \<Gamma>\<turnstile> \<langle>g', Normal s\<rangle> \<Rightarrow> x
   \<rbrakk> \<Longrightarrow>
  ccorresE st ct AF \<Gamma> P Q f g = ccorresE st ct AF \<Gamma> P' Q' f' g"
  apply atomize
  apply (clarsimp simp: ccorresE_def split: xstate.splits)
  by (auto simp add: succeeds_def reaches_def)

lemma ccorresE_guard_imp:
  "\<lbrakk> ccorresE st ct AF \<Gamma> Q Q' A B; \<And>s. P s \<Longrightarrow> Q s; \<And>t. t \<in> P' \<Longrightarrow> t \<in> Q' \<rbrakk>  \<Longrightarrow> ccorresE st ct AF \<Gamma> P P' A B"
  apply atomize
  apply (clarsimp simp: ccorresE_def split: xstate.splits)
  done

lemma ccorresE_guard_imp_stronger:
  "\<lbrakk> ccorresE st ct AF \<Gamma> Q Q' A B;
     \<And>s. \<lbrakk> P (st s); s \<in> P' \<rbrakk> \<Longrightarrow> Q (st s);
     \<And>s. \<lbrakk> P (st s); s \<in> P' \<rbrakk> \<Longrightarrow> s \<in> Q' \<rbrakk> \<Longrightarrow>
  ccorresE st ct AF \<Gamma> P P' A B"
  apply atomize
  apply (clarsimp simp: ccorresE_def split_def split: xstate.splits)
  done

lemma ccorresE_assume_pre:
  "\<lbrakk> \<And>s. \<lbrakk> G (st s); s \<in> G' \<rbrakk> \<Longrightarrow>
         ccorresE st ct AF \<Gamma> (G and (\<lambda>s'. s' = st s)) (G' \<inter> {t'. t' = s}) A B \<rbrakk> \<Longrightarrow>
     ccorresE st ct AF \<Gamma> G G' A B"
  apply atomize
  apply (simp add: ccorresE_def pred_conj_def)
  done

lemma ccorresE_Seq:
  "\<lbrakk> ccorresE st ct AF \<Gamma> \<top> UNIV L L';
     ccorresE st ct AF \<Gamma> \<top> UNIV R R' \<rbrakk> \<Longrightarrow>
   ccorresE st ct AF \<Gamma> \<top> UNIV (do {_ \<leftarrow> L; R }) (L' ;; R')"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
  subgoal
    apply (clarsimp split: xstate.splits
        simp add: succeeds_bind reaches_bind, intro conjI)
    by (metis (mono_tags, lifting) Normal_resultE case_exception_or_result_Result)
      (metis (mono_tags, lifting) case_exception_or_result_Exn 
        case_exception_or_result_Result exec_Normal_elim_cases(1) 
        exec_Normal_elim_cases(3) xstate.exhaust)+
  subgoal
    apply (clarsimp split: xstate.splits
        simp add: succeeds_bind reaches_bind)
    by (metis Abrupt Fault terminates.Seq xstate.exhaust)
  done
 
lemma ccorresE_Cond:
  "\<lbrakk> ccorresE st ct AF \<Gamma> \<top> C A L';
     ccorresE st ct AF \<Gamma> \<top> (UNIV - C) A R' \<rbrakk> \<Longrightarrow>
   ccorresE st ct AF \<Gamma> \<top> UNIV A (Cond C L' R')"
  apply (clarsimp simp: ccorresE_def pred_neg_def)
  subgoal for s
    apply (rule conjI)
     apply clarsimp
     apply (erule exec_Normal_elim_cases)
      apply (erule_tac x=s in allE, erule impE, fastforce, fastforce)
     apply (erule_tac x=s in allE, erule impE, fastforce, fastforce)
    apply clarsimp
    apply (cases "s \<in> C")
     apply (rule terminates.CondTrue, assumption)
     apply (erule allE, erule impE, fastforce)
     apply clarsimp
    apply (rule terminates.CondFalse, assumption)
    apply (erule allE, erule impE, fastforce)
    apply clarsimp
    done
  done

lemma ccorresE_Cond_match:
  "\<lbrakk> ccorresE st ct AF \<Gamma> C C' L L';
     ccorresE st ct AF \<Gamma> (not C) (UNIV - C') R R';
     \<And>s. C (st s) = (s \<in> C') \<rbrakk> \<Longrightarrow>
   ccorresE st ct AF \<Gamma> \<top> UNIV (condition C L R) (Cond C' L' R')"
  apply atomize
  apply (simp add: ccorresE_def pred_neg_def)
  apply clarify
  apply (intro conjI allI impI)

  subgoal for s t
    apply (auto elim!: exec_Normal_elim_cases split: xstate.splits)
    done
  subgoal for s
    apply (cases "s \<in> C'")
    subgoal
      by (simp add: terminates.CondTrue)
    subgoal
      by (simp add: terminates.CondFalse)
    done
  done

lemma ccorresE_Guard:
  "\<lbrakk> ccorresE st ct AF \<Gamma> \<top> G X Y \<rbrakk> \<Longrightarrow>  ccorresE st ct AF \<Gamma> \<top> G X (Guard F G Y)"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases, auto)[1]
  apply clarsimp
  apply (rule terminates.Guard, assumption)
  apply force
  done

lemma ccorresE_Catch:
  "\<lbrakk>ccorresE st ct AF \<Gamma> \<top> UNIV A A'; ccorresE st ct AF \<Gamma> \<top> UNIV B B'\<rbrakk> \<Longrightarrow>
    ccorresE st ct AF \<Gamma> \<top> UNIV (A <catch> (\<lambda>_. B)) (TRY A' CATCH B' END)"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x=s in allE)
   apply (erule exec_Normal_elim_cases)
  subgoal for s t s'
    apply (cases t)
    subgoal
      using reaches_catch
      by (metis case_xval_simps(1) succeeds_catch xstate.simps(16) xstate.simps(17))
    subgoal
      using reaches_catch
      by (metis case_xval_simps(1) succeeds_catch xstate.simps(17))
    subgoal
      using reaches_catch
      by (metis case_xval_simps(1) succeeds_catch xstate.simps(17) xstate.simps(18))
    subgoal
      using reaches_catch
      by (metis case_xval_simps(1) succeeds_catch xstate.simps(17) xstate.simps(19))
    done
  subgoal for s t

    apply (cases t)
       apply (fastforce simp add: reaches_catch succeeds_catch)+
    done
  subgoal for s
    by (metis case_xval_simps(1) succeeds_catch terminates.Catch xstate.simps(17))
  done


lemma ccorresE_Call:
  "\<lbrakk> \<Gamma> X' = Some Z'; ccorresE st ct AF \<Gamma> \<top> UNIV Z Z' \<rbrakk> \<Longrightarrow>
    ccorresE st ct AF \<Gamma> \<top> UNIV Z (Call X')"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
    apply (clarsimp)
   apply clarsimp
  apply clarify
  apply (erule terminates.Call)
  apply (erule allE, erule (1) impE)
  apply clarsimp
  done

lemma ccorresE_exec_Normal:
    "\<lbrakk> ccorresE st ct AF \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> Normal t; s \<in> G'; G (st s); succeeds B (st s) \<rbrakk> 
  \<Longrightarrow> reaches B (st s) (Result ()) (st t)"
  apply (clarsimp simp: ccorresE_def)
  apply force
  done

lemma ccorresE_exec_Abrupt:
    "\<lbrakk> ccorresE st ct AF \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> Abrupt t; s \<in> G'; G (st s); succeeds B (st s) \<rbrakk> 
  \<Longrightarrow> reaches B (st s) (Exn ()) (st t)"
  apply (clarsimp simp: ccorresE_def)
  apply force
  done

lemma ccorresE_exec_Fault:
    "\<lbrakk> ccorresE st ct AF \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> Fault f; f \<notin> AF; s \<in> G'; G (st s); succeeds B (st s) \<rbrakk> \<Longrightarrow> P"
  apply (clarsimp simp: ccorresE_def)
  apply force
  done

lemma ccorresE_exec_Stuck:
    "\<lbrakk> ccorresE st ct AF \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> Stuck; s \<in> G'; G (st s); succeeds B (st s) \<rbrakk> \<Longrightarrow> P"
  apply (clarsimp simp: ccorresE_def)
  apply force
  done

lemma ccorresE_exec_cases [consumes 5]:
    "\<lbrakk> ccorresE st ct AF \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> s'; s \<in> G'; G (st s); succeeds B (st s);
                  \<And>t'. \<lbrakk> s' = Normal t'; reaches B (st s) (Result ()) (st t')\<rbrakk> \<Longrightarrow> R;
                  \<And>t'. \<lbrakk> s' = Abrupt t'; reaches B (st s) (Exn ()) (st t') \<rbrakk> \<Longrightarrow> R;
                  \<And>f. \<lbrakk> s' = Fault f; f \<in> AF \<rbrakk> \<Longrightarrow> R
                  \<rbrakk> \<Longrightarrow> R"
  apply atomize
  apply (cases s')
     apply (drule ccorresE_exec_Normal, auto)[1]
    apply (drule ccorresE_exec_Abrupt, auto)[1]
  subgoal for f
    apply (cases "f \<in> AF")
    subgoal
      by auto
    subgoal
      by (drule ccorresE_exec_Fault, auto)[1]
    done
  apply (drule ccorresE_exec_Stuck, auto)[1]
  done

lemma ccorresE_terminates:
  "\<lbrakk> ccorresE st ct AF \<Gamma> \<top> UNIV B B'; succeeds B (st s); ct \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> B' \<down> Normal s"
   by (clarsimp simp: ccorresE_def)

lemma exec_While_final_inv':
  assumes exec: "\<Gamma>\<turnstile> \<langle>b, x\<rangle> \<Rightarrow> s'"
   shows
  "\<lbrakk> b = While C B; x = Normal s;
    \<And>s. \<lbrakk> s \<notin> C \<rbrakk> \<Longrightarrow> I s (Normal s);
    \<And>t t'. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Normal t'; I t' s' \<rbrakk> \<Longrightarrow> I t s';
    \<And>t t'. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Abrupt t' \<rbrakk> \<Longrightarrow> I t (Abrupt t');
    \<And>t. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Stuck \<rbrakk> \<Longrightarrow> I t Stuck;
    \<And>t f. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Fault f \<rbrakk> \<Longrightarrow> I t (Fault f) \<rbrakk>
    \<Longrightarrow> I s s'"
  using exec
  apply (induct arbitrary: s rule: exec.induct, simp_all)
  apply clarsimp
  apply atomize
  apply clarsimp
  apply (erule allE, erule (1) impE)
  apply (erule exec_elim_cases, auto)
  done

lemma exec_While_final_inv:
  "\<lbrakk> \<Gamma>\<turnstile> \<langle>While C B, Normal s\<rangle> \<Rightarrow> s';
    \<And>s. \<lbrakk> s \<notin> C \<rbrakk> \<Longrightarrow> I s (Normal s);
    \<And>t t'. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Normal t'; I t' s' \<rbrakk> \<Longrightarrow> I t s';
    \<And>t t'. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Abrupt t' \<rbrakk> \<Longrightarrow> I t (Abrupt t');
    \<And>t. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Stuck \<rbrakk> \<Longrightarrow> I t Stuck;
    \<And>t f. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Fault f \<rbrakk> \<Longrightarrow> I t (Fault f) \<rbrakk>
    \<Longrightarrow> I s s'"
   apply (erule exec_While_final_inv', (rule refl)+, simp_all)
   done

lemma ccorresE_termination':
  assumes no_fail: "succeeds (whileLoop CC BB r) s"
  and s_match: "s = st s' \<and> CC = (\<lambda>_. C) \<and> BB = (\<lambda>_. B)"
  and corres: "ccorresE st ct AF \<Gamma> \<top> UNIV B B'"
  and cond_match: "\<And>s. C (st s) = (s \<in> C')"
  and ct: "ct"
shows "\<Gamma>\<turnstile> While C' B' \<down> Normal s'"
proof -
  from no_fail have "run (whileLoop CC BB r) s \<noteq> \<top>"
    by (simp add: succeeds_def)
  from this show ?thesis
    using s_match
  proof (induct arbitrary: s' rule: whileLoop_ne_top_induct)
    case (step a s)
    then show ?case using corres cond_match ct
      apply (cases "s' \<notin> C'")
      apply (simp add: terminates.WhileFalse)
      apply (rule terminates.WhileTrue)
      apply simp
      subgoal
        by (simp add: runs_to_def_old ccorresE_terminates)
      subgoal
        apply (clarsimp simp: runs_to_def_old)
        by (metis Abrupt Fault ccorresE_exec_Normal ccorresE_exec_Stuck 
                  iso_tuple_UNIV_I top1I xstate.exhaust)
      done
  qed
qed

lemma ccorresE_termination:
  assumes no_fail: "succeeds (whileLoop (\<lambda>_. C) (\<lambda>_. B) r) s"
  and s_match: "s = st s'"
  and corres: "ccorresE st ct AF \<Gamma> \<top> UNIV B B'"
  and cond_match: "\<And>s. C (st s) = (s \<in> C')"
  and ct: "ct"
  shows "\<Gamma>\<turnstile> While C' B' \<down> Normal s'"
  apply (auto intro: ccorresE_termination' [OF no_fail _ corres _ ct] simp: s_match cond_match)
  done

lemma ccorresE_While:
  assumes body_refines: "ccorresE st ct AF \<Gamma> \<top> UNIV B B'"
      and cond_match: "\<And>s. C (st s) = (s \<in> C')"
    shows "ccorresE st ct AF \<Gamma> G G' (whileLoop (\<lambda>_. C) (\<lambda>_. B) ()) (While C' B')"
proof -
  {
    fix s t
    assume guard_abs: "G (st s)"
    assume guard_conc: "s \<in> G'"

    assume no_fail: "succeeds (whileLoop (\<lambda>_. C) (\<lambda>_. B) ()) (st s)"
    assume conc_steps: "\<Gamma>\<turnstile> \<langle>While C' B', Normal s\<rangle> \<Rightarrow> t"
    have "case t of
        Normal s' \<Rightarrow> reaches (whileLoop (\<lambda>_. C) (\<lambda>_. B) ()) (st s) (Result ()) (st s')
      | Abrupt s' \<Rightarrow> reaches (whileLoop (\<lambda>_. C) (\<lambda>_. B) ()) (st s) (Exn ()) (st s')
      | Fault e \<Rightarrow> e \<in> AF
      | _ \<Rightarrow> False"
      apply (insert no_fail, erule rev_mp)
      apply (rule exec_While_final_inv [OF conc_steps])
      subgoal
        using cond_match
        apply clarsimp
        apply (subst whileLoop_unroll)
        apply (simp add: reaches_condition_iff)
        done
      subgoal for t1 t'
        apply (subst (1 2 3) whileLoop_unroll)
        apply (clarsimp simp add: cond_match)
        using ccorresE_exec_Normal [OF body_refines, of t1 t']
        using cond_match
        apply (force split: xstate.splits simp add: succeeds_bind reaches_bind )
        done
      subgoal for t1 t'
        apply (subst (1 2 3) whileLoop_unroll)
        apply (clarsimp simp add: cond_match)
        using ccorresE_exec_Abrupt [OF body_refines, of t1 t']
        using cond_match
        apply (clarsimp simp add: succeeds_bind reaches_bind)
        using Exn_def by force
      subgoal for t
        apply (subst (1 2 3) whileLoop_unroll)
        apply (clarsimp simp add: cond_match)
        using ccorresE_exec_Stuck [OF body_refines, of t]
        apply (metis UNIV_I succeeds_bind top1I)
        done
      subgoal for t
        apply (subst (1 2 3) whileLoop_unroll)
        apply (clarsimp simp add: cond_match)
        using ccorresE_exec_Fault [OF body_refines, of t]
        apply (metis UNIV_I succeeds_bind top1I)
        done
      done
  }
  moreover
  {
    fix s
    assume guard_abs: "G (st s)"
    assume guard_conc: "s \<in> G'"
    assume no_fail: "succeeds (whileLoop (\<lambda>_. C) (\<lambda>_. B) ()) (st s)"
    have "ct \<longrightarrow> \<Gamma>\<turnstile>While C' B' \<down> Normal s"
      apply clarify
      apply (rule ccorresE_termination [OF no_fail])
         apply (rule refl)
        apply (rule body_refines)
       apply (rule cond_match)
      apply simp
      done
  }
  ultimately show ?thesis
    by (auto simp: ccorresE_def)
qed

lemma ccorresE_get:
  "(\<And>s. ccorresE st ct AF \<Gamma> (P and (\<lambda>s'. s' = s)) Q (L s) R) \<Longrightarrow> ccorresE st ct AF \<Gamma> P Q ((get_state) >>= L) R"
  apply atomize
  apply (auto simp add: ccorresE_def succeeds_bind reaches_bind pred_conj_def split: xstate.splits )
  done

lemma ccorresE_fail:
  "ccorresE st ct AF \<Gamma> P Q fail R"
  apply (clarsimp simp: ccorresE_def)
  done

lemma ccorresE_DynCom:
  "\<lbrakk> \<And>t. \<lbrakk> t \<in> P' \<rbrakk> \<Longrightarrow> ccorresE st ct AF \<Gamma> P (P' \<inter> {t'. t' = t}) A (B t) \<rbrakk> \<Longrightarrow> ccorresE st ct AF \<Gamma> P P' A (DynCom B)"
  apply atomize
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
   apply (erule allE, erule(1) impE)
   apply clarsimp
  apply clarify
  apply (rule terminates.DynCom)
  apply clarsimp
  done

lemma ccorresE_Catch_nothrow:
  "\<lbrakk>ccorresE st ct AF \<Gamma> \<top> UNIV A A'; \<not> exceptions_thrown A'\<rbrakk> \<Longrightarrow>
    ccorresE st ct AF \<Gamma> \<top> UNIV A (TRY A' CATCH B' END)"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
    apply (frule exceptions_thrown_not_abrupt, simp, simp)
    apply simp
   apply simp
  apply clarify
  apply (rule terminates.Catch)
   apply clarsimp
  apply clarsimp
  apply (drule (1) exceptions_thrown_not_abrupt)
   apply simp
  apply simp
  done


context stack_heap_state
begin


definition with_fresh_stack_ptr :: "nat \<Rightarrow> ('s \<Rightarrow> 'a list set) \<Rightarrow> ('a::mem_type ptr \<Rightarrow> ('e::default, 'v, 's) spec_monad) \<Rightarrow> ('e::default, 'v, 's) spec_monad"
  where
  "with_fresh_stack_ptr n I c \<equiv>
    do {
      p \<leftarrow> assume_result_and_state (\<lambda>s. {(p, t). \<exists>d vs bs. (p, d) \<in> stack_allocs n \<S> TYPE('a::mem_type) (htd s) \<and> 
           vs \<in> I s \<and> length vs = n \<and> length bs = n * size_of TYPE('a) \<and>
           t = hmem_upd (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs!i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n]) (htd_upd (\<lambda>_. d) s)});
      on_exit (c p)
        ({(s,t). \<exists>bs. length bs = n * size_of TYPE('a) \<and> t = hmem_upd (heap_update_list (ptr_val p) bs) (htd_upd (stack_releases n p) s)})
    }"

lemma monotone_with_fresh_stack_ptr_le[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>p. monotone R (\<le>) (\<lambda>f. c f p)"  
  shows "monotone R (\<le>) (\<lambda>f. with_fresh_stack_ptr n I (c f))"
  unfolding with_fresh_stack_ptr_def on_exit_def
  by (intro partial_function_mono)

lemma monotone_with_fresh_stack_ptr_ge[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>p. monotone R (\<ge>) (\<lambda>f. c f p)"  
  shows "monotone R (\<ge>) (\<lambda>f. with_fresh_stack_ptr n I (c f))"
  unfolding with_fresh_stack_ptr_def on_exit_def
  by (intro partial_function_mono)




ML \<open>
structure with_fresh_stack_ptr =
struct

type data = {
  match: term -> {n:term, init:term, c:term, ct_: term, instantiate: {n:term, init:term, c:term} -> term},
  cterm_match: cterm -> {n:cterm, init:cterm, c:cterm, ct_: cterm, instantiate: {n:cterm, init:cterm, c:cterm} -> cterm},
  term: typ -> term}

fun map_match f ({match, cterm_match, term}:data) = 
  {match = f match, cterm_match = cterm_match, term = term}:data
fun map_cterm_match f ({match, cterm_match, term}:data) = 
  {match = match, cterm_match = f cterm_match, term = term}:data
fun map_term f ({match, cterm_match, term}:data) = 
  {match = match, cterm_match = cterm_match, term = f term}:data

fun merge_match (f, g) = Utils.fast_merge (fn (f, g) => Utils.first_match [f, g]) (f, g)


structure Data = Generic_Data (
  type T = data;
  val empty = {match = fn _ => raise Match, cterm_match =  fn _ => raise Match, term = fn _ => raise Match}
  val merge = Utils.fast_merge (fn ({match = f1, cterm_match = g1, term = t1}, {match = f2, cterm_match = g2, term = t2}) =>
         {match = merge_match (f1, f2), cterm_match = merge_match (g1, g2), term = merge_match (t1, t2)}); 
)

fun match ctxt = #match (Data.get (Context.Proof ctxt))
fun cterm_match ctxt = #cterm_match (Data.get (Context.Proof ctxt))
fun term ctxt = #term (Data.get (Context.Proof ctxt))

fun add_match match = Data.map (map_match (Utils.add_match match))
fun add_cterm_match cterm_match = Data.map (map_cterm_match (Utils.add_match cterm_match))
fun add_term match = Data.map (map_term (Utils.add_match match))


end
\<close>

declaration \<open>
fn phi => fn context =>
 let
    val T = Morphism.typ phi @{typ 's}
    val t = Morphism.term phi @{term with_fresh_stack_ptr}
    val thy = Context.theory_of context
    fun term T' = 
      let
      in 
        if can (Sign.typ_match thy (T, T')) Vartab.empty then t else raise Match
      end
    fun match t = @{morph_match (fo) \<open>with_fresh_stack_ptr ?n ?init ?c\<close>} phi (Context.theory_of context) t
        handle Pattern.MATCH => raise Match
    fun cterm_match ct = @{cterm_morph_match (fo) \<open>with_fresh_stack_ptr ?n ?init ?c\<close>} phi ct
        handle Pattern.MATCH => raise Match
 in 
   context     
   |> with_fresh_stack_ptr.add_match match 
   |> with_fresh_stack_ptr.add_cterm_match cterm_match 
   |> with_fresh_stack_ptr.add_term term
 end
\<close>
 
end

end