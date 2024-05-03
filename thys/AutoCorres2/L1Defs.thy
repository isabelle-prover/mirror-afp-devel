(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


chapter \<open>L1 phase\<close>

theory L1Defs
imports CCorresE
begin

(* Definitions of constants used in the SimplConv output. *)
type_synonym 's L1_monad = "(unit, unit, 's) exn_monad"
definition "L1_seq (A :: 's L1_monad) (B :: 's L1_monad) \<equiv> (A >>= (\<lambda>_. B)) :: 's L1_monad"
definition "L1_skip \<equiv> return () :: 's L1_monad"
definition "L1_modify m \<equiv> (modify m) :: 's L1_monad"
definition "L1_condition c (A :: 's L1_monad) (B :: 's L1_monad) \<equiv> condition c A B"
definition "L1_catch (A :: 's L1_monad) (B :: 's L1_monad) \<equiv> (A <catch> (\<lambda>_. B))"
definition "L1_while c (A :: 's L1_monad) \<equiv> (whileLoop (\<lambda>_. c) (\<lambda>_. A) ())"
definition "L1_throw \<equiv> throw () :: 's L1_monad"
definition "L1_spec r \<equiv> state_select r :: 's L1_monad"
definition "L1_assume f \<equiv> assume_result_and_state f :: 's L1_monad"
definition "L1_guard c \<equiv> guard c :: 's L1_monad"
definition "L1_init v \<equiv> (do { x \<leftarrow> select UNIV; modify (v (\<lambda>_. x)) }) :: 's L1_monad"
definition "L1_call scope_setup (dest_fn :: 's L1_monad) scope_teardown result_exn return_xf \<equiv>
    do {
        s \<leftarrow> get_state;
        ((do { modify scope_setup;
              dest_fn })
         <catch> (\<lambda>_. L1_seq (modify (\<lambda>t. result_exn (scope_teardown s t) t)) L1_throw));
        t \<leftarrow> get_state;
        modify (scope_teardown s);
        modify (return_xf t)
    }"


definition "L1_fail \<equiv> fail :: 's L1_monad"
definition "L1_set_to_pred S \<equiv> \<lambda>s. s \<in> S"
definition "L1_rel_to_fun R = (\<lambda>s. Pair () ` Image R {s})"

lemma L1_rel_to_fun_alt: "L1_rel_to_fun R = (\<lambda>s. Pair () ` {s'. (s, s') \<in> R})"
  by (auto simp: L1_rel_to_fun_def)

lemmas L1_defs = L1_seq_def L1_skip_def L1_modify_def L1_condition_def
    L1_catch_def L1_while_def L1_throw_def L1_spec_def L1_assume_def L1_guard_def
    L1_fail_def L1_init_def L1_set_to_pred_def L1_rel_to_fun_def

lemmas L1_defs' = 
   L1_seq_def L1_skip_def L1_modify_def L1_condition_def L1_catch_def
   L1_while_def L1_throw_def L1_spec_def  L1_assume_def 
   L1_guard_def 
   L1_fail_def L1_init_def L1_set_to_pred_def L1_rel_to_fun_def

declare L1_set_to_pred_def [simp]
declare L1_rel_to_fun_def [simp]

definition L1_guarded:: "('s \<Rightarrow> bool) \<Rightarrow> 's L1_monad \<Rightarrow> 's L1_monad"
  where
"L1_guarded g f = L1_seq (L1_guard g) f"



locale L1_functions =
  fixes \<P>:: "unit ptr \<Rightarrow> 's L1_monad"
begin
  definition "L1_dyn_call g scope_setup (dest :: 's \<Rightarrow> unit ptr) scope_teardown result_exn return_xf \<equiv>
   L1_guarded g (gets dest >>= (\<lambda>p. L1_call scope_setup (\<P> p) scope_teardown result_exn return_xf))"
end


(* Our corres rule converting from the deeply-embedded SIMPL to a shallow embedding. *)
definition
  L1corres :: "bool \<Rightarrow> ('p \<Rightarrow> ('s, 'p, strictc_errortype) com option)  
                     \<Rightarrow> 's L1_monad \<Rightarrow> ('s, 'p, strictc_errortype) com \<Rightarrow> bool"
where
  "L1corres check_term \<Gamma> \<equiv>
   \<lambda>A C. \<forall>s. succeeds A s \<longrightarrow>
       ((\<forall>t. \<Gamma> \<turnstile> \<langle>C, Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
        (case t of
              Normal s' \<Rightarrow> reaches A s (Result ()) s'
            | Abrupt s' \<Rightarrow> reaches A s (Exn ()) s'
            | Fault e \<Rightarrow> e \<in> {AssumeError, StackOverflow}
            | _ \<Rightarrow> False))
        \<and> (check_term \<longrightarrow> \<Gamma> \<turnstile> C \<down> Normal s))"

definition
  L1corres' :: "bool \<Rightarrow> ('p \<Rightarrow> ('s, 'p, strictc_errortype) com option) \<Rightarrow> ('s \<Rightarrow> bool)  
                     \<Rightarrow> 's L1_monad \<Rightarrow> ('s, 'p, strictc_errortype) com \<Rightarrow> bool"
where
  "L1corres' check_term \<Gamma> P \<equiv>
   \<lambda>A C. \<forall>s. (P s) \<and> succeeds A s \<longrightarrow>
       ((\<forall>t. \<Gamma> \<turnstile> \<langle>C, Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
        (case t of
              Normal s' \<Rightarrow> reaches A s (Result ()) s'
            | Abrupt s' \<Rightarrow> reaches A s (Exn ()) s' 
            | Fault e \<Rightarrow> e \<in> {AssumeError, StackOverflow}
            | _ \<Rightarrow> False))
        \<and> (check_term \<longrightarrow> \<Gamma> \<turnstile> C \<down> Normal s))"


lemma L1corres_alt_def: "L1corres ct \<Gamma> = ccorresE (\<lambda>x. x) ct {AssumeError, StackOverflow} \<Gamma> \<top> UNIV"
  apply (rule ext)+
  apply (clarsimp simp: L1corres_def ccorresE_def)
  done

lemma L1corres'_alt_def: "L1corres' ct \<Gamma> P = ccorresE (\<lambda>x. x) ct {AssumeError, StackOverflow} \<Gamma> P UNIV"
  apply (rule ext)+
  apply (clarsimp simp: L1corres'_def ccorresE_def)
  done



lemma admissible_nondet_ord_L1corres [corres_admissible]:
  "ccpo.admissible Inf (\<ge>) (\<lambda>A. L1corres ct \<Gamma> A C)"
  unfolding L1corres_def imp_conjR  disj_imp[symmetric] 
  apply (intro admissible_all)
  apply (intro admissible_conj)
   apply (rule ccpo.admissibleI)
   apply (clarsimp split: xstate.splits)
   apply (intro conjI admissible_mem)
  subgoal   
    apply (simp add: ccpo.admissible_def chain_def 
        succeeds_def reaches_def split: prod.splits)
    apply transfer
    apply (clarsimp simp add: Inf_post_state_def top_post_state_def image_def vimage_def 
        split: if_split_asm)
    by (metis outcomes.simps(2) post_state.simps(3))
  subgoal
    apply (simp add: ccpo.admissible_def chain_def 
        succeeds_def reaches_def split: prod.splits)
    apply transfer
    apply (clarsimp simp add: Inf_post_state_def top_post_state_def image_def vimage_def 
        split: if_split_asm)
   by (metis outcomes.simps(2) post_state.simps(3))
  subgoal
    apply (simp add: ccpo.admissible_def chain_def 
        succeeds_def reaches_def split: prod.splits)
    apply transfer
    apply (clarsimp simp add: Inf_post_state_def top_post_state_def image_def vimage_def 
        split: if_split_asm)
   by (metis outcomes.simps(2) post_state.simps(3))
  subgoal
    apply (simp add: ccpo.admissible_def chain_def 
        succeeds_def reaches_def split: prod.splits)
    apply transfer
    apply (auto simp add: Inf_post_state_def top_post_state_def image_def vimage_def 
        split: if_split_asm)
    done
  apply (rule ccpo.admissibleI)
  apply (simp split: xstate.splits)
  apply (clarsimp simp add: ccpo.admissible_def chain_def 
      succeeds_def reaches_def split: prod.splits)
  apply transfer
  apply (auto simp add: Inf_post_state_def top_post_state_def image_def vimage_def 
      split: if_split_asm)
  done

lemma L1corres_top [corres_top]: "L1corres ct P \<top> C"
  by (auto simp add: L1corres_def)

lemma L1corres_guard_DynCom:
  "\<lbrakk>\<And>s. s \<in> g \<Longrightarrow> L1corres ct \<Gamma> (B s) (B' s)\<rbrakk> \<Longrightarrow>
      L1corres ct \<Gamma> (L1_seq (L1_guard (\<lambda>s. s \<in> g)) (gets B \<bind> (\<lambda>b. b))) (Guard f g (DynCom B'))"
  apply (clarsimp simp: L1corres_def L1_defs)
  apply (force elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind)
  done

lemma L1corres'_guard_DynCom_conseq:
  assumes conseq: "\<And>s. P s \<Longrightarrow> g s \<Longrightarrow> s \<in> g'"
  assumes corres: "\<And>s. P s \<Longrightarrow> g s \<Longrightarrow> L1corres' ct \<Gamma> (\<lambda>s. P s \<and> g s) (B s) (B' s)"
  shows "L1corres' ct \<Gamma> P (L1_seq (L1_guard g) (gets B \<bind> (\<lambda>b. b))) (Guard f g' (DynCom B'))"
  using conseq corres
  apply (clarsimp simp: L1corres'_def L1_defs)
  apply (force elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind)

  done



lemma L1corres'_guard_DynCom:
  "\<lbrakk>\<And>s. P s \<Longrightarrow> s \<in> g \<Longrightarrow> L1corres' ct \<Gamma> (\<lambda>s. P s \<and> s \<in> g) (B s) (B' s)\<rbrakk> \<Longrightarrow>
      L1corres' ct \<Gamma> P (L1_seq (L1_guard (\<lambda>s. s \<in> g)) (gets B \<bind> (\<lambda>b. b))) (Guard f g (DynCom B'))"
  apply (rule L1corres'_guard_DynCom_conseq [where B=B])
   apply simp
  apply simp
  done

lemma L1corres_DynCom: 
  assumes corres_f: "\<And>s. L1corres ct \<Gamma> (g s) (f s)" 
  shows "L1corres ct \<Gamma>  (gets g \<bind> (\<lambda>b. b)) (DynCom f)"
  using corres_f
  apply (clarsimp simp: L1corres_def L1_defs)
  apply (force elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind)
  done

lemma L1corres'_DynCom: 
  assumes corres_f: "\<And>s. P s \<Longrightarrow> L1corres' ct \<Gamma> P (g s) (f s)" 
  shows "L1corres' ct \<Gamma> P (gets g \<bind> (\<lambda>b. b)) (DynCom f)"
  using corres_f
  apply (clarsimp simp: L1corres'_def L1_defs)
  apply (force elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind)
  done

lemma L1corres'_DynCom_fix_state: 
  assumes corres_f: "\<And>s. P s \<Longrightarrow> L1corres' ct \<Gamma> (\<lambda>s'. P s' \<and> s' = s)  (g s) (f s)" 
  shows "L1corres' ct \<Gamma> P (gets g \<bind> (\<lambda>b. b)) (DynCom f)"
  using corres_f
  apply (clarsimp simp: L1corres'_def L1_defs)
  apply (force elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind)
  done

lemma L1corres'_guard':
  "\<lbrakk> L1corres' ct \<Gamma> (\<lambda>s. P s \<and> s \<in> g) B B' \<rbrakk> \<Longrightarrow>
      L1corres' ct \<Gamma> P (L1_seq (L1_guard (\<lambda>s. s \<in> g)) B) (Guard f g B')"
  apply (clarsimp simp: L1corres'_def L1_defs)
  apply (erule_tac x=s in allE)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
  subgoal
    by (auto simp: succeeds_bind reaches_bind split: xstate.splits)
  subgoal
    by (auto simp: succeeds_bind reaches_bind split: xstate.splits)
  subgoal
    by (auto simp: succeeds_bind intro: terminates.intros)
  done

lemma L1corres'_guarded:
  "\<lbrakk> L1corres' ct \<Gamma> (\<lambda>s. P s \<and> s \<in> g) B B' \<rbrakk> \<Longrightarrow>
      L1corres' ct \<Gamma> P (L1_guarded (\<lambda>s. s \<in> g) B) (Guard f g B')"
  unfolding L1_guarded_def by (rule L1corres'_guard')


lemma L1corres'_Guard_maybe_guard: 
"L1corres' ct \<Gamma> P B (Guard f g B') \<Longrightarrow> L1corres' ct \<Gamma> P B (maybe_guard f g B')"
  apply (simp add: L1corres'_def maybe_guard_def)
  by (meson exec.Guard iso_tuple_UNIV_I terminates_Normal_elim_cases(2))

lemma L1corres'_guarded_DynCom_conseq:
  assumes conseq: "\<And>s. P s \<Longrightarrow> g s \<Longrightarrow> s \<in> g'"
  assumes corres_B: "\<And>s. P s \<Longrightarrow> g s \<Longrightarrow> L1corres' ct \<Gamma> (\<lambda>s. P s \<and> g s) (B s) (B' s)"
  shows "L1corres' ct \<Gamma> P (L1_guarded g (gets B \<bind> (\<lambda>b. b))) (maybe_guard f g' (DynCom B'))"
  apply (rule L1corres'_Guard_maybe_guard)
  unfolding L1_guarded_def L1_set_to_pred_def
  using corres_B
  by (simp add: L1corres'_guard_DynCom_conseq [OF conseq])

lemma L1corres'_guarded_DynCom:
  assumes corres_B: "\<And>s. P s \<Longrightarrow> s \<in> g \<Longrightarrow> L1corres' ct \<Gamma> (\<lambda>s. P s \<and> s \<in> g) (B s) (B' s)"
  shows "L1corres' ct \<Gamma> P (L1_guarded (L1_set_to_pred g) (gets B \<bind> (\<lambda>b. b))) (maybe_guard f g (DynCom B'))"
  apply (rule L1corres'_guarded_DynCom_conseq [where B=B])
   apply simp
  using corres_B
  apply simp
  done

lemma L1corres'_conseq: 
  assumes corres_Q: "L1corres' ct \<Gamma> Q B B'"
  assumes conseq: "\<And>s. P s \<Longrightarrow> Q s"
  shows "L1corres' ct \<Gamma> P B B'"
  using conseq corres_Q
  by (auto simp add: L1corres'_def)

lemma L1corres_to_L1corres': "L1corres ct \<Gamma> = L1corres' ct \<Gamma> \<top>"
  by (simp add: L1corres_def L1corres'_def)


lemma L1corres_guarded_DynCom_conseq:
  assumes conseq: "\<And>s. g s \<Longrightarrow> s \<in> g'"
  assumes corres_B: "\<And>s. g s \<Longrightarrow> L1corres ct \<Gamma> (B s) (B' s)"
  shows "L1corres ct \<Gamma> (L1_guarded g (gets B \<bind> (\<lambda>b. b))) (maybe_guard f g' (DynCom B'))"
  using corres_B unfolding L1corres_to_L1corres'
  thm L1corres'_guarded_DynCom
  apply - 
  apply (rule L1corres'_guarded_DynCom_conseq [where B=B ])
  using conseq apply simp
  apply (rule L1corres'_conseq [where Q =  "\<top>"])
   apply (simp)
  apply simp
  done

lemma L1corres_guarded_DynCom:
  assumes corres_B: "\<And>s. s \<in> g \<Longrightarrow> L1corres ct \<Gamma> (B s) (B' s)"
  shows "L1corres ct \<Gamma> (L1_guarded (L1_set_to_pred g) (gets B \<bind> (\<lambda>b. b))) (maybe_guard f g (DynCom B'))"
  using corres_B unfolding L1corres_to_L1corres'
  apply - 
  apply (rule L1corres'_guarded_DynCom [where B=B ])
  apply (rule L1corres'_conseq [where Q =  "\<top>"])
   apply simp
  apply simp
  done

(* Wrapper for calling un-translated functions. *)
definition
  "L1_call_simpl check_term Gamma proc
    = do {s \<leftarrow> get_state;
         assert (check_term \<longrightarrow> Gamma \<turnstile> Call proc \<down> Normal s);
         xs \<leftarrow> select {t. Gamma \<turnstile> \<langle>Call proc, Normal s\<rangle> \<Rightarrow> t};
         case xs :: (_, strictc_errortype) xstate of
             Normal s \<Rightarrow> set_state s
           | Abrupt s \<Rightarrow> do {set_state s; throw () }
           | Fault ft \<Rightarrow> fail
           | Stuck \<Rightarrow> fail
      }"


lemma L1corres_call_simpl:
  "L1corres ct \<Gamma> (L1_call_simpl ct \<Gamma> proc) (Call proc)"
  apply (clarsimp simp: L1corres_def L1_call_simpl_def)
  apply safe
  subgoal for s t
    apply (cases t)
       apply (fastforce elim!:  exec_Normal_elim_cases 
        intro: terminates.intros exec.intros
 
        simp add: succeeds_bind reaches_bind Exn_def )+
    done
  subgoal for s
    apply (auto intro!: terminates.intros simp add: succeeds_bind reaches_bind)
    done
  done

lemma L1corres_skip:
  "L1corres ct \<Gamma> L1_skip SKIP"
  unfolding L1corres_def L1_defs
  by (force elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind)

lemma L1corres_throw:
  "L1corres ct \<Gamma> L1_throw Throw"
  unfolding L1corres_def L1_defs
  by (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def)

lemma L1corres_seq:
  "\<lbrakk> L1corres ct \<Gamma> L L'; L1corres ct \<Gamma> R R' \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma> (L1_seq L R) (L' ;; R')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_seq_def)
  apply (rule ccorresE_Seq)
  apply auto
  done

lemma L1corres_modify:
  "L1corres ct \<Gamma> (L1_modify m) (Basic m)"
  apply (clarsimp simp: L1corres_def L1_defs)
  apply (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def)
  done

lemma L1corres_condition:
  "\<lbrakk> L1corres ct \<Gamma> L L'; L1corres ct \<Gamma> R R' \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma> (L1_condition (L1_set_to_pred c) L R) (Cond c L' R')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_defs)
  apply (rule ccorresE_Cond_match)
    apply (erule ccorresE_guard_imp, simp+)[1]
   apply (erule ccorresE_guard_imp, simp+)[1]
  apply simp
  done

lemma L1corres_catch:
  "\<lbrakk> L1corres ct \<Gamma> L L'; L1corres ct \<Gamma> R R' \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma> (L1_catch L R) (Catch L' R')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_catch_def)
  apply (erule ccorresE_Catch)
  apply force
  done

lemma L1corres_while:
  "\<lbrakk> L1corres ct \<Gamma> B B' \<rbrakk> \<Longrightarrow>
      L1corres ct \<Gamma> (L1_while (L1_set_to_pred c) B) (While c B')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_defs)
  apply (rule ccorresE_While)
   apply clarsimp
  apply simp
  done

lemma L1corres_guard:
  "\<lbrakk> L1corres ct \<Gamma> B B' \<rbrakk> \<Longrightarrow>
      L1corres ct \<Gamma> (L1_seq (L1_guard (L1_set_to_pred c)) B) (Guard f c B')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: ccorresE_def L1_defs)
  apply (erule_tac x=s in allE)
  apply (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def)
  done


lemma L1corres_spec:
  "L1corres ct \<Gamma> (L1_spec x) (com.Spec x)"
  apply (clarsimp simp: L1corres_def L1_defs)
  apply (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def)
  done

lemma L1_init_alt_def:
  "L1_init upd \<equiv> L1_spec {(s, t). \<exists>v. t = upd (\<lambda>_. v) s}"
  apply (rule eq_reflection)
  apply (clarsimp simp: L1_defs)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L1corres_init:
  "L1corres ct \<Gamma> (L1_init upd) (lvar_nondet_init upd)"
  by (auto simp: L1_init_alt_def lvar_nondet_init_def intro: L1corres_spec)

lemma L1corres_guarded_spec:
  "L1corres ct \<Gamma> (L1_spec R) (guarded_spec_body F R)"
  apply (clarsimp simp: L1corres_alt_def ccorresE_def L1_spec_def guarded_spec_body_def)
  apply (force simp: liftE_def bind_def
               elim: exec_Normal_elim_cases intro: terminates.Guard terminates.Spec)
  done

lemma L1corres_assume:
  "L1corres ct \<Gamma> (L1_assume (L1_rel_to_fun R)) (guarded_spec_body AssumeError R)"
  apply (clarsimp simp: L1corres_alt_def ccorresE_def L1_assume_def L1_rel_to_fun_alt guarded_spec_body_def)
  apply (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def)
  done

lemma pred_conj_apply[simp]: "(P and Q) s \<longleftrightarrow> P s \<and> Q s"
  by (auto simp add: pred_conj_def)

lemma L1corres_call:
  "\<lbrakk> L1corres ct \<Gamma> dest_fn (Call dest) \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma>
        (L1_call scope_setup dest_fn scope_teardown_norm scope_teardown_exn f)
        (call_exn scope_setup dest scope_teardown_norm scope_teardown_exn (\<lambda>_ t. Basic (f t)))"
  apply (clarsimp simp: L1corres_alt_def)
  apply (unfold call_exn_def block_exn_def L1_call_def)
  apply (rule ccorresE_DynCom)
  apply clarsimp
  apply (rule ccorresE_get)
  apply (rule ccorresE_assume_pre, clarsimp)
  apply (rule ccorresE_guard_imp_stronger)
    apply (rule ccorresE_Seq)
     apply (rule ccorresE_Catch)
      apply (rule ccorresE_Seq)
       apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
      apply assumption
     apply (rule L1corres_seq[unfolded L1corres_alt_def])
      apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
     apply (rule L1corres_throw [unfolded L1corres_alt_def])
    apply (rule ccorresE_DynCom)
    apply (rule ccorresE_get)
    apply (rule ccorresE_assume_pre, clarsimp)
    apply (rule ccorresE_guard_imp)
      apply (rule ccorresE_Seq)
       apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
      apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
     apply simp
    apply simp
   apply simp
  apply simp
  done  

lemma (in L1_functions) L1corres_dyn_call_conseq:
  assumes conseq: "\<And>s. g s \<Longrightarrow> s \<in> g'"
  assumes corres_dest: "\<And>s. g s  \<Longrightarrow>  L1corres ct \<Gamma> (\<P> (dest s)) (Call (dest s))"
  shows
    "L1corres ct \<Gamma> 
        (L1_dyn_call g scope_setup dest scope_teardown_norm scope_teardown_exn result)
        (dynCall_exn f g' scope_setup dest scope_teardown_norm scope_teardown_exn (\<lambda>_ t. Basic (result t)))"
proof -
  have eq: "(gets (\<lambda>s. L1_call scope_setup (\<P> (dest s)) scope_teardown_norm scope_teardown_exn result) \<bind> (\<lambda>b. b)) = 
    (gets dest \<bind> (\<lambda>p. L1_call scope_setup (\<P> p) scope_teardown_norm scope_teardown_exn result))"
    apply (rule spec_monad_ext)
    apply (simp add: run_bind)
    done
  show ?thesis
    apply (simp add: L1_dyn_call_def dynCall_exn_def)
    apply (rule L1corres_guarded_DynCom_conseq [where B = "\<lambda>s. L1_call scope_setup (\<P> (dest s)) scope_teardown_norm scope_teardown_exn result", simplified eq])
     apply (simp add: conseq)
    apply (rule L1corres_call)
    apply (rule corres_dest)
    by simp
qed


lemma (in L1_functions) L1corres_dyn_call_same_guard:
  assumes eq: "L1_set_to_pred g \<equiv>  g'"
  assumes corres_dest: "\<And>s. g' s \<Longrightarrow>  L1corres ct \<Gamma> (\<P> (dest s)) (Call (dest s))"
  shows
    "L1corres ct \<Gamma> 
        (L1_dyn_call g' scope_setup dest scope_teardown_norm scope_teardown_exn result)
        (dynCall_exn f g scope_setup dest scope_teardown_norm scope_teardown_exn (\<lambda>_ t. Basic (result t)))"
  apply (rule L1corres_dyn_call_conseq)
   apply (simp add: eq [symmetric])
  by (rule corres_dest)

lemma (in L1_functions) L1corres_dyn_call_add_and_select_guard:
  assumes eq: "L1_set_to_pred g \<equiv> g'"
  assumes corres_dest: "\<And>s. G s \<Longrightarrow>  L1corres ct \<Gamma> (\<P> (dest s)) (Call (dest s))"
  shows
    "L1corres ct \<Gamma> 
        (L1_dyn_call (G and g') scope_setup dest scope_teardown_norm scope_teardown_exn result)
        (dynCall_exn f g scope_setup dest scope_teardown_norm scope_teardown_exn (\<lambda>_ t. Basic (result t)))"
  apply (rule L1corres_dyn_call_conseq)
   apply (simp add: eq [symmetric])
  apply (rule corres_dest)
  apply (simp)
  done


lemma L1_seq_guard_merge: "L1_seq (L1_guard P) (L1_seq (L1_guard Q) c) = L1_seq (L1_guard (P and Q)) c"
  unfolding L1_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma and_unfold: "(and) = (\<lambda>P Q s. P s \<and> Q s)"
  by (auto simp add: fun_eq_iff)

lemma L1_seq_guard_eq: "(\<And>s. P s = Q s) \<Longrightarrow> L1_seq (L1_guard P) c = L1_seq (L1_guard Q) c"
  unfolding L1_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma foldr_and_commute: "\<And>s. foldr (and) gs (P and g) s = (g s \<and> foldr (and) gs P s)"
  by (induct gs arbitrary: P g) (auto simp add:)


lemma L1corres_fail:
  "L1corres ct \<Gamma> L1_fail X"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_fail_def)
  apply (rule ccorresE_fail)
  done

lemma L1corres_prepend_unknown_var':
  "\<lbrakk> L1corres ct \<Gamma> A C; \<And>s::'s::type. X (\<lambda>_::'a::type. (X' s)) s = s \<rbrakk> \<Longrightarrow> L1corres ct \<Gamma> (L1_seq (L1_init X) A) C"
  unfolding L1corres_def L1_defs
  by (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def)
      metis+


lemma L1_catch_seq_join: "no_throw (\<lambda>_. True) A \<Longrightarrow> L1_seq A (L1_catch B C) = (L1_catch (L1_seq A B) C)"
  unfolding no_throw_def L1_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (clarsimp simp add: runs_to_def_old runs_to_partial_def_old Exn_def default_option_def)
  apply (intro conjI impI iffI)
     apply (metis Exn_def Exn_neq_Result)+
  done


lemma no_throw_L1_init [simp]: "no_throw P (L1_init f)"
  unfolding L1_init_def no_throw_def
  apply (clarsimp)
  apply (runs_to_vcg)
  done


lemma L1corres_prepend_unknown_var:
  "\<lbrakk> L1corres ct \<Gamma> (L1_catch A B) C; \<And>s. X (\<lambda>_::'d::type. (X' s)) s = s \<rbrakk>
         \<Longrightarrow> L1corres ct \<Gamma> (L1_catch (L1_seq (L1_init X) A) B) C"
  unfolding L1corres_def L1_defs
  by (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def succeeds_catch reaches_catch)
    metis+

lemma L1corres_Call:
  "\<lbrakk> \<Gamma> X' = Some Z'; L1corres ct \<Gamma> Z Z' \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma> Z (Call X')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (erule (1) ccorresE_Call)
  done

lemma L1_call_corres [fundef_cong]:
  "\<lbrakk> scope_setup = scope_setup';
     dest_fn = dest_fn';
     scope_teardown = scope_teardown';
     return_xf = return_xf' \<rbrakk> \<Longrightarrow>
    L1_call scope_setup dest_fn scope_teardown return_xf =
    L1_call scope_setup' dest_fn' scope_teardown' return_xf'"
  apply (clarsimp simp: L1_call_def)
  done


lemma L1_corres_cleanup: 
  "L1corres ct \<Gamma> (do {y <- state_select {(s,t). t = cleanup s};
                        return ()
                    })
     (Basic cleanup)"
  unfolding L1corres_def L1_defs
  by (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def)

lemma L1_corres_spec_cleanup: 
  "L1corres ct \<Gamma> (do { y <- state_select cleanup;
                        return ()
                    })
     (com.Spec cleanup)"
  unfolding L1corres_def L1_defs
  by (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def)
 
lemma L1_corres_cleanup_throw: 
  "L1corres ct \<Gamma> (do { _ <- state_select {(s,t). t = cleanup s};
                        throw ()
                  })
     (Basic cleanup;; THROW)"
  unfolding L1corres_def L1_defs
  by (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def default_option_def)


lemma L1_corres_spec_cleanup_throw: 
  "L1corres ct \<Gamma> (do{ _ <- state_select cleanup;
                        throw ()
                  })
     (com.Spec cleanup;; THROW)"
  unfolding L1corres_def L1_defs
  by (auto elim!:  exec_Normal_elim_cases 
      intro: terminates.intros 
      split: xstate.splits 
      simp add: succeeds_bind reaches_bind Exn_def default_option_def)

lemma on_exit_unit_def: "(on_exit f cleanup::(unit, unit, 's) exn_monad) =
  bind_handle f 
    (\<lambda>v. bind (state_select cleanup) (\<lambda>_. return ()))
    (\<lambda>e. bind (state_select cleanup)(\<lambda>_. throw ()))"
  unfolding on_exit_def on_exit'_def bind_handle_eq
  by (intro arg_cong2[where f=bind_exception_or_result])
     (auto simp: fun_eq_iff default_option_def Exn_def
           split: exception_or_result_split)

lemma on_exit_catch_conv: "on_exit f cleanup =
 do {
    r \<leftarrow> (f <catch> (\<lambda>e. state_select cleanup >>= (\<lambda>_. throw e)));
    state_select cleanup;
    return r
  }"
  unfolding on_exit_def on_exit'_def
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff fun_eq_iff Exn_def default_option_def
      intro!: arg_cong[where f="runs_to _ _"])
  by (metis default_option_def exception_or_result_cases not_None_eq)

lemma L2corres_on_exit': 
  assumes m_c: "L1corres ct \<Gamma> m c"
  shows "L1corres ct \<Gamma> (on_exit m {(s,t). t = cleanup s}) (On_Exit c (Basic cleanup))"
  unfolding on_exit_catch_conv
  apply (simp add: On_Exit_def)
  apply (rule L1corres_seq [simplified L1_seq_def])
   apply (simp add: L1_catch_def [symmetric])
   apply (rule L1corres_catch [OF m_c])
   apply (rule L1_corres_cleanup_throw [simplified])
  apply (rule L1_corres_cleanup [simplified])
  done

lemma L2corres_on_exit: 
  assumes m_c: "L1corres ct \<Gamma> m c"
  shows "L1corres ct \<Gamma> (on_exit m cleanup) (On_Exit c (com.Spec cleanup))"
  apply (simp add: on_exit_catch_conv On_Exit_def)
  apply (rule L1corres_seq [simplified L1_seq_def])
   apply (simp add: L1_catch_def [symmetric])
   apply (rule L1corres_catch [OF m_c])
   apply (rule L1_corres_spec_cleanup_throw[simplified])
  apply (rule L1_corres_spec_cleanup[simplified])
  done

definition
refines_simpl :: "bool \<Rightarrow> ('p \<Rightarrow> ('s, 'p, strictc_errortype) com option) \<Rightarrow> 
  ('s, 'p, strictc_errortype) com \<Rightarrow> 
  (('e::default, 'a, 't) spec_monad) \<Rightarrow>
   's \<Rightarrow> 't \<Rightarrow> (('s, strictc_errortype) xstate \<Rightarrow> (('e, 'a) exception_or_result * 't) \<Rightarrow> bool) \<Rightarrow> bool" where
"refines_simpl ct \<Gamma> c m s t R \<equiv>
  succeeds m t \<longrightarrow> 
   ((\<forall>s'. \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> 
      (s' \<in> {Fault AssumeError, Fault StackOverflow} \<or>
      (\<exists>r t'. reaches m t r t' \<and> R s' (r, t')))) \<and>
    (ct \<longrightarrow> \<Gamma> \<turnstile> c \<down> Normal s))"


lemma refines_simplI:
  assumes termi: "succeeds m t \<Longrightarrow> ct \<Longrightarrow> \<Gamma> \<turnstile> c \<down> Normal s"
  assumes sim: "\<And>s'. succeeds m t \<Longrightarrow> \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s' \<Longrightarrow> s' \<notin> {Fault AssumeError, Fault StackOverflow} 
    \<Longrightarrow>  \<exists>r t'. reaches m t r t' \<and> R s' (r, t')"
  shows "refines_simpl ct \<Gamma> c m s t R"
  using termi sim unfolding refines_simpl_def
  by blast

definition
rel_L1 :: "('s, strictc_errortype) xstate \<Rightarrow> ('e, 'a) xval \<times> 's \<Rightarrow> bool" where
"rel_L1 \<equiv> \<lambda>s (r, t). (case s of
              Normal s' \<Rightarrow> (\<exists>x. r = Result x) \<and> t = s'
            | Abrupt s' \<Rightarrow> (\<exists>x. r = Exn x) \<and> t = s'
            | Fault e \<Rightarrow> False
            | Stuck \<Rightarrow> False)"

lemma rel_L1_unit: 
"rel_L1 = (\<lambda>s (r, t). (case s of
              Normal s' \<Rightarrow> r = Result () \<and> t = s'
            | Abrupt s' \<Rightarrow> r = Exn () \<and> t = s'
            | Fault e \<Rightarrow> False
            | Stuck \<Rightarrow> False))"
  by (auto simp add: rel_L1_def split: xstate.splits)

lemma rel_L1_conv [simp]:
 "rel_L1 (Normal s) (r, t) = ((\<exists>x. r = Result x) \<and> t = s)"
 "rel_L1 (Abrupt s) (r, t) = ((\<exists>x. r = Exn x) \<and> t = s)"
 "rel_L1 (Fault e) x = False"
 "rel_L1 Stuck x = False"
  by (auto simp add: rel_L1_def)

lemma refines_simpl_rel_L1I:
  assumes termi: "succeeds m t \<Longrightarrow> ct \<Longrightarrow> \<Gamma> \<turnstile> c \<down> Normal s"
  assumes sim_Normal: "\<And>s'. succeeds m t \<Longrightarrow> \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal s'
    \<Longrightarrow>  \<exists>r. reaches m t (Result r) s'"
  assumes sim_Abrupt: "\<And>s'. succeeds m t \<Longrightarrow> \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Abrupt s'
    \<Longrightarrow>  \<exists>r. reaches m t (Exn r)  s'"
  assumes sim_Fault: "\<And>e. succeeds m t \<Longrightarrow> \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Fault e
    \<Longrightarrow> e \<in> {AssumeError, StackOverflow}"
  assumes sim_Stuck: "succeeds m t \<Longrightarrow> \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Stuck
    \<Longrightarrow> False"
  shows "refines_simpl ct \<Gamma> c m s t rel_L1"
  apply (rule refines_simplI [OF termi], assumption, assumption)
  apply (simp add: rel_L1_def)
  subgoal for s'
    using sim_Normal sim_Abrupt sim_Fault sim_Stuck
    apply (cases s')
       apply (fastforce split: prod.splits sum.splits)+
    done
  done

lemma L1corres_refines_simpl: 
  "L1corres ct \<Gamma> m c \<Longrightarrow> refines_simpl ct \<Gamma> c m s s rel_L1"
  apply (clarsimp simp add: L1corres_def refines_simpl_def rel_L1_def split: xstate.splits prod.splits sum.splits)
  by (smt (verit) Inl_Inr_False xstate.distinct(1) xstate.inject(1) xstate.inject(2))

lemma refines_simpl_L1corres:
  assumes "\<And>s. refines_simpl ct \<Gamma> c m s s rel_L1"
  shows "L1corres ct \<Gamma> m c"
  using assms
  apply (force simp add: L1corres_def refines_simpl_def rel_L1_def split: xstate.splits prod.splits sum.splits)
  done

theorem L1corres_refines_simpl_conv: 
  "L1corres ct \<Gamma> m c \<longleftrightarrow> (\<forall>s. refines_simpl ct \<Gamma> c m s s rel_L1)"
  using L1corres_refines_simpl refines_simpl_L1corres
  by metis

lemma refines_simpl_DynCom:
  "refines_simpl ct \<Gamma> (c s) m s t R \<Longrightarrow> refines_simpl ct \<Gamma> (DynCom c) m s t R"
  by (auto simp add: refines_simpl_def terminates.DynCom elim: exec_Normal_elim_cases(12))

lemma refines_simpl_StackOverflow:
  assumes c: "s \<in> g \<Longrightarrow> refines_simpl ct \<Gamma> c m s t R"
  shows "refines_simpl ct \<Gamma> (Guard StackOverflow g c) m s t R"
  using c 
  by (auto simp add: refines_simpl_def elim: exec_Normal_elim_cases intro: terminates.intros)



lemma refines_simpl_rel_L1_bind:
  fixes m1:: "('e, 'a, 's) exn_monad"
  fixes m2:: "'a \<Rightarrow> ('e, 'b, 's) exn_monad"
  assumes c1: "refines_simpl ct \<Gamma> c1 m1 s s rel_L1"
  assumes c2: "\<And>r s'. succeeds m1 s \<Longrightarrow> \<Gamma> \<turnstile> \<langle>c1, Normal s\<rangle> \<Rightarrow> Normal s' \<Longrightarrow> reaches m1 s (Result r) s' \<Longrightarrow> 
    refines_simpl ct \<Gamma> c2 (m2 r) s' s' rel_L1"
  shows "refines_simpl ct \<Gamma> (c1;;c2) (m1 >>= m2) s s rel_L1"
proof (rule refines_simpl_rel_L1I)
  assume nofail: "succeeds (m1 >>= m2) s"
  assume ct: "ct"
  from nofail have nofail_m1: "succeeds m1 s"
    by (simp add: succeeds_bind)
  with ct c1 have term_c1: "\<Gamma>\<turnstile>c1 \<down> Normal s"
    by (simp add: refines_simpl_def)
  then
  show "\<Gamma>\<turnstile>c1;;c2 \<down> Normal s"
  proof (rule terminates.intros, intro allI impI)
    fix s'
    assume exec_c1: "\<Gamma>\<turnstile> \<langle>c1,Normal s\<rangle> \<Rightarrow> s'" 
    show "\<Gamma>\<turnstile>c2 \<down> s'"
    proof (cases s')
      case (Normal s1)
      with exec_c1 c1 nofail_m1 term_c1 ct obtain r where sim1: "reaches m1 s (Result r) s1"
        by (force simp add: rel_L1_def refines_simpl_def)
      from c2 [OF nofail_m1 exec_c1 [simplified Normal] this]
      have "refines_simpl ct \<Gamma> c2 (m2 r) s1 s1 rel_L1" .
      with ct Normal nofail sim1
      show ?thesis
        by (simp add: refines_simpl_def reaches_bind succeeds_bind)
    qed simp_all
  qed   
next
  fix s'
  assume nofail:  "succeeds (m1 >>= m2) s" 
  from nofail have nofail_m1: "succeeds m1 s"
    by (simp add: succeeds_bind)
  assume exec: "\<Gamma>\<turnstile> \<langle>c1;;c2,Normal s\<rangle> \<Rightarrow> Normal s'"
  then show "\<exists>r. reaches (m1 >>= m2) s (Result r) s'"
  proof (cases)
    case (1 s1)
    hence exec_c1: "\<Gamma>\<turnstile> \<langle>c1,Normal s\<rangle> \<Rightarrow> s1" and
          exec_c2: "\<Gamma>\<turnstile> \<langle>c2, s1\<rangle> \<Rightarrow> Normal s'" .
    from exec_c2 obtain s1' where s1': "s1 = Normal s1'"
      by (meson Normal_resultE)
    from exec_c1 c1 nofail_m1  obtain r1 where sim1: "reaches m1 s (Result r1) s1'"
      by (metis (no_types, lifting) empty_iff insertE rel_L1_conv(1) s1' refines_simpl_def xstate.simps(7))


    from c2 [OF nofail_m1 exec_c1[simplified s1'] sim1]
    have "refines_simpl ct \<Gamma> c2 (m2 r1) s1' s1' rel_L1" . 
    with nofail exec_c2 obtain r2 where "reaches (m2 r1) s1' (Result r2) s'"
      by (smt (verit) empty_iff insertE rel_L1_conv(1) s1' sim1 refines_simpl_def succeeds_bind 
          reaches_bind xstate.simps(7))
    with sim1 nofail show ?thesis
      by (fastforce simp add: reaches_bind succeeds_bind)
  qed
next
  fix s'
  assume nofail: "succeeds (m1 >>= m2) s" 
  from nofail have nofail_m1: "succeeds m1 s"
    by (simp add: succeeds_bind)
  assume exec: "\<Gamma>\<turnstile> \<langle>c1;;c2,Normal s\<rangle> \<Rightarrow> Abrupt s'"
  then show "\<exists>r. reaches (m1 >>= m2) s (Exn r) s'"
  proof (cases)
    case (1 s1)
    hence exec_c1: "\<Gamma>\<turnstile> \<langle>c1,Normal s\<rangle> \<Rightarrow> s1" and
          exec_c2: "\<Gamma>\<turnstile> \<langle>c2,s1\<rangle> \<Rightarrow> Abrupt s'" .

    show ?thesis
    proof (cases s1)
      case (Normal s1')
      with exec_c1 c1 nofail_m1  obtain r1 where sim1: "reaches m1 s (Result r1) s1'"
        by (metis (no_types, lifting) empty_iff insertE rel_L1_conv(1)  refines_simpl_def xstate.simps(7))
      from c2 [OF nofail_m1 exec_c1[simplified Normal] sim1]
      have "refines_simpl ct \<Gamma> c2 (m2 r1) s1' s1' rel_L1" . 
      with nofail exec_c2 sim1 obtain r2 where "reaches (m2 r1) s1' (Exn r2) s'"
        by (smt (verit) Normal empty_iff insertE rel_L1_conv(2) refines_simpl_def succeeds_bind xstate.simps(11))
      with sim1 nofail show ?thesis
        by (fastforce simp add: reaches_bind succeeds_bind)
    next 
      case (Abrupt s1')
      with exec_c1 c1 nofail_m1  obtain r1 where sim1: "reaches m1 s (Exn r1) s1'"
        by (metis (no_types, lifting) empty_iff insertE rel_L1_conv(2) refines_simpl_def xstate.distinct(7))
      from Abrupt exec_c2 have "s' = s1'"
        by (meson Abrupt_end xstate.inject(2))
      with nofail
      show ?thesis 
        apply (clarsimp simp add: reaches_bind succeeds_bind Exn_def)
        using sim1 by fastforce
    next
      case (Fault x)
      with exec_c2 show ?thesis 
        by (meson Fault_end xstate.distinct(7))
    next
      case Stuck
      with exec_c2 show ?thesis
        using noStuck_startD' by blast
    qed
  qed
next
  fix e   
  assume nofail:  "succeeds (m1 >>= m2) s" 
  from nofail have nofail_m1: "succeeds m1 s"
    by (simp add: succeeds_bind) 
  assume exec: "\<Gamma>\<turnstile> \<langle>c1;;c2,Normal s\<rangle> \<Rightarrow> Fault e"
  then show "e \<in> {AssumeError, StackOverflow}"
  proof (cases)
    case (1 s1)
    hence exec_c1: "\<Gamma>\<turnstile> \<langle>c1,Normal s\<rangle> \<Rightarrow> s1" and
          exec_c2: "\<Gamma>\<turnstile> \<langle>c2,s1\<rangle> \<Rightarrow> Fault e" .
   show ?thesis
    proof (cases s1)
      case (Normal s1')
      with exec_c1 c1 nofail_m1  obtain r1 where sim1: "reaches m1 s (Result r1) s1'"
        by (metis (no_types, lifting) empty_iff insertE rel_L1_conv(1)  refines_simpl_def xstate.simps(7))
      from c2 [OF nofail_m1 exec_c1[simplified Normal] sim1]
      have "refines_simpl ct \<Gamma> c2 (m2 r1) s1' s1' rel_L1" . 

      with nofail exec_c2 sim1 show "e \<in> {AssumeError, StackOverflow}"
        by (metis (no_types, lifting) Normal insert_iff rel_L1_conv(3) refines_simpl_def singleton_iff 
            succeeds_bind xstate.inject(3))
    next
      case (Abrupt s1')
      with exec_c2 show ?thesis
        by (metis Abrupt_end xstate.distinct(7))
    next
      case (Fault x)
      with exec_c2 c1 exec_c1 show ?thesis
        by (metis exec_Normal_elim_cases(1) insert_iff nofail_m1 rel_L1_conv(3) refines_simpl_def singleton_iff xstate.inject(3))
    next
      case Stuck
      with exec_c2 show ?thesis
        using noStuck_startD' by blast
    qed
  qed
next
  assume nofail:  "succeeds (m1 >>= m2) s" 
  from nofail have nofail_m1: "succeeds m1 s"
    by (simp add: succeeds_bind) 
  assume exec: "\<Gamma>\<turnstile> \<langle>c1;;c2,Normal s\<rangle> \<Rightarrow> Stuck"
  then show False
  proof (cases)
    case (1 s1)
    hence exec_c1: "\<Gamma>\<turnstile> \<langle>c1,Normal s\<rangle> \<Rightarrow> s1" and
          exec_c2: "\<Gamma>\<turnstile> \<langle>c2,s1\<rangle> \<Rightarrow> Stuck" .
    show ?thesis 
    proof (cases s1)
      case (Normal s1')
      with exec_c1 c1 nofail_m1  obtain r1 where sim1: "reaches m1 s (Result r1) s1'"
        by (metis (no_types, lifting) empty_iff insertE rel_L1_conv(1)  refines_simpl_def xstate.simps(7))
      from c2 [OF nofail_m1 exec_c1[simplified Normal] sim1]
      have "refines_simpl ct \<Gamma> c2 (m2 r1) s1' s1' rel_L1" . 
      with nofail exec_c2 sim1 show False
        by (metis Normal insertE rel_L1_conv(4) refines_simpl_def singletonD succeeds_bind xstate.simps(15))
    next
      case (Abrupt s1')
      with exec_c2 show ?thesis
        by (metis Abrupt_end xstate.distinct(10))
    next
      case (Fault x)
      with exec_c2 show ?thesis 
        by (metis Fault_end isFault_simps(4) not_isFault_iff)
    next
      case Stuck
      with exec_c2 c1 exec_c1  show ?thesis
        by (metis insert_iff nofail_m1 rel_L1_conv(4) refines_simpl_def singletonD xstate.simps(15))
    qed
  qed
qed


lemma refines_simpl_rel_L1_catch:
  assumes L: "refines_simpl ct \<Gamma> L' L s s rel_L1" 
  assumes R: "\<And>s. refines_simpl ct \<Gamma> R' R s s rel_L1" 
  shows "refines_simpl ct \<Gamma> (Catch L' R') (L1_catch L R) s s rel_L1"
proof (rule refines_simpl_rel_L1I)
  assume nofault: "succeeds (L1_catch L R) s" 
  assume ct: "ct" 
  show "\<Gamma>\<turnstile>TRY L' CATCH R' END \<down> Normal s"
  proof (rule terminates.intros, safe)
    show "\<Gamma>\<turnstile>L' \<down> Normal s"
      using nofault ct L 
      by (simp add: refines_simpl_def L1_catch_def rel_L1_def succeeds_catch)
  next
    fix s'
    assume " \<Gamma>\<turnstile> \<langle>L',Normal s\<rangle> \<Rightarrow> Abrupt s'" 
    then show "\<Gamma>\<turnstile>R' \<down> Normal s'"
      using nofault ct L R       
      by (fastforce simp add: refines_simpl_def L1_catch_def rel_L1_def succeeds_catch)
  qed
next
  fix s'
  assume nofault:  "succeeds (L1_catch L R) s" 
  assume exec: "\<Gamma>\<turnstile> \<langle>TRY L' CATCH R' END,Normal s\<rangle> \<Rightarrow> Normal s'"
  then show "\<exists>r. reaches (L1_catch L R) s (Result r) s'"
  proof (cases)
    case (1 s1)
    hence exec_L': "\<Gamma>\<turnstile> \<langle>L',Normal s\<rangle> \<Rightarrow> Abrupt s1" and
          exec_R': "\<Gamma>\<turnstile> \<langle>R',Normal s1\<rangle> \<Rightarrow> Normal s'".
    from nofault L R exec_L' obtain
      nofault_L: "succeeds L s" and
      nofault_R: "succeeds R s1"
      by (smt (verit, best) L1_defs(5) case_xval_simps(1) insertE refines_simpl_def 
          rel_L1_conv(2) singletonD succeeds_catch xstate.simps(11))
    from nofault_L exec_L' L obtain r1 where r1: "reaches L s (Exn r1) s1"
      by (metis (no_types, lifting) insertE rel_L1_conv(2) refines_simpl_def 
          singletonD xstate.distinct(7))
    from r1 exec_R' R obtain r2 where  "reaches R s1 (Result r2) s'"
      by (metis (no_types, lifting) insertE nofault_R rel_L1_conv(1) 
          refines_simpl_def singletonD xstate.simps(7))
    with r1 nofault show ?thesis 
      by (fastforce simp add: reaches_catch succeeds_catch L1_defs )
  next
    case 2
    have exec_L': "\<Gamma>\<turnstile> \<langle>L',Normal s\<rangle> \<Rightarrow> Normal s'" by fact
    from nofault L R exec_L' obtain
      nofault_L: "succeeds L s" 
      by (simp add: L1_defs(5) succeeds_catch)
    with L exec_L' obtain r1 where "reaches L s (Result r1) s'"
      by (metis (no_types, lifting) insertE rel_L1_conv(1) refines_simpl_def singletonD xstate.distinct(3))
    then show ?thesis using nofault
      by (fastforce simp add: L1_catch_def succeeds_catch reaches_catch)
  qed
next
  fix s'
  assume nofault: "succeeds (L1_catch L R) s"
  assume exec: "\<Gamma>\<turnstile> \<langle>TRY L' CATCH R' END,Normal s\<rangle> \<Rightarrow> Abrupt s'"
  then show "\<exists>r. reaches (L1_catch L R) s (Exn r) s'"
  proof (cases)
    case (1 s1)
    hence exec_L': "\<Gamma>\<turnstile> \<langle>L',Normal s\<rangle> \<Rightarrow> Abrupt s1" and
          exec_R': "\<Gamma>\<turnstile> \<langle>R',Normal s1\<rangle> \<Rightarrow> Abrupt s'" .
    from nofault L R exec_L' obtain
      nofault_L: "succeeds L s" and
      nofault_R: "succeeds R s1"
      by (fastforce simp add: L1_catch_def refines_simpl_def reaches_catch succeeds_catch)

    from nofault_L exec_L' L obtain r1 where r1: "reaches L s (Exn r1) s1"
      by (metis (no_types, lifting) insertE rel_L1_conv(2) refines_simpl_def 
          singletonD xstate.distinct(7))
    from nofault_R r1 exec_R' R obtain r2 where  "reaches R s1 (Exn r2) s'"
      by (metis (no_types, lifting) empty_iff insertE rel_L1_conv(2) refines_simpl_def xstate.distinct(7))
    with r1 nofault show ?thesis 
      by (fastforce simp add: L1_catch_def succeeds_catch reaches_catch)
  next
    case 2
    then show ?thesis by simp
  qed
next
  fix e
  assume nofault: "succeeds (L1_catch L R) s"
  assume exec: "\<Gamma>\<turnstile> \<langle>TRY L' CATCH R' END,Normal s\<rangle> \<Rightarrow> Fault e"
  then show "e \<in> {AssumeError, StackOverflow}"
  proof (cases)
    case (1 s1)
    hence exec_L': "\<Gamma>\<turnstile> \<langle>L',Normal s\<rangle> \<Rightarrow> Abrupt s1" and
          exec_R': "\<Gamma>\<turnstile> \<langle>R',Normal s1\<rangle> \<Rightarrow> Fault e" .
    from nofault L R exec_L' obtain
      nofault_L: "succeeds L s" and
      nofault_R: "succeeds R s1"
      by (fastforce simp add: L1_catch_def refines_simpl_def reaches_catch succeeds_catch)
    from nofault_L exec_L' L obtain r1 where r1: "reaches L s (Exn r1) s1"
      by (metis (no_types, lifting) insertE rel_L1_conv(2) refines_simpl_def 
          singletonD xstate.distinct(7))
    from nofault_R r1 exec_R' R show ?thesis
      by (metis insert_iff rel_L1_conv(3) refines_simpl_def singletonD xstate.inject(3))
  next
    case 2
    have exec_L': "\<Gamma>\<turnstile> \<langle>L',Normal s\<rangle> \<Rightarrow> Fault e" by fact
    from nofault L R exec_L' obtain
      nofault_L: "succeeds L s" 
      by (simp add: L1_defs(5) succeeds_catch)
    with L exec_L' show ?thesis 
      by (metis insertCI insertE rel_L1_conv(3) refines_simpl_def singleton_iff xstate.inject(3))
  qed
next
  assume nofault: "succeeds (L1_catch L R) s"  
  assume exec: "\<Gamma>\<turnstile> \<langle>TRY L' CATCH R' END,Normal s\<rangle> \<Rightarrow> Stuck"
  then show False
  proof (cases)
    case (1 s1)
    hence exec_L': "\<Gamma>\<turnstile> \<langle>L',Normal s\<rangle> \<Rightarrow> Abrupt s1" and
          exec_R': "\<Gamma>\<turnstile> \<langle>R',Normal s1\<rangle> \<Rightarrow> Stuck" .
    from nofault L R exec_L' obtain
      nofault_L: "succeeds L s" and
      nofault_R: "succeeds R s1"
      by (fastforce simp add: L1_catch_def refines_simpl_def reaches_catch succeeds_catch)

    from nofault_R exec_R' R show ?thesis
      by (metis empty_iff insertE rel_L1_conv(4) refines_simpl_def xstate.distinct(11))
  next
    case 2
    have exec_L': "\<Gamma>\<turnstile> \<langle>L',Normal s\<rangle> \<Rightarrow> Stuck" by fact
    from nofault L R exec_L' obtain
      nofault_L: "succeeds L s" 
      by (simp add: L1_defs(5) succeeds_catch)
    with L exec_L' show ?thesis 
      by (metis insertE rel_L1_conv(4) refines_simpl_def singletonD xstate.distinct(11))
  qed
qed




lemmas refines_simpl_cleanup = L1corres_refines_simpl [OF L1_corres_cleanup]
lemmas refines_simpl_cleanup_throw = L1corres_refines_simpl [OF L1_corres_cleanup_throw]
lemmas refines_simpl_spec_cleanup = L1corres_refines_simpl [OF L1_corres_spec_cleanup]
lemmas refines_simpl_spec_cleanup_throw = L1corres_refines_simpl [OF L1_corres_spec_cleanup_throw]

lemma refines_simpl_rel_L1_on_exit': 
  fixes m:: "'s L1_monad"
  assumes m_c: "refines_simpl ct \<Gamma> c m s s rel_L1"
  shows "refines_simpl ct \<Gamma> (On_Exit c (Basic cleanup)) (on_exit m {(s,t). t = cleanup s}) s s rel_L1"
  unfolding on_exit_catch_conv
  apply (simp add: On_Exit_def)
  apply (rule refines_simpl_rel_L1_bind)
   apply (simp add: L1_catch_def [symmetric])
   apply (rule refines_simpl_rel_L1_catch [OF m_c])
   apply (rule refines_simpl_cleanup_throw [simplified])
  apply (rule refines_simpl_cleanup [simplified])
  done

lemma refines_simpl_rel_L1_on_exit: 
  fixes m:: "'s L1_monad"
  assumes m_c: "refines_simpl ct \<Gamma> c m s s rel_L1"
  shows "refines_simpl ct \<Gamma> (On_Exit c (com.Spec cleanup)) (on_exit m cleanup) s s rel_L1"
  apply (simp add: on_exit_catch_conv On_Exit_def)
  apply (rule refines_simpl_rel_L1_bind)
   apply (simp add: L1_catch_def [symmetric])
   apply (rule refines_simpl_rel_L1_catch [OF m_c])
   apply (rule refines_simpl_spec_cleanup_throw [simplified])
  apply (rule refines_simpl_spec_cleanup [simplified])
  done


named_theorems L1corres_with_fresh_stack_ptr

context stack_heap_state 
begin
lemma refines_simpl_rel_L1_with_fresh_stack_ptr: 
  fixes m:: "'a::mem_type ptr \<Rightarrow> 's L1_monad"
  assumes c_m: "\<And>p s. refines_simpl ct \<Gamma> (c p) (m p) s s rel_L1"
  shows "refines_simpl ct \<Gamma> (With_Fresh_Stack_Ptr n I c) (with_fresh_stack_ptr n I m) s s rel_L1"
  apply (simp add: with_fresh_stack_ptr_def With_Fresh_Stack_Ptr_def)
  apply (rule refines_simpl_StackOverflow)
  apply (rule refines_simpl_DynCom)
  apply (rule refines_simpl_rel_L1_bind)
  subgoal
    apply (rule refines_simpl_rel_L1I)
    subgoal
      by (simp add: terminates.Spec)
    subgoal for s'
      apply (erule exec_Normal_elim_cases)
      subgoal for t   
        by (auto simp add: succeeds_assume_result_and_state)
      by auto
    subgoal for s'
      by (meson exec_Normal_elim_cases(7) xstate.distinct(9) xstate.simps(5))
    subgoal for e
      by (meson exec_Normal_elim_cases(7) xstate.distinct(11) xstate.simps(7))
    subgoal
      apply (erule exec_Normal_elim_cases)
      using Ex_list_of_length by auto blast
    done
  apply (rule refines_simpl_DynCom)
  apply (clarsimp)
  apply (simp add: stack_allocs_allocated_ptrs)
  apply (rule refines_simpl_rel_L1_on_exit[OF c_m])
  done

lemma L1corres_with_fresh_stack_ptr[L1corres_with_fresh_stack_ptr]: 
  fixes m:: "'a::mem_type ptr \<Rightarrow> 's L1_monad"
  assumes c_m: "\<And>p. L1corres ct \<Gamma> (m p) (c p)"
  shows "L1corres ct \<Gamma> (with_fresh_stack_ptr n I m) (With_Fresh_Stack_Ptr n I c)"
  apply (rule refines_simpl_L1corres)
  apply (rule refines_simpl_rel_L1_with_fresh_stack_ptr)
  apply (rule L1corres_refines_simpl)
  apply (rule c_m)
  done
end



(*
 * Implementation of functions that have no bodies.
 *
 * For example, if the user has a call to an "extern" function,
 * but no body is available to the C parser, we do not have any
 * SIMPL to translate. We instead use the following definition.
 *)

definition "UNDEFINED_FUNCTION \<equiv> False"

definition
  undefined_function_body :: "('a, int, strictc_errortype) com"
where
  "undefined_function_body \<equiv> Guard UndefinedFunction {x. UNDEFINED_FUNCTION} SKIP"



definition
  init_return_undefined_function_body::"(('a \<Rightarrow> 'a) \<Rightarrow> (('g, 'l, 'e, 'z) state_scheme \<Rightarrow> ('g, 'l, 'e, 'z) state_scheme))
      \<Rightarrow> (('g, 'l, 'e, 'z) state_scheme, int, strictc_errortype) com" 
where
  "init_return_undefined_function_body ret \<equiv> Seq (lvar_nondet_init ret) (Guard UndefinedFunction {x. UNDEFINED_FUNCTION} SKIP)"


lemma L1corres_undefined_call:
    "L1corres ct \<Gamma> ((L1_seq (L1_guard (L1_set_to_pred {x. UNDEFINED_FUNCTION})) L1_skip)) (Call X')"
  by (clarsimp simp: L1corres_def L1_defs UNDEFINED_FUNCTION_def)

lemma L1_UNDEFINED_FUNCTION_fail: "(L1_guard (L1_set_to_pred {x. UNDEFINED_FUNCTION})) = L1_fail"
  apply (clarsimp simp add: L1_defs UNDEFINED_FUNCTION_def)
  by (simp add: run_guard spec_monad_ext)

lemma L1_seq_fail: "L1_seq L1_fail X = L1_fail"
  apply (clarsimp simp add: L1_defs)
  done

lemma L1_seq_init_fail: "(L1_seq (L1_init ret) L1_fail) = L1_fail"
  apply (clarsimp simp add: L1_defs)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L1_corres_L1_fail: "L1corres ct \<Gamma> L1_fail X"
  by (simp add: L1corres_def L1_defs)

lemma L1corres_init_return_undefined_call:
    "L1corres ct \<Gamma> (L1_seq (L1_init ret) ((L1_seq (L1_guard (L1_set_to_pred {x. UNDEFINED_FUNCTION})) L1_skip))) (Call X')"
  by (simp only: L1_UNDEFINED_FUNCTION_fail L1_seq_fail L1_seq_init_fail L1_corres_L1_fail)


(* Unfolding rules to run prior to L1 translation. *)
named_theorems L1unfold
(* L1 postprocessing rules, used by ExceptionRewrite and SimplConv. *)
named_theorems L1except

lemma signed_bounds_one_to_nat: "n <s 1 \<Longrightarrow> 0 \<le>s n \<Longrightarrow> unat n = 0"
  by (metis signed.leD unat_1_0 unat_gt_0 unsigned_eq_0_iff word_msb_0 word_sle_msb_le)

lemma signed_bounds_to_nat_boundsF: "n <s numeral B \<Longrightarrow> 0 \<le>s n \<Longrightarrow> unat n < numeral B"
  by (metis linorder_not_less of_nat_numeral signed.leD unat_less_helper word_msb_0 word_sle_msb_le)

lemma word_bounds_to_nat_boundsF: "(n::'a::len word) < numeral B \<Longrightarrow> 0 \<le>s n \<Longrightarrow> unat n < numeral B"
  by (simp add: unat_less_helper)

lemma word_bounds_one_to_nat: "(n::'a::len word) < 1 \<Longrightarrow> 0 \<le>s n \<Longrightarrow> unat n = 0"
  by (simp add: unat_less_helper)

lemma monotone_L1_seq_le [partial_function_mono]:
  assumes mono_X: "monotone R (\<le>) X"
  assumes mono_Y: "monotone R (\<le>) Y"
  shows "monotone R (\<le>) 
    (\<lambda>f. (L1_seq (X f) (Y f)))"
  unfolding L1_defs
  apply (intro partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_L1_seq_ge [partial_function_mono]:
  assumes mono_X: "monotone R (\<ge>) X"
  assumes mono_Y: "monotone R (\<ge>) Y"
  shows "monotone R (\<ge>) 
    (\<lambda>f. (L1_seq (X f) (Y f)))"
  unfolding L1_defs
  apply (intro partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_L1_catch_le [partial_function_mono]:
  assumes mono_X: "monotone R (\<le>) X"
  assumes mono_Y: "monotone R (\<le>) Y"
  shows "monotone R (\<le>)
    (\<lambda>f. (L1_catch (X f) (Y f)))"
  unfolding L1_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_L1_catch_ge [partial_function_mono]:
  assumes mono_X: "monotone R (\<ge>) X"
  assumes mono_Y: "monotone R (\<ge>) Y"
  shows "monotone R (\<ge>)
    (\<lambda>f. (L1_catch (X f) (Y f)))"
  unfolding L1_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_L1_condition_le [partial_function_mono]:
  assumes mono_X: "monotone R (\<le>) X"
  assumes mono_Y: "monotone R (\<le>) Y"
  shows "monotone R (\<le>) 
    (\<lambda>f. (L1_condition C (X f) (Y f)))"
  unfolding L1_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_L1_condition_ge [partial_function_mono]:
  assumes mono_X: "monotone R (\<ge>) X"
  assumes mono_Y: "monotone R (\<ge>) Y"
  shows "monotone R (\<ge>) 
    (\<lambda>f. (L1_condition C (X f) (Y f)))"
  unfolding L1_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done


lemma monotone_L1_guarded_le [partial_function_mono]:
  assumes mono_X [partial_function_mono]: "monotone R (\<le>) X"
  shows "monotone R (\<le>) 
    (\<lambda>f. (L1_guarded C (X f)))"
  unfolding L1_guarded_def
  apply (rule partial_function_mono)+
  done

lemma monotone_L1_guarded_ge [partial_function_mono]:
  assumes mono_X [partial_function_mono]: "monotone R (\<ge>) X"
  shows "monotone R (\<ge>) 
    (\<lambda>f. (L1_guarded C (X f)))"
  unfolding L1_guarded_def
  apply (rule partial_function_mono)+
  done



lemma monotone_L1_while_le [partial_function_mono]:
  assumes mono_B: "monotone R (\<le>) (\<lambda>f. B f)"
  shows "monotone R (\<le>) (\<lambda>f. L1_while C (B f))"
  unfolding L1_defs
  apply (rule partial_function_mono)
  apply (rule mono_B)
  done

lemma monotone_L1_while_ge [partial_function_mono]:
  assumes mono_B: "monotone R (\<ge>) (\<lambda>f. B f)"
  shows "monotone R (\<ge>) (\<lambda>f. L1_while C (B f))"
  unfolding L1_defs
  apply (rule partial_function_mono)
  apply (rule mono_B)
  done


lemma monotone_L1_call_le [partial_function_mono]: 
  assumes X[partial_function_mono]:  "monotone R (\<le>) X" 
  shows "monotone R (\<le>) 
    (\<lambda>f. L1_call scope_setup (X f) scope_teardown result_exn return_xf)"
  unfolding L1_call_def
  apply (rule partial_function_mono)+
  done

lemma monotone_L1_call_ge [partial_function_mono]: 
  assumes X[partial_function_mono]:  "monotone R (\<ge>) X" 
  shows "monotone R (\<ge>) 
    (\<lambda>f. L1_call scope_setup (X f) scope_teardown result_exn return_xf)"
  unfolding L1_call_def
  apply (rule partial_function_mono)+
  done

end
