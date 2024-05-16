(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter \<open>L2 phase: local variable abstraction with lambdas\<close>

theory L2Defs
imports CorresXF L1Defs L1Peephole L1Valid
begin

type_synonym ('s, 'a, 'e) L2_monad = "('e, 'a, 's) exn_monad"

definition "L2_unknown (ns :: nat list) \<equiv> select UNIV :: ('s, 'a, 'e) L2_monad"
definition "L2_seq (A :: ('s, 'a, 'e) L2_monad) (B :: 'a \<Rightarrow> ('s, 'b, 'e) L2_monad) \<equiv> (A >>= B) :: ('s, 'b, 'e) L2_monad"
definition "L2_modify m \<equiv>modify m :: ('s, unit, 'e) L2_monad"
definition "L2_gets f (names :: nat list) \<equiv> gets f :: ('s, 'a, 'e) L2_monad"
definition "L2_condition c (A :: ('s, 'a, 'e) L2_monad) (B :: ('s, 'a, 'e) L2_monad) \<equiv> condition c A B"
definition "L2_catch (A :: ('s, 'a, 'e) L2_monad) (B :: 'e \<Rightarrow> ('s, 'a, 'ee) L2_monad) \<equiv> (A <catch> B)"
definition "L2_try (A :: ('s, 'a, 'e + 'a) L2_monad)  \<equiv> try A"
definition "L2_while c (A :: 'a \<Rightarrow> ('s, 'a, 'e) L2_monad) i (ns :: nat list) \<equiv> whileLoop c A i :: ('s, 'a, 'e) L2_monad"
definition "L2_throw x (ns :: nat list) \<equiv> throw x :: ('s, 'a, 'e) L2_monad"
definition "L2_spec r \<equiv> (state_select r >>= (\<lambda>_. select UNIV)) :: ('s, 'a, 'e) L2_monad"
definition "L2_assume r \<equiv> (assume_result_and_state r) :: ('s, 'a, 'e) L2_monad"
definition "L2_guard c \<equiv> (guard c) :: ('s, unit, 'e) L2_monad"
definition "L2_guarded P c \<equiv> L2_seq (L2_guard P) (\<lambda>_. c)" \<comment>\<open>used to guard a function-pointer call\<close>
definition "L2_fail \<equiv> fail :: ('s, 'a, 'e) L2_monad"
definition "L2_call x emb (ns :: nat list) \<equiv> map_value (map_exn emb) x :: ('s, 'a, 'e) L2_monad"

abbreviation "L2_skip \<equiv> L2_gets (\<lambda>_. ()) []"
definition "L2_VARS f (names::nat list) \<equiv> f" \<comment> \<open>Auxilliary construct to preserve names, 
  like in @{const L2_unknown}, @{const L2_gets}, ...\<close> 

definition gets_theE :: "('s \<Rightarrow> 'a option) \<Rightarrow> ('e, 'a, 's) exn_monad" where 
  "gets_theE \<equiv> \<lambda>x. gets_the x" \<comment> \<open>Lifting into exception monad\<close>

(*
 * Temporary constructions, used internally but not emitted.
 *
 * "L2_folded_gets" is like "L2_gets", but the peephole optimiser will
 * try to eliminate the call to where it is used, eliminating it where
 * possible.  It is used for automatically generated "L2_gets" calls
 * which the user really doesn't need to know about.
 *
 * The various "call" defintions are to help generate proofs for the
 * different ways of making function calls, which are hard to unify.
 *)
definition "L2_folded_gets f names \<equiv> L2_gets f names :: ('s, 'a, 'e) L2_monad"
definition "L2_voidcall x emb ns \<equiv> L2_seq (L2_call x emb ns) (\<lambda>ret. L2_skip) :: ('s, unit, 'e) L2_monad"
definition "L2_modifycall x m emb ns \<equiv> L2_seq (L2_call x emb ns) (\<lambda>ret. L2_modify (m ret)) :: ('s, unit, 'e) L2_monad"
definition "L2_returncall x f emb ns \<equiv> L2_seq (L2_call x emb ns) (\<lambda>ret. L2_folded_gets (f ret) []) :: ('s, 'a, 'e) L2_monad"


definition "L2_seq_guard P A \<equiv> L2_seq (L2_guard P) A"
definition "L2_seq_gets c n A \<equiv> L2_seq (L2_gets (\<lambda>_. c) n) A" 

definition "SANITIZE_NAMES prj ns ns' = True"

lemma sanitize_namesI: "SANITIZE_NAMES prj ns ns'"
  by (simp add: SANITIZE_NAMES_def)

definition DYN_CALL :: "prop \<Rightarrow> prop" where "PROP DYN_CALL (PROP P) \<equiv> PROP P"

lemma DYN_CALL_I: "PROP P \<Longrightarrow> PROP DYN_CALL (PROP P)"
  by (simp add: DYN_CALL_def)

lemma DYN_CALL_D: "PROP DYN_CALL (PROP P) \<Longrightarrow> PROP P"
  by (simp add: DYN_CALL_def)

lemma runs_to_partial_top[corres_top]: "\<top> \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp add: runs_to_partial_def_old)

lemma admissible_runs_to_partial[corres_admissible]: "ccpo.admissible Inf (\<ge>) (\<lambda>f . f \<bullet> s ?\<lbrace>Q\<rbrace>)"
  unfolding runs_to_partial_def_old 
  apply (rule ccpo.admissibleI)
    apply (clarsimp simp add: ccpo.admissible_def chain_def 
        succeeds_def reaches_def split: prod.splits xval_splits)
    subgoal
      apply transfer
      apply (clarsimp simp add: Inf_post_state_def top_post_state_def image_def vimage_def 
        split: if_split_asm)
      by (metis outcomes.simps(2) post_state.distinct(1))
    done

lemma reaches_gets_theE [simp]:
     "reaches (gets_theE M) s rv s' \<longleftrightarrow> (\<exists>v'. rv = Result v' \<and> s' = s \<and> M s = Some v')"
  by (auto simp add: gets_theE_def)


lemma seucceeds_gets_theE [simp]:
     "succeeds (gets_theE M) s = (\<exists>v. M s = Some v)"
  apply (auto simp add: gets_theE_def)
  done

lemma L2_folded_gets_bind:
  "L2_seq (L2_folded_gets (\<lambda>_. x) ns) f = f x"
  unfolding L2_seq_def L2_folded_gets_def L2_gets_def
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


lemma L2_call_throw_names: "L2_call x emb ns = (x <catch> (\<lambda>r. L2_throw (emb r) ns))"
  unfolding L2_call_def L2_throw_def
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (auto simp add: runs_to_def_old map_exn_def split: xval_splits)
  done


(* fixme: we can merge these *)
lemmas L2_remove_scaffolding_1 =
  L2_folded_gets_bind [THEN eq_reflection]
  L2_returncall_def
  L2_modifycall_def
  L2_voidcall_def

lemmas L2_remove_scaffolding_2 =
  L2_remove_scaffolding_1
  L2_folded_gets_def

abbreviation (input) "L2_guarded_while G C B i n \<equiv> L2_seq (L2_guard (G i))
               (\<lambda>_. L2_while C (\<lambda>i. L2_seq (B i) (\<lambda>r. L2_seq (L2_guard (G r)) (\<lambda>_. L2_gets (\<lambda>_. r) n))) i n)"

lemmas L2_defs = L2_unknown_def L2_seq_def
    L2_modify_def L2_gets_def L2_condition_def L2_catch_def L2_while_def
    L2_throw_def L2_spec_def L2_assume_def L2_guard_def L2_fail_def L2_folded_gets_def
    L2_voidcall_def L2_modifycall_def L2_returncall_def 
    L2_try_def

(* Alternate definitions. *)
lemma L2_defs':
   "L2_unknown n \<equiv> unknown"
   "L2_seq A' B' \<equiv> A' >>= B'"
   "L2_modify m \<equiv> modify m"
   "L2_gets f n \<equiv> gets f"
   "L2_condition c L R \<equiv> condition c L R"
   "L2_catch A B \<equiv> (A <catch> B)"
   "L2_try A \<equiv> try A"
   "L2_while c' B'' i n \<equiv> whileLoop c' B'' i"
   "L2_throw x n \<equiv> throw x"
   "L2_spec r \<equiv> (state_select r >>= (\<lambda>_. select UNIV))"
   "L2_assume r' \<equiv> (assume_result_and_state r')"
   "L2_guard c \<equiv> guard c"
   "L2_fail \<equiv> fail"
  by (auto simp: (*monad_defs*) L2_defs unknown_def )


definition
   L2corres :: "('s \<Rightarrow> 't) \<Rightarrow> ('s \<Rightarrow> 'r) \<Rightarrow> ('s \<Rightarrow> 'e) \<Rightarrow> ('s \<Rightarrow> bool)
       \<Rightarrow> ('e, 'r, 't) exn_monad \<Rightarrow> (unit, unit, 's) exn_monad \<Rightarrow> bool"
where
  "L2corres st ret_xf ex_xf P A C
       \<equiv> corresXF st (\<lambda>_. ret_xf) (\<lambda>_. ex_xf) P A C"

lemma admissible_nondet_ord_L2corres [corres_admissible]:
  "ccpo.admissible Inf (\<ge>) (\<lambda>A. L2corres st ret_xf ex_xf P A C)"
  unfolding L2corres_def
  apply (rule admissible_nondet_ord_corresXF)
  done

lemma L2corres_top [corres_top]: "L2corres st ret_xf ex_xf P \<top> C"
  by (auto simp add: L2corres_def corresXF_def)

(* Wrapper for calling un-translated functions. *)

definition
  "L2_call_L1 arg_xf gs ret_xf l1body
    = do {
        s \<leftarrow> get_state;
        t \<leftarrow> select {t. gs t = s \<and> arg_xf t};
        run_bind l1body t (\<lambda>r' t'. 
          (case r' of 
             Exception _ \<Rightarrow> fail 
           | Result _ \<Rightarrow> do {set_state (gs t'); return (ret_xf t')} ))
    }"


lemma L2corres_L2_call_L1:
  "L2corres gs ret_xf ex_xf arg_xf
     (L2_call_L1 arg_xf gs ret_xf f) f"
  apply (clarsimp simp: L2corres_def corresXF_refines_iff L2_call_L1_def L1_seq_def L1_guard_def
                 split: xval_splits)
  apply (simp add: refines_def_old)
  apply (intro conjI impI)
  subgoal
    by (auto simp add: succeeds_bind succeeds_run_bind succeeds_exec_concrete_iff succeeds_catch)
  subgoal
    by (auto simp add: succeeds_bind succeeds_run_bind reaches_run_bind  
        succeeds_exec_concrete_iff succeeds_catch reaches_bind default_option_def Exn_def
        rel_XF_def rel_xval.simps Exn_def default_option_def
          split: exception_or_result_splits)

       (smt (verit, ccfv_threshold) Exn_def Exn_neq_Result exception_or_result_cases 
        imageI mem_Collect_eq old.unit.exhaust option.exhaust_sel)
  done


lemma L2corres_L2_call_simpl:
  "l1_f \<equiv> simpl_f \<Longrightarrow>
   L2corres gs ret_xf ex_xf arg_xf
     (L2_call_L1 arg_xf gs ret_xf simpl_f) l1_f"
  by (simp add: L2corres_L2_call_L1)

(* shouldn't be needed
lemma empty_set_exists: "(\<forall>a. a \<noteq> {}) = False"
  apply blast
  done
*)

lemma L2corres_modify_global:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> M (st s) = st (M' s) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_modify M) (L1_modify M')"
  unfolding L2_defs L1_defs
  by (auto simp add: L2corres_def corresXF_modify_global)


lemma L2corres_modify_unknown:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> st s = st (M s) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_unknown ns) (L1_modify M)"
  apply (clarsimp simp: L2corres_def L2_defs L1_defs)
  apply (auto intro: corresXF_select_modify)
  done

lemma L2corres_spec_unknown:
  "\<lbrakk> \<And>s a. st s = st (M (a::('a \<Rightarrow> ('a::{type}))) s) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_unknown ns) (L1_init M)"
  apply (auto simp add: L2corres_def corresXF_def L1_defs L2_defs 
      reaches_bind reaches_succeeds succeeds_bind)
  done

lemma L2corres_modify_gets:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> st s = st (M s); \<And>s. P s \<Longrightarrow> ret (M s) = f (st s) \<rbrakk> \<Longrightarrow>
         L2corres st ret ex P (L2_gets (\<lambda>s. f s) n) (L1_modify M)"
  by (simp add: L2corres_def L2_defs L1_defs corresXF_modify_gets)

lemma L2corres_gets_skip:
  "L2corres st ret ex P L2_skip L1_skip"
  by (simp add: L2corres_def L2_defs L1_defs corresXF_def)

lemma L2corres_guard:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> G' s =  G (st s) \<rbrakk> \<Longrightarrow> 
  L2corres st return_xf exception_xf P (L2_guard G) (L1_guard G')"
  by (simp add: L2corres_def L2_defs L1_defs corresXF_guard)


lemma L2corres_fail:
  "L2corres st return_xf exception_xf P L2_fail X"
  by (clarsimp simp add: L2corres_def L1_defs L2_defs corresXF_def)


lemma L2corres_spec:
  "\<lbrakk> \<And>s s'. ((s, s') \<in> A') = ((st s, st s') \<in> A); surj st \<rbrakk>
    \<Longrightarrow>  L2corres st return_xf exception_xf P (L2_spec A) (L1_spec A')"
  apply (clarsimp simp: L2corres_def L2_defs L1_spec_def corresXF_def succeeds_bind reaches_bind)
  by (metis surjD)


lemma L2corres_assume:
  "\<lbrakk> \<And>s s'. (((), s') \<in> A' s) = (((), st s') \<in> A (st s)) \<rbrakk>
    \<Longrightarrow>  L2corres st return_xf exception_xf P (L2_assume A) (L1_assume A')"
  by (clarsimp simp: L2corres_def L2_defs L1_assume_def corresXF_def)

lemma L2corres_seq:
  "\<lbrakk> L2corres st return_xf exception_xf P A A';
     \<And>x. L2corres st return_xf' exception_xf (P' x) (B x) B';
     \<lbrace>R\<rbrace> A' \<lbrace>\<lambda>_ s. P' (return_xf s) s\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>;
     \<And>s. R s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
     L2corres st return_xf' exception_xf R (L2_seq A B) (L1_seq A' B')"
  apply (unfold L2corres_def L2_seq_def L1_seq_def validE_def)
  apply (rule corresXF_join)
     apply assumption
    apply assumption
   apply simp
  apply assumption
  done

lemma L2corres_guard_imp:
  "\<lbrakk> L2corres st ret_state ex_state Q M M'; pred_imp P Q \<rbrakk> \<Longrightarrow> 
  L2corres st ret_state ex_state P M M'"
  by (simp add: L2corres_def pred_imp_def corresXF_guard_imp)


lemma L2corres_guarded'': 
  assumes bdy: "\<And>s' s. g' s' \<Longrightarrow> s = st s' \<Longrightarrow> P s' \<Longrightarrow> L2corres st ret ex P (c (dest s)) (c' (dest' s'))" 
  assumes g_g': "\<And>s'. P s' \<Longrightarrow> g' s' = g (st s')"
  assumes dest: "\<And>s' s. g' s' \<Longrightarrow> s = st s' \<Longrightarrow> P s' \<Longrightarrow> dest' s' = dest (st s')"
  shows "L2corres st ret ex P (L2_guarded g (L2_seq (L2_gets dest []) c)) (L1_guarded g' (gets dest' \<bind> c'))"
  using assms
  by (auto simp add: L2corres_def L2_defs L1_defs L2_guarded_def L1_guarded_def corresXF_def
      succeeds_bind reaches_bind  split: xval_splits)

lemma L2corres_catch:
  "\<lbrakk> L2corres st V E P L L';
    \<And>x. L2corres st V E' (P' x) (R x) R';
    \<lbrace>Q\<rbrace> L' \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>_ s. P' (E s) s\<rbrace>; \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
   L2corres st V E' Q (L2_catch L R) (L1_catch L' R')"
  apply (clarsimp simp: L2corres_def L2_catch_def L1_catch_def validE_def)
  apply (rule corresXF_except)
     apply (assumption)
    apply (assumption)
   apply auto
  done

lemma L2corres_throw:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> E s = A \<rbrakk> \<Longrightarrow> L2corres st V E P (L2_throw A n) (L1_throw)"
  by (clarsimp simp: L2corres_def L2_throw_def L1_throw_def corresXF_throw)

lemma L2corres_conseq: 
  assumes corres: "L2corres st return_xf exception_xf P C C'"
  assumes conseq: "\<And>s. Q s \<Longrightarrow> P s"
  shows "L2corres st return_xf exception_xf Q C C'"
  apply (rule L2corres_guard_imp [OF corres])
  using conseq by (simp add: pred_imp_def)

lemma L2corres_cond:
  "\<lbrakk> L2corres st return_xf exception_xf P A A';
     L2corres st return_xf exception_xf P' B B';
     \<And>s. R s \<Longrightarrow> P s;
     \<And>s. R s \<Longrightarrow> P' s;
     \<And>s. R s \<Longrightarrow> c' s = c (st s) \<rbrakk> \<Longrightarrow>
     L2corres st return_xf exception_xf R (L2_condition c A B) (L1_condition c' A' B')"
  apply (unfold L2corres_def L2_condition_def L1_condition_def)
  apply (rule corresXF_cond)
    apply (auto intro:  corresXF_guard_imp)
  done

lemma L2corres_inject_return:
  "\<lbrakk> L2corres st V E P L R; \<lbrace>P'\<rbrace> R \<lbrace>\<lambda>_ s. W (V s) = V' s\<rbrace>, \<lbrace> \<lambda>_ _. True \<rbrace>; \<And>s. P' s \<Longrightarrow> P s\<rbrakk> \<Longrightarrow>
     L2corres st V' E P' (L2_seq L (\<lambda>x. L2_gets (\<lambda>_. W x) n)) R"
  apply (clarsimp simp: L2corres_def validE_def)
  apply (drule corresXF_guard_imp [where P=P'], simp)
  apply (unfold L2_seq_def L2_gets_def)
  apply (rule corresXF_guard_imp)
  apply (erule corresXF_append_gets_abs)
    apply simp
  apply simp
  done

lemma L2corres_inject_return':
  "\<lbrakk> L2corres st V E P L R;Gets = (\<lambda>x. L2_gets (\<lambda>_. W x) n);\<lbrace>P'\<rbrace> R \<lbrace>\<lambda>_ s. W (V s) = V' s\<rbrace>, \<lbrace> \<lambda>_ _. True\<rbrace>; \<And>s. P' s \<Longrightarrow> P s
  \<rbrakk> \<Longrightarrow>
  L2corres st V' E P' (L2_seq L Gets) R"
  by (auto intro:  L2corres_inject_return)

lemma L2corres_skip:
  "L2corres st return_xf exception_xf P L2_skip L1_skip"
  by (rule L2corres_gets_skip)

lemma L2corres_while:
  assumes body_corres: "\<And>x. L2corres st ret ex (P' x) (A x) B"
  and inv_holds:  "\<lbrace>\<lambda>s. P (ret s) s \<rbrace> B \<lbrace>\<lambda>_ s. P (ret s) s \<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>"
  and cond_match: "\<And>s. P (ret s) s \<Longrightarrow> c' s = c (ret s) (st s)"
  and pred_imply: "\<And>s x. P x s \<Longrightarrow>  P' x s"
  and pred_extract: "\<And>s. P x s \<Longrightarrow>  ret s = x"
  and pred_imply2: "\<And>s. Q x s \<Longrightarrow>  P x s"
  shows "L2corres st ret ex (Q x) (L2_while c A x n) (L1_while c' B)"
  apply (clarsimp simp: L2corres_def L2_while_def L1_while_def)
  apply (rule corresXF_guard_imp)
  apply (rule corresXF_while [
         where P="\<lambda>r s. P (ret s) s" and C'=c and C="\<lambda>_. c'" and A=A and B="\<lambda>_. B"
         and ret="\<lambda>r s. ret s" and ex="\<lambda>r s. ex s" and st=st and y=x and x="()" and P'="\<lambda>r s. Q x s"])
       apply (rule corresXF_guard_imp)
        apply (rule body_corres [unfolded L2corres_def])
       apply (clarsimp simp: pred_imply)
      apply (clarsimp simp: cond_match)
     apply (rule inv_holds [unfolded validE_def, rule_format])
     apply assumption
    apply (metis pred_extract pred_imply2)
   apply (metis pred_extract pred_imply2)
  apply simp
  done

 
lemma L2corres_returncall:
  "\<lbrakk>  L2corres st ret' ex' P' Z dest_fn;
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>t s. st (return_xf t (scope_teardown s t)) = st t;
     \<And>t s. st (result_exn (scope_teardown s t) t) = st t;
     \<And>s. st (scope_setup s) = st s;
     \<And>t s. st (scope_teardown s t) = st t;
     \<And>t s. P s \<Longrightarrow> ret (return_xf t (scope_teardown s t)) = F (ret' t) (st t) ;
     \<And>t s. P s \<Longrightarrow> (ex (result_exn (scope_teardown s t) t)) = emb (ex' t) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_returncall Z F emb ns) 
   (L1_call scope_setup dest_fn scope_teardown result_exn return_xf)"
  unfolding L1_call_def L1_seq_def L1_throw_def L2_returncall_def L2_call_def L2corres_def L2_defs
  apply (rule corresXF_I)
  subgoal
    apply (clarsimp simp add: corresXF_def succeeds_bind succeeds_catch reaches_catch 
        reaches_map_value reaches_bind default_option_def Exn_def split: xval_splits exception_or_result_splits)
    by (smt (z3) Exn_def Result_neq_Exn map_exn_simps(2) the_Result_simp)
  subgoal
    apply (clarsimp simp add: corresXF_def succeeds_bind succeeds_catch reaches_catch 
        reaches_map_value reaches_bind default_option_def Exn_def split: xval_splits exception_or_result_splits)
    by (metis (mono_tags, opaque_lifting) Exception_eq_Exception Exn_def Exn_neq_Result map_exn_simps(1))
  subgoal
    apply (auto simp add: corresXF_def succeeds_bind succeeds_catch reaches_catch 
        reaches_map_value reaches_bind default_option_def Exn_def split: xval_splits exception_or_result_splits)
    done
  done


lemma L2corres_dest_fn_simp: 
  assumes dest_fn: "\<And>s. P s \<Longrightarrow> dest_fn = dest_fn'"
  assumes corres: "L2corres st ret ex P X 
   (L1_call scope_setup (measure_call dest_fn') scope_teardown result_exn return_xf)"
  shows "L2corres st ret ex P X 
   (L1_call scope_setup (measure_call dest_fn) scope_teardown result_exn return_xf)"
  using corres dest_fn unfolding L2corres_def corresXF_def 
  by blast


lemma L2corres_l2_propagate_fixed_cong: 
"(\<And>s. P s = P' s) \<Longrightarrow> (\<And>s. P' s \<Longrightarrow> A = A') \<Longrightarrow> L2corres st ret ex P A C = L2corres st ret ex P' A' C"
  unfolding L2corres_def corresXF_def simp_implies_def
  by (auto split: sum.splits prod.splits) 

lemma L2corres_modifycall:
  "\<lbrakk> L2corres st ret' ex' P' Z dest_fn;
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>s r. P r \<Longrightarrow> F (ret' s) (st s) = st (return_xf s (scope_teardown r s));
     \<And>s. st (scope_setup s) = st s;
     \<And>t s. st (scope_teardown s t) = st t;
     \<And>t s. st (result_exn (scope_teardown s t) t) = st t;
     \<And>t s. P s \<Longrightarrow> ex (result_exn (scope_teardown s t) t) = emb (ex' t)\<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_modifycall Z F emb ns)
                          (L1_call scope_setup dest_fn scope_teardown result_exn return_xf)"
  apply (clarsimp simp: L1_call_def L1_seq_def L1_throw_def L2_call_def L2_defs L2corres_def)
  apply (rule corresXF_I)
  subgoal
    apply (clarsimp simp add: corresXF_def succeeds_bind succeeds_catch reaches_catch 
        reaches_map_value reaches_bind default_option_def Exn_def split: xval_splits exception_or_result_splits)
    by (smt (z3) Exn_def Result_neq_Exn map_exn_simps(2) the_Result_simp)
  subgoal
    apply (clarsimp simp add: corresXF_def succeeds_bind succeeds_catch reaches_catch 
        reaches_map_value reaches_bind default_option_def Exn_def split: xval_splits exception_or_result_splits)
    by (metis (mono_tags, opaque_lifting) Exception_eq_Exception Exn_def Exn_neq_Result map_exn_simps(1))
  subgoal
    apply (auto simp add: corresXF_def succeeds_bind succeeds_catch reaches_catch 
        reaches_map_value reaches_bind default_option_def Exn_def split: xval_splits exception_or_result_splits)
    done
  done


lemma L2corres_voidcall:
  "\<lbrakk> L2corres st ret' ex' P' Z dest_fn;
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>s r. st (return_xf s (scope_teardown r s)) = st s;
     \<And>s. st (scope_setup s) = st s;
     \<And>t s. st (scope_teardown s t) = st t;
     \<And>t s. st (result_exn (scope_teardown s t) t) = st t;
     \<And>t s. P s \<Longrightarrow> ex (result_exn (scope_teardown s t) t) = emb (ex' t)\<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_voidcall Z emb ns)
         (L1_call scope_setup dest_fn scope_teardown result_exn return_xf)"
  apply (unfold L2_voidcall_def)
  apply (rule subst[where t = "L2_skip" and s = "L2_modify (\<lambda>s. s)"])
  subgoal
    apply (simp add: L2_defs)
    apply (rule spec_monad_ext)
    apply simp
    done
  apply (fold L2_modifycall_def L2corres_def)
  apply (fastforce elim!: L2corres_modifycall)
  done


lemma L2corres_call:
  "\<lbrakk> L2corres st ret' ex' P' Z dest_fn;
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>s r. st (return_xf s (scope_teardown r s)) = st s;
     \<And>s r. ret (return_xf s (scope_teardown r s)) = ret' s;
     \<And>s. st (scope_setup s) = st s;     
     \<And>t s. st (scope_teardown s t) = st t;
     \<And>t s. st (result_exn (scope_teardown s t) t) = st t;
     \<And>t s. P s \<Longrightarrow> ex (result_exn (scope_teardown s t) t) = emb (ex' t) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_call Z emb ns)
                          (L1_call scope_setup dest_fn scope_teardown result_exn return_xf)"
  apply (clarsimp simp: L2corres_def L2_call_def L1_call_def L1_seq_def L1_throw_def L2_defs)
  apply (rule corresXF_I)
  subgoal
    apply (clarsimp simp add: corresXF_def succeeds_bind succeeds_catch reaches_catch 
        reaches_map_value reaches_bind default_option_def Exn_def split: xval_splits exception_or_result_splits)
    by (smt (z3) Exn_def Result_neq_Exn map_exn_simps(2) the_Result_simp)
  subgoal
    apply (clarsimp simp add: corresXF_def succeeds_bind succeeds_catch reaches_catch 
        reaches_map_value reaches_bind default_option_def Exn_def split: xval_splits exception_or_result_splits)
    by (metis (mono_tags, opaque_lifting) Exception_eq_Exception Exn_def Exn_neq_Result map_exn_simps(1))
  subgoal
    apply (auto simp add: corresXF_def succeeds_bind succeeds_catch reaches_catch 
        reaches_map_value reaches_bind default_option_def Exn_def split: xval_splits exception_or_result_splits)
    done
  done

lemma (in L1_functions) L2corres_dyn_call:
"L2corres st ret ex P X 
   (L1_guarded g (gets dest >>= (\<lambda>p. L1_call scope_setup (\<P> p) scope_teardown result_exn return_xf))) \<Longrightarrow> 
 L2corres st ret ex P X (L1_dyn_call g scope_setup dest scope_teardown result_exn return_xf)"
  by (simp add: L1_dyn_call_def)


lemma L2_gets_bind: "\<lbrakk> \<And>s s'. V s = V s' \<rbrakk> \<Longrightarrow> L2_seq (L2_gets V n) f = f (V undefined)"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (simp add: runs_to_iff)
  by (auto simp add: runs_to_def_old) metis+


(* TODO: remove internal var if it is not user-visible *)
lemma L2corres_folded_gets:
  "\<lbrakk> \<And>a. L2corres st ret ex (P and (\<lambda>s. a = c (st s))) (X a) Y \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_seq (L2_folded_gets c ns) X) Y"
  by (fastforce simp add: L2_defs L2corres_def corresXF_def succeeds_bind reaches_bind split: xval_splits) 
 
lemma L2_call_cong [fundef_cong, cong]:
  "f = f' \<Longrightarrow> L2_call f = L2_call f'"
  by simp

lemma L2_call_liftE [simp]:
  "L2_call (liftE x) emb ns \<equiv> liftE x"
  by (clarsimp simp add: L2_call_def)

lemma L2_call_fail [simp]: "L2_call fail emb ns = fail"
  apply (simp add: L2_call_def)
  done


lemma L2_call_L2_gets [simp]: "L2_call (L2_gets x n) emb ns = L2_gets x n"
  apply (simp add: L2_defs L2_call_def)
  done


(*
 * Rules for adjusting case_prod statements after transformations.
 *
 * c.f. fix_L2_while_loop_splits_conv
 *)
lemma L2_split_fixup_1:
  "(L2_seq A (\<lambda>x. case y of (a, b) \<Rightarrow> B a b x)) =
           (case y of (a, b) \<Rightarrow> L2_seq A (\<lambda>x. B a b x))"
       by (auto simp: split_def)
lemma L2_split_fixup_2:
  "(L2_seq (case y of (a, b) \<Rightarrow> B a b) A) =
           (case y of (a, b) \<Rightarrow> L2_seq (B a b) A)"
       by (auto simp: split_def)
lemma L2_split_fixup_3:
  "(case (x, y) of (a, b) \<Rightarrow> P a b) = P x y"
       by (auto simp: split_def)
lemma L2_split_fixup_4:
  "case_prod (\<lambda>a (b :: 'a \<times> 'b). P a ) = case_prod (\<lambda>a. case_prod (\<lambda>(x :: 'a) (y :: 'b). P a ))"
       by (auto simp: split_def)
lemma L2_split_fixup_f:
  "(f (case y of (a, b) \<Rightarrow> G a b) =
           (case y of (a, b) \<Rightarrow> f (G a b)))"
       by (auto simp: split_def)
lemma L2_split_fixup_g:
  "case_prod (\<lambda>a (b :: 'a \<times> 'b). P a b) = case_prod (\<lambda>a. case_prod (\<lambda>(x :: 'a) (y :: 'b). P a (x, y)))"
       by (auto simp: split_def)

lemma liftE_fixup: "(\<lambda>x. liftE (case x of (a, b) \<Rightarrow> f a b)) = (\<lambda>(a,b). liftE (f a b))"
  by (simp add: fun_eq_iff split: prod.splits)

lemma finally_fixup: "(\<lambda>x. finally (case x of (a, b) \<Rightarrow> f a b)) = (\<lambda>(a,b). finally (f a b))"
  by (simp add: fun_eq_iff split: prod.splits)

lemma try_fixup: "(\<lambda>x. try (case x of (a, b) \<Rightarrow> f a b)) = (\<lambda>(a,b). try (f a b))"
  by (simp add: fun_eq_iff split: prod.splits)


lemmas L2_split_fixups =
  L2_split_fixup_1
  L2_split_fixup_2
  L2_split_fixup_3
  L2_split_fixup_4
  liftE_fixup
  finally_fixup
  try_fixup

  L2_split_fixup_f [where f=L2_guard]
  L2_split_fixup_f [where f=L2_gets]
  L2_split_fixup_f [where f=L2_modify]

  L2_split_fixup_g [where P="\<lambda>a b. L2_gets (P a b) n" for P n]
  L2_split_fixup_g [where P="\<lambda>a b. L2_guard (P a b)" for P]
  L2_split_fixup_g [where P="\<lambda>a b. L2_modify (P a b)" for P]
  L2_split_fixup_g [where P="\<lambda>a b. L2_spec (P a b)" for P]
  L2_split_fixup_g [where P="\<lambda>a b. L2_assume (P a b)" for P]
  L2_split_fixup_g [where P="\<lambda>a b. L2_throw (P a b) n" for P n]

  L2_split_fixup_g [where P="\<lambda>a b. L2_seq (L a b) (R a b)" for L R]
  L2_split_fixup_g [where P="\<lambda>a b. L2_while (C a b) (B a b) (I a b) n" for C B I n]
  L2_split_fixup_g [where P="\<lambda>a b. L2_unknown n" for n]
  L2_split_fixup_g [where P="\<lambda>a b. L2_catch (L a b) (R a b)" for L R]
  L2_split_fixup_g [where P="\<lambda>a b. L2_condition (C a b) (L a b) (R a b)" for C L R]
  L2_split_fixup_g [where P="\<lambda>a b. L2_call (M a b)" for M]
  L2_split_fixup_g [where P="\<lambda>a b. liftE (M a b)" for M]
  L2_split_fixup_g [where P="\<lambda>a b. finally (M a b)" for M]
  L2_split_fixup_g [where P="\<lambda>a b. try (M a b)" for M]
lemmas L2_split_fixups_congs =
  prod.case_cong

(* Peephole simplification rules for L2 programs (including HeapLift and WordAbstract). *)
named_theorems L2opt


lemma monotone_nondet_monad_L2_seq_le [partial_function_mono]:
  assumes mono_X: "monotone R (\<le>) X"
  assumes mono_Y: "\<And>r. monotone R (\<le>) (\<lambda>f. Y f r)"
  shows "monotone R (\<le>) 
    (\<lambda>f. (L2_seq (X f) (Y f)))"
  unfolding L2_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_nondet_monad_L2_seq_ge [partial_function_mono]:
  assumes mono_X: "monotone R (\<ge>) X"
  assumes mono_Y: "\<And>r. monotone R (\<ge>) (\<lambda>f. Y f r)"
  shows "monotone R (\<ge>) 
    (\<lambda>f. (L2_seq (X f) (Y f)))"
  unfolding L2_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_nondet_monad_L2_try_le [partial_function_mono]:
  assumes mono_X: "monotone R (\<le>) X"
  shows "monotone R (\<le>) 
    (\<lambda>f. (L2_try (X f)))"
  unfolding L2_defs
  apply (rule partial_function_mono)
  apply (rule mono_X)
  done

lemma monotone_nondet_monad_L2_try_ge [partial_function_mono]:
  assumes mono_X: "monotone R (\<ge>) X"
  shows "monotone R (\<ge>) 
    (\<lambda>f. (L2_try (X f)))"
  unfolding L2_defs
  apply (rule partial_function_mono)
  apply (rule mono_X)
  done

lemma monotone_nondet_monad_L2_catch_le [partial_function_mono]:
  assumes mono_X: "monotone R (\<le>) X"
  assumes mono_Y: "\<And>r. monotone R (\<le>) (\<lambda>f. Y f r)"
  shows "monotone R (\<le>)
    (\<lambda>f. (L2_catch (X f) (Y f)))"
  unfolding L2_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_nondet_monad_L2_catch_ge [partial_function_mono]:
  assumes mono_X: "monotone R (\<ge>) X"
  assumes mono_Y: "\<And>r. monotone R (\<ge>) (\<lambda>f. Y f r)"
  shows "monotone R (\<ge>)
    (\<lambda>f. (L2_catch (X f) (Y f)))"
  unfolding L2_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_nondet_monad_L2_condition_le [partial_function_mono]:
  assumes mono_X: "monotone R (\<le>) X"
  assumes mono_Y: "monotone R (\<le>) Y"
  shows "monotone R (\<le>) 
    (\<lambda>f. (L2_condition C (X f) (Y f)))"
  unfolding L2_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_nondet_monad_L2_condition_ge [partial_function_mono]:
  assumes mono_X: "monotone R (\<ge>) X"
  assumes mono_Y: "monotone R (\<ge>) Y"
  shows "monotone R (\<ge>) 
    (\<lambda>f. (L2_condition C (X f) (Y f)))"
  unfolding L2_defs
  apply (rule partial_function_mono)
   apply (rule mono_X)
  apply (rule mono_Y)
  done

lemma monotone_nondet_monad_L2_guarded_le [partial_function_mono]:
  assumes mono_X[partial_function_mono]: "monotone R (\<le>) X"
  shows "monotone R (\<le>) 
    (\<lambda>f. L2_guarded C (X f))"
  unfolding L2_guarded_def
  apply (rule partial_function_mono)+
  done

lemma monotone_nondet_monad_L2_guarded_ge [partial_function_mono]:
  assumes mono_X[partial_function_mono]: "monotone R (\<ge>) X"
  shows "monotone R (\<ge>) 
    (\<lambda>f. L2_guarded C (X f))"
  unfolding L2_guarded_def
  apply (rule partial_function_mono)+
  done


lemma monotone_nondet_monad_L2_while_le [partial_function_mono]:
  assumes mono_B: "\<And>r. monotone R (\<le>) (\<lambda>f. B f r)"
  shows "monotone R (\<le>) (\<lambda>f. L2_while C (B f) I ns)"
  unfolding L2_defs
  apply (rule partial_function_mono)
  apply (rule mono_B)
  done

lemma monotone_nondet_monad_L2_while_ge [partial_function_mono]:
  assumes mono_B: "\<And>r. monotone R (\<ge>) (\<lambda>f. B f r)"
  shows "monotone R (\<ge>) (\<lambda>f. L2_while C (B f) I ns)"
  unfolding L2_defs
  apply (rule partial_function_mono)
  apply (rule mono_B)
  done

lemma monotone_nondet_monad_map_exn_le [partial_function_mono]: 
  assumes X[partial_function_mono]:  "monotone R (\<le>) X" 
  shows "monotone R (\<le>) (\<lambda>f. map_value (map_exn emb) (X f))"
  unfolding map_exn_def
  apply (rule partial_function_mono)+
  done

lemma monotone_nondet_monad_map_exn_ge [partial_function_mono]: 
  assumes X[partial_function_mono]:  "monotone R (\<ge>) X" 
  shows "monotone R (\<ge>) (\<lambda>f. map_value (map_exn emb) (X f))"
  unfolding map_exn_def
  apply (rule partial_function_mono)+
  done


lemma monotone_nondet_monad_L2_call_le [partial_function_mono]: 
  assumes X[partial_function_mono]:  "monotone R (\<le>) X" 
  shows "monotone R (\<le>)  
    (\<lambda>f. L2_call (X f) emb ns)"
  unfolding L2_call_def
  apply (rule partial_function_mono)+
  done

lemma monotone_nondet_monad_L2_call_ge [partial_function_mono]: 
  assumes X[partial_function_mono]:  "monotone R (\<ge>) X" 
  shows "monotone R (\<ge>)  
    (\<lambda>f. L2_call (X f) emb ns)"
  unfolding L2_call_def
  apply (rule partial_function_mono)+
  done

section \<open>Some Relators\<close>

lemma exists_sum_unit_eq: "(\<exists>l'::unit. Inl x = Inl l' \<and> Inr y = Inr l') = (x=() \<and> y=())"
  by auto

lemmas unit_convs = exists_sum_unit_eq

definition "rel_Nonlocal = (\<lambda>e v. case e of Nonlocal x \<Rightarrow> v = x | _ \<Rightarrow> False)"

lemma rel_Nonlocal_conv: "(rel_Nonlocal e v) = (e = Nonlocal v)"
  by (cases e) (auto simp add: rel_Nonlocal_def)

lemma fun_of_rel_rel_Nonlocal[fun_of_rel_intros]: "fun_of_rel rel_Nonlocal the_Nonlocal"
  by (auto simp add: fun_of_rel_def rel_Nonlocal_def split: c_exntype.splits)

lemma funp_rel_Nonlocal[funp_intros, corres_admissible]: "funp rel_Nonlocal"
  using fun_of_rel_rel_Nonlocal
  by (auto simp add: funp_def)

lemma  rel_sum_rel_Nonlocal_case_InlI: "e = Nonlocal v' \<Longrightarrow> rel_sum rel_Nonlocal (=) (case e of Nonlocal v \<Rightarrow> Inl (Nonlocal v) | _ \<Rightarrow> Inr x) (Inl v')"
  by (simp add: rel_Nonlocal_def)

lemma  rel_xval_rel_Nonlocal_case_ExnI: "e = Nonlocal v' \<Longrightarrow> rel_xval rel_Nonlocal (=) (case e of Nonlocal v \<Rightarrow> Exn (Nonlocal v) | _ \<Rightarrow> Result x) (Exn v')"
  by (simp add: rel_Nonlocal_def)

lemma  rel_sum_rel_Nonlocal_case_InrI: "is_local e \<Longrightarrow> x = v' \<Longrightarrow> rel_sum rel_Nonlocal (=) (case e of Nonlocal v \<Rightarrow> Inl (Nonlocal v) | _ \<Rightarrow> Inr x) (Inr v')"
  apply (cases e)
  apply (auto simp add: rel_Nonlocal_def)
  done

lemma  rel_xval_rel_Nonlocal_case_ResultI: "is_local e \<Longrightarrow> x = v' \<Longrightarrow> rel_xval rel_Nonlocal (=) (case e of Nonlocal v \<Rightarrow> Exn (Nonlocal v) | _ \<Rightarrow> Result x) (Result v')"
  apply (cases e)
  apply (auto simp add: rel_Nonlocal_def)
  done

lemma rel_sum_rel_Nonlocal_map_sumI: "v = (map_sum (\<lambda>x. x) f (case e of Nonlocal x \<Rightarrow> Inl x | _ \<Rightarrow> Inr x)) \<Longrightarrow> 
 rel_sum rel_Nonlocal (=) (map_sum Nonlocal f (case e of Nonlocal x \<Rightarrow> Inl x | _ \<Rightarrow> Inr x)) v"
  apply simp
  apply (cases e)
      apply (auto simp add: rel_Nonlocal_def)
  done

lemma rel_xval_rel_Nonlocal_map_xvalI: "v = (map_xval (\<lambda>x. x) f (case e of Nonlocal x \<Rightarrow> Exn x | _ \<Rightarrow> Result x)) \<Longrightarrow> 
 rel_xval rel_Nonlocal (=) (map_xval Nonlocal f (case e of Nonlocal x \<Rightarrow> Exn x | _ \<Rightarrow> Result x)) v"
  apply simp
  apply (cases e)
      apply (auto simp add: rel_Nonlocal_def)
  done



(* FIXME: remove if unused? Probably used in replacement of refines_spec *)

definition "rel_Inr v v' \<equiv> (v = Inr v')"

lemma fun_of_rel_rel_Inr[fun_of_rel_intros]:
  "fun_of_rel rel_Inr (\<lambda>x. case x of Inr v \<Rightarrow> v | Inl _ \<Rightarrow> undefined)"
  by (auto simp add: rel_Inr_def fun_of_rel_def)

lemma funp_rel_Inr[funp_intros, corres_admissible]: "funp rel_Inr"
  using fun_of_rel_rel_Inr by (auto simp add: funp_def)

lemma rel_InrI: "v = Inr v' \<Longrightarrow> rel_Inr v v'"
  by (simp add: rel_Inr_def)

lemma rel_Inr_apply: "rel_Inr x y = (x = Inr y)"
  by (simp add: rel_Inr_def )

lemma rel_Inr_trivial [simp]: "rel_Inr (Inr v) v"
  by (simp add: rel_Inr_def)

definition rel_liftE:: "('e, 'a) xval \<Rightarrow> 'a val \<Rightarrow> bool" where "rel_liftE v v' \<equiv> (v = Result (the_Res v'))"


lemma fun_of_rel_rel_liftE[fun_of_rel_intros]:
  "fun_of_rel rel_liftE (\<lambda>x. case x of Result v \<Rightarrow> Result v | Exn _ \<Rightarrow> undefined)"
  by (auto simp add: rel_liftE_def fun_of_rel_def)

lemma funp_rel_liftE[funp_intros, corres_admissible]: "funp rel_liftE"
  using fun_of_rel_rel_liftE by (auto simp add: funp_def)


lemma rel_liftEI: "v = Result (the_Res v') \<Longrightarrow> rel_liftE v v'"
  by (simp add: rel_liftE_def)

lemma rel_liftE_apply: "rel_liftE x y = (x = Result (the_Res y))"
  by (simp add: rel_liftE_def )

lemma rel_liftE_trivial [simp]: "rel_liftE (Result v) (Result v)"
  by (simp add: rel_liftE_def)

lemma rel_liftE_rel_exception_or_result_conv: "rel_liftE = rel_exception_or_result (\<lambda>None \<Rightarrow> \<lambda>_. True | Some _ \<Rightarrow> \<lambda>_. False) (=)"
  apply (rule ext)+
  apply (auto simp add: rel_liftE_def rel_exception_or_result.simps)
  done

lemma rel_liftE_Result_Result_iff[simp]: "rel_liftE (Result v) (Result v') \<longleftrightarrow> v = v'"
  by (auto simp add: rel_liftE_def)

definition "rel_liftE' v v' \<equiv> (v = Inr v')"

lemma fun_of_rel_rel_liftE'[fun_of_rel_intros]:
  "fun_of_rel rel_liftE' (\<lambda>x. case x of Inr v \<Rightarrow> v | Inl _ \<Rightarrow> undefined)"
  by (auto simp add: rel_liftE'_def fun_of_rel_def)

lemma funp_rel_liftE'[funp_intros, corres_admissible]: "funp rel_liftE'"
  using fun_of_rel_rel_liftE' by (auto simp add: funp_def)

lemma rel_liftE'I: "v = Inr v' \<Longrightarrow> rel_liftE' v v'"
  by (simp add: rel_liftE'_def)

lemma rel_liftE'_apply: "rel_liftE' x y = (x = Inr y)"
  by (simp add: rel_liftE'_def )

lemma rel_liftE'_trivial [simp]: "rel_liftE' (Inr v) v"
  by (simp add: rel_liftE'_def)

lemma rel_liftE'_Inr_iff[simp]: "rel_liftE' (Inr v) v' \<longleftrightarrow> v = v'"
  by (auto simp add: rel_liftE'_def)

lemma rel_liftE'_rel_liftE_conv: "rel_liftE' = rel_map to_xval OO rel_liftE OO rel_map the_Res"
  apply (rule ext)+
  apply (auto simp add: relcompp.simps rel_map_def rel_liftE_def rel_liftE'_def)
  done

lemma rel_liftE_rel_liftE'_conv: "rel_liftE = rel_map from_xval OO rel_liftE' OO rel_map Result"
  apply (rule ext)+
  apply (auto simp add: relcompp.simps rel_map_def rel_liftE_def rel_liftE'_def)
  done


lemma rel_liftE'_Inr: "rel_liftE' (Inr x) x"
  by (simp)


definition rel_throwE' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a + 'c \<Rightarrow> 'b \<Rightarrow> bool" where
  "rel_throwE' L a c \<longleftrightarrow> (case a of Inl a' \<Rightarrow> L a' c | Inr _ \<Rightarrow> False)"

lemma rel_throwE'_iff: "rel_throwE' L a c \<longleftrightarrow> (\<exists>l. a = Inl l \<and> L l c)"
  by (auto simp add: rel_throwE'_def split: sum.splits)

lemma rel_throwE'_Inl:
  "L x y \<Longrightarrow> rel_throwE' L (Inl x) y"
  unfolding rel_throwE'_def
  by auto

lemma rel_throwE'_Inl_iff[simp]:
  "rel_throwE' L (Inl x) y \<longleftrightarrow> L x y"
  unfolding rel_throwE'_def
  by auto

lemma not_rel_throwE'_Inr[simp]: "\<not>rel_throwE' R (Inr d) a"
  by (auto simp: rel_throwE'_def)

definition rel_throwE :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'c) xval \<Rightarrow> 'b \<Rightarrow> bool" where
  "rel_throwE L a c \<longleftrightarrow> (case a of Exn a' \<Rightarrow> L a' c | Result _ \<Rightarrow> False)"

lemma rel_throwE_iff: "rel_throwE L a c \<longleftrightarrow> (\<exists>e. a = Exn e \<and> L e c)"
  by (auto simp add: rel_throwE_def split: xval_splits)

lemma rel_throwE_Exn:
  "L x y \<Longrightarrow> rel_throwE L (Exn x) y"
  unfolding rel_throwE_def
  by auto

lemma rel_throwE_Exn_iff[simp]:
  "rel_throwE L (Exn x) y \<longleftrightarrow> L x y"
  unfolding rel_throwE_def
  by auto

lemma not_rel_throwE_Result[simp]: "\<not>rel_throwE R (Result d) a"
  by (auto simp: rel_throwE_def)


lemma case_right_eq: "(case v of Inl l \<Rightarrow> False | Inr r \<Rightarrow> P r) = (\<exists>r. P r \<and> v = Inr r)"
  by (auto split: sum.splits)
lemma case_left_eq: "(case v of Inr r \<Rightarrow> False | Inl l \<Rightarrow> P l) = (\<exists>l. P l \<and> v = Inl l)"
  by (auto split: sum.splits)

lemma rel_sum_right: "rel_sum L R (Inr r) v = (\<exists>r'. v = Inr r' \<and> R r r')"
  by (auto elim: rel_sum.cases intro: rel_sum.intros split: sum.splits)
lemma rel_sum_left: "rel_sum L R (Inl l) v = (\<exists>l'. v = Inl l' \<and> L l l')"
  by (auto elim: rel_sum.cases intro: rel_sum.intros split: sum.splits)

lemma rel_sum_eq_apply: "(rel_sum (=) (=) x y) = (x = y)"
  by (cases x) (auto elim: rel_sum.cases intro: rel_sum.intros split: sum.splits)

lemma gen_unit_eq: "x = (y::unit)"
  by simp

lemma liftE_L2_while: "L2_while c (\<lambda>r. liftE (B r)) i n = liftE (whileLoop c B i)"
  by (clarsimp simp: L2_while_def liftE_whileLoop)

lemma liftE_L2_while_VARS: "L2_while c (\<lambda>r. liftE (B r)) i n = liftE (L2_VARS (whileLoop c B i) n)"
  by (simp add: liftE_L2_while L2_VARS_def)

lemma rel_XF_True_def: "(rel_XF st ret_xf ex_xf (\<lambda>_ _. True)) =   
         (\<lambda>(v, t) (r, s). s = st t \<and> 
            (case v of Exn x \<Rightarrow> r = Exn (ex_xf x t) | Result x \<Rightarrow> r = Result (ret_xf x t)))"
  apply (rule ext)+
  apply (auto simp add: rel_XF_def rel_xval.simps split: xval_splits)
  done

lemma refines_corresXF: "(\<forall>t. P t \<longrightarrow> refines C A t (st t) (\<lambda>(v, t) (r, s). s = st t \<and> 
    (case v of Exn x \<Rightarrow> r = Exn (ex_xf x t) | Result x \<Rightarrow> r = Result (ret_xf x t))))
 \<Longrightarrow> corresXF st ret_xf ex_xf P A C"
  by (simp add: corresXF_refines_iff rel_XF_True_def)


lemma corresXF_refines: "corresXF st ret_xf ex_xf P A C \<Longrightarrow>
(\<forall>t. P t \<longrightarrow> refines C A t (st t) (\<lambda>(v, t) (r, s). s = st t \<and> 
    (case v of Exn x \<Rightarrow>  r = Exn (ex_xf x t) | Result x \<Rightarrow> r = Result (ret_xf x t))))"
  by (simp add: corresXF_refines_iff rel_XF_True_def)


theorem corresXF_refines_conv:
\<open>corresXF st ret_xf ex_xf P A C \<longleftrightarrow> 
 (\<forall>t. P t \<longrightarrow> refines C A t (st t) (\<lambda>(v, t) (r, s). s = st t \<and> 
    (case v of Exn x \<Rightarrow>  r = Exn (ex_xf x t) | Result x \<Rightarrow> r = Result (ret_xf x t))))\<close>
  using corresXF_refines refines_corresXF ..

lemma sim_nondet_to_corresXF: "(\<And>s. refines f f' s s (=)) \<Longrightarrow> 
corresXF (\<lambda>s. s) (\<lambda>r _. r) (\<lambda>r _ . r) (\<lambda>_. True) f' f"
  unfolding refines_def_old  corresXF_def
  apply (auto split: xval_splits)
  done


named_theorems rel_spec_monad_rewrite_simps

locale sim_stack_heap_state = 
  abstract: stack_heap_state htd\<^sub>a htd_upd\<^sub>a hmem\<^sub>a hmem_upd\<^sub>a \<S> +
  concrete: stack_heap_state htd\<^sub>c htd_upd\<^sub>c hmem\<^sub>c hmem_upd\<^sub>c \<S> 
  for
    htd\<^sub>a:: "'s\<^sub>a \<Rightarrow> heap_typ_desc" and
    htd_upd\<^sub>a:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's\<^sub>a \<Rightarrow> 's\<^sub>a" and
    hmem\<^sub>a:: "'s\<^sub>a \<Rightarrow> heap_mem" and
    hmem_upd\<^sub>a:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's\<^sub>a \<Rightarrow> 's\<^sub>a" and 

    htd\<^sub>c:: "'s\<^sub>c \<Rightarrow> heap_typ_desc" and
    htd_upd\<^sub>c:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's\<^sub>c \<Rightarrow> 's\<^sub>c" and
    hmem\<^sub>c:: "'s\<^sub>c \<Rightarrow> heap_mem" and
    hmem_upd\<^sub>c:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's\<^sub>c \<Rightarrow> 's\<^sub>c" and
    \<S>::"addr set"
begin

definition rel_stack_free where 
  "rel_stack_free s\<^sub>c s\<^sub>a  \<equiv> stack_free (htd\<^sub>c s\<^sub>c) \<subseteq> stack_free (htd\<^sub>a s\<^sub>a)"


lemma refines_rel_stack_free_with_fresh_stack_ptr:
  assumes s: "rel_stack_free s\<^sub>c s\<^sub>a"
  assumes init_eq: "\<And>s\<^sub>c s\<^sub>a. I\<^sub>c s\<^sub>c = I\<^sub>a s\<^sub>a"
  assumes f: "\<And>s\<^sub>c s\<^sub>a p. rel_stack_free s\<^sub>c s\<^sub>a \<Longrightarrow>  
    refines (f\<^sub>c p) (f\<^sub>a p) s\<^sub>c s\<^sub>a
       (rel_prod (rel_xval L R) rel_stack_free)"
  shows "refines 
     (concrete.with_fresh_stack_ptr n I\<^sub>c f\<^sub>c)
     (abstract.with_fresh_stack_ptr n I\<^sub>a f\<^sub>a) s\<^sub>c s\<^sub>a
        (rel_prod (rel_xval L R) rel_stack_free)"
  apply (simp add: concrete.with_fresh_stack_ptr_def abstract.with_fresh_stack_ptr_def)
  apply (rule refines_bind_bind_exn [where Q="(rel_prod (rel_xval (\<lambda>_ _. False) (=)) rel_stack_free)"])
      apply simp_all
  subgoal
    apply (clarsimp simp add: refines_def_old rel_xval.simps)
    using s init_eq
    apply (simp add: rel_stack_free_def)
    subgoal for p d vs bs
      apply (frule (1) stack_allocs_stack_free_mono)
      apply clarsimp
      subgoal for d'
        apply (rule exI[where x="hmem_upd\<^sub>a  (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs ! i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<length vs]) (htd_upd\<^sub>a (\<lambda>_. d') s\<^sub>a)"]) 
        apply clarsimp
        apply (rule conjI)
         apply (rule exI[where x="d'"])
         apply clarsimp
         apply (rule exI[where x="vs"])
         apply clarsimp
         apply blast
        using stack_free_stack_allocs
        apply blast
        done
      done
    done
  apply (rule refines_rel_prod_on_exit [where S' = rel_stack_free])
   apply (rule f)
   apply assumption
   apply (simp add: rel_stack_free_def)
   apply (metis abstract.htd_hmem_upd abstract.typing.get_upd concrete.htd_hmem_upd 
      concrete.typing.get_upd stack_free_stack_releases_mono')
  subgoal using stack_free_stack_releases_mono' by blast
  done

definition rel_stack_free_eq where 
  "rel_stack_free_eq s\<^sub>c s\<^sub>a  \<equiv> stack_free (htd\<^sub>c s\<^sub>c) = stack_free (htd\<^sub>a s\<^sub>a)"

lemma refines_rel_stack_free_eq_with_fresh_stack_ptr:
  assumes s: "rel_stack_free_eq s\<^sub>c s\<^sub>a"
  assumes init_eq: "\<And>s\<^sub>c s\<^sub>a. I\<^sub>c s\<^sub>c = I\<^sub>a s\<^sub>a"
  assumes f: "\<And>s\<^sub>c s\<^sub>a p. rel_stack_free_eq s\<^sub>c s\<^sub>a \<Longrightarrow>  
    refines (f\<^sub>c p) (f\<^sub>a p) s\<^sub>c s\<^sub>a 
      (rel_prod (rel_xval L R) rel_stack_free_eq)"
  shows "refines 
     (concrete.with_fresh_stack_ptr n I\<^sub>c f\<^sub>c)
     (abstract.with_fresh_stack_ptr n I\<^sub>a f\<^sub>a) s\<^sub>c s\<^sub>a
        (rel_prod (rel_xval L R) rel_stack_free_eq)"
  apply (simp add: concrete.with_fresh_stack_ptr_def abstract.with_fresh_stack_ptr_def)
  apply (rule refines_bind_bind_exn [where Q="(rel_prod (rel_xval (\<lambda>_ _. False) (=)) rel_stack_free_eq)"])
      apply simp_all
  subgoal
    apply (clarsimp simp add: refines_def_old rel_xval.simps)
    using s init_eq
    apply (simp add: rel_stack_free_eq_def)
    subgoal for p d vs bs
      apply (frule (1) stack_allocs_stack_free_eq)
      apply clarsimp
      subgoal for d'
        apply (rule exI[where x="hmem_upd\<^sub>a (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs ! i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<length vs]) (htd_upd\<^sub>a (\<lambda>_. d') s\<^sub>a)"]) 
        apply clarsimp
        apply (rule conjI)
         apply (rule exI[where x="d'"])
         apply clarsimp
         apply (rule exI[where x="vs"])
         apply clarsimp
         apply blast
        using stack_free_stack_allocs
        apply blast
        done
      done
    done
  apply (rule refines_rel_prod_on_exit [where S' = rel_stack_free_eq])
   apply (rule f)
    apply assumption
   apply clarsimp
  subgoal for v t t' s\<^sub>c s\<^sub>a bs
    apply (rule exI[where x=" hmem_upd\<^sub>a (heap_update_list (ptr_val v) bs) (htd_upd\<^sub>a (stack_releases n v) s\<^sub>a)"])
    apply (clarsimp simp add: rel_stack_free_eq_def)
    by (metis dual_order.eq_iff stack_free_stack_releases_mono')
  subgoal by blast
  done

 
end

locale sim_stack_heap_raw_state = 
  abstract: stack_heap_raw_state hrs\<^sub>a hrs_upd\<^sub>a \<S> +
  concrete: stack_heap_raw_state hrs\<^sub>c hrs_upd\<^sub>c \<S> 
  for
    hrs\<^sub>a:: "'s\<^sub>a \<Rightarrow> heap_raw_state" and
    hrs_upd\<^sub>a:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's\<^sub>a \<Rightarrow> 's\<^sub>a" and

    hrs\<^sub>c:: "'s\<^sub>c \<Rightarrow> heap_raw_state" and
    hrs_upd\<^sub>c:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's\<^sub>c \<Rightarrow> 's\<^sub>c" and
    \<S>::"addr set"
begin
sublocale sim_stack_heap_state  
  "\<lambda>s. hrs_htd (hrs\<^sub>a s)" "\<lambda>upd. hrs_upd\<^sub>a (hrs_htd_update upd)" 
  "\<lambda>s. hrs_mem (hrs\<^sub>a s)" "\<lambda>upd. hrs_upd\<^sub>a (hrs_mem_update upd)" 
  "\<lambda>s. hrs_htd (hrs\<^sub>c s)" "\<lambda>upd. hrs_upd\<^sub>c (hrs_htd_update upd)" 
  "\<lambda>s. hrs_mem (hrs\<^sub>c s)" "\<lambda>upd. hrs_upd\<^sub>c (hrs_mem_update upd)" 
  \<S>
  by unfold_locales
end

named_theorems L2corres_with_fresh_stack_ptr

locale L2 = sim_stack_heap_state htd\<^sub>a htd_upd\<^sub>a hmem\<^sub>a hmem_upd\<^sub>a htd\<^sub>c htd_upd\<^sub>c hmem\<^sub>c hmem_upd\<^sub>c \<S> 
  for
    htd\<^sub>a:: "'s\<^sub>a \<Rightarrow> heap_typ_desc" and
    htd_upd\<^sub>a:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's\<^sub>a \<Rightarrow> 's\<^sub>a" and
    hmem\<^sub>a:: "'s\<^sub>a \<Rightarrow> heap_mem" and
    hmem_upd\<^sub>a:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's\<^sub>a \<Rightarrow> 's\<^sub>a" and 

    htd\<^sub>c:: "'s\<^sub>c \<Rightarrow> heap_typ_desc" and
    htd_upd\<^sub>c:: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 's\<^sub>c \<Rightarrow> 's\<^sub>c" and
    hmem\<^sub>c:: "'s\<^sub>c \<Rightarrow> heap_mem" and
    hmem_upd\<^sub>c:: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 's\<^sub>c \<Rightarrow> 's\<^sub>c" and
    \<S>::"addr set" +
  fixes st:: "'s\<^sub>c \<Rightarrow> 's\<^sub>a"
  assumes htd_st: "\<And>s. htd\<^sub>a (st s) = htd\<^sub>c s"
  assumes htd_upd_st: "\<And>s f. (htd_upd\<^sub>a f (st s)) = st (htd_upd\<^sub>c f s)"
  assumes hmem_upd_st: "\<And>s f. (hmem_upd\<^sub>a f (st s)) = st (hmem_upd\<^sub>c f s)"

begin
lemma rel_stack_free_eq_st: "rel_stack_free_eq s (st s)"
  by (simp add: rel_stack_free_eq_def htd_st)
 
definition rel_L2 where 
  "rel_L2 ex_xf ret_xf \<equiv> (\<lambda> (r\<^sub>c, s\<^sub>c) (r\<^sub>a, s\<^sub>a). 
     rel_xval (\<lambda>_ a. a = ex_xf s\<^sub>c) (\<lambda>_ a. a = ret_xf s\<^sub>c) r\<^sub>c r\<^sub>a \<and> 
     (s\<^sub>a = st s\<^sub>c))"

lemma rel_L2_def': 
  "(rel_L2 ex_xf ret_xf) = (\<lambda>(v, t) (r, s).
              s = st t \<and> (case v of Exn x \<Rightarrow> r = Exn (ex_xf t) | Result x \<Rightarrow> r = Result (ret_xf t)))"
  apply  (clarsimp simp add: rel_L2_def fun_eq_iff, intro iffI)
  subgoal using rel_xval.cases by fastforce
  subgoal by(auto split: xval_splits)
  done


lemma refines_rel_L2_on_exit':
  assumes f: "refines (f\<^sub>c p) (f\<^sub>a p) s\<^sub>c (st s\<^sub>c) (rel_L2 ex_xf ret_xf)"
  assumes ex_xf_htd_indep: "\<And>f s. ex_xf (htd_upd\<^sub>c f s) = ex_xf s"
  assumes ret_xf_htd_indep: "\<And>f s. ret_xf (htd_upd\<^sub>c f s) = ret_xf s"
  shows "refines 
    (on_exit (f\<^sub>c p) {(s,t). t = htd_upd\<^sub>c (release p) s})
    (on_exit (f\<^sub>a p) {(s,t). t = htd_upd\<^sub>a (release p) s}) s\<^sub>c (st s\<^sub>c) 
    (rel_L2 ex_xf ret_xf)"
  unfolding on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result) 
  apply (rule refines_mono [OF _ f])
  apply (clarsimp) 
  subgoal for r s q t
    apply (rule refines_bind_bind_exn[where
      Q="(\<lambda>(r', s) (q', t). is_Result r' \<and> is_Result q' \<and> rel_L2 ex_xf ret_xf (r, s) (q, t))"])
    subgoal
      apply (rule refines_assert_result_and_state)
       apply (clarsimp simp add: rel_L2_def, intro conjI)
      subgoal
        using ex_xf_htd_indep ret_xf_htd_indep 
        by metis
      subgoal
        using htd_upd_st by force
      by auto
    apply (auto simp: is_Result_def)
    done
  done

lemma refines_rel_L2_on_exit:
  assumes f: "refines (f\<^sub>c p) (f\<^sub>a p) s\<^sub>c (st s\<^sub>c) (rel_L2 ex_xf ret_xf)"
  assumes ex_xf_htd_indep: "\<And>g f s. ex_xf (hmem_upd\<^sub>c g (htd_upd\<^sub>c f s)) = ex_xf s"
  assumes ret_xf_htd_indep: "\<And>g f s. ret_xf (hmem_upd\<^sub>c g (htd_upd\<^sub>c f s)) = ret_xf s"
  assumes nonempty_cleanup\<^sub>a: "cleanup\<^sub>a \<noteq> {}"
  assumes cleanup_htd: "\<And>s s'. (s, s') \<in> cleanup\<^sub>c \<Longrightarrow> \<exists>g f. s' = (hmem_upd\<^sub>c g (htd_upd\<^sub>c f s))"
  assumes stuck_sim: "\<And>s. \<nexists>s'. (s, s') \<in> cleanup\<^sub>c \<Longrightarrow> \<nexists>t'. (st s, t') \<in> cleanup\<^sub>a"
  assumes cleanup_sim: "\<And>s t. (s, t) \<in> cleanup\<^sub>c \<Longrightarrow> (st s, st t) \<in>  cleanup\<^sub>a"
  shows "refines 
    (on_exit (f\<^sub>c p) cleanup\<^sub>c)
    (on_exit (f\<^sub>a p) cleanup\<^sub>a) s\<^sub>c (st s\<^sub>c) 
    (rel_L2 ex_xf ret_xf)"
  unfolding on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result) 
  apply (rule refines_mono [OF _ f])
  apply (clarsimp) 
  subgoal for r s q t
    apply (rule refines_bind_bind_exn [where
      Q="\<lambda>(r', s) (q', t). is_Result r' \<and> is_Result q' \<and> rel_L2 ex_xf ret_xf (r, s) (q, t)"])
    subgoal
      apply (rule refines_state_select)
       apply (clarsimp simp add: rel_L2_def, intro conjI)
      subgoal
        using cleanup_htd cleanup_sim
        by blast
      subgoal
        using ex_xf_htd_indep ret_xf_htd_indep cleanup_htd
        by metis
      subgoal
        using stuck_sim by (auto simp: rel_L2_def)
      done
    apply (auto simp: is_Result_def)
    done
  done


lemma refines_rel_L2_with_fresh_stack_ptr:
  assumes init_eq: "I\<^sub>c s\<^sub>c = I\<^sub>a (st s\<^sub>c)"
  assumes ex_xf_htd_indep: "\<And>g f s. ex_xf (hmem_upd\<^sub>c g (htd_upd\<^sub>c f s)) = ex_xf s"
  assumes ret_xf_htd_indep: "\<And>g f s. ret_xf (hmem_upd\<^sub>c g (htd_upd\<^sub>c f s)) = ret_xf s"
  assumes f: "\<And>(p::'a::mem_type ptr) d vs bs. (p, d) \<in> stack_allocs n \<S> TYPE('a) (htd\<^sub>c s\<^sub>c) \<Longrightarrow> vs \<in> I\<^sub>c s\<^sub>c \<Longrightarrow> length vs = n \<Longrightarrow> 
          length bs = n * size_of TYPE('a) \<Longrightarrow>
           refines 
             (f\<^sub>c p) 
             (f\<^sub>a p)
             (hmem_upd\<^sub>c (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs ! i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<length vs]) ((htd_upd\<^sub>c (\<lambda>_. d)) s\<^sub>c))  
             (st (hmem_upd\<^sub>c (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs ! i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<length vs]) ((htd_upd\<^sub>c (\<lambda>_. d)) s\<^sub>c))) 
             (rel_L2 ex_xf ret_xf)"
  shows "refines 
     (concrete.with_fresh_stack_ptr n I\<^sub>c f\<^sub>c)
     (abstract.with_fresh_stack_ptr n I\<^sub>a f\<^sub>a) s\<^sub>c (st s\<^sub>c) 
     (rel_L2 ex_xf ret_xf)"
  apply (simp add: concrete.with_fresh_stack_ptr_def abstract.with_fresh_stack_ptr_def)
  apply (rule refines_bind_bind_exn [where Q="(\<lambda>(r\<^sub>c, t\<^sub>c) (r\<^sub>a, t\<^sub>a).
           (\<exists>d p vs bs. (p, d) \<in> stack_allocs n \<S> TYPE('a) (htd\<^sub>c s\<^sub>c) \<and> r\<^sub>c = Result p \<and> r\<^sub>a = Result p \<and> vs \<in> I\<^sub>c s\<^sub>c \<and> length vs = n \<and> 
              length bs = n * size_of TYPE('a) \<and>
              t\<^sub>c = hmem_upd\<^sub>c  (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs ! i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<length vs]) ((htd_upd\<^sub>c (\<lambda>_. d)) s\<^sub>c) \<and>
              t\<^sub>a = st t\<^sub>c))"])
      apply simp_all
  subgoal
    apply (clarsimp simp add: refines_def_old rel_xval.simps)
    by (metis (full_types) hmem_upd_st htd_st htd_upd_st init_eq )
  subgoal for p 
    apply clarsimp
    apply (rule refines_rel_L2_on_exit )    
      apply (rule f) 
             apply simp
            apply simp
           apply simp
          apply simp
         apply (rule ex_xf_htd_indep)
        apply (rule ret_xf_htd_indep)
       apply blast
    subgoal by auto
    subgoal by auto
    subgoal using htd_upd_st hmem_upd_st by auto
    done
  done
  
lemma L2corres_refines_rel_L2_conv:
\<open>L2corres st ret_xf ex_xf P A C \<longleftrightarrow> 
 (\<forall>t. P t \<longrightarrow> refines C A t (st t) (rel_L2 ex_xf ret_xf))\<close>
  by (simp add: L2corres_def corresXF_refines_conv rel_L2_def')


lemma L2corres_refines_rel_L2:
  assumes L2: "L2corres st ret_xf ex_xf P A C"
  assumes P: "P s\<^sub>c"
  shows \<open>refines C A s\<^sub>c (st s\<^sub>c) (rel_L2 ex_xf ret_xf)\<close>
  using L2 P by (simp add: L2corres_refines_rel_L2_conv)

lemma L2corres_with_fresh_stack_ptr[L2corres_with_fresh_stack_ptr]:
  assumes l2: "\<And>p. L2corres st ret_xf ex_xf P (l2 p) (l1 p)"
  assumes I: "\<And>s. R s \<Longrightarrow> I_l1 s = I_l2 (st s)"
  assumes P: "\<And>s. R s \<Longrightarrow> P s"
  assumes ex_xf_htd_indep: "\<And>g f s. ex_xf  (hmem_upd\<^sub>c g (htd_upd\<^sub>c f s)) = ex_xf s"
  assumes ret_xf_htd_indep: "\<And>g f s. ret_xf (hmem_upd\<^sub>c g (htd_upd\<^sub>c f s)) = ret_xf s"
  assumes P_indep: "\<And>f g s. P (hmem_upd\<^sub>c g (htd_upd\<^sub>c f s)) = P s"
  shows "L2corres st ret_xf ex_xf R 
           (abstract.with_fresh_stack_ptr n (I_l2) (L2_VARS l2 nm)) 
           (concrete.with_fresh_stack_ptr n I_l1 l1)"
  apply (clarsimp simp add: L2_VARS_def L2corres_refines_rel_L2_conv)
  apply (rule refines_rel_L2_with_fresh_stack_ptr)
     apply (rule I, assumption)
    apply (rule ex_xf_htd_indep)
   apply (rule ret_xf_htd_indep)
  apply (rule L2corres_refines_rel_L2)
   apply (rule l2)
  apply (simp add: P_indep P)
  done

end

hide_const (open) L2

lemma refines_rel_prod_guard_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s\<^sub>c s\<^sub>a (rel_prod R S')"
  assumes cleanup: "\<And>s\<^sub>c s\<^sub>a t\<^sub>c. S' s\<^sub>c s\<^sub>a \<Longrightarrow> grd s\<^sub>a \<Longrightarrow> (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> \<exists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a \<and> S t\<^sub>c t\<^sub>a"
  assumes emp: "\<And>s\<^sub>c s\<^sub>a. S' s\<^sub>c s\<^sub>a \<Longrightarrow> \<nexists>t\<^sub>c. (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> \<nexists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a"
  shows "refines (on_exit f\<^sub>c cleanup\<^sub>c) (guard_on_exit f\<^sub>a grd cleanup\<^sub>a) s\<^sub>c s\<^sub>a (rel_prod R S)"
  unfolding on_exit_def on_exit'_def
  apply (rule refines_bind_exception_or_result[OF refines_weaken, OF f])
  apply (simp add: bind_assoc)
  apply (rule refines_bind_guard_right)
  apply (rule refines_bind'[OF refines_state_select])
  subgoal using cleanup by auto
  subgoal using emp by auto
  done

lemma refines_bind_no_throw_strong:
  assumes "no_throw (\<lambda>_. True) f"
  assumes "no_throw (\<lambda>_. True) f'"
  assumes f: "refines f f' s s' Q"
  assumes g: "\<And>r t r' t'. reaches f s (Result r) t \<Longrightarrow> reaches f' s' (Result r') t' \<Longrightarrow>
    Q (Result r, t) (Result r', t') \<Longrightarrow> refines (g r) (g' r') t t' R"
  shows "refines (f >>= g) (f' >>= g') s  s'  R"
  apply (rule refines_bind_bind_strong' [OF f])
  subgoal using assms
    apply (clarsimp simp add: no_throw_def runs_to_partial_def_old)
    by (metis the_Exception_simp the_Exception_Result reaches_succeeds)
  subgoal using assms
    apply (clarsimp simp add: no_throw_def runs_to_partial_def_old)
    by (metis the_Exception_simp the_Exception_Result reaches_succeeds)
  subgoal using assms
    apply (clarsimp simp add: no_throw_def runs_to_partial_def_old)
    by (metis the_Exception_simp the_Exception_Result reaches_succeeds)
  subgoal using g
    by auto
  done

lemma refines_bind_no_throw:
  assumes "no_throw (\<lambda>_. True) f"
  assumes "no_throw (\<lambda>_. True) f'"
  assumes f: "refines f f' s s' Q"
  assumes g: "\<And>r t r' t'. 
    Q (Result r, t) (Result r', t') \<Longrightarrow> refines (g r) (g' r') t t' R"
  shows "refines (f >>= g) (f' >>= g') s  s'  R"
  using assms
  by (rule refines_bind_no_throw_strong)

lemma no_throw_guard[simp]: "no_throw P (guard G)"
  by (auto simp add: no_throw_def runs_to_partial_def_old)

lemma no_throw_assert_result_and_state[simp]: "no_throw P (assert_result_and_state f)"
  by (auto simp add: no_throw_def runs_to_partial_def_old)

lemma no_throw_assume_result_and_state[simp]: "no_throw P (assume_result_and_state f)"
  by (auto simp add: no_throw_def runs_to_partial_def_old)

lemma refines_guard_same: "refines (guard P) (guard P) s s (\<lambda>(r, t) (r', t'). t=s \<and> t'=s)"
  by (simp add: refines_def_old)

lemma refines_state_select_same: 
  "refines (state_select R) (state_select R) s s (\<lambda>(r, t) (r', t'). t' = t \<and> (s, t) \<in> R)"
  by (simp add: refines_def_old)

lemma refines_assert_result_and_state_same: 
  "refines (assert_result_and_state R) (assert_result_and_state R) s s 
     (\<lambda>(r, t) (r', t'). \<exists>v. (v, t) \<in> R s \<and> r = Result v \<and> r' = Result v \<and> t = t')"
  by (auto simp add: refines_def_old)

lemma refines_assume_result_and_state_same: 
  "refines (assume_result_and_state R) (assume_result_and_state R) s s 
     (\<lambda>(r, t) (r', t'). \<exists>v. (v, t) \<in> R s \<and> r = Result v \<and> r' = Result v \<and> t = t')"
  by (auto simp add: refines_def_old)

lemma refines_assume_result_and_state_same': 
  assumes "R s = R' s"
  shows "refines (assume_result_and_state R) (assume_result_and_state R') s s 
            (\<lambda>(r, t) (r', t'). \<exists>v. (v, t) \<in> R s \<and> r = Result v \<and> r' = Result v \<and> t = t')"
  using assms
  by (auto simp add: refines_def_old)

lemma refines_rel_xval_guard_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s s (rel_prod (rel_xval L R) (=))"
  shows "refines
          (guard_on_exit f\<^sub>c P cleanup)
          (guard_on_exit f\<^sub>a P cleanup) s s 
          (rel_prod (rel_xval L R) (=))"
  unfolding guard_on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result')
   apply (rule f)
  apply clarsimp
  apply (rule refines_bind_no_throw_strong [OF _ _ refines_guard_same])
     apply simp
   apply simp
  apply clarsimp
  apply (rule refines_bind_no_throw_strong [OF _ _ refines_state_select_same])
     apply simp
   apply simp
  apply clarsimp
  done

lemma refines_rel_xval_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s s (rel_prod (rel_xval L R) (=))"
  shows "refines
          (on_exit f\<^sub>c cleanup)
          (on_exit f\<^sub>a cleanup) s s 
          (rel_prod (rel_xval L R) (=))"
  unfolding on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result')
   apply (rule f)
  apply clarsimp
  apply (rule refines_bind_no_throw_strong [OF _ _ refines_state_select_same])
     apply simp
    apply simp
  apply clarsimp
  done


lemma refines_rel_xval_assume_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s s (rel_prod (rel_xval L R) (=))"
  shows "refines
          (assume_on_exit f\<^sub>c P cleanup)
          (assume_on_exit f\<^sub>a P cleanup) s s
          (rel_prod (rel_xval L R) (=))"
  unfolding assume_on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result')
   apply (rule f)

  apply (rule refines_bind_no_throw_strong [OF _ _ ])
     apply simp
    apply simp
  apply clarsimp
   apply (rule refines_assume_result_and_state_same)
  apply clarsimp
  apply (rule refines_bind_no_throw_strong [OF _ _ refines_state_select_same])
     apply simp
   apply simp
  apply clarsimp
  done

lemma refines_state_assume_pred:
  assumes P: "P t"
  assumes ref: "refines f g s t R"
  shows "refines f (do {assume_result_and_state (\<lambda>s. {(x, y). (\<lambda>() s'. s' = s \<and> P s) x y}); g }) s t R"
  using P ref 
  by (auto simp add: refines_def_old succeeds_bind reaches_bind)

lemma refines_rel_prod_assume_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s\<^sub>c s\<^sub>a (rel_prod R S')"
  assumes cleanup: "\<And>s\<^sub>c s\<^sub>a t\<^sub>c. S' s\<^sub>c s\<^sub>a \<Longrightarrow> (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> \<exists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a \<and> S t\<^sub>c t\<^sub>a"
  assumes emp: "\<And>s\<^sub>c s\<^sub>a. S' s\<^sub>c s\<^sub>a \<Longrightarrow> \<nexists>t\<^sub>c. (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> \<nexists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a"
  assumes conseq: "\<And>s\<^sub>c s\<^sub>a. S' s\<^sub>c s\<^sub>a \<Longrightarrow> P s\<^sub>a"
  shows "refines (on_exit f\<^sub>c cleanup\<^sub>c) (assume_on_exit f\<^sub>a P cleanup\<^sub>a) s\<^sub>c s\<^sub>a (rel_prod R S)"
  unfolding assume_on_exit_bind_exception_or_result_conv on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result')
   apply (rule f)
  apply (rule refines_state_assume_pred )
  subgoal using conseq by auto
  subgoal 
    apply (rule refines_bind_no_throw_strong [where Q = "rel_prod (\<lambda>_ _. True) S"])
       apply simp
      apply simp
     apply (rule refines_state_select)
    subgoal using cleanup by auto
    subgoal using emp by auto
    subgoal 
      apply (rule refines_yield)
      apply auto
      done
    done
  done

lemma refines_runs_to_partial_rel_prod_assume_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s\<^sub>c s\<^sub>a (rel_prod R S')"
  assumes runs_to: "f\<^sub>c \<bullet> s\<^sub>c ?\<lbrace>\<lambda>r t. P t\<rbrace>"
  assumes cleanup: "\<And>s\<^sub>c s\<^sub>a t\<^sub>c. S' s\<^sub>c s\<^sub>a \<Longrightarrow> (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> P s\<^sub>c \<Longrightarrow> \<exists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a \<and> S t\<^sub>c t\<^sub>a"
  assumes emp: "\<And>s\<^sub>c s\<^sub>a. S' s\<^sub>c s\<^sub>a \<Longrightarrow> P s\<^sub>c \<Longrightarrow> \<nexists>t\<^sub>c. (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> \<nexists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a"
  assumes conseq: "\<And>s\<^sub>c s\<^sub>a.  S' s\<^sub>c s\<^sub>a  \<Longrightarrow> P s\<^sub>c \<Longrightarrow> P' s\<^sub>a"
  shows "refines (on_exit f\<^sub>c cleanup\<^sub>c) (assume_on_exit f\<^sub>a P' cleanup\<^sub>a) s\<^sub>c s\<^sub>a (rel_prod R S)"
proof -
  from refines_runs_to_partial_fuse [OF f runs_to]
  have "refines f\<^sub>c f\<^sub>a s\<^sub>c s\<^sub>a (\<lambda>(r, t) (r', t'). rel_prod R S' (r, t) (r', t') \<and> P t)" .
  moreover have "(\<lambda>(r, t) (r', t'). rel_prod R S' (r, t) (r', t') \<and> P t) = rel_prod R (\<lambda>t t'. S' t t' \<and> P t)"
    by (auto simp add: rel_prod_conv)
  ultimately have "refines f\<^sub>c f\<^sub>a s\<^sub>c s\<^sub>a (rel_prod R (\<lambda>t t'. S' t t' \<and> P t))" by simp
  then show ?thesis
    apply (rule refines_rel_prod_assume_on_exit) 
    subgoal using cleanup by blast
    subgoal using emp by blast
    subgoal using conseq by auto
    done
qed

locale L2_heap_raw_state = sim_stack_heap_raw_state hrs\<^sub>a hrs_upd\<^sub>a hrs\<^sub>c hrs_upd\<^sub>c  \<S> 
  for
    hrs\<^sub>a:: "'s\<^sub>a \<Rightarrow> heap_raw_state" and
    hrs_upd\<^sub>a:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's\<^sub>a \<Rightarrow> 's\<^sub>a" and

    hrs\<^sub>c:: "'s\<^sub>c \<Rightarrow> heap_raw_state" and
    hrs_upd\<^sub>c:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's\<^sub>c \<Rightarrow> 's\<^sub>c" and
    \<S>::"addr set" +
  fixes st:: "'s\<^sub>c \<Rightarrow> 's\<^sub>a"
  assumes hrs_htd_st: "\<And>s. hrs_htd (hrs\<^sub>a (st s)) = hrs_htd (hrs\<^sub>c s)"
  assumes hrs_upd_st: "\<And>s f. (hrs_upd\<^sub>a f (st s)) = st (hrs_upd\<^sub>c f s)"

begin
sublocale L2   
  "\<lambda>s. hrs_htd (hrs\<^sub>a s)" "\<lambda>upd. hrs_upd\<^sub>a (hrs_htd_update upd)" 
  "\<lambda>s. hrs_mem (hrs\<^sub>a s)" "\<lambda>upd. hrs_upd\<^sub>a (hrs_mem_update upd)" 
  "\<lambda>s. hrs_htd (hrs\<^sub>c s)" "\<lambda>upd. hrs_upd\<^sub>c (hrs_htd_update upd)" 
  "\<lambda>s. hrs_mem (hrs\<^sub>c s)" "\<lambda>upd. hrs_upd\<^sub>c (hrs_mem_update upd)" 
  \<S>
  apply (unfold_locales)
  subgoal using hrs_htd_st by simp
  subgoal using hrs_upd_st by simp
  subgoal using hrs_upd_st by simp
  done
end

locale typ_heap_typing = pointer_lense r w + heap_typing_state heap_typing heap_typing_upd 
  for 
    r:: "'t \<Rightarrow> ('a::xmem_type) ptr \<Rightarrow> 'a" and 
    w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't" and
    heap_typing :: "'t \<Rightarrow> heap_typ_desc" and
    heap_typing_upd :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 't \<Rightarrow> 't" and
    \<S>:: "addr set" 
begin

definition stack_ptr_acquire :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a ptr \<Rightarrow> heap_typ_desc \<Rightarrow> 't \<Rightarrow> 't"
  where "stack_ptr_acquire n vs p d s = 
     (fold (\<lambda>i. w (p +\<^sub>p int i) (\<lambda>_. (vs ! i))) [0..<n]) (heap_typing_upd (\<lambda>_. d) s)"

definition stack_ptr_release :: "nat \<Rightarrow> 'a ptr \<Rightarrow> 't \<Rightarrow> 't" 
  where "stack_ptr_release n p s = 
     (heap_typing_upd (stack_releases n p) o (fold (\<lambda>i. w (p +\<^sub>p int i) (\<lambda>_. c_type_class.zero)) [0..<n])) s"

definition assume_stack_alloc:: "nat \<Rightarrow> ('t \<Rightarrow> ('a::xmem_type) list set) \<Rightarrow> ('e::default, 'a ptr, 't) spec_monad" where
 "assume_stack_alloc n init \<equiv> assume_result_and_state (\<lambda>s. {(p, t). 
         \<exists>d vs. (p, d) \<in> stack_allocs n \<S> TYPE('a::xmem_type) (heap_typing s) \<and> 
                vs \<in> init s \<and> 
                length vs = n \<and>
                (\<forall>i \<in> {0..<n}. r s (p +\<^sub>p int i) = ZERO('a::xmem_type)) \<and>
                t = stack_ptr_acquire n vs p d s})"

definition guard_with_fresh_stack_ptr :: "nat \<Rightarrow> ('t \<Rightarrow> 'a list set) \<Rightarrow> ('a::xmem_type ptr \<Rightarrow> ('e::default, 'v, 't) spec_monad) \<Rightarrow> ('e, 'v, 't) spec_monad" where
"guard_with_fresh_stack_ptr n init c \<equiv>
  do {
    p \<leftarrow> assume_stack_alloc n init;
    guard_on_exit (c p) 
       (\<lambda>s. \<forall>i < n. root_ptr_valid (heap_typing s) (p +\<^sub>p int i))
       {(s, t). t = stack_ptr_release n p s}
  }"

definition assume_with_fresh_stack_ptr :: "nat \<Rightarrow> ('t \<Rightarrow> 'a list set) \<Rightarrow> ('a::xmem_type ptr \<Rightarrow> ('e::default,'v, 't) spec_monad) \<Rightarrow> ('e, 'v, 't) spec_monad" where
"assume_with_fresh_stack_ptr n init c \<equiv>
  do {
    p \<leftarrow> assume_stack_alloc n init;
    assume_on_exit (c p) 
       (\<lambda>s. \<forall>i < n. root_ptr_valid (heap_typing s) (p +\<^sub>p int i))
       {(s, t). t = stack_ptr_release n p s}
  }"

definition with_fresh_stack_ptr :: "nat \<Rightarrow> ('t \<Rightarrow> 'a list set) \<Rightarrow> ('a::xmem_type ptr \<Rightarrow> ('e::default,'v, 't) spec_monad) \<Rightarrow> ('e, 'v, 't) spec_monad" where
"with_fresh_stack_ptr n init c \<equiv>
  do {
    p \<leftarrow> assume_stack_alloc n init;
    on_exit (c p) 
       {(s, t). t = stack_ptr_release n p s}
  }"

lemma monotone_guard_with_fresh_stack_ptr_le[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>p. monotone R (\<le>) (\<lambda>f. c f p)"  
  shows "monotone R (\<le>) (\<lambda>f. guard_with_fresh_stack_ptr n I (c f))"
  unfolding guard_with_fresh_stack_ptr_def
  by (intro partial_function_mono)

lemma monotone_guard_with_fresh_stack_ptr_ge[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>p. monotone R (\<ge>) (\<lambda>f. c f p)"  
  shows "monotone R (\<ge>) (\<lambda>f. guard_with_fresh_stack_ptr n I (c f))"
  unfolding guard_with_fresh_stack_ptr_def
  by (intro partial_function_mono)

lemma monotone_assume_with_fresh_stack_ptr_le[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>p. monotone R (\<le>) (\<lambda>f. c f p)"  
  shows "monotone R (\<le>) (\<lambda>f. assume_with_fresh_stack_ptr n I (c f))"
  unfolding assume_with_fresh_stack_ptr_def
  by (intro partial_function_mono)

lemma monotone_assume_with_fresh_stack_ptr_ge[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>p. monotone R (\<ge>) (\<lambda>f. c f p)"  
  shows "monotone R (\<ge>) (\<lambda>f. assume_with_fresh_stack_ptr n I (c f))"
  unfolding assume_with_fresh_stack_ptr_def
  by (intro partial_function_mono)

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

lemma refines_rel_xval_guard_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (f\<^sub>c p) (f\<^sub>a p) s s (rel_prod (rel_xval L R) (=))"
  shows 
    "refines 
      (guard_with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))
      (guard_with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
      (rel_prod (rel_xval L R) (=))"
  unfolding guard_with_fresh_stack_ptr_def L2_VARS_def on_exit'_def assume_stack_alloc_def
  apply (rule refines_bind')
  apply (subst refines_assume_result_and_state_iff)
  apply (subst init_eq)
  apply (rule sim_set_refl)
  apply clarsimp
  apply (rule refines_bind_exception_or_result'[OF f])
  apply (rule refines_bind')
  apply (rule refines_bind')
  apply (rule refines_guard)
  apply simp_all
  apply (rule refines_assert_result_and_state)
  apply simp_all
  done


lemma refines_rel_xval_assume_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (f\<^sub>c p) (f\<^sub>a p) s s (rel_prod (rel_xval L R) (=))"
  shows 
    "refines 
      (assume_with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))
      (assume_with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
      (rel_prod (rel_xval L R) (=))"
  unfolding assume_with_fresh_stack_ptr_def L2_VARS_def on_exit'_def assume_stack_alloc_def
  apply (rule refines_bind')
  apply (subst refines_assume_result_and_state_iff)
  apply (subst init_eq)
  apply (rule sim_set_refl)
  apply clarsimp
  apply (rule refines_bind_exception_or_result'[OF f])
  apply (rule refines_bind')
  apply (rule refines_bind')
  apply (rule refines_assuming)
  apply simp_all
  apply (rule refines_assert_result_and_state)
  apply simp_all
  done

lemma refines_rel_xval_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (f\<^sub>c p) (f\<^sub>a p) s s (rel_prod (rel_xval L R) (=))"
  shows 
    "refines 
      (with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))
      (with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
      (rel_prod (rel_xval L R) (=))"
  unfolding with_fresh_stack_ptr_def L2_VARS_def assume_stack_alloc_def
  apply (rule refines_bind_no_throw [where Q = "rel_prod (rel_xval (\<lambda>_ _. False) (=)) (=)"])
  apply simp
    apply simp
  subgoal using init_eq by (auto simp add: refines_def_old rel_xval.simps) 
  subgoal 
    apply clarsimp
    apply (rule refines_rel_xval_on_exit)
    apply (rule f)
    done
  done

(* This is not in pointer_lense, since the lemma depends on the xmem type class *)
lemma write_same_ZERO:
  "r s p = ZERO('a) \<Longrightarrow> w p (\<lambda>y. ZERO('a)) s = s"
  using write_same by simp

end

lemma refines_rel_prod_eq_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s s (rel_prod Q (=))"
  shows "refines
        (on_exit f\<^sub>c cleanup)
        (on_exit f\<^sub>a cleanup) s s
        (rel_prod Q (=))"
  unfolding on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result')
   apply (rule f)
  apply clarsimp
  apply (rule refines_bind_no_throw )
  apply simp
  apply simp
   apply (rule refines_state_select_same)
  apply clarsimp
  done

context stack_heap_state
begin
lemma refines_rel_prod_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (f\<^sub>c p) (f\<^sub>a p) s s (rel_prod Q (=))"
  shows 
    "refines 
       (with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm)) 
       (with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
       (rel_prod Q (=))"
  unfolding with_fresh_stack_ptr_def L2_VARS_def
  apply (rule refines_bind_no_throw )
     apply simp
    apply simp
   apply (rule refines_assume_result_and_state_same')
   apply (simp only: init_eq)
  apply clarsimp
  apply (rule refines_rel_prod_eq_on_exit)
  apply (rule f)
  done
end

lemma h_val_coerce_ptr_coerce_packed:
  fixes p::"'c::packed_type ptr"
  assumes sz_eq: "size_of TYPE('c) = size_of TYPE('a::packed_type)" 
  shows "h_val h (PTR_COERCE ('c \<rightarrow> 'a) p) = COERCE ('c \<rightarrow> 'a) (h_val h p)"
  by (simp add:  h_val_def sz_eq from_bytes_def coerce_def to_bytes_p_def to_bytes_def 
      packed_type_access_ti access_ti\<^sub>0_def field_access_update_same(1) 
      size_of_fold sz_eq td_fafu_idem update_ti_t_def)


lemma h_val_field_ptr_coerce_from_bytes_packed:
  fixes p::"'c::packed_type ptr"
  assumes "field_ti TYPE('a) f = Some t"
  assumes "export_uinfo t = export_uinfo (typ_info_t TYPE('b::mem_type))"
  assumes [simp]: "size_of TYPE('c) = size_of TYPE('a)" 
  shows "h_val h (PTR('b) &((PTR_COERCE('c::packed_type \<rightarrow> 'a::packed_type) p)\<rightarrow>f)) = 
           from_bytes (access_ti\<^sub>0 t (COERCE ('c \<rightarrow> 'a) (h_val h p)))"
  apply (simp add:h_val_coerce_ptr_coerce_packed[symmetric]) 
  apply (rule h_val_field_from_bytes' [OF assms(1) assms(2)])
  done


lemma packed_type_value_update_ti_explode: 
  "(v::'a::packed_type) = update_ti (typ_info_t TYPE('a)) (to_bytes_p v) v'"
  by (simp add: size_of_def update_ti_s_from_bytes update_ti_update_ti_t)

lemma packed_type_to_bytes_to_bytes_p_conv: 
  "length bs = size_of TYPE('a::packed_type) \<Longrightarrow> to_bytes v bs = to_bytes_p (v::'a)"
  apply (simp add: to_bytes_p_def)
  by (simp add: packed_type_access_ti to_bytes_def)

lemma packed_type_to_byte_p_coerce:
  assumes sz:"size_of TYPE('c::packed_type) = size_of TYPE('a::packed_type)" 
  shows  "to_bytes_p (COERCE('a \<rightarrow> 'c) v) = to_bytes_p v" 
  using sz
  apply (simp add: to_bytes_p_def coerce_def)
  by (metis (mono_tags, lifting) field_access_update_same(1) field_desc.simps(2) field_desc_def 
      from_bytes_def len length_replicate size_of_fold td_fafu_idem to_bytes_def 
      update_ti_t_def wf_fd)

lemma to_bytes_coerce_packed: 
  "size_of TYPE('a) = size_of TYPE('b) \<Longrightarrow> length bs = size_of TYPE('a) \<Longrightarrow> 
  to_bytes (COERCE('a::packed_type\<rightarrow>'b::packed_type) v) bs = to_bytes v bs"
  by (simp add: coerce_def field_access_update_same(1) from_bytes_def packed_type_access_ti 
      size_of_def td_fafu_idem to_bytes_def update_ti_t_def)

lemma heap_update_ptr_coerse_packed:
  fixes p::"'c::packed_type ptr"
  assumes cgrd: "c_guard p"
  assumes [simp]: "size_of TYPE('c) = size_of TYPE('a::packed_type )" 
  shows "heap_update (PTR_COERCE('c \<rightarrow> 'a) p) v = heap_update p (COERCE('a \<rightarrow>'c) v)"
  apply (rule ext)
  apply (simp add: heap_update_def packed_type_to_bytes_to_bytes_p_conv packed_type_to_byte_p_coerce)
  done

lemma c_guard_ptr_coerceI: 
  "size_td (typ_info_t TYPE('c)) = size_td (typ_info_t TYPE('a)) \<Longrightarrow> 
  align_td (typ_info_t TYPE('a)) \<le> align_td (typ_info_t TYPE('c)) \<Longrightarrow>  
  c_guard p \<Longrightarrow>
  c_guard (PTR_COERCE('c::c_type\<rightarrow>'a::c_type) p)"
  apply (cases p)
  using power_le_dvd
  by (auto simp add: c_guard_def c_null_guard_def ptr_aligned_def align_of_def size_of_def)
 

lemma heap_update_field_ptr_coerce_from_bytes_packed:
  fixes p::"'c::{xmem_type, packed_type} ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a::{xmem_type, packed_type})) f 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t  (TYPE('b::{xmem_type}))"
  assumes cgrd: "c_guard (PTR_COERCE('c\<rightarrow> 'a) p)"
  assumes sz[simp]: "size_of TYPE('c) = size_of TYPE('a)" 
  shows "heap_update (PTR('b) &((PTR_COERCE('c\<rightarrow> 'a) p)\<rightarrow>f)) v h =
           heap_update p (coerce_map (update_ti t (to_bytes_p v)) (h_val h p)) h"
  apply (subst heap_update_field_root_conv' [OF  fl match cgrd])
  apply (simp add: heap_update_def h_val_coerce_ptr_coerce_packed )
  apply (subst coerce_coerce_map_cancel_packed[OF sz[symmetric], symmetric])
  apply (simp add: coerce_map_def)
  apply (subst to_bytes_coerce_packed)
    apply (simp_all)
  done


named_theorems L2_modify_heap_update_field_root_conv

context heap_state
begin
lemma heap_update_field_root_conv:
  fixes p::"'a::xmem_type ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (adjust_ti (typ_info_t TYPE('b::xmem_type)) fld (fld_update \<circ> (\<lambda>x _. x)), n)"
  assumes fg_cons: "fg_cons fld (fld_update \<circ> (\<lambda>x _. x))"
  assumes cgrd: "c_guard p"
  shows "(hmem_upd (heap_update (PTR('b) &(p\<rightarrow>f)) v)) = 
          (\<lambda>s. (hmem_upd (heap_update p (fld_update (\<lambda>_. v) (h_val (hmem s) p)))) s)"
  apply (subst heap_update_field_root_conv_pointless' [OF fl fg_cons cgrd])
  apply (rule ext)
  by (metis (mono_tags, lifting) heap.upd_cong)

lemma heap_update_field_root_conv':
  fixes p::"'a::xmem_type ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('b::xmem_type)"
  assumes cgrd: "c_guard p"
  shows "(hmem_upd (heap_update (PTR('b) &(p\<rightarrow>f)) v)) = 
          (\<lambda>s. (hmem_upd (heap_update p (update_ti t (to_bytes_p v) (h_val (hmem s) p)))) s)"
  using heap_update_field_root_conv' [OF fl match cgrd, of v]
  using heap.upd_cong by blast

lemma L2_modify_heap_update_field_root_conv:
  fixes p::"'a::xmem_type ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (adjust_ti (typ_info_t TYPE('b::xmem_type)) fld (fld_update \<circ> (\<lambda>x _. x)), n)"
  assumes fg_cons: "fg_cons fld (fld_update \<circ> (\<lambda>x _. x))"
  assumes cgrd: "c_guard p"
  shows "L2_modify (\<lambda>s. hmem_upd (heap_update (PTR('b) &(p\<rightarrow>f)) (v s)) s) = 
         L2_modify (\<lambda>s. (hmem_upd (heap_update p (fld_update (\<lambda>_. v s) (h_val (hmem s) p)))) s)"
  by (simp add:  heap_update_field_root_conv [OF fl fg_cons cgrd])

lemma L2_modify_heap_update_field_root_conv' [L2_modify_heap_update_field_root_conv]:
  fixes p::"'a::xmem_type ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('b::xmem_type)"
  assumes cgrd: "c_guard p"
  shows "L2_modify (\<lambda>s. hmem_upd (heap_update (PTR('b) &(p\<rightarrow>f)) (v s)) s) = 
         L2_modify (\<lambda>s. (hmem_upd (heap_update p (update_ti t (to_bytes_p (v s)) (h_val (hmem s) p)))) s)"
  by (simp add:  heap_update_field_root_conv' [OF fl match cgrd])


lemma L2_modify_heap_update_ptr_coerce_packed_conv':
  fixes p::"'c::packed_type ptr"
  assumes cgrd: "c_guard p"
  assumes sz: "size_td (typ_info_t TYPE('c)) = size_td (typ_info_t TYPE('a::packed_type))" 
  shows "L2_modify (\<lambda>s. hmem_upd (heap_update (PTR_COERCE('c \<rightarrow> 'a) p) (COERCE('c \<rightarrow> 'a) (v s))) s) = 
         L2_modify (\<lambda>s. (hmem_upd (heap_update p (v s))) s)"
  using  heap_update_ptr_coerse_packed [simplified size_of_def, OF cgrd sz] heap.upd_cong
  by (metis assms(2) coerce_cancel_packed size_of_def)

lemma L2_modify_heap_update_ptr_coerce_packed_conv[L2_modify_heap_update_field_root_conv]:
  fixes p::"'c::packed_type ptr"
  assumes cgrd: "c_guard p"
  assumes sz: "size_td (typ_info_t TYPE('c)) = size_td (typ_info_t TYPE('a::packed_type))" 
  shows "L2_modify (\<lambda>s. hmem_upd (heap_update (PTR_COERCE('c \<rightarrow> 'a) p) (v s)) s) = 
         L2_modify (\<lambda>s. (hmem_upd (heap_update p (COERCE('a \<rightarrow> 'c) (v s)))) s)"
  using  heap_update_ptr_coerse_packed [simplified size_of_def, OF cgrd sz] heap.upd_cong
  by (metis assms(2) coerce_cancel_packed size_of_def)

lemma L2_modify_heap_update_ptr_coerce_packed_field_root_conv [L2_modify_heap_update_field_root_conv]:
  fixes p::"'c::{xmem_type, packed_type} ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a::{xmem_type, packed_type})) f 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('b::xmem_type)"
  assumes cgrd: "c_guard (PTR_COERCE('c\<rightarrow> 'a) p)"
  assumes sz: "size_td (typ_info_t TYPE('c)) = size_td (typ_info_t TYPE('a))" 
  shows "L2_modify (\<lambda>s. hmem_upd (heap_update (PTR('b) &((PTR_COERCE('c\<rightarrow> 'a) p)\<rightarrow>f)) (v s)) s) = 
         L2_modify (\<lambda>s. (hmem_upd (heap_update p (coerce_map (update_ti t (to_bytes_p (v s))) (h_val (hmem s) p)))) s)"
  using heap_update_field_ptr_coerce_from_bytes_packed [simplified size_of_def, OF fl match cgrd sz] heap.upd_cong
  by meson
end


lemma L2_try_state_asssumeE_bindE:
  "L2_try (assume_result_and_state P >>= f) = assume_result_and_state P >>= (\<lambda>x. L2_try (f x))"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff L2_defs)
  done

lemma refines_L2_try_L2_seq_nondet:
  assumes g [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (L2_try (g v)) (g' v) t t (rel_prod rel_liftE (=)))"
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines f f' s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_try (L2_seq f g)) (f' >>=  g') s s  (rel_prod rel_liftE (=))"
  unfolding L2_try_def L2_seq_def try_nested_bind_exception_or_result_conv
  using g f
  apply (clarsimp simp add: refines_def_old L2_defs succeeds_bind reaches_bind reaches_try succeeds_bind_exception_or_result 
      rel_liftE_def unnest_exn_def reaches_bind_exception_or_result succeeds_bind_exception_or_result  split: xval_splits sum.splits)
  apply (intro conjI allI impI)
   apply (metis case_xval_simps(2) )
  apply clarsimp
  subgoal for r s' r'
    apply (cases r)
    subgoal
      apply (cases r')
      subgoal       
        apply (clarsimp simp add: default_option_def Exn_def [symmetric])
        by (meson Exn_neq_Result obj_sumE)

      subgoal
        apply (clarsimp simp add: default_option_def Exn_def [symmetric])
        subgoal for s1 y r1
          apply (cases r1)
          subgoal
            apply (clarsimp simp add: default_option_def Exn_def [symmetric])
            by (metis Exn_neq_Result Result_eq_Result case_xval_simps(1) old.sum.simps(5) sum_all_ex(2))
          subgoal
            by (auto simp add: default_option_def Exn_def [symmetric])
          done
        done
      done
    subgoal
      apply (cases r')

      subgoal       
        apply (clarsimp simp add: default_option_def Exn_def [symmetric])
        by (meson Exn_neq_Result sum_all_ex(2))
      subgoal       
        apply (clarsimp simp add: default_option_def Exn_def [symmetric])
        subgoal for s1 r1
          apply (cases r1)
          subgoal
            apply (clarsimp simp add: default_option_def Exn_def [symmetric])
            by (metis Result_eq_Result case_xval_simps(1) old.sum.simps(6) sum_all_ex(2))
          subgoal
            by (metis case_xval_simps(2))
          done
        done
      done
    done
  done



lemma refines_L2_try_pure:
  assumes f: "refines f (return f') s s (rel_prod rel_liftE (=))"
  shows "refines (L2_try f) (return f') s s (rel_prod rel_liftE (=))"
  unfolding L2_defs L2_guarded_def using f
  by (fastforce simp add: refines_def_old reaches_try rel_liftE_def)


lemma refines_liftE_conv: "refines f f' s t (rel_prod rel_liftE (=)) \<longleftrightarrow>
 refines f (liftE f') s t (=)"
 unfolding L2_defs L2_guarded_def 
  by (auto simp add: refines_def_old reaches_liftE rel_liftE_def)

lemma refines_rel_liftE_L2_try_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s s (rel_prod rel_liftE (=))"
  shows "refines (L2_try (on_exit f\<^sub>c cleanup)) (on_exit f\<^sub>a cleanup) s s (rel_prod rel_liftE (=))"
  using f unfolding L2_defs try_def refines_map_value_left_iff
  apply (rule refines_rel_prod_eq_on_exit[THEN refines_weaken])
  apply (auto simp: rel_liftE_def)
  done


lemma map_value_on_exit:
  "map_value g (on_exit f cleanup) = on_exit (map_value g f) cleanup"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff on_exit_def on_exit'_def)
  done

lemma L2_try_on_exit: "L2_try (on_exit f cleanup) = on_exit (L2_try f) cleanup"
  unfolding L2_try_def try_def
  by (simp add: map_value_on_exit)


context stack_heap_state
begin
lemma L2_try_with_fresh_stack_ptr: 
  "L2_try (with_fresh_stack_ptr n init f) = with_fresh_stack_ptr n init (\<lambda>p. L2_try (f p))"
  by (simp add: with_fresh_stack_ptr_def L2_try_state_asssumeE_bindE L2_try_on_exit)
end

lemma map_value_guard_on_exit:
  "map_value g (guard_on_exit f P cleanup) = guard_on_exit (map_value g f) P cleanup"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff on_exit'_def)
  done


lemma L2_try_guard_on_exit:
  "L2_try (guard_on_exit f P cleanup) = guard_on_exit (L2_try f) P cleanup"
  unfolding L2_try_def try_def
  by (simp add: map_value_guard_on_exit)


lemma map_value_assume_on_exit:
  "map_value g (assume_on_exit f P cleanup) = assume_on_exit (map_value g f) P cleanup"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff on_exit'_def)
  done

lemma L2_try_assume_on_exit:
  "L2_try (assume_on_exit f P cleanup) = assume_on_exit (L2_try f) P cleanup"
  unfolding L2_try_def try_def
  by (simp add: map_value_assume_on_exit)

context typ_heap_typing
begin
lemma L2_try_guard_with_fresh_stack_ptr:
  "L2_try (guard_with_fresh_stack_ptr n init f) = guard_with_fresh_stack_ptr n init (\<lambda>p. L2_try (f p))"
  unfolding guard_with_fresh_stack_ptr_def L2_try_state_asssumeE_bindE assume_stack_alloc_def 
    L2_try_guard_on_exit ..

lemma L2_try_assume_with_fresh_stack_ptr:
  "L2_try (assume_with_fresh_stack_ptr n init f) = assume_with_fresh_stack_ptr n init (\<lambda>p. L2_try (f p))"
  unfolding assume_with_fresh_stack_ptr_def L2_try_state_asssumeE_bindE assume_stack_alloc_def 
    L2_try_assume_on_exit ..

lemma L2_try_with_fresh_stack_ptr:
  "L2_try (with_fresh_stack_ptr n init f) = with_fresh_stack_ptr n init (\<lambda>p. L2_try (f p))"
  by (simp add: with_fresh_stack_ptr_def L2_try_state_asssumeE_bindE assume_stack_alloc_def
      L2_try_on_exit)
end

lemma refines_L2_seq:
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'. Q (Exn e, t) (Exn e', t') \<Longrightarrow> R (Exn e, t) (Exn e', t')"
  assumes lr: "\<And>e v' t t'. Q (Exn e, t) (Result v', t') \<Longrightarrow> refines (throw e) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exn e', t') \<Longrightarrow> refines (g v) (throw e') t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow> refines (g v) (g' v') t t' R"
  shows "refines (L2_seq f g) (L2_seq f' g') s s' R"
  unfolding L2_seq_def using f ll lr rl rr
  by (rule refines_bind_bind_exn)


lemma rel_Nonlocal_Nonlocal: "rel_Nonlocal (Nonlocal x) x"
  by (simp add: rel_Nonlocal_def)

lemmas rel_sum_Inl = rel_sum.intros(1)
lemmas rel_sum_Inr = rel_sum.intros(2)

lemma rel_sum_eq: "rel_sum (=) (=) x x"
  by (auto simp add: rel_sum.simps)


end
