(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


section \<open>Hoare-Triples for L1 (internal use)\<close>


theory L1Valid
imports L1Defs
begin

definition
  validE :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 'a, 's) exn_monad \<Rightarrow>
             ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
             ('e \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"

  where "validE P f Q E \<equiv> \<forall>s. P s \<longrightarrow> f \<bullet> s ?\<lbrace> \<lambda>v s. case v of Result r \<Rightarrow> Q r s | Exn e \<Rightarrow> E e s \<rbrace>"

open_bundle validE_syntax
begin
notation validE (\<open>(\<open>open_block notation=\<open>mixfix L1 Hoare triple\<close>\<close>\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>))\<close>)
end

lemma hoareE_TrueI: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>r _. True\<rbrace>"
  by (simp add: validE_def runs_to_partial_def_old split: xval_splits)

lemma combine_validE: "\<lbrakk> \<lbrace> P \<rbrace> x \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>;
         \<lbrace> P' \<rbrace> x \<lbrace> Q' \<rbrace>,\<lbrace> E' \<rbrace> \<rbrakk> \<Longrightarrow>
         \<lbrace> P and P' \<rbrace> x \<lbrace> \<lambda>r. (Q r) and (Q' r) \<rbrace>,\<lbrace>\<lambda>r. (E r) and (E' r) \<rbrace>"
  by (auto simp add: validE_def runs_to_partial_def_old split: xval_splits)

(* Weakest Precondition Proofs (WP) *)

lemma L1_skip_wp: "\<lbrace> P () \<rbrace> L1_skip \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  apply (clarsimp simp: L1_skip_def validE_def)
  done

lemma L1_modify_wp: "\<lbrace> \<lambda>s. P () (f s) \<rbrace> L1_modify f \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  apply (clarsimp simp: L1_modify_def validE_def)
  apply (runs_to_vcg)
  done

lemma L1_spec_wp: "\<lbrace> \<lambda>s. \<forall>t. (s, t) \<in> f \<longrightarrow> P () t \<rbrace> L1_spec f \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  apply (clarsimp simp add: L1_spec_def validE_def)
  apply (runs_to_vcg)
  apply auto
  done

lemma L1_assume_wp: "\<lbrace> \<lambda>s. \<forall>t. ((), t) \<in> f s \<longrightarrow> P () t \<rbrace> L1_assume f \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  apply (clarsimp simp add: L1_assume_def validE_def)
  apply (runs_to_vcg)
  apply auto
  done

lemma L1_init_wp: "\<lbrace> \<lambda>s. \<forall>x. P () (f (\<lambda>_. x) s) \<rbrace> L1_init f \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  apply (clarsimp simp add: L1_init_def validE_def)
  apply (runs_to_vcg)
  apply auto
  done

(* Liveness proofs. (LP) *)

lemma L1_skip_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q () s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_skip \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_skip_def)
  apply (clarsimp simp: validE_def)
  done

lemma L1_skip_lp_same_pre_post: "\<lbrace>P\<rbrace> L1_skip \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_skip_lp)


lemma L1_guard_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q () s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_guard e \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_guard_def guard_def)
  apply (clarsimp simp:  validE_def)
  apply (runs_to_vcg)
  apply auto
  done

lemma L1_guard_lp_same_pre_post: "\<lbrace>P\<rbrace> L1_guard e \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_guard_lp)

lemma L1_guarded_lp_same_pre_post: "\<lbrace>P\<rbrace> c \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace> 
\<Longrightarrow> \<lbrace>P\<rbrace> L1_guarded g c \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding L1_defs L1_guarded_def validE_def
  by (auto simp add: runs_to_partial_def_old succeeds_bind reaches_bind)

lemma L1_guarded_lp_gets: "(\<And>p. \<lbrace>P\<rbrace> (c p) \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>) 
\<Longrightarrow> \<lbrace>P\<rbrace> L1_guarded g (gets dest \<bind> (\<lambda>p. c p)) \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding L1_defs L1_guarded_def validE_def
  by (auto simp add: runs_to_partial_def_old succeeds_bind reaches_bind)





lemma L1_fail_lp: "\<lbrace>P\<rbrace> L1_fail \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_fail_def validE_def)
  done

lemma L1_fail_lp_same_pre_post: "\<lbrace>P\<rbrace> L1_fail \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_fail_lp)


lemma L1_throw_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> E () s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_throw \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_throw_def validE_def)
  done

lemma L1_throw_lp_same_pre_post: "\<lbrace>P\<rbrace> L1_throw \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_throw_lp)

lemma L1_spec_lp: "\<lbrakk> \<And>s r. \<lbrakk> (s, r) \<in> e; P s \<rbrakk> \<Longrightarrow> Q () r \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_spec e \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_spec_def validE_def)
  apply (runs_to_vcg)
  apply auto
  done

lemma L1_spec_lp_same_pre_post: "\<lbrakk> \<And>s r. \<lbrakk> (s, r) \<in> e; P s \<rbrakk> \<Longrightarrow> P r \<rbrakk> 
 \<Longrightarrow> \<lbrace>P\<rbrace> L1_spec e \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_spec_lp)


lemma L1_modify_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q () (f s) \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_modify f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_modify_def validE_def)
  apply (runs_to_vcg)
  apply auto
  done

lemma L1_modify_lp_same_pre_post: "\<lbrakk> \<And>s. P s \<Longrightarrow> P (f s) \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_modify f \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_modify_lp)

lemma L1_call_lp:
  "\<lbrakk> \<And>s r. P s \<Longrightarrow> Q () (return_xf r (scope_teardown s r)); 
    \<And>s r. P s \<Longrightarrow> E () (result_exn (scope_teardown s r) r)\<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> L1_call scope_setup dest_fn scope_teardown result_exn return_xf \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_defs L1_call_def validE_def)
  apply (runs_to_vcg)
  apply (auto simp add: runs_to_partial_def_old reaches_bind)
  done

lemma L1_call_lp_same_pre_post:
  "\<lbrakk> \<And>s r. P s \<Longrightarrow> P (return_xf r (scope_teardown s r)); 
    \<And>s r. P s \<Longrightarrow> P (result_exn (scope_teardown s r) r)\<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> L1_call scope_setup dest_fn scope_teardown result_exn return_xf \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_call_lp)

lemma L1_seq_lp: "\<lbrakk>
    \<lbrace>P1\<rbrace> A \<lbrace>Q1\<rbrace>,\<lbrace>E1\<rbrace>;
    \<lbrace>P2\<rbrace> B \<lbrace>Q2\<rbrace>,\<lbrace>E2\<rbrace>;
    \<And>s. P s \<Longrightarrow> P1 s;
    \<And>s. Q1 () s \<Longrightarrow> P2 s;
    \<And>s. Q2 () s \<Longrightarrow> Q () s;
    \<And>s. E1 () s \<Longrightarrow> E () s;
    \<And>s. E2 () s \<Longrightarrow> E () s
    \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_seq A B \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_seq_def validE_def)
  apply (runs_to_vcg)
  apply (fastforce simp add: runs_to_partial_def_old reaches_bind split: xval_splits)
  done

lemma L1_seq_lp_same_pre_post: "\<lbrakk>
    \<lbrace>P\<rbrace> A \<lbrace>\<lambda>_. P\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>;
    \<lbrace>P\<rbrace> B \<lbrace>\<lambda>_. P\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>
    \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_seq A B \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_seq_lp)

lemma L1_condition_lp: "
  \<lbrakk> \<lbrace>P1\<rbrace> A \<lbrace>Q1\<rbrace>,\<lbrace>E1\<rbrace>;
    \<lbrace>P2\<rbrace> B \<lbrace>Q2\<rbrace>,\<lbrace>E2\<rbrace>;
    \<And>s. P s \<Longrightarrow> P1 s;
    \<And>s. P s \<Longrightarrow> P2 s;
    \<And>s. Q1 () s \<Longrightarrow> Q () s;
    \<And>s. Q2 () s \<Longrightarrow> Q () s;
    \<And>s. E1 () s \<Longrightarrow> E () s;
    \<And>s. E2 () s \<Longrightarrow> E () s \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> L1_condition c A B \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_condition_def validE_def)
  apply (runs_to_vcg)
   apply (fastforce simp add: runs_to_partial_def_old split: xval_splits)+
  done

lemma L1_condition_lp_same_pre_post: "
  \<lbrakk>\<lbrace>P\<rbrace> A \<lbrace>\<lambda>_. P\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>;
   \<lbrace>P\<rbrace> B \<lbrace>\<lambda>_. P\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>
  \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> L1_condition c A B \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_condition_lp)


lemma L1_catch_lp: "
  \<lbrakk> \<lbrace>P1\<rbrace> A \<lbrace>Q1\<rbrace>,\<lbrace>E1\<rbrace>;
    \<lbrace>P2\<rbrace> B \<lbrace>Q2\<rbrace>,\<lbrace>E2\<rbrace>;
    \<And>s. P s \<Longrightarrow> P1 s;
    \<And>s. E1 () s \<Longrightarrow> P2 s;
    \<And>s. Q1 () s \<Longrightarrow> Q () s;
    \<And>s. Q2 () s \<Longrightarrow> Q () s;
    \<And>s. E2 () s \<Longrightarrow> E () s \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> L1_catch A B \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_catch_def validE_def)
  apply (runs_to_vcg)
  apply (fastforce simp add: runs_to_partial_def_old split: xval_splits)
  done

lemma L1_catch_lp_same_pre_post: "
  \<lbrakk>\<lbrace>P\<rbrace> A \<lbrace>\<lambda>_. P\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>;
   \<lbrace>P\<rbrace> B \<lbrace>\<lambda>_. P\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>
  \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> L1_catch A B \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_catch_lp)


lemma L1_init_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> \<forall>x. Q () (f (\<lambda>_. x) s) \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_init f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp add:  L1_init_def validE_def)
  apply (runs_to_vcg)
  apply auto
  done

lemma L1_init_lp_same_pre_post: "\<lbrakk> \<And>s. P s \<Longrightarrow> \<forall>x. P (f (\<lambda>_. x) s) \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_init f \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  by (rule L1_init_lp)


lemma validE_weaken:
  "\<lbrakk> \<lbrace>P'\<rbrace> A \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace>; \<And>s. P s \<Longrightarrow> P' s; \<And>r s. Q' r s \<Longrightarrow> Q r s; \<And>r s. E' r s \<Longrightarrow> E r s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (fastforce simp add: validE_def runs_to_partial_def_old split: xval_splits)
  done

lemma L1_while_lp:
  assumes body_lp: "\<lbrace> P' \<rbrace> B \<lbrace> Q' \<rbrace>, \<lbrace> E' \<rbrace>"
  and p_impl: "\<And>s. P s \<Longrightarrow> P' s"
  and q_impl: "\<And>s. Q' () s \<Longrightarrow> Q () s"
  and e_impl: "\<And>s. E' () s \<Longrightarrow> E () s"
  and inv: " \<And>s. Q' () s \<Longrightarrow> P' s"
  and inv': " \<And>s. P' s \<Longrightarrow> Q' () s"
shows "\<lbrace> P \<rbrace> L1_while c B \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (rule validE_weaken [where P'=P' and Q'=Q' and E'=E'])
     apply (clarsimp simp: L1_while_def validE_def)

     apply (rule runs_to_partial_whileLoop_exn  [where I="\<lambda>r s. (case r of Exn e \<Rightarrow> E' () s | _ \<Rightarrow>  P' s)"])
        apply simp
       apply (simp add: inv')
      apply (simp)
     apply simp
  subgoal using body_lp
    by ( simp add: inv validE_def runs_to_partial_def_old split: xval_splits)
    apply (simp add: p_impl)
   apply (simp add: q_impl)
  apply (simp add: e_impl)
  done

lemma L1_while_lp_same_pre_post:
  assumes body_lp: "\<lbrace> P \<rbrace> B \<lbrace> \<lambda>_. P\<rbrace>, \<lbrace> \<lambda>_. P \<rbrace>"
  shows "\<lbrace> P \<rbrace> L1_while c B \<lbrace>\<lambda>_. P \<rbrace>,\<lbrace> \<lambda>_. P \<rbrace>"
  by (rule L1_while_lp [OF body_lp])

lemma on_exit_lp_same_pre_post:
  assumes cleanup: "\<And>s t. (s,t) \<in> cleanup \<Longrightarrow>  P t = P s"
  assumes c: "\<lbrace>P\<rbrace> c \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> on_exit c cleanup \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp add: validE_def on_exit'_def on_exit_def)
  apply (runs_to_vcg)
  using cleanup c
  apply (fastforce simp add: validE_def runs_to_partial_def_old succeeds_bind   
      reaches_bind default_option_def Exn_def split: xval_splits)
  done

lemma seqE:
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>"
  assumes g_valid: "\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrace>A\<rbrace> do { x \<leftarrow> f; g x } \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  using assms
  apply (clarsimp simp add: validE_def)
  apply (runs_to_vcg)
  apply (fastforce simp add: runs_to_partial_def_old split: xval_splits)
  done

named_theorems with_fresh_stack_ptr_lp_same_pre_post
context stack_heap_state
begin
lemma with_fresh_stack_ptr_lp_same_pre_post[with_fresh_stack_ptr_lp_same_pre_post]: 
  assumes c: "\<And>p. \<lbrace>P\<rbrace> (c p) \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  assumes htd_indep: "\<And>s g. P (htd_upd g s) = P s"
  assumes hmem_indep: "\<And>s f. P (hmem_upd f s) = P s"
shows "\<lbrace>P\<rbrace> with_fresh_stack_ptr n g c \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp add: with_fresh_stack_ptr_def)
  apply (rule seqE [where B="\<lambda>_. P"])
  subgoal
    apply (clarsimp simp add: validE_def)
    apply (runs_to_vcg)
    by (clarsimp simp add:  htd_indep hmem_indep)
  subgoal
    apply (rule on_exit_lp_same_pre_post [OF _ c])
    apply (auto simp add: htd_indep hmem_indep)
    done
  done
end

lemma validE_weaken_dependent:
  assumes dep_spec: "\<And>s. P s \<Longrightarrow> \<lbrace>P' s\<rbrace> A \<lbrace>Q' s\<rbrace>, \<lbrace>E' s\<rbrace>" 
  assumes weaken_pre: "\<And>s. P s \<Longrightarrow> P' s s"
  assumes weaken_norm: "(\<And>s r t. P' s s \<Longrightarrow> Q' s r t \<Longrightarrow> Q r t)" 
  assumes weaken_exn: "(\<And>s r t. P' s s \<Longrightarrow> E' s r t \<Longrightarrow> E r t)"
  shows "\<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  using assms
  apply (fastforce simp add: validE_def runs_to_partial_def_old split: xval_splits)
  done

lemma validE_weaken_dependent_same:
  assumes dep_spec: "\<And>s. P s \<Longrightarrow> \<lbrace>P' s\<rbrace> A \<lbrace>\<lambda>_. P' s\<rbrace>, \<lbrace>\<lambda>_. P' s\<rbrace>" 
  assumes weaken_post: "(\<And>s t. P' s t \<Longrightarrow> P t)" 
  assumes weaken_pre: "\<And>s. P s \<Longrightarrow> P' s s"
  shows "\<lbrace>P\<rbrace> A \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  using dep_spec weaken_pre weaken_post weaken_post 
  by (rule validE_weaken_dependent)

end
