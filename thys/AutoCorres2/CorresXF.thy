(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * A stronger version of the "corres" framework, allowing return
 * relationships to reference state data.
 *)

theory CorresXF
imports
  CCorresE
begin

(*
 * Refinement with return extraction on the concrete side:
 *
 * For any step on the concrete side, there is an equivalent step on
 * the abstract side.
 *
 * If the abstract step fails, we don't need refinement to hold.
 *)

definition "corresXF_simple st xf P M M' \<equiv>
  \<forall>s. (P s \<and> succeeds M (st s)) \<longrightarrow> (\<forall>r' t'. reaches M' s r' t' \<longrightarrow>
        reaches M (st s) (xf r' t') (st t')) \<and> succeeds M' s"

(*
 * A definition better suited to dealing with monads with exceptions.
 *)
definition "corresXF st ret_xf ex_xf P A C \<equiv>
    \<forall>s. P s \<and> succeeds A (st s) \<longrightarrow>
        (\<forall>r t. reaches C s r t \<longrightarrow> 
          (case r of
             Exn r    \<Rightarrow> reaches A (st s) (Exn (ex_xf r t)) (st t)
           | Result r \<Rightarrow> reaches A (st s) (Result (ret_xf r t)) (st t)))
        \<and> succeeds C s"


definition "rel_XF st ret_xf ex_xf Q \<equiv> \<lambda>(r, t) (r', t'). 
  t' = st t \<and> 
  rel_xval (\<lambda>e e'. e' = ex_xf e t) (\<lambda>v v'. v' = ret_xf v t) r r' \<and>
  Q r t"

lemma corresXF_refines_iff: 
  "corresXF st ret_xf ex_xf P A C \<longleftrightarrow>
      (\<forall>s. P s \<longrightarrow> refines C A s (st s) (rel_XF st ret_xf ex_xf (\<lambda>_ _. True)))"
  apply standard
  subgoal
    apply (clarsimp simp add: corresXF_def refines_def_old rel_XF_def rel_xval.simps split: xval_splits)
    by (metis Exn_def default_option_def exception_or_result_cases not_Some_eq)
  subgoal
    apply (fastforce simp add: corresXF_def refines_def_old rel_XF_def rel_xval.simps split: xval_splits)
    done
  done

(*
* Stronger variant with postcondition
*)
definition "corresXF_post st ret_xf ex_xf P Q A C \<equiv>
    \<forall>s. P s \<and> succeeds A (st s) \<longrightarrow>
        (\<forall>r t. reaches C s r t \<longrightarrow> Q s r t \<and>
          (case r of
             Exn r    \<Rightarrow> reaches A (st s) (Exn (ex_xf r t)) (st t)
           | Result r \<Rightarrow> reaches A (st s) (Result (ret_xf r t)) (st t)))
        \<and> succeeds C s"

lemma corresXF_post_refines_iff: 
  "corresXF_post st ret_xf ex_xf P Q A C \<longleftrightarrow>
      (\<forall>s. P s \<longrightarrow> refines C A s (st s) (rel_XF st ret_xf ex_xf (Q s)))"
  apply standard
  subgoal
    apply (clarsimp simp add: corresXF_post_def refines_def_old rel_XF_def rel_xval.simps split: xval_splits)
    by (metis Exn_def default_option_def exception_or_result_cases not_Some_eq)
  subgoal
    apply (fastforce simp add: corresXF_post_def refines_def_old rel_XF_def rel_xval.simps split: xval_splits)
    done
  done

lemma corresXF_post_to_corresXF: 
  "corresXF_post st ret_xf ex_xf P Q A C \<Longrightarrow> corresXF st ret_xf ex_xf P A C"
  by (auto simp add: corresXF_def corresXF_post_def)

lemma corresXF_corres_XF_post_conv: 
  "corresXF st ret_xf ex_xf P A C = corresXF_post st ret_xf ex_xf P (\<lambda>_ _ _. True) A C"
  by (auto simp add: corresXF_def corresXF_post_def)


(* corresXF can be defined in terms of corresXF_simple. *)
lemma corresXF_simple_corresXF:
  "(corresXF_simple st
       (\<lambda>x s. case x of
           Exn r \<Rightarrow> Exn (ex_state r s)
         | Result r \<Rightarrow> (Result (ret_state r s))) P M M')
  = (corresXF st ret_state ex_state P M M')"
 unfolding corresXF_simple_def corresXF_def
 by (auto split: xval_splits)


lemma corresXF_simpleI: "\<lbrakk>
    \<And>s' t' r'. \<lbrakk>P s'; succeeds M (st s'); reaches M' s' r' t'\<rbrakk>
        \<Longrightarrow> reaches M (st s') (xf r' t') (st t');
    \<And>s'. \<lbrakk>P s'; succeeds M (st s') \<rbrakk> \<Longrightarrow> succeeds M' s'
  \<rbrakk> \<Longrightarrow> corresXF_simple st xf P M M'"
  apply atomize
  apply (clarsimp simp: corresXF_simple_def)
  done

lemma corresXF_I: "\<lbrakk>
    \<And>s' t' r'. \<lbrakk>P s'; succeeds M (st s'); reaches M' s' (Result r') t'\<rbrakk>
        \<Longrightarrow> reaches M (st s') (Result (ret_state r' t'))  (st t');
    \<And>s' t' r'. \<lbrakk>P s'; succeeds M (st s'); reaches M' s' (Exn r')  t'\<rbrakk>
        \<Longrightarrow> reaches M (st s') (Exn (ex_state r' t'))  (st t');
    \<And>s'. \<lbrakk>P s'; succeeds M (st s') \<rbrakk> \<Longrightarrow> succeeds M' s'
  \<rbrakk> \<Longrightarrow> corresXF st ret_state ex_state P M M'"
  apply atomize
  apply (clarsimp simp: corresXF_def)
  subgoal for s r t
    apply (erule_tac x=s in allE, erule (1) impE)
    apply (erule_tac x=s in allE, erule (1) impE)
    apply (erule_tac x=s in allE, erule (1) impE)
    apply (clarsimp split: xval_splits)
    apply auto
    done
  done

lemma ccpo_prod_gfp_gfp:
  "class.ccpo
    (prod_lub Inf Inf :: (('a::complete_lattice * 'b :: complete_lattice) set \<Rightarrow> _))
    (rel_prod (\<ge>) (\<ge>)) (mk_less (rel_prod (\<ge>) (\<ge>)))"
  by (rule ccpo_rel_prodI ccpo_Inf)+

lemma admissible_mem: "ccpo.admissible Inf (\<ge>) (\<lambda>A. x \<in> A)"
  by (auto simp: ccpo.admissible_def)

lemma admissible_nondet_ord_corresXF:
  "ccpo.admissible Inf (\<ge>) (\<lambda>A. corresXF st R E P A C)"
  unfolding corresXF_def imp_conjL imp_conjR
  apply (intro admissible_all  admissible_conj admissible_imp)
  subgoal for s
  apply (rule ccpo.admissibleI)
    apply (clarsimp simp add: ccpo.admissible_def chain_def 
        succeeds_def reaches_def split: prod.splits xval_splits)
    apply (intro conjI allI impI)
    subgoal
      apply transfer
      by (auto simp add: Inf_post_state_def top_post_state_def)
         (metis outcomes.simps(2) post_state.simps(3))
    subgoal
      apply transfer
      by (auto simp add: Inf_post_state_def top_post_state_def)
         (metis outcomes.simps(2) post_state.simps(3))
    done
  subgoal
    apply (rule ccpo.admissibleI)
    apply (clarsimp simp add: ccpo.admissible_def chain_def 
        succeeds_def reaches_def split: prod.splits xval_splits)
    apply transfer
    apply (auto simp add: Inf_post_state_def top_post_state_def image_def vimage_def 
        split: if_split_asm)
    done
  done



lemma corresXF_top: "corresXF st ret_xf ex_xf P \<top> C"
  by (auto simp add: corresXF_def)

lemma admissible_nondet_ord_corresXF_post:
  "ccpo.admissible Inf (\<ge>) (\<lambda>A. corresXF_post st R E P Q A C)"
  unfolding corresXF_post_def imp_conjL imp_conjR
  apply (intro admissible_all  admissible_conj admissible_imp)
  subgoal
  apply (rule ccpo.admissibleI)
    apply (clarsimp simp add: ccpo.admissible_def chain_def 
        succeeds_def reaches_def split: prod.splits xval_splits)
    apply (intro conjI allI impI)
    subgoal
      apply transfer
      apply (clarsimp simp add: Inf_post_state_def top_post_state_def)
      apply (metis (no_types, lifting) INF_top_conv(1) Inf_post_state_def top_post_state_def)
      done
    subgoal
      apply transfer
      by (auto simp add: Inf_post_state_def top_post_state_def)
         (metis outcomes.simps(2) post_state.simps(3))
   subgoal
     apply transfer
     apply (clarsimp simp add: Inf_post_state_def top_post_state_def)
     apply (metis (no_types, lifting) INF_top_conv(1) Inf_post_state_def top_post_state_def)
     done
   subgoal
     apply transfer
     apply (clarsimp simp add: Inf_post_state_def top_post_state_def image_def vimage_def 
         split: if_split_asm)
     by (metis outcomes.simps(2) post_state.simps(3))
    done
  subgoal
    apply (rule ccpo.admissibleI)
    apply (clarsimp simp add: ccpo.admissible_def chain_def 
        succeeds_def reaches_def split: prod.splits xval_splits)
    apply transfer
    apply (auto simp add: Inf_post_state_def top_post_state_def image_def vimage_def 
        split: if_split_asm)
    done
  done



lemma corresXF_post_top: "corresXF_post st ret_xf ex_xf P Q \<top> C"
  by (auto simp add: corresXF_post_def)

lemma corresXF_assume_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s'; s = st s' \<rbrakk> \<Longrightarrow> corresXF st xf_normal xf_exception P L R \<rbrakk> \<Longrightarrow> corresXF st xf_normal xf_exception P L R"
  apply atomize
  apply (clarsimp simp: corresXF_def)
  apply force
  done

lemma corresXF_assume_fix_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s'; s = st s' \<rbrakk> \<Longrightarrow> corresXF st xf_normal xf_exception (\<lambda>s. s = s' \<and> P s) L R \<rbrakk> \<Longrightarrow> corresXF st xf_normal xf_exception P L R"
  apply atomize
  apply (clarsimp simp: corresXF_def)
  done

lemma corresXF_guard_imp:
  "\<lbrakk> corresXF st xf_normal xf_exception Q f g; \<And>s. P s \<Longrightarrow> Q s \<rbrakk>
      \<Longrightarrow> corresXF st xf_normal xf_exception P f g"
  apply (clarsimp simp: corresXF_def)
  done

lemma corresXF_return:
  "\<lbrakk> \<And>s. \<lbrakk> P s \<rbrakk> \<Longrightarrow> xf_normal b s = a \<rbrakk> \<Longrightarrow>
     corresXF st xf_normal xf_exception P (return a) (return b)"
  apply (clarsimp simp: corresXF_def )
  done

lemma corresXF_gets:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> ret (g s) s = f (st s) \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (gets f) (gets g)"
  apply (clarsimp simp: corresXF_def)
  done

lemma corresXF_insert_guard:
  "\<lbrakk> corresXF st ret ex Q A C; \<And>s. \<lbrakk> P s \<rbrakk> \<Longrightarrow> G (st s) \<longrightarrow> Q s  \<rbrakk> \<Longrightarrow>
        corresXF st ret ex P (guard G >>= (\<lambda>_. A)) C "
  apply (auto  simp: corresXF_def succeeds_guard succeeds_bind reaches_bind reaches_guard)
  done

lemma corresXF_exec_abs_guard:
  "corresXF st ret_xf ex_xf (\<lambda>s. P s \<and> G (st s)) (A ()) C \<Longrightarrow> corresXF st ret_xf ex_xf P (guard G >>= A) C"
  apply (auto simp: corresXF_def succeeds_guard succeeds_bind reaches_bind reaches_guard)
  done

lemma corresXF_simple_exec:
  "\<lbrakk> corresXF_simple st xf P A B; reaches B s r' s'; succeeds A (st s); P s \<rbrakk>
      \<Longrightarrow> reaches A (st s) (xf r' s') (st s')"
  apply (fastforce simp: corresXF_simple_def)
  done

lemma corresXF_simple_fail:
  "\<lbrakk> corresXF_simple st xf P A B; \<not> succeeds B s; P s \<rbrakk>
      \<Longrightarrow> \<not> succeeds A (st s)"
  apply (fastforce simp: corresXF_simple_def)
  done

lemma corresXF_simple_no_fail:
  "\<lbrakk> corresXF_simple st xf P A B; succeeds A (st s); P s \<rbrakk>
      \<Longrightarrow> succeeds B s"
  apply (fastforce simp: corresXF_simple_def)
  done

lemma corresXF_exec_normal:
  "\<lbrakk> corresXF st ret ex P A B; reaches B s (Result r') s'; succeeds A (st s); P s \<rbrakk>
      \<Longrightarrow> reaches A (st s) (Result (ret r' s')) (st s')"
  by (auto simp add: corresXF_def split: xval_splits)

lemma corresXF_exec_except:
  "\<lbrakk> corresXF st ret ex P A B; reaches B s (Exn r') s'; succeeds A (st s); P s \<rbrakk>
      \<Longrightarrow> reaches A (st s) (Exn (ex r' s')) (st s')"
  by (auto simp add: corresXF_def split: xval_splits)

lemma corresXF_exec_fail:
  "\<lbrakk> corresXF st ret ex P A B; \<not> succeeds B s; P s \<rbrakk>
      \<Longrightarrow> \<not> succeeds A (st s)"
  by (auto simp add: corresXF_def split: xval_splits)

lemma corresXF_intermediate:
    "\<lbrakk> corresXF st ret_xf ex_xf P A' C;
         corresXF id (\<lambda>r s. r) (\<lambda>r s. r) (\<lambda>s. \<exists>x. s = st x \<and> P x) A A' \<rbrakk> \<Longrightarrow>
        corresXF st ret_xf ex_xf P A C"
  apply (clarsimp simp: corresXF_def split: xval_splits)
  apply fast
  done

lemma corresXF_join:
  "\<lbrakk> corresXF st V E P L L'; \<And>x y. corresXF st V' E (P' x y) (R x) (R' y); 
    \<And>s. Q s \<Longrightarrow> L' \<bullet> s ?\<lbrace> \<lambda>r t. case r of Exn _ \<Rightarrow> \<top> | Result v \<Rightarrow> P' (V v t) v t \<rbrace>; 
    \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
    corresXF st V' E Q (L >>= R) (L' >>= R')"
  apply (clarsimp simp add: corresXF_refines_iff split: xval_splits)
  apply (rule refines_bind_bind_exn[where Q="rel_XF st V E (\<lambda>_ _. True) \<sqinter>
    (\<lambda>(r, t) x. case r of Exn _ \<Rightarrow> \<top> | Result v \<Rightarrow> P' (V v t) v t)"])
  subgoal
    apply (rule refines_strengthen1[where R="rel_XF st V E (\<lambda>_ _. True)"])
    by auto
  by (auto simp add: rel_XF_def)

lemma corresXF_join_xf_state_independent_same_state:
  "\<lbrakk> corresXF (\<lambda>s. s) (\<lambda>r s. V r)  (\<lambda>r s. E r) P L L'; 
    \<And>y. corresXF (\<lambda>s. s) (\<lambda>r s. V' r)  (\<lambda>r s. E r) (P' (V y)) (R (V y)) (R' y); 
    \<And>s. Q s \<Longrightarrow> L \<bullet> s ?\<lbrace> \<lambda>r t. case r of Exn _ \<Rightarrow> \<top> | Result v \<Rightarrow> P' v t\<rbrace>; \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
    corresXF (\<lambda>s. s) (\<lambda>r s. V' r) (\<lambda>r s. E r) Q (L >>= R) (L' >>= R')"
  apply (clarsimp simp add: corresXF_refines_iff)
  apply (rule refines_bind_bind_exn[where
        Q="rel_XF (\<lambda>s. s) (\<lambda>r s. V r) (\<lambda>r s. E r) (\<lambda>_ _. True) \<sqinter>
          (\<lambda>x (r, t). case r of Exn _ \<Rightarrow> \<top> | Result v \<Rightarrow> P' v t)"])
  subgoal
    apply (rule refines_strengthen2[where R="rel_XF (\<lambda>s. s) (\<lambda>r s. V r) (\<lambda>r s. E r) (\<lambda>_ _. True)"])
    by auto
  by (auto simp add: rel_XF_def)

lemma corresXF_except:
  "\<lbrakk> corresXF st V E P L L'; \<And>x y. corresXF st V E' (P' x y) (R x) (R' y); 
    \<And>s. Q s \<Longrightarrow> L' \<bullet> s ?\<lbrace> \<lambda>r s. case r of Exn r \<Rightarrow> P' (E r s) r s | Result _ \<Rightarrow> \<top> \<rbrace>; 
    \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
    corresXF st V E' Q ( L <catch> R) (L' <catch> R')"
  apply (clarsimp simp add: corresXF_refines_iff)
  apply (rule refines_catch [where Q="(rel_XF st V E (\<lambda>_ _. True)) \<sqinter>
    (\<lambda>(r, s) x. case r of Exn r \<Rightarrow> P' (E r s) r s | Result _ \<Rightarrow> \<top>)"])
  subgoal 
    apply (rule refines_strengthen1[where R="rel_XF st V E (\<lambda>_ _. True)"])
    by auto
  apply (auto simp add: rel_XF_def)
  done

lemma corresXF_cond:
  "\<lbrakk> corresXF st V E P L L'; corresXF st V E P R R'; \<And>s. P s \<Longrightarrow> A (st s) = A' s \<rbrakk> \<Longrightarrow>
    corresXF st V E P (condition A L R) (condition A' L' R')"
  apply (clarsimp simp add: corresXF_refines_iff)
  using refines_condition by metis

lemma refines_assume_succeeds: "(succeeds g t \<Longrightarrow> refines f g s t R) \<Longrightarrow> refines f g s t R"
  by (auto simp add: refines_def_old)

lemma corresXF_while:
  assumes body_corres: "\<And>x y. corresXF st ret ex (\<lambda>s. P x s \<and> y = ret x s) (A y) (B x)"
  and cond_match: "\<And>s r. P r s \<Longrightarrow> C r s = C' (ret r s) (st s)"
  and pred_inv: "\<And>r s. P r s \<Longrightarrow> C r s \<Longrightarrow> succeeds (whileLoop C' A (ret r s)) (st s) \<Longrightarrow>
                          B r \<bullet> s ?\<lbrace> \<lambda>r s. case r of Exn _ \<Rightarrow> True | Result r \<Rightarrow> P r s \<rbrace>"
  and init_match: "\<And>s. P' x s \<Longrightarrow> y = ret x s"
  and pred_imply: "\<And>s. P' x s \<Longrightarrow> P x s"
shows "corresXF st ret ex (P' x) (whileLoop C' A y) (whileLoop C B x)"
  apply (clarsimp simp add: corresXF_refines_iff)
  apply (rule refines_assume_succeeds)
  subgoal for s
    apply (rule refines_mono [OF _ refines_whileLoop' 
          [where R = "rel_XF st ret ex (\<lambda>r s. case r of Exn _ \<Rightarrow> True | Result r \<Rightarrow> P r s) \<sqinter>
            (\<lambda>(r, s) _. case r of Exn _ \<Rightarrow> True | Result r \<Rightarrow>
              succeeds (whileLoop C' A (ret r s)) (st s))" 
          and C = C and C'=C' and B=B and B'=A and I=x and I'=y and s=s and s'="st s"]])
    subgoal by (auto simp add: rel_XF_def)
    subgoal by (auto simp add: rel_XF_def cond_match pred_imply)
    subgoal using body_corres pred_inv
      apply (subst (asm) rel_XF_def)
      apply (clarsimp simp add: corresXF_refines_iff)
      apply (rule refines_strengthen[where R="rel_XF st ret ex (\<lambda>_ _. True)" and
        G="\<lambda>r s. case r of Exn _ \<Rightarrow> True | Result r \<Rightarrow> succeeds (whileLoop C' A r) s"])
      subgoal by auto
      apply assumption
      subgoal
        apply (subst (asm) (3) whileLoop_unroll)
        apply (auto simp add: succeeds_bind runs_to_partial_def_old split: xval_splits)
        done
      apply (auto simp: rel_XF_def rel_xval.simps)
      done
    subgoal
      by (auto simp add: rel_XF_def init_match pred_imply)
    subgoal
      by (auto simp add: rel_XF_def rel_xval.simps rel_exception_or_result.simps Exn_def default_option_def split: xval_splits )
    done
  done

lemma corresXF_name_pre:
  "\<lbrakk> \<And>s'. corresXF st ret ex (\<lambda>s. P s \<and> s = s') A C \<rbrakk> \<Longrightarrow>
           corresXF st ret ex P A C"
  by (clarsimp simp: corresXF_def)

lemma corresXF_guarded_while_body:
  "corresXF st ret ex P A B \<Longrightarrow>
      corresXF st ret ex P
             (do{ r \<leftarrow> A; _ \<leftarrow> guard (G r); return r }) B"
  apply (clarsimp simp add: corresXF_refines_iff)
  apply (clarsimp simp add: refines_def_old succeeds_bind reaches_bind)
  by (smt (verit) Exn_def case_exception_or_result_Exn case_exception_or_result_Result 
      default_option_def the_Exception_simp the_Exception_Result exception_or_result_cases 
      is_Exception_simps(1) is_Exception_simps(2) not_None_eq)

lemma whileLoop_succeeds_terminates_guard_body: 
  assumes B_succeeds: "\<And>i s. succeeds (B i) s \<Longrightarrow> succeeds (B' i) s"
  assumes B_reaches: "\<And>i s r t. reaches (B' i) s r t \<Longrightarrow> succeeds (B i) s \<Longrightarrow> reaches (B i) s r t"
  assumes termi: "run (whileLoop C B I) s \<noteq> \<top>"  
  shows "run (whileLoop C B' I) s \<noteq> \<top>" 
  using termi
proof (induct rule: whileLoop_ne_top_induct)
  case step show ?case unfolding top_post_state_def
    apply (rule whileLoop_ne_Failure)
    using step B_succeeds B_reaches
    apply (clarsimp simp add: runs_to_def_old)
    by (metis top_post_state_def)
qed

lemma whileLoop_succeeds_guard_body: 
  assumes B_succeeds: "\<And>i s. succeeds (B i) s \<Longrightarrow> succeeds (B' i) s"
  assumes B_reaches: "\<And>i s r t. reaches (B' i) s r t \<Longrightarrow> succeeds (B i) s \<Longrightarrow> reaches (B i) s r t"
  assumes termi: "succeeds (whileLoop C B I) s"  
  shows "succeeds (whileLoop C B' I) s"
  using whileLoop_succeeds_terminates_guard_body [OF B_succeeds B_reaches] termi
  by (auto simp: succeeds_def top_post_state_def)


lemma corresXF_guarded_while:
  assumes body_corres: "\<And>x y. corresXF st ret ex (\<lambda>s. P x s \<and> y = ret x s) (A y) (B x)"
  and cond_match: "\<And>s r. \<lbrakk> P r s; G (ret r s) (st s) \<rbrakk> \<Longrightarrow> C r s = C' (ret r s) (st s)"
  and pred_inv: "\<And>r s. P r s \<Longrightarrow> C r s \<Longrightarrow> succeeds (whileLoop C' A (ret r s)) (st s) \<Longrightarrow> G (ret r s) (st s) \<Longrightarrow>
                          B r \<bullet> s ?\<lbrace> \<lambda>r s. case r of Exn _ \<Rightarrow> True | Result r \<Rightarrow> G (ret r s) (st s) \<longrightarrow> P r s \<rbrace>"
  and pred_imply: "\<And>s. \<lbrakk> G y (st s); P' x s \<rbrakk> \<Longrightarrow> P x s"
  and init_match: "\<And>s. \<lbrakk> G y (st s); P' x s \<rbrakk> \<Longrightarrow> y = ret x s"
  shows "corresXF st ret ex (P' x)
      (do {
         _ \<leftarrow> guard (G y);
         whileLoop C' (\<lambda>i. (do {
            r \<leftarrow> A i;
            _ \<leftarrow> guard (G r);
            return r
          })) y
       })
      (whileLoop C B x)"
proof -

  {fix i s
    assume *: "succeeds (whileLoop C' (\<lambda>i.
                       (do { r \<leftarrow> A i;
                            _ \<leftarrow> guard (G r);
                            return r
                        })) i) s" 
    have "succeeds (whileLoop C' A i) s"
      apply (rule  whileLoop_succeeds_guard_body [OF _ _ *])
      subgoal by (auto simp add: succeeds_bind)

      subgoal apply (clarsimp simp add: reaches_bind succeeds_bind)
        by (smt (verit, best) dual_order.refl exception_or_result_split_asm le_boolD)
      done
  } note new_body_fails_more = this


  note new_body_corres = body_corres [THEN corresXF_guarded_while_body]

  show ?thesis
    apply (rule corresXF_exec_abs_guard)
    apply (rule corresXF_name_pre)
    apply (rule corresXF_assume_pre)
    apply clarsimp
    subgoal for s'
      apply (rule corresXF_guard_imp)
       apply (rule corresXF_while [where 
            P="\<lambda>x s. P x s \<and> G (ret x s) (st s)" and P'="\<lambda>x s. P' x s \<and> s = s'"])
           apply (rule corresXF_guard_imp)
            apply (rule new_body_corres)
           apply (clarsimp)
          apply (clarsimp)
          apply (rule cond_match, simp, simp)
      subgoal for r s 
        using pred_inv [of r s, OF _ _ new_body_fails_more ]
        apply clarsimp
        apply (subst (asm)  whileLoop_unroll)
        apply (clarsimp simp add: cond_match)
        apply (clarsimp simp add: succeeds_bind)
        apply (clarsimp simp add: runs_to_partial_def_old split: xval_splits, intro conjI)
         apply (metis (mono_tags, lifting) body_corres corresXF_exec_normal)
        using body_corres corresXF_exec_normal by fastforce
      subgoal
        using init_match by auto
      subgoal
        using init_match pred_imply by auto
      subgoal by auto
      done
    done
qed


(*

definition "corresXF st ret_xf ex_xf P A C \<equiv>
    \<forall>s. P s \<and> \<not> snd (A (st s)) \<longrightarrow>
        (\<forall>(r, t) \<in> fst (C s).
          case r of
             Inl r \<Rightarrow> (Inl (ex_xf r t), st t) \<in> fst (A (st s))
           | Inr r \<Rightarrow> (Inr (ret_xf r t), st t) \<in> fst (A (st s)))
        \<and> \<not> snd (C s)"*)


(* Merge of lemmas ccorresE and corresXF. *)
definition "ac_corres st check_termination AF \<Gamma> rx ex G \<equiv>
  \<lambda>A B. \<forall>s. (G s \<and> succeeds A (st s)) \<longrightarrow>
         (\<forall>t. \<Gamma> \<turnstile> \<langle>B, Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
             (case t of
               Normal s' \<Rightarrow> reaches A (st s) (Result (rx s')) (st s')
             | Abrupt s' \<Rightarrow> reaches A (st s) (Exn (ex s')) (st s')
             | Fault e \<Rightarrow> e \<in> AF
             | _ \<Rightarrow> False))
          \<and> (check_termination \<longrightarrow> \<Gamma> \<turnstile> B \<down> Normal s)"

(* We can merge ccorresE and corresXF to form a ccorresXF statement. *)
lemma ccorresE_corresXF_merge:
  "\<lbrakk> ccorresE st1 ct AF \<Gamma> \<top> G1 M B;
     corresXF st2 rx ex G2 A M;
     \<And>s. st s = st2 (st1 s);
     \<And>r s. rx' s = rx r (st1 s);
     \<And>r s. ex' s = ex r (st1 s);
     \<And>s. G s \<longrightarrow> (s \<in> G1 \<and> G2 (st1 s)) \<rbrakk> \<Longrightarrow>
    ac_corres st ct AF \<Gamma> rx' ex' G A B"
  apply (unfold ac_corres_def)
  apply clarsimp
  apply (clarsimp simp: ccorresE_def)
  apply (clarsimp simp: corresXF_def)
  apply (erule allE, erule impE, force)
  apply (erule allE, erule impE, force)
  apply clarsimp
  apply (erule allE, erule impE, fastforce)
  subgoal for s t by (cases t; fastforce)
  done


(* We can also merge corresXF statements. *)
lemma corresXF_corresXF_merge:
  "\<lbrakk> corresXF st rx ex P A B; corresXF st' rx' ex' P' B C \<rbrakk> \<Longrightarrow>
    corresXF (st o st') (\<lambda>rv s. rx (rx' rv s) (st' s))
             (\<lambda>rv s. ex (ex' rv s) (st' s)) (\<lambda>s. P' s \<and> P (st' s)) A C "
  apply (clarsimp simp: corresXF_def split: xval_splits)
  apply fastforce
  done

lemma ac_corres_guard_imp:
  "\<lbrakk> ac_corres st ct AF G rx ex P A C; \<And>s. P' s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> ac_corres st ct AF G rx ex P' A C"
  apply atomize
  apply (clarsimp simp: ac_corres_def)
  done

(*
 * Rules to use the corresXF definitions.
 *)

lemma corresXF_modify_local:
  "\<lbrakk> \<And>s. st s = st (M s); \<And>s. P s \<Longrightarrow> ret () (M s) = x \<rbrakk>
      \<Longrightarrow> corresXF st ret ex P (return x) (modify M)"
  by (auto simp add: corresXF_def)

lemma corresXF_modify_global:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> M (st s) = st (M' s) \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (modify M) (modify M')"
  by (auto simp add: corresXF_def)

lemma corresXF_select_modify:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> st s = st (M s); \<And>s. P s \<Longrightarrow> ret () (M s) \<in> x \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (select x) (modify M)"
  by (auto simp add: corresXF_def)

lemma corresXF_select_select:
  "\<lbrakk> \<And>s a. st s = st (M (a::('a \<Rightarrow> ('a::{type}))) s);
         \<And>s x. \<lbrakk> P s; x \<in> b\<rbrakk> \<Longrightarrow> ret x s \<in> a \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (select a) (select b)"
  by (auto simp add: corresXF_def)

lemma corresXF_modify_gets:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> st s = st (M s); \<And>s. P s \<Longrightarrow> ret () (M s) = f (st (M s)) \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (gets f) (modify M)"
  by (auto simp add: corresXF_def)


lemma corresXF_guard:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> G' s =  G (st s) \<rbrakk> \<Longrightarrow> corresXF st ret ex P (guard G) (guard G')"
  by (auto simp add: corresXF_def)

lemma corresXF_fail:
  "corresXF st return_xf exception_xf P fail X"
  by (auto simp add: corresXF_def)

lemma corresXF_spec:
  "\<lbrakk> \<And>s s'. ((s, s') \<in> A') = ((st s, st s') \<in> A); surj st \<rbrakk>
    \<Longrightarrow>  corresXF st ret ex P (state_select A) (state_select A')"
  apply (clarsimp simp add: corresXF_def)
  apply (frule_tac y=undefined in surjD)
  apply (clarsimp simp: image_def set_eq_UNIV)
  apply metis
  done

lemma corresXF_throw:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> E B s = A \<rbrakk> \<Longrightarrow> corresXF st V E P (throw A) (throw B)"
  by (auto simp add: corresXF_def Exn_def)


lemma corresXF_append_gets_abs:
  assumes corres: "corresXF st ret ex P L R"
  and consistent: "\<And>s. P s \<Longrightarrow> R \<bullet> s ?\<lbrace>\<lambda>r s. case r of Exn _ \<Rightarrow> \<top> | Result v \<Rightarrow> M (ret v s) (st s) = ret' v s \<rbrace>"
shows "corresXF st ret' ex P (L >>= (\<lambda>r. gets (M r))) R"
  using corres consistent
  apply (clarsimp simp add: corresXF_refines_iff runs_to_partial_def_old refines_def_old 
      succeeds_bind reaches_bind rel_XF_def rel_xval.simps split: xval_splits )
  using Exn_def by force

lemma corresXF_skipE:
  "corresXF st ret ex P skip skip"
  by (auto simp add: corresXF_def Exn_def)


lemma corresXF_id:
    "corresXF id (\<lambda>r s. r) (\<lambda>r s. r) P M M"
  by (fastforce simp: corresXF_def split: xval_splits)

lemma corresXF_cong:
  "\<lbrakk> \<And>s. st s = st' s;
     \<And>s r. ret_xf r s = ret_xf' r s;
     \<And>s r. ex_xf r s = ex_xf' r s;
     \<And>s. P s = P' s;
     \<And>s s'. P' s' \<Longrightarrow> run A s = run A' s;
     \<And>s. P' s \<Longrightarrow> run C s = run C' s \<rbrakk> \<Longrightarrow>
           corresXF st ret_xf ex_xf P A C = corresXF st' ret_xf' ex_xf' P' A' C'"
   apply atomize
   apply (auto simp: corresXF_def reaches_def succeeds_def split: xval_splits)
   done

lemma corresXF_exec_abs_select:
  "\<lbrakk> x \<in> Q; x \<in> Q \<Longrightarrow> corresXF id rx ex P (A x) A' \<rbrakk> \<Longrightarrow> corresXF id rx ex P (select Q >>= A) A'"
  by (fastforce simp add: corresXF_def succeeds_bind reaches_bind split: xval_splits)

end
