(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Top-level AutoCorres theorem.
 *)

theory AutoCorres
  imports
    LocalVarExtract
    AutoCorresSimpset
    Polish
    Runs_To_VCG_StackPointer

keywords
  "autocorres"
  "init-autocorres"
  "final-autocorres":: thy_decl and
  "declare_prototype":: thy_goal_stmt
begin

unbundle no c_parser_separation_logic
unbundle no c_parser_separation_logic_more


no_syntax  "_Lab":: "'a bexp \<Rightarrow> ('a,'p,'f) com \<Rightarrow> bdy"
            (\<open>_\<bullet>/_\<close> [1000,71] 81) \<comment> \<open>avoid syntax conflict with \<^term>\<open>runs_to f s Q\<close>\<close>

lemma Eq_TrueD: "(P \<equiv> True) \<Longrightarrow> P"
  by blast

(* Remove various rules from the default simpset that don't really help. *)
declare word_neq_0_conv [simp del]
declare neq0_conv [simp del]
declare fun_upd_apply[simp del]
declare fun_upd_same [simp add]
lemma o_const_simp[simp]: "(\<lambda>x. C) \<circ> f = (\<lambda>x. C)"
  by (simp add: o_def)

(* Machinery for generating final corres thm *)
lemma corresTA_trivial: "corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  apply (auto intro: corresXF_I simp add: corresTA_def)
  done

lemma L2Tcorres_trivial_from_in_out_parameters:
  "IOcorres P Q st rx ex A C \<Longrightarrow> L2Tcorres id A A"
  by (rule L2Tcorres_id)

(* Dummy preconditions for more convenient usage *)
lemma L2Tcorres_trivial_from_local_var_extract:
  "L2corres st rx ex P A C \<Longrightarrow> L2Tcorres id A A"
  by (rule L2Tcorres_id)

lemma corresTA_trivial_from_heap_lift:
  "L2Tcorres st A C \<Longrightarrow> corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  by (rule corresTA_trivial)


lemma corresXF_from_L2_call:
  "L2_call c_WA emb ns = A \<Longrightarrow> corresXF (\<lambda>s. s) (\<lambda>rv s. rv) (\<lambda>r t. emb r) (\<lambda>_. True) A c_WA"
  unfolding L2_call_def corresXF_refines_conv
  apply (auto simp add: refines_def_old reaches_map_value map_exn_def split: xval_splits)[1]
  by (metis (lifting) Result_neq_Exn map_exn_simps(1)[of emb] map_exn_simps(2)[of undefined])

definition "ac_corres' exn st check_termination AF \<Gamma> rx ex G \<equiv>
  \<lambda>A B. \<forall>s. (G s \<and> succeeds A (st s)) \<longrightarrow>
         (\<forall>t. \<Gamma> \<turnstile> \<langle>B, Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
             (case t of
               Normal s' \<Rightarrow> (Result (rx s'), st s') \<in> outcomes (run A (st s))
             | Abrupt s' \<Rightarrow> (exn (ex s'), st s') \<in> outcomes (run A (st s))
             | Fault e \<Rightarrow> e \<in> AF
             | _ \<Rightarrow> False))
          \<and> (check_termination \<longrightarrow> \<Gamma> \<turnstile> B \<down> Normal s)"

lemma ac_corres'_nd_monad:
  assumes ac: "ac_corres st check_termination AF \<Gamma> rx ex G B C"
  assumes refines: "\<And>s. refines B A s s (rel_prod rel_liftE (=))"
  shows "ac_corres' (\<lambda>_. Exception (default::unit)) st check_termination AF \<Gamma> rx ex G A C"
  apply (simp add: ac_corres'_def)[1]
  apply (intro conjI allI impI)
  subgoal
    using assms
    apply (auto simp add:   ac_corres_def refines_def_old split: xstate.splits) [1]
     apply (metis reaches_def rel_liftE_Result_Result_iff)
    by (metis Exn_neq_Result rel_liftE_def)
  apply (elim conjE)
  subgoal premises prems for s
  proof -
    from refines [simplified refines_def_old, rule_format, OF prems (3)] have "succeeds B (st s)" by blast
    with prems(2) have "G s \<and> succeeds B (st s)"
      by (auto simp add: succeeds_def)
    from ac [simplified ac_corres_def, rule_format, OF this] prems(1)
    show ?thesis
      by blast
  qed
  done

lemma refines_spec_rel_Nonlocal_conv: 
  shows "refines f g s t (rel_prod (rel_xval rel_Nonlocal (=)) (=))
   \<longleftrightarrow> refines f (map_value (map_exn Nonlocal) g) s t (rel_prod (=) (=))"
  apply (simp add: refines_def_old reaches_map_value rel_xval.simps map_exn_def
       split: xval_splits)
  apply (intro iffI)
   apply (metis Exn_eq_Exn Result_eq_Result Result_neq_Exn rel_Nonlocal_conv)
  apply (simp add: rel_Nonlocal_def)
  apply clarsimp
  subgoal for r s
    apply (erule_tac x=r in allE)
    apply (erule_tac x=s in allE)
    by (smt (verit, best) Exn_def c_exntype.case(5) default_option_def 
        exception_or_result_cases not_Some_eq)
  done

lemmas refines_eq_convs = refines_spec_rel_Nonlocal_conv sum.rel_eq rel_xval_eq Relation.eq_OO

lemma ac_corres'_exception_monad:
  assumes ac: "ac_corres st check_termination AF \<Gamma> rx ex G B C"
  assumes refines: "\<And>s. refines B A s s (rel_prod (=) (=))"
  shows "ac_corres' Exn st check_termination AF \<Gamma> rx ex G A  C"
  term "map_value (map_exn Nonlocal) A"
  apply (simp add: ac_corres'_def, intro allI impI conjI)
  subgoal
    using assms
    by (auto simp add: refines_def_old reaches_map_value ac_corres_def  
        map_exn_def rel_sum.simps rel_Nonlocal_def split: xstate.splits c_exntype.splits)
      (metis reaches_def)+
  apply (elim conjE)
  subgoal premises prems for s
  proof -
    from refines [simplified refines_def_old, rule_format, OF prems (3)] have "succeeds B (st s)" by blast
    with prems(2) have "G s \<and> succeeds B (st s)"
      by (auto simp add: succeeds_def)
    from ac [simplified ac_corres_def, rule_format, OF this] prems(1)
    show ?thesis
      by blast
  qed
  done

lemma ac_corres_chain:
"\<lbrakk> L1corres check_termination Gamma c_L1 c;
   L2corres st_L2 rx_L2 ex_L2 P_L2 c_L2 c_L1;
   L2Tcorres st_HL c_HL c_L2;
   corresTA P_WA rx_WA ex_WA c_WA c_HL;
   L2_call c_WA emb ns = A
 \<rbrakk> \<Longrightarrow>
  ac_corres (st_HL o st_L2) check_termination {AssumeError, StackOverflow} Gamma (rx_WA o rx_L2) (emb o ex_WA o ex_L2) (P_L2 and (P_WA o st_HL o st_L2)) A c"

  apply (rule ccorresE_corresXF_merge)
       apply (unfold L1corres_alt_def)
       apply assumption
      apply (unfold L2corres_def L2Tcorres_def corresTA_def)
      apply (drule corresXF_from_L2_call)

      apply ((drule (1) corresXF_corresXF_merge)+, assumption)
     apply (clarsimp simp: L2_call_def L2_defs)

     apply simp
    apply clarsimp
   apply clarsimp
  done

lemma ac_corres_chain_sim_nd_monad:
"\<lbrakk> L1corres check_termination Gamma c_L1 c;
   L2corres st_L2 rx_L2 ex_L2 P_L2 c_L2 c_L1;
   IOcorres P_IO Q_IO st_IO rx_IO ex_IO c_IO c_L2;
   L2Tcorres st_HL c_HL c_IO;
   corresTA P_WA rx_WA ex_WA c_WA c_HL;
   \<And>s. refines c_WA A s s (rel_prod rel_liftE (=))
 \<rbrakk> \<Longrightarrow>
  ac_corres'  (\<lambda>_. Exception (default::unit)) (st_HL o st_IO o st_L2) check_termination {AssumeError, StackOverflow} Gamma 
    (\<lambda>s. (rx_WA o (\<lambda>v. rx_IO v (st_L2 s)) o rx_L2) s) 
    (\<lambda>s. (ex_WA o (\<lambda>e. ex_IO e (st_L2 s)) o ex_L2) s) 
    (P_L2 and (P_IO o st_L2) and (P_WA o st_HL o st_IO o st_L2)) A c"
  apply (rule ac_corres'_nd_monad)
  apply (rule ccorresE_corresXF_merge)
       apply (unfold L1corres_alt_def)
       apply assumption
      apply (unfold L2corres_def L2Tcorres_def corresTA_def IOcorres_def)
       apply (drule corresXF_post_to_corresXF)
       apply ((drule (1) corresXF_corresXF_merge)+, assumption)
      apply (clarsimp simp: L2_call_def L2_defs)
     apply simp
    apply clarsimp
   apply clarsimp
  apply assumption
  done

lemma ac_corres_chain_sim_exception_monad:
"\<lbrakk> L1corres check_termination Gamma c_L1 c;
   L2corres st_L2 rx_L2 ex_L2 P_L2 c_L2 c_L1;
   IOcorres P_IO Q_IO st_IO rx_IO ex_IO c_IO c_L2;
   L2Tcorres st_HL c_HL c_IO;
   corresTA P_WA rx_WA ex_WA c_WA c_HL;
   \<And>s. refines c_WA A s s (rel_prod (=) (=))
 \<rbrakk> \<Longrightarrow>
  ac_corres' Exn (st_HL o st_IO o st_L2) check_termination {AssumeError, StackOverflow} Gamma 
    (\<lambda>s. (rx_WA o (\<lambda>v. rx_IO v (st_L2 s)) o rx_L2) s) 
    (\<lambda>s. (ex_WA o (\<lambda>e. ex_IO e (st_L2 s)) o ex_L2) s) 
    (P_L2 and (P_IO o st_L2) and (P_WA o st_HL o st_IO o st_L2)) A c"
  apply (rule ac_corres'_exception_monad)
  apply (rule ccorresE_corresXF_merge)
       apply (unfold L1corres_alt_def)
       apply assumption
      apply (unfold L2corres_def L2Tcorres_def corresTA_def IOcorres_def)
       apply (drule corresXF_post_to_corresXF)
       apply ((drule (1) corresXF_corresXF_merge)+, assumption)
      apply (clarsimp simp: L2_call_def L2_defs)
     apply simp
    apply clarsimp
   apply clarsimp
  apply assumption
  done

lemmas ac_corres_chain_sims = ac_corres_chain_sim_nd_monad ac_corres_chain_sim_exception_monad



(*
 * Functions that don't have a body in the C file (i.e., they are
 * prototyped and called, but are never defined) will be abstracted
 * into a "fail" command by AutoCorres.
 *
 * More accurately, they will be abstracted into:
 *
 *     guard (\<lambda>s. INVALID_FUNCTION)
 *
 * where "INVALID_FUNCTION" is "False").
 *
 * We convert this above form into this alternative definition, so
 * users have a better idea what is going on.
 *)
definition "FUNCTION_BODY_NOT_IN_INPUT_C_FILE \<equiv> fail"
definition "OFUNCTION_BODY_NOT_IN_INPUT_C_FILE \<equiv> ofail"

lemma FUNCTION_BODY_NOT_IN_INPUT_C_FILE[polish]:
  "guard (\<lambda>s. UNDEFINED_FUNCTION) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "(FUNCTION_BODY_NOT_IN_INPUT_C_FILE >>= m) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "unknown >>= (\<lambda>x. FUNCTION_BODY_NOT_IN_INPUT_C_FILE) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "liftE FUNCTION_BODY_NOT_IN_INPUT_C_FILE = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (rule spec_monad_ext, 
      simp add: run_bind run_guard UNDEFINED_FUNCTION_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def)+

lemma OFUNCTION_BODY_NOT_IN_INPUT_C_FILE[polish]:
  "do {
    oguard (\<lambda>_. UNDEFINED_FUNCTION);
    oreturn undefined
  } = OFUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  unfolding UNDEFINED_FUNCTION_def OFUNCTION_BODY_NOT_IN_INPUT_C_FILE_def
  by simp_all
(* Rewrites that will be applied before collecting statistics. *)
lemmas ac_statistics_rewrites =
    (* Setup "L1_seq" to have a sane lines-of-spec measurement. *)
    L1_seq_def
    (* Convert L2 to standard exception monads. *)
    L2_defs'




text \<open>There might be unexpected simplification \<^emph>\<open>unfolding\<close> of @{const id} due to eta-expansion:
@{term id} might be expanded (e.g. by resolution to ) @{term "\<lambda>x. id x"}. Now the
simp rule @{thm id_apply} triggers and rewrites it @{term "\<lambda>x. x"}. Folding this back to
@{term id} might help in those cases.
\<close>


named_theorems
  l1_corres and l2_corres and io_corres and hl_corres and wa_corres and ts_corres and ac_corres and
  \<P>_defs and final_defs and
  l1_def and l2_def and io_def and hl_def and wa_def and ts_def and ac_def and no_throw

named_theorems
  sel_frame_thms and upd_frame_commutes

named_theorems
  heap_update_syntax

lemma fold_id: "(\<lambda>x. x) = id"
  by (simp add: id_def)

lemma fold_id_unit: " (\<lambda>_. ()) = id"
  by (simp add: id_def)

lemma transp_fun_ord: "transp X \<Longrightarrow> transp (fun_ord X)"
  by (force simp add: fun_ord_def transp_def)

lemma transp_flat_ord_option: "transp (flat_ord None)"
  by (rule option.transp_le)

lemma fun_ord_transp:
  shows "fun_ord X f g \<Longrightarrow> transp X \<Longrightarrow> fun_ord X g h \<Longrightarrow> fun_ord X f h"
  by (force simp add: fun_ord_def transp_def)

lemma antisymp_fun_ord: "antisymp X \<Longrightarrow> antisymp (fun_ord X)"
  by (auto simp add: antisymp_def fun_ord_def)

lemma antisymp_flat_ord_option: "antisymp (flat_ord None)"
  by (auto simp add: antisymp_def flat_ord_def)

lemma fun_ord_antisymp: "fun_ord X f g \<Longrightarrow> fun_ord X g f \<Longrightarrow> antisymp X \<Longrightarrow> f = g"
  by (auto simp add: fun_ord_def antisymp_def)

lemma admissible_subst_fun_lub_fun_ord: 
  "ccpo.admissible lub le X \<Longrightarrow> mcont (fun_lub lub) (fun_ord le) lub le F \<Longrightarrow> 
  ccpo.admissible (fun_lub lub) (fun_ord le) (\<lambda>x. X (F x))"
  by (rule admissible_subst)

declare ccpo.ccpo_fun[corres_admissible] 
  ccpo_Inf[corres_admissible] 
  ccpo_Sup[corres_admissible]

lemma admissible_option_le_fun1[corres_admissible]: "option.admissible (option.le_fun f)"
  apply (rule ccpo.admissibleI)
  by (smt (verit, ccfv_threshold) equals0I flat_interpretation 
      partial_function_definitions_def partial_function_lift)

lemma admissible_option_le_fun2[corres_admissible]: "option.admissible (\<lambda>f. option.le_fun f g)"
  apply (rule ccpo.admissibleI)
  by (smt (verit, ccfv_threshold) equals0I flat_interpretation 
      partial_function_definitions_def partial_function_lift)

lemma admissible_refines_spec_right[corres_admissible]:
  shows "ccpo.admissible Inf (\<ge>)
           (\<lambda>(A::('e::default, 'a, 's) spec_monad) . refines C A s t (=))"
  apply (subst prod.rel_eq[symmetric])
  by (rule admissible_refines_spec_funp) (intro funp_intros)

lemma admissible_refines_spec_left[corres_admissible]:
  shows "ccpo.admissible Inf (\<ge>)
           (\<lambda>(C::('e::default, 'a, 's) spec_monad) . refines C A s t (=))"
  by (smt (verit, ccfv_SIG) Inf_le_Sup ccpo.admissible_def le_refines_trans refines_Sup1)

lemma (in complete_lattice) admissible_gfp_le_right [corres_admissible]:
  "ccpo.admissible Inf (\<ge>) (\<lambda>x. (y \<le> x))"
  by (simp add: ccpo.admissibleI Inf_greatest)
lemma (in complete_lattice) admissible_gfp_le_left [corres_admissible]:
  "ccpo.admissible Inf (\<ge>) (\<lambda>y. (y \<le> x))"
  by (simp add: ccpo.admissibleI Inf_less_eq)

lemma admissible_fun_ord[corres_admissible]: 
"(\<And>x. ccpo.admissible lub le (\<lambda>f. X (f x) (g x))) \<Longrightarrow> ccpo.admissible lub le (\<lambda>f. fun_ord X f g)"
  by (simp add: fun_ord_def admissible_all)

lemma option_le_obind[monad_mono_intros]: "(\<And>x. option.le_fun (f2 x) (g2 x)) \<Longrightarrow> option.le_fun f1 g1 \<Longrightarrow> 
  option.le_fun (f1 |>> f2) (g1 |>> g2) "
  supply [[show_abbrevs=false]]
  thm flat_ord_def fun_ord_def
  apply (simp add: obind_def )
  by (smt (verit, best) flat_ord_def fun_ord_def option.case_eq_if)

lemma option_le_ocondition[monad_mono_intros]: 
  "option.le_fun f1 g1 \<Longrightarrow> option.le_fun f2 g2 \<Longrightarrow> option.le_fun (ocondition c f1 f2) (ocondition c g1 g2)"
  by (auto simp add: ocondition_def fun_ord_def)



lemma option_while'_le: 
    assumes bdy: "option.le_fun b2 b1"
  assumes while: "(so, s') \<in> option_while' c b1"
  shows "\<exists>s1. (so, s1) \<in> option_while' c b2 \<and> option_ord s1 s'"
  supply [[show_abbrevs=false]]
  thm bdy
  using while
proof (induct)
  case (final r)
  then show ?case
    by (meson option.leq_refl option_while'.final)
 
next
  case (fail r)
  show ?case
  proof (cases "b2 r")
    case None
    then show ?thesis using fail 
      by (meson flat_ordI option_while'.fail)  
  next
    case (Some x)

    with fail bdy
    have False
      apply (auto simp add: flat_ord_def fun_ord_def)
     
      by (metis option.distinct(1))
    thus ?thesis
      ..
  qed
next
  case (step r r' sr'')
  then show ?case using bdy
    by (metis (no_types, lifting) flat_ord_def fun_ord_def option_while'.simps)
qed


lemma option_le_refl[monad_mono_intros]: "option.le_fun f f"
  by (auto simp add: fun_ord_def flat_ord_def)

lemma option_le_owhile [monad_mono_intros]:"(\<And>x. option.le_fun (b1 x) (b2 x)) \<Longrightarrow> option.le_fun (owhile c b1 i) (owhile c b2 i)"
  apply (auto simp add: owhile_def option_while_def fun_ord_def )
  subgoal for x s s'
    using option_while'_le
    by (smt (verit, ccfv_threshold) fun_ord_def option_while'_inj theI_unique)
  subgoal for x s
    using option_while'_le
    by (smt (verit, ccfv_threshold) option.leq_refl option_while'_monotone the_equality)
  subgoal for x s
    by (simp add: flat_ord_def)
  subgoal for x
    by (simp add: flat_ord_def)
  done

lemma option_le_fun_trans: "option.le_fun f g \<Longrightarrow> option.le_fun g h \<Longrightarrow> option.le_fun f h"
  by (metis option.partial_function_definitions_axioms 
      partial_function_definitions.leq_trans partial_function_lift)

declare order.refl [monad_mono_intros]

lemma le_gets_the[monad_mono_intros]: "option.le_fun g f \<Longrightarrow> gets_the f \<le> gets_the g"
  by (smt (verit, best) flat_ord_def fun_ord_def not_Some_eq runs_to_gets_the_iff spec_monad_le_iff)

lemma map_of_default_pointless_eq: 
  "map_of_default d xs p x1 = map_of_default (\<lambda>p. (d p x1)) (map (\<lambda>(x, f). (x, f x1)) xs) p "
  by (induct xs) auto

lemma map_of_default_list_all_cases:
  assumes P_xs: "list_all (\<lambda>(p, f). P p f) xs"
  assumes P_d: "p \<notin> set (map fst xs) \<Longrightarrow> P p (d p)"
  shows "P p (map_of_default d xs p)"
  using P_xs P_d proof (induct xs arbitrary: d)
  case Nil
  then show ?case by auto
next
  case (Cons x1 xs)
  then show ?case by auto
qed

lemma list_all_prod_nil: "list_all (\<lambda>(p, v). P p v) []" by (rule list_all_nil)

lemma list_all_prod_cons: 
  assumes "list_all (\<lambda>(p, v). P p v) xs"
  assumes "P p v"
  shows "list_all (\<lambda>(p, v). P p v) ((p, v)#xs)" 
  using list_all_cons assms by auto

lemma map_of_default_both_nil:
  assumes P_d: "P (d1 p) (d2 p)"
  shows "P (map_of_default d1 [] p) (map_of_default d2 [] p)"
  using assms
  by auto 

lemma map_of_default_both_cons:
  assumes "P (map_of_default d1 xs p) (map_of_default d2 ys p)"
  assumes P_d: "P v1 v2"
  shows "P (map_of_default d1 ((x, v1)#xs) p) (map_of_default d2 ((x, v2)#ys) p)"
  using assms
  by auto


lemma map_of_default_list_all2_cases:
  assumes P_xs: "list_all2 (\<lambda>(p, f) (p', f'). p = p' \<and> P f f') xs ys"
  assumes P_d: "p \<notin> set (map fst xs) \<Longrightarrow> P (d p) (d' p)"
  shows "P (map_of_default d xs p) (map_of_default d' ys p)"
  using P_xs P_d proof (induct xs arbitrary: d d' ys p)
  case Nil
  then show ?case by auto
next
  case (Cons x1 xs)
  then show ?case by (cases ys) auto
qed

lemma list_all2_prod_nil: "list_all2 (\<lambda>(p, v) (p', v'). P p v p' v') [] []"
  by auto

lemma list_all2_prod_cons:
  assumes "list_all2 (\<lambda>(p, v) (p', v'). P p v p' v') xs ys"
  assumes "P p v p' v'"
  shows "list_all2 (\<lambda>(p, v) (p', v'). P p v p' v') ((p,v)#xs) ((p',v')#ys)"
  using assms
  by auto



lemma map_of_default_cons_condition:
  "map_of_default d ((q, f)#fs) p = condition (\<lambda>_. q = p) f (map_of_default d fs p)"
  by simp

lemma map_of_default_cons_ocondition:
  "map_of_default d ((q, f)#fs) p = ocondition (\<lambda>_. q = p) f (map_of_default d fs p)"
  by simp

lemma map_of_default_cons_L2_condition:
  "map_of_default d ((q, f)#fs) p = L2_condition (\<lambda>_. FUN_PTR (q = p)) f (map_of_default d fs p)"
  by (simp add: FUN_PTR_def)


lemma L2_call_map_of_default_commute: 
  "L2_call (map_of_default d fs p) emb ns = 
    map_of_default (\<lambda>p. L2_call (d p) emb ns) (map (apsnd (\<lambda>f. L2_call f emb ns)) fs) p"
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons f1 fs)
  then show ?case
    by (cases f1) simp
qed

lemma L2_call_map_of_default2_commute: 
  "L2_call (map_of_default d fs p x1 x2) emb ns = 
    map_of_default (\<lambda>p. L2_call (d p x1 x2) emb ns) (map (apsnd (\<lambda>f. L2_call (f x1 x2) emb ns)) fs) p"
  by (induct fs) auto





lemmas map_of_default_L2_commutes = 
  map_of_default_cons_L2_condition 
  map_of_default.simps(1)
  L2_call_map_of_default_commute
  L2_call_map_of_default2_commute
  list.map apsnd_conv

named_theorems L2_call_map_of_default_commutes

lemma  "\<top> x \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp only: runs_to_partial_top top_apply)

ML \<open>

structure map_of_default_args =
struct
fun dest_map_of_default t =
  case strip_comb t of
    (map_of_default as @{term_pat "map_of_default"}, (d:: fs :: p :: args)) => {d = d, fs = fs, p = p, args = args, map_of_default = map_of_default}
  | _ =>  raise TERM ("dest_map_of_default", [t])

fun dest_L2_call @{term_pat \<open>L2_call ?f ?emb ?ns\<close>} = {f = f, emb = emb, ns = ns}
  | dest_L2_call t = raise TERM ("dest_L2_call", [t])
 
fun dest_assoc ps = HOLogic.dest_list ps |> map (HOLogic.dest_prod)

fun dest_runs_to_partial @{term_pat \<open>runs_to_partial ?f ?s ?Q\<close>} = {f = f, s = s, Q = Q}
  | dest_runs_to_partial t = raise TERM ("dest_runs_to_partial", [t])

val dummyfy_consts = Term.map_aterms (fn Const (x,_) => Const (x, dummyT) | _ => raise Same.SAME)
fun mk_pair x y = Const (@{const_name Product_Type.Pair}, dummyT) $ x $ y
fun mk_cons x xs = Const (@{const_name list.Cons}, dummyT) $ x $ xs
val mk_nil = Const (@{const_name list.Nil}, dummyT)
fun C name = Const (name, dummyT)
fun F name = Free (name, dummyT)
val d = F "d"
val p = F "p"
val q = F "q"
val Q = F "Q"
val s = F "s"
val f = F "f"
val fs = F "fs"
val emb = F "emb"
val ns = F "ns"
fun x n = F ("x" ^ string_of_int n)
fun xs n = map x (1 upto n)
fun eq x y = C @{const_name HOL.eq} $ x $ y
fun neq x y = \<^Const>\<open>Not\<close> $ eq x y
val top = Const (@{const_name top}, dummyT)

fun map_of_default d fs p args =
  list_comb (C @{const_name map_of_default} $ d $ fs $ p, args)

fun runs_to_partial f s Q = C @{const_name runs_to_partial} $ f $ s $ Q
fun runs_to f s Q = C @{const_name runs_to} $ f $ s $ Q

fun runs_to_empty_prop runs_to args =
  let
    val assm = HOLogic.Trueprop $ runs_to (list_comb (d, p::args)) s Q
    val concl = HOLogic.Trueprop $ runs_to (map_of_default d mk_nil p args) s Q 
  in
    Logic.list_implies ([assm], concl)
  end

fun runs_to_cons_prop runs_to args =
  let
    val asm1 = Logic.mk_implies (HOLogic.Trueprop $ eq p q, 
      HOLogic.Trueprop $ runs_to (list_comb (f, args)) s Q)
    val asm2 = Logic.mk_implies (HOLogic.Trueprop $ neq p q, 
      HOLogic.Trueprop $ runs_to (map_of_default d fs p args) s Q)
    val concl = HOLogic.Trueprop $ runs_to (map_of_default d (mk_cons (mk_pair q f) fs) p args) s Q
  in
    Logic.list_implies ([asm1, asm2], concl)
  end

fun runs_to_partial_top_prop args =
  HOLogic.Trueprop $ runs_to_partial (list_comb (top, p::args)) s Q

fun mk_L2_call_map_of_default_commute_thm n =
  let
    val ctxt0 = @{context}
    val lhs = C @{const_name L2_call} $ map_of_default d fs p (xs n) $ emb $ ns
    val rhs = 
          map_of_default 
            (Abs ("p", dummyT, C @{const_name L2_call} $ (list_comb (d, (Bound 0::xs n))) $ emb $ ns))
            (C @{const_name map} $ 
              (C @{const_name apsnd} $ 
                 (Abs ("f", dummyT, C @{const_name L2_call} $ (list_comb (Bound 0,xs n)) $ emb $ ns))) $ 
              fs)
            p
            []
    val prop0 = HOLogic.Trueprop $ eq lhs rhs 
    val prop = prop0 |> Utils.infer_types_simple ctxt0
    val fs_typed = prop |> Utils.lhs_of_eq |> dest_L2_call |> #f |> dest_map_of_default |> #fs
    val thm = Goal.prove ctxt0 [] [] prop (fn {context=ctxt, ...} =>  (
      Induct.induct_tac ctxt false [[SOME (SOME (Binding.make ("fs", \<^here>)), (fs_typed, true))]] [] [] NONE [] THEN_ALL_NEW
      asm_full_simp_tac ctxt) 1 )
  in
    thm |> Drule.export_without_context
  end

fun mk_map_of_default_runs_to_thms n =
  let
    val ctxt0 = @{context}
    val args = xs n 
    val props0 = [
      runs_to_empty_prop runs_to_partial args, 
      runs_to_cons_prop runs_to_partial args,
      runs_to_partial_top_prop args,
      runs_to_empty_prop runs_to args, 
      runs_to_cons_prop runs_to args]
    val props = props0 |> map (Utils.infer_types_simple ctxt0)
    fun prove prop = Goal.prove ctxt0 [] [] prop (fn {context = ctxt, ...} => 
      asm_full_simp_tac ctxt 1)
    val thms = map prove props
  in
    thms |> map Drule.export_without_context
  end
fun L2_call_map_of_default_commutes_arity thm =
  let
    val n = thm |> Thm.concl_of |> Utils.lhs_of_eq |> dest_L2_call |> #f 
      |> dest_map_of_default |> #args |> length
  in SOME n end
  handle TERM _ => NONE

fun runs_to_partial_map_of_default_arity thm =
  let
    val n = thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_runs_to_partial |> #f 
      |> dest_map_of_default |> #args |> length
  in SOME n end
  handle TERM _ => NONE

fun note_L2_call_map_of_default_commutes name thms =
  Local_Theory.note ((Binding.make (name, \<^here>), @{attributes [L2_call_map_of_default_commutes]}), thms)

fun ensure_L2_call_map_of_default_commutes_upto n lthy =
  let
    val existing_arities = Named_Theorems.get lthy @{named_theorems L2_call_map_of_default_commutes}
      |> map_filter L2_call_map_of_default_commutes_arity
    val target_arities = 0 upto n
    val missing_arities = target_arities |> (filter_out (member (op =) existing_arities))
    val thms = map mk_L2_call_map_of_default_commute_thm missing_arities
  in
    if null thms then lthy
    else snd (Local_Theory.note 
      ((Binding.new_pos \<^here> Binding.empty, @{attributes [L2_call_map_of_default_commutes]}), thms) lthy)
  end

fun ensure_runs_to_partial_map_of_default_upto n lthy =
  let
    val existing_arities = Named_Rules.get lthy @{named_rules runs_to_vcg}
      |> map_filter runs_to_partial_map_of_default_arity
    val target_arities = 0 upto n
    val missing_arities = target_arities |> (filter_out (member (op =) existing_arities))
    val thms = maps mk_map_of_default_runs_to_thms missing_arities
  in
    if null thms then lthy
    else snd (Local_Theory.note 
      ((Binding.new_pos \<^here> Binding.empty, @{attributes [runs_to_vcg]}), thms) lthy)
  end

fun dest_prod ct = ct |> Match_Cterm.switch [
  @{cterm_match "(?key, ?value)"} #> (fn {key, value, ...} => {key=key, value=value})]

fun dest_list ct = ct |> Match_Cterm.switch [
  @{cterm_match "[]"} #> (fn _ => []),
  @{cterm_match "(?x#?xs)"} #> (fn {x, xs, ...} => x::dest_list xs)]

val dest_assoc_cterm = dest_list #> map dest_prod
val strip_assoc = dest_assoc_cterm #> map (fn {key, value} => (key, Utils.strip_comb_cterm value))

fun mk_prod (key, value) =
   \<^instantiate>\<open>
     key=key and 'a=\<open>Thm.ctyp_of_cterm key\<close> and 
     value=value and 'b=\<open>Thm.ctyp_of_cterm value\<close> 
   in cterm \<open>(key, value)\<close>\<close>

fun mk_nonempty_list [x] = \<^instantiate>\<open>x=x and 'a = \<open>Thm.ctyp_of_cterm x\<close> in cterm \<open>[x]\<close>\<close>
  | mk_nonempty_list (x::xs) = 
      let 
        val xs' = mk_nonempty_list xs 
      in \<^instantiate>\<open>x=x and xs=xs' and 'a = \<open>Thm.ctyp_of_cterm x\<close> in cterm \<open>x#xs\<close>\<close> end

fun strip_args_default args ct =
  if null args then ct
  else 
    let
      val (head, current_args) = Utils.strip_comb_cterm ct
    in
      if null current_args then 
         head |> fold_rev Thm.lambda args 
      else 
        let
          val n = length current_args
          val (prefix, suffix) = chop (n - length args) current_args
        in 
          if n = length args andalso forall (is_equal o Thm.fast_term_ord) (args ~~ suffix) then 
             head |> fold Thm.apply prefix 
          else raise Match end
    end

fun fold_top_conv ctxt =
  let
    val simp_ctxt1 = Simplifier.clear_simpset ctxt addsimps @{thms top_fun_def}
    val simp_ctxt2 = Simplifier.clear_simpset ctxt addsimps @{thms top_fun_def[symmetric]}
  in
     Simplifier.rewrite simp_ctxt1 then_conv Simplifier.rewrite simp_ctxt2
  end 

fun rename_dummy_abs (Abs (x, T, b)) =
    let
      val b' = rename_dummy_abs b
      val x' = if Term.is_dependent b then x else Name.uu_
    in Abs (x', T, b') end
  | rename_dummy_abs t = t

fun rename_dummy_abs_cterm ct =
  let
    val t = rename_dummy_abs (Thm.term_of ct)
  in Thm.renamed_term t ct end
end

\<close>


local_setup \<open>
  map_of_default_args.ensure_L2_call_map_of_default_commutes_upto 11 #> 
  map_of_default_args.ensure_runs_to_partial_map_of_default_upto 11
\<close>

thm runs_to_vcg
thm map_of_default.simps
thm map_of_default_cons_condition
thm map_of_default_cons_ocondition
thm L2_call_map_of_default_commutes
(* FIXME: remove should be subsumed by next simproc *)
simproc_setup passive map_of_default_args_conv (\<open>map_of_default d fs p\<close>) = \<open>
let
  open map_of_default_args
  val basic_ss = Simplifier.simpset_of @{context}
  fun is_funT ct = ct |> Thm.typ_of_cterm |> try dest_funT |> is_some
in
  K (fn ctxt => fn ct => 
  let
    val {fs, d, p, ...} = @{cterm_match "map_of_default ?d ?fs ?p"} ct
    val (keys, values) = strip_assoc fs |> split_list
    val _ = if null values then raise Match else ()
    val argss = map snd values
    val argns = map length argss
    val arity = hd argns
    val _ = arity > 0 orelse raise Match
    val [args] = argss |> sort_distinct (list_ord (Term_Ord.fast_term_ord o apply2 Thm.term_of))
    val _ = if exists is_funT args then raise Match else () (* avoid higher order functions like bind *)
    val fs' = (keys ~~ map fst values) |> map mk_prod |> mk_nonempty_list
    val d' = Thm.lambda p (fold_rev Thm.lambda args (Thm.apply d p)) |> fold_top_conv ctxt 
      |> Thm.rhs_of |> rename_dummy_abs_cterm 
    val rhs = \<^infer_instantiate>\<open>d'= d' and fs'= fs' and p = p in cterm \<open> map_of_default d' fs' p\<close>\<close> ctxt 
      |> fold (fn x => fn f => Thm.apply f x) args
    val eq = \<^infer_instantiate>\<open>lhs = ct and rhs = rhs in cprop \<open>lhs = rhs\<close>\<close> ctxt

    val simp_ctxt = (Simplifier.put_simpset basic_ss ctxt) addsimps @{thms map_of_default.simps}
    val thm = Goal.prove_internal ctxt [] eq (fn _ => asm_full_simp_tac simp_ctxt 1)
      |> safe_mk_meta_eq
  in 
    SOME thm
  end
  handle Pattern.MATCH => NONE
       | Bind => NONE
       | Match => NONE)
end
\<close>

simproc_setup passive map_of_default_fun_ptr_abs_args (\<open>map_of_default d fs p\<close>) = \<open>
let
  open map_of_default_args
  val basic_ss = Simplifier.simpset_of @{context}
  fun is_funT ct = ct |> Thm.typ_of_cterm |> try dest_funT |> is_some
  fun name_match ptr_name =
    is_some o try (unsuffix (ptr_name ^ "'")) 
  fun dest_fun_ptr_args ctxt {key, value} = 
    let
      val ptr_name = key |> Thm.term_of |> Term.term_name
      fun dest_fun_args t = 
        let 
          val (head, args) = strip_comb t
           
        in 
          if name_match ptr_name (Term.term_name head) then 
            SOME (map (Thm.cterm_of ctxt) args) 
          else 
            NONE  
        end 
      fun merge t _ = dest_fun_args t
      val args = [] |> Utils.fold_subterms_open merge (Thm.term_of value) |> these
    in
       args
    end
in
  K (fn ctxt => fn ct => 
  let
    val {fs, d, p, ...} = @{cterm_match "map_of_default ?d ?fs ?p"} ct
    val keys_values = dest_assoc_cterm fs
    val (keys, values) = keys_values |> map (fn {key, value} => (key, value)) |> split_list
    val argss = keys_values |> map (dest_fun_ptr_args ctxt)
    val _ = if null values then raise Match else ()

    val argns = map length argss
    val arity = hd argns
    val _ = arity > 0 orelse raise Match
    val [args] = argss |> sort_distinct (list_ord (Term_Ord.fast_term_ord o apply2 Thm.term_of))
    val _ = if exists is_funT args then raise Match else () (* avoid higher order functions like bind *)
    val abs_args = fold_rev Thm.lambda args
    val fs' = (keys ~~ map abs_args values) |> map mk_prod |> mk_nonempty_list
    val d' = Thm.lambda p (abs_args (Thm.apply d p)) |> fold_top_conv ctxt 
      |> Thm.rhs_of |> rename_dummy_abs_cterm 
    val rhs = \<^infer_instantiate>\<open>d'= d' and fs'= fs' and p = p in cterm \<open> map_of_default d' fs' p\<close>\<close> ctxt 
      |> fold (fn x => fn f => Thm.apply f x) args
    val eq = \<^infer_instantiate>\<open>lhs = ct and rhs = rhs in cprop \<open>lhs = rhs\<close>\<close> ctxt

    val simp_ctxt = (Simplifier.put_simpset basic_ss ctxt) addsimps @{thms map_of_default.simps}
    val thm = Goal.prove_internal ctxt [] eq (fn _ => asm_full_simp_tac simp_ctxt 1)
      |> safe_mk_meta_eq
  in 
    SOME thm
  end
  handle Pattern.MATCH => NONE
       | Bind => NONE
       | Match => NONE
       | TYPE _ => NONE (* loose bound variable when certifying an arg (e.g. the right hand side of thm ) *))
end
\<close>


lemma L2_condition_map_of_default_L2_call_fold_base: 
  "L2_condition (\<lambda>s. FUN_PTR (q = p)) (L2_call f emb ns) (L2_call \<top> emb ns) = 
   L2_call (map_of_default \<top> [(q, f)] p) emb ns"
  by (simp add: FUN_PTR_def)

lemma L2_guard_map_of_default_L2_call_fold_base: 
  "L2_seq (L2_guard (\<lambda>s. FUN_PTR (q = p))) (\<lambda>_. (L2_call f emb ns))  = 
   L2_call (map_of_default \<top> [(q, f)] p) emb ns"
  apply (clarsimp simp add: L2_defs L2_call_def FUN_PTR_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L2_condition_map_of_default_L2_call_fold_base': 
  "L2_condition (\<lambda>s. FUN_PTR (q = p)) (L2_call f emb ns) \<top> = 
   L2_call (map_of_default \<top> [(q, f)] p) emb ns"
  by (simp add: L2_call_def top_eq_fail FUN_PTR_def)

lemma L2_condition_map_of_default_L2_call_fold_cons: 
  "L2_condition (\<lambda>s. FUN_PTR (q = p)) (L2_call f emb ns) (L2_call (map_of_default d xs p) emb ns) = 
  L2_call (map_of_default d ((q, f)#xs) p) emb ns"
  by (simp add: FUN_PTR_def)

lemma condition_map_of_default_fold_cons_singleton: 
  "condition (\<lambda>s. FUN_PTR (q = (p::unit ptr)))
      f
      (g p) =
      (map_of_default g ([(q, f)]) p)"
  by (simp add: FUN_PTR_def)

lemma condition_map_of_default_call_fold_base: 
  "condition (\<lambda>s. FUN_PTR (q = p))
      (map_value (map_exn emb) f)
      (map_value (map_exn emb) fail) =
    map_value (map_exn emb) (map_of_default \<top> [(q, f)] p)"
  by (simp add: top_eq_fail[symmetric] FUN_PTR_def)

lemma guard_map_of_default_call_fold_base: 
  "guard (\<lambda>s. FUN_PTR (q = (p::unit ptr)))
      \<bind> (\<lambda>_. (map_value (map_exn emb) f))
       =
    map_value (map_exn emb) (map_of_default \<top> [(q, f)] p)"
  apply (clarsimp simp add: FUN_PTR_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma guard_map_of_default_call_fold_base': 
  assumes "NO_MATCH (map_value (map_exn emb) g) f"
  assumes "NO_MATCH ((bind g h)::('g option, 'h, 'c) spec_monad) (f::('g option, 'h, 'c) spec_monad)"
  shows   "guard (\<lambda>s. FUN_PTR (q = (p::unit ptr)))
      \<bind> (\<lambda>_. f)
       =
     (map_of_default \<top> [(q, f)] p)"
  apply (clarsimp simp add: FUN_PTR_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma guard_map_of_default_call_fold_base'': 
  assumes "NO_MATCH (map_value (map_exn emb) g) f"
  assumes "NO_MATCH (guard P) f"
  shows   "guard (\<lambda>s. FUN_PTR (q = (p::unit ptr)))
      \<bind> (\<lambda>_. bind f h)
       =
     (map_of_default \<top> [(q, f)] p) \<bind> h"
  apply (clarsimp simp add: FUN_PTR_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma guard_map_of_default_call_fold_base''': 
  assumes "NO_MATCH ((bind g h)::('g ::default, 'h, 'c) spec_monad) (f::('g ::default, 'h, 'c) spec_monad)"
  shows   "guard (\<lambda>s. FUN_PTR (q = (p::unit ptr)))
      \<bind> (\<lambda>_. f)
       =
     (map_of_default \<top> [(q, f)] p)"
  apply (clarsimp simp add: FUN_PTR_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma guard_map_of_default_call_fold_base'''': 
  shows   "guard (\<lambda>s. FUN_PTR (q = (p::unit ptr)))
      \<bind> (\<lambda>_. bind (guard P) (\<lambda>_. h))
       =
     (map_of_default \<top> [(q, bind (guard P) (\<lambda>_. h))] p) "
  apply (clarsimp simp add: FUN_PTR_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma condition_map_of_default_call_fold_base': 
  "condition (\<lambda>s. FUN_PTR (q = p))
      (map_value (map_exn emb) f)
      fail =
    map_value (map_exn emb) (map_of_default \<top> [(q, f)] p)"
  by (simp add: top_eq_fail FUN_PTR_def)

lemma condition_map_of_default_call_fold_base'': 
  "NO_MATCH (map_value (map_exn emb) g) f \<Longrightarrow> condition (\<lambda>s. FUN_PTR (q = p))
      f
      fail =
    (map_of_default \<top> [(q, f)] p)"
  by (simp add: top_eq_fail FUN_PTR_def)

lemma condition_map_of_default_call_fold_cons: 
  "condition (\<lambda>s. FUN_PTR (q = p))
      (map_value (map_exn emb) f)
      (map_value (map_exn emb) (map_of_default d xs p)) =
    map_value (map_exn emb) (map_of_default d ((q, f) # xs) p)"
  by (simp add: FUN_PTR_def)

lemma condition_map_of_default_call_fold_cons': 
  "condition (\<lambda>s. FUN_PTR (q = (p::unit ptr)))
      f
      (map_of_default d xs p) =
      (map_of_default d ((q, f) # xs) p)"
  by (simp add: FUN_PTR_def)

lemma ocondition_map_of_default_call_fold_base: 
  "ocondition (\<lambda>s. FUN_PTR (q = p)) f ofail =
     (map_of_default (\<lambda>_. ofail) [(q, f)] p)"
  by (simp add: FUN_PTR_def)

lemma oguard_map_of_default_call_fold_base: 
  assumes "NO_MATCH (obind g h) f"
  shows "obind (oguard (\<lambda>s. FUN_PTR (q = (p::unit ptr)))) (\<lambda>_. f) =
     (map_of_default (\<lambda>_. ofail) [(q, f)] p)"
  by (simp add: FUN_PTR_def)

lemma oguard_map_of_default_call_fold_base':
  shows "obind (oguard (\<lambda>s. FUN_PTR (q = (p::unit ptr)))) (\<lambda>_. (obind f h)) =
     obind ((map_of_default (\<lambda>_. ofail) [(q, f)] p)) h"
  by (simp add: FUN_PTR_def)


lemma ocondition_map_of_default_call_fold_cons: 
  "ocondition (\<lambda>s. FUN_PTR (q = p)) f (map_of_default d xs p) =
     (map_of_default d ((q, f) # xs) p)"
  by (simp add: FUN_PTR_def)

lemmas condition_map_of_default_folds =
  L2_condition_map_of_default_L2_call_fold_base
  L2_condition_map_of_default_L2_call_fold_base'
  L2_guard_map_of_default_L2_call_fold_base
  L2_condition_map_of_default_L2_call_fold_cons
  condition_map_of_default_call_fold_base
  condition_map_of_default_call_fold_base'
  condition_map_of_default_call_fold_base''
  guard_map_of_default_call_fold_base
  guard_map_of_default_call_fold_base'
  guard_map_of_default_call_fold_base''
  guard_map_of_default_call_fold_base'''
  guard_map_of_default_call_fold_base''''
  condition_map_of_default_call_fold_cons
  condition_map_of_default_call_fold_cons'
  ocondition_map_of_default_call_fold_base
  oguard_map_of_default_call_fold_base
  oguard_map_of_default_call_fold_base'
  ocondition_map_of_default_call_fold_cons

lemma L2_call_L2_fail: "L2_call L2_fail emb ns = L2_fail"
  by (simp add: L2_call_def L2_fail_def)
 
ML \<open>
structure map_of_default_args =
struct
 open map_of_default_args
 
fun distrib_L2_call_simpset ctxt =   
  let
    val L2_call_map_of_default_commutes = Named_Theorems.get ctxt @{named_theorems L2_call_map_of_default_commutes}
    val simp_ctxt = (Simplifier.clear_simpset ctxt) addsimps
         L2_call_map_of_default_commutes @
         @{thms map_of_default.simps(1) list.map apsnd_conv
            L2_fail_top[symmetric] L2_call_L2_fail}
  in simp_ctxt end

fun unfold_simpset ctxt =   
  let
    val simp_ctxt = (Simplifier.clear_simpset ctxt) addsimps
         @{thms map_of_default_cons_L2_condition map_of_default.simps(1) list.map apsnd_conv
            L2_fail_top[symmetric] L2_call_L2_fail}
  in simp_ctxt end

fun unfold_map_of_default_tac ctxt = 
  simp_tac (distrib_L2_call_simpset ctxt) THEN'
  simp_tac (unfold_simpset ctxt)

fun unfold_map_of_default_conv ctxt = 
  Simplifier.rewrite (distrib_L2_call_simpset ctxt) then_conv
  Simplifier.rewrite (unfold_simpset ctxt)

fun unfold_map_of_default_fconv ctxt =
  Simplifier.simplify (distrib_L2_call_simpset ctxt) #>
  Simplifier.simplify (unfold_simpset ctxt)


fun fold_simpset ctxt =
  Simplifier.clear_simpset ctxt 
    |> fold Simplifier.add_simp @{thms condition_map_of_default_folds L2_fail_top}
    |> Simplifier.add_proc @{simproc HOL.NO_MATCH}
fun args_simpset ctxt =
  Simplifier.clear_simpset ctxt
    |> Simplifier.add_proc @{simproc map_of_default_fun_ptr_abs_args}

fun fold_map_of_default_tac ctxt =
  simp_tac (fold_simpset ctxt) THEN' 
  simp_tac (args_simpset ctxt)

fun fold_map_of_default_conv ctxt = 
  Simplifier.rewrite (fold_simpset ctxt) then_conv
  Simplifier.rewrite (args_simpset ctxt)

fun fold_map_of_default_fconv ctxt = 
  Simplifier.simplify (fold_simpset ctxt) #>
  Simplifier.simplify (args_simpset ctxt)

fun fold_map_of_default_fconv' ctxt thm =
  let
    val _ = tracing ("fold_map_of_default_fconv thm: " ^ Thm.string_of_thm ctxt thm)
    val res = fold_map_of_default_fconv ctxt thm
    val _ = tracing ("fold_map_of_default_fconv res: " ^ Thm.string_of_thm ctxt res)
  in 
    res
  end
end


\<close>
thm L2_call_map_of_default_commutes

lemma fail_guard_intro: 
  assumes "\<And> s. \<not> fail_guard s \<Longrightarrow> run f s = \<top>"
  shows "(guard fail_guard \<bind> (\<lambda>_. f)) = f"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  using assms
  by (metis holds_top_post_state runs_to.rep_eq)

lemma map_of_default_domain_fail_guard: 
  "p \<notin> set (map fst xs) \<Longrightarrow> run (map_of_default (\<lambda>_. \<top>) xs p) s = \<top>"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  then show ?case 
    by (cases x1) auto
qed
 


lemma L2_guarded_fail_guard_intro:
  assumes "\<And> s. \<not> fail_guard s \<Longrightarrow> run f s = \<top>"
  shows "L2_guarded g f = L2_guarded (\<lambda>s. fail_guard s \<and> g s) f"
  apply (simp add: L2_guarded_def L2_seq_def L2_guard_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  using assms
  by (metis holds_top_post_state runs_to.rep_eq)

lemma L2_guarded_fail_guard_cong:
  assumes "\<And> s. \<not> fail_guard s \<Longrightarrow> run f s = \<top>"
  assumes "\<And> s. fail_guard s \<Longrightarrow> g s = g' s"
  shows "L2_guarded g f = L2_guarded g' f"
  apply (simp add: L2_guarded_def L2_seq_def L2_guard_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  subgoal
    using assms
    by (metis holds_top_post_state runs_to.rep_eq)
  subgoal
    using assms
    by (metis holds_top_post_state runs_to.rep_eq)
  done

lemma L2_guarded_map_of_default_guard_cong:
  assumes "\<And>s. p \<in> set (map fst xs) \<Longrightarrow> g s = g' s"
  shows "L2_guarded g (map_of_default (\<lambda>_. \<top>) xs p) = L2_guarded g' (map_of_default (\<lambda>_. \<top>) xs p)"
  apply (rule L2_guarded_fail_guard_cong)
   apply (rule map_of_default_domain_fail_guard)
   apply assumption
  by (rule assms)


lemma L1_guarded_fail_guard_cong:
  assumes "\<And> s. \<not> fail_guard s \<Longrightarrow> run f s = \<top>"
  assumes "\<And> s. fail_guard s \<Longrightarrow> g s = g' s"
  shows "(L1_guarded g f) = (L1_guarded g' f)"
  apply (simp add: L1_guarded_def L1_seq_def L1_guard_def)
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  subgoal
    using assms
    by (metis holds_top_post_state runs_to.rep_eq)
  subgoal
    using assms
    by (metis holds_top_post_state runs_to.rep_eq)
  done


lemma runs_to_run_topI: assumes "\<And>P. (runs_to f s P) = False" shows "run f s = \<top>"
  using assms
  apply (auto simp add: runs_to_def)
  by (metis assms run_runs_to_extensionality runs_to_top top_apply top_spec_monad.rep_eq)


lemma L1_guarded_L1_call_map_of_default_guard_cong:
  assumes domain: "\<And>s. e s \<in> set (map fst xs) \<Longrightarrow> g s = g' s"
  shows "(L1_guarded g
         (do {
            p \<leftarrow> gets e;
            L1_call init (map_of_default (\<lambda>_. \<top>) xs p) ret ex res
         })) = (L1_guarded g'
         (do {
            p \<leftarrow> gets e;
            L1_call init (map_of_default (\<lambda>_. \<top>) xs p) ret ex res
         }))"
  apply (rule L1_guarded_fail_guard_cong [where fail_guard = " \<lambda>s. e s \<in> set (map fst xs)"])
  subgoal 
    apply (simp add: L1_call_def)
    apply (rule runs_to_run_topI)
    apply (auto simp add: runs_to_iff map_of_default_fallthrough)
    done
  subgoal by (rule assms)
  done

lemma fun_ord_leD: "fun_ord X f g \<Longrightarrow> X (f x) (g x)"
  by (simp add: fun_ord_def)

lemma fun_ord_leD_fo: "fun_ord (fun_ord X) f g \<Longrightarrow> fun_ord X (f x) (g $ x)"
  by (simp add: fun_ord_def)

lemma le_funD_fo: "f \<le> g \<Longrightarrow> (f x) \<le> (g $ x)"
  by (simp add: le_funD fun_app_def)

lemma le_fun_const[monad_mono_intros]: 
  "(\<And>x. f x \<le> g) \<Longrightarrow> f \<le> (\<lambda>_. g) \<comment> \<open>in particular \<open>g = \<top>\<close>\<close>"
  by (rule Orderings.le_funI)


lemma option_le_fun_const[monad_mono_intros]: 
  "(\<And>x. X g (f x)) \<Longrightarrow> fun_ord X (\<lambda>_. g) f \<comment> \<open>in particular \<open>g = None\<close>\<close>"
  by (simp add: fun_ord_def)

lemma fun_ordI: "(\<And>x. X (g x) (f x)) \<Longrightarrow> fun_ord X g f"
  by (simp add: fun_ord_def)
lemma option_ord_None [monad_mono_intros]: "option_ord None X"
  by (auto simp add: flat_ord_def)

lemma option_le_map_of_default_list_all [monad_mono_intros]:
  assumes "list_all (\<lambda>(p, f). X f (m p)) xs"
  assumes "fun_ord X d m "
  shows "fun_ord X (map_of_default d xs) m"
  using assms 
proof (induct xs arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  then show ?case 
    by (simp add: fun_ord_def split_beta)
qed

lemma fun_ord_reflI[monad_mono_intros] \<comment> \<open>SIC: after @{thm option_le_map_of_default_list_all} \<close>: "(\<And>x. X (f x) (f x)) \<Longrightarrow>  fun_ord X f f"
  by (auto simp add: fun_ord_def)

lemma le_map_of_default_list_all [monad_mono_intros]:
  assumes "list_all (\<lambda>(p, f). m p \<le> f) xs"
  assumes "m \<le> d"
  shows "m \<le> map_of_default d xs"
  using assms 
proof (induct xs arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  then show ?case 
    by (simp add: le_fun_def split_beta)
qed



lemma list_all_cons_rev[monad_mono_intros]: 
  "list_all P xs \<Longrightarrow> P x \<Longrightarrow> list_all P (x#xs)"
  by (rule list_all_cons)

lemma list_all_empty[monad_mono_intros]: 
  "list_all P []"
  by simp

lemma mono_case_prod[monad_mono_intros]:
  "f (fst x) (snd x) \<le> g (fst x) (snd x) \<Longrightarrow> 
  (case x of (v1, v2) \<Rightarrow> f v1 v2) \<le> (case x of (v1, v2) \<Rightarrow> g v1 v2)"
  by (cases x) auto

lemma mono_option_le_fun_case_prod[monad_mono_intros]:
  "option.le_fun (f (fst x) (snd x)) (g (fst x) (snd x)) \<Longrightarrow> 
  option.le_fun (case x of (v1, v2) \<Rightarrow> f v1 v2) (case x of (v1, v2) \<Rightarrow> g v1 v2)"
  by (cases x) auto

lemma mono_option_fun_ord_case_prod[monad_mono_intros]:
  "fun_ord X (f (fst x) (snd x)) (g (fst x) (snd x)) \<Longrightarrow> 
  fun_ord X (case x of (v1, v2) \<Rightarrow> f v1 v2) (case x of (v1, v2) \<Rightarrow> g v1 v2)"
  by (cases x) auto

lemma option_le_antisym: "option.le_fun f g \<Longrightarrow> option.le_fun g f \<Longrightarrow> f = g"
  by (meson flat_interpretation partial_function_definitions.leq_antisym partial_function_lift)

lemma option_le_fun_eq_iff: "f = g \<longleftrightarrow> (option.le_fun f g \<and> option.le_fun g f)"
  using option_le_antisym option_le_refl
  by auto

lemmas (in complete_lattice) top_greatest [corres_top]

declare TrueI [corres_top]
lemma option_le_top[corres_top]: "option.le_fun (\<lambda>a. None) f"
  by (simp add: flat_ord_def fun_ord_def)

lemma notinI: "x \<in> X = False \<Longrightarrow> x \<notin> X"
  by auto

(* Utils *)
ML_file "lib/set.ML"
ML_file "trace_antiquote.ML"

(* Common data structures *)


ML_file "function_info.ML"
ML_file "program_info.ML"
ML_file "autocorres_trace.ML"
ML_file "autocorres_options.ML"
ML_file "autocorres_data.ML"

(* Common control code *)
ML_file "autocorres_util.ML"

(* L1 *)
ML_file "exception_rewrite.ML"
ML_file "simpl_conv.ML"
(* L2 *)
ML_file "prog.ML"
ML_file "pretty_bound_var_names.ML"
ML_file "l2_opt.ML"
ML_file "local_var_extract.ML"

(* IO *)

context globals_stack_heap_state
begin
ML_file "in_out_parameters.ML"

declaration \<open>fn phi =>
  In_Out_Parameters.Data.add (In_Out_Parameters.operations phi) phi\<close>
end

(* HL *)
ML_file "record_utils.ML"
ML_file "heap_lift_base.ML"
ML_file "heap_lift.ML"
(* WA *)
ML_file "word_abstract.ML"
ML_file "monad_convert.ML"
(* TS *)
ML_file "type_strengthen.ML"

ML_file "function_pointer.ML"
ML_file "autocorres.ML"


ML_val \<open>Variable.dest_all_cterm\<close>

(* Setup "init-autocorres" keyword. *)
ML \<open>
  Outer_Syntax.command @{command_keyword "init-autocorres"}
    "Initialise Autocorres"
    (AutoCorres.init_autocorres_parser >>
      (Toplevel.theory o (fn (opt, filename) => AutoCorres.do_init_autocorres opt filename true #> snd)))
\<close>


(* Setup "autocorres" keyword. *)
ML \<open>
  Outer_Syntax.command @{command_keyword "autocorres"}
    "Abstract the output of the C parser into a monadic representation."
    (AutoCorres.autocorres_parser >>
      (Toplevel.theory o (fn (opt, filename) => AutoCorres.parallel_autocorres opt filename)))
\<close>

(* Setup "final-autocorres" keyword. *)
ML \<open>
  Outer_Syntax.command @{command_keyword "final-autocorres"}
    "Finalise Autocorres"
    (AutoCorres.final_autocorres_parser >>
      (Toplevel.theory o (fn filename => AutoCorres.final_autocorres_cmd filename)))
\<close>

abbreviation "pre_post_pure_spec P R \<equiv> (guard (\<lambda>_. P) \<bind> (\<lambda>_. assume_result_and_state R))::('a, unit) res_monad"

lemma L2_pre_post_read_write_pre_post_pure_spec: 
"refines 
  (L2_pre_post_read_write r w Pre Post)
  (pre_post_pure_spec Pre (\<lambda>_::unit. {(v, _::unit). v \<in> Post (r s)} ))
  s ()
  (\<lambda>(v, s') (Res (v', t'), ()). s' = w (\<lambda>_. t') s \<and> v = Result v')"
  unfolding L2_defs L2_guarded_def
  apply (simp add: refines_bind_guard_right_iff)
  apply clarify
  apply (simp add: refines_assume_result_and_state_iff)
  apply (simp add: sim_set_def )
  done

text \<open>@{term "L2_pre_post_read_write r w"} only reads state according to reader @{term r} and only writes state according to writer @{term w}.\<close>
lemma L2_pre_post_read_write_effects_confined: 
"refines 
  (L2_pre_post_read_write r w Pre Post)
  (pre_post_pure_spec Pre (\<lambda>_::unit. {(v, _::unit). v \<in> Post (r s)} ))
  s ()
  (\<lambda>(_, s') (Res (_, t'), ()). s' = w (\<lambda>_. t') s)"
  unfolding L2_defs L2_guarded_def
  apply (simp add: refines_bind_guard_right_iff)
  apply clarify
  apply (simp add: refines_assume_result_and_state_iff)
  apply (simp add: sim_set_def )
  apply auto
  done

lemma L2_pre_post_read_write_effects_confined':
  shows "L2_pre_post_read_write r w Pre Post \<bullet> s ?\<lbrace>\<lambda>v s'. \<exists>v' t'. (v', t') \<in> Post (r s) \<and> v = Result v' \<and> s' = w (\<lambda>_. t') s\<rbrace>"
  unfolding L2_defs L2_guarded_def
  apply (runs_to_vcg)
  apply blast
  done

lemma L2_pre_post_read_write_writes_confined:
  shows "L2_pre_post_read_write r w Pre Post \<bullet> s ?\<lbrace>\<lambda>_ s'. \<exists>t'. s' = w (\<lambda>_. t') s\<rbrace>"
  unfolding L2_defs L2_guarded_def
  apply (runs_to_vcg)
  apply blast
  done

text \<open>This lemma in particular expresses what parts of the state are read and written. It 
  states that there is a pure function that simulates @{const L2_pre_post_read_write} which 
  only gets the inputs according to reads @{term r} and produces some outputs @{term "t'"} that are put into the
  original state by updating with the writes function @{term w}\<close>
lemma L2_pre_post_read_write_confined_canonical:
  fixes r:: "'s \<Rightarrow> 'r" \<comment> \<open>The reads projection from the state\<close>
  fixes w:: "('w \<Rightarrow> 'w) \<Rightarrow> 's \<Rightarrow> 's" \<comment> \<open>The writes function to the state\<close>
  fixes Post:: "'r \<Rightarrow> ('v \<times> 'w) set" \<comment> \<open>only depends on the reads and produces a value and the input for writes\<close>
  shows
  "\<exists>g::'r \<Rightarrow> ('v \<times> 'w, unit) res_monad. \<comment> \<open>a pure computation (sate is unit) that takes the reads as in put,  producing a result value and input for writes\<close>
    refines 
      (L2_pre_post_read_write r w Pre Post)
      (g (r s))
      s ()
      (\<lambda>(v, s') (Res (v', t'), ()). s' = w (\<lambda>_. t') s \<and> v = Result v')"
  apply (rule exI)
  apply (rule L2_pre_post_read_write_pre_post_pure_spec)
  done

lemma L2_pre_post_read_write_unconstrained: 
"refines
   (L2_pre_post_read_write (\<lambda>s. s) (\<lambda>f s. f s) Pre Post)
   (pre_post_pure_spec Pre (\<lambda>_::unit. {(v, _::unit). v \<in> Post s} ))
   s () 
   (\<lambda>(_, s') (Res (_, t'), ()). s' = t')"
  by (rule L2_pre_post_read_write_effects_confined)

lemma L2_pre_post_read_write_pure: 
"refines
   (L2_pre_post_read_write (\<lambda>s. ()) (\<lambda>_ s. s) Pre Post)
   (pre_post_pure_spec Pre (\<lambda>_::unit. {(v, _::unit). v \<in> Post ()} ))
   s () 
   (\<lambda>(_, s') (Res (_, t'), ()). s' = s)"
  by (rule L2_pre_post_read_write_effects_confined)
lemma L2_pre_post_read_anything_write_nothing: 
"refines
   (L2_pre_post_read_write (\<lambda>s. s) (\<lambda>_ s. s) Pre Post)
   (pre_post_pure_spec Pre (\<lambda>_::unit. {(v, _::unit). v \<in> Post s} ))
   s () 
   (\<lambda>(_, s') (Res (_, t'), ()). s' = s)"
  by (rule L2_pre_post_read_write_effects_confined)

ML \<open>
structure AutoCorres_Attrib =
struct
  fun dest_exec_spec_monad ct = ct |> Match_Cterm.switch [
    @{cterm_match \<open>exec_spec_monad ?get_x ?upd_x ?st ?args ?f ?res\<close>} #> (fn {get_x, upd_x, st, args, f, res, ...} => 
       {get_x = get_x, upd_x = upd_x, st = st, args = args, f = f, res = res}),
    fn _ => raise Match]

  val dest_proto_def = Thm.cconcl_of #> Utils.crhs_of_eq #> dest_exec_spec_monad

fun fields_from_variables (AstDatatype.Variables {global_vars, heap_vars, ...}) =
  let
     val globs = 
       if Symuset.is_univ global_vars then 
         error "fields_from_variables: expecting global variables not UNIV"
       else 
         the (Symuset.dest global_vars)
     val heap = if heap_vars then [NameGeneration.global_heap] else []
  in heap @ globs end

  datatype kind = Anything | Nothing | Specific

  fun var_kind v = 
    if AstDatatype.variables_ord (v, AstDatatype.prototype_default_vars) = EQUAL then Anything
    else if AstDatatype.variables_ord (v, AstDatatype.vars_empty) = EQUAL then Nothing
    else Specific
  
  fun read_write_terms ctxt read_vars write_vars =
    let
      val thy = Proof_Context.theory_of ctxt     
      val read_kind = var_kind read_vars
      val write_kind = var_kind write_vars
      val rec_name = NameGeneration.global_rcd_name
      val globalsT = Proof_Context.read_typ ctxt rec_name
      val fields = Record.get_extT_fields thy globalsT |> fst
      val field_lenses = fields |> map (fn x as (f, T) =>
               (x, (Const (f, globalsT --> T),
                Const (f ^  Record.updateN, (T --> T) --> globalsT --> globalsT))))
      fun global_lense name = 
        let             
          val name' = NameGeneration.ensure_varname name
        in 
          the (find_first (fn ((n, _), _) =>  Long_Name.base_name n = name') field_lenses)
        end
      val (r, readT)  = 
        case read_kind of
          Anything => (Abs ("s", globalsT, Bound 0), globalsT)
        | Nothing => (Abs ("s", globalsT, @{term "()"}), @{typ unit})
        | Specific =>
            let
              val prjs_read = map global_lense (fields_from_variables read_vars)
              val sels_read = map (#1 o #2) prjs_read
              val Ts = map (#2 o #1) prjs_read
              val readT = HOLogic.mk_tupleT Ts
            in (Abs ("s", globalsT, HOLogic.mk_tuple (map (fn sel => sel $ Bound 0) sels_read)), readT) end
  
      val (w, T) =
        case write_kind of                                                           
          Anything => (Abs ("t", globalsT, Abs ("_", globalsT --> globalsT, Abs ("_", globalsT, Bound 2))), globalsT)
        | Nothing => (Abs ("_", @{typ unit}, Abs ("_", @{typ unit} --> @{typ unit}, Abs ("s", globalsT, Bound 0))), @{typ unit})
        | Specific =>
            let
               val prjs_write = map global_lense (fields_from_variables write_vars)
               val n = length prjs_write
               val Ts = map (#2 o #1) prjs_write
               val T = HOLogic.mk_tupleT Ts 
               val upds = map (#2 o #2) prjs_write              
               val c = \<^Const>\<open>Fun.comp globalsT globalsT globalsT\<close>
               fun comp [f] = f
                 | comp (f::fs) = c $ f $ comp fs 
               val w = Abs ("t", T, Abs ("f", T --> T,  
                 let
                   val t' = Bound 1 $ Bound 2
                   val fld_upds = map (fn i => nth upds (i - 1) $ Abs ("_", nth Ts (i - 1), Tuple_Tools.mk_sel' Ts t' i)) (1 upto n)
                 in
                   comp fld_upds
                 end))
             in (w, T) end
    in {r = r, w = w, writeT = T, readT = readT, globalsT = globalsT, read_kind = read_kind, write_kind = write_kind, t = Free ("t", T)} end              

  val d1 = Unsynchronized.ref false

  fun make_prop fun_name read write def ctxt =
    let
      val {read_kind, write_kind, globalsT, readT, writeT, r, w, ...}  = read_write_terms ctxt read write
      val ((params, bdy), ctxt1) = dest_proto_def def |> #f |> Tuple_Tools.strip_case_prods ctxt
      val bdy' = Thm.term_of bdy
    in
      if read_kind = Anything andalso write_kind = Anything then 
        (Utils.verbose_msg 1 ctxt (fn _ => "no read / write proof for " ^ fun_name ^ " necessary (trivial)"); ([], ctxt))
      else if read_kind = Anything then 
        let
          val _ = Utils.verbose_msg 1 ctxt (fn _ => "doing read / write proof for " ^ fun_name ^ " (runs_to_partial)")
          val ([s], ctxt2) = Utils.fix_variant_frees [("s",globalsT)] ctxt1
          val prop = \<^infer_instantiate>\<open>bdy = bdy' and s = s and w = w in prop \<open>bdy \<bullet> s ?\<lbrace>\<lambda>_ s'. \<exists>t. s' = w t (\<lambda>_. t) s\<rbrace>\<close>\<close> ctxt
  
        in ([(s, (prop, []))], ctxt2) end
      else 
        let
          val _ = Utils.verbose_msg 1 ctxt (fn _ => "doing read / write proof for " ^ fun_name ^ " (refines)")
          val ([s], ctxt2) = Utils.fix_variant_frees [("s",globalsT)] ctxt1
          val prop = \<^infer_instantiate>\<open>bdy = bdy' and s = s and r = r and w = w in 
            prop \<open>\<exists>g. refines bdy (g (r s)) s () (\<lambda>(v, s') (Res (v', t'), ()). s' = w t' (\<lambda>_. t') s \<and> v = Result v')\<close>\<close> ctxt
        in ([(s, (prop, []))], ctxt2) end
    end

  fun runs_to_partial_tac s ctxt =  
    (Utils.dprint_subgoal_tac (!d1) "read / write proof start" ctxt THEN'
    simp_tac (ctxt addsimps @{thms L2_defs L2_guarded_def}) THEN'
    Utils.dprint_subgoal_tac (!d1) "read / write proof after unfold L2_defs" ctxt THEN'
    Runs_To_VCG.runs_to_vcg_tac' NONE (~1) Runs_To_VCG.no_trace_tac false {do_nosplit=false, no_unsafe_hyp_subst=false}
      (K no_tac) ctxt THEN'
    Utils.dprint_subgoal_tac (!d1) "read / write proof after runs_to_vcg" ctxt THEN_ALL_NEW (
      Induct_Tacs.case_tac ctxt (fst (dest_Free s)) [] NONE THEN'
      asm_full_simp_tac ctxt THEN' 
      Utils.dprint_subgoal_tac (!d1) "read / write proof after simp" ctxt))

  fun refines_tac s ctxt = 
    Utils.dprint_subgoal_tac (!d1) "read / write proof start" ctxt THEN'
    resolve_tac ctxt @{thms L2_pre_post_read_write_confined_canonical}

  fun read_write_confined_tac ctxt = SUBGOAL (fn (t, i) =>
    (case Utils.concl_of_subgoal t of
       @{term_pat "Trueprop (?bdy \<bullet> ?s ?\<lbrace>?P\<rbrace>)"}  => runs_to_partial_tac s ctxt i
    |  @{term_pat "Trueprop (\<exists>g. refines ?f ?g ?s ?t ?P)"} => refines_tac s ctxt i
    | _ => no_tac))
 
  fun make_read_write_proof ctxt (fun_name, pos) (AstDatatype.Dependencies {read, write}) def =
    let
      val {read_kind, write_kind, globalsT, readT, writeT, r, w, ...}  = read_write_terms ctxt read write
      val ((params, bdy), ctxt1) = dest_proto_def def |> #f |> Tuple_Tools.strip_case_prods ctxt
      val bdy' = Thm.term_of bdy
    in
      if read_kind = Anything andalso write_kind = Anything then 
        (Utils.verbose_msg 1 ctxt (fn _ => "no read / write proof for " ^ fun_name ^ " necessary (trivial)"); NONE)
      else if read_kind = Anything then 
        let
          val _ = Utils.verbose_msg 1 ctxt (fn _ => "doing read / write proof for " ^ fun_name ^ " (runs_to_partial)")
          val ([s], ctxt2) = Utils.fix_variant_frees [("s",globalsT)] ctxt1
          val prop = \<^infer_instantiate>\<open>bdy = bdy' and s = s and w = w in prop \<open>bdy \<bullet> s ?\<lbrace>\<lambda>_ s'. \<exists>t. s' = w t (\<lambda>_. t) s\<rbrace>\<close>\<close> ctxt
          val thm = Goal.prove ctxt2 [] [] prop (fn {context, ...} =>  
            runs_to_partial_tac s context 1)
  
        in SOME (thm |> singleton (Proof_Context.export ctxt2 ctxt)) end
      else 
        let
          val _ = Utils.verbose_msg 1 ctxt (fn _ => "doing read / write proof for " ^ fun_name ^ " (refines)")
          val ([s], ctxt2) = Utils.fix_variant_frees [("s",globalsT)] ctxt1
          val prop = \<^infer_instantiate>\<open>bdy = bdy' and s = s and r = r and w = w in 
            prop \<open>\<exists>g. refines bdy (g (r s)) s () (\<lambda>(v, s') (Res (v', t'), ()). s' = w t' (\<lambda>_. t') s \<and> v = Result v')\<close>\<close> ctxt
          val thm = Goal.prove ctxt2 [] [] prop (fn {context, ...} => 
           refines_tac s context 1)
        in SOME (thm |> singleton (Proof_Context.export ctxt2 ctxt)) end
    
    end


  fun check_prog_name context (prog_name, pos)  =                    
    let 
      val data = AutoCorres_Options.Options_Theory.get (Context.theory_of context)
    in 
     case Symtab.lookup data prog_name of 
       SOME X => X 
      | NONE => error ("undefined program name: " ^ prog_name  ^ Position.here pos) 
    end
  fun check_fun_name context prog_info (fun_name, pos) =
    let
      val cse = ProgramInfo.get_csenv prog_info
    in 
      if Symtab.defined (ProgramAnalysis.get_fninfo cse) fun_name then ()
      else error ("undeclared function: " ^ fun_name ^ Position.here pos)
    end
  fun check_dependencies context prog_info (fun_name, pos) =
    let
      val ctxt = Context.proof_of context
      val cse = ProgramInfo.get_csenv prog_info
      val deps = ProgramAnalysis.get_variable_dependencies cse
      val d = case Symtab.lookup deps fun_name of SOME d => d
        | NONE => error ("undeclared function: " ^ fun_name ^ Position.here pos)
      val all_embedded_funs = ProgramAnalysis.get_embedded_fncalls cse |> Binaryset.listItems |> 
        maps (fn ProgramAnalysis.DirectCall x => [x] | ProgramAnalysis.FnPtrCall (_, xs, _) => map #1 xs) 
       |> sort_distinct fast_string_ord
      val relevant_funs = ProgramAnalysis.get_final_callees cse all_embedded_funs
      val _ = Utils.verbose_msg 1 ctxt (fn _ => "relevant_funs: " ^ @{make_string} relevant_funs)
      
    in
      if member (op =) relevant_funs fun_name then
        SOME d
      else (Utils.verbose_msg 1 ctxt (fn _ => "no read / write proof for " ^ fun_name ^ " necessary (does not appear in an expression)"); NONE)
    end
  val _ = Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>declare_prototype\<close> "declare specification of C prototype to autocorres"  
         ((Args.mode "skip_proof") -- Parse.thm >> (fn (skip_proof, fact_ref) => fn lthy =>
    let
      val thm = singleton (Attrib.eval_thms lthy) fact_ref
      val lhs = thm |> Thm.cconcl_of |> Utils.clhs_of_eq |> Thm.term_of
      val fun_name = 
        (case lhs of 
           Const (x, _) => 
             (case try (unsuffix "_body") (Long_Name.base_name x) of 
               SOME n => n  
             | _ => error ("expecting definition of a C prototype in SIMPL with left hand side: ..._body, got " ^ x))
        | _ => error ("expecting definition of a C prototype in SIMPL with left hand side: ..._body"))
      val main = C_Files.get_main (Proof_Context.theory_of lthy)
      val prog_name = main |> Path.explode |> Path.drop_ext |> Path.file_name
      val {prog_info, options,...} = check_prog_name (Context.Proof lthy) (prog_name, Position.none)
      val skips = AutoCorres_Options.get_skips options
      val _ = check_fun_name (Context.Proof lthy) prog_info (fun_name, Position.none)
      val deps_opt = check_dependencies (Context.Proof lthy) prog_info (fun_name, Position.none)
      val ctxt0 = lthy |> HPInter.enter_scope prog_name fun_name 
      val thm' = Thm.proof_attributes (map (Attrib.attribute ctxt0) @{attributes [fold_locals]}) thm ctxt0 |> fst
      val decl = Local_Theory.declaration {pervasive=false, pos=\<^here>, syntax=false} (fn _ => 
        AutoCorresData.define_function {concealed_named_theorems=false} 
          prog_name skips FunctionInfo.CP fun_name thm')
    in 
      case deps_opt of 
       NONE => Proof.theorem NONE (fn thmss => decl) [] lthy 
      | SOME (AstDatatype.Dependencies {read, write}) => 
        let
          val ctxt0 = lthy |> HPInter.enter_scope prog_name fun_name 
          val (state_prop, ctxt) = make_prop fun_name read write thm ctxt0
          val prop = map snd state_prop
          val prop' = 
            if null prop then prop 
            else if skip_proof then (warning "skipping proof"; []) 
            else prop 
        in Proof.theorem NONE (fn thmss => decl) [prop'] ctxt 
        end 
    end))  
end
\<close>

method_setup read_write_confined = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (AutoCorres_Attrib.read_write_confined_tac ctxt))\<close>
  "standard read / write confinement proof for C prototypes"

attribute_setup autocorres_definition = \<open>
  Scan.lift (Parse.embedded_position -- AutoCorres_Options.parse_phase -- Parse.embedded_position) >> (fn ((prog_name, phase), fun_name) =>
    Thm.declaration_attribute (fn thm => fn context =>
      let
        val {options, prog_info, ...} = AutoCorres_Attrib.check_prog_name context prog_name
        val _ = AutoCorres_Attrib.check_fun_name context prog_info fun_name
        val skips = AutoCorres_Options.get_skips options
        val ctxt = Context.proof_of context |> HPInter.enter_scope (fst prog_name) (fst fun_name) 
        val thm' = Thm.proof_attributes (map (Attrib.attribute ctxt) @{attributes [fold_locals]}) thm ctxt |> fst
        val deps_opt = if phase = FunctionInfo.CP then AutoCorres_Attrib.check_dependencies context prog_info fun_name else NONE
        val _ = is_none deps_opt orelse error ("use command declare_prototype to declare C prototype") 
      in
        AutoCorresData.define_function {concealed_named_theorems=false} (fst prog_name) skips phase (fst fun_name) thm' context
      end))
\<close> "autocorres_definition <prog_name> <phase> <fun_name>"

attribute_setup autocorres_corres_thm = \<open>
  Scan.lift (Parse.embedded_position -- AutoCorres_Options.parse_phase -- Parse.embedded_position) >> (fn ((prog_name, phase), fun_name) =>
    Thm.declaration_attribute (fn thm => fn context =>
      let
        val {options, prog_info, ...} = AutoCorres_Attrib.check_prog_name context prog_name
        val _ = AutoCorres_Attrib.check_fun_name context prog_info fun_name
        val skips = AutoCorres_Options.get_skips options
      in
        AutoCorresData.corres_thm (fst prog_name) skips phase (fst fun_name) thm context
      end))
\<close> "autocorres_corres_thm <prog_name> <phase> <fun_name>"

setup \<open>
let
  fun fresh_var maxidx (n, T) = Var (("_" ^ n, maxidx + 1), T)
  fun head_type t = t |> HOLogic.dest_Trueprop |> head_of |> fastype_of
  fun get_maxidx maxidx ts =
    if maxidx < 0
    then fold (curry Int.max) (map maxidx_of_term ts) 0
    else maxidx

  \<comment> \<open>Note that the \<open>mk_pattern\<close> functions serve two purposes. When adding a rule
   into the term net we insert Var's for the positions that we want to synthesise. The
   concrete program '?C' serves as index into the net and is unmodified. Note that
   @{ML Utils.open_beta_norm_eta} should actually be the identity (with respect to matching)
   when applied to the rules.

   Before querying the term-net with a concrete subgoal we also use \<open>mk_pattern\<close>.
   Here @{ML Utils.open_beta_norm_eta} is essential to make term-net-retrieval for matching (instead of 'unification')
   work, as it gets rid of beta-eta artefacts in the goal that are generated during recursive
   application of the rules.
  \<close>

  fun mk_corresTA_pattern maxidx (t as @{term_pat "Trueprop (corresTA ?P ?rx ?ex ?A ?C)"}) =
    let
      val mi = get_maxidx maxidx [P, rx, ex, A, C]
      val T = head_type t
      val [PT, rxT, exT, AT, _] = binder_types T
      val [P', rx', ex', A'] = map (fresh_var mi) [("P", PT), ("rx", rxT), ("ex", exT), ("A", AT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "corresTA"}, T) $
            P' $ rx'  $ ex' $ A' $ Utils.open_beta_norm_eta C)

    in pat end

  fun mk_abstract_val_pattern maxidx (t as (@{term_pat "Trueprop (abstract_val ?P ?A ?f ?C)"})) =
    let
      val mi = get_maxidx maxidx [P, A, f, C]
      val T = head_type t
      val [PT, AT, fT, _] = binder_types T
      val [P', A', f'] = map (fresh_var mi) [("P", PT), ("A", AT), ("f", fT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "abstract_val"}, T) $
            P' $ A' $ f' $ Utils.open_beta_norm_eta C)
    in pat end

  fun mk_valid_typ_abs_fn_pattern maxidx (t as (@{term_pat "Trueprop (valid_typ_abs_fn ?P ?Q ?A ?C)"})) =
    let
      val mi = get_maxidx maxidx [P, Q, A, C]
      val T = head_type t
      val [PT, QT, AT, CT] = binder_types T
      val [P', Q', A', C'] = map (fresh_var mi) [("P", PT), ("Q", QT), ("A", AT), ("C", CT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "valid_typ_abs_fn"}, T) $
            P' $ Q' $ A' $ C')
    in pat end

  fun mk_introduce_typ_abs_fn_pattern maxidx (t as (@{term_pat "Trueprop (introduce_typ_abs_fn ?f)"})) =
    let
      val mi = get_maxidx maxidx [f]
      val T = head_type t
      val [fT] = binder_types T
      val [f'] = map (fresh_var mi) [("f", fT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "introduce_typ_abs_fn"}, T) $ f')
    in pat end

  fun mk_id_pattern _ t = t

  fun mk_abs_expr_pattern maxidx (t as (@{term_pat "Trueprop (abs_expr ?st ?P ?A ?C)"})) =
    let
      val mi = get_maxidx maxidx [st, P, A, C]
      val T = head_type t
      val [stT, PT, AT, _] = binder_types T
      val [st', P', A'] = map (fresh_var mi) [("st", stT), ("P", PT), ("A", AT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "abs_expr"}, T) $
            st' $ P' $ A' $ Utils.open_beta_norm_eta C)
    in pat end

  fun mk_abs_guard_pattern maxidx (t as (@{term_pat "Trueprop (abs_guard ?st ?A ?C)"})) =
    let
      val mi = get_maxidx maxidx[st, A, C]
      val T = head_type t
      val [stT, AT, _] = binder_types T
      val [st', A'] = map (fresh_var mi) [("st", stT), ("A", AT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "abs_guard"}, T) $
            st' $ A' $ Utils.open_beta_norm_eta C)
    in pat end

  fun mk_L2Tcorres_pattern maxidx (t as (@{term_pat "Trueprop (L2Tcorres ?st ?A ?C)"})) =
    let
      val mi = get_maxidx maxidx[st, A, C]
      val T = head_type t
      val [stT, AT, _] = binder_types T
      val [st', A'] = map (fresh_var mi) [("st", stT), ("A", AT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "L2Tcorres"}, T) $
            st' $ A' $ Utils.open_beta_norm_eta C)
    in pat end

  fun mk_abs_modifies_pattern maxidx (t as (@{term_pat "Trueprop (abs_modifies ?st ?P ?A ?C)"})) =
    let
      val mi = get_maxidx maxidx [st, P, A, C]
      val T = head_type t
      val [stT, PT, AT, _] = binder_types T
      val [st', P', A'] = map (fresh_var mi) [("st", stT), ("P", PT), ("A", AT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "abs_modifies"}, T) $
            st' $ P' $ A' $ Utils.open_beta_norm_eta C)
    in pat end

  fun mk_struct_rewrite_guard_pattern maxidx (t as (@{term_pat "Trueprop (struct_rewrite_guard ?A ?C)"})) =
    let
      val mi = get_maxidx maxidx [A, C]
      val T = head_type t
      val [AT, _] = binder_types T
      val [A'] = map (fresh_var mi) [("A", AT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "struct_rewrite_guard"}, T) $
            A' $ Utils.open_beta_norm_eta C)
    in pat end

  fun mk_struct_rewrite_expr_pattern maxidx (t as (@{term_pat "Trueprop (struct_rewrite_expr ?P ?A ?C)"})) =
    let
      val mi = get_maxidx maxidx[P, A, C]
      val T = head_type t
      val [PT, AT, _] = binder_types T
      val [P', A'] = map (fresh_var mi) [("P", PT), ("A", AT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "struct_rewrite_expr"}, T) $
            P' $ A' $ Utils.open_beta_norm_eta C)
    in pat end

  fun mk_struct_rewrite_modifies_pattern maxidx (t as (@{term_pat "Trueprop (struct_rewrite_modifies ?P ?A ?C)"})) =
    let
      val mi = get_maxidx maxidx [P, A, C]
      val T = head_type t
      val [PT, AT, _] = binder_types T
      val [P', A'] = map (fresh_var mi) [("P", PT), ("A", AT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "struct_rewrite_modifies"}, T) $
            P' $ A' $ Utils.open_beta_norm_eta C)
    in pat end

  fun mk_abs_spec_pattern maxidx (t as (@{term_pat "Trueprop (abs_spec ?st ?P ?A ?C)"})) =
    let
      val mi = get_maxidx maxidx[st, P, A, C]
      val T = head_type t
      val [stT, PT, AT, _] = binder_types T
      val [st', P', A'] = map (fresh_var mi) [("st", stT), ("P", PT), ("A", AT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "abs_spec"}, T) $
            st' $ P' $ A' $ Utils.open_beta_norm_eta C)
    in pat end

  fun mk_heap_lift__wrap_h_val_pattern maxidx (t as (@{term_pat "Trueprop (heap_lift__wrap_h_val ?X ?Y)"})) =
    let
      val mi = get_maxidx maxidx [X, Y]
      val T = head_type t
      val [XT, YT] = binder_types T
      val [X', Y'] = map (fresh_var mi) [("X", XT), ("Y", YT)]
      val pat = HOLogic.mk_Trueprop (Const (@{const_name "heap_lift__wrap_h_val"}, T) $ X' $ Y' )
    in pat end

in
  Context.theory_map (fold WordAbstract.add_pattern [
    mk_corresTA_pattern,
    mk_abstract_val_pattern,
    mk_valid_typ_abs_fn_pattern,
    mk_introduce_typ_abs_fn_pattern,
    mk_id_pattern
  ]) #>
  Context.theory_map (fold HeapLift.add_pattern [
    mk_abs_expr_pattern,
    mk_abs_guard_pattern,
    mk_L2Tcorres_pattern,
    mk_abs_modifies_pattern,
    mk_struct_rewrite_guard_pattern,
    mk_struct_rewrite_expr_pattern,
    mk_struct_rewrite_modifies_pattern,
    mk_abs_spec_pattern,
    mk_heap_lift__wrap_h_val_pattern,
    mk_id_pattern
  ])
end

\<close>

lemma refines_spec_monad_eq_iff: "f = g \<longleftrightarrow> (\<forall>s. refines f g s s (=)) \<and> (\<forall>s. refines g f s s (=))"
  apply (rule)
  subgoal 
      by (simp add: refines_right_eq_id)
  subgoal
    by (simp add: dual_order.antisym le_spec_monad_le_refines_iff)
  done

lemma (in complete_lattice) admissible_gfp_eq_right:
  "ccpo.admissible Inf (\<ge>) (\<lambda>y. (y = x))"
proof -
  have eq: "(\<lambda>y. (y = x)) = (\<lambda>y. (y \<le> x) \<and> (x \<le> y))"
    by (auto)
  show ?thesis
    apply (subst eq)
    apply (rule admissible_conj)
     apply (rule admissible_gfp_le_left)
    apply (rule admissible_gfp_le_right)
    done
qed

lemma (in complete_lattice) admissible_gfp_eq_left:
  "ccpo.admissible Inf (\<ge>) (\<lambda>y. (x = y))"
proof -
  have "(\<lambda>y. (x = y)) = (\<lambda>y. (y = x))" by (auto simp add: fun_eq_iff)
  from admissible_gfp_eq_right [of x, simplified this [symmetric]]
  show ?thesis .
qed

lemma admissible_gfp_eq_option_right: 
  shows "ccpo.admissible option.lub_fun option.le_fun (\<lambda>f. f = g)"
  apply (rule ccpo.admissibleI)
  by (smt (verit, ccfv_threshold) equals0I flat_interpretation 
      partial_function_definitions_def partial_function_lift)
lemma admissible_gfp_eq_option_left: 
  shows "ccpo.admissible option.lub_fun option.le_fun (\<lambda>f. g = f)"
proof -
  have "(\<lambda>f. (f = g)) = (\<lambda>f. (g = f))" by (auto simp add: fun_eq_iff)
  from admissible_gfp_eq_option_right [of g, simplified this]
  show ?thesis .
qed


end
