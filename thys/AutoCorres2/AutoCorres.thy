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
  "final-autocorres":: thy_decl
begin

no_syntax  "_Lab":: "'a bexp \<Rightarrow> ('a,'p,'f) com \<Rightarrow> bdy"
            (\<open>_\<bullet>/_\<close> [1000,71] 81) \<comment> \<open>avoid syntax conflict with \<^term>\<open>runs_to f s Q\<close>\<close>

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
  by (smt (z3) Exn_neq_Result Result_eq_Result the_Exn_Exn(1))



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

lemma [polish]:
  "guard (\<lambda>s. UNDEFINED_FUNCTION) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "(FUNCTION_BODY_NOT_IN_INPUT_C_FILE >>= m) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "unknown >>= (\<lambda>x. FUNCTION_BODY_NOT_IN_INPUT_C_FILE) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "liftE FUNCTION_BODY_NOT_IN_INPUT_C_FILE = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (rule spec_monad_ext, 
      simp add: run_bind run_guard UNDEFINED_FUNCTION_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def)+

(* Rewrites that will be applied before collecting statistics. *)
lemmas ac_statistics_rewrites =
    (* Setup "L1_seq" to have a sane lines-of-spec measurement. *)
    L1_seq_def
    (* Convert L2 to standard exception monads. *)
    L2_defs'


text \<open>There might be unexpected simplification 'unfolding' of @{const id} due to eta-expansion:
@{term id} might be expanded (e.g. by resolution to ) @{term "\<lambda>x. id x"}. Now the
simp rule @{thm id_apply} triggers and rewrites it @{term "\<lambda>x. x"}. Folding this back to
@{term id} might help in those cases.
\<close>

named_theorems
  l1_corres and l2_corres and io_corres and hl_corres and wa_corres and ts_corres and ac_corres and
  known_function_corres and known_function

lazy_named_theorems
  l1_def and l2_def and io_def and hl_def and wa_def and ts_def and ac_def
named_theorems
  heap_update_syntax

lemma fold_id: "(\<lambda>x. x) = id"
  by (simp add: id_def)

lemma fold_id_unit: " (\<lambda>_. ()) = id"
  by (simp add: id_def)
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
ML_file "pretty_bound_var_names.ML"
ML_file "monad_convert.ML"
(* TS *)
ML_file "type_strengthen.ML"

ML_file "autocorres.ML"

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


end
