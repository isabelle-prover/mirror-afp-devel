(*  Title:      Eisbach_Protocol_Verification.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section \<open>Useful Eisbach Methods for Automating Protocol Verification\<close>
theory Eisbach_Protocol_Verification
  imports Stateful_Protocol_Composition_and_Typing.Stateful_Compositionality
          "HOL-Eisbach.Eisbach_Tools"
begin

ML\<open>fun code_simp_all_tac ctx = PARALLEL_ALLGOALS (fn i => Code_Simp.dynamic_tac ctx i)\<close>
method_setup code_simp_all = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (code_simp_all_tac ctxt))\<close>
                             \<open>code_simp (all goals)\<close>

ML\<open>fun normalization_all_tac ctx = PARALLEL_ALLGOALS (fn i => (CONVERSION(Nbe.dynamic_conv ctx) 
                                                               THEN_ALL_NEW (TRY o resolve_tac ctx [TrueI])) i)\<close>
method_setup normalization_all = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (normalization_all_tac ctxt))\<close>
                             \<open>normalization (all goals)\<close>

ML\<open>fun eval_all_tac ctx = 
  let
    fun eval_tac ctxt =
      let val conv = Code_Runtime.dynamic_holds_conv
      in
        CONVERSION (Conv.params_conv ~1 (Conv.concl_conv ~1 o conv) ctxt) THEN'
        resolve_tac ctxt [TrueI]
      end
  in
    PARALLEL_ALLGOALS (fn i => eval_tac ctx i)
  end \<close>
method_setup eval_all = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (eval_all_tac ctxt))\<close>
                             \<open>evaluation (all goals)\<close>

named_theorems exhausts
named_theorems type_class_instance_lemmata
named_theorems protocol_checks
named_theorems protocol_checks'
named_theorems coverage_check_unfold_protocol_lemma
named_theorems coverage_check_unfold_transaction_lemma
named_theorems coverage_check_unfold_lemmata
named_theorems protocol_check_intro_lemmata
named_theorems transaction_coverage_lemmata
named_theorems protocol_def 
named_theorems protocol_defs 

method UNIV_lemma =
  (rule UNIV_eq_I; (subst insert_iff)+; subst empty_iff; smt exhausts)+

method type_class_instance =
  (intro_classes; auto simp add: type_class_instance_lemmata)

method protocol_model_subgoal =
  (((rule allI, case_tac f); (erule forw_subst)+)?, simp_all)

method protocol_model_interpretation =
  (unfold_locales; protocol_model_subgoal+)

method composable_protocols_intro =
  (unfold protocol_checks' Let_def;
   intro comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>tI';
   (simp only: list.map(1,2) prod.sel(1))?;
   (intro list_set_ballI)?;
   (simp only: if_P if_not_P)?)

method coverage_check_intro =
  (((unfold coverage_check_unfold_protocol_lemma)?;
    intro protocol_check_intro_lemmata;
    simp only: list_all_simps list_all_append list.map concat.simps map_append product_concat_map;
    intro conjI TrueI);
   clarsimp?;
   (intro conjI TrueI)?;
   (rule transaction_coverage_lemmata)?)

method coverage_check_unfold =
  (unfold coverage_check_unfold_lemmata
          Let_def case_prod_unfold Product_Type.fst_conv Product_Type.snd_conv;
   simp only: list_all_simps;
   intro conjI TrueI)

method coverage_check_intro' =
  (((unfold coverage_check_unfold_protocol_lemma coverage_check_unfold_transaction_lemma)?;
    intro protocol_check_intro_lemmata;
    simp only: list_all_simps list_all_append list.map concat.simps map_append product_concat_map;
    intro conjI TrueI);
   (clarsimp+)?;
   (intro conjI TrueI)?;
   ((rule transaction_coverage_lemmata)+)?;
   coverage_check_unfold)

method check_protocol_intro =
  (unfold_locales, unfold protocol_checks[symmetric])

method check_protocol_intro' =
  ((check_protocol_intro;
    coverage_check_intro?;
    (unfold protocol_checks' Let_def; intro conjI)?),
  tactic distinct_subgoals_tac)

method check_protocol_with methods meth =
  ((check_protocol_intro; coverage_check_intro?), meth)

method parallel_check_protocol_with methods meth =
  (check_protocol_with \<open>((simp_all add: protocol_def protocol_defs Let_def, safe)?), tactic \<open>distinct_subgoals_tac\<close>, meth\<close>)

method check_protocol =
  (parallel_check_protocol_with \<open>code_simp_all\<close>)

method check_protocol_nbe =
  (parallel_check_protocol_with \<open>normalization_all\<close>)

method check_protocol_eval =
  (parallel_check_protocol_with \<open>eval_all\<close>)

method check_protocol_compositionality =
  (check_protocol_with \<open>code_simp_all\<close>; fastforce?)

method check_protocol_compositionality_nbe =
  (check_protocol_with \<open>normalization_all\<close>; fastforce?)

method check_protocol_compositionality_eval =
  (check_protocol_with \<open>(eval_all?, code_simp_all?)\<close>; fastforce?)
  
end
