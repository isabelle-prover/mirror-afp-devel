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

named_theorems exhausts
named_theorems type_class_instance_lemmata
named_theorems protocol_checks
named_theorems protocol_checks'
named_theorems coverage_check_unfold_protocol_lemma
named_theorems coverage_check_unfold_transaction_lemma
named_theorems coverage_check_unfold_lemmata
named_theorems protocol_check_intro_lemmata
named_theorems transaction_coverage_lemmata

method UNIV_lemma =
  (rule UNIV_eq_I; (subst insert_iff)+; subst empty_iff; smt exhausts)+

method type_class_instance =
  (intro_classes; auto simp add: type_class_instance_lemmata)

method protocol_model_subgoal =
  (((rule allI, case_tac f); (erule forw_subst)+)?; simp)

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
  (check_protocol_intro; meth)

method check_protocol =
  (check_protocol_with \<open>coverage_check_intro?; code_simp\<close>)

method check_protocol_nbe =
  (check_protocol_with \<open>coverage_check_intro?; normalization\<close>)

method check_protocol_unsafe =
  (check_protocol_with \<open>coverage_check_intro?; eval\<close>)

method check_protocol_compositionality =
  (check_protocol_with \<open>coverage_check_intro?; (code_simp; fastforce?)\<close>)

method check_protocol_compositionality_nbe =
  (check_protocol_with \<open>coverage_check_intro?; (normalization; fastforce?)\<close>)

method check_protocol_compositionality_unsafe =
  (check_protocol_with \<open>coverage_check_intro?; (eval?; (code_simp; fastforce?))\<close>)

end
