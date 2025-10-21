theory Untyped_Superposition_Inference_System
  imports 
    Untyped_Superposition
    Grounded_Superposition
    First_Order_Clause.Untyped_Calculus
begin

context untyped_superposition_calculus
begin

sublocale typed: superposition_calculus where
  welltyped = "\<lambda>_ _ (). True"
  by
    unfold_locales
    (auto intro: term.ground_exists simp: term.exists_imgu right_unique_def split: unit.splits)

lemma weakly_welltyped_atom [simp]: "typed.weakly_welltyped_atom (\<lambda>_. ()) a"
  unfolding typed.weakly_welltyped_atom_def
  by blast
  
lemma weakly_welltyped_literal [simp]: "typed.weakly_welltyped_literal (\<lambda>_. ()) l"
  unfolding typed.weakly_welltyped_literal_def
  by simp

declare
  typed.term.welltyped_renaming [simp del]
  typed.term.welltyped_subst_stability [simp del]
  typed.term.welltyped_subst_stability' [simp del]

(* TODO: Write own *)
abbreviation entails where
  "entails N N' \<equiv> typed.entails_\<G> (empty_typed ` N) (empty_typed ` N')"

sublocale untyped_consequence_relation where 
  typed_bottom = "\<bottom>\<^sub>F" and typed_entails = typed.entails_\<G> and
  bottom = bottom and entails = entails
proof unfold_locales 

  have "bottom = snd ` \<bottom>\<^sub>F"
    using image_iff typed.bot_not_empty 
    by fastforce

  then show "bottom \<equiv> snd ` \<bottom>\<^sub>F"
    by argo
qed

sublocale untyped_inference_system where 
  inferences = inferences and typed_inferences = typed.inferences
proof unfold_locales

  {
    fix \<V> D \<V>' C
    have "typed.eq_factoring (\<V>, D) (\<V>', C) \<longleftrightarrow> eq_factoring D C"
      unfolding \<V>_all_same[of \<V>] \<V>_all_same[of \<V>']
    proof (rule iffI)
      assume "typed.eq_factoring (empty_typed D) (empty_typed C)"

      then show "eq_factoring D C"
      proof (cases rule: typed.eq_factoring.cases)
        case typed_eq_factoringI: eq_factoringI

        then show ?thesis
          by (intro eq_factoringI; (rule typed_eq_factoringI)?)
      qed
    next
      assume "eq_factoring D C"

      then show "typed.eq_factoring (empty_typed D) (empty_typed C)"
      proof (cases rule: eq_factoring.cases)
        case eq_factoringI

        then show ?thesis
          by (intro typed.eq_factoringI) (auto simp: case_unit_Unity)
      qed
    qed
  }

  then have "remove_types ` typed.eq_factoring_inferences = eq_factoring_inferences"
    by auto

  moreover {
    fix \<V> D \<V>' C
    have "typed.eq_resolution (\<V>, D) (\<V>', C) \<longleftrightarrow> eq_resolution D C"
      unfolding \<V>_all_same[of \<V>] \<V>_all_same[of \<V>']
    proof (rule iffI)
      assume "typed.eq_resolution (empty_typed D) (empty_typed C)"

      then show "eq_resolution D C"
      proof (cases rule: typed.eq_resolution.cases)
        case typed_eq_resolutionI: eq_resolutionI

        then show ?thesis
          by (intro eq_resolutionI; (rule typed_eq_resolutionI)?)
      qed
    next
      assume "eq_resolution D C"

      then show "typed.eq_resolution (empty_typed D) (empty_typed C)"
      proof (cases rule: eq_resolution.cases)
        case eq_resolutionI

        then show ?thesis
          by (intro typed.eq_resolutionI) (auto simp: case_unit_Unity)
      qed
    qed
  }

  then have "remove_types ` typed.eq_resolution_inferences = eq_resolution_inferences"
    by auto

  moreover {
    fix \<V>\<^sub>1 D \<V>\<^sub>2 E \<V>\<^sub>3 C
    have "typed.superposition (\<V>\<^sub>1, D) (\<V>\<^sub>2, E) (\<V>\<^sub>3, C) \<longleftrightarrow> superposition D E C"
      unfolding \<V>_all_same[of \<V>\<^sub>1] \<V>_all_same[of \<V>\<^sub>2] \<V>_all_same[of \<V>\<^sub>3]
    proof (rule iffI)
      assume "typed.superposition (empty_typed D) (empty_typed E) (empty_typed C)"

      then show "superposition D E C"
      proof (cases rule: typed.superposition.cases)
        case typed_superpositionI: superpositionI

        then show ?thesis
          by (intro superpositionI; (rule typed_superpositionI)?)
      qed
    next
      assume "superposition D E C"

      then show "typed.superposition (empty_typed D) (empty_typed E) (empty_typed C)"
      proof (cases rule: superposition.cases)
        case superpositionI

        show ?thesis
          by
            (intro typed.superpositionI; (rule superpositionI)?)
            (auto simp: case_unit_Unity)
      qed
    qed
  }

  then have "remove_types ` typed.superposition_inferences = superposition_inferences"
    by auto

  ultimately show "inferences \<equiv> remove_types ` typed.inferences"
    unfolding inferences_def typed.inferences_def image_Un
    by auto
qed

end

end