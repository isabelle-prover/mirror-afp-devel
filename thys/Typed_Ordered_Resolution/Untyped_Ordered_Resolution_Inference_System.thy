theory Untyped_Ordered_Resolution_Inference_System
  imports 
    Untyped_Ordered_Resolution
    First_Order_Clause.Untyped_Calculus
    Grounded_Ordered_Resolution
begin

context untyped_ordered_resolution_calculus
begin

sublocale typed: ordered_resolution_calculus where
  welltyped = "\<lambda>_ _ (). True"
  by
    unfold_locales
    (auto intro: term.ground_exists simp: term.exists_imgu right_unique_def split: unit.splits)

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
    have "typed.factoring (\<V>, D) (\<V>', C) \<longleftrightarrow> factoring D C"
      unfolding \<V>_all_same[of \<V>] \<V>_all_same[of \<V>']
    proof (rule iffI)
      assume "typed.factoring (empty_typed D) (empty_typed C)"

      then show "factoring D C"
      proof (cases rule: typed.factoring.cases)
        case typed_factoringI: factoringI

        then show ?thesis
          by (intro factoringI; (rule typed_factoringI)?)
      qed
    next
      assume "factoring D C"

      then show "typed.factoring (empty_typed D) (empty_typed C)"
      proof (cases rule: factoring.cases)
        case factoringI

        then show ?thesis
          by (intro typed.factoringI) (auto simp: case_unit_Unity)
      qed
    qed
  }

  then have "remove_types ` typed.factoring_inferences = factoring_inferences"
    by auto

  moreover {
    fix \<V>\<^sub>1 D \<V>\<^sub>2 E \<V>\<^sub>3 C
    have "typed.resolution (\<V>\<^sub>1, D) (\<V>\<^sub>2, E) (\<V>\<^sub>3, C) \<longleftrightarrow> resolution D E C"
      unfolding \<V>_all_same[of \<V>\<^sub>1] \<V>_all_same[of \<V>\<^sub>2] \<V>_all_same[of \<V>\<^sub>3]
    proof (rule iffI)
      assume "typed.resolution (empty_typed D) (empty_typed E) (empty_typed C)"

      then show "resolution D E C"
      proof (cases rule: typed.resolution.cases)
        case typed_resolutionI: resolutionI

        then show ?thesis
          by (intro resolutionI; (rule typed_resolutionI)?)
      qed
    next
      assume "resolution D E C"

      then show "typed.resolution (empty_typed D) (empty_typed E) (empty_typed C)"
      proof (cases rule: resolution.cases)
        case resolutionI

        show ?thesis
          by
            (intro typed.resolutionI; (rule resolutionI)?)
            (auto simp: case_unit_Unity)
      qed
    qed
  }

  then have "remove_types ` typed.resolution_inferences = resolution_inferences"
    by auto

  ultimately show "inferences \<equiv> remove_types ` typed.inferences"
    unfolding inferences_def typed.inferences_def image_Un
    by auto
qed

end

end