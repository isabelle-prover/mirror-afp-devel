theory Grounded_Untyped_Superposition
  imports Untyped_Superposition Grounded_Superposition
begin

context untyped_superposition_calculus
begin

sublocale typed: superposition_calculus where welltyped = "\<lambda>_ _ (). True"
proof unfold_locales
  show "right_unique (\<lambda>_ (). True)"
    unfolding right_unique_def
    by auto
next
  fix \<tau>
  show "\<exists>b. term.vars b = {} \<and> (case \<tau> of () \<Rightarrow> True)"
    by (auto simp: term.ground_exists split: unit.splits)
qed (auto split: unit.splits)

declare
  typed.term.welltyped_renaming [simp del]
  typed.term.welltyped_subst_stability [simp del]
  typed.term.welltyped_subst_stability_UNIV [simp del]

lemma all_infinite_variables_per_type [intro]: 
  fixes \<V> :: "'v \<Rightarrow> unit"
  shows "infinite_variables_per_type_on X \<V>"
  unfolding infinite_variables_per_type_on_def
  using infinite_UNIV
  by auto

lemma typed_eq_resolution_eq_eq_resolution [simp]: 
  "typed.eq_resolution (\<V>, D) (\<V>, C) \<longleftrightarrow> eq_resolution D C"
proof (rule iffI)
  assume "typed.eq_resolution (\<V>, D) (\<V>, C)"
  
  then show "eq_resolution D C"
  proof (cases rule: typed.eq_resolution.cases)
    case typed_eq_resolutionI: eq_resolutionI
    
    then show ?thesis
      by (intro eq_resolutionI) (auto simp: case_unit_Unity)
  qed
next
  assume "eq_resolution D C"

  then show "typed.eq_resolution (\<V>, D) (\<V>, C)"
  proof (cases rule: eq_resolution.cases)
    case eq_resolutionI
    
    then show ?thesis
      by (intro typed.eq_resolutionI) (auto simp: case_unit_Unity)
  qed
qed

lemma typed_eq_factoring_eq_eq_factoring [simp]: 
  "typed.eq_factoring (\<V>, D) (\<V>, C) \<longleftrightarrow> eq_factoring D C"
proof (rule iffI)
  assume "typed.eq_factoring (\<V>, D) (\<V>, C)"
  
  then show "eq_factoring D C"
  proof (cases rule: typed.eq_factoring.cases)
    case typed_eq_factoringI: eq_factoringI
    
    then show ?thesis
      by (intro eq_factoringI) (auto simp: case_unit_Unity)
  qed
next
  assume "eq_factoring D C"

  then show "typed.eq_factoring (\<V>, D) (\<V>, C)"
  proof (cases rule: eq_factoring.cases)
    case eq_factoringI
    
    then show ?thesis
      by (intro typed.eq_factoringI) (auto simp: case_unit_Unity)
  qed
qed

lemma typed_superposition_eq_superposition [simp]:
  "typed.superposition (\<V>\<^sub>1, D) (\<V>\<^sub>2, E) (\<V>\<^sub>3, C) \<longleftrightarrow> superposition D E C"
proof (rule iffI)
  assume "typed.superposition (\<V>\<^sub>1, D) (\<V>\<^sub>2, E) (\<V>\<^sub>3, C)"
  
  then show "superposition D E C"
  proof (cases rule: typed.superposition.cases)
    case typed_superpositionI: superpositionI
    
    show ?thesis
      by (intro superpositionI; (rule typed_superpositionI)?)
  qed
next
  assume "superposition D E C"

  then show "typed.superposition (\<V>\<^sub>1, D) (\<V>\<^sub>2, E) (\<V>\<^sub>3, C)"
  proof (cases rule: superposition.cases)
    case superpositionI
   
    show ?thesis
      by
        (intro typed.superpositionI; (rule superpositionI all_infinite_variables_per_type)?)
        (auto simp: case_unit_Unity)
  qed
qed

abbreviation bottom\<^sub>F :: "('f, 'v) atom clause set" where
  "bottom\<^sub>F \<equiv> {{#}}"

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv> { Infer [D] C | D C. eq_factoring D C }"

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv> { Infer [D] C | D C. eq_resolution D C }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [D, E] C | D E C. superposition D E C }"

definition inferences :: "('f, 'v) atom clause inference set" where
  "inferences \<equiv> superposition_inferences \<union> eq_resolution_inferences \<union> eq_factoring_inferences"

abbreviation empty_typed :: "'C \<Rightarrow> (('v \<Rightarrow> unit) \<times> 'C)" where
  "empty_typed C \<equiv> ((\<lambda>_. ()), C)"

abbreviation empty_typed_inference :: "'C inference \<Rightarrow> (('v \<Rightarrow> unit) \<times> 'C) inference" where
  "empty_typed_inference \<iota> \<equiv> Infer (map empty_typed (prems_of \<iota>)) (empty_typed (concl_of \<iota>))"

lemma \<V>_all_same [simp]:
  fixes \<V> :: "'v \<Rightarrow> unit"
  shows "\<V> = (\<lambda>_. ())"
  by auto

lemma typed_eq_factoring_inferences [simp]: 
  "typed.eq_factoring_inferences = empty_typed_inference ` eq_factoring_inferences"
proof -
  {
    fix D C \<V>\<^sub>1 \<V>\<^sub>2

    assume "typed.eq_factoring (\<V>\<^sub>1, D) (\<V>\<^sub>2, C)"

    then have "Infer [(\<V>\<^sub>1, D)] (\<V>\<^sub>2, C) \<in> empty_typed_inference ` eq_factoring_inferences"
      unfolding \<V>_all_same[of \<V>\<^sub>1] \<V>_all_same[of \<V>\<^sub>2]
      by force
  }

  then show ?thesis
    by auto
qed

lemma typed_eq_resolution_inferences [simp]: 
  "typed.eq_resolution_inferences = empty_typed_inference `  eq_resolution_inferences"
proof -
  {
    fix D C \<V>\<^sub>1 \<V>\<^sub>2

    assume "typed.eq_resolution (\<V>\<^sub>1, D) (\<V>\<^sub>2, C)"

    then have "Infer [(\<V>\<^sub>1, D)] (\<V>\<^sub>2, C) \<in> empty_typed_inference ` eq_resolution_inferences"
      unfolding \<V>_all_same[of \<V>\<^sub>1] \<V>_all_same[of \<V>\<^sub>2]
      by force
  }
  
  then show ?thesis
    by auto
qed

lemma typed_superposition_inferences [simp]: 
  "typed.superposition_inferences = empty_typed_inference ` superposition_inferences"
proof -
  {
    fix D E C \<V>\<^sub>1 \<V>\<^sub>2 \<V>\<^sub>3

    assume "typed.superposition (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C)"

    then have "Infer [(\<V>\<^sub>2, D), (\<V>\<^sub>1, E)] (\<V>\<^sub>3, C) \<in> empty_typed_inference ` superposition_inferences"
      unfolding \<V>_all_same[of \<V>\<^sub>1] \<V>_all_same[of \<V>\<^sub>2] \<V>_all_same[of \<V>\<^sub>3]
      by force
  }

  then show ?thesis
    by auto
qed

lemma typed_inferences [simp]: "typed.inferences = empty_typed_inference ` inferences"
  unfolding
    inferences_def
    typed.inferences_def
    typed_superposition_inferences
    typed_eq_resolution_inferences
    typed_eq_factoring_inferences
  by auto

(* TODO: tiebreaker ? *)
sublocale standard_lifting where 
  Bot_F = bottom\<^sub>F and
  Inf_F = inferences and
  Bot_G  = typed.bottom\<^sub>F and
  entails_G = typed.entails_\<G> and
  Inf_G = typed.inferences and
  Red_I_G = typed.Red_I and
  Red_F_G = typed.Red_F and
  \<G>_F = "\<lambda>C. {empty_typed C}" and
  \<G>_I = "\<lambda>\<iota>. Some {empty_typed_inference \<iota>}"
proof unfold_locales
  fix \<iota>

  assume "\<iota> \<in> inferences"

  then have "empty_typed_inference \<iota> \<in> typed.inferences"
    by simp

  then have "empty_typed_inference \<iota> \<in> typed.Red_I_\<G> {empty_typed (concl_of \<iota>)}"
    by (rule typed.Red_I_of_Inf_to_N) simp

  then show "the (Some {empty_typed_inference \<iota>}) \<subseteq> typed.Red_I_\<G> {empty_typed (concl_of \<iota>)}"
    by simp
qed auto

end

end