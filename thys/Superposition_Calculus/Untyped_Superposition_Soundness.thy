theory Untyped_Superposition_Soundness
  imports Grounded_Untyped_Superposition Superposition_Soundness
begin

context untyped_superposition_calculus
begin

sublocale sound_inference_system inferences bottom\<^sub>F entails_\<G>
proof unfold_locales
  fix \<iota>
  assume \<iota>: "\<iota> \<in> inferences"

  define \<iota>\<^sub>\<tau> :: "('f, 'v, unit) typed_clause inference" where 
    "\<iota>\<^sub>\<tau> \<equiv> empty_typed_inference \<iota>"

  have "typed.entails_\<G> (set (prems_of \<iota>\<^sub>\<tau>)) {concl_of \<iota>\<^sub>\<tau>}"
  proof (rule typed.sound)

    show "\<iota>\<^sub>\<tau> \<in> typed.inferences"
      using \<iota>
      unfolding typed_inferences \<iota>\<^sub>\<tau>_def
      by auto
  qed

  then show "entails_\<G> (set (prems_of \<iota>)) {concl_of \<iota>}"
    unfolding \<iota>\<^sub>\<tau>_def
    by (auto simp: UNION_singleton_eq_range)
qed

end

end
