theory Untyped_Superposition_Completeness
  imports Grounded_Untyped_Superposition Superposition_Completeness
begin

context untyped_superposition_calculus
begin

sublocale statically_complete_calculus bottom\<^sub>F inferences entails_\<G> Red_I_\<G> Red_F_\<G>
proof unfold_locales
  fix b N

  assume
    bottom: "b \<in> bottom\<^sub>F" and
    saturated: "saturated N" and
    entails_\<G>: "entails_\<G> N {b}"

  have "\<exists>b\<in>\<bottom>\<^sub>F. b \<in> (\<Union>C\<in>N. {empty_typed C})"
  proof (rule typed.statically_complete)

    show "empty_typed b \<in> \<bottom>\<^sub>F"
      using bottom
      by auto
  next

    show "typed.saturated (\<Union>C\<in>N. {empty_typed C})"
    proof (rule sat_imp_ground_sat[OF saturated])

      have "typed.Inf_from (empty_typed ` N) = {\<iota>. \<exists>\<iota>'\<in>Inf_from N. \<iota> = empty_typed_inference \<iota>'}"
        unfolding typed.Inf_from_def Inf_from_def
        by fastforce

      then show "ground_Inf_overapproximated N"
        unfolding UNION_singleton_eq_range
        by auto
    qed
  next

    show "typed.entails_\<G> (\<Union>C\<in>N. {empty_typed C}) {empty_typed b}"
      using entails_\<G>
      by auto
  qed

  then show "\<exists>B'\<in>bottom\<^sub>F. B' \<in> N"
    by blast
qed

end

end
