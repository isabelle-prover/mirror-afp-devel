theory MLSSmf_to_MLSS_Correctness
  imports MLSSmf_to_MLSS_Soundness MLSSmf_to_MLSS_Completeness
begin

fun reduce :: "('v, 'f) MLSSmf_clause \<Rightarrow> ('v, 'f) Composite pset_fm set set" where
  "reduce \<C> = normalized_MLSSmf_clause.reduced_dnf \<C>"

fun interp_DNF :: "(('v, 'f) Composite \<Rightarrow> hf) \<Rightarrow> ('v, 'f) Composite pset_fm set set \<Rightarrow> bool" where
  "interp_DNF \<M> clauses \<longleftrightarrow> (\<exists>clause \<in> clauses. \<forall>lt \<in> clause. interp I\<^sub>s\<^sub>a \<M> lt)"

corollary MLSSmf_to_MLSS_correct:
  assumes "norm_clause \<C>"
    shows "(\<exists>M\<^sub>v M\<^sub>f. I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C>) \<longleftrightarrow> (\<exists>\<M>. interp_DNF \<M> (reduce \<C>))"
proof
  from assms interpret normalized_MLSSmf_clause \<C> by unfold_locales
  assume "\<exists>M\<^sub>v M\<^sub>f. I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C>"
  with MLSSmf_to_MLSS_soundness obtain \<M> where "is_model_for_reduced_dnf \<M>"
    using assms by blast
  then have "interp_DNF \<M> (reduce \<C>)" unfolding is_model_for_reduced_dnf_def by simp
  then show "\<exists>\<M>. interp_DNF \<M> (reduce \<C>)" by blast
next
  from assms interpret normalized_MLSSmf_clause \<C> by unfold_locales
  assume "\<exists>\<M>. interp_DNF \<M> (reduce \<C>)"
  then obtain \<M> where "interp_DNF \<M> (reduce \<C>)" by blast
  then have "is_model_for_reduced_dnf \<M>" unfolding is_model_for_reduced_dnf_def by simp
  with MLSSmf_to_MLSS_completeness show "\<exists>M\<^sub>v M\<^sub>f. I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C>" by blast
qed

end