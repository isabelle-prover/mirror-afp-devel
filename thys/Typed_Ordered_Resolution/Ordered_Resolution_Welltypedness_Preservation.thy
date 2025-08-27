theory Ordered_Resolution_Welltypedness_Preservation
  imports Grounded_Ordered_Resolution
begin

context ordered_resolution_calculus
begin

lemma factoring_preserves_typing:
  assumes factoring: "factoring (\<V>, C) (\<V>, D)"
  shows "clause.is_welltyped \<V> C \<longleftrightarrow> clause.is_welltyped \<V> D"
  using assms
proof (cases "(\<V>, C)" "(\<V>, D)" rule: factoring.cases)
  case (factoringI L\<^sub>1 \<mu> t\<^sub>1 t\<^sub>2 L\<^sub>2 C')

  show ?thesis
  proof (rule iffI)
    assume "clause.is_welltyped \<V> C" 
    then show "clause.is_welltyped \<V> D"
      using factoringI
      by simp
  next
    assume D_is_welltyped: "clause.is_welltyped \<V> D" 

    note imgu = factoringI(3, 4)

    have "clause.is_welltyped \<V> (add_mset L\<^sub>1 C')"
      using D_is_welltyped imgu
      unfolding factoringI
      by simp

    moreover have "literal.is_welltyped \<V> L\<^sub>2"
      using  D_is_welltyped term.imgu_same_type'[OF imgu] imgu
      unfolding factoringI 
      by force

    ultimately show "clause.is_welltyped \<V> C"
      unfolding factoringI
      by simp
  qed
qed

lemma resolution_preserves_typing:
  assumes
    resolution: "resolution (\<V>\<^sub>2, D) (\<V>\<^sub>1, C) (\<V>\<^sub>3, R)" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    C_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 C"
  shows "clause.is_welltyped \<V>\<^sub>3 R"
  using resolution
proof (cases "(\<V>\<^sub>2, D)" "(\<V>\<^sub>1, C)" "(\<V>\<^sub>3, R)" rule: resolution.cases)
  case (resolutionI \<rho>\<^sub>1 \<rho>\<^sub>2 \<mu> t\<^sub>1 t\<^sub>2 L\<^sub>1 L\<^sub>2 C' D')

  note \<mu>_type_preserving = resolutionI(6)

  have "clause.is_welltyped \<V>\<^sub>3 (C \<cdot> \<rho>\<^sub>1)"
    using C_is_welltyped clause.welltyped_renaming[OF resolutionI(3, 13)]
    by blast

  then have C\<mu>_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
    using \<mu>_type_preserving
    by simp

  moreover have "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2)"
    using D_is_welltyped clause.welltyped_renaming[OF resolutionI(4, 14)]
    by blast

  then have D\<mu>_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
    using \<mu>_type_preserving
    by simp

  ultimately show ?thesis
    unfolding resolutionI
    by auto
qed

end

end
