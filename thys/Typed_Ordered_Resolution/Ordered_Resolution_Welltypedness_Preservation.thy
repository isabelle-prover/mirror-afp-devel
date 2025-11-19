theory Ordered_Resolution_Welltypedness_Preservation
  imports Grounded_Ordered_Resolution
begin

context ordered_resolution_calculus
begin

lemma factoring_preserves_typing:
  assumes factoring: "factoring (\<V>, D) (\<V>, C)"
  shows "clause.is_welltyped \<V> D \<longleftrightarrow> clause.is_welltyped \<V> C"
  using assms
proof (cases "(\<V>, D)" "(\<V>, C)" rule: factoring.cases)
  case (factoringI l\<^sub>1 \<mu> t\<^sub>1 t\<^sub>2 l\<^sub>2 D')
 
  show ?thesis
  proof (rule iffI)
    assume "clause.is_welltyped \<V> D" 
    then show "clause.is_welltyped \<V> C"
      using factoringI
      by simp
  next
    assume C_is_welltyped: "clause.is_welltyped \<V> C" 

    note imgu = factoringI(3, 4)

    have "clause.is_welltyped \<V> (add_mset l\<^sub>1 D')"
      using C_is_welltyped imgu
      unfolding factoringI
      by simp

    moreover have "literal.is_welltyped \<V> l\<^sub>2"
      using C_is_welltyped term.imgu_same_type[OF imgu] imgu
      unfolding factoringI
      by force

    ultimately show "clause.is_welltyped \<V> D"
      unfolding factoringI
      by simp
  qed
qed

lemma resolution_preserves_typing:
  assumes
    resolution: "resolution (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C)" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    E_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 E"
  shows "clause.is_welltyped \<V>\<^sub>3 C"
  using resolution
proof (cases "(\<V>\<^sub>2, D)" "(\<V>\<^sub>1, E)" "(\<V>\<^sub>3, C)" rule: resolution.cases)
  case (resolutionI \<rho>\<^sub>1 \<rho>\<^sub>2 \<mu> t\<^sub>1 t\<^sub>2 l\<^sub>1 l\<^sub>2 E' D')

  note \<mu>_type_preserving = resolutionI(6)

  have "clause.is_welltyped \<V>\<^sub>3 (E \<cdot> \<rho>\<^sub>1)"
    using E_is_welltyped clause.welltyped_renaming[OF resolutionI(3, 13)]
    by blast

  then have E\<mu>_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
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
