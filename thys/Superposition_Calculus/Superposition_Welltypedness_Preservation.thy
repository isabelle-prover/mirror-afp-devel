theory Superposition_Welltypedness_Preservation
  imports Superposition
begin

context superposition_calculus
begin

lemma eq_resolution_preserves_typing:
  assumes
    eq_resolution: "eq_resolution (\<V>, D) (\<V>, C)" and
    D_is_welltyed: "clause.is_welltyped \<V> D"
  shows "clause.is_welltyped \<V> C"
  using assms
  by (cases "(\<V>, D)" "(\<V>, C)" rule: eq_resolution.cases) auto
 
lemma eq_factoring_preserves_typing:
  assumes 
    eq_factoring: "eq_factoring (\<V>, D) (\<V>, C)" and
    D_is_welltyped: "clause.is_welltyped \<V> D"
  shows "clause.is_welltyped \<V> C"
  using eq_factoring D_is_welltyped
proof (cases "(\<V>, D)" "(\<V>, C)" rule: eq_factoring.cases)
  case (eq_factoringI l\<^sub>1 \<mu> t\<^sub>1 t\<^sub>1' t\<^sub>2 l\<^sub>2 D' t\<^sub>2')

  show ?thesis
    using D_is_welltyped term.imgu_same_type[OF _  eq_factoringI(5)] eq_factoringI(4)
    unfolding eq_factoringI
    by fastforce
qed

lemma superposition_preserves_typing:
  assumes
    superposition: "superposition (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C)" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    E_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 E"
  shows "clause.is_welltyped \<V>\<^sub>3 C"
  using superposition
proof (cases "(\<V>\<^sub>2, D)" "(\<V>\<^sub>1, E)" "(\<V>\<^sub>3, C)" rule: superposition.cases)
  case (superpositionI \<P> \<rho>\<^sub>1 \<rho>\<^sub>2 t\<^sub>1 \<mu> t\<^sub>2 c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 E' D')

  note [simp] = \<P>_simps[OF superpositionI(1)]

  have "clause.is_welltyped \<V>\<^sub>3 (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
    using E_is_welltyped clause.welltyped_renaming[OF superpositionI(4, 19)] superpositionI(8)
    by simp

  moreover have "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
    using D_is_welltyped clause.welltyped_renaming[OF superpositionI(5, 20)] superpositionI(8, 9)
    by simp

  moreover have "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> = t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>"
    using superpositionI(9) term.is_imgu_unifies_pair
    by auto
 
  ultimately show ?thesis
    unfolding superpositionI
    by auto
qed

lemma eq_resolution_weakly_welltyped_clause:
  assumes eq_resolution: "eq_resolution (\<V>, D) (\<V>, C)"
  shows "weakly_welltyped_clause \<V> D \<longleftrightarrow> weakly_welltyped_clause \<V> C"
  using eq_resolution
proof (cases "(\<V>, D)" "(\<V>, C)" rule: eq_resolution.cases)
  case (eq_resolutionI \<mu> t t' l D')

  show ?thesis
    using eq_resolutionI(1) imgu_weakly_welltyped_literal_Neg[OF _ eq_resolutionI(2)]
    unfolding eq_resolutionI
    by auto
qed 

lemma eq_factoring_weakly_welltyped_clause:
  assumes eq_factoring: "eq_factoring (\<V>, D) (\<V>, C)"
  shows "weakly_welltyped_clause \<V> D \<longleftrightarrow> weakly_welltyped_clause \<V> C"
  using eq_factoring
proof (cases "(\<V>, D)" "(\<V>, C)" rule: eq_factoring.cases)
  case (eq_factoringI l\<^sub>1 \<mu> t\<^sub>1 t\<^sub>1' t\<^sub>2 l\<^sub>2 D' t\<^sub>2')

  show ?thesis
    using eq_factoringI(4) imgu_weakly_welltyped_literal_Pos[OF _ eq_factoringI(5)]
    unfolding eq_factoringI
    by auto
qed

lemma superposition_weakly_welltyped_clause:
  assumes superposition: "superposition (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C)"
  shows 
    "weakly_welltyped_clause \<V>\<^sub>2 D \<and> weakly_welltyped_clause \<V>\<^sub>1 E \<longleftrightarrow>
     weakly_welltyped_clause \<V>\<^sub>3 C"
  using assms
proof (cases "(\<V>\<^sub>2, D)" "(\<V>\<^sub>1, E)" "(\<V>\<^sub>3, C)" rule: superposition.cases)
  case (superpositionI \<P> \<rho>\<^sub>1 \<rho>\<^sub>2 t\<^sub>1 \<mu> t\<^sub>2 c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 E' D')

  note [simp] = \<P>_simps[OF superpositionI(1)]

  have "weakly_welltyped_clause \<V>\<^sub>3 (E' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<longleftrightarrow> weakly_welltyped_clause \<V>\<^sub>1 E'"
    using
      weakly_welltyped_clause_renaming[OF superpositionI(4)] 
      superpositionI(8, 19)
    unfolding superpositionI
    by auto

  moreover have "weakly_welltyped_clause \<V>\<^sub>3 (D' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<longleftrightarrow> weakly_welltyped_clause \<V>\<^sub>2 D'"
    using
      weakly_welltyped_clause_renaming[OF superpositionI(5)] 
      superpositionI(8, 20)
    unfolding superpositionI
    by auto

  moreover have 
    "weakly_welltyped_literal \<V>\<^sub>3 (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) \<cdot>l \<mu>) \<longleftrightarrow>
      weakly_welltyped_literal \<V>\<^sub>2 (t\<^sub>2 \<approx> t\<^sub>2') \<and> weakly_welltyped_literal \<V>\<^sub>1 (\<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1'))"
  proof -
    
    have "\<forall>\<tau>. \<V>\<^sub>3 \<turnstile> t\<^sub>2 \<cdot>t \<rho>\<^sub>2 : \<tau> \<longleftrightarrow> \<V>\<^sub>3 \<turnstile> t\<^sub>1 \<cdot>t \<rho>\<^sub>1 : \<tau>"
    proof (rule term.imgu_same_type)

      show "term.is_imgu \<mu> {{t\<^sub>2 \<cdot>t \<rho>\<^sub>2, t\<^sub>1 \<cdot>t \<rho>\<^sub>1}}"
        using superpositionI(9)
        by (simp add: insert_commute)
    next
      show "type_preserving_on (term.vars (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<union> term.vars (t\<^sub>1 \<cdot>t \<rho>\<^sub>1)) \<V>\<^sub>3 \<mu>"
        using superpositionI(8)
        unfolding superpositionI
        by auto
    qed

    moreover have \<V>: "\<forall>x\<in>literal.vars (t\<^sub>2 \<approx> t\<^sub>2'). \<V>\<^sub>2 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>2 x)"
      using superpositionI(20)
      unfolding superpositionI
      by auto

    have type_preserving_l\<^sub>2: "weakly_welltyped_literal \<V>\<^sub>2 (t\<^sub>2 \<approx> t\<^sub>2')"
      using superpositionI(23)
      unfolding superpositionI .

    then have "weakly_welltyped_literal \<V>\<^sub>3 (t\<^sub>2 \<approx> t\<^sub>2' \<cdot>l \<rho>\<^sub>2)"
      unfolding weakly_welltyped_literal_renaming[OF superpositionI(5) \<V>] .

    then have  "\<forall>\<tau>. \<V>\<^sub>3 \<turnstile> t\<^sub>2 \<cdot>t \<rho>\<^sub>2 : \<tau> \<longleftrightarrow> \<V>\<^sub>3 \<turnstile> t\<^sub>2' \<cdot>t \<rho>\<^sub>2 : \<tau>"
      by auto

    ultimately have "\<forall>\<tau>. \<V>\<^sub>3 \<turnstile> t\<^sub>2' \<cdot>t \<rho>\<^sub>2 : \<tau> \<longleftrightarrow> \<V>\<^sub>3 \<turnstile> t\<^sub>1 \<cdot>t \<rho>\<^sub>1 : \<tau>"
      by auto      

    then have "weakly_welltyped_atom \<V>\<^sub>3 (Upair (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) (t\<^sub>1 \<cdot>t \<rho>\<^sub>1))"
      by auto     

    moreover have "type_preserving_on (atom.vars (Upair (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) (t\<^sub>1 \<cdot>t \<rho>\<^sub>1))) \<V>\<^sub>3 \<mu>"
      using superpositionI(8)
      unfolding superpositionI
      by auto

    ultimately have "weakly_welltyped_atom \<V>\<^sub>3 (Upair (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<cdot>a \<mu>)"
      by auto

    then have "\<And>\<tau>. \<V>\<^sub>3 \<turnstile> t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> : \<tau> \<longleftrightarrow> \<V>\<^sub>3 \<turnstile> t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> : \<tau>"
      by auto

    then have "\<And>\<tau>. \<V>\<^sub>3 \<turnstile> (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<cdot>t \<mu> : \<tau> \<longleftrightarrow> \<V>\<^sub>3 \<turnstile> (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> \<cdot>t \<mu> : \<tau>"
      by (smt (verit, ccfv_SIG) context.apply_context_subst term.welltyped_context_compatible
           term.welltyped_subterm)

    then have
      "weakly_welltyped_literal \<V>\<^sub>3 (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) \<cdot>l \<mu>) \<longleftrightarrow>
       weakly_welltyped_literal \<V>\<^sub>3 (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) \<cdot>l \<mu>)"
      by auto

    moreover have \<mu>: "type_preserving_on (literal.vars (\<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1') \<cdot>l \<rho>\<^sub>1)) \<V>\<^sub>3 \<mu>"
      using superpositionI(8)
      unfolding superpositionI
      by auto

    have "weakly_welltyped_literal \<V>\<^sub>3 (\<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1') \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) \<longleftrightarrow>
        weakly_welltyped_literal \<V>\<^sub>1 (\<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1'))"
      unfolding weakly_welltyped_literal_subst[OF \<mu>]
    proof (rule weakly_welltyped_literal_renaming[OF superpositionI(4)])
      show "\<forall>x\<in>literal.vars (\<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1')). \<V>\<^sub>1 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>1 x)"
        using superpositionI(19)
        unfolding superpositionI
        by auto
    qed

    ultimately show ?thesis
      using type_preserving_l\<^sub>2
      by auto
  qed

  ultimately show ?thesis
    unfolding superpositionI
    by auto
qed

end

end
