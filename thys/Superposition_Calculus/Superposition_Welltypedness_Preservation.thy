theory Superposition_Welltypedness_Preservation
  imports Superposition
begin

context superposition_calculus
begin

lemma eq_resolution_preserves_typing:
  assumes "eq_resolution (D, \<V>) (C, \<V>)"
  shows "clause.is_welltyped \<V> D \<longleftrightarrow> clause.is_welltyped \<V> C"
  using assms
  by(cases "(D, \<V>)" "(C, \<V>)" rule: eq_resolution.cases) auto

lemma eq_factoring_preserves_typing:
  assumes "eq_factoring (D, \<V>) (C, \<V>)"
  shows "clause.is_welltyped \<V> D \<longleftrightarrow> clause.is_welltyped \<V> C"
  using assms
  by (cases "(D, \<V>)" "(C, \<V>)" rule: eq_factoring.cases) fastforce

lemma superposition_preserves_typing_C:
  assumes
    superposition: "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    E_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 E"
  shows "clause.is_welltyped \<V>\<^sub>3 C"
  using superposition
proof (cases "(D, \<V>\<^sub>2)" "(E, \<V>\<^sub>1)" "(C, \<V>\<^sub>3)" rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 l\<^sub>1 E' l\<^sub>2 D' \<P> c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

  then have welltyped_\<mu>:
    "term.subst.is_welltyped_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu>"
    by meson

  have "clause.is_welltyped \<V>\<^sub>3 (E \<cdot> \<rho>\<^sub>1)"
    using E_is_welltyped clause.is_welltyped.typed_renaming[OF superpositionI(3, 13)]
    by blast

  then have E\<mu>_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
    using welltyped_\<mu>
    by simp

  have "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2)"
    using D_is_welltyped clause.is_welltyped.typed_renaming[OF superpositionI(4, 14)]
    by blast

  then have D\<mu>_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
    using welltyped_\<mu>
    by simp

  have imgu: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> = t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>"
    using superpositionI(12) term.is_imgu_unifies_pair
    by auto

  from literal_cases[OF superpositionI(8)] E\<mu>_is_welltyped D\<mu>_is_welltyped imgu
  show ?thesis
    unfolding superpositionI
    by cases auto
qed

lemma superposition_preserves_typing_D:
  assumes
    superposition: "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)" and
    C_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 C"
  shows "clause.is_welltyped \<V>\<^sub>2 D"
  using superposition
proof (cases "(D, \<V>\<^sub>2)" "(E, \<V>\<^sub>1)" "(C, \<V>\<^sub>3)" rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 l\<^sub>1 E' l\<^sub>2 D' \<P> c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

  have \<mu>_is_welltyped:
    "term.subst.is_welltyped_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu>"
    using superpositionI(12)
    by blast

  show ?thesis
  proof-

    have "clause.is_welltyped \<V>\<^sub>2 D'"
    proof-
      have "clause.is_welltyped \<V>\<^sub>3 (D' \<cdot> \<rho>\<^sub>2)"
        using C_is_welltyped \<mu>_is_welltyped
        unfolding superpositionI
        by auto

      moreover have "\<forall>x\<in>clause.vars D'. \<V>\<^sub>2 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>2 x)"
        using superpositionI(14)
        unfolding superpositionI
        by simp

      ultimately show ?thesis
        using clause.is_welltyped.typed_renaming[OF superpositionI(4)]
        unfolding superpositionI
        by blast
    qed

    moreover have "literal.is_welltyped \<V>\<^sub>2 l\<^sub>2"
    proof-

      have \<V>\<^sub>2_\<V>\<^sub>3: "\<forall>x \<in> literal.vars l\<^sub>2. \<V>\<^sub>2 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>2 x)"
        using superpositionI(14)
        unfolding superpositionI
        by auto

      have "literal.is_welltyped \<V>\<^sub>3 (l\<^sub>2 \<cdot>l \<rho>\<^sub>2)"
      proof-
        obtain \<tau> where \<tau>: "welltyped \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>"
          using superpositionI(12)
          by force

        moreover obtain \<tau>' where \<tau>': "welltyped \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) \<tau>'"
        proof-
          have \<mu>_is_welltyped: "term.subst.is_welltyped_on (term.vars ((c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>)) \<V>\<^sub>3 \<mu>"
            using \<mu>_is_welltyped superpositionI(8)
            unfolding superpositionI
            by auto

          have "term.is_welltyped \<V>\<^sub>3 ((c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<cdot>t \<mu>)"
            using C_is_welltyped superpositionI(8)
            unfolding superpositionI
            by auto

          then show ?thesis
            unfolding term.welltyped.explicit_subst_stability[OF \<mu>_is_welltyped]
            using that term.welltyped.subterm
            by meson
        qed

        moreover have "\<tau> = \<tau>'"
        proof-
          have "welltyped \<V>\<^sub>2 t\<^sub>2 \<tau>" "welltyped \<V>\<^sub>2 t\<^sub>2' \<tau>'"
            using
              \<tau> \<tau>'
              superpositionI(12, 14)
              term.welltyped.explicit_typed_renaming[OF superpositionI(4)]
            unfolding superpositionI
            by(auto simp: Set.ball_Un)

          then show ?thesis
            using superpositionI(17)
            by (simp add: term.typed_if_welltyped)
        qed

        ultimately show ?thesis
          unfolding superpositionI
          by auto
      qed

      then show ?thesis
        using literal.is_welltyped.typed_renaming[OF superpositionI(4) \<V>\<^sub>2_\<V>\<^sub>3]
        unfolding superpositionI
        by simp
    qed

    ultimately show ?thesis
      unfolding superpositionI
      by simp
  qed
qed

lemma superposition_preserves_typing_E:
  assumes
    superposition: "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)" and
    C_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 C"
  shows "clause.is_welltyped \<V>\<^sub>1 E"
  using superposition
proof (cases "(D, \<V>\<^sub>2)" "(E, \<V>\<^sub>1)" "(C, \<V>\<^sub>3)" rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 l\<^sub>1 E' l\<^sub>2 D' \<P> c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

  have [simp]: "\<And>a \<sigma>. \<P> a \<cdot>l \<sigma> = \<P> (a \<cdot>a \<sigma>)"
    using superpositionI(8)
    by auto

  have [simp]: "\<And>\<V> a. literal.is_welltyped \<V> (\<P> a) \<longleftrightarrow> atom.is_welltyped \<V> a"
    using superpositionI(8)
    by (auto simp: literal_is_welltyped_iff_atm_of)

  have [simp]: "\<And>a. literal.vars (\<P> a) = atom.vars a"
    using superpositionI(8)
    by auto

  have \<mu>_is_welltyped:
    "term.subst.is_welltyped_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu>"
    using superpositionI(12)
    by blast

  show ?thesis
  proof-
    have "clause.is_welltyped \<V>\<^sub>1 E'"
    proof-
      have "clause.is_welltyped \<V>\<^sub>3 (E' \<cdot> \<rho>\<^sub>1)"
        using C_is_welltyped \<mu>_is_welltyped
        unfolding superpositionI
        by auto

      moreover have "\<forall>x\<in>clause.vars E'. \<V>\<^sub>1 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>1 x)"
        using superpositionI(13)
        unfolding superpositionI
        by simp

      ultimately show ?thesis
        using clause.is_welltyped.typed_renaming[OF superpositionI(3)]
        unfolding superpositionI
        by blast
    qed

    moreover have "literal.is_welltyped \<V>\<^sub>1 l\<^sub>1"
    proof-

      have \<V>\<^sub>1_\<V>\<^sub>3: "\<forall>x \<in> literal.vars l\<^sub>1. \<V>\<^sub>1 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>1 x)"
        using superpositionI(13)
        unfolding superpositionI
        by auto

      have "literal.is_welltyped \<V>\<^sub>3 (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)))"
      proof-

        have \<mu>_is_welltyped:
          "term.subst.is_welltyped_on
            (clause.vars (add_mset (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2)))
             \<V>\<^sub>3 \<mu>"
          using \<mu>_is_welltyped
          unfolding superpositionI
          by auto

        have "atom.is_welltyped \<V>\<^sub>3 (Upair (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) (t\<^sub>1 \<cdot>t \<rho>\<^sub>1))"
          using
            superpositionI(12)
            superposition_preserves_typing_D[OF superposition C_is_welltyped]
            clause.is_welltyped.typed_renaming[OF superpositionI(4) superpositionI(14)]
          unfolding superpositionI
          by auto

        moreover have "literal.is_welltyped \<V>\<^sub>3 (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)))"
          using C_is_welltyped
          unfolding superpositionI clause.is_welltyped.subst_stability[OF \<mu>_is_welltyped]
          by simp

        ultimately show ?thesis
          by auto
      qed

      then show ?thesis
        using literal.is_welltyped.typed_renaming[OF superpositionI(3) \<V>\<^sub>1_\<V>\<^sub>3]
        unfolding superpositionI
        by simp
    qed

    ultimately show ?thesis
      unfolding superpositionI
      by simp
  qed
qed

lemma superposition_preserves_typing:
  assumes "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"
  shows "clause.is_welltyped \<V>\<^sub>2 D \<and> clause.is_welltyped \<V>\<^sub>1 E \<longleftrightarrow> clause.is_welltyped \<V>\<^sub>3 C"
  using
    superposition_preserves_typing_C
    superposition_preserves_typing_D
    superposition_preserves_typing_E
    assms
  by blast

end

end
