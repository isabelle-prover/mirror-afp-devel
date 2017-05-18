(*  Title:       EquivalenceOfCategories
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Equivalence of Categories"

text {*
  In this chapter we define the notions of equivalence and adjoint equivalence of categories
  and establish some properties of functors that are part of an equivalence.
*}

theory EquivalenceOfCategories
imports Adjunction
begin
  locale equivalence_of_categories =
    C: category C +
    D: category D +
    F: "functor" D C F +
    G: "functor" C D G +
    \<eta>: natural_isomorphism D D D.map "G o F" \<eta> +
    \<epsilon>: natural_isomorphism C C "F o G" C.map \<epsilon>
  for C :: "'c comp"
  and D :: "'d comp"
  and F :: "'d \<Rightarrow> 'c"
  and G :: "'c \<Rightarrow> 'd"
  and \<eta> :: "'d \<Rightarrow> 'd"
  and \<epsilon> :: "'c \<Rightarrow> 'c"
  begin

    lemma C_arr_expansion:
    assumes "C.arr f"
    shows "C (\<epsilon> (C.cod f)) (C (F (G f)) (C.inv (\<epsilon> (C.dom f)))) = f"
    and "C (C.inv (\<epsilon> (C.cod f))) (C f (\<epsilon> (C.dom f))) = F (G f)"
    proof -
      have \<epsilon>_dom: "C.inverse_arrows (\<epsilon> (C.dom f)) (C.inv (\<epsilon> (C.dom f)))"
        using assms \<epsilon>.components_are_iso C.inv_is_inverse by auto
      have \<epsilon>_cod: "C.inverse_arrows (\<epsilon> (C.cod f)) (C.inv (\<epsilon> (C.cod f)))"
        using assms \<epsilon>.components_are_iso C.inv_is_inverse by auto
      have "C (\<epsilon> (C.cod f)) (C (F (G f)) (C.inv (\<epsilon> (C.dom f))))
              = C (C (\<epsilon> (C.cod f)) (F (G f))) (C.inv (\<epsilon> (C.dom f)))"
        using assms \<epsilon>.preserves_hom C.inv_in_hom \<epsilon>.components_are_iso by force
      also have "... = C (C f (\<epsilon> (C.dom f))) (C.inv (\<epsilon> (C.dom f)))"
        using assms \<epsilon>.is_natural_1 \<epsilon>.is_natural_2 by simp
      also have "... = f"
        using assms \<epsilon>_dom \<epsilon>.preserves_hom C.inv_in_hom \<epsilon>.components_are_iso C.comp_arr_inv
        by force
      finally show "C (\<epsilon> (C.cod f)) (C (F (G f)) (C.inv (\<epsilon> (C.dom f)))) = f" by blast
      show "C (C.inv (\<epsilon> (C.cod f))) (C f (\<epsilon> (C.dom f))) = F (G f)"
        using assms \<epsilon>_cod \<epsilon>.preserves_hom C.inv_in_hom \<epsilon>.components_are_iso C.comp_inv_arr
              F.preserves_hom G.preserves_hom \<epsilon>.is_natural_1 \<epsilon>.is_natural_2
              C.comp_assoc [of "F (G f)" "\<epsilon> (C.cod f)" "C.inv (\<epsilon> (C.cod f))"]
        by force
    qed

    lemma G_is_faithful:
    shows "faithful_functor C D G"
    proof
      fix f f'
      assume par: "C.par f f'" and eq: "G f = G f'"
      show "f = f'"
      proof -
        have 1: "C.inv (\<epsilon> (C.cod f)) \<in> C.hom (C.cod f) (F (G (C.cod f))) \<and>
                 C.iso (C.inv (\<epsilon> (C.cod f)))"
          using par C.inv_in_hom \<epsilon>.components_are_iso C.iso_inv_iso
         by auto
        have 2: "\<epsilon> (C.dom f) \<in> C.hom (F (G (C.dom f))) (C.dom f) \<and>
                 C.iso (\<epsilon> (C.dom f))"
          using par \<epsilon>.preserves_hom [of "C.dom f" "C.dom f" "C.dom f"]
                \<epsilon>.components_are_iso [of "C.dom f"]
          by auto
        have 3: "C (C.inv (\<epsilon> (C.cod f))) (C f (\<epsilon> (C.dom f)))
                   = C (C.inv (\<epsilon> (C.cod f))) (C f' (\<epsilon> (C.dom f)))"
          using par C_arr_expansion eq by metis
        have 4: "C f (\<epsilon> (C.dom f)) = C f' (\<epsilon> (C.dom f))"
          using 1 2 3 par C.iso_is_section [of "C.inv (\<epsilon> (C.cod f))"]
                  C.section_is_mono [of "C.inv (\<epsilon> (C.cod f))"]
                  C.monoE [of "C.inv (\<epsilon> (C.cod f))" "C f (\<epsilon> (C.dom f))" "C f' (\<epsilon> (C.dom f))"]
          by simp
        show ?thesis
        proof -
          have "C.epi (\<epsilon> (C.dom f))"
            using 2 par C.iso_is_retraction C.retraction_is_epi by blast
          thus ?thesis using 1 2 4 par by fastforce
        qed
      qed
    qed

    lemma G_is_essentially_surjective:
    shows "essentially_surjective_functor C D G"
    proof
      have "\<And>b. D.ide b \<Longrightarrow> \<exists>a. C.ide a \<and> D.isomorphic (G a) b"
      proof
        fix b
        assume b: "D.ide b"
        show "C.ide (F b) \<and> D.isomorphic (G (F b)) b"
        proof (unfold D.isomorphic_def)
          have "C.ide (F b) \<and> D.inv (\<eta> b) \<in> D.hom (G (F b)) b \<and> D.iso (D.inv (\<eta> b))"
            using b \<eta>.components_are_iso D.inv_in_hom D.iso_inv_iso by simp
          thus "C.ide (F b) \<and> (\<exists>f. f \<in> D.hom (G (F b)) b \<and> D.iso f)" by blast
        qed
      qed
      thus "\<forall>b. D.ide b \<longrightarrow> (\<exists>a. C.ide a \<and> D.isomorphic (G a) b)"
        by blast
    qed

    interpretation \<epsilon>_inv: inverse_transformation C C "F o G" C.map \<epsilon> ..
    interpretation \<eta>_inv: inverse_transformation D D D.map "G o F" \<eta> ..
    interpretation GF: equivalence_of_categories D C G F \<epsilon>_inv.map \<eta>_inv.map ..

    lemma F_is_faithful:
    shows "faithful_functor D C F"
      using GF.G_is_faithful by simp

    lemma F_is_essentially_surjective:
    shows "essentially_surjective_functor D C F"
      using GF.G_is_essentially_surjective by simp

    lemma G_is_full:
    shows "full_functor C D G"
    proof
      fix a a' g
      assume a: "C.ide a" and a': "C.ide a'"
      assume g: "g \<in> D.hom (G a) (G a')"
      show "\<exists>f. f \<in> C.hom a a' \<and> G f = g"
      proof
        have \<epsilon>a: "C.inverse_arrows (\<epsilon> a) (C.inv (\<epsilon> a))"
          using a \<epsilon>.components_are_iso C.inv_is_inverse by auto
        have \<epsilon>a': "C.inverse_arrows (\<epsilon> a') (C.inv (\<epsilon> a'))"
          using a' \<epsilon>.components_are_iso C.inv_is_inverse by auto
        let ?f = "C (\<epsilon> a') (C (F g) (C.inv (\<epsilon> a)))"
        have f: "?f \<in> C.hom a a'"
          using a a' g \<epsilon>.preserves_hom C.inv_in_hom \<epsilon>.components_are_iso by simp
        moreover have "G ?f = g"
        proof -
          interpret F: faithful_functor D C F
            using F_is_faithful by auto
          have "F (G ?f) = F g"
          proof -
            have "F (G ?f) = C (C.inv (\<epsilon> a')) (C ?f (\<epsilon> a))"
              using f C_arr_expansion(2) [of "?f"] by auto
            also have "... = C (C (C.inv (\<epsilon> a')) (\<epsilon> a')) (C (C (F g) (C.inv (\<epsilon> a))) (\<epsilon> a))"
              using a a' g \<epsilon>.preserves_hom C.inv_in_hom \<epsilon>.components_are_iso
                    C.comp_assoc [of "C (C (F g) (C.inv (\<epsilon> a))) (\<epsilon> a)" "\<epsilon> a'" "C.inv (\<epsilon> a')"]
              by force
            also have "... = C (C (C.inv (\<epsilon> a')) (\<epsilon> a')) (C (F g) (C (C.inv (\<epsilon> a)) (\<epsilon> a)))"
              using a a' g \<epsilon>.preserves_hom C.inv_in_hom \<epsilon>.components_are_iso
                    C.comp_assoc [of "\<epsilon> a" "C.inv (\<epsilon> a)" "F g"]
              by auto
            also have "... = F g"
              using a a' \<epsilon>a \<epsilon>a' C.comp_inv_arr g \<epsilon>.preserves_hom by auto
            finally show ?thesis by blast
          qed
          thus ?thesis using f g F.is_faithful [of "G ?f" g] by force
        qed
        ultimately show "?f \<in> C.hom a a' \<and> G ?f = g" by blast
      qed
    qed

  end

  (* I'm not sure why I had to close and re-open the context here in order to
   * get the G_is_full fact in the interpretation GF. *)

  context equivalence_of_categories
  begin

    interpretation \<epsilon>_inv: inverse_transformation C C "F o G" C.map \<epsilon> ..
    interpretation \<eta>_inv: inverse_transformation D D D.map "G o F" \<eta> ..
    interpretation GF: equivalence_of_categories D C G F \<epsilon>_inv.map \<eta>_inv.map ..

    lemma F_is_full:
    shows "full_functor D C F"
      using GF.G_is_full by simp

  end

  text {*
    Traditionally the term "equivalence of categories" is also used for a functor
    that is part of an equivalence of categories.  However, it seems best to use
    that term for a situation in which all of the structure of an equivalence is
    explicitly given, and to have a different term for one of the functors involved.
  *}

  locale equivalence_functor =
    C: category C +
    D: category D +
    "functor" C D G
  for C :: "'c comp"
  and D :: "'d comp"
  and G :: "'c \<Rightarrow> 'd" +
  assumes induces_equivalence: "\<exists>F \<eta> \<epsilon>. equivalence_of_categories C D F G \<eta> \<epsilon>"

  sublocale equivalence_of_categories \<subseteq> equivalence_functor C D G
  proof
    show "\<exists>F \<eta> \<epsilon>. equivalence_of_categories C D F G \<eta> \<epsilon>"
    proof -
      have "equivalence_of_categories C D F G \<eta> \<epsilon>" ..
      thus ?thesis by blast
    qed
  qed

  text {*
    An equivalence functor is fully faithful and essentially surjective.
  *}

  sublocale equivalence_functor \<subseteq> fully_faithful_functor C D G
  proof -
    obtain F \<eta> \<epsilon> where 1: "equivalence_of_categories C D F G \<eta> \<epsilon>"
      using induces_equivalence by blast
    interpret equivalence_of_categories C D F G \<eta> \<epsilon>
      using 1 by auto
    show "fully_faithful_functor C D G"
      using G_is_full G_is_faithful fully_faithful_functor.intro by auto
  qed

  sublocale equivalence_functor \<subseteq> essentially_surjective_functor C D G
  proof -
    obtain F \<eta> \<epsilon> where 1: "equivalence_of_categories C D F G \<eta> \<epsilon>"
      using induces_equivalence by blast
    interpret equivalence_of_categories C D F G \<eta> \<epsilon>
      using 1 by auto
    show "essentially_surjective_functor C D G" using G_is_essentially_surjective by auto
  qed

  text {*
    A special case of an equivalence functor is an endofunctor @{text F} equipped with
    a natural isomorphism from @{text F} to the identity functor.
  *}

  locale endofunctor =
    "functor" A A F
  for A :: "'a comp"
  and F :: "'a \<Rightarrow> 'a"
  begin

    lemma isomorphic_to_identity_is_equivalence:
    assumes "natural_isomorphism A A F A.map \<phi>"
    shows "equivalence_functor A A F"
    proof -
      interpret \<phi>: natural_isomorphism A A F A.map \<phi>
         using assms by auto
      interpret \<phi>': inverse_transformation A A F A.map \<phi> ..
      interpret F\<phi>': natural_isomorphism A A F "F o F" "F o \<phi>'.map"
      proof -
        interpret \<tau>: horizontal_composite A A A A.map F F F \<phi>'.map F ..
        interpret F\<phi>': natural_transformation A A F "F o F" "F o \<phi>'.map"
        proof -
          have "F o A.map = F"
            using Functor.comp_ide_dom functor_axioms by blast
          thus "natural_transformation A A F (F o F) (F o \<phi>'.map)"
            using \<tau>.natural_transformation_axioms by simp
        qed
        show "natural_isomorphism A A F (F o F) (F o \<phi>'.map)"
          apply unfold_locales
          using preserves_iso \<phi>'.components_are_iso by fastforce
      qed
      interpret F\<phi>'o\<phi>': vertical_composite A A A.map F "F o F" \<phi>'.map "F o \<phi>'.map" ..
      interpret F\<phi>'o\<phi>': natural_isomorphism A A A.map "F o F" F\<phi>'o\<phi>'.map
        using \<phi>'.natural_isomorphism_axioms F\<phi>'.natural_isomorphism_axioms
              natural_isomorphisms_compose
        by fast
      interpret inv_F\<phi>'o\<phi>': inverse_transformation A A A.map "F o F" F\<phi>'o\<phi>'.map ..
      interpret F: equivalence_of_categories A A F F F\<phi>'o\<phi>'.map inv_F\<phi>'o\<phi>'.map ..
      show ?thesis ..
    qed

  end

  text {*
    An adjoint equivalence is an equivalence of categories that is also an adjunction.
  *}

  locale adjoint_equivalence =
    unit_counit_adjunction C D F G \<eta> \<epsilon> +
    \<eta>: natural_isomorphism D D D.map "G o F" \<eta> +
    \<epsilon>: natural_isomorphism C C "F o G" C.map \<epsilon>
  for C :: "'c comp"
  and D :: "'d comp"
  and F :: "'d \<Rightarrow> 'c"
  and G :: "'c \<Rightarrow> 'd"
  and \<eta> :: "'d \<Rightarrow> 'd"
  and \<epsilon> :: "'c \<Rightarrow> 'c"

  text {*
    An adjoint equivalence is clearly an equivalence of categories.
  *}

  sublocale adjoint_equivalence \<subseteq> equivalence_of_categories ..

  context adjoint_equivalence
  begin

    text {*
      The triangle identities for an adjunction reduce to inverse relations when
      @{text \<eta>} and @{text \<epsilon>} are natural isomorphisms.
    *}

    lemma triangle_G':
    assumes "C.ide a"
    shows "D.inverse_arrows (\<eta> (G a)) (G (\<epsilon> a))"
    proof
      have 1: "D (G (\<epsilon> a)) (\<eta> (G a)) = G a"
        using assms triangle_G G\<epsilon>o\<eta>G.map_simp_ide by fastforce
      thus "D.ide (D (G (\<epsilon> a)) (\<eta> (G a)))"
        using assms by simp
      hence "\<eta> (G a) = D.inv (G (\<epsilon> a))"
        using assms \<epsilon>.components_are_iso G.preserves_iso D.inverse_unique
              D.section_retraction_of_iso D.section_retractionI
        by metis
      thus "D.ide (D (\<eta> (G a)) (G (\<epsilon> a)))"
        using assms \<epsilon>.components_are_iso G.preserves_iso D.inv_is_inverse
              D.comp_inv_arr
        by simp
    qed

    lemma triangle_F':
    assumes "D.ide b"
    shows "C.inverse_arrows (F (\<eta> b)) (\<epsilon> (F b))"
    proof
      have 1: "C (\<epsilon> (F b)) (F (\<eta> b)) = F b"
        using assms triangle_F \<epsilon>FoF\<eta>.map_simp_ide by auto
      thus "C.ide (C (\<epsilon> (F b)) (F (\<eta> b)))"
        using assms by simp
      hence "C.inv (\<epsilon> (F b)) = F (\<eta> b)"
        using assms \<epsilon>.components_are_iso F.preserves_iso C.inverse_unique
              C.section_retraction_of_iso C.section_retractionI
        by simp
      thus "C.ide (C (F (\<eta> b)) (\<epsilon> (F b)))"
        using assms \<epsilon>.components_are_iso F.preserves_iso C.inv_is_inverse [of "\<epsilon> (F b)"]
              C.comp_inv_arr
        by simp
    qed

    text {*
      An adjoint equivalence can be dualized by interchanging the two functors and inverting
      the natural isomorphisms.  This is somewhat awkward to prove, but probably useful to have
      done it once and for all.
    *}

    lemma dual_equivalence:
    assumes "adjoint_equivalence C D F G \<eta> \<epsilon>"
    shows "adjoint_equivalence D C G F (inverse_transformation.map C C (C.map) \<epsilon>)
                                       (inverse_transformation.map D D (G o F) \<eta>)"
    proof -
      interpret adjoint_equivalence C D F G \<eta> \<epsilon> using assms by auto
      interpret \<epsilon>': inverse_transformation C C "F o G" C.map \<epsilon> ..
      interpret \<eta>': inverse_transformation D D D.map "G o F" \<eta> ..
      have 1: "G o (F o G) = (G o F) o G \<and> F o (G o F) = (F o G) o F" by auto
      interpret G\<epsilon>': natural_transformation C D G "(G o F) o G" "G o \<epsilon>'.map"
      proof -
        interpret G\<epsilon>': horizontal_composite C C D C.map "F o G" G G \<epsilon>'.map G ..
        show "natural_transformation C D G ((G o F) o G) (G o \<epsilon>'.map)"
          using 1 G\<epsilon>'.natural_transformation_axioms G.natural_transformation_axioms by auto
      qed
      interpret \<eta>'G: natural_transformation C D "(G o F) o G" G "\<eta>'.map o G"
      proof -
        interpret \<eta>'G: horizontal_composite C D D G G "G o F" D.map G \<eta>'.map ..
        show "natural_transformation C D ((G o F) o G) G (\<eta>'.map o G)"
          using 1 \<eta>'G.natural_transformation_axioms G.natural_transformation_axioms by auto
      qed
      interpret \<epsilon>'F: natural_transformation D C F "((F o G) o F)" "\<epsilon>'.map o F"
      proof -
        interpret \<epsilon>'F: horizontal_composite D C C F F C.map "F o G" F \<epsilon>'.map ..
        show "natural_transformation D C F ((F o G) o F) (\<epsilon>'.map o F)"
          using 1 \<epsilon>'F.natural_transformation_axioms F.natural_transformation_axioms by auto
      qed
      interpret F\<eta>': natural_transformation D C "(F o G) o F" F "F o \<eta>'.map"
      proof -
        interpret F\<eta>': horizontal_composite D D C "G o F" D.map F F \<eta>'.map F ..
        show "natural_transformation D C ((F o G) o F) F (F o \<eta>'.map)"
          using 1 F\<eta>'.natural_transformation_axioms F.natural_transformation_axioms by auto
      qed
      interpret F\<eta>'o\<epsilon>'F: vertical_composite D C F "(F o G) o F" F "\<epsilon>'.map o F" "F o \<eta>'.map" ..
      interpret \<eta>'GoG\<epsilon>': vertical_composite C D G "G o F o G" G "G o \<epsilon>'.map" "\<eta>'.map o G" ..
      show ?thesis
      proof
        show "\<eta>'GoG\<epsilon>'.map = G"
        proof (intro NaturalTransformation.eqI)
          show "natural_transformation C D G G G"
            using G.natural_transformation_axioms by auto
          show "natural_transformation C D G G \<eta>'GoG\<epsilon>'.map"
            using \<eta>'GoG\<epsilon>'.natural_transformation_axioms by auto
          show "\<And>a. C.ide a \<Longrightarrow> \<eta>'GoG\<epsilon>'.map a = G a"
          proof -
            fix a
            assume a: "C.ide a"
            show "\<eta>'GoG\<epsilon>'.map a = G a"
              using a \<eta>'GoG\<epsilon>'.map_simp_ide [of a] triangle_G'
                    \<eta>.components_are_iso \<epsilon>.components_are_iso G.preserves_ide
                    \<eta>'.inverts_components \<epsilon>'.inverts_components
                    D.inverse_unique G.preserves_inverse_arrows G\<epsilon>o\<eta>G.map_simp_ide
                    D.inverse_arrows_sym triangle_G
              by (metis o_apply)
          qed
        qed
        show "F\<eta>'o\<epsilon>'F.map = F"
        proof (intro NaturalTransformation.eqI)
          show "natural_transformation D C F F F"
            using F.natural_transformation_axioms by auto
          show "natural_transformation D C F F F\<eta>'o\<epsilon>'F.map"
            using F\<eta>'o\<epsilon>'F.natural_transformation_axioms by auto
          show "\<And>b. D.ide b \<Longrightarrow> F\<eta>'o\<epsilon>'F.map b = F b"
          proof -
            fix b
            assume b: "D.ide b"
            show "F\<eta>'o\<epsilon>'F.map b = F b"
              using b F\<eta>'o\<epsilon>'F.map_simp_ide [of b] \<epsilon>FoF\<eta>.map_simp_ide triangle_F triangle_F'
                    \<eta>.components_are_iso \<epsilon>.components_are_iso G.preserves_ide
                    \<eta>'.inverts_components \<epsilon>'.inverts_components F.preserves_ide
                    C.inverse_unique F.preserves_inverse_arrows C.inverse_arrows_sym
              by (metis o_apply)
          qed
        qed
      qed
    qed

  end

  text {*
    Notably absent here is a proof that a fully faithful and essentially surjective
    functor extends to an adjoint equivalence.  To prove this without repeating things
    that were already proved in @{theory Adjunction} requires that the development in
    that theory be modified to allow the unit or counit of the adjunction to be a specified
    initial or terminal arrow, rather than an arbitrarily chosen one.
    I did not need this result this time around, so it is left for the future.
  *}

end
