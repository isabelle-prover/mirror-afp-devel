(*  Title:       Category3Adapter
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Extensions to AFP Article `Category3'"

  text {*
    This theory contains some extensions to the author's previous AFP article \cite{Category3-AFP},
    most of which are used in the present work.  Upon acceptance of the present submission
    it is proposed to integrate these extensions into the previous article and delete this adapter
    theory in a subsequent AFP release cycle.
  *}

theory Category3Adapter
imports "../Category3/Adjunction"
begin

  section "Extensions to `Category'"

  context category
  begin

    text {*
      As I have gotten more experience in using the framework from \cite{Category3-AFP},
      my usage has become more stylized.  I have found it useful to have available an
      `X in hom' lemma for most definitions `X' that are made that relate to arrows in
      a category.  The following fact does this for composition in a category and is included
      for uniformity and convenience.
    *}

    lemma comp_in_hom:
    assumes "arr f" and "arr g" and "cod f = dom g"
      shows "C g f \<in> hom (dom f) (cod g)"
        using assms by simp

    text {*
      It is occasionally useful to have available the facts that the functions @{term dom}
      and @{term cod} preseve @{term null}.
    *}

    lemma dom_null:
    shows "dom null = null"
      using has_domD(1) dom_def not_arr_null by auto
 
    lemma cod_null:
    shows "cod null = null"
      using has_codD(1) cod_def not_arr_null by auto

    text {*
      The next two results are sometimes useful for performing manipulations at the
      head of a chain of composed arrows.  I have adopted the convention that such
      chains are canonically represented in right-associated form.  This makes it
      easy to perform manipulations at the ``tail'' of a chain, but more difficult
      to perform them at the ``head''.  These results take care of the rote manipulations
      using associativity that are needed to either permute or combine arrows at the
      head of a chain.
    *}

    lemma comp_permute:
    assumes "C f g = C k l" and "seq f g" and "seq g h"
    shows "C f (C g h) = C k (C l h)"
      using assms comp_assoc
      by (metis (full_types) arr_comp arr_compD(1) arr_compD(2) arr_compD(3) dom_comp)

    lemma comp_reduce:
    assumes "C f g = k" and "seq f g" and "seq g h"
    shows "C f (C g h) = C k h"
      using assms by auto
    
  end

  section "Extensions to `EpiMonoIso'"

  context category
  begin

    text {*
      The next several facts provide some conveniences when working with inverse arrows.
    *}

    lemma comp_arr_inv:
    assumes "inverse_arrows f g"
    shows "C f g = dom g"
    proof -
      have "ide (C f g)" using assms inverse_arrows_def by blast
      thus "C f g = dom g" using assms inverse_arrows_def dom_comp [of g f] by auto
    qed

    lemma comp_inv_arr:
    assumes "inverse_arrows f g"
    shows "C g f = dom f"
    proof -
      have "ide (C g f)" using assms inverse_arrows_def by blast
      thus "C g f = dom f" using assms inverse_arrows_def dom_comp [of f g] by auto
    qed

    lemma inv_in_hom [simp]:
    assumes "iso f"
    shows "inv f \<in> hom (cod f) (dom f)"
    proof -
      have "inverse_arrows f (inv f)"
        using assms inv_is_inverse by blast
      then show ?thesis
        by (simp add: inverse_arrowsD(1))
    qed

    lemma inv_comp:
    assumes "iso f" and "iso g" and "seq g f"
    shows "inv (C g f) = C (inv f) (inv g)"
    proof -
      have f: "inverse_arrows f (inv f)"
        using assms(1) inv_is_inverse by blast
      have g: "inverse_arrows g (inv g)"
        using assms(2) inv_is_inverse by blast
      have "inverse_arrows (C g f) (C (inv f) (inv g))"
      proof
        show "antipar (C g f) (C (inv f) (inv g))"
          using assms inv_in_hom by simp
        show "ide (C (C g f) (C (inv f) (inv g)))"
          using assms f g inv_in_hom comp_assoc [of "inv g" "inv f" f] comp_arr_inv by simp
        show "ide (C (C (inv f) (inv g)) (C g f))"
          using assms f g inv_in_hom comp_assoc [of f g "inv g"] comp_inv_arr by simp
      qed
      thus ?thesis using inverse_unique by auto
    qed

    text {*
      There is no need for the `antipar' condition in the original version of
      @{text "section_retraction"} in @{theory EpiMonoIso}.
      The introduction rule can be strengthened to eliminate that assumption,
      as in the following fact.
    *}

    lemma section_retractionI':
    assumes "ide (C e m)"
    shows "section_retraction m e"
      using assms section_retraction_def [of m e]
      by (metis arr_compD(2) arr_compD(3) arr_dom_iff_arr cod_comp ideD(1) ideD(3) ide_comp_simp)

    text {*
      A section or retraction of an isomorphism is in fact an inverse.
    *}

    lemma section_retraction_of_iso:
    assumes "iso f"
    shows "section_retraction f g \<Longrightarrow> inverse_arrows f g"
    and "section_retraction g f \<Longrightarrow> inverse_arrows f g"
    proof -
      assume fg: "section_retraction f g"
      show "inverse_arrows f g"
      proof
        show 1: "antipar f g" using fg by auto
        show "ide (C g f)" using fg by auto
        show "ide (C f g)"
        proof -
          have "C g f = dom f" using fg ide_comp_simp by auto
          hence "inv f = C (C g f) (inv f)"
            using assms 1 inv_in_hom by simp
          also have "... = g"
            using assms 1 inv_in_hom inv_is_inverse comp_arr_inv by force
          finally have "g = inv f" by simp
          thus ?thesis
            using assms 1 inv_is_inverse comp_inv_arr by force
        qed
      qed
      next
      assume fg: "section_retraction g f"
      show "inverse_arrows f g"
      proof
        show 1: "antipar f g" using fg by auto
        show "ide (C f g)" using fg by auto
        show "ide (C g f)"
        proof -
          have "inverse_arrows f (inv f)"
            using assms inv_is_inverse by blast
          have "C f g = dom g" using fg ide_comp_simp by auto
          hence "inv f = C (inv f) (C f g)"
            using assms 1 inv_in_hom by simp
          also have "... = C (C (inv f) f) g"
            using assms fg 1 inv_in_hom inv_is_inverse by simp
          also have "... = g"
            using assms fg 1 inv_in_hom inv_is_inverse comp_inv_arr by simp
          finally have "g = inv f" by simp
          thus ?thesis
            using assms 1 inv_is_inverse comp_arr_inv by force
        qed
      qed
    qed

    text {*
      A situation that occurs frequently is that we have a commuting triangle,
      but we need the triangle obtained by inverting one side that is an isomorphism.
      The following fact streamlines this derivation.
    *}

    lemma invert_side_of_triangle:
    assumes "seq f g" and "C f g = h"
    shows "iso f \<Longrightarrow> seq (inv f) h \<and> g = C (inv f) h"
    and "iso g \<Longrightarrow> seq h (inv g) \<and> f = C h (inv g)"
    proof -
      assume f: "iso f"
      have "seq (inv f) h"
        using assms f inv_in_hom by auto
      moreover have "g = C (inv f) h"
      proof -
        have "g = C (C (inv f) f) g"
          using assms f comp_inv_arr inv_is_inverse by simp
        also have "... = C (inv f) h"
          using assms f inv_in_hom by simp
        finally show ?thesis by blast
      qed
      ultimately show "seq (inv f) h \<and> g = C (inv f) h" by simp
      next
      assume g: "iso g"
      have "seq h (inv g)"
        using assms g inv_in_hom by auto
      moreover have "f = C h (inv g)"
      proof -
        have "f = C f (C g (inv g))"
          using assms g comp_arr_inv inv_is_inverse inv_in_hom by simp
        also have "... = C h (inv g)"
          using assms g inv_in_hom by auto
        finally show ?thesis by blast
      qed
      ultimately show "seq h (inv g) \<and> f = C h (inv g)" by simp
    qed

    text {*
      A similar situation is where we have a commuting square and we want to
      invert two opposite sides.
    *}

    lemma invert_opposite_sides_of_square:
    assumes "seq f g" and "seq h k" and "C f g = C h k"
    shows "\<lbrakk> iso f; iso k \<rbrakk> \<Longrightarrow> seq g (inv k) \<and> seq (inv f) h \<and> C g (inv k) = C (inv f) h"
    proof -
      assume f: "iso f" and k: "iso k"
      have "dom g = dom k \<and> cod f = cod h"
        using assms by (metis cod_comp dom_comp)
      hence 1: "seq g (inv k) \<and> seq (inv f) h"
        using assms f k inv_in_hom by simp
      moreover have "C g (inv k) = C (inv f) h"
      proof -
        have "g = C (inv f) (C h k)"
          using assms f invert_side_of_triangle(1) [of g f "C h k"] by simp
        hence "g = C (C (inv f) h) k"
          using assms f 1 inv_in_hom inv_is_inverse by simp
        thus ?thesis
          using assms k 1 invert_side_of_triangle(2) [of k "C (inv f) h" g] by simp
      qed
      ultimately show ?thesis by blast
    qed

  end

  section "Extensions to `ProductCategory'"

  context product_category
  begin

    text {*
      It is helpful to have explicit characterizations of isomorphisms and inverses in
      a product category.
    *}

    lemma iso_char:
    shows "iso f \<longleftrightarrow> C1.iso (fst f) \<and> C2.iso (snd f)"
    proof
      assume f: "iso f"
      obtain g where g: "inverse_arrows f g" using f by auto
      have "C1.inverse_arrows (fst f) (fst g)"
      proof
        show "C1.antipar (fst f) (fst g)" using f g by auto
        have 1: "ide (comp f g) \<and> ide (comp g f)" using f g by blast
        show "C1.ide (C1 (fst f) (fst g))" using 1 f g ide_char by auto
        show "C1.ide (C1 (fst g) (fst f))" using 1 f g ide_char by auto
      qed
      moreover have "C2.inverse_arrows (snd f) (snd g)"
      proof
        show "C2.antipar (snd f) (snd g)" using f g by auto
        have 1: "ide (comp f g) \<and> ide (comp g f)" using f g by blast
        show "C2.ide (C2 (snd f) (snd g))" using 1 f g ide_char by auto
        show "C2.ide (C2 (snd g) (snd f))" using 1 f g ide_char by auto
      qed
      ultimately show "C1.iso (fst f) \<and> C2.iso (snd f)" by auto
      next
      assume f: "C1.iso (fst f) \<and> C2.iso (snd f)"
      obtain g1 where g1: "C1.inverse_arrows (fst f) g1" using f by blast
      obtain g2 where g2: "C2.inverse_arrows (snd f) g2" using f by blast
      have "inverse_arrows f (g1, g2)"
        using f g1 g2 dom_char ide_char comp_char by (intro inverse_arrowsI; auto)
      thus "iso f" by auto
    qed

    lemma inv_char:
    assumes "iso f"
    shows "inv f = (C1.inv (fst f), C2.inv (snd f))"
    proof -
      have "inverse_arrows f (C1.inv (fst f), C2.inv (snd f))"
      proof
        have 1: "C1.inverse_arrows (fst f) (C1.inv (fst f))"
          using assms iso_char C1.inv_is_inverse by simp
        have 2: "C2.inverse_arrows (snd f) (C2.inv (snd f))"
          using assms iso_char C2.inv_is_inverse by simp
        show "antipar f (C1.inv (fst f), C2.inv (snd f))"
          using 1 2 arr_char dom_char cod_char by auto
        show "ide (comp (C1.inv (fst f), C2.inv (snd f)) f)"
          using 1 2 ide_char comp_char C1.comp_inv_arr C2.comp_inv_arr by auto
        show "ide (comp f (C1.inv (fst f), C2.inv (snd f)))"
          using 1 2 ide_char comp_char C1.comp_arr_inv C2.comp_arr_inv by auto
      qed
      thus ?thesis using inverse_unique by auto
    qed

  end

  section "Extensions to `Functor'"

  text {*
    It is convenient to have an easy way to obtain from a category the identity functor
    on that category. The following declaration causes the definitions and facts from the
    @{locale identity_functor} locale to be inherited by the @{locale category} locale,
    including the function @{term map} on arrows that represents the identity functor.
    This makes it generally unnecessary to give explicit interpretations of
    @{locale identity_functor}.
  *}

  sublocale category \<subseteq> identity_functor C ..

  text {*
    The following are some useful additional preservation properties of functors.
  *}

  context "functor"
  begin

    lemma preserves_section_retraction:
    assumes "A.section_retraction m e"
    shows "B.section_retraction (F m) (F e)"
      using assms
      by (metis (mono_tags, lifting) A.section_retractionD(1) A.section_retractionD(2)
          A.section_retractionD(3) A.section_retractionD(4) A.section_retractionD(5)
          B.section_retractionI preserves_arr preserves_cod
          preserves_comp_2 preserves_dom preserves_ide)

    lemma preserves_section:
    assumes "A.section m"
    shows "B.section (F m)"
      using assms
      by (meson A.sectionE B.section_def preserves_section_retraction)

    lemma preserves_retraction:
    assumes "A.retraction e"
    shows "B.retraction (F e)"
      using assms
      by (meson A.retractionE B.retraction_def preserves_section_retraction)

    lemma preserves_inverse_arrows:
    assumes "A.inverse_arrows f g"
    shows "B.inverse_arrows (F f) (F g)"
      using assms A.inverse_arrowsD(1) A.inverse_arrowsD(2) A.inverse_arrowsD(3) A.is_functor
            B.arr_compD(1) B.ideD(1) B.inverse_arrowsI category.ide_comp_simp functor_def
            preserves_cod preserves_comp_2 preserves_dom preserves_ide
      by (metis (no_types, hide_lams))

    lemma preserves_inv:
    assumes "A.iso f"
    shows "F (A.inv f) = B.inv (F f)"
      using assms preserves_inverse_arrows A.inv_is_inverse B.inv_is_inverse
            B.inverse_arrow_unique
      by blast

  end

  text {*
    Inverse functors uniquely determine each other.
  *}

  lemma inverse_functor_eq:
  assumes "inverse_functors C D F G" and "inverse_functors C D F G'"
  shows "G = G'"
  proof -
    interpret FG: inverse_functors C D F G using assms(1) by auto
    interpret FG': inverse_functors C D F G' using assms(2) by auto
    show "G = G'"
    proof
      fix x
      have "\<not>FG.B.arr x \<Longrightarrow> G x = G' x"
        using FG.G.is_extensional FG'.G.is_extensional by presburger
      moreover have "FG.B.arr x \<Longrightarrow> G x = G' x"
      proof -
        assume x: "FG.B.arr x"
        have "G x = (G' o F) (G x)" using x FG'.inv by fastforce
        also have "... = G' ((F o G) x)" by simp
        also have "... = G' x" using x FG.inv' by simp
        finally show "G x = G' x" by auto
      qed
      ultimately show "G x = G' x" by blast
    qed
  qed

  lemma inverse_functor_eq':
  assumes "inverse_functors C D F G" and "inverse_functors C D F' G"
  shows "F = F'"
    using assms inverse_functors_sym inverse_functor_eq by blast

  context invertible_functor
  begin

    lemma has_unique_inverse:
      shows "\<exists>!G. inverse_functors A B F G"
        using invertible inverse_functor_eq by blast

    definition the_inverse
    where "the_inverse \<equiv> THE G. inverse_functors A B F G"

    interpretation inverse_functors A B F the_inverse
      using the_inverse_def has_unique_inverse theI' [of "\<lambda>G. inverse_functors A B F G"]
      by simp

    lemma the_inverse_is_inverse:
    shows "inverse_functors A B F the_inverse" ..

  end

  sublocale invertible_functor \<subseteq> inverse_functors A B F the_inverse
    using the_inverse_is_inverse by simp

  section "Extensions to `NaturalTransformation'"

  text {*
    In the original version of theory @{theory NaturalTransformation} the naturality
    condition was split into two conditions: @{text is_natural_1} and @{text is_natural_2}
    which each express the equality of the diagonal of a naturality square with the
    composition of two of the sides.  These conditions are often used in combination,
    and the following fact caters to such situations.
  *}

  context natural_transformation
  begin

    lemma naturality:
    assumes "A.arr f"
    shows "B (G f) (\<tau> (A.dom f)) = B (\<tau> (A.cod f)) (F f)"
      using assms is_natural_1 is_natural_2 by simp

  end

  text {*
    The original version of theory @{theory NaturalTransformation} identified a functor
    with the corresponding identity natural transformation.  Since the function that
    represents a functor is formally identical to the function that represents the
    corresponding identity natural transformation, no additional locale was needed for
    identity natural transformations.  However, an identity natural transformation is also
    a natural isomorphism, so it is useful for @{locale functor} to inherit from the
    @{locale natural_isomorphism} locale.
  *}

  sublocale "functor" \<subseteq> natural_isomorphism A B F F F
    apply unfold_locales
    using preserves_ide B.ide_is_iso by simp

  context natural_isomorphism
  begin

    text {*
      Natural isomorphisms preserve isomorphisms, in the sense that the sides of
      of the naturality square determined by an isomorphism are all isomorphisms,
      so the diagonal is, as well.
    *}

    lemma preserves_iso:
    assumes "A.iso f"
    shows "B.iso (\<tau> f)"
      using assms G.preserves_iso components_are_iso B.isos_compose
      by (metis A.arr_cod_iff_arr A.dom_cod A.ide_cod A.iso_is_arr F.preserves_dom F.preserves_iso
          F.preserves_seq is_natural_2 preserves_arr preserves_dom)

  end
  
  section "Subcategory"

  text{*
    The following locale gives a construction of the subcategory of a category
    defined by a predicate on arrows subject to closure conditions.  The arrows of
    the subcategory are directly identified with the arrows of the ambient category.
  *}

  locale subcategory =
    C: category C
    for C :: "'a comp"
    and Arr :: "'a \<Rightarrow> bool" +
    assumes Arr_implies_arr: "Arr f \<Longrightarrow> C.arr f"
    and dom_closed: "Arr f \<Longrightarrow> Arr (C.dom f)"
    and cod_closed: "Arr f \<Longrightarrow> Arr (C.cod f)"
    and comp_closed: "\<lbrakk> Arr f; Arr g; C.cod f = C.dom g \<rbrakk> \<Longrightarrow> Arr (C g f)"
  begin

    definition comp
    where "comp g f = (if Arr f \<and> Arr g \<and> C.cod f = C.dom g then C g f else C.null)"

    interpretation partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. comp n f = n \<and> comp f n = n"
      proof
        show 1: "\<forall>f. comp C.null f = C.null \<and> comp f C.null = C.null"
          by (simp add: comp_def)
        show "\<And>n. \<forall>f. comp n f = n \<and> comp f n = n \<Longrightarrow> n = C.null"
          using 1 C.ex_un_null by metis
      qed
    qed

    lemma null_char [simp]:
    shows "null = C.null"
    proof -
      have "\<forall>f. comp C.null f = C.null \<and> comp f C.null = C.null"
        by (simp add: comp_def)
      thus ?thesis using ex_un_null by (metis comp_null(2))
    qed

    lemma unit_if_Arr_and_C_unit:
    shows "Arr a \<and> C.unit a \<Longrightarrow> unit a"
      using unit_def C.unit_def comp_def by simp

    lemma has_dom_char:
    shows "has_dom f \<longleftrightarrow> Arr f"
    proof
      assume F: "has_dom f"
      thus "Arr f" using F has_dom_def unit_if_Arr_and_C_unit comp_def null_char by metis
      next
      assume F: "Arr f"
      hence "C.has_dom f"
        using Arr_implies_arr by (metis C.dom_def C.not_arr_null dom_closed)
      hence "unit (C.dom f) \<and> comp f (C.dom f) \<noteq> null"
        using F unit_def comp_def dom_closed unit_if_Arr_and_C_unit null_char
              Arr_implies_arr C.has_dom_def by fastforce
      thus "has_dom f" using has_dom_def by auto
    qed

    lemma has_cod_char:
    shows "has_cod f \<longleftrightarrow> Arr f"
    proof
      assume F: "has_cod f"
      thus "Arr f" using F has_cod_def unit_if_Arr_and_C_unit comp_def null_char by metis
      next
      assume F: "Arr f"
      hence "C.has_cod f"
        using Arr_implies_arr by (metis C.cod_def C.not_arr_null cod_closed)
      hence "unit (C.cod f) \<and> comp (C.cod f) f \<noteq> null"
        using F unit_def comp_def Arr_implies_arr C.has_codD(1) C.has_cod_def cod_closed
        by auto
      thus "has_cod f" using has_cod_def by auto
    qed

    lemma arr_char [iff]:
    shows "arr f \<longleftrightarrow> Arr f"
      using arr_def has_dom_char has_cod_char by blast

    interpretation category comp
      apply unfold_locales
      using Arr_implies_arr C.dom_comp C.not_arr_null comp_closed null_char comp_def
           apply (metis (full_types))
      using Arr_implies_arr C.cod_comp C.not_arr_null comp_closed null_char comp_def
          apply (metis (full_types))
    proof -
      fix f g h
      assume gf: "comp g f \<noteq> null" and hg: "comp h g \<noteq> null"
      have 1: "C.seq g f \<and> C.seq h g \<and> comp (comp h g) f = C (C h g) f
                 \<and> comp h (comp g f) = C h (C g f)"
      proof -
        have "C.seq g f \<and> C.seq h g"
          using gf hg null_char comp_def Arr_implies_arr by metis
        moreover have "comp (comp h g) f = C (C h g) f "
          using gf hg null_char comp_def comp_closed Arr_implies_arr by auto
        moreover have "comp h (comp g f) = C h (C g f)"
          using gf hg null_char comp_def comp_closed Arr_implies_arr by auto
        ultimately show ?thesis by auto
      qed
      show "comp (comp h g) f \<noteq> null"
        using 1 null_char C.not_arr_null by force
      show "comp h (comp g f) \<noteq> null"
        using 1 null_char C.not_arr_null by force
      show "comp h (comp g f) = comp (comp h g) f"
        using 1 by simp
     next
     fix f
     show "has_dom f \<longleftrightarrow> has_cod f"
       using has_dom_char has_cod_char by simp
    qed

    theorem is_category:
    shows "category comp" ..

    lemma dom_simp [simp]:
    assumes "arr f"
    shows "dom f = C.dom f"
    proof -
      have "unit (C.dom f)"
        using assms unit_if_Arr_and_C_unit C.dom_def C.has_domD(2) not_arr_null dom_closed
        by force
      moreover have "comp f (C.dom f) \<noteq> null"
        using assms Arr_implies_arr comp_def null_char dom_closed not_arr_null by auto
      ultimately show ?thesis using dom_simp by auto
    qed

    lemma dom_char:
    shows "dom f = (if arr f then C.dom f else C.null)"
      using dom_simp dom_def has_dom_char by auto

    lemma cod_simp [simp]:
    assumes "arr f"
    shows "cod f = C.cod f"
    proof -
      have "unit (C.cod f)"
        using assms unit_if_Arr_and_C_unit C.cod_def C.has_codD(2) not_arr_null cod_closed
        by force
      moreover have "comp (C.cod f) f \<noteq> null"
        using assms Arr_implies_arr comp_def null_char cod_closed not_arr_null by auto
      ultimately show ?thesis using cod_simp by auto
    qed

    lemma cod_char:
    shows "cod f = (if arr f then C.cod f else C.null)"
      using cod_simp cod_def has_cod_char by auto

    lemma hom_char [iff]:
    shows "f \<in> hom a b \<longleftrightarrow> Arr a \<and> Arr b \<and> Arr f \<and> f \<in> C.hom a b"
      using Arr_implies_arr arr_def cod_closed dom_closed has_cod_char has_dom_char by force

    lemma ide_char [iff]:
    shows "ide f \<longleftrightarrow> arr f \<and> C.ide f"
      by (metis C.ideI_dom C.ideD(2) dom_simp ideI_dom ideD(1) ideD(2) Arr_implies_arr arr_char)

    lemma comp_char:
    shows "comp g f = (if seq g f then C g f else C.null)"
      using Arr_implies_arr comp_def by auto

    lemma comp_simp [simp]:
    assumes "seq g f"
    shows "comp g f = C g f"
      using assms comp_char by auto

  end

  sublocale subcategory \<subseteq> category comp
    using is_category by auto

  section "Inclusion Functor"

  text {*
    If @{text S} is a subcategory of @{text C}, then there is an inclusion functor
    from @{text S} to @{text C}.  Inclusion functors are faithful embeddings.
  *}

  locale inclusion_functor =
    C: category C +
    S: subcategory C Arr
  for C :: "'a comp"
  and Arr :: "'a \<Rightarrow> bool"
  begin

    interpretation "functor" S.comp C S.map
      apply unfold_locales
      using S.arr_char S.Arr_implies_arr S.dom_char S.cod_char S.ide_dom S.ide_cod S.comp_char
            S.arr_comp
      by auto

    lemma is_functor:
    shows "functor S.comp C S.map" ..

    interpretation faithful_functor S.comp C S.map
      apply unfold_locales by simp

    lemma is_faithful_functor:
    shows "faithful_functor S.comp C S.map" ..

    interpretation embedding_functor S.comp C S.map
      apply unfold_locales by simp

    lemma is_embedding_functor:
    shows "embedding_functor S.comp C S.map" ..

  end

  sublocale inclusion_functor \<subseteq> faithful_functor S.comp C S.map
    using is_faithful_functor by auto
  sublocale inclusion_functor \<subseteq> embedding_functor S.comp C S.map
    using is_embedding_functor by auto

  text {*
    The inclusion of a full subcategory is a special case.
    Such functors are fully faithful.
  *}

  locale full_subcategory =
    C: category C
    for C :: "'a comp"
    and Ide :: "'a \<Rightarrow> bool" +
    assumes Ide_implies_Ide: "Ide f \<Longrightarrow> C.ide f"

  sublocale full_subcategory \<subseteq> subcategory C "\<lambda>f. C.arr f \<and> Ide (C.dom f) \<and> Ide (C.cod f)"
      by (unfold_locales; simp)

  locale full_inclusion_functor =
    C: category C +
    S: full_subcategory C Ide
  for C :: "'a comp"
  and Ide :: "'a \<Rightarrow> bool"

  sublocale full_inclusion_functor \<subseteq>
              inclusion_functor C "\<lambda>f. C.arr f \<and> Ide (C.dom f) \<and> Ide (C.cod f)" ..

  context full_inclusion_functor
  begin

    interpretation full_functor S.comp C S.map
      apply unfold_locales by auto

    lemma is_full_functor:
    shows "full_functor S.comp C S.map" ..

  end

  sublocale full_inclusion_functor \<subseteq> full_functor S.comp C S.map
    using is_full_functor by auto
  sublocale full_inclusion_functor \<subseteq> fully_faithful_functor S.comp C S.map ..

  context full_subcategory
  begin

    text {*
      Isomorphisms in a full subcategory are inherited from the ambient category.
    *}

    lemma iso_char:
    shows "iso f \<longleftrightarrow> arr f \<and> C.iso f"
    proof
      assume f: "iso f"
      obtain g where g: "inverse_arrows f g" using f by blast
      have "C.inverse_arrows f g"
        using g inverse_arrows_def [of f g] by auto
      thus "arr f \<and> C.iso f" using g by auto
      next
      assume f: "arr f \<and> C.iso f"
      obtain g where g: "C.inverse_arrows f g" using f by blast
      have "inverse_arrows f g"
      proof
        show "antipar f g" using f g by auto
        show "ide (comp g f)"
          using f g ide_char
          by (metis (no_types, lifting) C.comp_inv_arr \<open>antipar f g\<close> arr_comp cod_comp
              comp_simp dom_simp ideI_cod)
        show "ide (comp f g)" 
          using f g ide_char
          by (metis (no_types, lifting) C.comp_arr_inv \<open>antipar f g\<close> arr_comp comp_simp
              dom_comp dom_simp ideI_dom)
      qed
      thus "iso f" by auto
    qed

  end

  section "Equivalence of Categories"

  text {*
    Here we define the notion of equivalence of categories and show that functors that
    are part of an equivalence of categories are fully faithful and essentially surjective.
  *}

  locale essentially_surjective_functor =
    "functor" +
  assumes essentially_surjective: "\<forall>b. B.ide b \<longrightarrow> (\<exists>a. A.ide a \<and> B.isomorphic (F a) b)"

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
      show "D.antipar (\<eta> (G a)) (G (\<epsilon> a))"
        using assms G.preserves_ide \<eta>.preserves_hom \<epsilon>.preserves_hom G.preserves_hom
        by simp
      have 1: "D (G (\<epsilon> a)) (\<eta> (G a)) = G a"
        using assms triangle_G G\<epsilon>o\<eta>G.map_simp_ide by fastforce
      thus "D.ide (D (G (\<epsilon> a)) (\<eta> (G a)))"
        using assms by simp
      hence "\<eta> (G a) = D.inv (G (\<epsilon> a))"
        using assms \<epsilon>.components_are_iso G.preserves_iso D.inverse_unique
              D.section_retraction_of_iso D.section_retractionI'
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
      show "C.antipar (F (\<eta> b)) (\<epsilon> (F b))"
        using assms F.preserves_ide \<eta>.preserves_hom \<epsilon>.preserves_hom F.preserves_hom
        by simp
      have 1: "C (\<epsilon> (F b)) (F (\<eta> b)) = F b"
        using assms triangle_F \<epsilon>FoF\<eta>.map_simp_ide by auto
      thus "C.ide (C (\<epsilon> (F b)) (F (\<eta> b)))"
        using assms by simp
      hence "C.inv (\<epsilon> (F b)) = F (\<eta> b)"
        using assms \<epsilon>.components_are_iso F.preserves_iso C.inverse_unique
              C.section_retraction_of_iso C.section_retractionI'
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
