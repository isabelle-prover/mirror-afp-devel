(*  Title:       MonoidalCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Monoidal Category"

text_raw{*
\label{monoidal-category-chap}
*}

text {*
  In this theory, we define the notion ``monoidal category,'' and develop consequences of
  the definition.  The main result is a proof of MacLane's coherence theorem.
*}
    
theory MonoidalCategory
imports Category3.EquivalenceOfCategories
begin

  section "Monoidal Category"

  text {*
    A typical textbook presentation defines a monoidal category to be a category @{term C}
    equipped with (among other things) a binary ``tensor product'' functor @{text "\<otimes>: C \<times> C \<rightarrow> C"}
    and an ``associativity'' natural isomorphism @{text \<alpha>}, whose components are isomorphisms
    @{text "\<alpha> (a, b, c): (a \<otimes> b) \<otimes> c \<rightarrow> a \<otimes> (b \<otimes> c)"} for objects @{text a}, @{text b},
    and @{text c} of @{text C}.  This way of saying things avoids an explicit definition of
    the functors that are the domain and codomain of @{text \<alpha>} and, in particular, what category
    serves as the domain of these functors.  The domain category is in fact the product
    category @{text "C \<times> C \<times> C"} and the domain and codomain of @{text \<alpha>} are the functors
    @{text "T o (T \<times> C): C \<times> C \<times> C \<rightarrow> C"} and @{text "T o (C \<times> T): C \<times> C \<times> C \<rightarrow> C"}.
    In a formal development, though, we can't gloss over the fact that
    @{text "C \<times> C \<times> C"} has to mean either @{text "C \<times> (C \<times> C)"} or @{text "(C \<times> C) \<times> C"},
    which are not formally identical, and that associativities are somehow involved in the
    definitions of the functors @{text "T o (T \<times> C)"} and @{text "T o (C \<times> T)"}.
    Here we define the @{text binary_endofunctor} locale to codify our choices about what
    @{text "C \<times> C \<times> C"}, @{text "T o (T \<times> C)"}, and @{text "T o (C \<times> T)"} actually mean.
    In particular, we choose @{text "C \<times> C \<times> C"} to be @{text "C \<times> (C \<times> C)"} and define the
    functors @{text "T o (T \<times> C)"}, and @{text "T o (C \<times> T)"} accordingly.
  *}

  locale binary_endofunctor =
    C: category C +
    CC: product_category C C +
    CCC: product_category C CC.comp +
    binary_functor C C C T
  for C :: "'a comp"                            (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  begin

    definition ToTC
    where "ToTC f \<equiv> if CCC.arr f then T (T (fst f, fst (snd f)), snd (snd f)) else C.null"

    lemma functor_ToTC:
    shows "functor CCC.comp C ToTC"
      apply unfold_locales
      using ToTC_def preserves_hom preserves_comp by auto

    lemma ToTC_simp [simp]:
    assumes "C.arr f" and "C.arr g" and "C.arr h"
    shows "ToTC (f, g, h) = T (T (f, g), h)"
      using assms ToTC_def CCC.arr_char by simp

    definition ToCT
    where "ToCT f \<equiv> if CCC.arr f then T (fst f, T (fst (snd f), snd (snd f))) else C.null"

    lemma functor_ToCT:
    shows "functor CCC.comp C ToCT"
      apply unfold_locales
      using ToCT_def preserves_hom preserves_comp by auto

    lemma ToCT_simp [simp]:
    assumes "C.arr f" and "C.arr g" and "C.arr h"
    shows "ToCT (f, g, h) = T (f, T (g, h))"
      using assms ToCT_def CCC.arr_char by simp

  end

  text {*
    Our primary definition for ``monoidal category'' follows the somewhat non-traditional
    development in \cite{Etingof15}.  There a monoidal category is defined to be a category
    @{text C} equipped with a binary \emph{tensor product} functor @{text "T: C \<times> C \<rightarrow> C"},
    an \emph{associativity isomorphism}, which is a natural isomorphism
    @{text "\<alpha>: T o (T \<times> C) \<rightarrow> T o (C \<times> T)"}, a \emph{unit object} @{text \<I>} of @{text C},
    and an isomorphism @{text "\<iota>: T (\<I>, \<I>) \<rightarrow> \<I>"}, subject to two axioms:
    the \emph{pentagon axiom}, which expresses the commutativity of certain pentagonal diagrams
    involving components of @{text \<alpha>}, and the left and right \emph{unit axioms}, which state
    that the endofunctors @{text "T (\<I>, -)"} and @{text "T (-, \<I>)"} are equivalences of categories.
    This definition is formalized in the @{text monoidal_category} locale.

    In more traditional developments, the definition of monoidal category involves additional
    left and right \emph{unitor} isomorphisms @{text \<lambda>} and @{text \<rho>} and associated axioms
    involving their components.
    However, as is shown in \cite{Etingof15} and formalized here, the unitors are uniquely
    determined by @{text \<alpha>} and their values @{text "\<lambda>(\<I>)"} and @{text "\<rho>(\<I>)"} at @{text \<I>},
    which coincide.  Treating @{text \<lambda>} and @{text \<rho>} as defined notions results in a more
    economical basic definition of monoidal category that requires less data to be given,
    and has a similar effect on the definition of ``monoidal functor.''
    Moreover, in the context of the formalization of categories that we use here,
    the unit object @{text \<I>} also need not be given separately, as it can be obtained as the
    codomain of the isomorphism @{text \<iota>}.
  *}

  locale monoidal_category =
    category C +
    CC: product_category C C +
    CCC: product_category C CC.comp +
    T: binary_endofunctor C T +
    \<alpha>: natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha> +
    L: equivalence_functor C C "\<lambda>f. T (cod \<iota>, f)" +
    R: equivalence_functor C C "\<lambda>f. T (f, cod \<iota>)"
  for C :: "'a comp"                            (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a +
  assumes \<iota>_in_hom: "\<iota> \<in> hom (T (cod \<iota>, cod \<iota>)) (cod \<iota>)"
  and \<iota>_is_iso: "iso \<iota>"
  and pentagon: "\<lbrakk> ide a; ide b; ide c; ide d \<rbrakk> \<Longrightarrow>
                 T (a, \<alpha> (b, c, d)) \<cdot> \<alpha> (a, T (b, c), d) \<cdot> T (\<alpha> (a, b, c), d)
                   = \<alpha> (a, b, T (c, d)) \<cdot> \<alpha> (T (a, b), c, d)"
  begin

    text{*
      We now define helpful notation and abbreviations to improve readability.
      We did not define and use the notation @{text \<otimes>} for the tensor product
      in the definition of the locale because to define @{text \<otimes>} as a binary
      operator requires that it be in curried form, whereas for @{text T}
      to be a binary functor requires that it take a pair as its argument.
    *}

    abbreviation unity :: 'a                ("\<I>")
    where "unity \<equiv> cod \<iota>"

    abbreviation L :: "'a \<Rightarrow> 'a"
    where "L f \<equiv> T (\<I>, f)"

    abbreviation R :: "'a \<Rightarrow> 'a"
    where "R f \<equiv> T (f, \<I>)"

    abbreviation tensor                     (infixr "\<otimes>" 53)
    where "f \<otimes> g \<equiv> T (f, g)"

    abbreviation assoc                      ("\<a>[_, _, _]")
    where "\<a>[a, b, c] \<equiv> \<alpha> (a, b, c)"

    text{*
      In HOL we can just give the definitions of the left and right unitors ``up front''
      without any preliminary work.  Later we will have to show that these definitions
      have the right properties.  The next two definitions define the values of the
      unitors when applied to identities; that is, their components as natural transformations.
    *}

    definition lunit                        ("\<l>[_]")
    where "lunit a \<equiv> THE f. f \<in> hom (\<I> \<otimes> a) a \<and> \<I> \<otimes> f = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"

    definition runit                        ("\<r>[_]")
    where "runit a \<equiv> THE f. f \<in> hom (a \<otimes> \<I>) a \<and> f \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"

    text{*
      The next two definitions extend the unitors to all arrows, not just identities.
      Unfortunately, the traditional symbol @{text \<lambda>} for the left unitor is already
      reserved for a higher purpose, so we have to make do with a poor substitute.
    *}

    abbreviation \<ll>
    where "\<ll> f \<equiv> if arr f then f \<cdot> \<l>[dom f] else null"

    abbreviation \<rho>
    where "\<rho> f \<equiv> if arr f then f \<cdot> \<r>[dom f] else null"

    text{*
      We now embark upon a development of the consequences of the monoidal category axioms.
      One of our objectives is to be able to show that an interpretation of the
      @{text monoidal_category} locale induces an interpretation of a locale corresponding
      to a more traditional definition of monoidal category.
      Another is to obtain the facts we need to prove the coherence theorem.
    *}

    lemma ide_unity [simp]:
    shows "ide \<I>"
      using \<iota>_in_hom by simp

    lemma tensor_in_hom:
    assumes "f \<in> hom a b" and "g \<in> hom c d"
    shows "f \<otimes> g \<in> hom (a \<otimes> c) (b \<otimes> d)"
      using assms T.preserves_hom CC.arr_char by simp

    lemma tensor_preserves_ide:
    assumes "ide a" and "ide b"
    shows "ide (a \<otimes> b)"
      using assms T.preserves_ide CC.ide_char by simp

    lemma tensor_preserves_iso:
    assumes "iso f" and "iso g"
    shows "iso (f \<otimes> g)"
      using assms T.preserves_iso CC.iso_char by simp

    lemma inv_tensor:
    assumes "iso f" and "iso g"
    shows "inv (f \<otimes> g) = (inv f \<otimes> inv g)"
      using assms T.preserves_inv CC.iso_char CC.inv_char by auto

    lemma interchange:
    assumes "seq h g" and "seq h' g'"
    shows "(h \<otimes> h') \<cdot> (g \<otimes> g') = h \<cdot> g \<otimes> h' \<cdot> g'"
    proof -
      have "CC.arr (h, h')"
        using assms CC.arr_char by simp
      moreover have "(g, g') \<in> CC.hom (CC.dom (g, g')) (CC.dom (h, h'))"
        using assms CC.hom_char CC.dom_char by force
      ultimately show ?thesis
        using T.preserves_comp [of "(g, g')" "(h, h')"] by simp
    qed

    lemma \<alpha>_simp:
    assumes "arr f" and "arr g" and "arr h"
    shows "\<alpha> (f, g, h) = (f \<otimes> g \<otimes> h) \<cdot> \<a>[dom f, dom g, dom h]"
      using assms \<alpha>.is_natural_1 [of "(f, g, h)"] CCC.arr_char [of "(f, g, h)"] by simp

    lemma assoc_in_hom:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<a>[a, b, c] \<in> hom ((a \<otimes> b) \<otimes> c) (a \<otimes> b \<otimes> c)"
      using assms \<alpha>.preserves_hom CCC.ide_char by simp

    lemma assoc_naturality:
    assumes "arr f0" and "arr f1" and "arr f2"
    shows "\<a>[cod f0, cod f1, cod f2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2)
             = (f0 \<otimes> f1 \<otimes> f2) \<cdot> \<a>[dom f0, dom f1, dom f2]"
      using assms \<alpha>.is_natural_1 \<alpha>.is_natural_2 CCC.ide_char by auto

    lemma iso_assoc:
    assumes "ide a" and "ide b" and "ide c"
    shows "iso \<a>[a, b, c]"
      using assms \<alpha>.preserves_iso CCC.ide_char by simp

    text{*
      The next result uses the fact that the functor @{text L} is an equivalence
      (and hence faithful) to show the existence of a unique solution to the characteristic
      equation used in the definition of a component @{term "\<l>[a]"} of the left unitor.
      It follows that @{term "\<l>[a]"}, as given by our definition using definite description,
      satisfies this characteristic equation and is therefore uniquely determined by
      by @{text \<otimes>}, @{term \<alpha>}, and @{text \<iota>}.
    *}

    lemma lunit_char:
    assumes "ide a"
    shows "\<l>[a] \<in> hom (\<I> \<otimes> a) a" and "\<I> \<otimes> \<l>[a] = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"
    and "\<exists>!f. f \<in> hom (\<I> \<otimes> a) a \<and> \<I> \<otimes> f = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"
    proof -
      obtain F \<eta> \<epsilon> where L: "equivalence_of_categories C C F (\<lambda>f. \<I> \<otimes> f) \<eta> \<epsilon>"
        using L.induces_equivalence by blast
      interpret L: equivalence_of_categories C C F "\<lambda>f. \<I> \<otimes> f" \<eta> \<epsilon>
        using L by auto
      let ?P = "\<lambda>f. f \<in> hom (\<I> \<otimes> a) a \<and> \<I> \<otimes> f = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"
      have "(\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a] \<in> hom (\<I> \<otimes> \<I> \<otimes> a) (\<I> \<otimes> a)"
        using assms \<iota>_in_hom R.preserves_hom \<alpha>.preserves_hom \<alpha>.components_are_iso inv_in_hom
        by simp
      moreover have "ide (\<I> \<otimes> a)" using assms by simp
      ultimately have "\<exists>f. ?P f"
        using assms L.is_full [of a "\<I> \<otimes> a" "(\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"] by blast
      moreover have "\<And>f f'. ?P f \<Longrightarrow> ?P f' \<Longrightarrow> f = f'"
      proof -
        fix f f'
        assume f: "?P f" and f': "?P f'"
        have "par f f'" using f f' by simp
        show "f = f'" using f f' L.is_faithful [of f f'] by auto
      qed
      ultimately show "\<exists>!f. ?P f" by blast
      hence 1: "?P \<l>[a]"
        unfolding lunit_def using theI' [of ?P] by fast
      show "\<l>[a] \<in> hom (\<I> \<otimes> a) a" using 1 by fast
      show "\<I> \<otimes> \<l>[a] = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]" using 1 by fast
    qed

    lemma \<ll>_ide_simp:
    assumes "ide a"
    shows "\<ll> a = \<l>[a]"
      using assms lunit_char by simp

    lemma lunit_in_hom:
    assumes "ide a"
    shows "\<l>[a] \<in> hom (\<I> \<otimes> a) a"
      using assms lunit_char(1) by blast

    text{*
      As the right-hand side of the characteristic equation for @{term "\<I> \<otimes> \<l>[a]"}
      is an isomorphism, and the equivalence functor @{text L} reflects isomorphisms,
      it follows that @{term "\<l>[a]"} is an isomorphism.
    *}

    lemma iso_lunit:
    assumes "ide a"
    shows "iso \<l>[a]"
    proof -
      have "iso ((\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a])"
        using assms \<iota>_is_iso T.preserves_iso \<alpha>.components_are_iso iso_inv_iso isos_compose
              \<iota>_in_hom CC.iso_char CCC.ide_char ide_is_iso \<alpha>.preserves_hom
              inv_in_hom T.preserves_hom
        by force
      thus "iso \<l>[a]"
        using assms lunit_char L.reflects_iso [of "\<l>[a]" "\<I> \<otimes> a" a] by presburger
    qed

    text{*
      To prove that an arrow @{term f} is equal to @{term "\<l>[a]"} we need only show
      that it is parallel to @{term "\<l>[a]"} and that @{term "\<I> \<otimes> f"} satisfies the same
      characteristic equation as @{term "\<I> \<otimes> \<l>[a]"} does.
    *}

    lemma lunit_eqI:
    assumes "ide a" and "f \<in> hom (\<I> \<otimes> a) a" and "\<I> \<otimes> f = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"
    shows "f = \<l>[a]"
      using assms lunit_char the1_equality by blast

    text{*
      The next facts establish the corresponding results for the components of the
      right unitor.
    *}

    lemma runit_char:
    assumes "ide a"
    shows "\<r>[a] \<in> hom (a \<otimes> \<I>) a" and "\<r>[a] \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
    and "\<exists>!f. f \<in> hom (a \<otimes> \<I>) a \<and> f \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
    proof -
      obtain F \<eta> \<epsilon> where R: "equivalence_of_categories C C F (\<lambda>f. f \<otimes> \<I>) \<eta> \<epsilon>"
        using R.induces_equivalence by blast
      interpret R: equivalence_of_categories C C F "\<lambda>f. f \<otimes> \<I>" \<eta> \<epsilon>
        using R by auto
      let ?P = "\<lambda>f. f \<in> hom (a \<otimes> \<I>) a \<and> f \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
      have "(a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>] \<in> hom ((a \<otimes> \<I>) \<otimes> \<I>) (a \<otimes> \<I>)"
        using assms \<iota>_in_hom T.preserves_hom \<alpha>.preserves_hom \<alpha>.components_are_iso inv_in_hom
        by simp
      moreover have "ide (a \<otimes> \<I>)" using assms by simp
      ultimately have "\<exists>f. ?P f"
        using assms R.is_full [of a "a \<otimes> \<I>" "(a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"] by blast
      moreover have "\<And>f f'. ?P f \<Longrightarrow> ?P f' \<Longrightarrow> f = f'"
      proof -
        fix f f'
        assume f: "?P f" and f': "?P f'"
        have "par f f'" using f f' by simp
        show "f = f'" using f f' R.is_faithful [of f f'] by auto
      qed
      ultimately show "\<exists>!f. ?P f" by blast
      hence 1: "?P \<r>[a]" unfolding runit_def using theI' [of ?P] by fast
      show "\<r>[a] \<in> hom (a \<otimes> \<I>) a" using 1 by fast
      show "\<r>[a] \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]" using 1 by fast
    qed

    lemma \<rho>_ide_simp:
    assumes "ide a"
    shows "\<rho> a = \<r>[a]"
      using assms runit_char by simp

    lemma runit_in_hom:
    assumes "ide a"
    shows "\<r>[a] \<in> hom (a \<otimes> \<I>) a"
      using assms runit_char(1) by blast

    lemma runit_eqI:
    assumes "ide a" and "f \<in> hom (a \<otimes> \<I>) a" and "f \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
    shows "f = \<r>[a]"
      using assms runit_char the1_equality by blast

    lemma iso_runit:
    assumes "ide a"
    shows "iso \<r>[a]"
    proof -
      have "iso ((a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>])"
        using assms \<iota>_is_iso T.preserves_iso \<alpha>.components_are_iso isos_compose
              \<iota>_in_hom CC.iso_char CCC.ide_char ide_is_iso \<alpha>.preserves_hom T.preserves_hom
        by force
      thus "iso \<r>[a]"
        using assms runit_char R.reflects_iso [of "\<r>[a]" "a \<otimes> \<I>" a] by presburger
    qed

    text{*
      We can now show that the components of the left and right unitors have the
      naturality properties required of a natural transformation.
    *}

    lemma lunit_naturality:
    assumes "arr f"
    shows "\<l>[cod f] \<cdot> (\<I> \<otimes> f) = f \<cdot> \<l>[dom f]"
    proof -
      interpret \<alpha>': inverse_transformation CCC.comp C T.ToTC T.ToCT \<alpha> ..
      have "par (\<l>[cod f] \<cdot> (\<I> \<otimes> f)) (f \<cdot> \<l>[dom f])"
        using assms lunit_in_hom tensor_in_hom \<iota>_in_hom CC.hom_char
        by force
      moreover have "\<I> \<otimes> \<l>[cod f] \<cdot> (\<I> \<otimes> f) = \<I> \<otimes> f \<cdot> \<l>[dom f]"
      proof -
        have "\<I> \<otimes> \<l>[cod f] \<cdot> (\<I> \<otimes> f) = \<I> \<cdot> \<I> \<otimes> \<l>[cod f] \<cdot> (\<I> \<otimes> f)"
          using \<iota>_in_hom by force
        also have "... = (\<I> \<otimes> \<l>[cod f]) \<cdot> (\<I> \<otimes> \<I> \<otimes> f)"
          using assms lunit_in_hom \<iota>_in_hom tensor_in_hom interchange [of \<I> \<I> "\<I> \<otimes> f" "\<l>[cod f]"]
          by force
        also have "... = (\<iota> \<otimes> cod f) \<cdot> inv \<a>[\<I>, \<I>, cod f] \<cdot> (\<I> \<otimes> \<I> \<otimes> f)"
          using assms lunit_char(2) lunit_in_hom tensor_in_hom assoc_in_hom \<alpha>.components_are_iso
                inv_in_hom \<iota>_in_hom
          by force
        also have "... = (\<iota> \<otimes> cod f) \<cdot> ((\<I> \<otimes> \<I>) \<otimes> f) \<cdot> inv \<a>[\<I>, \<I>, dom f]"
          using assms \<iota>_in_hom tensor_in_hom \<alpha>'.is_natural_1 [of "(\<I>, \<I>, f)"] \<alpha>'.map_ide_simp
                \<alpha>'.is_natural_2 [of "(\<I>, \<I>, f)"] CCC.arr_char by auto
        also have "... = ((\<iota> \<otimes> cod f) \<cdot> ((\<I> \<otimes> \<I>) \<otimes> f)) \<cdot> inv \<a>[\<I>, \<I>, dom f]"
          using assms lunit_in_hom tensor_in_hom assoc_in_hom \<alpha>.components_are_iso
                inv_in_hom \<iota>_in_hom
          by force
        also have "... = ((\<I> \<otimes> f) \<cdot> (\<iota> \<otimes> dom f)) \<cdot> inv \<a>[\<I>, \<I>, dom f]"
          using assms \<iota>_in_hom tensor_in_hom interchange by force
        also have "... = (\<I> \<otimes> f) \<cdot> (\<iota> \<otimes> dom f) \<cdot> inv \<a>[\<I>, \<I>, dom f]"
          using assms \<alpha>.components_are_iso inv_in_hom assoc_in_hom tensor_in_hom \<iota>_in_hom
          by force
        also have "... = \<I> \<otimes> f \<cdot> \<l>[dom f]"
          using assms \<iota>_in_hom lunit_char interchange by force
        finally show ?thesis by blast
      qed
      ultimately show "\<l>[cod f] \<cdot> (\<I> \<otimes> f) = f \<cdot> \<l>[dom f]"
        using L.is_faithful by blast
    qed

    lemma runit_naturality:
    assumes "arr f"
    shows "\<r>[cod f] \<cdot> (f \<otimes> \<I>) = f \<cdot> \<r>[dom f]"
    proof -
      have "par (\<r>[cod f] \<cdot> (f \<otimes> \<I>)) (f \<cdot> \<r>[dom f])"
        using assms runit_in_hom tensor_in_hom \<iota>_in_hom CC.hom_char by force
      moreover have "\<r>[cod f] \<cdot> (f \<otimes> \<I>) \<otimes> \<I> = f \<cdot> \<r>[dom f] \<otimes> \<I>"
      proof -
        have "\<r>[cod f] \<cdot> (f \<otimes> \<I>) \<otimes> \<I> = \<r>[cod f] \<cdot> (f \<otimes> \<I>) \<otimes> \<I> \<cdot> \<I>"
          using \<iota>_in_hom by force
        also have "... = (\<r>[cod f] \<otimes> \<I>) \<cdot> ((f \<otimes> \<I>) \<otimes> \<I>)"
          using assms runit_in_hom \<iota>_in_hom tensor_in_hom interchange [of \<I> \<I> "\<I> \<otimes> f" "\<r>[cod f]"]
          by force
        also have "... = (cod f \<otimes> \<iota>) \<cdot> \<a>[cod f, \<I>, \<I>] \<cdot> ((f \<otimes> \<I>) \<otimes> \<I>)"
          using assms runit_char(2) runit_in_hom tensor_in_hom assoc_in_hom \<iota>_in_hom by force
        also have "... = (cod f \<otimes> \<iota>) \<cdot> (f \<otimes> \<I> \<otimes> \<I>) \<cdot>  \<a>[dom f, \<I>, \<I>]"
          using assms \<iota>_in_hom tensor_in_hom \<alpha>.is_natural_1 [of "(f, \<I>, \<I>)"]
                 \<alpha>.is_natural_2 [of "(f, \<I>, \<I>)"] CCC.arr_char by auto
        also have "... = ((cod f \<otimes> \<iota>) \<cdot> (f \<otimes> \<I> \<otimes> \<I>)) \<cdot> \<a>[dom f, \<I>, \<I>]"
          using assms runit_in_hom tensor_in_hom assoc_in_hom \<iota>_in_hom by force
        also have "... = ((f \<otimes> \<I>) \<cdot> (dom f \<otimes> \<iota>)) \<cdot> \<a>[dom f, \<I>, \<I>]"
          using assms \<iota>_in_hom tensor_in_hom interchange by force
        also have "... = (f \<otimes> \<I>) \<cdot> (dom f \<otimes> \<iota>) \<cdot> \<a>[dom f, \<I>, \<I>]"
          using assms assoc_in_hom tensor_in_hom \<iota>_in_hom by force
        also have "... = f \<cdot> \<r>[dom f] \<otimes> \<I>"
          using assms runit_char(2) \<iota>_in_hom runit_in_hom interchange by force
        finally show ?thesis by blast
      qed
      ultimately show "\<r>[cod f] \<cdot> (f \<otimes> \<I>) = f \<cdot> \<r>[dom f]"
        using R.is_faithful by blast
    qed

  end

  text{*
    The following locale is an extension of @{locale monoidal_category} that has the
    unitors and their inverses, as well as the inverse to the associator,
    conveniently pre-interpreted.
  *}

  locale extended_monoidal_category =
    monoidal_category +
    \<alpha>': inverse_transformation CCC.comp C T.ToTC T.ToCT \<alpha> +
    \<ll>: natural_isomorphism C C L map \<ll> +
    \<ll>': inverse_transformation C C L map \<ll> +
    \<rho>: natural_isomorphism C C R map \<rho> +
    \<rho>': inverse_transformation C C R map \<rho>

  text{*
    Next we show that an interpretation of @{locale monoidal_category} extends to an
    interpretation of @{locale extended_monoidal_category} and we arrange for the former
    locale to inherit from the latter.
  *}

  context monoidal_category
  begin

    interpretation \<alpha>': inverse_transformation CCC.comp C T.ToTC T.ToCT \<alpha> ..

    interpretation \<ll>: natural_transformation C C L map \<ll>
    proof -
      interpret \<ll>: transformation_by_components C C L map "\<lambda>a. \<l>[a]"
        apply unfold_locales
        using lunit_in_hom lunit_naturality by auto
      have "\<ll>.map = \<ll>"
        using \<ll>.is_natural_1 \<ll>.is_extensional by auto
      thus "natural_transformation C C L map \<ll>"
        using \<ll>.natural_transformation_axioms by auto
    qed

    interpretation \<ll>: natural_isomorphism C C L map \<ll>
      apply unfold_locales
      using iso_lunit \<ll>_ide_simp by simp

    interpretation \<rho>: natural_transformation C C R map \<rho>
    proof -
      interpret \<rho>: transformation_by_components C C R map "\<lambda>a. \<r>[a]"
        apply unfold_locales
        using runit_in_hom runit_naturality by auto
      have "\<rho>.map = \<rho>"
        using \<rho>.is_natural_1 \<rho>.is_extensional by auto
      thus "natural_transformation C C R map \<rho>"
        using \<rho>.natural_transformation_axioms by auto
    qed

    interpretation \<rho>: natural_isomorphism C C R map \<rho>
      apply unfold_locales
      using iso_runit \<rho>_ide_simp by simp

    lemma induces_extended_monoidal_category:
    shows "extended_monoidal_category C T \<alpha> \<iota>" ..

  end

  sublocale monoidal_category \<subseteq> extended_monoidal_category
    using induces_extended_monoidal_category by auto

  context monoidal_category
  begin

    abbreviation \<alpha>'
    where "\<alpha>' \<equiv> \<alpha>'.map"

    lemma natural_isomorphism_\<alpha>':
    shows "natural_isomorphism CCC.comp C T.ToCT T.ToTC \<alpha>'" ..

    abbreviation assoc'                ("\<a>\<^sup>-\<^sup>1[_, _, _]")
    where "\<a>\<^sup>-\<^sup>1[a, b, c] \<equiv> inv \<a>[a, b, c]"

    lemma \<alpha>'_ide_simp:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<alpha>' (a, b, c) = \<a>\<^sup>-\<^sup>1[a, b, c]"
      using assms \<alpha>'.inverts_components inverse_unique by force

    lemma \<alpha>'_simp:
    assumes "arr f" and "arr g" and "arr h"
    shows "\<alpha>' (f, g, h) = ((f \<otimes> g) \<otimes> h) \<cdot> \<a>\<^sup>-\<^sup>1[dom f, dom g, dom h]"
      using assms T.ToTC_simp T.preserves_arr \<alpha>'.is_natural_1 \<alpha>'_ide_simp by force

    lemma assoc_inv:
    assumes "ide a" and "ide b" and "ide c"
    shows "inverse_arrows \<a>[a, b, c] \<a>\<^sup>-\<^sup>1[a, b, c]"
      using assms iso_assoc inv_is_inverse by simp

    lemma assoc'_in_hom:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<a>\<^sup>-\<^sup>1[a, b, c] \<in> hom (a \<otimes> (b \<otimes> c)) ((a \<otimes> b) \<otimes> c)"
      using assms assoc_inv assoc_in_hom inverse_arrows_def by simp

    lemma comp_assoc_assoc' [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<a>[a, b, c] \<cdot> \<a>\<^sup>-\<^sup>1[a, b, c] = a \<otimes> (b \<otimes> c)"
    and "\<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> \<a>[a, b, c] = (a \<otimes> b) \<otimes> c"
    proof -
      have 1: "inverse_arrows \<a>[a, b, c] \<a>\<^sup>-\<^sup>1[a, b, c]"
        using assms assoc_inv by simp
      show "\<a>[a, b, c] \<cdot> \<a>\<^sup>-\<^sup>1[a, b, c] = a \<otimes> (b \<otimes> c)"
        using assms 1 comp_arr_inv assoc_in_hom [of a b c] by auto
      show "\<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> \<a>[a, b, c] = (a \<otimes> b) \<otimes> c"
        using assms 1 comp_inv_arr assoc_in_hom [of a b c] by fastforce
    qed

    lemma assoc'_naturality:
    assumes "arr f0" and "arr f1" and "arr f2"
    shows "((f0 \<otimes> f1) \<otimes> f2) \<cdot> \<a>\<^sup>-\<^sup>1[dom f0, dom f1, dom f2]
              = \<a>\<^sup>-\<^sup>1[cod f0, cod f1, cod f2] \<cdot> (f0 \<otimes> (f1 \<otimes> f2))"
      using assms \<alpha>'.is_natural_1 \<alpha>'.is_natural_2 CCC.cod_char T.ToCT_simp by auto

    abbreviation \<ll>'
    where "\<ll>' \<equiv> \<ll>'.map"

    abbreviation lunit'                ("\<l>\<^sup>-\<^sup>1[_]")
    where "\<l>\<^sup>-\<^sup>1[a] \<equiv> inv \<l>[a]"

    lemma \<ll>'_ide_simp:
    assumes "ide a"
    shows "\<ll>'.map a = \<l>\<^sup>-\<^sup>1[a]"
      using assms \<ll>'.inverts_components \<ll>_ide_simp inverse_unique by force

    lemma lunit_inv:
    assumes "ide a"
    shows "inverse_arrows \<l>[a] \<l>\<^sup>-\<^sup>1[a]"
      using assms iso_lunit inv_is_inverse by simp

    lemma lunit'_in_hom:
    assumes "ide a"
    shows "\<l>\<^sup>-\<^sup>1[a] \<in> hom a (\<I> \<otimes> a)"
      using assms lunit_inv lunit_in_hom inverse_arrows_def by simp

    lemma comp_lunit_lunit' [simp]:
    assumes "ide a"
    shows "\<l>[a] \<cdot> \<l>\<^sup>-\<^sup>1[a] = a"
    and "\<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a] = \<I> \<otimes> a"
    proof -
      have 1: "inverse_arrows \<l>[a] \<l>\<^sup>-\<^sup>1[a]"
        using assms lunit_inv by simp
      show "\<l>[a] \<cdot> \<l>\<^sup>-\<^sup>1[a] = a"
        using assms 1 comp_arr_inv lunit_in_hom by auto
      show "\<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a] = \<I> \<otimes> a"
        using assms 1 comp_inv_arr lunit_in_hom by auto
    qed

    lemma lunit'_naturality:
    assumes "arr f"
    shows "(\<I> \<otimes> f) \<cdot> \<l>\<^sup>-\<^sup>1[dom f] = \<l>\<^sup>-\<^sup>1[cod f] \<cdot> f"
      using assms \<ll>'.is_natural_1 \<ll>'.is_natural_2 \<ll>'_ide_simp by simp

    abbreviation \<rho>'
    where "\<rho>' \<equiv> \<rho>'.map"

    abbreviation runit'                ("\<r>\<^sup>-\<^sup>1[_]")
    where "\<r>\<^sup>-\<^sup>1[a] \<equiv> inv \<r>[a]"

    lemma \<rho>'_ide_simp:
    assumes "ide a"
    shows "\<rho>'.map a = \<r>\<^sup>-\<^sup>1[a]"
    proof -
      have "inverse_arrows (\<rho> a) (\<rho>'.map a)"
        using assms \<rho>'.inverts_components by force
      hence "inverse_arrows \<r>[a] (\<rho>'.map a)"
        using assms \<rho>_ide_simp by force
      thus ?thesis
        using assms inverse_unique by presburger
    qed

    lemma runit_inv:
    assumes "ide a"
    shows "inverse_arrows \<r>[a] \<r>\<^sup>-\<^sup>1[a]"
      using assms iso_runit inv_is_inverse by simp

    lemma runit'_in_hom:
    assumes "ide a"
    shows "\<r>\<^sup>-\<^sup>1[a] \<in> hom a (a \<otimes> \<I>)"
      using assms runit_inv runit_in_hom inverse_arrows_def by simp

    lemma comp_runit_runit' [simp]:
    assumes "ide a"
    shows "\<r>[a] \<cdot> \<r>\<^sup>-\<^sup>1[a] = a"
    and "\<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a] = a \<otimes> \<I>"
    proof -
      have 1: "inverse_arrows \<r>[a] \<r>\<^sup>-\<^sup>1[a]"
        using assms runit_inv by simp
      show "\<r>[a] \<cdot> \<r>\<^sup>-\<^sup>1[a] = a"
        using assms 1 comp_arr_inv runit_in_hom by auto
      show "\<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a] = a \<otimes> \<I>"
        using assms 1 comp_inv_arr runit_in_hom by auto
    qed

    lemma runit'_naturality:
    assumes "arr f"
    shows "(f \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[dom f] = \<r>\<^sup>-\<^sup>1[cod f] \<cdot> f"
      using assms \<rho>'.is_natural_1 \<rho>'.is_natural_2 \<rho>'_ide_simp by simp

    lemma lunit_commutes_with_L:
    assumes "ide a"
    shows "\<l>[\<I> \<otimes> a] = \<I> \<otimes> \<l>[a]"
      using assms lunit_naturality [of "\<l>[a]"] lunit_in_hom iso_lunit iso_is_section
            section_is_mono monoE [of "\<l>[a]" "\<I> \<otimes> \<l>[a]" "\<l>[\<I> \<otimes> a]"]
      by force

    lemma runit_commutes_with_R:
    assumes "ide a"
    shows "\<r>[a \<otimes> \<I>] = \<r>[a] \<otimes> \<I>"
      using assms runit_naturality [of "\<r>[a]"] runit_in_hom iso_runit iso_is_section
            section_is_mono runit_in_hom monoE [of "\<r>[a]" "\<r>[a] \<otimes> \<I>" "\<r>[a \<otimes> \<I>]"]
      by force

    text{*
      The components of the left and right unitors are related via a ``triangle''
      diagram that also involves the associator.
      The proof follows \cite{Etingof15}, Proposition 2.2.3.
    *}

    lemma triangle:
    assumes "ide a" and "ide b"
    shows "(a \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, b] = \<r>[a] \<otimes> b"
    proof -
      text{*
        We show that the lower left triangle in the following diagram commutes.
      *}
      text{*
$$\xymatrix{
  {@{term "((a \<otimes> \<I>) \<otimes> \<I>) \<otimes> b"}}
     \ar[rrrr]^{\scriptsize @{term "\<a>[a, \<I>, \<I>] \<otimes> b"}}
     \ar[ddd]_{\scriptsize @{term "\<a>[a \<otimes> \<I>, \<I>, b]"}}
     \ar[drr]_{\scriptsize @{term "(\<r>[a] \<otimes> \<I>) \<otimes> b"}}
  && &&
  {@{term "(a \<otimes> (\<I> \<otimes> \<I>)) \<otimes> b"}}
     \ar[dll]^{\scriptsize @{term "(a \<otimes> \<iota>) \<otimes> b"}}
     \ar[ddd]^{\scriptsize @{term "\<a>[a, \<I> \<otimes> \<I>, b]"}} \\
  && {@{term "(a \<otimes> \<I>) \<otimes> b"}}
      \ar[d]^{\scriptsize @{term "\<a>[a, \<I>, b]"}} \\
  && {@{term "a \<otimes> \<I> \<otimes> b"}}  \\
  {@{term "(a \<otimes> \<I>) \<otimes> \<I> \<otimes> b"}}
      \ar[urr]^{\scriptsize @{term "\<r>[a] \<otimes> \<I> \<otimes> b"}}
      \ar[drr]_{\scriptsize @{term "\<a>[a, \<I>, \<I> \<otimes> b]"}}
  && &&
  {@{term "a \<otimes> (\<I> \<otimes> \<I>) \<otimes> b"}}
      \ar[ull]_{\scriptsize @{term "a \<otimes> \<iota> \<otimes> b"}}
      \ar[dll]^{\scriptsize @{term "a \<otimes> \<a>[\<I>, \<I>, b]"}}  \\
  && {@{term "a \<otimes> \<I> \<otimes> \<I> \<otimes> b"}}
      \ar[uu]^{\scriptsize @{term "a \<otimes> \<l>[\<I> \<otimes> b]"}}
}$$
      *}
      have *: "(a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] = \<r>[a] \<otimes> \<I> \<otimes> b"
      proof -
        have 1: "((a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b]) \<cdot> \<a>[a \<otimes> \<I>, \<I>, b]
                    = (\<r>[a] \<otimes> \<I> \<otimes> b) \<cdot> \<a>[a \<otimes> \<I>, \<I>, b]"
        proof -
          have "((a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b]) \<cdot> \<a>[a \<otimes> \<I>, \<I>, b]
                  = (a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> \<a>[a \<otimes> \<I>, \<I>, b]"
            using assms \<iota>_in_hom tensor_in_hom assoc_in_hom lunit_in_hom by force
          also have "... = (a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> (a \<otimes> \<a>[\<I>, \<I>, b]) \<cdot> \<a>[a, \<I> \<otimes> \<I>, b] \<cdot> (\<a>[a, \<I>, \<I>] \<otimes> b)"
            using assms \<iota>_in_hom tensor_in_hom assoc_in_hom pentagon by simp
          also have "... = ((a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> (a \<otimes> \<a>[\<I>, \<I>, b])) \<cdot> \<a>[a, \<I> \<otimes> \<I>, b] \<cdot> (\<a>[a, \<I>, \<I>] \<otimes> b)"
            using assms \<iota>_in_hom tensor_in_hom assoc_in_hom lunit_in_hom by force
          also have "... = (a \<otimes> \<iota> \<otimes> b) \<cdot> \<a>[a, \<I> \<otimes> \<I>, b] \<cdot> (\<a>[a, \<I>, \<I>] \<otimes> b)"
            using assms lunit_commutes_with_L lunit_char(2) \<iota>_in_hom iso_assoc \<alpha>.components_are_iso
                  inv_is_inverse tensor_in_hom assoc_in_hom inv_in_hom comp_inv_arr interchange
            by simp
          also have "... = (\<a>[a, \<I>, b] \<cdot> ((a \<otimes> \<iota>) \<otimes> b)) \<cdot> (\<a>[a, \<I>, \<I>] \<otimes> b)"
            using assms \<iota>_in_hom tensor_in_hom assoc_naturality [of a \<iota> b] by simp
          also have "... = \<a>[a, \<I>, b] \<cdot> ((a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>] \<otimes> b)"
            using assms \<iota>_in_hom tensor_in_hom assoc_in_hom interchange by simp
          also have "... = \<a>[a, \<I>, b] \<cdot> ((\<r>[a] \<otimes> \<I>) \<otimes> b)"
            using assms runit_char(2) by simp
          also have "... = (\<r>[a] \<otimes> \<I> \<otimes> b) \<cdot> \<a>[a \<otimes> \<I>, \<I>, b]"
            using assms \<iota>_in_hom runit_in_hom assoc_naturality [of "\<r>[a]" \<I> b] by simp
          finally show ?thesis by blast
        qed
        show "(a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] = \<r>[a] \<otimes> \<I> \<otimes> b"
        proof -
          have "epi \<a>[a \<otimes> \<I>, \<I>, b]"
            using assms \<iota>_in_hom tensor_in_hom tensor_preserves_ide iso_assoc
                  iso_is_retraction retraction_is_epi
            by simp
          moreover have "seq ((a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b]) \<a>[a \<otimes> \<I>, \<I>, b]"
            using assms \<iota>_in_hom tensor_in_hom tensor_preserves_ide lunit_in_hom runit_in_hom
                  assoc_in_hom
            by simp
          moreover have "seq (\<r>[a] \<otimes> \<I> \<otimes> b) \<a>[a \<otimes> \<I>, \<I>, b]"
            using assms \<iota>_in_hom tensor_in_hom tensor_preserves_ide lunit_in_hom runit_in_hom
                  assoc_in_hom
            by simp
          ultimately show ?thesis
            using 1 epiE by blast
        qed
      qed
      text{*
         In \cite{Etingof15} it merely states that the preceding result suffices
         ``because any object of @{text C} is isomorphic to one of the form @{term "\<I> \<otimes> b"}.''
         However, it seems a little bit more involved than that to formally transport the
         equation @{text "(*)"} along the isomorphism @{term "\<l>[b]"} from @{term "\<I> \<otimes> b"}
         to @{term b}.
      *}
      have "(a \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, b] = ((a \<otimes> \<l>[b]) \<cdot> (a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> (a \<otimes> \<I> \<otimes> \<l>\<^sup>-\<^sup>1[b])) \<cdot>
                                     (a \<otimes> \<I> \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
      proof -
        have "\<a>[a, \<I>, b] = (a \<otimes> \<I> \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
        proof -
          have "(a \<otimes> \<I> \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])
                  = ((a \<otimes> \<I> \<otimes> \<l>[b]) \<cdot> (a \<otimes> \<I> \<otimes> \<l>\<^sup>-\<^sup>1[b])) \<cdot> \<a>[a, \<I>, b]"
            using assms \<iota>_in_hom tensor_in_hom lunit_in_hom iso_lunit
                  inv_is_inverse inv_in_hom assoc_naturality [of a \<I> "\<l>\<^sup>-\<^sup>1[b]"]
            by simp
          also have "... = (a \<otimes> \<I> \<otimes> \<l>[b] \<cdot> \<l>\<^sup>-\<^sup>1[b]) \<cdot> \<a>[a, \<I>, b]"
          proof -
            have "a \<cdot> a = a \<and> cod a = dom a" by (simp add: assms(1))
            moreover have 1: "antipar \<l>[b] (\<l>\<^sup>-\<^sup>1[b])"
              using assms iso_lunit inv_is_inverse by blast
            moreover have "seq (\<I> \<otimes> \<l>\<^sup>-\<^sup>1[b]) (\<I> \<otimes> \<l>[b])"
              using 1 L.preserves_seq by blast
            ultimately show ?thesis
              using assms L.preserves_comp_1 L.preserves_seq ideD(1) interchange
              by metis
          qed
          also have "... = \<a>[a, \<I>, b]"
            using assms \<iota>_in_hom tensor_in_hom lunit_in_hom iso_lunit inv_is_inverse inv_in_hom
                  comp_arr_inv
            by simp
          finally show ?thesis by presburger
        qed
        moreover have "a \<otimes> \<l>[b] = (a \<otimes> \<l>[b]) \<cdot> (a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> (a \<otimes> \<I> \<otimes> \<l>\<^sup>-\<^sup>1[b])"
          using assms \<iota>_in_hom tensor_in_hom lunit_in_hom iso_lunit inv_in_hom inv_is_inverse
                lunit_commutes_with_L \<iota>_in_hom tensor_in_hom lunit_in_hom comp_arr_dom
                interchange
          by auto
        ultimately show ?thesis by presburger
      qed
      also have "... = (a \<otimes> \<l>[b]) \<cdot> (a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> ((a \<otimes> \<I> \<otimes> \<l>\<^sup>-\<^sup>1[b]) \<cdot> (a \<otimes> \<I> \<otimes> \<l>[b])) \<cdot>
                       \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
        using assms \<iota>_in_hom tensor_in_hom lunit_in_hom iso_lunit inv_in_hom assoc_in_hom
        by force
      also have "... = (a \<otimes> \<l>[b]) \<cdot> (a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
      proof -
        have "(a \<otimes> \<I> \<otimes> \<l>\<^sup>-\<^sup>1[b]) \<cdot> (a \<otimes> \<I> \<otimes> \<l>[b]) = a \<otimes> \<I> \<otimes> \<I> \<otimes> b"
          using assms \<iota>_in_hom tensor_in_hom lunit_in_hom iso_lunit inv_in_hom inv_is_inverse
                interchange
          by auto
        thus ?thesis
          using assms \<iota>_in_hom tensor_in_hom lunit_in_hom iso_lunit inv_in_hom comp_cod_arr
                comp_ide_arr ide_unity tensor_preserves_ide
          by simp
      qed
      also have "... = (a \<otimes> \<l>[b]) \<cdot> ((a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b]) \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
        using assms \<iota>_in_hom tensor_in_hom lunit_in_hom iso_lunit inv_in_hom inv_is_inverse
        by simp
      also have "... = \<r>[a] \<otimes> b"
      proof -
        have "\<r>[a] \<otimes> b = (a \<otimes> \<l>[b]) \<cdot> (\<r>[a] \<otimes> \<I> \<otimes> b) \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
          using assms \<iota>_in_hom tensor_in_hom lunit_in_hom runit_in_hom iso_lunit inv_in_hom
                interchange runit_char(1) inv_is_inverse comp_arr_inv
          by auto
        thus ?thesis using assms * by presburger
      qed
      finally show ?thesis by blast
    qed

    lemma lunit_tensor_gen:
    assumes "ide a" and "ide b" and "ide c"
    shows "(a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c]) = a \<otimes> \<l>[b] \<otimes> c"
    proof -
      text{*
        We show that the lower right triangle in the following diagram commutes.
      *}
      text{*
$$\xymatrix{
  {@{term "((a \<otimes> \<I>) \<otimes> b) \<otimes> c"}}
     \ar[rrrr]^{\scriptsize @{term "\<a>[a, \<I>, b] \<otimes> c"}}
     \ar[ddd]_{\scriptsize @{term "\<a>[a \<otimes> \<I>, b, c]"}}
     \ar[drr]_{\scriptsize @{term "\<r>[a] \<otimes> b \<otimes> c"}}
  && &&
  {@{term "(a \<otimes> (\<I> \<otimes> b)) \<otimes> c"}}
     \ar[dll]^{\scriptsize @{term "(a \<otimes> \<l>[b]) \<otimes> c"}}
     \ar[ddd]^{\scriptsize @{term "\<a>[a, \<I> \<otimes> b, c]"}} \\
  && {@{term "(a \<otimes> b) \<otimes> c"}}
      \ar[d]^{\scriptsize @{term "\<a>[a, b, c]"}}    \\
  && {@{term "a \<otimes> b \<otimes> c"}}        \\
  {@{term "(a \<otimes> \<I>) \<otimes> b \<otimes> c"}}
      \ar[urr]^{\scriptsize @{term "\<r>[a] \<otimes> b \<otimes> c"}}
      \ar[drr]_{\scriptsize @{term "\<a>[a, \<I>, b \<otimes> c]"}}
  && &&
  {@{term "a \<otimes> (\<I> \<otimes> b) \<otimes> c"}}
      \ar[ull]_{\scriptsize @{term "a \<otimes> \<l>[b] \<otimes> c"}}
      \ar[dll]^{\scriptsize @{term "a \<otimes> \<a>[\<I>, b, c]"}}  \\
  && {@{term "a \<otimes> \<I> \<otimes> b \<otimes> c"}}
      \ar[uu]^{\scriptsize @{term "a \<otimes> \<l>[b \<otimes> c]"}}
}$$
      *}
      have "((a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c])) \<cdot> (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c))
              = (a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c]) \<cdot> \<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"
        using assms lunit_in_hom assoc_in_hom tensor_in_hom by force
      also have "... = ((a \<otimes> \<l>[b \<otimes> c]) \<cdot> \<a>[a, \<I>, b \<otimes> c]) \<cdot> \<a>[a \<otimes> \<I>, b, c]"
        using assms lunit_in_hom assoc_in_hom tensor_in_hom pentagon by simp
      also have "... = (\<r>[a] \<otimes> (b \<otimes> c)) \<cdot> \<a>[a \<otimes> \<I>, b, c]"
        using assms runit_in_hom assoc_in_hom tensor_in_hom triangle tensor_preserves_ide
        by auto
      also have "... = \<a>[a, b, c] \<cdot> ((\<r>[a] \<otimes> b) \<otimes> c)"
        using assms runit_in_hom tensor_in_hom assoc_naturality [of "\<r>[a]" b c] by force
      also have "... = (\<a>[a, b, c] \<cdot> ((a \<otimes> \<l>[b]) \<otimes> c)) \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"
        using assms lunit_in_hom runit_in_hom assoc_in_hom tensor_in_hom triangle interchange
        by force
      also have "... = ((a \<otimes> (\<l>[b] \<otimes> c)) \<cdot> \<a>[a, \<I> \<otimes> b, c]) \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"
        using assms lunit_in_hom assoc_in_hom tensor_in_hom assoc_naturality [of a "\<l>[b]" c]
        by force
      also have "... = (a \<otimes> (\<l>[b] \<otimes> c)) \<cdot> (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c))"
        using assms lunit_in_hom assoc_in_hom tensor_in_hom by force
      finally have 1: "((a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c])) \<cdot> \<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)
                        = (a \<otimes> (\<l>[b] \<otimes> c)) \<cdot> \<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"
        by blast
      text{*
        The result follows by cancelling the isomorphism
        @{term "\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"}
      *}
      have 2: "iso (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c))"
        using assms assoc_in_hom tensor_in_hom iso_assoc tensor_preserves_ide
              tensor_preserves_iso isos_compose
        by simp
      moreover have
          "seq ((a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c])) (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c))"
        using assms assoc_in_hom lunit_in_hom tensor_in_hom tensor_preserves_ide
        by force
      moreover have "seq (a \<otimes> (\<l>[b] \<otimes> c)) (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c))"
        using assms assoc_in_hom lunit_in_hom tensor_in_hom tensor_preserves_ide
        by force
      ultimately show ?thesis
        using 1 2 assms assoc_in_hom lunit_in_hom tensor_in_hom tensor_preserves_ide
              iso_is_retraction retraction_is_epi
              epiE [of "\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"
                       "(a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c])" "a \<otimes> \<l>[b] \<otimes> c"]
        by meson
    qed

    text{*
      The following result is quoted without proof as Theorem 7 of \cite{Kelly64} where it is
      attributed to MacLane \cite{MacLane63}.  It also appears as \cite{MacLane71},
      Exercise 1, page 161.  I did not succeed within a few hours to construct a proof following
      MacLane's hint.  The proof below is based on \cite{Etingof15}, Proposition 2.2.4.
    *}

    lemma lunit_tensor':
    assumes "ide c" and "ide d"
    shows "\<l>[c \<otimes> d] \<cdot> \<a>[\<I>, c, d] = \<l>[c] \<otimes> d"
    proof -
      have "L (\<l>[c \<otimes> d] \<cdot> \<a>[\<I>, c, d]) = L (\<l>[c] \<otimes> d)"
      proof -
        have "L (\<l>[c \<otimes> d] \<cdot> \<a>[\<I>, c, d]) = \<I> \<cdot> \<I> \<otimes> \<l>[c \<otimes> d] \<cdot> \<a>[\<I>, c, d]"
          using \<iota>_in_hom by simp
        also have "... = (\<I> \<otimes> \<l>[c \<otimes> d]) \<cdot> (\<I> \<otimes> \<a>[\<I>, c, d])"
          using assms lunit_in_hom assoc_in_hom tensor_in_hom tensor_preserves_ide
                interchange [of \<I> \<I>]
          by fastforce
        also have "... = L (\<l>[c] \<otimes> d)"
          using assms lunit_tensor_gen by simp
        finally show ?thesis by blast
      qed
      thus ?thesis
        using assms lunit_in_hom lunit_in_hom assoc_in_hom tensor_in_hom tensor_preserves_ide
              L.is_faithful [of "\<l>[c \<otimes> d] \<cdot> \<a>[\<I>, c, d]" "\<l>[c] \<otimes> d"]
        by force
    qed

    lemma lunit_tensor:
    assumes "ide a" and "ide b"
    shows "\<l>[a \<otimes> b] = (\<l>[a] \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, a, b]"
    proof -
      have "\<l>[a \<otimes> b] = \<l>[a \<otimes> b] \<cdot> (\<a>[\<I>, a, b] \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, a, b])"
        using assms assoc_inv assoc'_in_hom comp_arr_inv lunit_in_hom
              tensor_in_hom tensor_preserves_ide comp_arr_dom
        by force
      also have "... = (\<l>[a \<otimes> b] \<cdot> \<a>[\<I>, a, b]) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, a, b]"
        using assms lunit_in_hom assoc_in_hom assoc'_in_hom tensor_in_hom tensor_preserves_ide
        by force
      also have "... = (\<l>[a] \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, a, b]"
        using assms lunit_tensor' by auto
      finally show ?thesis by auto
    qed

    text{*
      We next show the corresponding result for the right unitor.
    *}
      
    lemma runit_tensor_gen:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<r>[a \<otimes> b] \<otimes> c = ((a \<otimes> \<r>[b]) \<otimes> c) \<cdot> (\<a>[a, b, \<I>] \<otimes> c)"
    proof -
      text{*
        We show that the upper right triangle in the following diagram commutes.
      *}
      text{*
$$\xymatrix{
  && {@{term "((a \<otimes> b) \<otimes> \<I>) \<otimes> c"}}
     \ar[dll]_{\scriptsize @{term "\<a>[a \<otimes> b, \<I>, c]"}}
     \ar[dd]^{\scriptsize @{term "\<r>[a \<otimes> b] \<otimes> c"}}
     \ar[drr]^{\scriptsize @{term "\<a>[a, b, \<I>] \<otimes> c"}} \\
  {@{term "(a \<otimes> b) \<otimes> \<I> \<otimes> c"}}
     \ar[ddd]_{\scriptsize @{term "\<a>[a, b, \<I> \<otimes> c]"}}
     \ar[drr]_{\scriptsize @{term "(a \<otimes> b) \<otimes> \<l>[c]"}}
  && &&
  {@{term "(a \<otimes> b \<otimes> \<I>) \<otimes> c"}}
     \ar[dll]^{\scriptsize @{term "(a \<otimes> \<r>[b]) \<otimes> c"}}
     \ar[ddd]^{\scriptsize @{term "\<a>[a, b \<otimes> \<I>, c]"}} \\
  && {@{term "(a \<otimes> b) \<otimes> c"}}
     \ar[d]^{\scriptsize @{term "\<a>[a, b, c]"}}     \\
  && {@{term "a \<otimes> b \<otimes> c"}}        \\
  {@{term "a \<otimes> b \<otimes> \<I> \<otimes> c"}}
     \ar[urr]^{\scriptsize @{term "a \<otimes> b \<otimes> \<l>[c]"}}
  && &&
  {@{term "a \<otimes> (b \<otimes> \<I>) \<otimes> c"}}
     \ar[llll]^{\scriptsize @{term "a \<otimes> \<a>[b, \<I>, c]"}}
     \ar[ull]_{\scriptsize @{term "a \<otimes> \<r>[b] \<otimes> c"}}
}$$
      *}
      have "\<r>[a \<otimes> b] \<otimes> c = ((a \<otimes> b) \<otimes> \<l>[c]) \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms triangle by simp
      also have "... = (\<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> (a \<otimes> b \<otimes> \<l>[c]) \<cdot> \<a>[a, b, \<I> \<otimes> c]) \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms assoc_naturality [of a b "\<l>[c]"] lunit_in_hom assoc_in_hom iso_assoc
              tensor_in_hom
              invert_side_of_triangle(1)
                 [of "(a \<otimes> b) \<otimes> \<l>[c]" "\<a>[a, b, c]" "(a \<otimes> b \<otimes> \<l>[c]) \<cdot> \<a>[a, b, \<I> \<otimes> c]"]
        by simp
      also have "... = \<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> (a \<otimes> b \<otimes> \<l>[c]) \<cdot> \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms assoc'_in_hom lunit_in_hom tensor_in_hom by force
      also have "... = \<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> ((a \<otimes> (\<r>[b] \<otimes> c)) \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, \<I>, c])) \<cdot>
                       \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms triangle lunit_in_hom assoc_in_hom tensor_in_hom interchange
              iso_assoc runit_in_hom assoc'_in_hom inv_tensor tensor_preserves_iso
              invert_side_of_triangle(2) [of "a \<otimes> \<a>[b, \<I>, c]" "a \<otimes> b \<otimes> \<l>[c]" "a \<otimes> \<r>[b] \<otimes> c"]
        by force
      also have "... = (\<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> (a \<otimes> (\<r>[b] \<otimes> c))) \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, \<I>, c]) \<cdot>
                       \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms assoc'_in_hom assoc_in_hom runit_in_hom tensor_in_hom by simp
      also have "... = (((a \<otimes> \<r>[b]) \<otimes> c) \<cdot> \<a>\<^sup>-\<^sup>1[a, b \<otimes> \<I>, c]) \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, \<I>, c]) \<cdot>
                       \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms assoc'_naturality [of a "\<r>[b]" c] runit_in_hom by simp
      also have "... = ((a \<otimes> \<r>[b]) \<otimes> c) \<cdot> \<a>\<^sup>-\<^sup>1[a, b \<otimes> \<I>, c] \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, \<I>, c]) \<cdot>
                       \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms runit_in_hom tensor_in_hom assoc'_in_hom by simp
      also have "... = ((a \<otimes> \<r>[b]) \<otimes> c) \<cdot> (\<a>[a, b, \<I>] \<otimes> c)"
      proof -
        have "\<a>\<^sup>-\<^sup>1[a, b \<otimes> \<I>, c] \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, \<I>, c]) \<cdot> \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]
                = \<a>[a, b, \<I>] \<otimes> c"
          using assms pentagon [of a b \<I> c] iso_assoc assoc_in_hom assoc'_in_hom
                tensor_in_hom inv_tensor tensor_preserves_iso
                invert_side_of_triangle(1)
                  [of "\<a>[a, b \<otimes> \<I>, c] \<cdot> (\<a>[a, b, \<I>] \<otimes> c)" "a \<otimes> \<a>[b, \<I>, c]"
                      "\<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"]
                invert_side_of_triangle(1)
                  [of "\<a>[a, b, \<I>] \<otimes> c" "\<a>[a, b \<otimes> \<I>, c]"
                      "(a \<otimes> \<a>\<^sup>-\<^sup>1[b, \<I>, c]) \<cdot> \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"]
          by simp
        thus ?thesis by simp
      qed
      finally show ?thesis by blast
    qed

    lemma runit_tensor:
    assumes "ide a" and "ide b"
    shows "\<r>[a \<otimes> b] = (a \<otimes> \<r>[b]) \<cdot> \<a>[a, b, \<I>]"
    proof -
      have "R ((a \<otimes> \<r>[b]) \<cdot> (\<a>[a, b, \<I>])) = R \<r>[a \<otimes> b]"
      proof -
        have "R ((a \<otimes> \<r>[b]) \<cdot> (\<a>[a, b, \<I>])) = (a \<otimes> \<r>[b]) \<cdot> \<a>[a, b, \<I>] \<otimes> \<I> \<cdot> \<I>"
          using \<iota>_in_hom by simp
        also have "... = ((a \<otimes> \<r>[b]) \<otimes> \<I>) \<cdot> (\<a>[a, b, \<I>] \<otimes> \<I>)"
          using assms runit_in_hom assoc_in_hom tensor_in_hom tensor_preserves_ide
                interchange [of \<I> \<I>]
          by fastforce
        also have "... = R \<r>[a \<otimes> b]"
          using assms runit_tensor_gen by simp
        finally show ?thesis by blast
      qed
      thus ?thesis
        using assms runit_in_hom assoc_in_hom tensor_in_hom tensor_preserves_ide
              R.is_faithful [of "(a \<otimes> \<r>[b]) \<cdot> (\<a>[a, b, \<I>])" "\<r>[a \<otimes> b]"]
        by force
    qed

    text {*
      Sometimes inverted forms of the triangle and pentagon axioms are useful.
    *}

    lemma triangle':
    assumes "ide a" and "ide b"
    shows "(a \<otimes> \<l>[b]) = (\<r>[a] \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[a, \<I>, b]"
    proof -
      have "(\<r>[a] \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[a, \<I>, b] = ((a \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, b]) \<cdot> \<a>\<^sup>-\<^sup>1[a, \<I>, b]"
          using assms triangle [of a b] by presburger
      also have "... = (a \<otimes> \<l>[b])"
        using assms assoc_in_hom assoc'_in_hom lunit_in_hom tensor_in_hom
              comp_arr_dom [of "a \<otimes> \<l>[b]"]
        by force
      finally show ?thesis by auto
    qed

    lemma pentagon':
    assumes "ide a" and "ide b" and "ide c" and "ide d"
    shows "((\<a>\<^sup>-\<^sup>1[a, b, c] \<otimes> d) \<cdot> \<a>\<^sup>-\<^sup>1[a, b \<otimes> c, d]) \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, c, d])
              = \<a>\<^sup>-\<^sup>1[a \<otimes> b, c, d] \<cdot> \<a>\<^sup>-\<^sup>1[a, b, c \<otimes> d]"
    proof -
      have "((\<a>\<^sup>-\<^sup>1[a, b, c] \<otimes> d) \<cdot> \<a>\<^sup>-\<^sup>1[a, b \<otimes> c, d]) \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, c, d])
              = inv ((a \<otimes> \<a>[b, c, d]) \<cdot> (\<a>[a, b \<otimes> c, d] \<cdot> (\<a>[a, b, c] \<otimes> d)))"
        using assms assoc_in_hom assoc'_in_hom tensor_in_hom ide_is_iso iso_assoc isos_compose
              tensor_preserves_iso tensor_preserves_ide inv_ide inv_tensor
              inv_comp [of "\<a>[a, b \<otimes> c, d]" "(a \<otimes> \<a>[b, c, d])"]
              inv_comp [of "\<a>[a, b, c] \<otimes> d" "(a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d]"]
        by simp
      also have "... = inv (\<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d])"
        using assms pentagon by presburger
      also have "... = \<a>\<^sup>-\<^sup>1[a \<otimes> b, c, d] \<cdot> \<a>\<^sup>-\<^sup>1[a, b, c \<otimes> d]"
        using assms assoc_in_hom tensor_in_hom ide_is_iso iso_assoc tensor_preserves_ide
              inv_comp [of "\<a>[a \<otimes> b, c, d]" "\<a>[a, b, c \<otimes> d]"]
        by simp
      finally show ?thesis by auto
    qed

    text{*
      The following non-obvious fact is Corollary 2.2.5 from \cite{Etingof15}.
      The statement that @{term "\<l>[\<I>] = \<r>[\<I>]"} is Theorem 6 from \cite{Kelly64}.
      MacLane \cite{MacLane71} does not show this, but assumes it as an axiom.
    *}

    lemma unitor_coincidence:
    shows "\<l>[\<I>] = \<iota>" and "\<r>[\<I>] = \<iota>"
    proof -
      have "\<l>[\<I>] \<otimes> \<I> = (\<I> \<otimes> \<l>[\<I>]) \<cdot> \<a>[\<I>, \<I>, \<I>]"
        using lunit_tensor' [of \<I> \<I>] lunit_commutes_with_L [of \<I>] by simp
      moreover have "(\<I> \<otimes> \<l>[\<I>]) \<cdot> \<a>[\<I>, \<I>, \<I>] = \<r>[\<I>] \<otimes> \<I>"
        using triangle [of \<I> \<I>] by simp
      moreover have "(\<I> \<otimes> \<l>[\<I>]) \<cdot> \<a>[\<I>, \<I>, \<I>] = \<iota> \<otimes> \<I>"
        using lunit_char(2) \<iota>_in_hom lunit_in_hom tensor_in_hom assoc_in_hom assoc'_in_hom
              comp_assoc_assoc'
        by force
      ultimately have "\<l>[\<I>] \<otimes> \<I> = \<iota> \<otimes> \<I> \<and> \<r>[\<I>] \<otimes> \<I> = \<iota> \<otimes> \<I>" by presburger
      moreover have "par \<l>[\<I>] \<iota> \<and> par \<r>[\<I>] \<iota>"
        using lunit_in_hom runit_in_hom \<iota>_in_hom tensor_in_hom by simp
      ultimately have 1: "\<l>[\<I>] = \<iota> \<and> \<r>[\<I>] = \<iota>"
        using R.is_faithful by blast
      show "\<l>[\<I>] = \<iota>" using 1 by auto
      show "\<r>[\<I>] = \<iota>" using 1 by auto
    qed

    lemma \<iota>_triangle:
    shows "\<iota> \<otimes> \<I> = (\<I> \<otimes> \<iota>) \<cdot> \<a>[\<I>, \<I>, \<I>]"
    and "(\<iota> \<otimes> \<I>) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>] = \<I> \<otimes> \<iota>"
      using triangle [of \<I> \<I>] unitor_coincidence
       apply simp
      using triangle' [of \<I> \<I>] unitor_coincidence
      by simp

    text{*
      The only isomorphism that commutes with @{term \<iota>} is @{term \<I>}.
    *}

    lemma iso_commuting_with_\<iota>_equals_\<I>:
    assumes "f \<in> hom \<I> \<I>" and "iso f" and "f \<cdot> \<iota> = \<iota> \<cdot> (f \<otimes> f)"
    shows "f = \<I>"
    proof -
      have 1: "f \<otimes> f = f \<otimes> \<I>"
      proof -
        have "f \<otimes> f = (inv \<iota> \<cdot> \<iota>) \<cdot> (f \<otimes> f)"
          using assms \<iota>_in_hom \<iota>_is_iso inv_is_inverse comp_inv_arr by simp
        also have "... = (inv \<iota> \<cdot> f) \<cdot> \<iota>"
          using assms \<iota>_in_hom \<iota>_is_iso tensor_in_hom inv_in_hom inv_is_inverse by simp
        also have "... = ((f \<otimes> \<I>) \<cdot> inv \<iota>) \<cdot> \<iota>"
          using assms unitor_coincidence runit'_naturality [of f] by simp
        also have "... = f \<otimes> \<I>"
          using assms \<iota>_in_hom \<iota>_is_iso tensor_in_hom inv_in_hom inv_is_inverse comp_inv_arr
          by simp
        finally show ?thesis by blast
      qed
      moreover have "(f \<otimes> f) \<cdot> (inv f \<otimes> \<I>) = \<I> \<otimes> f \<and> (f \<otimes> \<I>) \<cdot> (inv f \<otimes> \<I>) = \<I> \<otimes> \<I>"
        using assms inv_is_inverse inv_in_hom interchange comp_arr_inv by auto
      ultimately have "\<I> \<otimes> f = \<I> \<otimes> \<I>" by metis
      moreover have "par f \<I>"
        using assms tensor_in_hom by auto
      ultimately have "f = \<I>"
        using L.is_faithful by blast
      thus ?thesis using 1 by blast
    qed

  end

  text{*
    We now show that the unit @{text \<iota>} of a monoidal category is unique up to a unique
    isomorphism (Proposition 2.2.6 of \cite{Etingof15}).
  *}

  locale monoidal_category_with_alternate_unit =
    monoidal_category C T \<alpha> \<iota> +
    C\<^sub>1: monoidal_category C T \<alpha> \<iota>\<^sub>1
  for C :: "'a comp"                            (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a
  and \<iota>\<^sub>1 :: 'a +
  assumes \<iota>\<^sub>1_in_hom: "\<iota>\<^sub>1 \<in> hom (T (cod \<iota>\<^sub>1, cod \<iota>\<^sub>1)) (cod \<iota>\<^sub>1)"
  and \<iota>\<^sub>1_is_iso: "iso \<iota>\<^sub>1"
  begin

    no_notation C\<^sub>1.tensor                       (infixr "\<otimes>" 53)
    no_notation C\<^sub>1.unity                        ("\<I>")
    no_notation C\<^sub>1.lunit                        ("\<l>[_]")
    no_notation C\<^sub>1.runit                        ("\<r>[_]")
    no_notation C\<^sub>1.assoc                        ("\<a>[_, _, _]")
    no_notation C\<^sub>1.assoc'                       ("\<a>\<^sup>-\<^sup>1[_, _, _]")

    notation C\<^sub>1.tensor                          (infixr "\<otimes>\<^sub>1" 53)
    notation C\<^sub>1.unity                           ("\<I>\<^sub>1")
    notation C\<^sub>1.lunit                           ("\<l>\<^sub>1[_]")
    notation C\<^sub>1.runit                           ("\<r>\<^sub>1[_]")
    notation C\<^sub>1.assoc                           ("\<a>\<^sub>1[_, _, _]")
    notation C\<^sub>1.assoc'                          ("\<a>\<^sub>1\<^sup>-\<^sup>1[_, _, _]")

    definition i
    where "i \<equiv> \<l>[\<I>\<^sub>1] \<cdot> inv \<r>\<^sub>1[\<I>]"

    lemma iso_i:
    shows "i \<in> hom \<I> \<I>\<^sub>1" and "iso i"
    proof -
      show "i \<in> hom \<I> \<I>\<^sub>1"
        using lunit_in_hom C\<^sub>1.runit_in_hom C\<^sub>1.iso_runit inv_in_hom i_def by simp
      show "iso i"
        using iso_lunit C\<^sub>1.iso_runit lunit_in_hom C\<^sub>1.runit_in_hom
              inv_in_hom iso_inv_iso isos_compose i_def
        by simp
    qed

    text{*
      The following is Exercise 2.2.7 of \cite{Etingof15}.
    *}

    lemma i_maps_\<iota>_to_\<iota>\<^sub>1:
    shows "i \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (i \<otimes> i)"
    proof -
      have 1: "inv \<r>\<^sub>1[\<I>] \<cdot> \<iota> = (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]) \<cdot> (inv \<r>\<^sub>1[\<I>] \<otimes> inv \<r>\<^sub>1[\<I>])"
      proof -
        have "\<iota> \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]) = \<r>\<^sub>1[\<I>] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1])"
        proof -
          text {*
$$\xymatrix{
  && {@{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dddll]_{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dddrr]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]"}}
  \\
  \\
  && {@{term[source=true] "\<I> \<otimes> \<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dll]^{\scriptsize @{term[source=true] "\<I> \<otimes> \<r>\<^sub>1[\<I>]"}}
     \ar[drr]_{\scriptsize @{term[source=true] "\<I> \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1]"}}
  \\
  {@{term[source=true] "\<I> \<otimes> \<I>"}}
     \ar[dddrr]_{\scriptsize @{term[source=true] "\<iota>"}}
  &&
  &&
  {@{term[source=true] "\<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dddll]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>]"}}
  \\
  && {@{ term[source=true] "(\<I> \<otimes> \<I>) \<otimes> \<I>\<^sub>1"}}
     \ar[ull]_{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I> \<otimes> \<I>]"}}
     \ar[urr]^{\scriptsize @{term[source=true] "\<iota> \<otimes> \<I>"}}
  \\
  \\
  && {@{term[source=true] "\<I>"}}
}$$
          *}
          have "\<iota> \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]) = \<iota> \<cdot> (\<I> \<otimes> \<r>\<^sub>1[\<I>]) \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using C\<^sub>1.runit_in_hom interchange by simp
          also have "... = \<iota> \<cdot> (\<r>\<^sub>1[\<I> \<otimes> \<I>] \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1]) \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using C\<^sub>1.runit_tensor [of \<I> \<I>] C\<^sub>1.runit_in_hom assoc'_in_hom 
                  invert_side_of_triangle(2) [of "\<a>[\<I>, \<I>, \<I>\<^sub>1]" "\<I> \<otimes> \<r>\<^sub>1[\<I>]" "\<r>\<^sub>1[\<I> \<otimes> \<I>]"]
            by simp
          also have "... = (\<iota> \<cdot> \<r>\<^sub>1[\<I> \<otimes> \<I>]) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using \<iota>_in_hom C\<^sub>1.runit_in_hom tensor_in_hom assoc'_in_hom by simp
          also have "... = (\<r>\<^sub>1[\<I>] \<cdot> (\<iota> \<otimes> \<I>\<^sub>1)) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using C\<^sub>1.runit_naturality [of \<iota>] \<iota>_in_hom by simp
          also have "... = \<r>\<^sub>1[\<I>] \<cdot> ((\<iota> \<otimes> \<I>\<^sub>1) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1]) \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using \<iota>_in_hom C\<^sub>1.runit_in_hom tensor_in_hom assoc'_in_hom by simp
          also have "... = \<r>\<^sub>1[\<I>] \<cdot> (\<I> \<otimes> \<l>[\<I>\<^sub>1]) \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using lunit_tensor [of \<I> \<I>\<^sub>1] lunit_commutes_with_L unitor_coincidence by simp
          also have "... = \<r>\<^sub>1[\<I>] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1])"
            using C\<^sub>1.runit_in_hom lunit_in_hom interchange by simp
          finally show ?thesis by blast
        qed
        moreover have "seq \<iota> (\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]) \<and> seq \<r>\<^sub>1[\<I>] (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1])"
          using C\<^sub>1.runit_in_hom \<iota>_in_hom tensor_in_hom lunit_in_hom by simp
        moreover have "iso \<r>\<^sub>1[\<I>] \<and> iso (\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>])"
          using C\<^sub>1.iso_runit tensor_preserves_iso by force
        ultimately show ?thesis
          using invert_opposite_sides_of_square [of "\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]" "\<r>\<^sub>1[\<I>]" "\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]" \<iota>]
                inv_tensor
          by simp
      qed
      have 2: "\<l>[\<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]) = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1])"
      proof -
        text {*
$$\xymatrix{
  && {@{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> (\<I> \<otimes> \<I>\<^sub>1)"}}
     \ar[dddll]_{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[dd]^{\scriptsize @{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[dddrr]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]"}}
  \\
  \\
  && {@{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<I>\<^sub>1"}}
     \ar[dll]^{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1] \<otimes> \<I>\<^sub>1"}}
     \ar[drr]_{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<I>\<^sub>1"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1]"}}
  \\
  {@{term[source=true] "\<I>\<^sub>1 \<otimes> \<I>\<^sub>1"}}
     \ar[dddrr]_{\scriptsize @{term[source=true] "\<iota>\<^sub>1"}}
  &&
  &&
  {@{term[source=true] "\<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dddll]^{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1]"}}
  \\
  && {@{term[source=true] "\<I> \<otimes> \<I>\<^sub>1 \<otimes> \<I>\<^sub>1"}}
     \ar[ull]_{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1 \<otimes> \<I>\<^sub>1]"}}
     \ar[urr]^{\scriptsize @{term[source=true] "\<I> \<otimes> \<iota>\<^sub>1"}}
  \\
  \\
  && {@{term[source=true] "\<I>\<^sub>1"}}
}$$
        *}
        have "\<l>[\<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]) = \<l>[\<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I>\<^sub>1) \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using lunit_in_hom C\<^sub>1.runit_in_hom interchange by force
        also have "... = \<l>[\<I>\<^sub>1] \<cdot> ((\<I> \<otimes> \<iota>\<^sub>1) \<cdot> \<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1]) \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using C\<^sub>1.runit_tensor [of \<I> \<I>\<^sub>1] C\<^sub>1.unitor_coincidence C\<^sub>1.runit_commutes_with_R
          by simp
        also have "... = (\<l>[\<I>\<^sub>1] \<cdot> (\<I> \<otimes> \<iota>\<^sub>1)) \<cdot> \<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1] \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using lunit_in_hom assoc_in_hom tensor_in_hom C\<^sub>1.\<iota>_in_hom by simp
        also have "... = (\<iota>\<^sub>1 \<cdot> \<l>[\<I>\<^sub>1 \<otimes> \<I>\<^sub>1]) \<cdot> \<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1] \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using lunit_naturality [of \<iota>\<^sub>1] C\<^sub>1.\<iota>_in_hom lunit_commutes_with_L by simp
        also have "... = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1 \<otimes> \<I>\<^sub>1] \<cdot> \<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1]) \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using C\<^sub>1.\<iota>_in_hom lunit_in_hom tensor_in_hom assoc_in_hom by simp
        also have "... = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1] \<otimes> \<I>\<^sub>1) \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using lunit_tensor' by auto
        also have "... = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1])"
          using lunit_in_hom interchange by simp
        finally show ?thesis by blast
      qed
      show ?thesis
      proof -
        text {*
$$\xymatrix{
  {@{term[source=true] "\<I>\<^sub>1 \<otimes> \<I>\<^sub>1"}}
     \ar[dd]_{\scriptsize @{term "\<iota>\<^sub>1"}}
  &&
  {@{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> (\<I> \<otimes> \<I>\<^sub>1)"}}
     \ar[ll]_{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[rr]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]"}}
  &&
  {@{term[source=true] "\<I>\<^sub>1 \<otimes> \<I>\<^sub>1"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<iota>"}}
  \\
  \\
  {@{term[source=true] "\<I>\<^sub>1"}}
  &&
  {@{term[source=true] "\<I> \<otimes> \<I>\<^sub>1"}}
     \ar[ll]_{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1]"}}
     \ar[rr]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>]"}}
  &&
  {@{term[source=true] "\<I>"}}
}$$
        *}
        have "i \<cdot> \<iota> = \<l>[\<I>\<^sub>1] \<cdot> inv \<r>\<^sub>1[\<I>] \<cdot> \<iota>"
          using lunit_in_hom C\<^sub>1.runit'_in_hom \<iota>_in_hom i_def by simp
        also have "... = \<l>[\<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]) \<cdot> (inv \<r>\<^sub>1[\<I>] \<otimes> inv \<r>\<^sub>1[\<I>])"
          using 1 by presburger
        also have "... = (\<l>[\<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1])) \<cdot> (inv \<r>\<^sub>1[\<I>] \<otimes> inv \<r>\<^sub>1[\<I>])"
          using lunit_in_hom C\<^sub>1.runit_in_hom tensor_in_hom C\<^sub>1.runit'_in_hom by simp
        also have "... =  (\<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1])) \<cdot> (inv \<r>\<^sub>1[\<I>] \<otimes> inv \<r>\<^sub>1[\<I>])"
          using 2 by presburger
        also have "... = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1]) \<cdot> (inv \<r>\<^sub>1[\<I>] \<otimes> inv \<r>\<^sub>1[\<I>])"
          using C\<^sub>1.\<iota>_in_hom lunit_in_hom C\<^sub>1.runit_in_hom tensor_in_hom C\<^sub>1.runit'_in_hom
          by simp
        also have "... = \<iota>\<^sub>1 \<cdot> (i \<otimes> i)"
          using lunit_in_hom C\<^sub>1.runit'_in_hom interchange i_def by simp
        finally show ?thesis by blast
      qed
    qed

    lemma i_uniqueness:
    assumes "f \<in> hom \<I> \<I>\<^sub>1" and "iso f" and "f \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (f \<otimes> f)"
    shows "f = i"
    proof -
      have "inv i \<cdot> f = \<I>"
      proof -
        have "inv i \<cdot> f \<in> hom \<I> \<I> \<and> iso (inv i \<cdot> f) \<and>
              (inv i \<cdot> f) \<cdot> \<iota> = \<iota> \<cdot> (inv i \<cdot> f \<otimes> inv i \<cdot> f)"
        proof -
          have "inv i \<cdot> f \<in> hom \<I> \<I> \<and> iso (inv i \<cdot> f)"
            using assms iso_i inv_in_hom iso_inv_iso isos_compose by simp
          moreover have "(inv i \<cdot> f) \<cdot> \<iota> = \<iota> \<cdot> (inv i \<cdot> f \<otimes> inv i \<cdot> f)"
          proof -
            have "(inv i \<cdot> f) \<cdot> \<iota> = (inv i \<cdot> \<iota>\<^sub>1) \<cdot> (f \<otimes> f)"
              using assms iso_i inv_in_hom \<iota>_in_hom \<iota>\<^sub>1_in_hom by simp
            also have "... = (\<iota> \<cdot> (inv i \<otimes> inv i)) \<cdot> (f \<otimes> f)"
            proof -
              have "inv i \<cdot> \<iota>\<^sub>1 = \<iota> \<cdot> (inv i \<otimes> inv i)"
                using assms iso_i invert_opposite_sides_of_square [of \<iota> i "i \<otimes> i" \<iota>\<^sub>1 ]
                      inv_tensor [of i i] \<iota>_in_hom \<iota>\<^sub>1_in_hom tensor_in_hom tensor_preserves_iso
                      inv_in_hom i_maps_\<iota>_to_\<iota>\<^sub>1
                by simp
              thus ?thesis by presburger
            qed
            also have "... = \<iota> \<cdot> (inv i \<cdot> f \<otimes> inv i \<cdot> f)"
              using assms \<iota>_in_hom iso_i inv_in_hom tensor_in_hom interchange by simp
            finally show ?thesis by blast
          qed
          ultimately show ?thesis by fast
        qed
        thus ?thesis using iso_commuting_with_\<iota>_equals_\<I> [of "inv i \<cdot> f"] by simp
      qed
      hence "inverse_arrows (inv i) f"
        using iso_i section_retraction_of_iso(2) [of "inv i" f] iso_inv_iso
        by (simp add: section_retractionI)
      moreover have "inverse_arrows (inv i) i"
        using iso_i inv_is_inverse [of i] iso_inv_iso inverse_arrows_sym by simp
      ultimately show "f = i"
        using inverse_arrow_unique by simp
    qed

    lemma unit_unique_upto_unique_iso:
    shows "\<exists>!f. f \<in> hom \<I> \<I>\<^sub>1 \<and> iso f \<and> f \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (f \<otimes> f)"
    proof
      show "i \<in> hom \<I> \<I>\<^sub>1 \<and> iso i \<and> i \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (i \<otimes> i)"
        using iso_i i_maps_\<iota>_to_\<iota>\<^sub>1 by auto
      show "\<And>f. f \<in> hom \<I> \<I>\<^sub>1 \<and> iso f \<and> f \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (f \<otimes> f) \<Longrightarrow> f = i"
      proof -
        fix f
        assume f: "f \<in> hom \<I> \<I>\<^sub>1 \<and> iso f \<and> f \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (f \<otimes> f)"
        hence "inv i \<cdot> f \<in> hom \<I> \<I> \<and> iso (inv i \<cdot> f)"
          using iso_i inv_in_hom isos_compose iso_inv_iso by simp
        moreover have "(inv i \<cdot> f) \<cdot> \<iota> = \<iota> \<cdot> (inv i \<cdot> f \<otimes> inv i \<cdot> f)"
        proof -
          have "(inv i \<cdot> f) \<cdot> \<iota> = inv i \<cdot> f \<cdot> \<iota>"
            using f iso_i inv_in_hom \<iota>_in_hom by simp
          also have "... = inv i \<cdot> \<iota>\<^sub>1 \<cdot> (f \<otimes> f)"
            using f by simp
          also have "... = (inv i \<cdot> \<iota>\<^sub>1) \<cdot> (f \<otimes> f)"
            using f iso_i inv_in_hom \<iota>\<^sub>1_in_hom tensor_in_hom by simp
          also have "... = (\<iota> \<cdot> (inv i \<otimes> inv i)) \<cdot> (f \<otimes> f)"
          proof -
            have "seq i \<iota> \<and> seq \<iota>\<^sub>1 (i \<otimes> i) \<and> iso (i \<otimes> i) \<and> inv (i \<otimes> i) = inv i \<otimes> inv i"
              using iso_i \<iota>_in_hom \<iota>\<^sub>1_in_hom tensor_preserves_iso inv_tensor by auto
            thus ?thesis
              using iso_i i_maps_\<iota>_to_\<iota>\<^sub>1 invert_opposite_sides_of_square [of \<iota> i "i \<otimes> i" \<iota>\<^sub>1]
              by presburger
          qed
          also have "... =  \<iota> \<cdot> (inv i \<cdot> f \<otimes> inv i \<cdot> f)"
            using f iso_i inv_in_hom \<iota>_in_hom interchange by simp
          finally show ?thesis by blast
        qed
        ultimately have "inv i \<cdot> f = \<I>"
          using i_uniqueness [of "inv i \<cdot> f"] iso_commuting_with_\<iota>_equals_\<I> by blast
        hence "section_retraction f (inv i)"
          using f iso_i iso_inv_iso inv_in_hom by auto
        thus "f = i"
          using section_retraction_of_iso(2) [of "inv i" f] inverse_arrow_unique inv_is_inverse
                inv_inv iso_inv_iso iso_i
          by blast
      qed
    qed

  end

  section "Elementary Monoidal Category"

  text{*
    Although the economy of data assumed by @{locale monoidal_category} is useful for general
    results, to establish interpretations it is more convenient to work with a traditional
    definition of monoidal category.  The following locale provides such a definition.
    It permits a monoidal category to be specified by giving the tensor product and the
    components of the associator and unitors, which are required only to satisfy elementary
    conditions that imply functoriality and naturality, without having to worry about
    extensionality or formal interpretations for the various functors and natural transformations.
  *}

  locale elementary_monoidal_category =
    category C
  for C :: "'a comp"                  (infixr "\<cdot>" 55)
  and tensor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<otimes>" 53)
  and unity :: 'a                      ("\<I>")
  and lunit :: "'a \<Rightarrow> 'a"              ("\<l>[_]")
  and runit :: "'a \<Rightarrow> 'a"              ("\<r>[_]")
  and assoc :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>[_, _, _]") +
  assumes ide_unity [simp]: "ide \<I>"
  and iso_lunit: "ide a \<Longrightarrow> iso \<l>[a]"
  and iso_runit: "ide a \<Longrightarrow> iso \<r>[a]"
  and iso_assoc: "\<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow> iso \<a>[a, b, c]"
  and tensor_in_hom [simp]: "\<lbrakk> f \<in> hom a b; g \<in> hom c d \<rbrakk> \<Longrightarrow> (f \<otimes> g) \<in> hom (a \<otimes> c) (b \<otimes> d)"
  and tensor_preserves_ide: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> ide (a \<otimes> b)"
  and interchange: "\<lbrakk> seq g f; seq g' f' \<rbrakk> \<Longrightarrow> (g \<otimes> g') \<cdot> (f \<otimes> f') = g \<cdot> f \<otimes> g' \<cdot> f'"
  and lunit_in_hom [simp]: "ide a \<Longrightarrow> \<l>[a] \<in> hom (\<I> \<otimes> a) a"
  and lunit_naturality: "arr f \<Longrightarrow> \<l>[cod f] \<cdot> (\<I> \<otimes> f) = f \<cdot> \<l>[dom f]"
  and runit_in_hom [simp]: "ide a \<Longrightarrow> \<r>[a] \<in> hom (a \<otimes> \<I>) a"
  and runit_naturality: "arr f \<Longrightarrow> \<r>[cod f] \<cdot> (f \<otimes> \<I>) = f \<cdot> \<r>[dom f]"
  and assoc_in_hom [simp]:
      "\<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow> \<a>[a, b, c] \<in> hom ((a \<otimes> b) \<otimes> c) (a \<otimes> (b \<otimes> c))"
  and assoc_naturality:
      "\<lbrakk> arr f0; arr f1; arr f2 \<rbrakk> \<Longrightarrow> \<a>[cod f0, cod f1, cod f2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2)
                                        = (f0 \<otimes> (f1 \<otimes> f2)) \<cdot> \<a>[dom f0, dom f1, dom f2]"
  and triangle: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> (a \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, b] = \<r>[a] \<otimes> b"
  and pentagon: "\<lbrakk> ide a; ide b; ide c; ide d \<rbrakk> \<Longrightarrow>
                   (a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d] \<cdot> (\<a>[a, b, c] \<otimes> d)
                     = \<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d]"

  text{*
    An interpretation for the @{text monoidal_category} locale readily induces an
    interpretation for the @{text elementary_monoidal_category} locale.
  *}
      
  context monoidal_category
  begin

    lemma induces_elementary_monoidal_category:
      shows "elementary_monoidal_category C tensor \<I> lunit runit assoc"
        using \<iota>_in_hom iso_assoc tensor_preserves_ide assoc_in_hom tensor_in_hom
              assoc_naturality lunit_naturality runit_naturality lunit_in_hom runit_in_hom
              iso_lunit iso_runit interchange pentagon triangle
        apply unfold_locales by auto

  end

  context elementary_monoidal_category
  begin

    interpretation CC: product_category C C ..
    interpretation CCC: product_category C CC.comp ..

    text{*
      To avoid name clashes between the @{locale monoidal_category} and
      @{locale elementary_monoidal_category} locales, some constants for which definitions
      are needed here are given separate names from the versions in @{locale monoidal_category}.
      We eventually show that the locally defined versions are equal to their counterparts
      in @{locale monoidal_category}.
    *}
      
    definition T\<^sub>E\<^sub>M\<^sub>C :: "'a * 'a \<Rightarrow> 'a"
    where "T\<^sub>E\<^sub>M\<^sub>C f \<equiv> if CC.arr f then (fst f \<otimes> snd f) else null"

    lemma T_simp [simp]:
    assumes "arr f" and "arr g"
    shows "T\<^sub>E\<^sub>M\<^sub>C (f, g) = f \<otimes> g"
      using assms T\<^sub>E\<^sub>M\<^sub>C_def by simp

    definition L\<^sub>E\<^sub>M\<^sub>C
    where "L\<^sub>E\<^sub>M\<^sub>C \<equiv> \<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (\<I>, f)"

    definition R\<^sub>E\<^sub>M\<^sub>C :: "'a \<Rightarrow> 'a"
    where "R\<^sub>E\<^sub>M\<^sub>C \<equiv> \<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (f, \<I>)"

    definition \<alpha>
    where "\<alpha> f \<equiv> if CCC.arr f then (fst f \<otimes> (fst (snd f) \<otimes> snd (snd f))) \<cdot>
                                   \<a>[dom (fst f), dom (fst (snd f)), dom (snd (snd f))]
                  else null"

    lemma \<alpha>_ide_simp [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<alpha> (a, b, c) = \<a>[a, b, c]"
      unfolding \<alpha>_def using assms assoc_in_hom comp_cod_arr by fastforce
      
    definition \<ll>\<^sub>E\<^sub>M\<^sub>C
    where "\<ll>\<^sub>E\<^sub>M\<^sub>C f \<equiv> if arr f then f \<cdot> \<l>[dom f] else null"

    definition \<rho>\<^sub>E\<^sub>M\<^sub>C
    where "\<rho>\<^sub>E\<^sub>M\<^sub>C f \<equiv> if arr f then f \<cdot> \<r>[dom f] else null"

    interpretation T: binary_endofunctor C T\<^sub>E\<^sub>M\<^sub>C
      apply unfold_locales
      using tensor_in_hom interchange T\<^sub>E\<^sub>M\<^sub>C_def by auto

    lemma binary_endofunctor_T:
    shows "binary_endofunctor C T\<^sub>E\<^sub>M\<^sub>C" ..

    interpretation ToTC: "functor" CCC.comp C T.ToTC
      using T.functor_ToTC by auto

    interpretation ToCT: "functor" CCC.comp C T.ToCT
      using T.functor_ToCT by auto

    interpretation L: "functor" C C L\<^sub>E\<^sub>M\<^sub>C
      using T.fixing_ide_gives_functor_1 [of \<I>] L\<^sub>E\<^sub>M\<^sub>C_def by auto

    lemma functor_L:
    shows "functor C C L\<^sub>E\<^sub>M\<^sub>C" ..

    interpretation R: "functor" C C R\<^sub>E\<^sub>M\<^sub>C
      using T.fixing_ide_gives_functor_2 [of \<I>] R\<^sub>E\<^sub>M\<^sub>C_def by auto

    lemma functor_R:
    shows "functor C C R\<^sub>E\<^sub>M\<^sub>C" ..
        
    interpretation \<alpha>: natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>
    proof -
      interpret \<alpha>: transformation_by_components CCC.comp C T.ToTC T.ToCT \<alpha>
        apply unfold_locales
        using T.preserves_ide T.preserves_hom assoc_in_hom assoc_naturality interchange
              T.ToCT_def T.ToTC_def \<alpha>_def T\<^sub>E\<^sub>M\<^sub>C_def
        by auto
      have 1: "\<And>f. CCC.arr f \<Longrightarrow>
                      dom (fst f) = fst (CCC.dom f) \<and>
                      dom (fst (snd f)) = fst (snd (CCC.dom f)) \<and>
                      dom (snd (snd f)) = snd (snd (CCC.dom f)) \<and>
                      cod (fst f) = fst (CCC.cod f) \<and>
                      cod (fst (snd f)) = fst (snd (CCC.cod f)) \<and>
                      cod (snd (snd f)) = snd (snd (CCC.cod f))"
        by simp
      interpret \<alpha>: natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>.map
        apply unfold_locales
        using 1 iso_assoc \<alpha>.map_simp_ide assoc_in_hom tensor_preserves_ide \<alpha>_def by auto
      have "\<alpha> = \<alpha>.map"
      proof
        fix f
        have "\<not>CCC.arr f \<Longrightarrow> \<alpha> f = \<alpha>.map f" using \<alpha>.map_def \<alpha>_def by auto
        moreover have "CCC.arr f \<Longrightarrow> \<alpha> f = \<alpha>.map f"
          using 1 assoc_naturality \<alpha>_def
                assoc_in_hom [of "fst (CCC.cod f)" "fst (snd (CCC.cod f))" "snd (snd (CCC.cod f))"]
                comp_cod_arr
                  [of "\<a>[fst (CCC.cod f), fst (snd (CCC.cod f)), snd (snd (CCC.cod f))]"]
                T.preserves_arr T.ToTC_def T\<^sub>E\<^sub>M\<^sub>C_def \<alpha>.map_def
          by auto
        ultimately show "\<alpha> f = \<alpha>.map f" using \<alpha>_def by auto
      qed
      thus "natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>"
        using \<alpha>.natural_isomorphism_axioms by simp
    qed

    lemma natural_isomorphism_\<alpha>:
    shows "natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>" ..

    interpretation \<alpha>': inverse_transformation CCC.comp C T.ToTC T.ToCT \<alpha> ..

    interpretation \<ll>: natural_isomorphism C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>\<^sub>E\<^sub>M\<^sub>C
    proof -
      interpret \<ll>: transformation_by_components C C L\<^sub>E\<^sub>M\<^sub>C map "\<lambda>a. \<l>[a]"
        apply unfold_locales
        using lunit_in_hom lunit_naturality T_simp L\<^sub>E\<^sub>M\<^sub>C_def by auto
      interpret \<ll>: natural_isomorphism C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>.map
        apply unfold_locales
        using iso_lunit \<ll>.map_simp_ide by simp
      have "\<ll>.map = \<ll>\<^sub>E\<^sub>M\<^sub>C"
        using \<ll>.map_def lunit_naturality T_simp \<ll>\<^sub>E\<^sub>M\<^sub>C_def L\<^sub>E\<^sub>M\<^sub>C_def by fastforce
      thus "natural_isomorphism C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>\<^sub>E\<^sub>M\<^sub>C"
        using \<ll>.natural_isomorphism_axioms by force
    qed

    lemma natural_isomorphism_\<ll>:
    shows "natural_isomorphism C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>\<^sub>E\<^sub>M\<^sub>C" ..

    interpretation \<ll>': inverse_transformation C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>\<^sub>E\<^sub>M\<^sub>C ..

    interpretation \<rho>: natural_isomorphism C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>\<^sub>E\<^sub>M\<^sub>C
    proof -
      interpret \<rho>: transformation_by_components C C R\<^sub>E\<^sub>M\<^sub>C map "\<lambda>a. \<r>[a]"
        apply unfold_locales
        using tensor_in_hom runit_in_hom runit_naturality T_simp R\<^sub>E\<^sub>M\<^sub>C_def by auto
      interpret \<rho>: natural_isomorphism C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>.map
        apply unfold_locales
        using iso_runit \<rho>.map_simp_ide by simp
      have "\<rho>\<^sub>E\<^sub>M\<^sub>C = \<rho>.map"
        using \<rho>.map_def runit_naturality T_simp \<rho>\<^sub>E\<^sub>M\<^sub>C_def R\<^sub>E\<^sub>M\<^sub>C_def by fastforce
      thus "natural_isomorphism C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>\<^sub>E\<^sub>M\<^sub>C"
        using \<rho>.natural_isomorphism_axioms by force
    qed

    lemma natural_isomorphism_\<rho>:
    shows "natural_isomorphism C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>\<^sub>E\<^sub>M\<^sub>C" ..

    interpretation \<rho>': inverse_transformation C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>\<^sub>E\<^sub>M\<^sub>C ..

    text{*
      The endofunctors @{term L\<^sub>E\<^sub>M\<^sub>C} and @{term R\<^sub>E\<^sub>M\<^sub>C} are equivalence functors,
      due to the existence of the unitors.
    *}

    lemma L_is_equivalence_functor:
    shows "equivalence_functor C C L\<^sub>E\<^sub>M\<^sub>C"
    proof -
      interpret endofunctor C L\<^sub>E\<^sub>M\<^sub>C ..
      show ?thesis
        using isomorphic_to_identity_is_equivalence \<ll>.natural_isomorphism_axioms by simp
    qed

    interpretation L: equivalence_functor C C L\<^sub>E\<^sub>M\<^sub>C
      using L_is_equivalence_functor by auto

    lemma R_is_equivalence_functor:
    shows "equivalence_functor C C R\<^sub>E\<^sub>M\<^sub>C"
    proof -
      interpret endofunctor C R\<^sub>E\<^sub>M\<^sub>C ..
      show ?thesis
        using isomorphic_to_identity_is_equivalence \<rho>.natural_isomorphism_axioms by simp
    qed

    interpretation R: equivalence_functor C C R\<^sub>E\<^sub>M\<^sub>C
      using R_is_equivalence_functor by auto

    text{*
      To complete an interpretation of the @{locale "monoidal_category"} locale,
      we define @{term "\<iota> \<equiv> \<l>[\<I>]"}.
      We could also have chosen @{term "\<iota> \<equiv> \<rho>[\<I>]"} as the two are equal, though to prove
      that requires some work yet.
    *}

    definition \<iota>
    where "\<iota> \<equiv> \<l>[\<I>]"

    lemma \<iota>_in_hom:
    shows "\<iota> \<in> hom (\<I> \<otimes> \<I>) \<I>"
      using lunit_in_hom \<iota>_def by simp

    lemma induces_monoidal_category:
    shows "monoidal_category C T\<^sub>E\<^sub>M\<^sub>C \<alpha> \<iota>"
    proof -
      interpret L: equivalence_functor C C "\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (cod \<iota>, f)"
      proof -
        have "L\<^sub>E\<^sub>M\<^sub>C = (\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (cod \<iota>, f))" using \<iota>_in_hom L\<^sub>E\<^sub>M\<^sub>C_def by auto
        thus "equivalence_functor C C (\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (cod \<iota>, f))"
          using \<iota>_in_hom L.equivalence_functor_axioms T\<^sub>E\<^sub>M\<^sub>C_def L\<^sub>E\<^sub>M\<^sub>C_def by simp
      qed
      interpret R: equivalence_functor C C "\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (f, cod \<iota>)"
      proof -
        have "R\<^sub>E\<^sub>M\<^sub>C = (\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (f, cod \<iota>))" using \<iota>_in_hom R\<^sub>E\<^sub>M\<^sub>C_def by auto
        thus "equivalence_functor C C (\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (f, cod \<iota>))"
          using \<iota>_in_hom R.equivalence_functor_axioms T\<^sub>E\<^sub>M\<^sub>C_def R\<^sub>E\<^sub>M\<^sub>C_def by simp
      qed
      show ?thesis
      proof
        show "\<iota> \<in> hom (T\<^sub>E\<^sub>M\<^sub>C (cod \<iota>, cod \<iota>)) (cod \<iota>)" using \<iota>_in_hom by simp
        show "iso \<iota>" using iso_lunit \<iota>_def by simp
        show "\<And>a b c d. \<lbrakk> ide a; ide b; ide c; ide d \<rbrakk> \<Longrightarrow>
                        T\<^sub>E\<^sub>M\<^sub>C (a, \<alpha> (b, c, d)) \<cdot> \<alpha> (a, T\<^sub>E\<^sub>M\<^sub>C (b, c), d) \<cdot> T\<^sub>E\<^sub>M\<^sub>C (\<alpha> (a, b, c), d)
                          = \<alpha> (a, b, T\<^sub>E\<^sub>M\<^sub>C (c, d)) \<cdot> \<alpha> (T\<^sub>E\<^sub>M\<^sub>C (a, b), c, d)"
          using pentagon T_simp assoc_in_hom tensor_preserves_ide by simp
      qed
    qed

    interpretation MC: monoidal_category C T\<^sub>E\<^sub>M\<^sub>C \<alpha> \<iota>
      using induces_monoidal_category by auto

    text{*
      We now show that the notions defined in the interpretation @{text MC} agree with their
      counterparts in the present locale.  These facts are needed if we define an
      interpretation for the @{locale elementary_monoidal_category} locale, use it to
      obtain the induced interpretation for @{locale monoidal_category}, and then want to
      transfer facts obtained in the induced interpretation back to the original one.
    *}

    lemma \<I>_agreement:
    shows "\<I> = MC.unity"
      using \<iota>_in_hom by simp

    lemma L\<^sub>E\<^sub>M\<^sub>C_agreement:
    shows "L\<^sub>E\<^sub>M\<^sub>C = MC.L"
      using \<iota>_in_hom L\<^sub>E\<^sub>M\<^sub>C_def by auto

    lemma R\<^sub>E\<^sub>M\<^sub>C_agreement:
    shows "R\<^sub>E\<^sub>M\<^sub>C = MC.R"
      using \<iota>_in_hom R\<^sub>E\<^sub>M\<^sub>C_def by auto

    text{*
      We wish to show that the components of the unitors @{term MC.\<ll>} and @{term MC.\<rho>}
      defined in the induced interpretation @{text MC} agree with those given by the
      parameters @{term lunit} and @{term runit} to the present locale.  To avoid a lengthy
      development that repeats work already done in the @{locale monoidal_category} locale,
      we establish the agreement in a special case and then use the properties already
      shown for @{text MC} to prove the general case.  In particular, we first show that
      @{term "\<l>[\<I>] = MC.lunit MC.unity"} and @{term "\<r>[\<I>] = MC.runit MC.unity"},
      from which it follows by facts already proved for @{term MC} that both are equal to @{term \<iota>}.
      We then show that for an arbitrary identity @{term a} the arrows @{term "\<l>[a]"}
      and @{term "\<r>[a]"} satisfy the equations that uniquely characterize the components
      @{term "MC.lunit a"} and @{term "MC.runit a"}, respectively, and are therefore equal
      to those components.
    *}
      
    lemma unitor_coincidence\<^sub>E\<^sub>M\<^sub>C:
    shows "\<l>[\<I>] = \<iota>" and "\<r>[\<I>] = \<iota>"
    proof -
      have "\<r>[\<I>] = MC.runit MC.unity"
      proof (intro MC.runit_eqI)
        show "ide MC.unity" by simp
        show "\<r>[\<I>] \<in> hom (MC.tensor MC.unity MC.unity) MC.unity"
          using runit_in_hom [of \<I>] \<iota>_in_hom by simp
        show "MC.tensor \<r>[\<I>] MC.unity
                = MC.tensor MC.unity \<iota> \<cdot> MC.assoc MC.unity MC.unity MC.unity"
          using T\<^sub>E\<^sub>M\<^sub>C_def runit_in_hom \<iota>_in_hom triangle \<iota>_def \<alpha>_ide_simp by simp
      qed
      moreover have "\<l>[\<I>] = MC.lunit MC.unity"
      proof (intro MC.lunit_eqI)
        show "ide MC.unity" by simp
        show "\<l>[\<I>] \<in> hom (MC.tensor MC.unity MC.unity) MC.unity"
          using lunit_in_hom [of \<I>] \<iota>_in_hom by simp
        show "MC.tensor MC.unity \<l>[\<I>]
                = MC.tensor \<iota> MC.unity \<cdot> MC.assoc' MC.unity MC.unity MC.unity"
          using T\<^sub>E\<^sub>M\<^sub>C_def lunit_in_hom \<iota>_in_hom \<iota>_def MC.\<iota>_triangle by presburger
      qed
      moreover have "MC.lunit MC.unity = \<iota> \<and> MC.runit MC.unity = \<iota>"
        using MC.unitor_coincidence by simp
      ultimately have 1: "\<l>[\<I>] = \<iota> \<and> \<r>[\<I>] = \<iota>" by simp
      show "\<l>[\<I>] = \<iota>" using 1 by simp
      show "\<r>[\<I>] = \<iota>" using 1 by simp
    qed

    lemma lunit_char\<^sub>E\<^sub>M\<^sub>C:
    assumes "ide a"
    shows "\<I> \<otimes> \<l>[a] = (\<iota> \<otimes> a) \<cdot> MC.assoc' MC.unity MC.unity a"
    proof -
      have "(\<r>[\<I>] \<otimes> a) \<cdot> MC.assoc' MC.unity MC.unity a
                = ((\<I> \<otimes> \<l>[a]) \<cdot> \<a>[\<I>, \<I>, a]) \<cdot> MC.assoc' MC.unity MC.unity a"
        using assms triangle by simp
      also have "... = (\<I> \<otimes> \<l>[a]) \<cdot> (\<a>[\<I>, \<I>, a] \<cdot> MC.assoc' MC.unity MC.unity a)"
        using assms assoc_in_hom MC.assoc'_in_hom lunit_in_hom tensor_in_hom \<I>_agreement
        by auto
      also have "... = (\<I> \<otimes> \<l>[a]) \<cdot> (\<I> \<otimes> (\<I> \<otimes> a))"
        using assms MC.assoc_inv [of \<I> \<I> a] comp_arr_inv MC.assoc'_in_hom
              \<I>_agreement lunit_in_hom tensor_in_hom
        by simp
      also have "... = \<I> \<otimes> \<l>[a]"
      proof -
        have "\<I> \<otimes> \<l>[a] \<in> hom (\<I> \<otimes> (\<I> \<otimes> a)) (\<I> \<otimes> a)"
          using assms lunit_in_hom tensor_in_hom by simp
        thus ?thesis using comp_arr_dom by fastforce
      qed
      finally have "\<I> \<otimes> \<l>[a] = (\<r>[\<I>] \<otimes> a) \<cdot> MC.assoc' MC.unity MC.unity a" by presburger
      thus "\<I> \<otimes> \<l>[a] = (\<iota> \<otimes> a) \<cdot> MC.assoc' MC.unity MC.unity a"
        using unitor_coincidence\<^sub>E\<^sub>M\<^sub>C by auto
    qed
    
    lemma runit_char\<^sub>E\<^sub>M\<^sub>C:
    assumes "ide a"
    shows "\<r>[a] \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
      using assms triangle \<iota>_def by simp

    lemma \<ll>\<^sub>E\<^sub>M\<^sub>C_agreement:
    shows "\<ll>\<^sub>E\<^sub>M\<^sub>C = MC.\<ll>"
    proof
      have 1: "\<And>a. ide a \<Longrightarrow> \<l>[a] = MC.lunit a"
      proof -
        fix a
        assume a: "ide a"
        show "\<l>[a] = MC.lunit a"
        proof (intro MC.lunit_eqI)
          show "ide a" by fact
          show "\<l>[a] \<in> hom (MC.tensor MC.unity a) a"
            using a lunit_in_hom [of a] \<iota>_in_hom by simp
          show "MC.tensor MC.unity \<l>[a] = MC.tensor \<iota> a \<cdot> MC.assoc' MC.unity MC.unity a"
            using a \<I>_agreement T\<^sub>E\<^sub>M\<^sub>C_def lunit_in_hom \<ll>\<^sub>E\<^sub>M\<^sub>C_def [of a] lunit_in_hom
                  lunit_char\<^sub>E\<^sub>M\<^sub>C [of a] \<iota>_in_hom
            by auto
        qed
      qed
      fix f
      have "\<not> arr f \<Longrightarrow> \<ll>\<^sub>E\<^sub>M\<^sub>C f = MC.\<ll> f" by simp
      moreover have "arr f \<Longrightarrow> \<ll>\<^sub>E\<^sub>M\<^sub>C f = MC.\<ll> f"
        using 1 [of "dom f"] \<ll>\<^sub>E\<^sub>M\<^sub>C_def by force
      ultimately show "\<ll>\<^sub>E\<^sub>M\<^sub>C f = MC.\<ll> f" by blast
    qed

    lemma \<rho>\<^sub>E\<^sub>M\<^sub>C_agreement:
    shows "\<rho>\<^sub>E\<^sub>M\<^sub>C = MC.\<rho>"
    proof
      have 1: "\<And>a. ide a \<Longrightarrow> \<r>[a] = MC.runit a"
      proof -
        fix a
        assume a: "ide a"
        show "\<r>[a] = MC.runit a"
        proof (intro MC.runit_eqI)
          show "ide a" by fact
          show "\<r>[a] \<in> hom (MC.tensor a MC.unity) a"
            using a runit_in_hom [of a] \<iota>_in_hom by simp
          show "MC.tensor \<r>[a] MC.unity = MC.tensor a \<iota> \<cdot> MC.assoc a MC.unity MC.unity"
            using a \<I>_agreement T\<^sub>E\<^sub>M\<^sub>C_def runit_in_hom \<rho>\<^sub>E\<^sub>M\<^sub>C_def [of a] runit_char\<^sub>E\<^sub>M\<^sub>C [of a]
                  \<iota>_in_hom
            by simp
        qed
      qed
      fix f
      have "\<not> arr f \<Longrightarrow> \<rho>\<^sub>E\<^sub>M\<^sub>C f = MC.\<rho> f" by simp
      moreover have "arr f \<Longrightarrow> \<rho>\<^sub>E\<^sub>M\<^sub>C f = MC.\<rho> f"
        using 1 [of "dom f"] \<rho>\<^sub>E\<^sub>M\<^sub>C_def by auto
      ultimately show "\<rho>\<^sub>E\<^sub>M\<^sub>C f = MC.\<rho> f" by blast
    qed

    (* The next facts do not play nicely with simp if they have the opposite orientation. *)
    lemma assoc_agreement:
    assumes "ide a" and "ide b" and "ide c"
    shows "MC.assoc a b c = \<a>[a, b, c]"
      using assms \<alpha>_ide_simp by auto

    lemma lunit_agreement:
    assumes "ide a"
    shows "MC.lunit a = \<l>[a]"
    proof -
      have "MC.lunit a = MC.\<ll> a"
        using assms MC.lunit_in_hom by simp
      also have "... = \<ll>\<^sub>E\<^sub>M\<^sub>C a"
        using \<ll>\<^sub>E\<^sub>M\<^sub>C_agreement by simp
      also have "... = \<l>[a]"
        using assms \<ll>\<^sub>E\<^sub>M\<^sub>C_def lunit_in_hom by simp
      finally show ?thesis by simp
    qed

    lemma runit_agreement:
    assumes "ide a"
    shows "MC.runit a = \<r>[a]"
    proof -
      have "MC.runit a = MC.\<rho> a"
        using assms MC.runit_in_hom by simp
      also have "... = \<rho>\<^sub>E\<^sub>M\<^sub>C a"
        using \<rho>\<^sub>E\<^sub>M\<^sub>C_agreement by simp
      also have "... = \<r>[a]"
        using assms \<rho>\<^sub>E\<^sub>M\<^sub>C_def runit_in_hom by simp
      finally show ?thesis by simp
    qed

  end

  section "Strict Monoidal Category"

  text{*
    A monoidal category is \emph{strict} if the components of the associator and unitors
    are all identities.
  *}
      
  locale strict_monoidal_category =
    monoidal_category +
  assumes strict_assoc: "\<lbrakk> ide a0; ide a1; ide a2 \<rbrakk> \<Longrightarrow> ide \<a>[a0, a1, a2]"
  and strict_lunit: "ide a \<Longrightarrow> \<l>[a] = a"
  and strict_runit: "ide a \<Longrightarrow> \<r>[a] = a"
  begin

    lemma strict_unit:
    shows "\<iota> = \<I>"
      using strict_lunit unitor_coincidence(1) by auto

  end

  section "Opposite Monoidal Category"

  text{*
    The \emph{opposite} of a monoidal category has the same underlying category, but the
    arguments to the tensor product are reversed and the associator is inverted and its
    arguments reversed.
  *}
      
  locale opposite_monoidal_category =
    C: monoidal_category C T\<^sub>C \<alpha>\<^sub>C \<iota>
  for C :: "'a comp"                            (infixr "\<cdot>" 55)
  and T\<^sub>C :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha>\<^sub>C :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a
  begin

    abbreviation T
    where "T f \<equiv> T\<^sub>C (snd f, fst f)"

    abbreviation \<alpha>
    where "\<alpha> f \<equiv> C.\<alpha>' (snd (snd f), fst (snd f), fst f)"

  end

  sublocale opposite_monoidal_category \<subseteq> monoidal_category C T \<alpha> \<iota>
  proof -
    interpret T: binary_endofunctor C T
      apply unfold_locales using C.interchange by auto
    interpret ToTC: "functor" C.CCC.comp C T.ToTC
      using T.functor_ToTC by auto
    interpret ToCT: "functor" C.CCC.comp C T.ToCT
      using T.functor_ToCT by auto
    interpret \<alpha>: natural_transformation C.CCC.comp C T.ToTC T.ToCT \<alpha>
      apply unfold_locales
          apply auto[1]
         apply simp
        apply simp
    proof -
      fix f
      assume f: "C.CCC.arr f"
      show "T.ToCT f \<cdot> \<alpha> (C.CCC.dom f) = \<alpha> f"
        using f C.CCC.dom_char T.ToCT_def by (simp add: C.\<alpha>'_simp)
      show "\<alpha> (C.CCC.cod f) \<cdot> T.ToTC f = \<alpha> f"
        using f C.CCC.cod_char T.ToTC_def C.\<alpha>'_simp C.\<alpha>'.naturality by auto
    qed
    interpret \<alpha>: natural_isomorphism C.CCC.comp C T.ToTC T.ToCT \<alpha>
      apply unfold_locales using C.\<alpha>'.components_are_iso by simp
    interpret L: equivalence_functor C C "\<lambda>f. T (\<I>, f)"
      using C.R.equivalence_functor_axioms by simp
    interpret R: equivalence_functor C C "\<lambda>f. T (f, \<I>)"
      using C.L.equivalence_functor_axioms by simp
    show "monoidal_category C T \<alpha> \<iota>"
      apply unfold_locales
      using C.\<iota>_in_hom
        apply simp
      using C.\<iota>_is_iso
       apply simp
    proof -
      fix a b c d
      assume a: "C.ide a" and b: "C.ide b" and c: "C.ide c" and d: "C.ide d"
      show "T (a, \<alpha> (b, c, d)) \<cdot> \<alpha> (a, T (b, c), d) \<cdot> T (\<alpha> (a, b, c), d)
              = \<alpha> (a, b, T (c, d)) \<cdot> \<alpha> (T (a, b), c, d)"
        using a b c d C.\<alpha>'_ide_simp C.pentagon' [of d c b a] C.assoc'_in_hom C.tensor_in_hom
        by simp
    qed
  qed

  context opposite_monoidal_category
  begin

    lemma lunit_simp:
    assumes "C.ide a"
    shows "lunit a = C.runit a"
    proof (intro C.runit_eqI)
      show "C.ide a" by fact
      show "lunit a \<in> C.hom (C.tensor a C.unity) a"
        using assms lunit_char(1) by simp
      show "C.tensor (lunit a) C.unity = C.tensor a \<iota> \<cdot> C.assoc a C.unity C.unity"
        using assms lunit_char(2) C.iso_assoc by auto
    qed

    lemma runit_simp:
    assumes "C.ide a"
    shows "runit a = C.lunit a"
    proof (intro C.lunit_eqI)
      show "C.ide a" by fact
      show "runit a \<in> C.hom (C.tensor C.unity a) a"
        using assms runit_char(1) by simp
      show "C.tensor C.unity (runit a) = C.tensor \<iota> a \<cdot> C.assoc' C.unity C.unity a"
        using assms runit_char(2) C.iso_assoc by auto
    qed

  end

  section "Monoidal Language"

  text{*
    In this section we assume that a category @{term C} is given, and we define a
    formal syntax of terms constructed from arrows of @{term C} using function symbols
    that correspond to unity, composition, tensor, the associator and its formal inverse,
    and the left and right unitors and their formal inverses.
    We will use this syntax to state and prove the coherence theorem and then to construct
    the free monoidal category generated by @{term C}.
  *}

  locale monoidal_language =
    C: category C
    for C :: "'a comp"
  begin

    datatype (discs_sels) 't "term" =
      Prim 't                              ("\<^bold>\<langle>_\<^bold>\<rangle>")
    | Unity                                ("\<^bold>\<I>")
    | Tensor "'t term" "'t term"           (infixr "\<^bold>\<otimes>" 53)
    | Comp "'t term" "'t term"             (infixr "\<^bold>\<cdot>" 55)
    | Lunit "'t term"                      ("\<^bold>\<l>\<^bold>[_\<^bold>]")
    | Lunit' "'t term"                     ("\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[_\<^bold>]")
    | Runit "'t term"                      ("\<^bold>\<r>\<^bold>[_\<^bold>]")
    | Runit' "'t term"                     ("\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[_\<^bold>]")
    | Assoc "'t term" "'t term" "'t term"  ("\<^bold>\<a>\<^bold>[_, _, _\<^bold>]")
    | Assoc' "'t term" "'t term" "'t term" ("\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[_, _, _\<^bold>]")

    lemma not_is_Tensor_Unity:
    shows "\<not> is_Tensor Unity"
      by simp

    text{*
      We define formal domain and codomain functions on terms.
    *}

    primrec Dom :: "'a term \<Rightarrow> 'a term"
    where "Dom \<^bold>\<langle>f\<^bold>\<rangle> = \<^bold>\<langle>C.dom f\<^bold>\<rangle>"
        | "Dom \<^bold>\<I> = \<^bold>\<I>"
        | "Dom (t \<^bold>\<otimes> u) = (Dom t \<^bold>\<otimes> Dom u)"
        | "Dom (t \<^bold>\<cdot> u) = Dom u"
        | "Dom \<^bold>\<l>\<^bold>[t\<^bold>] = (\<^bold>\<I> \<^bold>\<otimes> Dom t)"
        | "Dom \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Dom t"
        | "Dom \<^bold>\<r>\<^bold>[t\<^bold>] = (Dom t \<^bold>\<otimes> \<^bold>\<I>)"
        | "Dom \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Dom t"
        | "Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = ((Dom t \<^bold>\<otimes> Dom u) \<^bold>\<otimes> Dom v)"
        | "Dom \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = (Dom t \<^bold>\<otimes> (Dom u \<^bold>\<otimes> Dom v))"

    primrec Cod :: "'a term \<Rightarrow> 'a term"
    where "Cod \<^bold>\<langle>f\<^bold>\<rangle> = \<^bold>\<langle>C.cod f\<^bold>\<rangle>"
        | "Cod \<^bold>\<I> = \<^bold>\<I>"
        | "Cod (t \<^bold>\<otimes> u) = (Cod t \<^bold>\<otimes> Cod u)"
        | "Cod (t \<^bold>\<cdot> u) = Cod t"
        | "Cod \<^bold>\<l>\<^bold>[t\<^bold>] = Cod t"
        | "Cod \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = (\<^bold>\<I> \<^bold>\<otimes> Cod t)"
        | "Cod \<^bold>\<r>\<^bold>[t\<^bold>] = Cod t"
        | "Cod \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = (Cod t \<^bold>\<otimes> \<^bold>\<I>)"
        | "Cod \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = (Cod t \<^bold>\<otimes> (Cod u \<^bold>\<otimes> Cod v))"
        | "Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = ((Cod t \<^bold>\<otimes> Cod u) \<^bold>\<otimes> Cod v)"

    text{*
      A term is a ``formal arrow'' if it is constructed from arrows of @{term C} in such a way
      that composition is applied only to formally composable pairs of terms.
    *}

    primrec Arr :: "'a term \<Rightarrow> bool"
    where "Arr \<^bold>\<langle>f\<^bold>\<rangle> = C.arr f"
        | "Arr \<^bold>\<I> = True"
        | "Arr (t \<^bold>\<otimes> u) = (Arr t \<and> Arr u)"
        | "Arr (t \<^bold>\<cdot> u) = (Arr t \<and> Arr u \<and> Dom t = Cod u)"
        | "Arr \<^bold>\<l>\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<r>\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = (Arr t \<and> Arr u \<and> Arr v)"
        | "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = (Arr t \<and> Arr u \<and> Arr v)"

    abbreviation Par :: "'a term \<Rightarrow> 'a term \<Rightarrow> bool"
    where "Par t u \<equiv> Arr t \<and> Arr u \<and> Dom t = Dom u \<and> Cod t = Cod u"

    abbreviation Seq :: "'a term \<Rightarrow> 'a term \<Rightarrow> bool"
    where "Seq t u \<equiv> Arr t \<and> Arr u \<and> Dom t = Cod u"

    abbreviation Hom :: "'a term \<Rightarrow> 'a term \<Rightarrow> 'a term set"
    where "Hom a b \<equiv> { t. Arr t \<and> Dom t = a \<and> Cod t = b }"

    text{*
      A term is a ``formal identity'' if it is constructed from identity arrows of @{term C}
      and @{term "\<^bold>\<I>"} using only the @{text "\<^bold>\<otimes>"} operator.
    *}

    primrec Ide :: "'a term \<Rightarrow> bool"
    where "Ide \<^bold>\<langle>f\<^bold>\<rangle> = C.ide f"
        | "Ide \<^bold>\<I> = True"
        | "Ide (t \<^bold>\<otimes> u) = (Ide t \<and> Ide u)"
        | "Ide (t \<^bold>\<cdot> u) = False"
        | "Ide \<^bold>\<l>\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<r>\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = False"
        | "Ide \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = False"

    lemma Ide_implies_Arr [simp]:
    shows "Ide t \<Longrightarrow> Arr t"
      by (induct t) auto

    lemma Arr_implies_Ide_Dom [elim]:
    shows "Arr t \<Longrightarrow> Ide (Dom t)"
      by (induct t) auto

    lemma Arr_implies_Ide_Cod [elim]:
    shows "Arr t \<Longrightarrow> Ide (Cod t)"
      by (induct t) auto

    lemma Ide_in_Hom [simp]:
    shows "Ide t \<Longrightarrow> t \<in> Hom t t"
      by (induct t) auto

    text{*
      A formal arrow is ``canonical'' if the only arrows of @{term C} used in its construction
      are identities.
    *}

    primrec Can :: "'a term \<Rightarrow> bool"
    where "Can \<^bold>\<langle>f\<^bold>\<rangle> = C.ide f"
        | "Can \<^bold>\<I> = True"
        | "Can (t \<^bold>\<otimes> u) = (Can t \<and> Can u)"
        | "Can (t \<^bold>\<cdot> u) = (Can t \<and> Can u \<and> Dom t = Cod u)"
        | "Can \<^bold>\<l>\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<r>\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = (Can t \<and> Can u \<and> Can v)"
        | "Can \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = (Can t \<and> Can u \<and> Can v)"

    lemma Ide_implies_Can:
    shows "Ide t \<Longrightarrow> Can t"
      by (induct t) auto

    lemma Can_implies_Arr:
    shows "Can t \<Longrightarrow> Arr t"
      by (induct t) auto

    text{*
      We next define the formal inverse of a term.
      This is only sensible for formal arrows built using only isomorphisms of @{term C};
      in particular, for canonical formal arrows.
    *}

    primrec Inv :: "'a term \<Rightarrow> 'a term"
    where "Inv \<^bold>\<langle>f\<^bold>\<rangle> = \<^bold>\<langle>C.inv f\<^bold>\<rangle>"
        | "Inv \<^bold>\<I> = \<^bold>\<I>"
        | "Inv (t \<^bold>\<otimes> u) = (Inv t \<^bold>\<otimes> Inv u)"
        | "Inv (t \<^bold>\<cdot> u) = (Inv u \<^bold>\<cdot> Inv t)"
        | "Inv \<^bold>\<l>\<^bold>[t\<^bold>] = \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = \<^bold>\<l>\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<r>\<^bold>[t\<^bold>] = \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = \<^bold>\<r>\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Inv t, Inv u, Inv v\<^bold>]"
        | "Inv \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = \<^bold>\<a>\<^bold>[Inv t, Inv u, Inv v\<^bold>]"

    lemma Inv_preserves_Ide:
    shows "Ide t \<Longrightarrow> Ide (Inv t)"
      by (induct t) auto

    lemma Inv_preserves_Can:
    assumes "Can t"
    shows "Can (Inv t)" and "Dom (Inv t) = Cod t" and "Cod (Inv t) = Dom t"
    proof -
      have 0: "Can t \<Longrightarrow> Can (Inv t) \<and> Dom (Inv t) = Cod t \<and> Cod (Inv t) = Dom t"
        by (induct t) auto
      show "Can (Inv t)" using assms 0 by blast
      show "Dom (Inv t) = Cod t" using assms 0 by blast
      show "Cod (Inv t) = Dom t" using assms 0 by blast
    qed

    lemma Inv_in_Hom [simp]:
    assumes "Can t"
    shows "Inv t \<in> Hom (Cod t) (Dom t)"
      using assms Inv_preserves_Can Can_implies_Arr by simp

    lemma Inv_Ide [simp]:
    assumes "Ide a"
    shows "Inv a = a"
      using assms by (induct a) auto

    lemma Inv_Inv [simp]:
    assumes "Can t"
    shows "Inv (Inv t) = t"
      using assms by (induct t) auto

    text{*
      We call a term ``diagonal'' if it is either @{term "\<^bold>\<I>"} or it is constructed from
      arrows of @{term C} using only the @{text "\<^bold>\<otimes>"} operator associated to the right.
      Essentially, such terms are lists of arrows of @{term C}, where @{term "\<^bold>\<I>"} represents
      the empty list and @{text "\<^bold>\<otimes>"} is used as the list constructor.
      We call them ``diagonal'' because terms can regarded as defining ``interconnection matrices''
      of arrows connecting ``inputs'' to ``outputs'', and from this point of view diagonal
      terms correspond to diagonal matrices.  The matrix point of view is suggestive for the
      extension of the results presented here to the symmetric monoidal and cartesian monoidal
      cases.
    *}

    fun Diag :: "'a term \<Rightarrow> bool"
    where "Diag \<^bold>\<I> = True"
        | "Diag \<^bold>\<langle>f\<^bold>\<rangle> = C.arr f"
        | "Diag (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u) = (C.arr f \<and> Diag u \<and> u \<noteq> \<^bold>\<I>)"
        | "Diag _ = False"

    lemma Diag_TensorE:
    assumes "Diag (Tensor t u)"
    shows "\<^bold>\<langle>un_Prim t\<^bold>\<rangle> = t" and "C.arr (un_Prim t)" and "Diag t" and "Diag u" and "u \<noteq> \<^bold>\<I>"
    proof -
      have 1: "t = \<^bold>\<langle>un_Prim t\<^bold>\<rangle> \<and> C.arr (un_Prim t) \<and> Diag t \<and> Diag u \<and> u \<noteq> \<^bold>\<I>"
        using assms by (cases t; simp; cases u; simp)
      show "\<^bold>\<langle>un_Prim t\<^bold>\<rangle> = t" using 1 by simp
      show "C.arr (un_Prim t)" using 1 by simp
      show "Diag t" using 1 by simp
      show "Diag u" using 1 by simp
      show "u \<noteq> \<^bold>\<I>" using 1 by simp
    qed

    lemma Diag_implies_Arr [elim]:
    shows "Diag t \<Longrightarrow> Arr t"
      by (induct t; simp add: Diag_TensorE)

    lemma Dom_preserves_Diag [elim]:
    shows "Diag t \<Longrightarrow> Diag (Dom t)"
    proof (induct t; simp add: Diag_TensorE)
      fix u v
      assume I1: "Diag (Dom u)"
      assume I2: "Diag (Dom v)"
      assume uv: "Diag (u \<^bold>\<otimes> v)"
      show "Diag (Dom u \<^bold>\<otimes> Dom v)"
      proof -
        have 1: "is_Prim (Dom u) \<and> C.arr (un_Prim (Dom u)) \<and>
                 Dom u = \<^bold>\<langle>C.dom (un_Prim u)\<^bold>\<rangle>"
          using uv by (cases u; simp; cases v, simp_all)
        have 2: "Diag v \<and> v \<noteq> \<^bold>\<I> \<and> \<not> is_Comp v \<and> \<not> is_Lunit' v \<and> \<not> is_Runit' v"
          using uv by (cases u; simp; cases v, simp_all)
        have "Diag (Dom v) \<and> Dom v \<noteq> \<^bold>\<I>"
          using 2 I2 by (cases v, simp_all)
        thus ?thesis using 1 by force
      qed
    qed
    
    lemma Cod_preserves_Diag [elim]:
    shows "Diag t \<Longrightarrow> Diag (Cod t)"
    proof (induct t, simp_all add: Diag_TensorE)
      fix u v
      assume I1: "Diag (Cod u)"
      assume I2: "Diag (Cod v)"
      assume uv: "Diag (u \<^bold>\<otimes> v)"
      show "Diag (Cod u \<^bold>\<otimes> Cod v)"
      proof -
        have 1: "is_Prim (Cod u) \<and> C.arr (un_Prim (Cod u)) \<and> Cod u = \<^bold>\<langle>C.cod (un_Prim u)\<^bold>\<rangle>"
          using uv by (cases u; simp; cases v; simp)
        have 2: "Diag v \<and> v \<noteq> \<^bold>\<I> \<and> \<not> is_Comp v \<and> \<not> is_Lunit' v \<and> \<not> is_Runit' v"
          using uv by (cases u; simp; cases v; simp)
        have "Diag (Cod v) \<and> Cod v \<noteq> \<^bold>\<I>"
          using I2 2 by (cases v, simp_all)
        thus ?thesis using 1 by force
      qed
    qed

    lemma Inv_preserves_Diag:
    assumes "Can t" and "Diag t"
    shows "Diag (Inv t)"
    proof -
      have "Can t \<and> Diag t \<Longrightarrow> Diag (Inv t)"
        apply (induct t, simp_all)
        by (metis (no_types, lifting) Can.simps(1) Inv.simps(1) Inv.simps(2) Diag.simps(3)
            Inv_Inv Diag_TensorE(1) C.inv_ide)
      thus ?thesis using assms by blast
    qed

    text{*
      The following function defines the ``dimension'' of a term,
      which is the number of arrows of @{term C} it contains.
      For diagonal terms, this is just the length of the term when regarded as a list
      of arrows of @{term C}.
      Alternatively, if a term is regarded as defining an interconnection matrix,
      then the dimension is the number of inputs (or outputs).
    *}

    primrec dim :: "'a term \<Rightarrow> nat"
    where "dim \<^bold>\<langle>f\<^bold>\<rangle> = 1"
        | "dim \<^bold>\<I> = 0"
        | "dim (t \<^bold>\<otimes> u) = (dim t + dim u)"
        | "dim (t \<^bold>\<cdot> u) = dim t"
        | "dim \<^bold>\<l>\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<r>\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = dim t + dim u + dim v"
        | "dim \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = dim t + dim u + dim v"

    text{*
      The following function defines a tensor product for diagonal terms.
      If terms are regarded as lists, this is just list concatenation.
      If terms are regarded as matrices, this corresponds to constructing a block
      diagonal matrix.
    *}

    fun TensorDiag  (infixr "\<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor>" 53)
    where "\<^bold>\<I> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = u"
        | "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<I> = t"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u"
        | "(t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
        | "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = undefined"

    lemma TensorDiag_Prim [simp]:
    assumes "t \<noteq> \<^bold>\<I>"
    shows "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> t = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> t"
      using assms by (cases t, simp_all)

    lemma TensorDiag_term_Unity [simp]:
    shows "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<I> = t"
      by (cases "t = \<^bold>\<I>"; cases t, simp_all)

    lemma TensorDiag_Diag:
    assumes "Diag (t \<^bold>\<otimes> u)"
    shows "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = t \<^bold>\<otimes> u"
      using assms TensorDiag_Prim by (metis Diag_TensorE(1) Diag_TensorE(5))

    lemma TensorDiag_preserves_Diag:
    assumes "Diag t" and "Diag u"
    shows "Diag (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
    and "Dom (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u"
    and "Cod (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
    proof -
      have 0: "\<And>u. \<lbrakk> Diag t; Diag u \<rbrakk> \<Longrightarrow>
                     Diag (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and> Dom (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
                                       Cod (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
      proof (induct t, simp_all add: Diag_TensorE(1-4))
        fix f :: 'a and u :: "'a term"
        assume f: "C.arr f"
        assume u: "Diag u"
        show "Diag (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and> Dom (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = \<^bold>\<langle>C.dom f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
                                 Cod (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = \<^bold>\<langle>C.cod f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
          using u f by (cases u, simp_all)
        next
        fix u v w
        assume I1: "\<And>u. Diag u \<Longrightarrow> Diag (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and> Dom (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
                                                     Cod (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
        assume I2: "\<And>u. Diag u \<Longrightarrow> Diag (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and> Dom (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
                                                     Cod (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
        assume vw: "Diag (v \<^bold>\<otimes> w)"
        assume u: "Diag u"
        show "Diag ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and>
              Dom ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = (Dom v \<^bold>\<otimes> Dom w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
              Cod ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = (Cod v \<^bold>\<otimes> Cod w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
        proof -
          have v: "v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> Diag v"
            using vw Diag_implies_Arr Diag_TensorE by force
          have w: "Diag w"
            using vw by (simp add: Diag_TensorE)
          have "u = \<^bold>\<I> \<Longrightarrow> ?thesis" by (simp add: vw)
          moreover have "u \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
            using u v w I1 I2 Dom_preserves_Diag [of u] Cod_preserves_Diag [of u]
            by (cases u, simp_all)
          ultimately show ?thesis by blast
        qed
      qed
      show "Diag (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) " using assms 0 by blast
      show "Dom (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u" using assms 0 by blast
      show "Cod (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u" using assms 0 by blast
    qed

    lemma TensorDiag_in_Hom:
    assumes "Diag t" and "Diag u"
    shows "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u \<in> Hom (Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u) (Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)"
      using assms TensorDiag_preserves_Diag Diag_implies_Arr by simp

    lemma Dom_TensorDiag:
    assumes "Diag t" and "Diag u"
    shows "Dom (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u"
      using assms TensorDiag_preserves_Diag(2) by simp

    lemma Cod_TensorDiag:
    assumes "Diag t" and "Diag u"
    shows "Cod (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
      using assms TensorDiag_preserves_Diag(3) by simp

    lemma not_is_Tensor_TensorDiagE:
    assumes "\<not> is_Tensor (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)" and "Diag t" and "Diag u"
    and "t \<noteq> \<^bold>\<I>" and "u \<noteq> \<^bold>\<I>"
    shows "False"
    proof -
      have "\<lbrakk> \<not> is_Tensor (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u); Diag t; Diag u; t \<noteq> \<^bold>\<I>; u \<noteq> \<^bold>\<I> \<rbrakk> \<Longrightarrow> False"
      proof (induct t, simp_all add: Diag_TensorE)
        fix v w
        assume I2: "\<not> is_Tensor (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<Longrightarrow> False"
        assume 1: "\<not> is_Tensor ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
        assume vw: "Diag (v \<^bold>\<otimes> w)"
        assume u: "Diag u"
        assume 2: "u \<noteq> \<^bold>\<I>"
        show "False"
        proof -
          have v: "v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle>"
            using vw Diag_TensorE by force
          have w: "Diag w \<and> w \<noteq> \<^bold>\<I>"
            using vw by (simp add: Diag_TensorE)
          have "(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = v \<^bold>\<otimes> (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
          proof -
            have "(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
              using u 2 by (cases u, simp_all)
            also have "... = v \<^bold>\<otimes> (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
              using u v w I2 TensorDiag_Prim not_is_Tensor_Unity by metis
            finally show ?thesis by simp
          qed
          thus ?thesis using 1 by simp
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma TensorDiag_assoc:
    assumes "Diag t" and "Diag u" and "Diag v"
    shows "(t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
    proof -
      have "\<And>n t u v. \<lbrakk> dim t = n; Diag t; Diag u; Diag v \<rbrakk> \<Longrightarrow>
                        (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
      proof -
        fix n
        show "\<And>t u v. \<lbrakk> dim t = n; Diag t; Diag u; Diag v \<rbrakk> \<Longrightarrow>
                        (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
        proof (induction n rule: nat_less_induct)
          fix n :: nat and t :: "'a term" and u v
          assume I: "\<forall>m<n. \<forall>t u v. dim t = m \<longrightarrow> Diag t \<longrightarrow> Diag u \<longrightarrow> Diag v \<longrightarrow>
                                   (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
          assume dim: "dim t = n"
          assume t: "Diag t"
          assume u: "Diag u"
          assume v: "Diag v"
          show "(t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
          proof -
            have "t = \<^bold>\<I> \<Longrightarrow> ?thesis" by simp
            moreover have "u = \<^bold>\<I> \<Longrightarrow> ?thesis" by simp
            moreover have "v = \<^bold>\<I> \<Longrightarrow> ?thesis" by simp
            moreover have "t \<noteq> \<^bold>\<I> \<and> u \<noteq> \<^bold>\<I> \<and> v \<noteq> \<^bold>\<I> \<and> is_Prim t \<Longrightarrow> ?thesis"
              using v by (cases t, simp_all, cases u, simp_all; cases v, simp_all)
            moreover have "t \<noteq> \<^bold>\<I> \<and> u \<noteq> \<^bold>\<I> \<and> v \<noteq> \<^bold>\<I> \<and> is_Tensor t \<Longrightarrow> ?thesis"
            proof (cases t; simp)
              fix w :: "'a term" and x :: "'a term"
              assume 1: "u \<noteq> \<^bold>\<I> \<and> v \<noteq> \<^bold>\<I>"
              assume 2: "t = (w \<^bold>\<otimes> x)"
              show "((w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = (w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
              proof -
                have w: "w = \<^bold>\<langle>un_Prim w\<^bold>\<rangle>"
                  using t 1 2 Diag_TensorE by auto
                have x: "Diag x"
                  using t w 1 2 by (metis Diag.simps(3))
                have "((w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (x \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v"
                  using u v w x 1 2 by (cases u, simp_all)
                also have "... = (w \<^bold>\<otimes> (x \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v"
                  using t w u 1 2 TensorDiag_Prim not_is_Tensor_TensorDiagE Diag_TensorE
                        not_is_Tensor_Unity
                  by metis
                also have "... = w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> ((x \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
                  using u v w x 1 by (cases u, simp_all; cases v, simp_all)
                also have "... = w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (x \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v))"
                proof -
                  have "dim x < dim t"
                    using w 2
                    by (metis (no_types, lifting) Groups.add_ac(2) One_nat_def add_Suc_right le_add2
                        le_imp_less_Suc dim.simps(1) dim.simps(3))
                  thus ?thesis 
                    using u v x dim I by simp
                qed
                also have "... = (w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
                proof -
                  have 3: "is_Tensor (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
                    using u v 1 not_is_Tensor_TensorDiagE by auto
                  obtain u' :: "'a term" and v' where uv': "u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = u' \<^bold>\<otimes> v'"
                    using 3 is_Tensor_def by blast
                  thus ?thesis by simp
                qed
                finally show ?thesis by simp
              qed
            qed
            moreover have "t = \<^bold>\<I> \<or> is_Prim t \<or> is_Tensor t"
              using t by (cases t, simp_all)
            ultimately show ?thesis by blast
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma TensorDiag_preserves_Ide:
    assumes "Ide t" and "Ide u" and "Diag t" and "Diag u"
    shows "Ide (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
      using assms
      by (metis (mono_tags, lifting) Arr_implies_Ide_Dom Ide_in_Hom Diag_implies_Arr
          TensorDiag_preserves_Diag(1) TensorDiag_preserves_Diag(2) mem_Collect_eq)

    lemma TensorDiag_preserves_Can:
    assumes "Can t" and "Can u" and "Diag t" and "Diag u"
    shows "Can (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Diag t; Can u \<and> Diag u \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
      proof (induct t; simp)
        show "\<And>x u. C.ide x \<and> C.arr x \<Longrightarrow> Can u \<and> Diag u \<Longrightarrow> Can (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
          by (metis Ide.simps(1) Ide.simps(2) Ide_implies_Can Diag.simps(2) TensorDiag_Prim
                    TensorDiag_preserves_Ide Can.simps(3))
        fix t u v
        assume tu: "Can t \<and> Can u \<and> Diag (t \<^bold>\<otimes> u)"
        assume v: "Can v \<and> Diag v"
        assume I1: "\<And>v. \<lbrakk> Diag t; Can v \<and> Diag v \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
        assume I2: "\<And>v. \<lbrakk> Diag u; Can v \<and> Diag v \<rbrakk> \<Longrightarrow> Can (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
        have t: "Can t \<and> Diag t"
          using tu Diag_TensorE(3) by fastforce
        have u: "Can u \<and> Diag u"
          using t tu
          by (metis Diag.elims(2) Diag.simps(3) Diag.simps(4) Diag.simps(5))
        show "Can ((t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
        proof -
          have "v = Unity \<Longrightarrow> ?thesis" using tu v by simp
          moreover have "v \<noteq> Unity \<Longrightarrow> ?thesis"
          proof -
            assume 1: "v \<noteq> Unity"
            have "(t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
              using 1 by (cases v, simp_all)
            moreover have "Can (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v))"
              using t u tu v I1 I2
              by (simp add: TensorDiag_preserves_Diag(1))
            ultimately show ?thesis by simp
          qed
          ultimately show ?thesis by blast
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma Inv_TensorDiag:
    assumes "Can t" and "Can u" and "Diag t" and "Diag u"
    shows "Inv (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv u"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Diag t; Can u \<and> Diag u \<rbrakk> \<Longrightarrow> Inv (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv u"
      proof (induct t, simp_all)
        fix f u
        assume f: "C.ide f \<and> C.arr f"
        assume u: "Can u \<and> Diag u"
        show "Inv (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv u"
          using f u by (cases u, simp_all)
        next
        fix t u v
        assume I1: "\<And>v. \<lbrakk> Diag t; Can v \<and> Diag v \<rbrakk> \<Longrightarrow> Inv (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v) = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v"
        assume I2: "\<And>v. \<lbrakk> Diag u; Can v \<and> Diag v \<rbrakk> \<Longrightarrow> Inv (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v) = Inv u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v"
        assume tu: "Can t \<and> Can u \<and> Diag (t \<^bold>\<otimes> u)"
        have t: "Can t \<and> Diag t"
          using tu Diag_TensorE by force
        have u: "Can u \<and> Diag u"
          using t tu by (metis Diag.elims(2) Diag.simps(3) Diag.simps(4) Diag.simps(5))
        assume v: "Can v \<and> Diag v"
        show "Inv ((t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v) = (Inv t \<^bold>\<otimes> Inv u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v"
        proof -
          have "v = Unity \<Longrightarrow> ?thesis" by simp
          moreover have "v \<noteq> Unity \<Longrightarrow> ?thesis"
          proof -
            assume 1: "v \<noteq> Unity"
            have "Inv ((t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v) = Inv (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v))"
              using 1 by (cases v, simp_all)
            also have "... = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
              using t u v I1 TensorDiag_preserves_Diag TensorDiag_preserves_Can
                    Inv_preserves_Diag Inv_preserves_Can
              by simp
            also have "... = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (Inv u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v)"
              using t u v I2 TensorDiag_preserves_Diag TensorDiag_preserves_Can
                    Inv_preserves_Diag Inv_preserves_Can
              by simp
            also have "... = (Inv t \<^bold>\<otimes> Inv u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v"
              using v 1 by (cases v, simp_all)
            finally show ?thesis by blast
          qed
          ultimately show ?thesis by blast
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text{*
      The following function defines composition for compatible diagonal terms,
      by ``pushing the composition down'' to arrows of @{text C}.
    *}

    fun CompDiag :: "'a term \<Rightarrow> 'a term \<Rightarrow> 'a term"  (infixr "\<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor>" 55)
    where "\<^bold>\<I> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u = u"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<langle>g\<^bold>\<rangle> = \<^bold>\<langle>C f g\<^bold>\<rangle>"
        | "(u \<^bold>\<otimes> v) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (w \<^bold>\<otimes> x) = (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w \<^bold>\<otimes> v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x)"
        | "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<I> = t"
        | "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> _ = undefined \<^bold>\<cdot> undefined"

    text{*
      Note that the last clause above is not relevant to diagonal terms.
      We have chosen a provably non-diagonal value in order to validate associativity.
    *}

    lemma CompDiag_preserves_Diag:
    assumes "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Diag (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
    and "Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u"
    and "Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t"
    proof -
      have 0: "\<And>u. \<lbrakk> Diag t; Diag u; Dom t = Cod u \<rbrakk> \<Longrightarrow>
                     Diag (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and> Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t"
      proof (induct t, simp_all add: Diag_TensorE)
        fix f u
        assume f: "C.arr f"
        assume u: "Diag u"
        assume 1: "\<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod u"
        show "Diag (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and> Cod (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = \<^bold>\<langle>C.cod f\<^bold>\<rangle>"
          using f u 1 by (cases u, simp_all)
        next
        fix u v w
        assume I2: "\<And>u. \<lbrakk> Diag u; Dom w = Cod u \<rbrakk> \<Longrightarrow>
                          Diag (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and> Cod (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod w"
        assume vw: "Diag (v \<^bold>\<otimes> w)"
        have v: "Diag v"
          using vw Diag_TensorE by force
        have w: "Diag w"
          using vw Diag_TensorE by force
        assume u: "Diag u"
        assume 1: "(Dom v \<^bold>\<otimes> Dom w) = Cod u"
        show "Diag ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and>
                                     Cod ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod v \<^bold>\<otimes> Cod w"
          using u v w 1
        proof (cases u, simp_all)
          fix x y
          assume 2: "u = Tensor x y"
          have 4: "is_Prim x \<and> x = \<^bold>\<langle>un_Prim x\<^bold>\<rangle> \<and> C.arr (un_Prim x) \<and> Diag y \<and> y \<noteq> \<^bold>\<I>"
            using u 2 by (cases x, cases y, simp_all)
          have 5: "is_Prim v \<and> v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> C.arr (un_Prim v) \<and> Diag w \<and> w \<noteq> \<^bold>\<I>"
            using v w vw
            by (metis Diag_TensorE(1) Diag_TensorE(2) Diag_TensorE(5) term.disc(1))
          have 6: "C.dom (un_Prim v) = C.cod (un_Prim x) \<and> Dom w = Cod y"
            using 1 2 4 5 apply (cases u, simp_all)
            by (metis Cod.simps(1) Dom.simps(1) term.simps(1))
          have "(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u = \<^bold>\<langle>C (un_Prim v) (un_Prim x)\<^bold>\<rangle> \<^bold>\<otimes> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y"
            using 2 4 5 6 CompDiag.simps(2) [of "un_Prim v" "un_Prim x"] by simp
          moreover have "Diag (\<^bold>\<langle>C (un_Prim v) (un_Prim x)\<^bold>\<rangle> \<^bold>\<otimes> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"
          proof -
            have "Diag (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"
              using I2 4 5 6 by simp
            thus ?thesis
              using 4 5 6 Diag.simps(3) [of "C (un_Prim v) (un_Prim x)" "(w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"]
              by (cases w; cases y) auto
          qed
          ultimately show "Diag (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x \<^bold>\<otimes> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y) \<and>
                           Dom (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Dom x \<and> Dom (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y) = Dom y \<and>
                           Cod (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Cod v \<and> Cod (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y) = Cod w"
            using 4 5 6 I2
            by (metis Cod.simps(1) CompDiag.simps(2) Dom.simps(1) C.cod_comp C.dom_comp)
        qed
      qed
      show "Diag (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)" using assms 0 by blast
      show "Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u" using assms 0 by blast
      show "Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t" using assms 0 by blast
    qed

    lemma CompDiag_in_Hom:
    assumes "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<in> Hom (Dom u) (Cod t)"
      using assms CompDiag_preserves_Diag Diag_implies_Arr by simp

    lemma Dom_CompDiag:
    assumes "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u"
      using assms CompDiag_preserves_Diag(2) by simp

    lemma Cod_CompDiag:
    assumes "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t"
      using assms CompDiag_preserves_Diag(3) by simp

    lemma CompDiag_Cod_Diag [simp]:
    assumes "Diag t"
    shows "CompDiag (Cod t) t = t"
    proof -
      have "Diag t \<Longrightarrow> Cod t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = t"
        by (induct t) (auto simp add: Diag_TensorE)
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_Diag_Dom [simp]:
    assumes "Diag t"
    shows "CompDiag t (Dom t) = t"
    proof -
      have "Diag t \<Longrightarrow> t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Dom t = t"
        by (induct t) (auto simp add: Diag_TensorE)
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_Ide_Diag [simp]:
    assumes "Diag t" and "Ide a" and "Dom a = Cod t"
    shows "a \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = t"
      using assms Ide_in_Hom by simp

    lemma CompDiag_Diag_Ide [simp]:
    assumes "Diag t" and "Ide a" and "Dom t = Cod a"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> a = t"
      using assms Ide_in_Hom by auto

    lemma CompDiag_assoc:
    assumes "Diag t" and "Diag u" and "Diag v"
    and "Dom t = Cod u" and "Dom u = Cod v"
    shows "(t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
    proof -
      have "\<And>u v. \<lbrakk> Diag t; Diag u; Diag v; Dom t = Cod u; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                    (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
      proof (induct t, simp_all)
        fix f u v
        assume f: "C.arr f"
        assume u: "Diag u"
        assume v: "Diag v"
        assume 1: "\<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod u"
        assume 2: "Dom u = Cod v"
        show "(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
          using u v f 1 2 by (cases u, simp_all; cases v, simp_all)
        next
        fix u v w x
        assume I1: "\<And>u v. \<lbrakk> Diag w; Diag u; Diag v; Dom w = Cod u; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                            (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume I2: "\<And>u v. \<lbrakk> Diag x; Diag u; Diag v; Dom x = Cod u; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                            (x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume wx: "Diag (w \<^bold>\<otimes> x)"
        assume u: "Diag u"
        assume v: "Diag v"
        assume 1: "(Dom w \<^bold>\<otimes> Dom x) = Cod u"
        assume 2: "Dom u = Cod v"
        show "((w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = (w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v"
        proof -
          have w: "Diag w"
            using wx Diag_TensorE by blast
          have x: "Diag x"
            using wx Diag_TensorE by blast
          have "is_Tensor u"
            using u 1 by (cases u) simp_all
          thus ?thesis
            using u v apply (cases u, simp_all, cases v, simp_all)
          proof -
            fix u1 u2 v1 v2
            assume 3: "u = (u1 \<^bold>\<otimes> u2)"
            assume 4: "v = (v1 \<^bold>\<otimes> v2)"
            show "(w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u1) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1 = w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1 \<and>
                  (x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u2) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2 = x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2"
            proof -
              have "Diag u1 \<and> Diag u2"
                using u 3 Diag_TensorE by blast
              moreover have "Diag v1 \<and> Diag v2"
                using v 4 Diag_TensorE by blast
              ultimately show ?thesis using w x I1 I2 1 2 3 4 by simp
            qed
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_preserves_Ide:
    assumes "Ide t" and "Ide u" and "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Ide (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
    proof -
      have "\<And>u. \<lbrakk> Ide t; Ide u; Diag t; Diag u; Dom t = Cod u \<rbrakk> \<Longrightarrow> Ide (CompDiag t u)"
        by (induct t; simp)
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_preserves_Can:
    assumes "Can t" and "Can u" and "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Diag t; Can u \<and> Diag u; Dom t = Cod u \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
      proof (induct t, simp_all)
        fix t u v
        assume I1: "\<And>v. \<lbrakk> Diag t; Can v \<and> Diag v; Dom t = Cod v \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume I2: "\<And>v. \<lbrakk> Diag u; Can v \<and> Diag v; Dom u = Cod v \<rbrakk> \<Longrightarrow> Can (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume tu: "Can t \<and> Can u \<and> Diag (t \<^bold>\<otimes> u)"
        have t: "Can t \<and> Diag t"
          using tu Diag_TensorE by blast
        have u: "Can u \<and> Diag u"
          using tu Diag_TensorE by blast
        assume v: "Can v \<and> Diag v"
        assume 1: "(Dom t \<^bold>\<otimes> Dom u) = Cod v"
        show "Can ((t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        proof -
          have 2: "(Dom t \<^bold>\<otimes> Dom u) = Cod v" using 1 by simp
          show ?thesis
            using v 2
          proof (cases v; simp)
            fix w x
            assume wx: "v = (w \<^bold>\<otimes> x)"
            have "Can w \<and> Diag w" using v wx Diag_TensorE by auto
            moreover have "Can x \<and> Diag x" using v wx Diag_TensorE by auto
            moreover have "Dom t = Cod w" using 2 wx by simp
            moreover have ux: "Dom u = Cod x" using 2 wx by simp
            ultimately show "Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w) \<and> Can (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x)"
              using t u I1 I2 by simp
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma Inv_CompDiag:
    assumes "Can t" and "Can u" and "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Diag t; Can u \<and> Diag u; Dom t = Cod u \<rbrakk> \<Longrightarrow>
              Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t"
      proof (induct t, simp_all)
        show "\<And>x u. \<lbrakk> C.ide x \<and> C.arr x; Can u \<and> Diag u; \<^bold>\<langle>x\<^bold>\<rangle> = Cod u \<rbrakk> \<Longrightarrow>
                      Inv u = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv (Cod u)"
          by (metis Cod.simps(1) CompDiag_Diag_Ide Ide.simps(1) Inv.simps(1)
                    Inv_preserves_Can(2) Inv_preserves_Diag C.ide_def C.inv_ide)
        show "\<And>u. Can u \<and> Diag u \<Longrightarrow> \<^bold>\<I> = Cod u \<Longrightarrow> Inv u = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<I>"
          by (simp add: Inv_preserves_Can(2) Inv_preserves_Diag)
        fix t u v
        assume tu: "Can t \<and> Can u \<and> Diag (t \<^bold>\<otimes> u)"
        have t: "Can t \<and> Diag t"
          using tu Diag_TensorE by blast
        have u: "Can u \<and> Diag u"
          using tu Diag_TensorE by blast
        assume I1: "\<And>v. \<lbrakk> Diag t; Can v \<and> Diag v; Dom t = Cod v \<rbrakk> \<Longrightarrow>
                          Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) = Inv v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t"
        assume I2: "\<And>v. \<lbrakk> Diag u; Can v \<and> Diag v; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                          Inv (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) = Inv v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv u"
        assume v: "Can v \<and> Diag v"
        assume 1: "(Dom t \<^bold>\<otimes> Dom u) = Cod v"
        show "Inv ((t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) = Inv v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (Inv t \<^bold>\<otimes> Inv u)"
          using v 1
        proof (cases v, simp_all)
          fix w x
          assume wx: "v = (w \<^bold>\<otimes> x)"
          have "Can w \<and> Diag w" using v wx Diag_TensorE by auto
          moreover have "Can x \<and> Diag x" using v wx Diag_TensorE by auto
          moreover have "Dom t = Cod w" using wx 1 by simp
          moreover have "Dom u = Cod x" using wx 1 by simp
          ultimately show "Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w) = Inv w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t \<and>
                           Inv (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Inv x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv u"
            using t u I1 I2 by simp
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma Can_and_Diag_implies_Ide:
    assumes "Can t" and "Diag t"
    shows "Ide t"
    proof -
      have "\<lbrakk> Can t; Diag t \<rbrakk> \<Longrightarrow> Ide t"
        by (induct t, simp_all add: Diag_TensorE)
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_Can_Inv [simp]:
    assumes "Can t" and "Diag t"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t = Cod t"
      using assms Can_and_Diag_implies_Ide Ide_in_Hom by simp
      
    lemma CompDiag_Inv_Can [simp]:
    assumes "Can t" and "Diag t"
    shows "Inv t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = Dom t"
      using assms Can_and_Diag_implies_Ide Ide_in_Hom by simp

    text{*
      The next fact is a syntactic version of the interchange law, for diagonal terms.
    *}

    lemma CompDiag_TensorDiag:
    assumes "Diag t" and "Diag u" and "Diag v" and "Diag w"
    and "Seq t v" and "Seq u w"
    shows "(t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
    proof -
      have "\<And>u v w. \<lbrakk> Diag t; Diag u; Diag v; Diag w; Seq t v; Seq u w \<rbrakk> \<Longrightarrow>
                      (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
      proof (induct t, simp_all)
        fix u v w
        assume u: "Diag u"
        assume v: "Diag v"
        assume w: "Diag w"
        assume uw: "Seq u w"
        show "Arr v \<and> \<^bold>\<I> = Cod v \<Longrightarrow> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
          using u v w uw by (cases v) simp_all
        show "\<And>f. \<lbrakk> C.arr f; Arr v \<and> \<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod v \<rbrakk> \<Longrightarrow>
                    (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
        proof -
          fix f
          assume f: "C.arr f"
          assume 1: "Arr v \<and> \<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod v"
          show "(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
          proof -
            have 2: "v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> C.arr (un_Prim v)" using v 1 by (cases v) simp_all
            have "u = \<^bold>\<I> \<Longrightarrow> ?thesis"
              using v w uw 1 2 Cod.simps(3) CompDiag_Cod_Diag Dom.simps(2)
                    TensorDiag_Prim TensorDiag_term_Unity TensorDiag_preserves_Diag(3)
              by (cases w) simp_all
            moreover have "u \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
            proof -
              assume 3: "u \<noteq> \<^bold>\<I>"
              hence 4: "w \<noteq> \<^bold>\<I>" using u w uw by (cases u, simp_all; cases w, simp_all)
              have "(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<otimes> w)"
              proof -
                have "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u"
                  using u f 3 TensorDiag_Diag by (cases u) simp_all
                moreover have "v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w = v \<^bold>\<otimes> w"
                  using w 2 4 TensorDiag_Diag by (cases v, simp_all; cases w, simp_all)
                ultimately show ?thesis by simp
              qed
              also have 5: "... = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<otimes> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)" by simp
              also have "... = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                using f u w uw 1 2 3 4 5
                      TensorDiag_Diag TensorDiag_Prim TensorDiag_preserves_Diag(1)
                      CompDiag_preserves_Diag(1)
                by (metis (full_types) Cod.simps(3) Dom.simps(1) Dom.simps(3) Diag.simps(2))
              finally show ?thesis by blast
            qed
            ultimately show ?thesis by blast
          qed
        qed
        fix t1 t2
        assume I2: "\<And>u v w. \<lbrakk> Diag t2; Diag u; Diag v; Diag w;
                              Arr v \<and> Dom t2 = Cod v; Seq u w \<rbrakk> \<Longrightarrow>
                              (t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
        assume t12: "Diag (t1 \<^bold>\<otimes> t2)"
        have t1: "t1 = \<^bold>\<langle>un_Prim t1\<^bold>\<rangle> \<and> C.arr (un_Prim t1) \<and> Diag t1"
          using t12 by (cases t1) simp_all
        have t2: "Diag t2 \<and> t2 \<noteq> \<^bold>\<I>"
          using t12 by (cases t1) simp_all
        assume 1: "Arr t1 \<and> Arr t2 \<and> Arr v \<and> (Dom t1 \<^bold>\<otimes> Dom t2) = Cod v"
        show "((t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = ((t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
        proof -
          have "u = \<^bold>\<I> \<Longrightarrow> ?thesis"
            using w uw TensorDiag_term_Unity CompDiag_Cod_Diag by (cases w) simp_all
          moreover have "u \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
          proof -
            assume u': "u \<noteq> \<^bold>\<I>"
            hence w': "w \<noteq> \<^bold>\<I>" using u w uw by (cases u; simp; cases w; simp)
            show ?thesis
              using 1 v
            proof (cases v, simp_all)
              fix v1 v2
              assume v12: "v = Tensor v1 v2"
              have v1: "v1 = \<^bold>\<langle>un_Prim v1\<^bold>\<rangle> \<and> C.arr (un_Prim v1) \<and> Diag v1"
                using v v12 by (cases v1) simp_all
              have v2: "Diag v2 \<and> v2 \<noteq> \<^bold>\<I>"
                using v v12 by (cases v1) simp_all
              have 2: "v = (\<^bold>\<langle>un_Prim v1\<^bold>\<rangle> \<^bold>\<otimes> v2)"
                using v1 v12 by simp
              show "((t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((v1 \<^bold>\<otimes> v2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w)
                      = ((t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<otimes> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
              proof -
                have 3: "(t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = t1 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
                  using u u' by (cases u) simp_all
                have 4: "TensorDiag v w = TensorDiag v1 (TensorDiag v2 w)"
                  using v w v1 v2 2 TensorDiag_assoc TensorDiag_Diag by metis
                have "((t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((v1 \<^bold>\<otimes> v2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w)
                        = (t1 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v1 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (v2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w))"
                  using 3 4 v12 by simp
                also have "... = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> ((t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w))"
                proof -
                  have "is_Tensor (t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
                    using t2 u u' not_is_Tensor_TensorDiagE by auto
                  moreover have "is_Tensor (v2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w)"
                    using v2 v12 w w' not_is_Tensor_TensorDiagE by auto
                  ultimately show ?thesis
                    using u u' v w t1 v1 t12 v12 TensorDiag_Prim not_is_Tensor_Unity
                    by (metis (no_types, lifting) CompDiag.simps(2) CompDiag.simps(3)
                        is_Tensor_def)
                qed
                also have "... = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                  using u w uw t2 v2 1 2 Diag_implies_Arr I2 by fastforce
                also have "... = ((t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<otimes> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                proof -
                  have "CompDiag u w \<noteq> Unity"
                  proof -
                    have "Arr v1 \<and> \<^bold>\<langle>C.dom (un_Prim t1)\<^bold>\<rangle> = Cod v1"
                      using t1 v1 1 2
                      by (metis Arr.simps(1) Cod.simps(3) Dom.simps(1) term.sel(2))
                    thus ?thesis
                      using t1 t2 v1 v2 u w uw u' CompDiag_preserves_Diag
                            TensorDiag_preserves_Diag TensorDiag_Prim
                      by (metis (mono_tags, lifting) Cod.simps(2) Cod.simps(3)
                          TensorDiag.simps(2) term.distinct(3))
                  qed
                  hence "((t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<otimes> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)
                           = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> ((t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w))"
                    by (cases "CompDiag u w") simp_all
                  thus ?thesis by presburger
                qed
                finally show ?thesis by blast
              qed
            qed
          qed
          ultimately show ?thesis by blast
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text{*
      The following function reduces an arrow to diagonal form.
      The precise relationship between a term and its diagonalization is developed below.
    *}

    fun Diagonalize :: "'a term \<Rightarrow> 'a term"   ("\<^bold>\<lfloor>_\<^bold>\<rfloor>")
    where "\<^bold>\<lfloor>\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>\<rfloor> = \<^bold>\<langle>f\<^bold>\<rangle>"
        | "\<^bold>\<lfloor>\<^bold>\<I>\<^bold>\<rfloor> = \<^bold>\<I>"
        | "\<^bold>\<lfloor>t \<^bold>\<otimes> u\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>t \<^bold>\<cdot> u\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<l>\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<r>\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>)"

    lemma Diag_Diagonalize:
    assumes "Arr t"
    shows "Diag \<^bold>\<lfloor>t\<^bold>\<rfloor>" and "Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>" and "Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
    proof -
      have 0: "Arr t \<Longrightarrow> Diag \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
        using TensorDiag_preserves_Diag CompDiag_preserves_Diag TensorDiag_assoc
        apply (induct t)
                 apply auto
         apply (metis (full_types))
        by (metis (full_types))
      show "Diag \<^bold>\<lfloor>t\<^bold>\<rfloor>" using assms 0 by blast
      show "Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>" using assms 0 by blast
      show "Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>" using assms 0 by blast
    qed

    lemma Diagonalize_in_Hom:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>t\<^bold>\<rfloor> \<in> Hom \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
      using assms Diag_Diagonalize Diag_implies_Arr by blast

    lemma Diagonalize_Dom:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = Dom \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Diagonalize_in_Hom by simp

    lemma Diagonalize_Cod:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> = Cod \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Diagonalize_in_Hom by simp

    lemma Diagonalize_preserves_Ide:
    assumes "Ide a"
    shows "Ide \<^bold>\<lfloor>a\<^bold>\<rfloor>"
    proof -
      have "Ide a \<Longrightarrow> Ide \<^bold>\<lfloor>a\<^bold>\<rfloor>"
        using Ide_implies_Arr TensorDiag_preserves_Ide Diag_Diagonalize
        by (induct a) simp_all
      thus ?thesis using assms by blast
    qed

    text{*
      The diagonalizations of canonical arrows are identities.
    *}

    lemma Ide_Diagonalize_Can:
    assumes "Can t"
    shows "Ide \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Can t \<Longrightarrow> Ide \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        using Can_implies_Arr TensorDiag_preserves_Ide Diag_Diagonalize CompDiag_preserves_Ide
              TensorDiag_preserves_Diag
        by (induct t) auto
      thus ?thesis using assms by blast
    qed

    lemma Diagonalize_preserves_Can:
    assumes "Can t"
    shows "Can \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Ide_Diagonalize_Can Ide_implies_Can by auto

    lemma Diagonalize_Diag [simp]:
    assumes "Diag t"
    shows "\<^bold>\<lfloor>t\<^bold>\<rfloor> = t"
    proof -
      have "Diag t \<Longrightarrow> \<^bold>\<lfloor>t\<^bold>\<rfloor> = t"
        apply (induct t, simp_all)
        using TensorDiag_Prim Diag_TensorE by metis
      thus ?thesis using assms by blast
    qed

    lemma Diagonalize_Diagonalize [simp]:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Diag_Diagonalize Diagonalize_Diag by blast

    lemma Diagonalize_Tensor:
    assumes "Arr t" and "Arr u"
    shows "\<^bold>\<lfloor>t \<^bold>\<otimes> u\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<^bold>\<rfloor>"
      using assms Diagonalize_Diagonalize by simp

    lemma Diagonalize_Tensor_Unity_Arr [simp]:
    assumes "Arr u"
    shows "\<^bold>\<lfloor>\<^bold>\<I> \<^bold>\<otimes> u\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
      using assms by simp

    lemma Diagonalize_Tensor_Arr_Unity [simp]:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>t \<^bold>\<otimes> \<^bold>\<I>\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms by simp

    lemma Diagonalize_Tensor_Prim_Arr [simp]:
    assumes "arr f" and "Arr u" and "Diagonalize u \<noteq> Unity"
    shows "\<^bold>\<lfloor>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u\<^bold>\<rfloor> = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
      using assms by simp

    lemma Diagonalize_Tensor_Tensor:
    assumes "Arr t" and "Arr u" and "Arr v"
    shows "\<^bold>\<lfloor>(t \<^bold>\<otimes> u) \<^bold>\<otimes> v\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<otimes> (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>v\<^bold>\<rfloor>)\<^bold>\<rfloor>"
      using assms Diag_Diagonalize Diagonalize_Diagonalize by (simp add: TensorDiag_assoc)

    lemma Diagonalize_Comp_Cod_Arr:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Cod t \<^bold>\<cdot> t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Arr t \<Longrightarrow> \<^bold>\<lfloor>Cod t \<^bold>\<cdot> t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        apply (induct t, simp_all)
        using CompDiag_assoc CompDiag_TensorDiag Arr_implies_Ide_Cod Ide_in_Hom
              TensorDiag_in_Hom CompDiag_in_Hom CompDiag_preserves_Diag
              TensorDiag_preserves_Diag CompDiag_Cod_Diag Diag_Diagonalize
              Diagonalize_in_Hom TensorDiag_assoc
           apply simp
        using CompDiag_assoc Arr_implies_Ide_Cod Ide_in_Hom
              CompDiag_in_Hom CompDiag_preserves_Diag
              CompDiag_Cod_Diag Diag_Diagonalize Diagonalize_in_Hom
          apply metis
        using CompDiag_assoc CompDiag_TensorDiag Arr_implies_Ide_Cod Ide_in_Hom
              TensorDiag_in_Hom CompDiag_in_Hom CompDiag_preserves_Diag
              TensorDiag_preserves_Diag CompDiag_Cod_Diag Diag_Diagonalize
              Diagonalize_in_Hom TensorDiag_assoc
        by simp_all
      thus ?thesis using assms by blast
    qed

    lemma Diagonalize_Comp_Arr_Dom:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>t \<^bold>\<cdot> Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Arr t \<Longrightarrow> \<^bold>\<lfloor>t \<^bold>\<cdot> Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        apply (induct t, simp_all)
        using CompDiag_assoc CompDiag_TensorDiag Arr_implies_Ide_Dom Ide_in_Hom
              TensorDiag_in_Hom CompDiag_in_Hom CompDiag_preserves_Diag
              TensorDiag_preserves_Diag CompDiag_Diag_Dom Diag_Diagonalize
              Diagonalize_in_Hom TensorDiag_assoc
           apply simp
        using CompDiag_assoc Arr_implies_Ide_Dom Ide_in_Hom
              CompDiag_in_Hom CompDiag_preserves_Diag
              CompDiag_Diag_Dom Diag_Diagonalize Diagonalize_in_Hom
          apply metis
        using CompDiag_assoc CompDiag_TensorDiag Arr_implies_Ide_Dom Ide_in_Hom
              TensorDiag_in_Hom CompDiag_in_Hom CompDiag_preserves_Diag
              TensorDiag_preserves_Diag CompDiag_Diag_Dom Diag_Diagonalize
              Diagonalize_in_Hom TensorDiag_assoc
        by simp_all
      thus ?thesis using assms by blast
    qed

    lemma Diagonalize_Inv:
    assumes "Can t"
    shows "\<^bold>\<lfloor>Inv t\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Can t \<Longrightarrow> \<^bold>\<lfloor>Inv t\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      proof (induct t, simp_all)
        fix u v
        assume I1: "\<^bold>\<lfloor>Inv u\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>u\<^bold>\<rfloor>"
        assume I2: "\<^bold>\<lfloor>Inv v\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>v\<^bold>\<rfloor>"
        show "Can u \<and> Can v \<Longrightarrow> Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>v\<^bold>\<rfloor> = Inv (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>)"
          using Inv_TensorDiag Diag_Diagonalize Can_implies_Arr Diagonalize_preserves_Can
                I1 I2
          by simp
        show "Can u \<and> Can v \<and> Dom u = Cod v \<Longrightarrow> Inv \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> = Inv (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>)"
          using Inv_CompDiag Diag_Diagonalize Can_implies_Arr Diagonalize_in_Hom
                Diagonalize_preserves_Can I1 I2
          by simp
        fix w
        assume I3: "\<^bold>\<lfloor>Inv w\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>w\<^bold>\<rfloor>"
        assume uvw: "Can u \<and> Can v \<and> Can w"
        show "Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (Inv \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>w\<^bold>\<rfloor>) = Inv ((\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>)"
          using uvw I1 I2 I3
                Inv_TensorDiag Diag_Diagonalize Can_implies_Arr Diagonalize_preserves_Can
                TensorDiag_preserves_Diag TensorDiag_preserves_Can TensorDiag_assoc
          by simp
        show "(Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>w\<^bold>\<rfloor> = Inv (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>))"
          using uvw I1 I2 I3
                Inv_TensorDiag Diag_Diagonalize Can_implies_Arr Diagonalize_preserves_Can
                TensorDiag_preserves_Diag TensorDiag_preserves_Can TensorDiag_assoc
                Inv_preserves_Can
          apply simp
          using TensorDiag_assoc by metis
      qed
      thus ?thesis using assms by blast
    qed

    text{*
      Our next objective is to begin making the connection, to be completed in a
      subsequent section, between arrows and their diagonalizations.
      To summarize, an arrow @{term t} and its diagonalization @{term "\<^bold>\<lfloor>t\<^bold>\<rfloor>"} are opposite sides
      of a square whose other sides are certain canonical terms
      @{text "Dom t\<^bold>\<down> \<in> Hom (Dom t) \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>"} and @{text "Cod t\<^bold>\<down> \<in> Hom (Cod t) \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"},
      where @{text "Dom t\<^bold>\<down>"} and @{text "Cod t\<^bold>\<down>"} are defined by the function @{text red}
      below.  The coherence theorem amounts to the statement that every such square commutes
      when the formal terms involved are evaluated in the evident way in any monoidal category.

      Function @{text red} defined below takes an identity term @{term a} to a canonical arrow
      @{text "a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>"}.  The auxiliary function @{text red2} takes a pair @{term "(a, b)"}
      of diagonal identity terms and produces a canonical arrow
      @{text "a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>"}.
      The canonical arrow @{text "a\<^bold>\<down>"} amounts to a ``parallel innermost reduction''
      from @{term a} to @{term "\<^bold>\<lfloor>a\<^bold>\<rfloor>"}, where the reduction steps are canonical arrows
      that involve the unitors and associator only in their uninverted forms.
      In general, a parallel innermost reduction from @{term a} will not be unique:
      at some points there is a choice available between left and right unitors
      and at other points there are choices between unitors and associators.
      These choices are inessential, and the ordering of the clauses in the function definitions
      below resolves them in an arbitrary way.  What is more important is having chosen an
      innermost reduction, which is what allows us to write these definitions in structurally
      recursive form.

      The essence of coherence is that the axioms for a monoidal category allow us to
      prove that any reduction from @{term a} to @{term "\<^bold>\<lfloor>a\<^bold>\<rfloor>"} is equivalent
      (under evaluation of terms) to a parallel innermost reduction.
      The problematic cases are terms of the form @{term "((a \<^bold>\<otimes> b) \<^bold>\<otimes> c) \<^bold>\<otimes> d"},
      which present a choice between an inner and outer reduction that lead to terms
      with different structures.  It is of course the pentagon axiom that ensures the
      confluence (under evaluation) of the two resulting paths.

      Although simple in appearance, the structurally recursive definitions below were
      difficult to get right even after I started to understand what I was doing.
      I wish I could have just written them down straightaway.  If so, then I could have
      avoided laboriously constructing and then throwing away thousands of lines of proof
      text that used a non-structural, ``operational'' approach to defining a reduction
      from @{term a} to @{term "\<^bold>\<lfloor>a\<^bold>\<rfloor>"}.
    *}

    fun red2                       (infixr "\<^bold>\<Down>" 53)
    where "\<^bold>\<I> \<^bold>\<Down> a = \<^bold>\<l>\<^bold>[a\<^bold>]"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> \<^bold>\<I> = \<^bold>\<r>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>]"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> a = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> a"
        | "(a \<^bold>\<otimes> b) \<^bold>\<Down> \<^bold>\<I> = \<^bold>\<r>\<^bold>[a \<^bold>\<otimes> b\<^bold>]"
        | "(a \<^bold>\<otimes> b) \<^bold>\<Down> c = (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) \<^bold>\<cdot> (a \<^bold>\<otimes> (b \<^bold>\<Down> c)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[a, b, c\<^bold>]"
        | "a \<^bold>\<Down> b = undefined"

    fun red                         ("_\<^bold>\<down>" [56] 56)
    where "\<^bold>\<I>\<^bold>\<down> = \<^bold>\<I>"
        | "\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>\<down> = \<^bold>\<langle>f\<^bold>\<rangle>"
        | "(a \<^bold>\<otimes> b)\<^bold>\<down> = (if Diag (a \<^bold>\<otimes> b) then a \<^bold>\<otimes> b else (\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<cdot> (a\<^bold>\<down> \<^bold>\<otimes> b\<^bold>\<down>))"
        | "a\<^bold>\<down> = undefined"

    lemma red_Diag [simp]:
    assumes "Ide a" and "Diag a"
    shows "a\<^bold>\<down> = a"
      using assms by (cases a) simp_all

    lemma red2_Diag:
    assumes "Diag (a \<^bold>\<otimes> b)"
    shows "a \<^bold>\<Down> b = a \<^bold>\<otimes> b"
    proof -
      have a: "a = \<^bold>\<langle>un_Prim a\<^bold>\<rangle>"
        using assms Diag_TensorE by metis
      have b: "Diag b \<and> b \<noteq> \<^bold>\<I>"
        using assms Diag_TensorE by metis
      show ?thesis using a b
        apply (cases b)
          apply simp_all
         apply (metis red2.simps(3))
        by (metis red2.simps(4))
    qed

    lemma Can_red2:
    assumes "Ide a" and "Diag a" and "Ide b" and "Diag b"
    shows "Can (a \<^bold>\<Down> b)"
    and "a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>"
    proof -
      have 0: "\<And>b. \<lbrakk> Ide a \<and> Diag a; Ide b \<and> Diag b \<rbrakk> \<Longrightarrow>
                     Can (a \<^bold>\<Down> b) \<and> a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>"
      proof (induct a, simp_all)
        fix b
        show "Ide b \<and> Diag b \<Longrightarrow> Can b \<and> Dom b = b \<and> Cod b = b"
          using Ide_implies_Can Ide_in_Hom Diagonalize_Diag by auto
        fix f
        show "\<lbrakk> C.ide f \<and> C.arr f; Ide b \<and> Diag b \<rbrakk> \<Longrightarrow>
                Can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b) \<and> Arr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b) \<and> Dom (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b) = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b \<and>
                                                Cod (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b) = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b"
          using Ide_implies_Can Ide_in_Hom by (cases b; auto)
        next
        fix a b c
        assume ab: "Ide a \<and> Ide b \<and> Diag (Tensor a b)"
        assume c: "Ide c \<and> Diag c"
        assume I1: "\<And>c. \<lbrakk> Diag a; Ide c \<and> Diag c \<rbrakk> \<Longrightarrow>
                          Can (a \<^bold>\<Down> c) \<and> Arr (a \<^bold>\<Down> c) \<and> Dom (a \<^bold>\<Down> c) = a \<^bold>\<otimes> c \<and>
                                                       Cod (a \<^bold>\<Down> c) = a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"
        assume I2: "\<And>c. \<lbrakk> Diag b; Ide c \<and> Diag c \<rbrakk> \<Longrightarrow>
                          Can (b \<^bold>\<Down> c) \<and> Arr (b \<^bold>\<Down> c) \<and> Dom (b \<^bold>\<Down> c) = b \<^bold>\<otimes> c \<and>
                                                       Cod (b \<^bold>\<Down> c) = b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"
        show "Can ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) \<and> Arr ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) \<and>
              Dom ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) = (a \<^bold>\<otimes> b) \<^bold>\<otimes> c \<and>
              Cod ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) = (\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"
        proof -
          have a: "Diag a \<and> Ide a"
            using ab Diag_TensorE by blast
          have b: "Diag b \<and> Ide b"
            using ab Diag_TensorE by blast
          have "c = \<^bold>\<I> \<Longrightarrow> ?thesis"
          proof -
            assume 1: "c = \<^bold>\<I>"
            have 2: "(a \<^bold>\<otimes> b) \<^bold>\<Down> c = \<^bold>\<r>\<^bold>[a \<^bold>\<otimes> b\<^bold>]"
              using 1 by simp
            have 3: "Can (a \<^bold>\<Down> b) \<and> Arr (a \<^bold>\<Down> b) \<and> Dom (a \<^bold>\<Down> b) = a \<^bold>\<otimes> b \<and> Cod (a \<^bold>\<Down> b) = a \<^bold>\<otimes> b"
              using a b ab 1 2 I1 Diagonalize_Diag Diagonalize.simps(3) by metis
            hence 4: "Seq (a \<^bold>\<Down> b) \<^bold>\<r>\<^bold>[a \<^bold>\<otimes> b\<^bold>]"
              using ab
              by (metis (mono_tags, lifting) Arr.simps(7) Cod.simps(3) Cod.simps(7)
                  Diag_implies_Arr Ide_in_Hom mem_Collect_eq)
            have "Can ((a \<^bold>\<otimes> b) \<^bold>\<Down> c)"
              using 1 2 3 4 ab by (simp add: Ide_implies_Can)
            moreover have "Dom ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) = (a \<^bold>\<otimes> b) \<^bold>\<otimes> c"
              using 1 2 3 4 a b ab I1 Ide_in_Hom TensorDiag_preserves_Diag by simp
            moreover have "Cod ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) = \<^bold>\<lfloor>(a \<^bold>\<otimes> b) \<^bold>\<otimes> c\<^bold>\<rfloor>"
             using 1 2 3 4 ab using Diagonalize_Diag by fastforce
            ultimately show ?thesis using Can_implies_Arr by (simp add: 1 ab)
          qed
          moreover have "c \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
          proof -
            assume 1: "c \<noteq> \<^bold>\<I>"
            have 2: "(a \<^bold>\<otimes> b) \<^bold>\<Down> c = (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) \<^bold>\<cdot> (a \<^bold>\<otimes> b \<^bold>\<Down> c) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[a, b, c\<^bold>]"
              using 1 a b ab c by (cases c; simp)
            have 3: "Can (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) \<and> Dom (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) = a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor> \<and>
                                          Cod (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) = \<^bold>\<lfloor>a \<^bold>\<otimes> (b \<^bold>\<otimes> c)\<^bold>\<rfloor>"
            proof -
              have "Can (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) \<and> Dom (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) = a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor> \<and>
                                         Cod (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) = \<^bold>\<lfloor>a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>\<^bold>\<rfloor>"
                using a c ab 1 2 I1 Diag_implies_Arr Diag_Diagonalize(1)
                      Diagonalize_preserves_Ide TensorDiag_preserves_Ide
                      TensorDiag_preserves_Diag(1)
                by auto
              moreover have "\<^bold>\<lfloor>a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>a \<^bold>\<otimes> (b \<^bold>\<otimes> c)\<^bold>\<rfloor>"
                using ab c Diagonalize_Tensor Diagonalize_Diagonalize Diag_implies_Arr
                by (metis Arr.simps(3) Diagonalize.simps(3))
              ultimately show ?thesis by presburger
            qed
            have 4: "Can (b \<^bold>\<Down> c) \<and> Dom (b \<^bold>\<Down> c) = b \<^bold>\<otimes> c \<and> Cod (b \<^bold>\<Down> c) = \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>"
              using b c ab 1 2 I2 by simp
            hence "Can (a \<^bold>\<otimes> (b \<^bold>\<Down> c)) \<and> Dom (a \<^bold>\<otimes> (b \<^bold>\<Down> c)) = a \<^bold>\<otimes> (b \<^bold>\<otimes> c) \<and>
                                        Cod (a \<^bold>\<otimes> (b \<^bold>\<Down> c)) = a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>"
              using ab Ide_implies_Can Ide_in_Hom by force
            moreover have "\<^bold>\<lfloor>a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>"
            proof -
              have "\<^bold>\<lfloor>a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>\<^bold>\<rfloor> = a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)"
                using a b c 4
                by (metis Arr_implies_Ide_Dom Can_implies_Arr Ide_implies_Arr
                    Diag_Diagonalize(1) Diagonalize.simps(3) Diagonalize_Diag)
              also have "... = (a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"
                using a b ab c TensorDiag_assoc by metis
              also have "... = \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>"
                using a b c by (metis Diagonalize.simps(3) Diagonalize_Diag)
              finally show ?thesis by blast
            qed
            moreover have "Can \<^bold>\<a>\<^bold>[a, b, c\<^bold>] \<and> Dom \<^bold>\<a>\<^bold>[a, b, c\<^bold>] = (a \<^bold>\<otimes> b) \<^bold>\<otimes> c \<and>
                                            Cod \<^bold>\<a>\<^bold>[a, b, c\<^bold>] = a \<^bold>\<otimes> (b \<^bold>\<otimes> c)"
              using ab c Ide_implies_Can Ide_in_Hom by auto
            ultimately show ?thesis
              using ab c 2 3 4 Diag_implies_Arr Diagonalize_Diagonalize Ide_implies_Can
                    Diagonalize_Diag Arr_implies_Ide_Dom Can_implies_Arr
              by (metis Can.simps(4) Cod.simps(4) Dom.simps(4) Diagonalize.simps(3))
          qed
          ultimately show ?thesis by blast
        qed
      qed
      show "Can (a \<^bold>\<Down> b)" using assms 0 by blast
      show "a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>" using 0 assms by blast
    qed

    lemma red2_in_Hom:
    assumes "Ide a" and "Diag a" and "Ide b" and "Diag b"
    shows "a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>"
      using assms Can_red2 Can_implies_Arr by simp

    lemma Can_red:
    assumes "Ide a"
    shows "Can (a\<^bold>\<down>)" and "a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>"
    proof -
      have 0: "Ide a \<Longrightarrow> Can (a\<^bold>\<down>) \<and> a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>"
      proof (induct a, simp_all)
        fix b c
        assume b: "Can (b\<^bold>\<down>) \<and> Arr (b\<^bold>\<down>) \<and> Dom (b\<^bold>\<down>) = b \<and> Cod (b\<^bold>\<down>) = \<^bold>\<lfloor>b\<^bold>\<rfloor>"
        assume c: "Can (c\<^bold>\<down>) \<and> Arr (c\<^bold>\<down>) \<and> Dom (c\<^bold>\<down>) = c \<and> Cod (c\<^bold>\<down>) = \<^bold>\<lfloor>c\<^bold>\<rfloor>"
        assume bc: "Ide b \<and> Ide c"
        show "(Diag (b \<^bold>\<otimes> c) \<longrightarrow>
                 Can b \<and> Can c \<and> Dom b = b \<and> Dom c = c \<and> Cod b \<^bold>\<otimes> Cod c = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and>
              (\<not> Diag (b \<^bold>\<otimes> c) \<longrightarrow>
                 Can (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and> Dom (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>c\<^bold>\<rfloor> \<and> Arr (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and>
                 Dom (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>c\<^bold>\<rfloor> \<and> Cod (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>)"
        proof
          show "Diag (b \<^bold>\<otimes> c) \<longrightarrow>
                  Can b \<and> Can c \<and> Dom b = b \<and> Dom c = c \<and> Cod b \<^bold>\<otimes> Cod c = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>"
            using bc Diag_TensorE Ide_implies_Can Inv_preserves_Can(2)
                  CompDiag_Ide_Diag Inv_Ide Diagonalize.simps(3) Diagonalize_Diag
            by (metis CompDiag_Inv_Can)
          show "\<not> Diag (b \<^bold>\<otimes> c) \<longrightarrow>
                  Can (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and> Dom (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>c\<^bold>\<rfloor> \<and> Arr (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and>
                                    Dom (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>c\<^bold>\<rfloor> \<and> Cod (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>"
            using b c bc Ide_in_Hom Ide_implies_Can Diagonalize_Diag Can_red2 Diag_Diagonalize
                  Ide_implies_Arr Diagonalize_Tensor Diagonalize_preserves_Ide
                  TensorDiag_preserves_Diag TensorDiag_preserves_Ide
                  TensorDiag_preserves_Can
            by (cases b) simp_all
        qed
      qed
      show "Can (a\<^bold>\<down>)" using assms 0 by blast
      show "a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>" using assms 0 by blast
    qed

    lemma red_in_Hom:
    assumes "Ide a"
    shows "a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>"
      using assms Can_red Can_implies_Arr by simp

    lemma Diagonalize_red [simp]:
    assumes "Ide a"
    shows "\<^bold>\<lfloor>a\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>a\<^bold>\<rfloor>"
      using assms Can_red Ide_Diagonalize_Can Diagonalize_in_Hom Ide_in_Hom by fastforce

    lemma Diagonalize_red2 [simp]:
    assumes "Ide a" and "Ide b" and "Diag a" and "Diag b"
    shows "\<^bold>\<lfloor>a \<^bold>\<Down> b\<^bold>\<rfloor> = \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>"
      using assms Can_red2 Ide_Diagonalize_Can Diagonalize_in_Hom [of "a \<^bold>\<Down> b"] red2_in_Hom Ide_in_Hom
      by simp

  end

  section "Coherence"

  context category
  begin

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

  text{*
    If @{term D} is a monoidal category, then a functor @{text "V: C \<rightarrow> D"} extends
    in an evident way to an evaluation map that interprets each formal arrow of the
    monoidal language of @{term C} as an arrow of @{term D}.
  *}

  locale evaluation_map =
    monoidal_language C +
    monoidal_category D T \<alpha> \<iota> +
    V: "functor" C D V
    for C :: "'c comp"                  (infixr "\<cdot>\<^sub>C" 55)
    and D :: "'d comp"                  (infixr "\<cdot>" 55)
    and T :: "'d * 'd \<Rightarrow> 'd"
    and \<alpha> :: "'d * 'd * 'd \<Rightarrow> 'd"
    and \<iota> :: 'd
    and V :: "'c \<Rightarrow> 'd"
  begin

    notation unity                     ("\<I>")
    notation tensor                    (infixr "\<otimes>" 53)
    notation runit                     ("\<r>[_]")
    notation lunit                     ("\<l>[_]")
    notation assoc'                    ("\<a>\<^sup>-\<^sup>1[_, _, _]")
    notation runit'                    ("\<r>\<^sup>-\<^sup>1[_]")
    notation lunit'                    ("\<l>\<^sup>-\<^sup>1[_]")

    primrec eval :: "'c term \<Rightarrow> 'd"    ("\<guillemotleft>_\<guillemotright>")
    where "\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle>\<guillemotright> = V f"
        | "\<guillemotleft>\<^bold>\<I>\<guillemotright> = \<I>"
        | "\<guillemotleft>t \<^bold>\<otimes> u\<guillemotright> = \<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>"
        | "\<guillemotleft>t \<^bold>\<cdot> u\<guillemotright> = \<guillemotleft>t\<guillemotright> \<cdot> \<guillemotleft>u\<guillemotright>"
        | "\<guillemotleft>\<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright> = \<ll> \<guillemotleft>t\<guillemotright>"
        | "\<guillemotleft>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> = \<ll>' \<guillemotleft>t\<guillemotright>"
        | "\<guillemotleft>\<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright> = \<rho> \<guillemotleft>t\<guillemotright>"
        | "\<guillemotleft>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> = \<rho>' \<guillemotleft>t\<guillemotright>"
        | "\<guillemotleft>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright> = \<alpha> (\<guillemotleft>t\<guillemotright>, \<guillemotleft>u\<guillemotright>, \<guillemotleft>v\<guillemotright>)"
        | "\<guillemotleft>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright> = \<alpha>' (\<guillemotleft>t\<guillemotright>, \<guillemotleft>u\<guillemotright>, \<guillemotleft>v\<guillemotright>)"

    text{*
      Identity terms evaluate to identities of @{text D} and evaluation preserves
      domain and codomain.
    *}

    lemma ide_eval_Ide [simp]:
    shows "Ide t \<Longrightarrow> ide \<guillemotleft>t\<guillemotright>"
      apply (induct t)
      by (auto simp add: tensor_preserves_ide)

    lemma eval_in_hom:
    shows "Arr t \<Longrightarrow> \<guillemotleft>t\<guillemotright> \<in> hom \<guillemotleft>Dom t\<guillemotright> \<guillemotleft>Cod t\<guillemotright>"
      apply (induct t)
               apply simp
              apply simp
      using T.preserves_hom apply auto[1]
            apply auto[1]
    proof -
      fix t u v
      assume I: "Arr t \<Longrightarrow> \<guillemotleft>t\<guillemotright> \<in> hom \<guillemotleft>Dom t\<guillemotright> \<guillemotleft>Cod t\<guillemotright>"
      show "Arr \<^bold>\<l>\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>\<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright> \<in> hom \<guillemotleft>Dom \<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright> \<guillemotleft>Cod \<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright>"
        using I \<ll>.preserves_hom arr_cod_iff_arr [of "\<guillemotleft>t\<guillemotright>"] Arr_implies_Ide_Dom by simp
      show "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> \<in> hom \<guillemotleft>Dom \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> \<guillemotleft>Cod \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright>"
        using I \<ll>'.preserves_hom arr_dom_iff_arr [of "\<guillemotleft>t\<guillemotright>"] Arr_implies_Ide_Cod by simp
      show "Arr \<^bold>\<r>\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>\<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright> \<in> hom \<guillemotleft>Dom \<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright> \<guillemotleft>Cod \<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright>"
        using I \<rho>.preserves_hom arr_cod_iff_arr [of "\<guillemotleft>t\<guillemotright>"] Arr_implies_Ide_Dom by simp
      show "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> \<in> hom \<guillemotleft>Dom \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> \<guillemotleft>Cod \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright>"
        using I \<rho>'.preserves_hom arr_dom_iff_arr [of "\<guillemotleft>t\<guillemotright>"] Arr_implies_Ide_Cod by simp
      assume I1: "Arr t \<Longrightarrow> \<guillemotleft>t\<guillemotright> \<in> hom \<guillemotleft>Dom t\<guillemotright> \<guillemotleft>Cod t\<guillemotright>"
      assume I2: "Arr u \<Longrightarrow> \<guillemotleft>u\<guillemotright> \<in> hom \<guillemotleft>Dom u\<guillemotright> \<guillemotleft>Cod u\<guillemotright>"
      assume I3: "Arr v \<Longrightarrow> \<guillemotleft>v\<guillemotright> \<in> hom \<guillemotleft>Dom v\<guillemotright> \<guillemotleft>Cod v\<guillemotright>"
      show "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>] \<Longrightarrow> \<guillemotleft>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright> \<in> hom \<guillemotleft>Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright> \<guillemotleft>Cod \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright>"
        using I1 I2 I3
              arr_dom_iff_arr [of "\<guillemotleft>t\<guillemotright>"] arr_dom_iff_arr [of "\<guillemotleft>u\<guillemotright>"]
              arr_dom_iff_arr [of "\<guillemotleft>v\<guillemotright>"] arr_cod_iff_arr [of "\<guillemotleft>t\<guillemotright>"]
              arr_cod_iff_arr [of "\<guillemotleft>u\<guillemotright>"] arr_cod_iff_arr [of "\<guillemotleft>v\<guillemotright>"]
              T.ToTC_simp T.ToCT_simp
        by auto
      show "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] \<Longrightarrow> \<guillemotleft>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright> \<in> hom \<guillemotleft>Dom \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright> \<guillemotleft>Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright>"
       proof -
        assume "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
        hence 1: "Arr t \<and> Arr u \<and> Arr v" by simp
        have "\<guillemotleft>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright> = ((\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>) \<otimes> \<guillemotleft>v\<guillemotright>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<guillemotleft>t\<guillemotright>, dom \<guillemotleft>u\<guillemotright>, dom \<guillemotleft>v\<guillemotright>]"
          using 1 I1 I2 I3 \<alpha>'_simp [of "\<guillemotleft>t\<guillemotright>" "\<guillemotleft>u\<guillemotright>" "\<guillemotleft>v\<guillemotright>"] Arr_implies_Ide_Dom by simp
        moreover have "\<a>\<^sup>-\<^sup>1[dom \<guillemotleft>t\<guillemotright>, dom \<guillemotleft>u\<guillemotright>, dom \<guillemotleft>v\<guillemotright>]
                 \<in> hom (dom \<guillemotleft>t\<guillemotright> \<otimes> dom \<guillemotleft>u\<guillemotright> \<otimes> dom \<guillemotleft>v\<guillemotright>) ((dom \<guillemotleft>t\<guillemotright> \<otimes> dom \<guillemotleft>u\<guillemotright>) \<otimes> dom \<guillemotleft>v\<guillemotright>)"
          using 1 I1 I2 I3 ide_dom assoc'_in_hom [of "dom \<guillemotleft>t\<guillemotright>" "dom \<guillemotleft>u\<guillemotright>" "dom \<guillemotleft>v\<guillemotright>"]
                ide_dom [of "\<guillemotleft>t\<guillemotright>"] ide_dom [of "\<guillemotleft>u\<guillemotright>"] ide_dom [of "\<guillemotleft>v\<guillemotright>"]
          by simp
        moreover have "(\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>) \<otimes> \<guillemotleft>v\<guillemotright> \<in> hom ((dom \<guillemotleft>t\<guillemotright> \<otimes> dom \<guillemotleft>u\<guillemotright>) \<otimes> dom \<guillemotleft>v\<guillemotright>)
                                                ((cod \<guillemotleft>t\<guillemotright> \<otimes> cod \<guillemotleft>u\<guillemotright>) \<otimes> cod \<guillemotleft>v\<guillemotright>)"
          using 1 I1 I2 I3 tensor_in_hom by simp
        ultimately show ?thesis
          using 1 I1 I2 I3 ide_dom ide_cod tensor_in_hom ide_eval_Ide
                Arr_implies_Ide_Dom Arr_implies_Ide_Cod assoc'_in_hom
          by simp
      qed
    qed

    lemma dom_eval:
    assumes "Arr f"
    shows "dom \<guillemotleft>f\<guillemotright> = \<guillemotleft>Dom f\<guillemotright>"
      using assms eval_in_hom by simp
      
    lemma cod_eval:
    assumes "Arr f"
    shows "cod \<guillemotleft>f\<guillemotright> = \<guillemotleft>Cod f\<guillemotright>"
      using assms eval_in_hom by simp
      
    lemma eval_Prim [simp]:
    assumes "C.arr f"
    shows "\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle>\<guillemotright> = V f"
      by simp

    lemma eval_Tensor [simp]:
    assumes "Arr t" and "Arr u"
    shows "\<guillemotleft>t \<^bold>\<otimes> u\<guillemotright> = \<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>"
      using assms eval_in_hom by auto

    lemma eval_Comp [simp]:
    assumes "Arr t" and "Arr u" and "Dom t = Cod u"
    shows " \<guillemotleft>t \<^bold>\<cdot> u\<guillemotright> = \<guillemotleft>t\<guillemotright> \<cdot> \<guillemotleft>u\<guillemotright>"
      using assms by simp

    lemma eval_Lunit [simp]:
    assumes "Arr t"
    shows "\<guillemotleft>\<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright> = \<l>[\<guillemotleft>Cod t\<guillemotright>] \<cdot> (\<I> \<otimes> \<guillemotleft>t\<guillemotright>)"
      using assms eval_in_hom \<ll>.is_natural_2 [of "\<guillemotleft>t\<guillemotright>"] \<ll>_ide_simp [of "\<guillemotleft>Cod t\<guillemotright>"] Ide_in_Hom
      by (simp add: Arr_implies_Ide_Cod)

    lemma eval_Lunit' [simp]:
    assumes "Arr t"
    shows "\<guillemotleft>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> = \<l>\<^sup>-\<^sup>1[\<guillemotleft>Cod t\<guillemotright>] \<cdot> \<guillemotleft>t\<guillemotright>"
      using assms eval_in_hom \<ll>'.is_natural_2 [of "\<guillemotleft>t\<guillemotright>"] \<ll>_ide_simp Ide_in_Hom
      by (simp add: Arr_implies_Ide_Cod)

    lemma eval_Runit [simp]:
    assumes "Arr t"
    shows "\<guillemotleft>\<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright> = \<r>[\<guillemotleft>Cod t\<guillemotright>] \<cdot> (\<guillemotleft>t\<guillemotright> \<otimes> \<I>)"
      using assms eval_in_hom \<rho>.is_natural_2 [of "\<guillemotleft>t\<guillemotright>"] \<rho>_ide_simp Ide_in_Hom
      by (simp add: Arr_implies_Ide_Cod)

    lemma eval_Runit' [simp]:
    assumes "Arr t"
    shows "\<guillemotleft>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> = \<r>\<^sup>-\<^sup>1[\<guillemotleft>Cod t\<guillemotright>] \<cdot> \<guillemotleft>t\<guillemotright>"
      using assms eval_in_hom \<rho>'.is_natural_2 [of "\<guillemotleft>t\<guillemotright>"] \<rho>_ide_simp Ide_in_Hom
      by (simp add: Arr_implies_Ide_Cod)

    lemma eval_Assoc [simp]:
    assumes "Arr t" and "Arr u" and "Arr v"
    shows "\<guillemotleft>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright> = \<a>[cod \<guillemotleft>t\<guillemotright>, cod \<guillemotleft>u\<guillemotright>, cod \<guillemotleft>v\<guillemotright>] \<cdot> ((\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>) \<otimes> \<guillemotleft>v\<guillemotright>)"
    proof -
      have "\<guillemotleft>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright> = \<alpha> (\<guillemotleft>t\<guillemotright>, \<guillemotleft>u\<guillemotright>, \<guillemotleft>v\<guillemotright>)" by simp
      also have "... = (\<alpha> (CCC.cod (\<guillemotleft>t\<guillemotright>, \<guillemotleft>u\<guillemotright>, \<guillemotleft>v\<guillemotright>))) \<cdot> (T.ToTC (\<guillemotleft>t\<guillemotright>, \<guillemotleft>u\<guillemotright>, \<guillemotleft>v\<guillemotright>))"
        using assms eval_in_hom \<alpha>.is_natural_2 [of "(\<guillemotleft>t\<guillemotright>, \<guillemotleft>u\<guillemotright>, \<guillemotleft>v\<guillemotright>)"] by simp
      also have "... = (\<alpha> (cod \<guillemotleft>t\<guillemotright>, cod \<guillemotleft>u\<guillemotright>, cod \<guillemotleft>v\<guillemotright>)) \<cdot> ((\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>) \<otimes> \<guillemotleft>v\<guillemotright>)"
        using assms CCC.arr_char CC.arr_char CCC.cod_simp CC.cod_char eval_in_hom
              mem_Collect_eq fst_conv snd_conv T.ToTC_simp tensor_in_hom
        by simp
      finally show ?thesis
        using assms ide_eval_Ide Arr_implies_Ide_Dom Arr_implies_Ide_Cod by simp
    qed

    lemma eval_Assoc' [simp]:
    assumes "Arr t" and "Arr u" and "Arr v"
    shows "\<guillemotleft>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright> = \<a>\<^sup>-\<^sup>1[cod \<guillemotleft>t\<guillemotright>, cod \<guillemotleft>u\<guillemotright>, cod \<guillemotleft>v\<guillemotright>] \<cdot> (\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright> \<otimes> \<guillemotleft>v\<guillemotright>)"
      using assms eval_in_hom \<alpha>'_simp [of "\<guillemotleft>t\<guillemotright>" "\<guillemotleft>u\<guillemotright>" "\<guillemotleft>v\<guillemotright>"]
            assoc'_naturality [of "\<guillemotleft>t\<guillemotright>" "\<guillemotleft>u\<guillemotright>" "\<guillemotleft>v\<guillemotright>"] Arr_implies_Ide_Cod
      by simp

    text{*
      The following are conveniences for the case of identity arguments
      to avoid having to get rid of the extra identities that are introduced by
      the general formulas above.
    *}

    lemma eval_Lunit_Ide [simp]:
    assumes "Ide a"
    shows "\<guillemotleft>\<^bold>\<l>\<^bold>[a\<^bold>]\<guillemotright> = \<l>[\<guillemotleft>a\<guillemotright>]"
      using assms lunit_in_hom by simp

    lemma eval_Lunit'_Ide [simp]:
    assumes "Ide a"
    shows "\<guillemotleft>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]\<guillemotright> = \<l>\<^sup>-\<^sup>1[\<guillemotleft>a\<guillemotright>]"
      using assms lunit_in_hom by simp

    lemma eval_Runit_Ide [simp]:
    assumes "Ide a"
    shows "\<guillemotleft>\<^bold>\<r>\<^bold>[a\<^bold>]\<guillemotright> = \<r>[\<guillemotleft>a\<guillemotright>]"
      using assms runit_in_hom by simp

    lemma eval_Runit'_Ide [simp]:
    assumes "Ide a"
    shows "\<guillemotleft>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]\<guillemotright> = \<r>\<^sup>-\<^sup>1[\<guillemotleft>a\<guillemotright>]"
      using assms runit_in_hom [of "\<guillemotleft>a\<guillemotright>"] by simp

    lemma eval_Assoc_Ide [simp]:
    assumes "Ide a" and "Ide b" and "Ide c"
    shows "\<guillemotleft>\<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<guillemotright> = \<a>[\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
      using assms assoc_in_hom comp_cod_arr [of "\<a>[\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"] by simp

    lemma eval_Assoc'_Ide [simp]:
    assumes "Ide a" and "Ide b" and "Ide c"
    shows "\<guillemotleft>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[a, b, c\<^bold>]\<guillemotright> = \<a>\<^sup>-\<^sup>1[\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
      using assms assoc_in_hom comp_cod_arr [of "\<a>[\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"] \<alpha>'_ide_simp by simp

    text{*
      Canonical arrows evaluate to isomorphisms in @{text D}, and formal inverses evaluate
      to inverses in @{text D}.
    *}

    lemma iso_eval_Can:
    shows "Can t \<Longrightarrow> iso \<guillemotleft>t\<guillemotright>"
    proof (induct t; simp add: fsts.intros snds.intros tensor_preserves_iso)
      show "\<And>t1 t2. \<lbrakk> iso \<guillemotleft>t1\<guillemotright>; iso \<guillemotleft>t2\<guillemotright>; Can t1 \<and> Can t2 \<and> Dom t1 = Cod t2 \<rbrakk> \<Longrightarrow>
                    iso (\<guillemotleft>t1\<guillemotright> \<cdot> \<guillemotleft>t2\<guillemotright>)"
        using Can_implies_Arr eval_in_hom isos_compose by auto
      show "\<And>t. \<lbrakk> iso \<guillemotleft>t\<guillemotright>; Can t \<rbrakk> \<Longrightarrow> iso (\<guillemotleft>t\<guillemotright> \<cdot> lunit (dom \<guillemotleft>t\<guillemotright>))"
        using \<ll>.preserves_iso by auto
      show "\<And>t. \<lbrakk> iso \<guillemotleft>t\<guillemotright>; Can t \<rbrakk> \<Longrightarrow> iso (\<ll>'.map \<guillemotleft>t\<guillemotright>)"
        using \<ll>'.preserves_iso by simp
      show "\<And>t. \<lbrakk> iso \<guillemotleft>t\<guillemotright>; Can t \<rbrakk> \<Longrightarrow> iso (\<guillemotleft>t\<guillemotright> \<cdot> runit (dom \<guillemotleft>t\<guillemotright>))"
        using \<rho>.preserves_iso by auto
      show "\<And>t. \<lbrakk> iso \<guillemotleft>t\<guillemotright>; Can t \<rbrakk> \<Longrightarrow> iso (\<rho>'.map \<guillemotleft>t\<guillemotright>)"
        using \<rho>'.preserves_iso by simp
      show "\<And>t1 t2 t3. \<lbrakk> iso \<guillemotleft>t1\<guillemotright>; iso \<guillemotleft>t2\<guillemotright>; iso \<guillemotleft>t3\<guillemotright>; Can t1 \<and> Can t2 \<and> Can t3 \<rbrakk> \<Longrightarrow>
                       iso (assoc \<guillemotleft>t1\<guillemotright> \<guillemotleft>t2\<guillemotright> \<guillemotleft>t3\<guillemotright>)"
        using \<alpha>.preserves_iso CCC.iso_char CC.iso_char by auto
      show "\<And>t1 t2 t3. \<lbrakk> iso \<guillemotleft>t1\<guillemotright>; iso \<guillemotleft>t2\<guillemotright>; iso \<guillemotleft>t3\<guillemotright>; Can t1 \<and> Can t2 \<and> Can t3 \<rbrakk> \<Longrightarrow>
                       iso (\<alpha>' (\<guillemotleft>t1\<guillemotright>, \<guillemotleft>t2\<guillemotright>, \<guillemotleft>t3\<guillemotright>))"
        using \<alpha>'.preserves_iso CCC.iso_char CC.iso_char by auto
    qed

    lemma eval_Inv_Can:
    shows "Can t \<Longrightarrow> \<guillemotleft>Inv t\<guillemotright> = inv \<guillemotleft>t\<guillemotright>"
    proof (induct t)
      show "\<And>x. Can \<^bold>\<langle>x\<^bold>\<rangle> \<Longrightarrow> \<guillemotleft>Inv \<^bold>\<langle>x\<^bold>\<rangle>\<guillemotright> = inv \<guillemotleft>\<^bold>\<langle>x\<^bold>\<rangle>\<guillemotright>" by simp
      show "Can \<^bold>\<I> \<Longrightarrow> \<guillemotleft>Inv \<^bold>\<I>\<guillemotright> = inv \<guillemotleft>\<^bold>\<I>\<guillemotright>" by simp
      show "\<And>t1 t2. (Can t1 \<Longrightarrow> \<guillemotleft>Inv t1\<guillemotright> = inv \<guillemotleft>t1\<guillemotright>) \<Longrightarrow>
                    (Can t2 \<Longrightarrow> \<guillemotleft>Inv t2\<guillemotright> = inv \<guillemotleft>t2\<guillemotright>) \<Longrightarrow>
                     Can (t1 \<^bold>\<otimes> t2) \<Longrightarrow> \<guillemotleft>Inv (t1 \<^bold>\<otimes> t2)\<guillemotright> = inv \<guillemotleft>t1 \<^bold>\<otimes> t2\<guillemotright>"
        using iso_eval_Can inv_tensor iso_inv_iso by auto
      show "\<And>t1 t2. (Can t1 \<Longrightarrow> \<guillemotleft>Inv t1\<guillemotright> = inv \<guillemotleft>t1\<guillemotright>) \<Longrightarrow>
                    (Can t2 \<Longrightarrow> \<guillemotleft>Inv t2\<guillemotright> = inv \<guillemotleft>t2\<guillemotright>) \<Longrightarrow>
                     Can (t1 \<^bold>\<cdot> t2) \<Longrightarrow> \<guillemotleft>Inv (t1 \<^bold>\<cdot> t2)\<guillemotright> = inv \<guillemotleft>t1 \<^bold>\<cdot> t2\<guillemotright>"
        using iso_eval_Can inv_comp iso_inv_iso eval_in_hom Can_implies_Arr by auto
      fix t
      assume I: "Can t \<Longrightarrow> \<guillemotleft>Inv t\<guillemotright> = inv \<guillemotleft>t\<guillemotright>"
      show "Can \<^bold>\<l>\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>Inv \<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright> = inv \<guillemotleft>\<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright>"
      proof -
        assume t: "Can \<^bold>\<l>\<^bold>[t\<^bold>]"
        have "\<guillemotleft>Inv \<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright> = \<guillemotleft>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]\<guillemotright>" by simp
        also have "... = \<ll>' (inv \<guillemotleft>t\<guillemotright>)"
          using t I by simp
        also have "... = \<ll>' (cod (inv \<guillemotleft>t\<guillemotright>)) \<cdot> inv \<guillemotleft>t\<guillemotright>"
          using t \<ll>'.is_natural_2 map_simp iso_inv_iso iso_is_arr iso_eval_Can by fastforce
        also have "... = inv (\<guillemotleft>t\<guillemotright> \<cdot> \<ll> (dom \<guillemotleft>t\<guillemotright>))"
        proof -
          have 1: "iso \<guillemotleft>t\<guillemotright>" using t iso_eval_Can by simp
          moreover have "iso (\<ll> (dom \<guillemotleft>t\<guillemotright>))"
            using t 1 \<ll>.components_are_iso ide_dom by blast
          moreover have "seq \<guillemotleft>t\<guillemotright> (\<ll> (dom \<guillemotleft>t\<guillemotright>))"
            using t 1 \<ll>.preserves_cod \<ll>.preserves_arr arr_dom_iff_arr cod_dom iso_is_arr map_simp
            by presburger
          ultimately show ?thesis
            using t 1 inv_comp \<ll>'.map_ide_simp inv_is_inverse inv_in_hom by simp
        qed
        also have "... = inv \<guillemotleft>\<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright>"
          using t eval.simps(7) \<ll>_ide_simp iso_eval_Can by auto
        finally show ?thesis by blast
      qed
      show "Can \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>Inv \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> = inv \<guillemotleft>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright>"
      proof -
        assume t: "Can (Lunit' t)"
        have "\<guillemotleft>Inv (Lunit' t)\<guillemotright> = \<guillemotleft>Lunit (Inv t)\<guillemotright>" by simp
        also have "... = \<ll> (inv \<guillemotleft>t\<guillemotright>)"
          using t I by simp
        also have "... = inv \<guillemotleft>t\<guillemotright> \<cdot> \<ll> (dom (inv \<guillemotleft>t\<guillemotright>))"
          using t \<ll>.is_natural_1 [of "inv \<guillemotleft>t\<guillemotright>"] by (simp add: arr_dom_iff_arr)
        also have "... = inv (\<ll>' (cod \<guillemotleft>t\<guillemotright>) \<cdot> \<guillemotleft>t\<guillemotright>)"
        proof -
          have 1: "iso \<guillemotleft>t\<guillemotright>" using t iso_eval_Can by simp
          moreover have "iso (\<ll>' (cod \<guillemotleft>t\<guillemotright>))"
            using t 1 \<ll>'.components_are_iso ide_cod by blast
          moreover have "seq (\<ll>' (cod \<guillemotleft>t\<guillemotright>)) \<guillemotleft>t\<guillemotright>"
            using t 1 \<ll>'.preserves_dom \<ll>'.preserves_arr arr_cod_iff_arr dom_cod iso_is_arr map_simp
            by presburger
          ultimately show ?thesis
            using t 1 inv_comp \<ll>'.map_ide_simp inv_is_inverse inv_in_hom \<ll>.components_are_iso
            by simp
        qed
        also have "... = inv \<guillemotleft>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright>"
          using t \<ll>'.is_natural_2 iso_eval_Can by force
        finally show ?thesis by auto
      qed
      show "Can \<^bold>\<r>\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>Inv \<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright> = inv \<guillemotleft>\<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright>"
      proof -
        assume t: "Can \<^bold>\<r>\<^bold>[t\<^bold>]"
        have "\<guillemotleft>Inv \<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright> = \<guillemotleft>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]\<guillemotright>" by simp
        also have "... = \<rho>' (inv \<guillemotleft>t\<guillemotright>)"
          using t I by simp
        also have "... = \<rho>' (cod (inv \<guillemotleft>t\<guillemotright>)) \<cdot> inv \<guillemotleft>t\<guillemotright>"
          using t \<rho>'.is_natural_2 map_simp iso_inv_iso iso_is_arr iso_eval_Can by fastforce
        also have "... = inv (\<guillemotleft>t\<guillemotright> \<cdot> \<rho> (dom \<guillemotleft>t\<guillemotright>))"
        proof -
          have 1: "iso \<guillemotleft>t\<guillemotright>" using t iso_eval_Can by simp
          moreover have "iso (\<rho> (dom \<guillemotleft>t\<guillemotright>))"
            using t 1 \<rho>.components_are_iso ide_dom by blast
          moreover have "seq \<guillemotleft>t\<guillemotright> (\<rho> (dom \<guillemotleft>t\<guillemotright>))"
            using t 1 \<rho>.preserves_cod \<rho>.preserves_arr arr_dom_iff_arr cod_dom iso_is_arr map_simp
            by presburger
          ultimately show ?thesis
            using t 1 inv_comp \<rho>'.map_ide_simp inv_is_inverse inv_in_hom by simp
        qed
        also have "... = inv \<guillemotleft>\<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright>"
          using t eval.simps(7) \<rho>_ide_simp iso_eval_Can by auto
        finally show ?thesis by blast
      qed
      show "Can \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>Inv \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> = inv \<guillemotleft>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright>"
      proof -
        assume t: "Can \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        have "\<guillemotleft>Inv \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> = \<guillemotleft>\<^bold>\<r>\<^bold>[Inv t\<^bold>]\<guillemotright>"
          by simp
        also have "... = \<rho> (inv \<guillemotleft>t\<guillemotright>)"
          using t I by simp
        also have "... = inv \<guillemotleft>t\<guillemotright> \<cdot> \<rho> (dom (inv \<guillemotleft>t\<guillemotright>))"
          using t \<rho>.is_natural_1 by (simp add: arr_dom_iff_arr)
        also have "... = inv (\<rho>' (cod \<guillemotleft>t\<guillemotright>) \<cdot> \<guillemotleft>t\<guillemotright>)"
        proof -
          have 1: "iso \<guillemotleft>t\<guillemotright>" using t iso_eval_Can by simp
          moreover have "iso (\<rho>' (cod \<guillemotleft>t\<guillemotright>))"
            using t 1 \<rho>'.components_are_iso ide_cod by blast
          moreover have "seq (\<rho>' (cod \<guillemotleft>t\<guillemotright>)) \<guillemotleft>t\<guillemotright>"
            using t 1 \<rho>'.preserves_dom \<rho>'.preserves_arr arr_cod_iff_arr dom_cod iso_is_arr map_simp
            by presburger
          ultimately show ?thesis
            using t 1 inv_comp \<rho>'.map_ide_simp inv_is_inverse inv_in_hom \<rho>.components_are_iso
            by simp
        qed
        also have "... = inv \<guillemotleft>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright>"
          using t \<rho>'.is_natural_2 iso_eval_Can by force
        finally show ?thesis by auto
      qed
      next
      fix t u v
      assume I1: "Can t \<Longrightarrow> \<guillemotleft>Inv t\<guillemotright> = inv \<guillemotleft>t\<guillemotright>"
      assume I2: "Can u \<Longrightarrow> \<guillemotleft>Inv u\<guillemotright> = inv \<guillemotleft>u\<guillemotright>"
      assume I3: "Can v \<Longrightarrow> \<guillemotleft>Inv v\<guillemotright> = inv \<guillemotleft>v\<guillemotright>"
      show "Can \<^bold>\<a>\<^bold>[t, u, v\<^bold>] \<Longrightarrow> \<guillemotleft>Inv \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright> = inv \<guillemotleft>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright>"
      proof -
        assume tuv: "Can \<^bold>\<a>\<^bold>[t, u, v\<^bold>]"
        have t: "Can t" using tuv by simp
        have u: "Can u" using tuv by simp
        have v: "Can v" using tuv by simp
        have "\<guillemotleft>Inv \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright> = \<guillemotleft>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Inv t, Inv u, Inv v\<^bold>]\<guillemotright>"by simp
        also have "... = \<a>\<^sup>-\<^sup>1[dom \<guillemotleft>t\<guillemotright>, dom \<guillemotleft>u\<guillemotright>, dom \<guillemotleft>v\<guillemotright>] \<cdot> (inv \<guillemotleft>t\<guillemotright> \<otimes> inv \<guillemotleft>u\<guillemotright> \<otimes> inv \<guillemotleft>v\<guillemotright>)"
          using t u v I1 I2 I3 eval_in_hom \<alpha>'_simp inv_in_hom iso_eval_Can assoc'_naturality
          by simp
        also have "... = inv ((\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright> \<otimes> \<guillemotleft>v\<guillemotright>) \<cdot> \<a>[dom \<guillemotleft>t\<guillemotright>, dom \<guillemotleft>u\<guillemotright>, dom \<guillemotleft>v\<guillemotright>])"
          using t u v I1 I2 I3 eval_in_hom iso_eval_Can inv_comp inv_tensor tensor_preserves_iso
                iso_assoc assoc_in_hom tensor_in_hom
          by force
        also have "... = inv (\<alpha> (\<guillemotleft>t\<guillemotright>, \<guillemotleft>u\<guillemotright>, \<guillemotleft>v\<guillemotright>))"
          using t u v Can_implies_Arr eval_in_hom \<alpha>_simp by force
        also have "... = inv \<guillemotleft>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright>" by simp
        finally show ?thesis by blast
      qed
      show "Can \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] \<Longrightarrow> \<guillemotleft>Inv \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright> = inv \<guillemotleft>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright>"
      proof -
        assume tuv: "Can \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
        have t: "Can t" using tuv by simp
        have u: "Can u" using tuv by simp
        have v: "Can v" using tuv by simp
        have "\<guillemotleft>Inv \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright> = \<guillemotleft>\<^bold>\<a>\<^bold>[Inv t, Inv u, Inv v\<^bold>]\<guillemotright>" by simp
        also have "... = (inv \<guillemotleft>t\<guillemotright> \<otimes> inv \<guillemotleft>u\<guillemotright> \<otimes> inv \<guillemotleft>v\<guillemotright>) \<cdot> \<a>[cod \<guillemotleft>t\<guillemotright>, cod \<guillemotleft>u\<guillemotright>, cod \<guillemotleft>v\<guillemotright>]"
          using t u v I1 I2 I3 Can_implies_Arr eval_in_hom \<alpha>_simp inv_in_hom iso_eval_Can
          by force
        also have "... = inv (\<a>\<^sup>-\<^sup>1[cod \<guillemotleft>t\<guillemotright>, cod \<guillemotleft>u\<guillemotright>, cod \<guillemotleft>v\<guillemotright>] \<cdot> (\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright> \<otimes> \<guillemotleft>v\<guillemotright>))"
          using t u v I1 I2 I3 Can_implies_Arr eval_in_hom iso_eval_Can iso_assoc iso_inv_iso
                Arr_implies_Ide_Cod ide_eval_Ide inv_inv assoc'_in_hom inv_comp
                tensor_preserves_iso inv_tensor tensor_in_hom
          by simp
        also have "... = inv (((\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>) \<otimes> \<guillemotleft>v\<guillemotright>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<guillemotleft>t\<guillemotright>, dom \<guillemotleft>u\<guillemotright>, dom \<guillemotleft>v\<guillemotright>])"
          using t u v Can_implies_Arr eval_in_hom \<alpha>'_simp assoc'_naturality [of "\<guillemotleft>t\<guillemotright>" "\<guillemotleft>u\<guillemotright>" "\<guillemotleft>v\<guillemotright>"]
                Arr_implies_Ide_Dom Arr_implies_Ide_Cod
          by simp
        also have "... = inv \<guillemotleft>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright>"
          using t u v Can_implies_Arr eval_in_hom \<alpha>'_simp Arr_implies_Ide_Dom Arr_implies_Ide_Cod
          by simp
        finally show ?thesis by blast
      qed
    qed

    text{*
      The operation @{text "\<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor>"} evaluates to composition in @{text D}.
    *}

    lemma eval_CompDiag:
    assumes "Diag t" and "Diag u" and "Seq t u"
    shows "\<guillemotleft>t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<guillemotright> = \<guillemotleft>t\<guillemotright> \<cdot> \<guillemotleft>u\<guillemotright>"
    proof -
      have "\<And>u. \<lbrakk> Diag t; Diag u; Seq t u \<rbrakk> \<Longrightarrow> \<guillemotleft>t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<guillemotright> = \<guillemotleft>t\<guillemotright> \<cdot> \<guillemotleft>u\<guillemotright>"
        using eval_in_hom
      proof (induct t, simp_all)
        fix u f
        assume u: "Diag u"
        assume f: "C.arr f"
        assume 1: "Arr u \<and> \<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod u"
        show "\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<guillemotright> = V f \<cdot> \<guillemotleft>u\<guillemotright>"
          using f u 1 preserves_comp_2 by (cases u; simp)
        next
        fix u v w
        assume I1: "\<And>u. \<lbrakk> Diag v; Diag u; Arr u \<and> Dom v = Cod u \<rbrakk> \<Longrightarrow>
                         \<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<guillemotright> = \<guillemotleft>v\<guillemotright> \<cdot> \<guillemotleft>u\<guillemotright>"
        assume I2: "\<And>u. \<lbrakk> Diag w; Diag u; Arr u \<and> Dom w = Cod u \<rbrakk> \<Longrightarrow>
                         \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<guillemotright> = \<guillemotleft>w\<guillemotright> \<cdot> \<guillemotleft>u\<guillemotright>"
        assume vw: "Diag (Tensor v w)"
        have v: "Diag v \<and> v = Prim (un_Prim v)"
          using vw by (simp add: Diag_TensorE)
        have w: "Diag w"
          using vw by (simp add: Diag_TensorE)
        assume u: "Diag u"
        assume 1: "Arr v \<and> Arr w \<and> Arr u \<and> Dom v \<^bold>\<otimes> Dom w = Cod u"
        show "\<guillemotleft>(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<guillemotright> = (\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w\<guillemotright>) \<cdot> \<guillemotleft>u\<guillemotright>"
          using u 1 eval_in_hom CompDiag_in_Hom
        proof (cases u, simp_all)
          fix x y
          assume 3: "u = x \<^bold>\<otimes> y"
          have x: "Diag x"
            using u 1 3 Diag_TensorE by simp
          have y: "Diag y"
            using u x 1 3 Diag_TensorE by simp
          assume 4: "Arr v \<and> Arr w \<and> Dom v = Cod x \<and> Dom w = Cod y"
          have "\<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<guillemotright> \<otimes> \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<guillemotright> = \<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x \<^bold>\<otimes> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<guillemotright>"
            using v w x y 4 CompDiag_in_Hom eval_in_hom by simp
          moreover have "... = T (\<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<guillemotright>, \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<guillemotright>)" by simp
          moreover have "... = T (\<guillemotleft>v\<guillemotright> \<cdot> \<guillemotleft>x\<guillemotright>, \<guillemotleft>w\<guillemotright> \<cdot> \<guillemotleft>y\<guillemotright>)"
            using v w x y 4 I1 [of x] I2 [of y] Diag_implies_Arr by simp
          moreover have "... = (\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w\<guillemotright>) \<cdot> (\<guillemotleft>x\<guillemotright> \<otimes> \<guillemotleft>y\<guillemotright>)"
            using v w x y 4 Diag_implies_Arr eval_in_hom interchange by simp
          ultimately have "\<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<guillemotright> \<otimes> \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<guillemotright> = (\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w\<guillemotright>) \<cdot> (\<guillemotleft>x\<guillemotright> \<otimes> \<guillemotleft>y\<guillemotright>)" by presburger
          moreover have "arr \<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<guillemotright> \<and> arr \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<guillemotright>"
            using v w x y 4 CompDiag_in_Hom eval_in_hom by simp
          ultimately show "tensor \<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<guillemotright> \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<guillemotright> = (\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w\<guillemotright>) \<cdot> (\<guillemotleft>x\<guillemotright> \<otimes> \<guillemotleft>y\<guillemotright>)"
            by simp
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text{*
      For identity terms @{term a} and @{term b}, the reduction @{term "(a \<^bold>\<otimes> b)\<^bold>\<down>"}
      factors (under evaluation in @{text D}) into the parallel reduction @{term "a\<^bold>\<down> \<^bold>\<otimes> b\<^bold>\<down>"},
      followed by a reduction of its codomain @{term "\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>"}.
    *}

    lemma eval_red_Tensor:
    assumes "Ide a" and "Ide b"
    shows "\<guillemotleft>(a \<^bold>\<otimes> b)\<^bold>\<down>\<guillemotright> = \<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<guillemotright> \<cdot> (\<guillemotleft>a\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>b\<^bold>\<down>\<guillemotright>)"
    proof -
      have "Diag (a \<^bold>\<otimes> b) \<Longrightarrow> ?thesis"
        using assms Can_red2 Ide_implies_Arr red_Diag
              Diagonalize_Diag red2_Diag Can_implies_Arr iso_eval_Can iso_is_arr
        apply simp
        using Diag_TensorE eval_Tensor Diagonalize_Diag Diag_implies_Arr red_Diag tensor_preserves_ide
              ide_eval_Ide dom_eval
        by (metis comp_arr_ide)
      moreover have "\<not> Diag (a \<^bold>\<otimes> b) \<Longrightarrow> ?thesis"
        using assms Can_red2 by (simp add: Can_red(1) iso_eval_Can)
      ultimately show ?thesis by blast
    qed

    lemma eval_red2_Diag_Unity:
    assumes "Ide a" and "Diag a"
    shows "\<guillemotleft>a \<^bold>\<Down> \<^bold>\<I>\<guillemotright> = \<r>[\<guillemotleft>a\<guillemotright>]"
      using assms tensor_preserves_ide
      apply (cases a)
               apply simp_all
    proof -
      show "\<And>f. C.ide f \<Longrightarrow> a = \<^bold>\<langle>f\<^bold>\<rangle> \<Longrightarrow> V f \<cdot> runit (V f) = \<r>[V f]"
        using preserves_ide runit_naturality
        by (metis ideD(1) ide_def V.preserves_ide \<rho>_ide_simp)
      show "a = \<^bold>\<I> \<Longrightarrow> \<I> \<cdot> lunit \<I> = \<r>[\<I>]"
        using preserves_ide runit_naturality unitor_coincidence \<rho>_ide_simp by simp
      show "\<And>b c. \<lbrakk> Ide b \<and> Ide c; Diag (b \<^bold>\<otimes> c) \<rbrakk> \<Longrightarrow>
                  (\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>) \<cdot> runit (\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>) = \<r>[\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>]"
      proof -
        fix b c
        assume bc: "Ide b \<and> Ide c"
        assume 1: "Diag (Tensor b c)"
        have b: "is_Prim b \<and> b = \<^bold>\<langle>un_Prim b\<^bold>\<rangle> \<and> C.ide (un_Prim b) \<and>
                 C.arr (un_Prim b) \<and> Diag b \<and> ide \<guillemotleft>b\<guillemotright> \<and> arr \<guillemotleft>b\<guillemotright>"
          using assms bc 1 ide_eval_Ide eval_in_hom V.preserves_arr Diag_TensorE
          by (metis (no_types, lifting) Ide.simps(1) term.disc(1) eval.simps(1))
        have c: "Ide c \<and> Arr c \<and> Diag c \<and> ide \<guillemotleft>c\<guillemotright> \<and> arr \<guillemotleft>c\<guillemotright>"
          using assms bc 1 ide_eval_Ide eval_in_hom Diag_implies_Arr Diag_TensorE
          by simp
        show "(\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>) \<cdot> runit (\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>) = \<r>[\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>]"
        proof -
          have "\<guillemotleft>(b \<^bold>\<otimes> c) \<^bold>\<Down> \<^bold>\<I>\<guillemotright> = \<r>[\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>]"
          proof -
            have "\<guillemotleft>(b \<^bold>\<otimes> c) \<^bold>\<Down> \<^bold>\<I>\<guillemotright> = \<guillemotleft>\<^bold>\<r>\<^bold>[b \<^bold>\<otimes> c\<^bold>]\<guillemotright>" by simp
            also have "... = (\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>) \<cdot> \<r>[\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>]"
              using b c bc 1 \<rho>_ide_simp red2_Diag tensor_preserves_ide by simp
            also have "... = \<r>[\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>]"
              using b c tensor_preserves_ide runit_in_hom by simp
            finally show ?thesis by blast
          qed
          thus "(\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>) \<cdot> runit (\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>) = \<r>[\<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>]"
            using b c ide_eval_Ide tensor_preserves_ide runit_in_hom by simp
        qed
      qed
    qed

    lemma eval_red_Tensor_Ide_Unity:
    assumes "Ide a"
    shows "\<guillemotleft>(a \<^bold>\<otimes> \<^bold>\<I>)\<^bold>\<down>\<guillemotright> = \<r>[\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright>] \<cdot> \<guillemotleft>a\<^bold>\<down> \<^bold>\<otimes> \<^bold>\<I>\<guillemotright>"
    proof -
      have "\<guillemotleft>(a \<^bold>\<otimes> \<^bold>\<I>)\<^bold>\<down>\<guillemotright> = \<guillemotleft>(\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<I>) \<^bold>\<cdot> (a\<^bold>\<down> \<^bold>\<otimes> \<^bold>\<I>)\<guillemotright>"
        by (cases a) simp_all
      also have "... = \<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<I>\<guillemotright> \<cdot> \<guillemotleft>a\<^bold>\<down> \<^bold>\<otimes> \<^bold>\<I>\<guillemotright>"
        by simp
      also have "... = \<r>[\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright>] \<cdot> \<guillemotleft>a\<^bold>\<down> \<^bold>\<otimes> \<^bold>\<I>\<guillemotright>"
        using assms eval_red2_Diag_Unity Diagonalize_preserves_Ide Diag_Diagonalize(1) by simp
      finally show ?thesis by blast
    qed

    text{*
      Define a formal arrow t to be ``coherent'' if the square formed by @{term t}, @{term "\<^bold>\<lfloor>t\<^bold>\<rfloor>"}
      and the reductions @{term "Dom t\<^bold>\<down>"} and @{term "Cod t\<^bold>\<down>"} commutes under evaluation
      in @{text D}.  We will show that all formal arrows are coherent.
      Since the diagonalizations of canonical arrows are identities, a corollary is that parallel
      canonical arrow have equal evaluations.
    *}

    abbreviation coherent
    where "coherent t \<equiv> \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>t\<guillemotright> = \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright>"

    text{*
      Diagonal arrows are coherent, since for such arrows @{term t} the reductions
      @{term "Dom t\<^bold>\<down>"} and @{term "Cod t\<^bold>\<down>"} are identities.
    *}

    lemma Diag_implies_coherent:
    assumes "Diag t"
    shows "coherent t"
      using assms dom_eval cod_eval Diag_implies_Arr Arr_implies_Ide_Dom Arr_implies_Ide_Cod
            Dom_preserves_Diag Cod_preserves_Diag Diagonalize_Diag red_Diag
      by simp

    text{*
      The evaluation of a coherent arrow @{term t} has a canonical factorization in @{text D}
      into the evaluations of a reduction @{term "Dom t\<^bold>\<down>"}, diagonalization @{term "\<^bold>\<lfloor>t\<^bold>\<rfloor>"},
      and inverse reduction @{term "Inv (Cod t\<^bold>\<down>)"}.
      This will later allow us to use the term @{term "Inv (Cod t\<^bold>\<down>) \<^bold>\<cdot> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<cdot> Dom t\<^bold>\<down>"}
      as a normal form for @{term t}.
    *}

    lemma canonical_factorization:
    assumes "Arr t"
    shows "coherent t \<longleftrightarrow> \<guillemotleft>t\<guillemotright> = inv \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright>"
    proof
      assume 1: "coherent t"
      have "inv \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright> = inv \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>t\<guillemotright>"
        using 1 by simp
      also have "... = (inv \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright>) \<cdot> \<guillemotleft>t\<guillemotright>"
        using assms 1 eval_in_hom red_in_Hom inv_in_hom Arr_implies_Ide_Cod comp_assoc
                    Can_red iso_eval_Can
        by simp
      also have "... = \<guillemotleft>t\<guillemotright>"
        using assms 1 eval_in_hom red_in_Hom inv_in_hom Arr_implies_Ide_Cod comp_assoc
              Can_red iso_eval_Can comp_cod_arr [of "\<guillemotleft>t\<guillemotright>"]
              Ide_in_Hom inv_is_inverse [of "\<guillemotleft>Cod t\<^bold>\<down>\<guillemotright>"]
        by (simp add: comp_inv_arr)
      finally show "\<guillemotleft>t\<guillemotright> = inv \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright>" by presburger
      next
      assume 1: "\<guillemotleft>t\<guillemotright> = inv \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright>"
      hence "\<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>t\<guillemotright> = \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> inv \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright>" by simp
      also have "... = (\<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> inv \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright>) \<cdot> \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright>"
        using assms eval_in_hom red_in_Hom inv_in_hom Arr_implies_Ide_Cod comp_assoc
              Can_red iso_eval_Can Diagonalize_in_Hom Arr_implies_Ide_Dom
        by simp
      also have "... = \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright>"
      proof -
        have "\<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> inv \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> = cod \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright>"
          using assms 1 eval_in_hom red_in_Hom inv_in_hom Arr_implies_Ide_Cod
              Can_red iso_eval_Can inv_is_inverse [of "\<guillemotleft>red (Cod t)\<guillemotright>"]
              Diagonalize_in_Hom inverse_arrowsD(3) comp_arr_inv
          by simp
        thus ?thesis
          using assms 1 eval_in_hom red_in_Hom inv_in_hom Arr_implies_Ide_Cod
                Can_red iso_eval_Can comp_cod_arr [of "\<guillemotleft>t\<guillemotright>"] Arr_implies_Ide_Dom
                inv_is_inverse [of "\<guillemotleft>red (Cod t)\<guillemotright>"] Diagonalize_in_Hom
          by auto
      qed
      finally show "coherent t" by blast
    qed

    text{*
      A canonical arrow is coherent if and only if its formal inverse is.
    *}

    lemma Can_implies_coherent_iff_coherent_Inv:
    assumes "Can t"
    shows "coherent t \<longleftrightarrow> coherent (Inv t)"
    proof
      have 1: "\<And>t. Can t \<Longrightarrow> coherent t \<Longrightarrow> coherent (Inv t)"
      proof -
        fix t
        assume "Can t"
        hence t: "Can t \<and> Arr t \<and> Ide (Dom t) \<and> Ide (Cod t) \<and>
                  arr \<guillemotleft>t\<guillemotright> \<and> iso \<guillemotleft>t\<guillemotright> \<and> inverse_arrows \<guillemotleft>t\<guillemotright> (inv \<guillemotleft>t\<guillemotright>) \<and>
                  Can \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Arr \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> arr \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<and> iso \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<and> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<in> Hom \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<and>
                  inverse_arrows \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> (inv \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright>) \<and> Inv t \<in> Hom (Cod t) (Dom t)"
          using assms Can_implies_Arr Arr_implies_Ide_Dom Arr_implies_Ide_Cod
                eval_in_hom iso_eval_Can inv_is_inverse Diagonalize_in_Hom
                Diagonalize_preserves_Can Inv_in_Hom
          by simp
        assume coh: "coherent t"
        have "\<guillemotleft>Cod (Inv t)\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>Inv t\<guillemotright> = (inv \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright>) \<cdot> \<guillemotleft>Cod (Inv t)\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>Inv t\<guillemotright>"
          using t coh eval_in_hom red_in_Hom comp_cod_arr [of "\<guillemotleft>Cod (Inv t)\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>Inv t\<guillemotright>"]
                Can_implies_Arr Can_red(1) Inv_preserves_Can(1) Inv_preserves_Can(3)
                canonical_factorization comp_inv_arr iso_eval_Can iso_is_arr
          by auto
        also have "... = inv \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Cod (Inv t)\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>Inv t\<guillemotright>"
          using t eval_in_hom red_in_Hom inv_in_hom by auto
        also have "... = inv \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright> \<cdot> inv \<guillemotleft>t\<guillemotright>"
          using t by (simp add: eval_Inv_Can)
        also have "... = inv \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> (\<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom t\<^bold>\<down>\<guillemotright>) \<cdot> inv \<guillemotleft>t\<guillemotright>"
          using t red_in_Hom
          by (metis (no_types, lifting) comp_assoc' comp_null(2) match_1 match_2)
        also have "... = inv \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> (\<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>t\<guillemotright>) \<cdot> inv \<guillemotleft>t\<guillemotright>"
          using t coh by simp
        also have "... = inv \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>t\<guillemotright> \<cdot> inv \<guillemotleft>t\<guillemotright>"
          (*
           * TODO: Very simple example of comp_assoc issue.  The proof that sledgehammer
           * finds uses comp_assoc' and works down from the composites not being null.
           * Maybe this could be made more automatic somehow.
           *)
          using t red_in_Hom
          by (metis (no_types, lifting) comp_assoc' comp_null(2) match_1 match_2)
        also have "... = inv \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom (Inv t)\<^bold>\<down>\<guillemotright>"
          using t comp_arr_inv red_in_Hom dom_eval cod_eval by auto
        also have "... = \<guillemotleft>\<^bold>\<lfloor>Inv t\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom (Inv t)\<^bold>\<down>\<guillemotright>"
          using t Diagonalize_Inv eval_Inv_Can by (metis (no_types, lifting))
        finally show "coherent (Inv t)" by blast
      qed
      show "coherent t \<Longrightarrow> coherent (Inv t)" using assms 1 by simp
      show "coherent (Inv t) \<Longrightarrow> coherent t"
      proof -
        assume "coherent (Inv t)"
        hence "coherent (Inv (Inv t))"
          using assms 1 Inv_preserves_Can by blast
        thus ?thesis using assms by simp
      qed
    qed

    text{*
      Some special cases of coherence are readily dispatched.
    *}

    lemma coherent_Unity:
    shows "coherent \<^bold>\<I>"
      by simp

    lemma coherent_Prim:
    assumes "Arr (Prim f)"
    shows "coherent \<^bold>\<langle>f\<^bold>\<rangle>"
      using assms by simp

    lemma coherent_Lunit_Ide:
    assumes "Ide a"
    shows "coherent \<^bold>\<l>\<^bold>[a\<^bold>]"
    proof -
      have a: "Ide a \<and> Arr a \<and> Dom a = a \<and> Cod a = a \<and>
               ide \<guillemotleft>a\<guillemotright> \<and> ide \<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright> \<and> \<guillemotleft>a\<^bold>\<down>\<guillemotright> \<in> hom \<guillemotleft>a\<guillemotright> \<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide
              red_in_Hom eval_in_hom
        by simp
      thus ?thesis
        using a lunit_in_hom eval_Lunit lunit_naturality [of "\<guillemotleft>a\<^bold>\<down>\<guillemotright>"]
              comp_cod_arr [of "\<l>[\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright>]"] comp_assoc tensor_in_hom
        by simp
    qed
      
    lemma coherent_Runit_Ide:
    assumes "Ide a"
    shows "coherent (Runit a)"
    proof -
      have a: "Ide a \<and> Arr a \<and> Dom a = a \<and> Cod a = a \<and>
               ide \<guillemotleft>a\<guillemotright> \<and> ide \<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright> \<and> \<guillemotleft>a\<^bold>\<down>\<guillemotright> \<in> hom \<guillemotleft>a\<guillemotright> \<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide
              red_in_Hom eval_in_hom
        by simp
      have "\<guillemotleft>Cod \<^bold>\<r>\<^bold>[a\<^bold>]\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<r>\<^bold>[a\<^bold>]\<guillemotright> = \<guillemotleft>a\<^bold>\<down>\<guillemotright> \<cdot> \<r>[\<guillemotleft>a\<guillemotright>]"
        using a runit_in_hom by simp
      also have "... = \<r>[\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright>] \<cdot> (\<guillemotleft>a\<^bold>\<down>\<guillemotright> \<otimes> \<I>)"
        using a eval_Runit runit_naturality [of "\<guillemotleft>red a\<guillemotright>"] runit_in_hom by simp
      also have "... = \<guillemotleft>\<^bold>\<lfloor>\<^bold>\<r>\<^bold>[a\<^bold>]\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom \<^bold>\<r>\<^bold>[a\<^bold>]\<^bold>\<down>\<guillemotright>"
      proof -
        have "\<not> Diag (a \<^bold>\<otimes> \<^bold>\<I>)" by (cases a; simp)
        thus ?thesis
          using a runit_in_hom comp_cod_arr [of "\<r>[\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright>]"] comp_assoc tensor_in_hom
                red2_in_Hom eval_in_hom eval_red2_Diag_Unity
                Diag_Diagonalize [of a] Diagonalize_preserves_Ide
          by simp
      qed
      finally show ?thesis by blast
    qed

    lemma coherent_Lunit'_Ide:
    assumes "Ide a"
    shows "coherent \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]"
      using assms Ide_implies_Can coherent_Lunit_Ide
            Can_implies_coherent_iff_coherent_Inv [of "Lunit a"] by simp

    lemma coherent_Runit'_Ide:
    assumes "Ide a"
    shows "coherent \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]"
      using assms Ide_implies_Can coherent_Runit_Ide
            Can_implies_coherent_iff_coherent_Inv [of "Runit a"] by simp

    text{*
      To go further, we need the next result, which is in some sense the crux of coherence:
      For diagonal identities @{term a}, @{term b}, and @{term c},
      the reduction @{term "((a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c) \<^bold>\<cdot> ((a \<^bold>\<Down> b) \<^bold>\<otimes> c)"} from @{term "(a \<^bold>\<otimes> b) \<^bold>\<otimes> c"}
      that first reduces the subterm @{term "a \<^bold>\<otimes> b"} and then reduces the result,
      is equivalent under evaluation in @{text D} to the reduction that first
      applies the associator @{term "\<^bold>\<a>\<^bold>[a, b, c\<^bold>]"} and then applies the reduction
      @{term "(a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (a \<^bold>\<otimes> (b \<^bold>\<Down> c))"} from @{term "a \<^bold>\<otimes> (b \<^bold>\<otimes> c)"}.
      The triangle and pentagon axioms are used in the proof.
    *}

    lemma coherence_key_fact:
    assumes "Ide a \<and> Diag a" and "Ide b \<and> Diag b" and "Ide c \<and> Diag c"
    shows "\<guillemotleft>(a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>a \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
             = (\<guillemotleft>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright> \<cdot> (\<guillemotleft>a\<guillemotright> \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot> \<a>[\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
    proof -
      have "b = \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms TensorDiag_preserves_Diag TensorDiag_preserves_Ide
              Diag_implies_Arr eval_in_hom lunit_in_hom tensor_preserves_ide
              TensorDiag_preserves_Ide not_is_Tensor_TensorDiagE
              preserves_ide eval_red2_Diag_Unity red2_in_Hom assoc_in_hom
              tensor_in_hom ide_eval_Ide triangle
        by simp
        text {* The triangle is used! *}
      moreover have "c = \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms TensorDiag_preserves_Diag TensorDiag_preserves_Ide
              Diag_implies_Arr eval_in_hom lunit_in_hom tensor_preserves_ide
              TensorDiag_preserves_Ide not_is_Tensor_TensorDiagE
              preserves_ide eval_red2_Diag_Unity red2_in_Hom runit_in_hom
              assoc_in_hom tensor_in_hom runit_tensor runit_naturality [of "\<guillemotleft>a \<^bold>\<Down> b\<guillemotright>"]
        by simp
      moreover have "\<lbrakk> b \<noteq> \<^bold>\<I>; c \<noteq> \<^bold>\<I> \<rbrakk> \<Longrightarrow> ?thesis"
      proof -
        assume b': "b \<noteq> \<^bold>\<I>"
        hence b: "Ide b \<and> Diag b \<and> Arr b \<and> b \<noteq> \<^bold>\<I> \<and>
                  ide \<guillemotleft>b\<guillemotright> \<and> arr \<guillemotleft>b\<guillemotright> \<and> \<^bold>\<lfloor>b\<^bold>\<rfloor> = b \<and> red b = b \<and> Dom b = b \<and> Cod b = b"
          using assms Diagonalize_preserves_Ide Ide_in_Hom by simp
        assume c': "c \<noteq> \<^bold>\<I>"
        hence c: "Ide c \<and> Diag c \<and> Arr c \<and> c \<noteq> \<^bold>\<I> \<and>
                  ide \<guillemotleft>c\<guillemotright> \<and> arr \<guillemotleft>c\<guillemotright> \<and> \<^bold>\<lfloor>c\<^bold>\<rfloor> = c \<and> red c = c \<and> Dom c = c \<and> Cod c = c"
          using assms Diagonalize_preserves_Ide Ide_in_Hom by simp
        have "\<And>a. Ide a \<and> Diag a \<Longrightarrow>
                   \<guillemotleft>(a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>a \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
                      = (\<guillemotleft>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright> \<cdot> (\<guillemotleft>a\<guillemotright> \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot> \<a>[\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
        proof -
          fix a :: "'c term"
          show "Ide a \<and> Diag a \<Longrightarrow>
                \<guillemotleft>(a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>a \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
                   = (\<guillemotleft>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright> \<cdot> (\<guillemotleft>a\<guillemotright> \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot> \<a>[\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
            apply (induct a)
            using b c TensorDiag_in_Hom eval_in_hom apply simp_all
          proof -
            show "\<guillemotleft>b \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>b\<guillemotright> \<cdot> lunit \<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
                    = ((\<guillemotleft>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright> \<cdot> lunit (\<guillemotleft>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>)) \<cdot> (\<I> \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot> \<a>[\<I>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
              using b c red2_in_Hom TensorDiag_in_Hom
                    lunit_in_hom assoc_in_hom assoc'_in_hom tensor_in_hom
                    lunit_naturality [of "\<guillemotleft>b \<^bold>\<Down> c\<guillemotright>"] lunit_tensor comp_assoc_assoc'
                    TensorDiag_preserves_Ide tensor_preserves_ide
              by (simp add: Can_red2(1) iso_eval_Can tensor_preserves_ide dom_eval cod_eval)
            show "\<And>f. C.ide f \<and> C.arr f \<Longrightarrow>
                       \<guillemotleft>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
                         = (\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright> \<cdot> (V f \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot> \<a>[V f, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
            proof -
              fix f
              assume f: "C.ide f \<and> C.arr f"
              show "\<guillemotleft>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
                      = (\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright> \<cdot> (V f \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot> \<a>[V f, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
              proof -
                have "\<guillemotleft>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
                                   = ((V f \<otimes> \<guillemotleft>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>) \<cdot> (V f \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>) \<cdot> \<a>[V f, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]) \<cdot>
                                     ((V f \<otimes> \<guillemotleft>b\<guillemotright>) \<otimes> \<guillemotleft>c\<guillemotright>)"
                proof -
                  have "(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b) \<^bold>\<Down> c = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> (b \<^bold>\<Down> c)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, b, c\<^bold>]"
                    using b c by (cases c) simp_all
                  also have "... = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> (b \<^bold>\<Down> c)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, b, c\<^bold>]"
                    using b c TensorDiag_Prim not_is_Tensor_TensorDiagE TensorDiag_preserves_Diag
                    apply (cases "TensorDiag b c") apply simp_all by blast
                  finally have "(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b) \<^bold>\<Down> c = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> (b \<^bold>\<Down> c)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, b, c\<^bold>]"
                    by blast
                  hence "\<guillemotleft>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b) \<^bold>\<Down> c\<guillemotright>
                           = (V f \<otimes> \<guillemotleft>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>) \<cdot> (V f \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>) \<cdot> \<a>[V f, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
                    using b c f red2_in_Hom TensorDiag_in_Hom eval_in_hom assoc_in_hom
                    by simp
                  moreover have "\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright> = (V f \<otimes> \<guillemotleft>b\<guillemotright>) \<otimes> \<guillemotleft>c\<guillemotright>"
                    using b c f red2_Diag [of "\<^bold>\<langle>f\<^bold>\<rangle>" b] by simp
                  ultimately show ?thesis by presburger
                qed
                also have "... = ((V f \<otimes> \<guillemotleft>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>) \<cdot> (V f \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot> \<a>[V f, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
                  using b c f TensorDiag_in_Hom red2_in_Hom tensor_in_hom eval_in_hom
                        preserves_arr assoc_in_hom
                  by simp
                also have "... = (\<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright> \<cdot> (V f \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot> \<a>[V f, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
                proof -
                  have "V f \<otimes> \<guillemotleft>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright> = \<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>"
                    using b c f Arr.simps(1) Ide_implies_Arr TensorDiag_preserves_Ide
                          ideD(1) eval_Prim eval_Tensor
                    by metis
                  also have "... = \<guillemotleft>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright>"
                    using b c TensorDiag_Prim TensorDiag_preserves_Diag
                          not_is_Tensor_TensorDiagE
                    by (cases "TensorDiag b c", simp_all; blast)
                  ultimately show ?thesis by presburger
                qed
                finally show ?thesis by blast
              qed
            qed
            fix d e
            assume I: "Diag e \<Longrightarrow> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>e \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
                                    = (\<guillemotleft>e \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright> \<cdot> (\<guillemotleft>e\<guillemotright> \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot> \<a>[\<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
            assume de: "Ide d \<and> Ide e \<and> Diag (d \<^bold>\<otimes> e)"
            show "\<guillemotleft>((d \<^bold>\<otimes> e) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>(d \<^bold>\<otimes> e) \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
                    = (\<guillemotleft>(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright> \<cdot> ((\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e\<guillemotright>) \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot>
                      \<a>[\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
            proof -
              let ?f = "un_Prim d"
              have "is_Prim d"
                using de Diag_TensorE by (cases d) simp_all
              hence "d = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.ide ?f"
                using de by (metis Ide.simps(1) term.collapse(1))
              hence d: "Ide d \<and> Arr d \<and> Dom d = d \<and> Cod d = d \<and> Diag d \<and>
                        d = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.ide ?f \<and> ide \<guillemotleft>d\<guillemotright> \<and> arr \<guillemotleft>d\<guillemotright>"
                using de ide_eval_Ide eval_in_hom Ide_implies_Arr Diag_Diagonalize(1) C.ide_def 
                by (metis (no_types, lifting) Cod.simps(1) Dom.simps(1) Diagonalize.simps(1)
                    ideD(1))
              have "Diag e \<and> e \<noteq> \<^bold>\<I>"
                using de Diag_TensorE by metis
              hence e: "Ide e \<and> Arr e \<and> Dom e = e \<and> Cod e = e \<and> Diag e \<and>
                        e \<noteq> \<^bold>\<I> \<and> ide \<guillemotleft>e\<guillemotright> \<and> arr \<guillemotleft>e\<guillemotright>"
                using de eval_in_hom Ide_in_Hom by simp
              have 1: "is_Tensor (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)"
                using e b de not_is_Tensor_TensorDiagE [of e b] by auto
              have 2: "is_Tensor (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)"
                using b c not_is_Tensor_TensorDiagE [of b c] by auto
              have 3: "is_Tensor (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))"
                using b c e 2 not_is_Tensor_TensorDiagE [of e "b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"]
                      TensorDiag_preserves_Diag
                by auto
              have "\<guillemotleft>((d \<^bold>\<otimes> e) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>(d \<^bold>\<otimes> e) \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)
                      = ((\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>) \<cdot> (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright>) \<cdot>
                         \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<guillemotright>, \<guillemotleft>c\<guillemotright>]) \<cdot>
                        ((\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<guillemotright>) \<cdot> (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<Down> b\<guillemotright>) \<cdot> \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>] \<otimes> \<guillemotleft>c\<guillemotright>)"
              proof -
                have "\<guillemotleft>((d \<^bold>\<otimes> e) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright>
                         = (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>) \<cdot> (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright>) \<cdot>
                           \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
                proof -
                  have "((d \<^bold>\<otimes> e) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c = (d \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)) \<^bold>\<Down> c"
                    using b c d e de 1 TensorDiag_Diag TensorDiag_preserves_Diag TensorDiag_assoc
                    by metis
                  also have "... = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)) \<^bold>\<Down> c"
                    using 1 d TensorDiag_Prim not_is_Tensor_Unity by metis
                  also have "... = (d \<^bold>\<Down> (\<^bold>\<lfloor>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (d \<^bold>\<otimes> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c)) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b, c\<^bold>]"
                    using c d 1 by (cases c) simp_all
                  also have "... = (d \<^bold>\<Down> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (d \<^bold>\<otimes> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c)) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b, c\<^bold>]"
                    using e b TensorDiag_preserves_Diag Diagonalize_Diag by simp
                  also have "... = (d \<^bold>\<otimes> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (d \<^bold>\<otimes> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c)) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b, c\<^bold>]"
                    using b c d e 3 TensorDiag_preserves_Diag red2_Diag TensorDiag_assoc
                    apply auto
                    by (metis Diag.simps(3) C.ideD(1) not_is_Tensor_Unity)
                  finally have "((d \<^bold>\<otimes> e) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c
                                  = (d \<^bold>\<otimes> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (d \<^bold>\<otimes> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c)) \<^bold>\<cdot>
                                    \<^bold>\<a>\<^bold>[d, e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b, c\<^bold>]"
                    by fast
                  thus ?thesis
                    using b c d e TensorDiag_in_Hom eval_in_hom red2_in_Hom
                          TensorDiag_preserves_Diag TensorDiag_preserves_Ide
                          assoc_in_hom
                    by simp
                qed
                moreover have "\<guillemotleft>(d \<^bold>\<otimes> e) \<^bold>\<Down> b\<guillemotright>
                                 = (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<guillemotright>) \<cdot> (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<Down> b\<guillemotright>) \<cdot> \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>]"
                proof -
                  have "(d \<^bold>\<otimes> e) \<^bold>\<Down> b = (d \<^bold>\<Down> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> b)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b\<^bold>]"
                      using b c d e de 1 TensorDiag_Prim Diagonalize_Diag
                      by (cases b) simp_all
                  also have "... = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> b)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b\<^bold>]"
                    using b c d e de 1 TensorDiag_Diag TensorDiag_preserves_Diag
                    apply simp
                    by (metis TensorDiag_Prim red2_Diag not_is_Tensor_Unity)
                  finally have "(d \<^bold>\<otimes> e) \<^bold>\<Down> b = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> b)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b\<^bold>]"
                    by simp
                  thus ?thesis using b d e eval_in_hom TensorDiag_in_Hom red2_in_Hom by simp
                qed
                ultimately show ?thesis by presburger
              qed
              also have "... = (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright>) \<cdot> \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<guillemotright>, \<guillemotleft>c\<guillemotright>] \<cdot>
                               ((\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<Down> b\<guillemotright>) \<otimes> \<guillemotleft>c\<guillemotright>) \<cdot> (\<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>] \<otimes> \<guillemotleft>c\<guillemotright>)"
                using b c d e TensorDiag_in_Hom red2_in_Hom tensor_in_hom
                      TensorDiag_preserves_Ide TensorDiag_preserves_Diag
                      eval_in_hom assoc_in_hom interchange
                by simp
              also have "... = (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright>) \<cdot> (\<guillemotleft>d\<guillemotright> \<otimes> (\<guillemotleft>e \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)) \<cdot>
                               \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright> \<otimes> \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>] \<cdot> (\<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>] \<otimes> \<guillemotleft>c\<guillemotright>)"
                using b c d e TensorDiag_in_Hom red2_in_Hom tensor_in_hom
                      TensorDiag_preserves_Ide TensorDiag_preserves_Diag
                      eval_in_hom assoc_in_hom assoc_naturality [of "\<guillemotleft>d\<guillemotright>" "\<guillemotleft>e \<^bold>\<Down> b\<guillemotright>" "\<guillemotleft>c\<guillemotright>"]
                      comp_permute [of "\<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<guillemotright>, \<guillemotleft>c\<guillemotright>]" "(\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<Down> b\<guillemotright>) \<otimes> \<guillemotleft>c\<guillemotright>"
                                       "\<guillemotleft>d\<guillemotright> \<otimes> (\<guillemotleft>e \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)" "\<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright> \<otimes> \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"]
                by simp
              also have "... = (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>e \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)) \<cdot>
                               \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright> \<otimes> \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>] \<cdot> (\<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>] \<otimes> \<guillemotleft>c\<guillemotright>)"
                using b c d e TensorDiag_in_Hom red2_in_Hom tensor_in_hom
                      TensorDiag_preserves_Ide TensorDiag_preserves_Diag
                      eval_in_hom assoc_in_hom interchange tensor_preserves_ide
                      comp_reduce [of "\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright>"
                                      "\<guillemotleft>d\<guillemotright> \<otimes> (\<guillemotleft>e \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)"
                                      "\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<guillemotright> \<cdot> (\<guillemotleft>e \<^bold>\<Down> b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>)"
                                      "\<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright> \<otimes> \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>] \<cdot> (\<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>] \<otimes> \<guillemotleft>c\<guillemotright>)"]
                 by simp
              also have "... = (((\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright>) \<cdot> (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e\<guillemotright> \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot>
                                (\<guillemotleft>d\<guillemotright> \<otimes> \<a>[\<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>])) \<cdot>
                               \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright> \<otimes> \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>] \<cdot> (\<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>] \<otimes> \<guillemotleft>c\<guillemotright>)"
                using b c d e I TensorDiag_in_Hom red2_in_Hom tensor_in_hom
                      TensorDiag_preserves_Ide TensorDiag_preserves_Diag
                      eval_in_hom assoc_in_hom interchange
                by simp
              also have "... = ((\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright>) \<cdot> (\<guillemotleft>d\<guillemotright> \<otimes> (\<guillemotleft>e\<guillemotright> \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>))) \<cdot>
                                 \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright> \<otimes> \<guillemotleft>c\<guillemotright>] \<cdot> \<a>[\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
                using b c d e comp_assoc assoc_in_hom red2_in_Hom eval_in_hom tensor_in_hom
                      TensorDiag_in_Hom ide_eval_Ide TensorDiag_preserves_Diag
                      tensor_preserves_ide TensorDiag_preserves_Ide pentagon
                by simp
              text {* The pentagon is used! *}
              also have "... = (((\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>) \<cdot> (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>) \<cdot>
                                 \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>]) \<cdot> ((\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e\<guillemotright>) \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot>
                               \<a>[\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
                using b c d e 2 TensorDiag_in_Hom red2_in_Hom tensor_in_hom
                      TensorDiag_preserves_Ide TensorDiag_preserves_Diag
                      eval_in_hom assoc_in_hom tensor_preserves_ide
                      assoc_naturality [of "\<guillemotleft>d\<guillemotright>" "\<guillemotleft>e\<guillemotright>" "\<guillemotleft>b \<^bold>\<Down> c\<guillemotright>"]
                by simp
              also have "... = (\<guillemotleft>(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright> \<cdot> ((\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e\<guillemotright>) \<otimes> \<guillemotleft>b \<^bold>\<Down> c\<guillemotright>)) \<cdot>
                               \<a>[\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
              proof -
                have "\<guillemotleft>(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright>
                           = (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright>) \<cdot> (\<guillemotleft>d\<guillemotright> \<otimes> \<guillemotleft>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<guillemotright>) \<cdot>
                              \<a>[\<guillemotleft>d\<guillemotright>, \<guillemotleft>e\<guillemotright>, \<guillemotleft>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<guillemotright>]"
                proof -
                  have "(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)
                          = (d \<^bold>\<Down> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>\<rfloor>)) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>]"
                    using b c e not_is_Tensor_TensorDiagE
                    by (cases "b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c") auto
                  also have "... = (d \<^bold>\<Down> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>]"
                    using b c d e 2 TensorDiag_preserves_Diag Diagonalize_Diag by simp
                  also have "... = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>]"
                    using b c d e 3
                    by (metis Diag.simps(3) TensorDiag_preserves_Diag(1) C.ideD(1)
                        red2_Diag not_is_Tensor_Unity)
                  finally have "(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)
                                  = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot>
                                    \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>]"
                    by blast
                  thus ?thesis
                    using b c d e red2_in_Hom TensorDiag_in_Hom eval_in_hom assoc_in_hom
                          TensorDiag_preserves_Diag TensorDiag_preserves_Ide
                    by simp
                qed
                thus ?thesis using d e b c by simp
              qed
              finally show ?thesis by simp
            qed
          qed
        qed
        thus ?thesis using assms(1) by blast
      qed
      ultimately show ?thesis by blast
    qed

    lemma coherent_Assoc_Ide:
    assumes "Ide a" and "Ide b" and "Ide c"
    shows "coherent \<^bold>\<a>\<^bold>[a, b, c\<^bold>]"
    proof -
      have a: "Ide a \<and> Arr a \<and> Dom a = a \<and> Cod a = a \<and>
               ide \<guillemotleft>a\<guillemotright> \<and> ide \<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright> \<and> \<guillemotleft>a\<^bold>\<down>\<guillemotright> \<in> hom \<guillemotleft>a\<guillemotright> \<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide
              red_in_Hom eval_in_hom
        by simp
      have b: "Ide b \<and> Arr b \<and> Dom b = b \<and> Cod b = b \<and>
               ide \<guillemotleft>b\<guillemotright> \<and> ide \<guillemotleft>\<^bold>\<lfloor>b\<^bold>\<rfloor>\<guillemotright> \<and> \<guillemotleft>b\<^bold>\<down>\<guillemotright> \<in> hom \<guillemotleft>b\<guillemotright> \<guillemotleft>\<^bold>\<lfloor>b\<^bold>\<rfloor>\<guillemotright>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide
              red_in_Hom eval_in_hom
        by simp
      have c: "Ide c \<and> Arr c \<and> Dom c = c \<and> Cod c = c \<and>
               ide \<guillemotleft>c\<guillemotright> \<and> ide \<guillemotleft>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<guillemotright> \<and> \<guillemotleft>c\<^bold>\<down>\<guillemotright> \<in> hom \<guillemotleft>c\<guillemotright> \<guillemotleft>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<guillemotright>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide
              red_in_Hom eval_in_hom
        by simp
      have "\<guillemotleft>Cod \<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<guillemotright>
              = (\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>)\<guillemotright> \<cdot> (\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright> \<otimes> (\<guillemotleft>\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<guillemotright>)) \<cdot>
                 (\<guillemotleft>a\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>b\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>c\<^bold>\<down>\<guillemotright>)) \<cdot> \<a>[\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>, \<guillemotleft>c\<guillemotright>]"
        using a b c red_in_Hom red2_in_Hom Diagonalize_in_Hom Diag_Diagonalize
              tensor_in_hom eval_in_hom Diagonalize_preserves_Ide interchange
              Ide_in_Hom eval_red_Tensor assoc_in_hom
        by auto
      also have "... = ((\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>)\<guillemotright> \<cdot> (\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright> \<otimes> \<guillemotleft>\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<guillemotright>)) \<cdot>
                        \<a>[\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<guillemotright>, \<guillemotleft>\<^bold>\<lfloor>b\<^bold>\<rfloor>\<guillemotright>, \<guillemotleft>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<guillemotright>]) \<cdot> ((\<guillemotleft>a\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>b\<^bold>\<down>\<guillemotright>) \<otimes> \<guillemotleft>c\<^bold>\<down>\<guillemotright>)"
        using a b c red_in_Hom red2_in_Hom Diagonalize_in_Hom Diag_Diagonalize
               tensor_in_hom assoc_in_hom eval_in_hom Diagonalize_preserves_Ide
               Ide_in_Hom TensorDiag_preserves_Diag Ide_implies_Arr
               TensorDiag_preserves_Ide assoc_naturality [of "\<guillemotleft>a\<^bold>\<down>\<guillemotright>" "\<guillemotleft>b\<^bold>\<down>\<guillemotright>" "\<guillemotleft>c\<^bold>\<down>\<guillemotright>"]
         by simp
      also have "... = (\<guillemotleft>(\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<guillemotright> \<cdot> (\<guillemotleft>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<guillemotright> \<otimes> \<guillemotleft>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<guillemotright>)) \<cdot>
                       ((\<guillemotleft>a\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>b\<^bold>\<down>\<guillemotright>) \<otimes> \<guillemotleft>c\<^bold>\<down>\<guillemotright>)"
        using a b c Diag_Diagonalize Diagonalize_preserves_Ide coherence_key_fact by simp
      also have "... = \<guillemotleft>\<^bold>\<lfloor>\<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom \<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<^bold>\<down>\<guillemotright>"
        using a b c red_in_Hom red2_in_Hom Diagonalize_in_Hom tensor_in_hom eval_in_hom
              TensorDiag_preserves_Diag Diagonalize_preserves_Ide TensorDiag_preserves_Ide
              Diag_Diagonalize interchange Ide_in_Hom eval_red_Tensor assoc_in_hom
              TensorDiag_assoc
        by simp
      finally show ?thesis by blast
    qed

    lemma coherent_Assoc'_Ide:
    assumes "Ide a" and "Ide b" and "Ide c"
    shows "coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[a, b, c\<^bold>]"
    proof -
      have "Can \<^bold>\<a>\<^bold>[a, b, c\<^bold>]" using assms Ide_implies_Can by simp
      moreover have "\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[a, b, c\<^bold>] = Inv \<^bold>\<a>\<^bold>[a, b, c\<^bold>]"
        using assms Inv_Ide by simp
      ultimately show ?thesis
        using assms Ide_implies_Can coherent_Assoc_Ide Inv_Ide
              Can_implies_coherent_iff_coherent_Inv
              (* TODO: simp loops here -- look into this. *)
        by metis
    qed

    text{*
      The next lemma implies coherence for the special case of a term that is the tensor
      of two diagonal arrows.
    *}

    lemma eval_red2_naturality:
    assumes "Diag t" and "Diag u"
    shows "\<guillemotleft>Cod t \<^bold>\<Down> Cod u\<guillemotright> \<cdot> (\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>) = \<guillemotleft>t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> \<cdot> \<guillemotleft>Dom t \<^bold>\<Down> Dom u\<guillemotright>"
    proof -
      have *: "\<And>t u. Diag (t \<^bold>\<otimes> u) \<Longrightarrow> arr \<guillemotleft>t\<guillemotright> \<and> arr \<guillemotleft>u\<guillemotright>"
        using Diag_implies_Arr Arr.simps(3) fst_map_prod snd_map_prod eval_in_hom by blast
      have "t = \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms Diag_implies_Arr lunit_in_hom lunit_naturality
              Arr_implies_Ide_Dom Arr_implies_Ide_Cod
        apply simp
        by (metis arr_cod_iff_arr cod_eval dom_eval ide_eval_Ide)
      moreover have "t \<noteq> \<^bold>\<I> \<and> u = \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod
              Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag
              eval_red2_Diag_Unity eval_in_hom runit_naturality [of "\<guillemotleft>t\<guillemotright>"]
        by simp
      moreover have "t \<noteq> \<^bold>\<I> \<and> u \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms * Arr_implies_Ide_Dom Arr_implies_Ide_Cod
              Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag
              eval_in_hom
        apply (induct t) apply simp_all
      proof -
        fix f
        assume f: "C.arr f"
        assume "u \<noteq> \<^bold>\<I>"
        hence u: "u \<noteq> \<^bold>\<I> \<and>
                  Diag u \<and> Diag (Dom u) \<and> Diag (Cod u) \<and> Ide (Dom u) \<and> Ide (Cod u) \<and>
                  arr \<guillemotleft>u\<guillemotright> \<and> arr \<guillemotleft>Dom u\<guillemotright> \<and> arr \<guillemotleft>Cod u\<guillemotright> \<and> ide \<guillemotleft>Dom u\<guillemotright> \<and> ide \<guillemotleft>Cod u\<guillemotright>"
          using assms(2) Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag
                Arr_implies_Ide_Dom Arr_implies_Ide_Cod ide_eval_Ide Ide_implies_Arr Ide_in_Hom
                eval_in_hom
          by simp
        hence 1: "Dom u \<noteq> \<^bold>\<I> \<and> Cod u \<noteq> \<^bold>\<I>" using u by (cases u) simp_all
        show "\<guillemotleft>\<^bold>\<langle>C.cod f\<^bold>\<rangle> \<^bold>\<Down> Cod u\<guillemotright> \<cdot> (V f \<otimes> \<guillemotleft>u\<guillemotright>) = (V f \<otimes> \<guillemotleft>u\<guillemotright>) \<cdot> \<guillemotleft>\<^bold>\<langle>C.dom f\<^bold>\<rangle> \<^bold>\<Down> Dom u\<guillemotright>"
          using f u 1 Diag_implies_Arr tensor_in_hom red2_Diag dom_eval cod_eval by simp
        next
        fix v w
        assume I2: "\<lbrakk> w \<noteq> Unity; Diag w \<rbrakk> \<Longrightarrow>
                      \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright> \<cdot> (\<guillemotleft>w\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>) = \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> \<cdot> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>"
        assume "u \<noteq> \<^bold>\<I>"
        hence u: "u \<noteq> \<^bold>\<I> \<and> Arr u \<and> Arr (Dom u) \<and> Arr (Cod u) \<and>
                  Diag u \<and> Diag (Dom u) \<and> Diag (Cod u) \<and> Ide (Dom u) \<and> Ide (Cod u) \<and>
                  arr \<guillemotleft>u\<guillemotright> \<and> arr \<guillemotleft>Dom u\<guillemotright> \<and> arr \<guillemotleft>Cod u\<guillemotright> \<and> ide \<guillemotleft>Dom u\<guillemotright> \<and> ide \<guillemotleft>Cod u\<guillemotright>"
          using assms(2) Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag
                Arr_implies_Ide_Dom Arr_implies_Ide_Cod ide_eval_Ide Ide_implies_Arr Ide_in_Hom
                eval_in_hom
          by simp
        assume vw: "Diag (v \<^bold>\<otimes> w)"
        let ?f = "un_Prim v"
        have "v = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.arr ?f"
          using vw by (metis Diag_TensorE(1) Diag_TensorE(2))
        hence "Arr v \<and> v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> C.arr ?f \<and> Diag v" by (cases v; simp)
        hence v: "v = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.arr ?f \<and> Arr v \<and> Arr (Dom v) \<and> Arr (Cod v) \<and> Diag v \<and>
                  arr \<guillemotleft>v\<guillemotright> \<and> arr \<guillemotleft>Dom v\<guillemotright> \<and> arr \<guillemotleft>Cod v\<guillemotright> \<and> ide \<guillemotleft>Dom v\<guillemotright> \<and> ide \<guillemotleft>Cod v\<guillemotright>"
          using vw * Arr_implies_Ide_Dom Arr_implies_Ide_Cod
          by (cases v) simp_all
        have "Diag w \<and> w \<noteq> \<^bold>\<I>"
          using vw v by (metis Diag.simps(3))
        hence w: "w \<noteq> \<^bold>\<I> \<and> Arr w \<and> Arr (Dom w) \<and> Arr (Cod w) \<and>
                  Diag w \<and> Diag (Dom w) \<and> Diag (Cod w) \<and>
                  Ide (Dom w) \<and> Ide (Cod w) \<and>
                  arr \<guillemotleft>w\<guillemotright> \<and> arr \<guillemotleft>Dom w\<guillemotright> \<and> arr \<guillemotleft>Cod w\<guillemotright> \<and> ide \<guillemotleft>Dom w\<guillemotright> \<and> ide \<guillemotleft>Cod w\<guillemotright>"
          using vw * Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag
                Arr_implies_Ide_Dom Arr_implies_Ide_Cod ide_eval_Ide Ide_implies_Arr Ide_in_Hom
                eval_in_hom
          by simp
        show "\<guillemotleft>(Cod v \<^bold>\<otimes> Cod w) \<^bold>\<Down> Cod u\<guillemotright> \<cdot> ((\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w\<guillemotright>) \<otimes> \<guillemotleft>u\<guillemotright>)
                = \<guillemotleft>(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> \<cdot> \<guillemotleft>(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u\<guillemotright>"
        proof -
          have u': "Dom u \<noteq> \<^bold>\<I> \<and> Cod u \<noteq> \<^bold>\<I>" using u by (cases u) simp_all
          have w':  "Dom w \<noteq> \<^bold>\<I> \<and> Cod w \<noteq> \<^bold>\<I>" using w by (cases w) simp_all
          have "\<guillemotleft>(Cod v \<^bold>\<otimes> Cod w) \<^bold>\<Down> Cod u\<guillemotright> \<cdot> ((\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w\<guillemotright>) \<otimes> \<guillemotleft>u\<guillemotright>)
                  = (\<guillemotleft>Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)\<guillemotright> \<cdot> (\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>) \<cdot>
                    \<a>[\<guillemotleft>Cod v\<guillemotright>, \<guillemotleft>Cod w\<guillemotright>, \<guillemotleft>Cod u\<guillemotright>]) \<cdot> ((\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w\<guillemotright>) \<otimes> \<guillemotleft>u\<guillemotright>)"
          proof -
            have "(Cod v \<^bold>\<otimes> Cod w) \<^bold>\<Down> Cod u
                    = (Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>)) \<^bold>\<cdot> (Cod v \<^bold>\<otimes> Cod w \<^bold>\<Down> Cod u) \<^bold>\<cdot>
                      \<^bold>\<a>\<^bold>[Cod v, Cod w, Cod u\<^bold>]"
              using u v w Diagonalize_Diag TensorDiag_Diag Diag_Diagonalize
              by (cases u) simp_all
            hence "\<guillemotleft>(Cod v \<^bold>\<otimes> Cod w) \<^bold>\<Down> Cod u\<guillemotright>
                     = \<guillemotleft>Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)\<guillemotright> \<cdot> (\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>) \<cdot>
                       \<a>[\<guillemotleft>Cod v\<guillemotright>, \<guillemotleft>Cod w\<guillemotright>, \<guillemotleft>Cod u\<guillemotright>]"
              using u v w eval_in_hom red2_in_Hom assoc_in_hom by simp
            thus ?thesis by presburger
          qed
          also have "... = ((\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<guillemotright>) \<cdot> (\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>) \<cdot>
                            \<a>[\<guillemotleft>Cod v\<guillemotright>, \<guillemotleft>Cod w\<guillemotright>, \<guillemotleft>Cod u\<guillemotright>]) \<cdot> ((\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w\<guillemotright>) \<otimes> \<guillemotleft>u\<guillemotright>)"
          proof -
            have "\<guillemotleft>Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)\<guillemotright> = \<guillemotleft>Cod v \<^bold>\<otimes> Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<guillemotright>"
            proof -
              have "Diag (Cod v \<^bold>\<otimes> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u))"
              proof -
                have "Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u \<noteq> \<^bold>\<I>"
                proof -
                  have "is_Tensor (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)"
                  proof -
                    have "Cod w \<noteq> \<^bold>\<I>" using w by (cases w) simp_all
                    thus ?thesis
                      using u u' w Cod_preserves_Diag
                            not_is_Tensor_TensorDiagE [of "Cod w" "Cod u"]
                      by blast
                  qed
                  thus ?thesis by auto
                qed
                moreover have "Diag (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)"
                  using u w TensorDiag_preserves_Diag by simp
                moreover have "Cod v = \<^bold>\<langle>C.cod ?f\<^bold>\<rangle>"
                  using v by (metis Cod.simps(1))
                ultimately show ?thesis
                  using u v w by (cases "Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u") simp_all
              qed
              thus ?thesis using red2_Diag by presburger
            qed
            also have "... = \<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<guillemotright>"
              using assms u v w TensorDiag_in_Hom eval_in_hom by simp
            finally have "\<guillemotleft>Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)\<guillemotright> = \<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<guillemotright>"
              by blast
            thus ?thesis by presburger
          qed
          also have "... = ((\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>) \<cdot> \<a>[\<guillemotleft>Cod v\<guillemotright>, \<guillemotleft>Cod w\<guillemotright>, \<guillemotleft>Cod u\<guillemotright>]) \<cdot>
                           ((\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w\<guillemotright>) \<otimes> \<guillemotleft>u\<guillemotright>)"
          proof -
            have "(\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<guillemotright>) \<cdot> (\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>)
                     = \<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>"
              using u v w Diagonalize_Diag eval_in_hom TensorDiag_preserves_Diag red2_Diag
                    comp_cod_arr [of "\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>"] red2_in_Hom tensor_in_hom
              by fastforce
            moreover have
                "seq (\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<guillemotright>) (\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>)"
              using u v w eval_in_hom red2_in_Hom TensorDiag_in_Hom tensor_in_hom Ide_in_Hom
              by simp
            moreover have "seq (\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>) \<a>[\<guillemotleft>Cod v\<guillemotright>, \<guillemotleft>Cod w\<guillemotright>, \<guillemotleft>Cod u\<guillemotright>]"
              using u v w eval_in_hom red2_in_Hom assoc_in_hom tensor_in_hom by simp
            ultimately show ?thesis
              using u v w
                    comp_reduce [of "\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<guillemotright>"
                                    "\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>"
                                    "\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright>"
                                    "\<a>[\<guillemotleft>Cod v\<guillemotright>, \<guillemotleft>Cod w\<guillemotright>, \<guillemotleft>Cod u\<guillemotright>]"]
              by presburger
          qed
          also have
            "... = (\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> \<cdot> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>) \<cdot> \<a>[\<guillemotleft>Dom v\<guillemotright>, \<guillemotleft>Dom w\<guillemotright>, \<guillemotleft>Dom u\<guillemotright>]"
            using u v w I2 eval_in_hom red2_in_Hom TensorDiag_in_Hom
                  assoc_in_hom tensor_in_hom Ide_in_Hom comp_assoc
                  Diag_implies_Arr interchange
                  comp_reduce [of "\<guillemotleft>Cod v\<guillemotright> \<otimes> \<guillemotleft>red2 (Cod w) (Cod u)\<guillemotright>"
                                  "(\<guillemotleft>v\<guillemotright> \<otimes> (\<guillemotleft>w\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>))"
                                  "\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>Cod w \<^bold>\<Down> Cod u\<guillemotright> \<cdot> (\<guillemotleft>w\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>)"
                                  "\<a>[\<guillemotleft>Dom v\<guillemotright>, \<guillemotleft>Dom w\<guillemotright>, \<guillemotleft>Dom u\<guillemotright>]"]
                  assoc_naturality [of "\<guillemotleft>v\<guillemotright>" "\<guillemotleft>w\<guillemotright>" "\<guillemotleft>u\<guillemotright>"]
            by simp
          also have "... = (\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright>) \<cdot> (\<guillemotleft>Dom v\<guillemotright> \<otimes> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>) \<cdot>
                           \<a>[\<guillemotleft>Dom v\<guillemotright>, \<guillemotleft>Dom w\<guillemotright>, \<guillemotleft>Dom u\<guillemotright>]"
            using u v w eval_in_hom red2_in_Hom TensorDiag_in_Hom
                  assoc_in_hom tensor_in_hom Ide_in_Hom comp_assoc
                  Diag_implies_Arr interchange
                  comp_reduce [of "\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright>"
                                  "\<guillemotleft>Dom v\<guillemotright> \<otimes> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>"
                                  "\<guillemotleft>v\<guillemotright> \<otimes> \<guillemotleft>w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> \<cdot> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>"
                                  "\<a>[\<guillemotleft>Dom v\<guillemotright>, \<guillemotleft>Dom w\<guillemotright>, \<guillemotleft>Dom u\<guillemotright>]"]
            by simp
          also have "... = \<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> \<cdot> (\<guillemotleft>Dom v\<guillemotright> \<otimes> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>) \<cdot>
                           \<a>[\<guillemotleft>Dom v\<guillemotright>, \<guillemotleft>Dom w\<guillemotright>, \<guillemotleft>Dom u\<guillemotright>]"
            using u u' v w not_is_Tensor_TensorDiagE [of "w" "u"]
                  TensorDiag_Prim [of "w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u" ?f] eval_in_hom TensorDiag_in_Hom
            by fastforce
          also have "... = \<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> \<cdot> \<guillemotleft>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<guillemotright> \<cdot>
                          (\<guillemotleft>Dom v\<guillemotright> \<otimes> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>) \<cdot> \<a>[\<guillemotleft>Dom v\<guillemotright>, \<guillemotleft>Dom w\<guillemotright>, \<guillemotleft>Dom u\<guillemotright>]"
          proof -
            have "\<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> = \<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> \<cdot> \<guillemotleft>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<guillemotright>"
              using u v w eval_in_hom comp_arr_dom [of "\<guillemotleft>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright>"]
                    TensorDiag_in_Hom [of w u] TensorDiag_preserves_Diag
                    TensorDiag_in_Hom [of v "w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u"]
                    Arr_implies_Ide_Dom Diag_implies_Arr dom_eval ide_eval_Ide
              by (metis (no_types, lifting) arr_dom_iff_arr ideD(1))
            thus ?thesis
              (*
               * Here metis is apparently able to split cases based on whether the
               * left-hand side is null or not null.  If it is null, then the result
               * follows trivially.  If it is not null, then comp_assoc' can be used,
               * as it relies on the hypothesis that the compositions are non-null.
               *)
              by (metis comp_assoc' comp_null(2) match_1 comp_null(1))
          qed
          also have "... = \<guillemotleft>(v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<guillemotright> \<cdot> \<guillemotleft>(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u\<guillemotright>"
          proof -
            have "(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u
                     = (Dom v \<^bold>\<Down> (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>)) \<^bold>\<cdot> (Dom v \<^bold>\<otimes> (Dom w \<^bold>\<Down> Dom u)) \<^bold>\<cdot>
                       \<^bold>\<a>\<^bold>[Dom v, Dom w, Dom u\<^bold>]"
              using u u' v w red2_in_Hom TensorDiag_in_Hom tensor_in_hom Ide_in_Hom
              by (cases u) simp_all
            hence
              "\<guillemotleft>(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u\<guillemotright>
                     = \<guillemotleft>Dom v \<^bold>\<Down> (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u)\<guillemotright> \<cdot> (\<guillemotleft>Dom v\<guillemotright> \<otimes> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>) \<cdot>
                       \<a>[\<guillemotleft>Dom v\<guillemotright>, \<guillemotleft>Dom w\<guillemotright>, \<guillemotleft>Dom u\<guillemotright>]"
              using u v w assoc_in_hom eval_in_hom red2_in_Hom by simp
            also have
              "... = \<guillemotleft>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<guillemotright> \<cdot> (\<guillemotleft>Dom v\<guillemotright> \<otimes> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>) \<cdot>
                             \<a>[\<guillemotleft>Dom v\<guillemotright>, \<guillemotleft>Dom w\<guillemotright>, \<guillemotleft>Dom u\<guillemotright>]"
            proof -
              have "Diag (Dom v \<^bold>\<otimes> (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u))"
              proof -
                have "Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<noteq> \<^bold>\<I>"
                proof -
                  have "is_Tensor (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u)"
                    using u u' w w' not_is_Tensor_TensorDiagE by blast
                  thus ?thesis by auto
                qed
                moreover have "Diag (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u)"
                  using u w TensorDiag_preserves_Diag by simp
                moreover have "Dom v = \<^bold>\<langle>C.dom ?f\<^bold>\<rangle>"
                  using v by (metis Dom.simps(1))
                ultimately show ?thesis
                  using u v w TensorDiag_preserves_Diag
                  by (cases "TensorDiag (Dom w) (Dom u)") simp_all
              qed
              hence "\<guillemotleft>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<guillemotright> = \<guillemotleft>Dom v \<^bold>\<Down> (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u)\<guillemotright>"
                using TensorDiag_Diag red2_Diag by simp
              thus ?thesis by presburger
            qed
            finally have
              "\<guillemotleft>(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u\<guillemotright>
                   = \<guillemotleft>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<guillemotright> \<cdot> (\<guillemotleft>Dom v\<guillemotright> \<otimes> \<guillemotleft>Dom w \<^bold>\<Down> Dom u\<guillemotright>) \<cdot>
                     \<a>[\<guillemotleft>Dom v\<guillemotright>, \<guillemotleft>Dom w\<guillemotright>, \<guillemotleft>Dom u\<guillemotright>]"
              by blast
            thus ?thesis
              using assms v w TensorDiag_assoc by presburger
          qed
          finally show ?thesis
            using vw TensorDiag_Diag by simp
        qed
      qed
      ultimately show ?thesis by blast
    qed

    lemma Tensor_preserves_coherent:
    assumes "Arr t" and "Arr u" and "coherent t" and "coherent u"
    shows "coherent (t \<^bold>\<otimes> u)"
    proof -
      have t: "Arr t \<and> Ide (Dom t) \<and> Ide (Cod t) \<and> Ide \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<and>
               arr \<guillemotleft>t\<guillemotright> \<and> arr \<guillemotleft>Dom t\<guillemotright> \<and> ide \<guillemotleft>Dom t\<guillemotright> \<and> arr \<guillemotleft>Cod t\<guillemotright> \<and> ide \<guillemotleft>Cod t\<guillemotright>"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod Diagonalize_preserves_Ide
              eval_in_hom
        by auto
      have u: "Arr u \<and> Ide (Dom u) \<and> Ide (Cod u) \<and> Ide \<^bold>\<lfloor>Dom u\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod u\<^bold>\<rfloor> \<and>
               arr \<guillemotleft>u\<guillemotright> \<and> arr \<guillemotleft>Dom u\<guillemotright> \<and> ide \<guillemotleft>Dom u\<guillemotright> \<and> arr \<guillemotleft>Cod u\<guillemotright> \<and> ide \<guillemotleft>Cod u\<guillemotright>"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod Diagonalize_preserves_Ide
              eval_in_hom
        by auto
      have "\<guillemotleft>Cod (t \<^bold>\<otimes> u)\<^bold>\<down>\<guillemotright> \<cdot> (\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>)
              = (\<guillemotleft>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<guillemotright> \<cdot> (\<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>Cod u\<^bold>\<down>\<guillemotright>)) \<cdot> (\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>)"
        using t u eval_red_Tensor by simp
      also have "... = \<guillemotleft>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<guillemotright> \<cdot> (\<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>Cod u\<^bold>\<down>\<guillemotright>) \<cdot> (\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>)"
        using t u eval_in_hom tensor_in_hom red_in_Hom red2_in_Hom Diagonalize_in_Hom
              Diag_Diagonalize
        by simp
      also have "... = \<guillemotleft>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<guillemotright> \<cdot> (\<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<otimes> \<guillemotleft>\<^bold>\<lfloor>u\<^bold>\<rfloor>\<guillemotright>) \<cdot> (\<guillemotleft>Dom t\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>Dom u\<^bold>\<down>\<guillemotright>)"
        using assms t u eval_in_hom Diagonalize_in_Hom red_in_Hom interchange by simp
      also have "... = (\<guillemotleft>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<guillemotright> \<cdot> (\<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<guillemotright> \<otimes> \<guillemotleft>\<^bold>\<lfloor>u\<^bold>\<rfloor>\<guillemotright>)) \<cdot> (\<guillemotleft>Dom t\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>Dom u\<^bold>\<down>\<guillemotright>)"
        using t u eval_in_hom tensor_in_hom red_in_Hom red2_in_Hom Diagonalize_in_Hom
              Diag_Diagonalize
        by simp
      also have "... = (\<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>\<guillemotright>) \<cdot> (\<guillemotleft>Dom t\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>Dom u\<^bold>\<down>\<guillemotright>)"
        using assms t u Diag_Diagonalize Diagonalize_in_Hom
              eval_red2_naturality [of "Diagonalize t" "Diagonalize u"]
        by simp
      also have "... = \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>\<guillemotright> \<cdot> (\<guillemotleft>Dom t\<^bold>\<down>\<guillemotright> \<otimes> \<guillemotleft>Dom u\<^bold>\<down>\<guillemotright>)"
        using t u eval_in_hom tensor_in_hom TensorDiag_in_Hom red2_in_Hom
              Diagonalize_in_Hom Diag_Diagonalize red_in_Hom
        by simp
      also have "... = \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>(Dom t \<^bold>\<otimes> Dom u)\<^bold>\<down>\<guillemotright>"
        using t u eval_red_Tensor by simp
      finally have "\<guillemotleft>Cod (t \<^bold>\<otimes> u)\<^bold>\<down>\<guillemotright> \<cdot> (\<guillemotleft>t\<guillemotright> \<otimes> \<guillemotleft>u\<guillemotright>) = \<guillemotleft>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>(Dom t \<^bold>\<otimes> Dom u)\<^bold>\<down>\<guillemotright>"
        by blast
      thus ?thesis using t u by simp
    qed

    lemma Comp_preserves_coherent:
    assumes "Arr t" and "Arr u" and "Dom t = Cod u"
    and "coherent t" and "coherent u"
    shows "coherent (t \<^bold>\<cdot> u)"
    proof -
      have t: "Arr t \<and> Ide (Dom t) \<and> Ide (Cod t) \<and> Ide \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<and>
               arr \<guillemotleft>t\<guillemotright> \<and> arr \<guillemotleft>Dom t\<guillemotright> \<and> ide \<guillemotleft>Dom t\<guillemotright> \<and> arr \<guillemotleft>Cod t\<guillemotright> \<and> ide \<guillemotleft>Cod t\<guillemotright>"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod Diagonalize_preserves_Ide
              eval_in_hom
        by auto
      have u: "Arr u \<and> Ide (Dom u) \<and> Ide (Cod u) \<and> Ide \<^bold>\<lfloor>Dom u\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod u\<^bold>\<rfloor> \<and>
               arr \<guillemotleft>u\<guillemotright> \<and> arr \<guillemotleft>Dom u\<guillemotright> \<and> ide \<guillemotleft>Dom u\<guillemotright> \<and> arr \<guillemotleft>Cod u\<guillemotright> \<and> ide \<guillemotleft>Cod u\<guillemotright>"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod Diagonalize_preserves_Ide
              eval_in_hom
        by auto
      have "\<guillemotleft>Cod (t \<^bold>\<cdot> u)\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>t \<^bold>\<cdot> u\<guillemotright> = \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>t\<guillemotright> \<cdot> \<guillemotleft>u\<guillemotright>"
        using t u by simp
      also have "... = (\<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<cdot> \<guillemotleft>t\<guillemotright>) \<cdot> \<guillemotleft>u\<guillemotright>"
      proof -
        (* TODO: This is a very simple example of where I have to spoon-feed it to get it to
           apply comp_assoc. *)
        have "seq \<guillemotleft>Cod t\<^bold>\<down>\<guillemotright> \<guillemotleft>t\<guillemotright>"
          using assms t eval_in_hom red_in_Hom by auto
        moreover have "seq \<guillemotleft>t\<guillemotright> \<guillemotleft>u\<guillemotright>"
          using assms t u eval_in_hom by auto
        ultimately show ?thesis using comp_assoc by presburger
      qed
      also have "... = \<guillemotleft>\<^bold>\<lfloor>t \<^bold>\<cdot> u\<^bold>\<rfloor>\<guillemotright> \<cdot> \<guillemotleft>Dom (t \<^bold>\<cdot> u)\<^bold>\<down>\<guillemotright>"
        using t u assms  eval_in_hom red_in_Hom Diag_Diagonalize
        by (simp add: Diag_Diagonalize(1) Diag_implies_Arr eval_CompDiag)
      finally show "coherent (t \<^bold>\<cdot> u)" by blast
    qed

    text{*
      The main result: ``Every formal arrow is coherent.''
    *}

    theorem coherence:
    assumes "Arr t"
    shows "coherent t"
    proof -
      have "Arr t \<Longrightarrow> coherent t"
      proof (induct t)
        fix u v
        show "\<lbrakk> Arr u \<Longrightarrow> coherent u; Arr v \<Longrightarrow> coherent v \<rbrakk> \<Longrightarrow>
                Arr (u \<^bold>\<otimes> v) \<Longrightarrow> coherent (u \<^bold>\<otimes> v)"
          using Tensor_preserves_coherent by simp
        show "\<lbrakk> Arr u \<Longrightarrow> coherent u; Arr v \<Longrightarrow> coherent v \<rbrakk> \<Longrightarrow>
                Arr (u \<^bold>\<cdot> v) \<Longrightarrow> coherent (u \<^bold>\<cdot> v)"
          using Comp_preserves_coherent by simp
        next
        show "coherent \<^bold>\<I>" by simp
        fix f
        show "Arr \<^bold>\<langle>f\<^bold>\<rangle> \<Longrightarrow> coherent \<^bold>\<langle>f\<^bold>\<rangle>" by simp
        next
        fix t
        assume I: "Arr t \<Longrightarrow> coherent t"
        show Lunit: "Arr \<^bold>\<l>\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<l>\<^bold>[t\<^bold>]"
        proof -
          assume "Arr \<^bold>\<l>\<^bold>[t\<^bold>]"
          hence t: "Arr t" by simp
          have "coherent (t \<^bold>\<cdot> \<^bold>\<l>\<^bold>[Dom t\<^bold>])"
          proof -
            have "coherent t" using t I by simp
            moreover have "coherent \<^bold>\<l>\<^bold>[Dom t\<^bold>]"
              using t Arr_implies_Ide_Dom coherent_Lunit_Ide by blast
            moreover have "Arr \<^bold>\<l>\<^bold>[Dom t\<^bold>] \<and> Dom t = Cod \<^bold>\<l>\<^bold>[Dom t\<^bold>]"
              using t Arr_implies_Ide_Dom Ide_in_Hom by simp
            ultimately show ?thesis
              using t Comp_preserves_coherent [of t "\<^bold>\<l>\<^bold>[Dom t\<^bold>]"] by metis
          qed
          moreover have "Par \<^bold>\<l>\<^bold>[t\<^bold>] (t \<^bold>\<cdot> \<^bold>\<l>\<^bold>[Dom t\<^bold>])"
            using t Arr_implies_Ide_Dom Ide_implies_Arr Ide_in_Hom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<l>\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t \<^bold>\<cdot> \<^bold>\<l>\<^bold>[Dom t\<^bold>]\<^bold>\<rfloor>"
            using t Diagonalize_Comp_Arr_Dom by simp
          moreover have "\<guillemotleft>\<^bold>\<l>\<^bold>[t\<^bold>]\<guillemotright> = \<guillemotleft>t \<^bold>\<cdot> \<^bold>\<l>\<^bold>[Dom t\<^bold>]\<guillemotright>"
            using t Arr_implies_Ide_Dom Ide_implies_Arr eval_in_hom \<ll>_ide_simp by auto
          ultimately show ?thesis by auto
        qed
        show Runit: "Arr \<^bold>\<r>\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<r>\<^bold>[t\<^bold>]"
        proof -
          assume "Arr \<^bold>\<r>\<^bold>[t\<^bold>]"
          hence t: "Arr t" by simp
          have "coherent (t \<^bold>\<cdot> \<^bold>\<r>\<^bold>[Dom t\<^bold>])"
          proof -
            have "coherent t" using t I by simp
            moreover have "coherent \<^bold>\<r>\<^bold>[Dom t\<^bold>]"
              using t Arr_implies_Ide_Dom coherent_Runit_Ide by blast
            moreover have "Arr \<^bold>\<r>\<^bold>[Dom t\<^bold>] \<and> Cod \<^bold>\<r>\<^bold>[Dom t\<^bold>] = Dom t"
              using t Arr_implies_Ide_Dom Ide_in_Hom by simp
            ultimately show ?thesis
              using t Comp_preserves_coherent [of t "\<^bold>\<r>\<^bold>[Dom t\<^bold>]"] by metis
          qed
          moreover have "Par \<^bold>\<r>\<^bold>[t\<^bold>] (t \<^bold>\<cdot> \<^bold>\<r>\<^bold>[Dom t\<^bold>])"
            using t Arr_implies_Ide_Dom Ide_implies_Arr Ide_in_Hom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<r>\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t \<^bold>\<cdot> \<^bold>\<r>\<^bold>[Dom t\<^bold>]\<^bold>\<rfloor>"
            using t Diagonalize_Comp_Arr_Dom by simp
          moreover have "\<guillemotleft>\<^bold>\<r>\<^bold>[t\<^bold>]\<guillemotright> = \<guillemotleft>t \<^bold>\<cdot> \<^bold>\<r>\<^bold>[Dom t\<^bold>]\<guillemotright>"
            using t Arr_implies_Ide_Dom Ide_implies_Arr eval_in_hom \<rho>_ide_simp by auto
          ultimately show ?thesis by auto
        qed
        show "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        proof -
          assume "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
          hence t: "Arr t" by simp
          have "coherent (\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t)"
          proof -
            have "coherent t" using t I by simp
            moreover have "coherent \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>]"
              using t Arr_implies_Ide_Cod coherent_Lunit'_Ide by blast
            moreover have "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<and> Dom \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] = Cod t"
              using t Arr_implies_Ide_Cod Ide_in_Hom by simp
            ultimately show ?thesis
              using t Comp_preserves_coherent [of "\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>]" t] by metis
          qed
          moreover have "Par \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] (\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t)"
            using t Arr_implies_Ide_Cod Ide_implies_Arr Ide_in_Hom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t\<^bold>\<rfloor>"
            using t Diagonalize_Comp_Cod_Arr by simp
          moreover have "\<guillemotleft>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> = \<guillemotleft>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t\<guillemotright>"
            using t Arr_implies_Ide_Cod Ide_implies_Arr eval_in_hom \<ll>'.is_natural_2 [of "\<guillemotleft>t\<guillemotright>"]
            by simp
          ultimately show ?thesis by auto
        qed
        show "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        proof -
          assume "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
          hence t: "Arr t" by simp
          have "coherent (\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t)"
          proof -
            have "coherent t" using t I by simp
            moreover have "coherent \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>]"
              using t Arr_implies_Ide_Cod coherent_Runit'_Ide by blast
            moreover have "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<and> Dom \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] = Cod t"
              using t Arr_implies_Ide_Cod Ide_in_Hom by simp
            ultimately show ?thesis
              using t Comp_preserves_coherent [of "\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>]" t] by metis
          qed
          moreover have "Par \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] (\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t)"
            using t Arr_implies_Ide_Cod Ide_implies_Arr Ide_in_Hom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t\<^bold>\<rfloor>"
            using t Diagonalize_Comp_Cod_Arr by simp
          moreover have "\<guillemotleft>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<guillemotright> = \<guillemotleft>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t\<guillemotright>"
            using t Arr_implies_Ide_Cod Ide_implies_Arr eval_in_hom \<rho>'.is_natural_2 [of "\<guillemotleft>t\<guillemotright>"]
            by simp
          ultimately show ?thesis by auto
        qed
        next
        fix t u v
        assume I1: "Arr t \<Longrightarrow> coherent t"
        assume I2: "Arr u \<Longrightarrow> coherent u"
        assume I3: "Arr v \<Longrightarrow> coherent v"
        show "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>] \<Longrightarrow> coherent \<^bold>\<a>\<^bold>[t, u, v\<^bold>]"
        proof -
          assume tuv: "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>]"
          have t: "Arr t" using tuv by simp
          have u: "Arr u" using tuv by simp
          have v: "Arr v" using tuv by simp
          have "coherent ((t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
          proof -
            have "Arr (t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<and> coherent (t \<^bold>\<otimes> u \<^bold>\<otimes> v)"
            proof
              have 1: "Arr t \<and> coherent t" using t I1 by simp
              have 2: "Arr (u \<^bold>\<otimes> v) \<and> coherent (u \<^bold>\<otimes> v)"
                using u v I2 I3 Tensor_preserves_coherent by force
              show "Arr (t \<^bold>\<otimes> u \<^bold>\<otimes> v) " using 1 2 by simp
              show "coherent (t \<^bold>\<otimes> u \<^bold>\<otimes> v)"
                using 1 2 Tensor_preserves_coherent by blast
            qed
            moreover have "Arr \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom by simp
            moreover have "coherent \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom coherent_Assoc_Ide by blast
            moreover have "Dom (t \<^bold>\<otimes> u \<^bold>\<otimes> v) = Cod \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom Ide_in_Hom by simp
            ultimately show ?thesis
              using t u v Arr_implies_Ide_Dom Ide_implies_Arr
                    Comp_preserves_coherent [of "t \<^bold>\<otimes> u \<^bold>\<otimes> v" "\<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"]
              by metis
          qed
          moreover have "Par \<^bold>\<a>\<^bold>[t, u, v\<^bold>] ((t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
            using t u v Arr_implies_Ide_Dom Ide_implies_Arr Ide_in_Hom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>(t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<^bold>\<rfloor>"
          proof -
            have "(\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>
                     = (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom v\<^bold>\<rfloor>)"
            proof -
              have 1: "Diag \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Diag \<^bold>\<lfloor>u\<^bold>\<rfloor> \<and> Diag \<^bold>\<lfloor>v\<^bold>\<rfloor> \<and>
                       Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Dom \<^bold>\<lfloor>u\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom u\<^bold>\<rfloor> \<and> Dom \<^bold>\<lfloor>v\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom v\<^bold>\<rfloor>"
                using t u v Diag_Diagonalize by blast
              moreover have "Diag (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>)"
                using 1 TensorDiag_preserves_Diag(1) by blast
              moreover have "\<And>t. Arr t \<Longrightarrow> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
                using t Diagonalize_Comp_Arr_Dom by simp
              moreover have "Dom \<^bold>\<lfloor>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor>"
                using Diag_Diagonalize tuv by blast
              ultimately show ?thesis
                using t u v tuv 1
                by (metis (no_types) TensorDiag_assoc TensorDiag_preserves_Diag(2)
                    Diagonalize.simps(9))
            qed
            thus ?thesis
              using t u v Diagonalize_Comp_Arr_Dom CompDiag_TensorDiag Diag_Diagonalize
              by simp
          qed
          moreover have "\<guillemotleft>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<guillemotright> = \<guillemotleft>(t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<guillemotright>"
            using t u v Arr_implies_Ide_Dom Ide_implies_Arr eval_in_hom
                  \<alpha>_simp [of "\<guillemotleft>t\<guillemotright>" "\<guillemotleft>u\<guillemotright>" "\<guillemotleft>v\<guillemotright>"] CC.ide_char CCC.ide_char CC.arr_char CCC.arr_char
                  tensor_in_hom
            by simp
          ultimately show "coherent \<^bold>\<a>\<^bold>[t, u, v\<^bold>]" by metis
        qed
        show "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] \<Longrightarrow> coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
        proof -
          assume tuv: "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
          have t: "Arr t" using tuv by simp
          have u: "Arr u" using tuv by simp
          have v: "Arr v" using tuv by simp
          have "coherent (((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
          proof -
            have "Arr ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<and> coherent ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v)"
            proof
              have 1: "Arr v \<and> coherent v" using v I3 by simp
              have 2: "Arr (t \<^bold>\<otimes> u) \<and> coherent (t \<^bold>\<otimes> u)"
                using t u I1 I2 Tensor_preserves_coherent by force
              show "Arr ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v)" using 1 2 by simp
              show "coherent ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v)"
                using 1 2 Tensor_preserves_coherent by blast
            qed
            moreover have "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom by simp
            moreover have "coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom coherent_Assoc'_Ide by blast
            moreover have "Dom ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) = Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom Ide_in_Hom by simp
            ultimately show ?thesis
              using t u v Arr_implies_Ide_Dom Ide_implies_Arr
                    Comp_preserves_coherent [of "((t \<^bold>\<otimes> u) \<^bold>\<otimes> v)" "\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"]
              by metis
          qed
          moreover have "Par \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] (((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
            using t u v Arr_implies_Ide_Dom Ide_implies_Arr Ide_in_Hom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<^bold>\<rfloor>"
            using t u v Diagonalize_Comp_Arr_Dom CompDiag_TensorDiag Diag_Diagonalize
            apply simp
            using t u v tuv TensorDiag_assoc TensorDiag_preserves_Diag
                  TensorDiag_in_Hom CompDiag_Diag_Dom [of "(\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>"]
            by simp
          moreover have "\<guillemotleft>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<guillemotright> = \<guillemotleft>((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<guillemotright>"
            using t u v Arr_implies_Ide_Dom Ide_implies_Arr eval_in_hom
                  CC.ide_char CCC.ide_char CC.arr_char CCC.arr_char tensor_in_hom
                  assoc'_in_hom [of "\<guillemotleft>t\<guillemotright>" "\<guillemotleft>u\<guillemotright>" "\<guillemotleft>v\<guillemotright>"] \<alpha>'.map_ide_simp
                  comp_cod_arr [of "inv \<a>[\<guillemotleft>t\<guillemotright>, \<guillemotleft>u\<guillemotright>, \<guillemotleft>v\<guillemotright>]"]
                  \<alpha>'.is_natural_1 [of "(\<guillemotleft>t\<guillemotright>, \<guillemotleft>u\<guillemotright>, \<guillemotleft>v\<guillemotright>)"] \<alpha>'_simp
            by simp
          ultimately show "coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]" by metis
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text{*
      MacLane \cite{MacLane71} says: ``A coherence theorem asserts `Every diagram commutes',''
      but that is somewhat misleading.  A coherence theorem provides some kind of hopefully
      useful way of distinguishing diagrams that definitely commute from diagrams that might not.
      The next result expresses coherence for monoidal categories in this way.
      As the hypotheses can be verified algorithmically (using the functions @{term Dom},
      @{term Cod}, @{term Arr}, and @{term Diagonalize}) if we are given an oracle for equality
      of arrows in @{text C}, the result provides a decision procedure, relative to @{text C},
      for the word problem for the free monoidal category generated by @{text C}.
    *}

    corollary eval_eqI:
    assumes "Par t u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    shows "\<guillemotleft>t\<guillemotright> = \<guillemotleft>u\<guillemotright>"
      using assms coherence canonical_factorization by simp

    text{*
      Our final corollary expresses coherence in a more ``MacLane-like'' fashion:
      parallel canonical arrows are equivalent under evaluation.
    *}

    corollary maclane_coherence:
    assumes "Par t u" and "Can t" and "Can u"
    shows "\<guillemotleft>t\<guillemotright> = \<guillemotleft>u\<guillemotright>"
    proof (intro eval_eqI)
      show "Par t u" by fact
      show "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
      proof -
        have "Ide \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>u\<^bold>\<rfloor> \<and> Par \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
          using assms eval_eqI Ide_Diagonalize_Can Diagonalize_in_Hom by simp
        thus ?thesis using Ide_in_Hom by auto
      qed
    qed

  end

end

