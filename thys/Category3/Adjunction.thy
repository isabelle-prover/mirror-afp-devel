(*  Title:       Adjunction
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Adjunction

theory Adjunction
imports Yoneda
begin

  text{*
    This theory defines the notions of adjoint functor and adjunction in various
    ways and establishes their equivalence.
    The notions ``left adjoint functor'' and ``right adjoint functor'' are defined
    in terms of universal arrows.
    ``Meta-adjunctions'' are defined in terms of natural bijections between hom-sets,
    where the notion of naturality is axiomatized directly.
    ``Hom-adjunctions'' formalize the notion of adjunction in terms of natural
    isomorphisms of hom-functors.
    ``Unit-counit adjunctions'' define adjunctions in terms of functors equipped
    with unit and counit natural transformations that satisfy the usual
    ``triangle identities.''
    The @{text adjunction} locale is defined as the grand unification of all the
    definitions, and includes formulas that connect the data from each of them.
    It is shown that each of the definitions induces an interpretation of the
    @{text adjunction} locale, so that all the definitions are essentially equivalent.
    Finally, it is shown that right adjoint functors are unique up to natural
    isomorphism.

    The reference \cite{Wikipedia-Adjoint-Functors} was useful in constructing this theory.
  *}

  section "Left Adjoint Functor"

  text{*
    ``@{term e} is an arrow from @{term "F x"} to @{term y}.''
  *}

  locale arrow_from_functor =
    C: category C +
    D: category D +
    F: "functor" D C F
    for D :: "'d comp"
    and C :: "'c comp"
    and F :: "'d \<Rightarrow> 'c"
    and x :: 'd
    and y :: 'c
    and e :: 'c +
    assumes arrow: "D.ide x \<and> e \<in> C.hom (F x) y"
  begin

    text{*
      ``@{term g} is a @{term D}-coextension of @{term f} along @{term e}.''
    *}

    definition is_coext :: "'d \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    where "is_coext x' f g \<equiv> g \<in> D.hom x' x \<and> f = C e (F g)"

  end

  text{*
    ``@{term e} is a terminal arrow from @{term "F x"} to @{term y}.''
  *}

  locale terminal_arrow_from_functor =
    arrow_from_functor D C F x y e
    for D :: "'d comp"
    and C :: "'c comp"
    and F :: "'d \<Rightarrow> 'c"
    and x :: 'd
    and y :: 'c
    and e :: 'c +
    assumes is_terminal: "arrow_from_functor D C F x' y f \<Longrightarrow> (\<exists>!g. is_coext x' f g)"
  begin

    definition the_coext :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    where "the_coext x' f = (THE g. is_coext x' f g)"

    lemma the_coext_prop:
    assumes "arrow_from_functor D C F x' y f"
    shows "the_coext x' f \<in> D.hom x' x \<and> f = C e (F (the_coext x' f))"
      using assms is_terminal the_coext_def is_coext_def theI2 [of "\<lambda>g. is_coext x' f g"]
      by (metis (no_types, lifting) mem_Collect_eq)

    lemma the_coext_unique:
    assumes "arrow_from_functor D C F x' y f" and "is_coext x' f g"
    shows "g = the_coext x' f"
      using assms is_terminal the_coext_def the_equality by metis

  end

  text{*
    A left adjoint functor is a functor @{text "F: D \<rightarrow> C"}
    that enjoys the following universal coextension property: for each object
    @{term y} of @{term C} there exists an object @{term x} of @{term D} and an
    arrow @{text "e \<in> C.hom (F x) y"} such that for any arrow
    @{text "f \<in> C.hom (F x') y"} there exists a unique @{text "g \<in> D.hom x' x"}
    such that @{term "f = C e (F g)"}.
  *}

  locale left_adjoint_functor =
    C: category C +
    D: category D +
    "functor" D C F
    for D :: "'d comp"
    and C :: "'c comp"
    and F :: "'d \<Rightarrow> 'c" +
    assumes ex_terminal_arrow: "C.ide y \<Longrightarrow> (\<exists>x e. terminal_arrow_from_functor D C F x y e)"

  section "Right Adjoint Functor"

  text{*
    ``@{term e} is an arrow from @{term x} to @{term "G y"}.''
  *}

  locale arrow_to_functor =
    C: category C +
    D: category D +
    G: "functor" C D G
    for C :: "'c comp"
    and D :: "'d comp"
    and G :: "'c \<Rightarrow> 'd"
    and x :: 'd
    and y :: 'c
    and e :: 'd +
    assumes arrow: "C.ide y \<and> e \<in> D.hom x (G y)"
  begin

    text{*
      ``@{term f} is a @{term C}-extension of @{term g} along @{term e}.''
    *}

    definition is_ext :: "'c \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> bool"
    where "is_ext y' g f \<equiv> f \<in> C.hom y y' \<and> g = D (G f) e"

  end

  text{*
    ``@{term e} is an initial arrow from @{term x} to @{term "G y"}.''
  *}

  locale initial_arrow_to_functor =
    arrow_to_functor C D G x y e
    for C :: "'c comp"
    and D :: "'d comp"
    and G :: "'c \<Rightarrow> 'd"
    and x :: 'd
    and y :: 'c
    and e :: 'd +
    assumes is_initial: "arrow_to_functor C D G x y' g \<Longrightarrow> (\<exists>!f. is_ext y' g f)"
  begin

    definition the_ext :: "'c \<Rightarrow> 'd \<Rightarrow> 'c"
    where "the_ext y' g = (THE f. is_ext y' g f)"

    lemma the_ext_prop:
    assumes "arrow_to_functor C D G x y' g"
    shows "the_ext y' g \<in> C.hom y y' \<and> g = D (G (the_ext y' g)) e"
      using assms is_initial the_ext_def is_ext_def theI2 [of "\<lambda>f. is_ext y' g f"]
      by (metis (no_types, lifting))

    lemma the_ext_unique:
    assumes "arrow_to_functor C D G x y' g" and "is_ext y' g f"
    shows "f = the_ext y' g"
      using assms is_initial the_ext_def the_equality by metis

  end

  text{*
    A right adjoint functor is a functor @{text "G: C \<rightarrow> D"}
    that enjoys the following universal extension property:
    for each object @{term x} of @{term D} there exists an object @{term y} of @{term C}
    and an arrow @{text "e \<in> D.hom x (G y)"} such that for any arrow
    @{text "g \<in> D.hom x (G y')"} there exists a unique @{text "f \<in> C.hom y y'"}
    such that @{term "h = D e (G f)"}.
  *}

  locale right_adjoint_functor =
    C: category C +
    D: category D +
    "functor" C D G
    for C :: "'c comp"
    and D :: "'d comp"
    and G :: "'c \<Rightarrow> 'd" +
    assumes initial_arrows_exist: "D.ide x \<Longrightarrow> (\<exists>y e. initial_arrow_to_functor C D G x y e)"

  section "Various Definitions of Adjunction"

  subsection "Meta-Adjunction"

  text{*
    A ``meta-adjunction'' consists of a functor @{text "F: D \<rightarrow> C"},
    a functor @{text "G: C \<rightarrow> D"}, and for each object @{term x}
    of @{term C} and @{term y} of @{term D} a bijection between
    @{text "C.hom (F y) x"} to @{text "D.hom y (G x)"} which is natural in @{term x}
    and @{term y}.  The naturality is easy to express at the meta-level without having
    to resort to the formal baggage of ``set category,'' ``hom-functor,''
    and ``natural isomorphism,'' hence the name.
  *}

  locale meta_adjunction =
    C: category C +
    D: category D +
    F: "functor" D C F +
    G: "functor" C D G
    for C :: "'c comp"
    and D :: "'d comp"
    and F :: "'d \<Rightarrow> 'c"
    and G :: "'c \<Rightarrow> 'd"
    and \<phi> :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    and \<psi> :: "'c \<Rightarrow> 'd \<Rightarrow> 'c" +
    assumes \<phi>_mapsto: "\<lbrakk> D.ide y; f \<in> C.hom (F y) x \<rbrakk> \<Longrightarrow> \<phi> y f \<in> D.hom y (G x)"
    and \<psi>_mapsto: "\<lbrakk> C.ide x; g \<in> D.hom y (G x) \<rbrakk> \<Longrightarrow> \<psi> x g \<in> C.hom (F y) x"
    and \<psi>_\<phi>: "\<lbrakk> D.ide y; f \<in> C.hom (F y) x \<rbrakk> \<Longrightarrow> \<psi> x (\<phi> y f) = f"
    and \<phi>_\<psi>: "\<lbrakk> C.ide x; g \<in> D.hom y (G x) \<rbrakk> \<Longrightarrow> \<phi> y (\<psi> x g) = g"
    and naturality: "\<lbrakk> f \<in> C.hom x x'; g \<in> D.hom y' y; h \<in> C.hom (F y) x \<rbrakk> \<Longrightarrow>
                        \<phi> y' (C f (C h (F g))) = D (G f) (D (\<phi> y h) g)"
  begin

    text{*
      The naturality of @{term \<psi>} is a consequence of the naturality of @{term \<phi>}
      and the other assumptions.
    *}

    lemma naturality': "\<lbrakk> f \<in> C.hom x x'; g \<in> D.hom y' y; h \<in> D.hom y (G x) \<rbrakk> \<Longrightarrow>
                           C f (C (\<psi> x h) (F g)) = \<psi> x' (D (G f) (D h g))"
    proof -
      assume f: "f \<in> C.hom x x'" and g: "g \<in> D.hom y' y" and h: "h \<in> D.hom y (G x)"
      have 1: "C f (C (\<psi> x h) (F g)) \<in> C.hom (F y') x'"
        using f g h \<psi>_mapsto F.preserves_cod F.preserves_dom by auto
      have 2: "D (D (G f) h) g \<in> D.hom y' (G x')"
        using f g h \<phi>_mapsto G.preserves_cod G.preserves_dom by auto
      have "\<psi> x h \<in> C.hom (F y) x" using f h \<psi>_mapsto by auto
      hence "\<phi> y' (C f (C (\<psi> x h) (F g))) = D (G f) (D (\<phi> y (\<psi> x h)) g)"
        using f g naturality by blast
      hence "\<psi> x' (\<phi> y' (C f (C (\<psi> x h) (F g)))) = \<psi> x' (D (G f) (D (\<phi> y (\<psi> x h)) g))"
        by simp
      thus ?thesis
        using 1 2 f h \<psi>_\<phi> \<phi>_\<psi> by auto
    qed

  end

  subsection "Hom-Adjunction"

  text{*
    The bijection between hom-sets that defines an adjunction can be represented
    formally as a natural isomorphism of hom-functors.  However, stating the definition
    this way is more complex than was the case for @{text "meta_adjunction"}.
    One reason is that we need to have a ``set category'' that is suitable as
    a target category for the hom-functors, and since the arrows of the categories
    @{term C} and @{term D} will in general have distinct types, we need a set category
    that simultaneously embeds both.  Another reason is that we simply have to formally
    construct the various categories and functors required to express the definition.

    This is a good place to point out that I have often included more sublocales
    in a locale than are strictly required.  The main reason for this is the fact that
    the locale system in Isabelle only gives one name to each entity introduced by
    a locale: the name that it has in the first locale in which it occurs.
    This means that entities that make their first appearance deeply nested in sublocales
    will have to be referred to by long qualified names that can be difficult to
    understand, or even to discover.  To counteract this, I have typically introduced
    sublocales before the superlocales that contain them to ensure that the entities
    in the sublocales can be referred to by short meaningful (and predictable) names.
    In my opinion, though, it would be better if the locale system would make entities
    that occur in multiple locales accessible by \emph{all} possible qualified names,
    so that the most perspicuous name could be used in any particular context.
  *}

  locale hom_adjunction =
    C: category C +
    D: category D +
    S: set_category S +
    Cop: dual_category C +
    Dop: dual_category D +
    CopxC: product_category Cop.comp C +
    DopxD: product_category Dop.comp D +
    DopxC: product_category Dop.comp C +
    F: "functor" D C F +
    G: "functor" C D G +
    HomC: hom_functor C S \<phi>C +
    HomD: hom_functor D S \<phi>D +
    Fop: dual_functor Dop.comp Cop.comp F +
    FopxC: product_functor Dop.comp C Cop.comp C Fop.map C.map +
    DopxG: product_functor Dop.comp C Dop.comp D Dop.map G +
    Hom_FopxC: composite_functor DopxC.comp CopxC.comp S FopxC.map HomC.map +
    Hom_DopxG: composite_functor DopxC.comp DopxD.comp S DopxG.map HomD.map +
    Hom_FopxC: set_valued_functor DopxC.comp S Hom_FopxC.map +
    Hom_DopxG: set_valued_functor DopxC.comp S Hom_DopxG.map +
    \<Phi>: set_valued_transformation DopxC.comp S Hom_FopxC.map Hom_DopxG.map \<Phi> +
    \<Psi>: set_valued_transformation DopxC.comp S Hom_DopxG.map Hom_FopxC.map \<Psi> +
    \<Phi>\<Psi>: inverse_transformations DopxC.comp S Hom_FopxC.map Hom_DopxG.map \<Phi> \<Psi>
    for C :: "'c comp"
    and D :: "'d comp"
    and S :: "'s comp"
    and \<phi>C :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and \<phi>D :: "'d * 'd \<Rightarrow> 'd \<Rightarrow> 's"
    and F :: "'d \<Rightarrow> 'c"
    and G :: "'c \<Rightarrow> 'd"
    and \<Phi> :: "'d * 'c \<Rightarrow> 's"
    and \<Psi> :: "'d * 'c \<Rightarrow> 's"
  begin

    abbreviation \<psi>C :: "'c * 'c \<Rightarrow> 's \<Rightarrow> 'c"
    where "\<psi>C \<equiv> HomC.\<psi>"

    abbreviation \<psi>D :: "'d * 'd \<Rightarrow> 's \<Rightarrow> 'd"
    where "\<psi>D \<equiv> HomD.\<psi>"

  end

  subsection "Unit/Counit Adjunction"

  text{*
    Expressed in unit/counit terms, an adjunction consists of functors
    @{text "F: D \<rightarrow> C"} and @{text "G: C \<rightarrow> D"}, equipped with natural transformations
    @{text "\<eta>: 1 \<rightarrow> GF"} and @{text "\<epsilon>: FG \<rightarrow> 1"} satisfying certain ``triangle identities''.
   *}

  locale unit_counit_adjunction =
    C: category C +
    D: category D +
    F: "functor" D C F +
    G: "functor" C D G +
    GF: composite_functor D C D F G +
    FG: composite_functor C D C G F +
    FGF: composite_functor D C C F "F o G" +
    GFG: composite_functor C D D G "G o F" +
    \<eta>: natural_transformation D D D.map "G o F" \<eta> +
    \<epsilon>: natural_transformation C C "F o G" C.map \<epsilon> +
    F\<eta>: horizontal_composite D D C D.map "G o F" F F \<eta> F +
    \<eta>G: horizontal_composite C D D G G D.map "G o F" G \<eta> +
    \<epsilon>F: horizontal_composite D C C F F "F o G" C.map F \<epsilon> +
    G\<epsilon>: horizontal_composite C C D "F o G" C.map G G \<epsilon> G +
    \<epsilon>FoF\<eta>: vertical_composite D C F "F o G o F" F "F o \<eta>" "\<epsilon> o F" +
    G\<epsilon>o\<eta>G: vertical_composite C D G "G o F o G" G "\<eta> o G" "G o \<epsilon>"
    for C :: "'c comp"
    and D :: "'d comp"
    and F :: "'d \<Rightarrow> 'c"
    and G :: "'c \<Rightarrow> 'd"
    and \<eta> :: "'d \<Rightarrow> 'd"
    and \<epsilon> :: "'c \<Rightarrow> 'c" +
    assumes triangle_F: "\<epsilon>FoF\<eta>.map = F"
    and triangle_G: "G\<epsilon>o\<eta>G.map = G"

  subsection "Adjunction"

  text{*
    The grand unification of everything to do with an adjunction.
  *}

  locale adjunction =
    C: category C +
    D: category D +
    S: set_category S +
    Cop: dual_category C +
    Dop: dual_category D +
    CopxC: product_category Cop.comp C +
    DopxD: product_category Dop.comp D +
    DopxC: product_category Dop.comp C +
    idDop: identity_functor Dop.comp +
    HomC: hom_functor C S \<phi>C +
    HomD: hom_functor D S \<phi>D +
    F: left_adjoint_functor D C F +
    G: right_adjoint_functor C D G +
    GF: composite_functor D C D F G +
    FG: composite_functor C D C G F +
    FGF: composite_functor D C C F FG.map +
    GFG: composite_functor C D D G GF.map +
    Fop: dual_functor Dop.comp Cop.comp F +
    FopxC: product_functor Dop.comp C Cop.comp C Fop.map C.map +
    DopxG: product_functor Dop.comp C Dop.comp D Dop.map G +
    Hom_FopxC: composite_functor DopxC.comp CopxC.comp S FopxC.map HomC.map +
    Hom_DopxG: composite_functor DopxC.comp DopxD.comp S DopxG.map HomD.map +
    Hom_FopxC: set_valued_functor DopxC.comp S Hom_FopxC.map +
    Hom_DopxG: set_valued_functor DopxC.comp S Hom_DopxG.map +
    \<eta>: natural_transformation D D D.map GF.map \<eta> +
    \<epsilon>: natural_transformation C C FG.map C.map \<epsilon> +
    F\<eta>: horizontal_composite D D C D.map "G o F" F F \<eta> F +
    \<eta>G: horizontal_composite C D D G G D.map "G o F" G \<eta> +
    \<epsilon>F: horizontal_composite D C C F F "F o G" C.map F \<epsilon> +
    G\<epsilon>: horizontal_composite C C D "F o G" C.map G G \<epsilon> G +
    \<epsilon>FoF\<eta>: vertical_composite D C F FGF.map F F\<eta>.map \<epsilon>F.map +
    G\<epsilon>o\<eta>G: vertical_composite C D G GFG.map G \<eta>G.map G\<epsilon>.map +
    \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi> +
    \<eta>\<epsilon>: unit_counit_adjunction C D F G \<eta> \<epsilon> +
    \<Phi>\<Psi>: hom_adjunction C D S \<phi>C \<phi>D F G \<Phi> \<Psi>
    for C :: "'c comp"
    and D :: "'d comp"
    and S :: "'s comp"
    and \<phi>C :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and \<phi>D :: "'d * 'd \<Rightarrow> 'd \<Rightarrow> 's"
    and F :: "'d \<Rightarrow> 'c"
    and G :: "'c \<Rightarrow> 'd"
    and \<phi> :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    and \<psi> :: "'c \<Rightarrow> 'd \<Rightarrow> 'c"
    and \<eta> :: "'d \<Rightarrow> 'd"
    and \<epsilon> :: "'c \<Rightarrow> 'c"
    and \<Phi> :: "'d * 'c \<Rightarrow> 's"
    and \<Psi> :: "'d * 'c \<Rightarrow> 's" +
    assumes \<phi>_in_terms_of_\<eta>: "\<lbrakk> D.ide y; f \<in> C.hom (F y) x \<rbrakk> \<Longrightarrow> \<phi> y f = D (G f) (\<eta> y)"
    and \<psi>_in_terms_of_\<epsilon>: "\<lbrakk> C.ide x; g \<in> D.hom y (G x) \<rbrakk> \<Longrightarrow> \<psi> x g = C (\<epsilon> x) (F g)"
    and \<eta>_in_terms_of_\<phi>: "D.ide y \<Longrightarrow> \<eta> y = \<phi> y (F y)"
    and \<epsilon>_in_terms_of_\<psi>: "C.ide x \<Longrightarrow> \<epsilon> x = \<psi> x (G x)"
    and \<phi>_in_terms_of_\<Phi>: "\<lbrakk> D.ide y; f \<in> C.hom (F y) x \<rbrakk> \<Longrightarrow>
                              \<phi> y f = (\<Phi>\<Psi>.\<psi>D (y, G x) o S.Fun (\<Phi> (y, x)) o \<phi>C (F y, x)) f"
    and \<psi>_in_terms_of_\<Psi>: "\<lbrakk> C.ide x; g \<in> D.hom y (G x) \<rbrakk> \<Longrightarrow>
                              \<psi> x g = (\<Phi>\<Psi>.\<psi>C (F y, x) o S.Fun (\<Psi> (y, x)) o \<phi>D (y, G x)) g"
    and \<Phi>_in_terms_of_\<phi>:
           "\<lbrakk> C.ide x; D.ide y \<rbrakk> \<Longrightarrow>
                \<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                    (\<phi>D (y, G x) o \<phi> y o \<Phi>\<Psi>.\<psi>C (F y, x))"
    and \<Psi>_in_terms_of_\<psi>:
           "\<lbrakk> C.ide x; D.ide y \<rbrakk> \<Longrightarrow>
                \<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                    (\<phi>C (F y, x) o \<psi> x o \<Phi>\<Psi>.\<psi>D (y, G x))"

  section "Meta-Adjunctions Induce Unit/Counit Adjunctions"

  context meta_adjunction
  begin

    interpretation GF: composite_functor D C D F G ..
    interpretation FG: composite_functor C D C G F ..
    interpretation FGF: composite_functor D C C F FG.map ..
    interpretation GFG: composite_functor C D D G GF.map ..

    definition \<eta>o :: "'d \<Rightarrow> 'd"
    where "\<eta>o y = \<phi> y (F y)"

    lemma \<eta>o_mapsto:
    assumes "D.ide y"
    shows "\<eta>o y \<in> D.hom y (G (F y))"
      using assms \<eta>o_def \<phi>_mapsto F.preserves_ide by simp

    lemma \<phi>_in_terms_of_\<eta>o:
    assumes "D.ide y" and "f \<in> C.hom (F y) x"
    shows "\<phi> y f = D (G f) (\<eta>o y)"
      unfolding \<eta>o_def using assms \<phi>_mapsto naturality [of f "F y" x y y y "F y"] by auto

    lemma \<phi>_F_char:
    assumes G: "g \<in> D.hom y' y"
    shows "\<phi> y' (F g) = D (\<eta>o y) g"
      using \<eta>o_def G naturality [of "F y" "F y" "F y" g y' y "F y"] \<phi>_mapsto by auto

    interpretation \<eta>: transformation_by_components D D D.map GF.map \<eta>o
      apply unfold_locales
      (* 2 *) using \<eta>o_def \<phi>_mapsto F.preserves_ide apply simp
      (* 1 *) using \<phi>_F_char \<phi>_in_terms_of_\<eta>o by fastforce

    lemma \<eta>_map_simp:
    assumes "D.ide y"
    shows "\<eta>.map y = \<phi> y (F y)"
      using assms \<eta>.map_simp_ide \<eta>o_def by simp

    definition \<epsilon>o :: "'c \<Rightarrow> 'c"
    where "\<epsilon>o x = \<psi> x (G x)"

    lemma \<epsilon>o_mapsto:
    assumes "C.ide x"
    shows "\<epsilon>o x \<in> C.hom (F (G x)) x"
      using assms \<epsilon>o_def \<psi>_mapsto G.preserves_ide by simp

    lemma \<psi>_in_terms_of_\<epsilon>o:
    assumes "C.ide x" and "g \<in> D.hom y (G x)"
    shows "\<psi> x g = C (\<epsilon>o x) (F g)"
      unfolding \<epsilon>o_def using assms \<psi>_mapsto naturality' [of x x x g y "G x" "G x"] by auto

    lemma \<psi>_G_char:
    assumes "f \<in> C.hom x x'"
    shows "\<psi> x' (G f) = C f (\<epsilon>o x)"
    proof (unfold \<epsilon>o_def)
      have 0: "C.ide x \<and> C.ide x'" using assms by auto
      thus "\<psi> x' (G f) = C f (\<psi> x (G x))"
        using 0 assms naturality' [of f x x' "G x" "G x" "G x" "G x" ] \<psi>_mapsto by auto
    qed

    interpretation \<epsilon>: transformation_by_components C C FG.map C.map \<epsilon>o
      apply unfold_locales
      (* 2 *) using \<epsilon>o_def \<psi>_mapsto G.preserves_ide apply simp
      (* 1 *) using \<psi>_G_char \<psi>_in_terms_of_\<epsilon>o by fastforce

    lemma \<epsilon>_map_simp:
    assumes "C.ide x"
    shows "\<epsilon>.map x = \<psi> x (G x)"
      using assms \<epsilon>o_def by simp

    interpretation FD: composite_functor D D C D.map F ..
    interpretation CF: composite_functor D C C F C.map ..
    interpretation GC: composite_functor C C D C.map G ..
    interpretation DG: composite_functor C D D G D.map ..

    interpretation F\<eta>: horizontal_composite D D C D.map "G o F" F F \<eta>.map F ..
    interpretation F\<eta>: natural_transformation D C F "F o G o F" "F o \<eta>.map"
      apply unfold_locales using F\<eta>.is_extensional F\<eta>.is_natural_1 F\<eta>.is_natural_2 by auto

    interpretation \<epsilon>F: horizontal_composite D C C F F "F o G" C.map F \<epsilon>.map ..
    interpretation \<epsilon>F: natural_transformation D C "F o G o F" F "\<epsilon>.map o F"
      apply unfold_locales using \<epsilon>F.is_extensional \<epsilon>F.is_natural_1 \<epsilon>F.is_natural_2 by auto

    interpretation \<eta>G: horizontal_composite C D D G G D.map "G o F" G \<eta>.map ..
    interpretation \<eta>G: natural_transformation C D G "G o F o G" "\<eta>.map o G"
      apply unfold_locales using \<eta>G.is_extensional \<eta>G.is_natural_1 \<eta>G.is_natural_2 by auto

    interpretation G\<epsilon>: horizontal_composite C C D "F o G" C.map G G \<epsilon>.map G ..
    interpretation G\<epsilon>: natural_transformation C D "G o F o G" G "G o \<epsilon>.map"
      apply unfold_locales using G\<epsilon>.is_extensional G\<epsilon>.is_natural_1 G\<epsilon>.is_natural_2 by auto

    interpretation \<epsilon>FoF\<eta>: vertical_composite D C F "F o G o F" F "F o \<eta>.map" "\<epsilon>.map o F" ..
    interpretation G\<epsilon>o\<eta>G: vertical_composite C D G "G o F o G" G "\<eta>.map o G" "G o \<epsilon>.map" ..

    lemma unit_counit_F:
    assumes "D.ide y"
    shows "F y = C (\<epsilon>o (F y)) (F (\<eta>o y))"
      using assms \<psi>_in_terms_of_\<epsilon>o [of "F y" "\<phi> y (F y)" y ] \<eta>o_def \<psi>_\<phi> \<eta>o_mapsto F.preserves_ide
      by auto

    lemma unit_counit_G:
    assumes "C.ide x"
    shows "G x = D (G (\<epsilon>o x)) (\<eta>o (G x))"
      using assms \<phi>_in_terms_of_\<eta>o [of "G x" "\<psi> x (G x)" x ] \<epsilon>o_def \<phi>_\<psi> \<epsilon>o_mapsto G.preserves_ide
      by auto

    theorem induces_unit_counit_adjunction:
    shows "unit_counit_adjunction C D F G \<eta>.map \<epsilon>.map"
    proof
      show "\<epsilon>FoF\<eta>.map = F"
      proof (intro NaturalTransformation.eqI)
        show "natural_transformation D C F F \<epsilon>FoF\<eta>.map"
          using \<epsilon>FoF\<eta>.is_natural_transformation by auto
        show "natural_transformation D C F F F" ..
        show "\<And>y. D.ide y \<Longrightarrow> \<epsilon>FoF\<eta>.map y = F y"
          using \<epsilon>FoF\<eta>.map_simp_2 unit_counit_F by auto
      qed
      show "G\<epsilon>o\<eta>G.map = G"
      proof (intro NaturalTransformation.eqI)
        show "natural_transformation C D G G G\<epsilon>o\<eta>G.map"
          using G\<epsilon>o\<eta>G.is_natural_transformation by auto
        show "natural_transformation C D G G G" ..
        show "\<And>x. C.ide x \<Longrightarrow> G\<epsilon>o\<eta>G.map x = G x"
          using G\<epsilon>o\<eta>G.map_simp_1 unit_counit_G by auto
      qed
    qed

    text{*
      From the defined @{term \<eta>} and @{term \<epsilon>} we can recover the original @{term \<phi>} and @{term \<psi>}.
     *}

    lemma \<phi>_in_terms_of_\<eta>:
    assumes "D.ide y" and "f \<in> C.hom (F y) x"
    shows "\<phi> y f = D (G f) (\<eta>.map y)"
      using assms by (simp add: \<phi>_in_terms_of_\<eta>o)

    lemma \<psi>_in_terms_of_\<epsilon>:
    assumes "C.ide x" and "g \<in> D.hom y (G x)"
    shows "\<psi> x g = C (\<epsilon>.map x) (F g)"
      using assms by (simp add: \<psi>_in_terms_of_\<epsilon>o)

    abbreviation \<eta> :: "'d \<Rightarrow> 'd" where "\<eta> \<equiv> \<eta>.map"
    abbreviation \<epsilon> :: "'c \<Rightarrow> 'c" where "\<epsilon> \<equiv> \<epsilon>.map"

    lemma \<eta>_is_natural_transformation:
    shows "natural_transformation D D D.map GF.map \<eta>" ..

    lemma \<epsilon>_is_natural_transformation:
    shows "natural_transformation C C FG.map C.map \<epsilon>" ..

  end

  section "Meta-Adjunctions Induce Left and Right Adjoint Functors"

  context meta_adjunction
  begin

    interpretation unit_counit_adjunction C D F G \<eta> \<epsilon>
      using induces_unit_counit_adjunction by auto

    lemma has_terminal_arrows_from_functor:
    assumes x: "C.ide x"
    shows "terminal_arrow_from_functor D C F (G x) x (\<epsilon> x)"
    and "\<And>y' f. arrow_from_functor D C F y' x f
                   \<Longrightarrow> terminal_arrow_from_functor.the_coext D C F (G x) (\<epsilon> x) y' f = \<phi> y' f"
    proof -
      interpret \<epsilon>x: arrow_from_functor D C F "G x" x "\<epsilon> x"
        apply unfold_locales
        using x \<epsilon>.preserves_hom G.preserves_ide by auto
      have 1: "\<And>y' f. arrow_from_functor D C F y' x f \<Longrightarrow>
                      \<epsilon>x.is_coext y' f (\<phi> y' f) \<and> (\<forall>g'. \<epsilon>x.is_coext y' f g' \<longrightarrow> g' = \<phi> y' f)"
      proof
        fix y' :: 'd and f :: 'c
        assume f: "arrow_from_functor D C F y' x f"
        let ?g = "\<phi> y' f"
        show "\<epsilon>x.is_coext y' f ?g"
        proof -
          have *: "?g \<in> D.hom y' (G x)"
            using f \<phi>_mapsto [of y' f x] arrow_from_functor.arrow by fast
          then have "C (\<epsilon> x) (F ?g) = f"
            using f x \<psi>_\<phi> [of y' f x] \<psi>_in_terms_of_\<epsilon> arrow_from_functor.arrow by fastforce
          with * show ?thesis using \<epsilon>x.is_coext_def by auto
        qed
        have "\<And>g'. \<epsilon>x.is_coext y' f g' \<Longrightarrow> g' = ?g"
        proof -
          fix g' :: 'd
          assume g': "\<epsilon>x.is_coext y' f g'"
          show "g' = ?g"
          proof -
            have "\<And>g y' x. \<lbrakk> C.ide x; g \<in> D.hom y' (G x) \<rbrakk> \<Longrightarrow> C (\<psi> x (G x)) (F g) = \<psi> x g"
              using \<epsilon>o_def \<psi>_in_terms_of_\<epsilon>o by (metis (no_types))
            thus ?thesis
              using g' x \<epsilon>_map_simp \<phi>_\<psi> [of x g' y'] \<epsilon>x.is_coext_def [of y' f g'] 
              by fastforce
          qed
        qed
        thus "\<forall>g'. \<epsilon>x.is_coext y' f g' \<longrightarrow> g' = ?g" by blast
      qed
      interpret \<epsilon>x: terminal_arrow_from_functor D C F "G x" x "\<epsilon> x"
        apply unfold_locales using 1 by blast
      show "terminal_arrow_from_functor D C F (G x) x (\<epsilon> x)" ..
      show "\<And>y' f. arrow_from_functor D C F y' x f \<Longrightarrow> \<epsilon>x.the_coext y' f = \<phi> y' f"
        using 1 \<epsilon>x.the_coext_def by auto
    qed

    lemma has_left_adjoint_functor:
    shows "left_adjoint_functor D C F"
      apply unfold_locales using has_terminal_arrows_from_functor by auto

  end

  context meta_adjunction
  begin

    interpretation unit_counit_adjunction C D F G \<eta> \<epsilon>
      using induces_unit_counit_adjunction by auto

    lemma has_initial_arrows_to_functor:
    assumes y: "D.ide y"
    shows "initial_arrow_to_functor C D G y (F y) (\<eta> y)"
    and "\<And>x' g. arrow_to_functor C D G y x' g \<Longrightarrow>
                  initial_arrow_to_functor.the_ext C D G (F y) (\<eta> y) x' g = \<psi> x' g"
    proof -
      interpret \<eta>y: arrow_to_functor C D G y "F y" "\<eta> y"
        apply unfold_locales using y by simp
      have 1: "\<And>x' g. arrow_to_functor C D G y x' g \<Longrightarrow>
                         \<eta>y.is_ext x' g (\<psi> x' g) \<and> (\<forall>f'. \<eta>y.is_ext x' g f' \<longrightarrow> f' = \<psi> x' g)"
      proof
        fix x' :: 'c and g :: 'd
        assume g: "arrow_to_functor C D G y x' g"
        let ?f = "\<psi> x' g"
        show "\<eta>y.is_ext x' g ?f"
        proof -
          have *: "?f \<in> C.hom (F y) x'"
            using g \<psi>_mapsto [of x' g y] arrow_to_functor.arrow by fastforce
          then have "D (G ?f) (\<eta> y) = g"
            using g y \<phi>_\<psi> [of x' g] \<phi>_in_terms_of_\<eta> arrow_to_functor.arrow by fastforce
          with * show ?thesis using \<eta>y.is_ext_def by auto
        qed
        have "\<And>f'. \<eta>y.is_ext x' g f' \<Longrightarrow> f' = \<psi> x' g"
        proof -
          fix f' :: 'c
          assume f': "\<eta>y.is_ext x' g f'"
          show "f' = ?f"
          proof -
            have "\<And>f y x'. \<lbrakk> D.ide y; f \<in> C.hom (F y) x' \<rbrakk> \<Longrightarrow> D (G f) (\<phi> y (F y)) = \<phi> y f"
              by (metis (no_types) \<eta>o_def \<phi>_in_terms_of_\<eta>o)
            thus ?thesis
              using f' y \<eta>_map_simp \<psi>_\<phi> \<eta>y.is_ext_def by force
            qed
        qed
        thus "\<forall>f'. \<eta>y.is_ext x' g f' \<longrightarrow> f' = \<psi> x' g" by blast
      qed
      interpret \<eta>y: initial_arrow_to_functor C D G y "F y" "\<eta> y"
        apply unfold_locales using 1 by blast
      show "initial_arrow_to_functor C D G y (F y) (\<eta> y)" ..
      show "\<And>x' g. arrow_to_functor C D G y x' g \<Longrightarrow> \<eta>y.the_ext x' g = \<psi> x' g"
        using 1 \<eta>y.the_ext_def by auto
    qed

    lemma has_right_adjoint_functor:
    shows "right_adjoint_functor C D G"
      apply unfold_locales using has_initial_arrows_to_functor by auto

  end

  section "Unit/Counit Adjunctions Induce Meta-Adjunctions"

  context unit_counit_adjunction
  begin

    definition \<phi> :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    where "\<phi> y h = D (G h) (\<eta> y)"

    definition \<psi> :: "'c \<Rightarrow> 'd \<Rightarrow> 'c"
    where "\<psi> x h = C (\<epsilon> x) (F h)"

    interpretation meta_adjunction C D F G \<phi> \<psi>
    proof
      fix x :: 'c and y :: 'd and f :: 'c
      assume y: "D.ide y" and f: "f \<in> C.hom (F y) x"
      show 0: "\<phi> y f \<in> D.hom y (G x)"
        using f y G.preserves_hom \<eta>.preserves_hom \<phi>_def D.ideD by simp
      show "\<psi> x (\<phi> y f) = f"
      proof -
        have "\<psi> x (\<phi> y f) = C (\<epsilon> x) (F (D (G f) (\<eta> y)))"
          using \<phi>_def \<psi>_def by auto
        also have "... = C (C (\<epsilon> x) (F (G f))) (F (\<eta> y))"
          using y f by auto
        also have "... = C (C f (\<epsilon> (F y))) (F (\<eta> y))"
          using y f \<epsilon>.is_natural_1 \<epsilon>.is_natural_2 by fastforce
        also have "... = C f (C (\<epsilon> (F y)) (F (\<eta> y)))"
          using y f by simp
        also have "... = f"
        proof -
          have "C (\<epsilon> (F y)) (F (\<eta> y)) = \<epsilon>FoF\<eta>.map y"
            using y \<epsilon>FoF\<eta>.map_simp_2 by simp
          thus ?thesis using y f triangle_F by auto
        qed
        finally show ?thesis by auto
      qed
      next
      fix x :: 'c and y :: 'd and g :: 'd
      assume x: "C.ide x" and g: "g \<in> D.hom y (G x)"
      show "\<psi> x g \<in> C.hom (F y) x" using g x \<psi>_def by simp
      show "\<phi> y (\<psi> x g) = g"
      proof -
        have "\<phi> y (\<psi> x g) = D (D (G (\<epsilon> x)) (\<eta> (G x))) g"
          using g x \<phi>_def \<psi>_def \<eta>.is_natural_1 \<eta>.is_natural_2 by fastforce
        also have "... = g"
        proof -
          have "D (G (\<epsilon> x)) (\<eta> (G x)) = G\<epsilon>o\<eta>G.map x"
            using x G\<epsilon>o\<eta>G.map_simp_1 by force
          thus ?thesis using x g triangle_G by auto
        qed
        finally show ?thesis by auto
      qed
      next
      fix f :: 'c and g :: 'd and h :: 'c and x :: 'c and x' :: 'c and y :: 'd and y' :: 'd
      assume f: "f \<in> C.hom x x'" and g: "g \<in> D.hom y' y" and h: "h \<in> C.hom (F y) x"
      show "\<phi> y' (C f (C h (F g))) = D (G f) (D (\<phi> y h) g)"
        using f g h \<phi>_def \<eta>.is_natural_1 \<eta>.is_natural_2 by force
    qed

    theorem induces_meta_adjunction:
    shows "meta_adjunction C D F G \<phi> \<psi>" ..

    text{*
      From the defined @{term \<phi>} and @{term \<psi>} we can recover the original @{term \<eta>} and @{term \<epsilon>}.
    *}

    lemma \<eta>_in_terms_of_\<phi>:
    assumes "D.ide y"
    shows "\<eta> y = \<phi> y (F y)"
      using assms by (simp add: \<phi>_def)

    lemma \<epsilon>_in_terms_of_\<psi>:
    assumes "C.ide x"
    shows "\<epsilon> x = \<psi> x (G x)"
      using assms by (simp add: \<psi>_def)

  end

  section "Left and Right Adjoint Functors Induce Meta-Adjunctions"

  text{*
    A left adjoint functor induces a meta-adjunction, modulo the choice of a
    right adjoint and counit.
  *}

  context left_adjoint_functor
  begin

    definition Go :: "'c \<Rightarrow> 'd"
    where "Go a = (SOME b. \<exists>e. terminal_arrow_from_functor D C F b a e)"

    definition \<epsilon>o :: "'c \<Rightarrow> 'c"
    where "\<epsilon>o a = (SOME e. terminal_arrow_from_functor D C F (Go a) a e)"

    lemma Go_\<epsilon>o_terminal:
    assumes "\<exists>b e. terminal_arrow_from_functor D C F b a e"
    shows "terminal_arrow_from_functor D C F (Go a) a (\<epsilon>o a)"
      using assms Go_def \<epsilon>o_def
            someI_ex [of "\<lambda>b. \<exists>e. terminal_arrow_from_functor D C F b a e"]
            someI_ex [of "\<lambda>e. terminal_arrow_from_functor D C F (Go a) a e"]
      by simp

    text{*
      The right adjoint @{term G} to @{term F} takes each arrow @{term f} of @{term C}
      to the unique @{term D}-coextension of @{term "C f (\<epsilon>o (C.dom f))"}
      along @{term "\<epsilon>o (C.cod f)"}.
    *}

    definition G :: "'c \<Rightarrow> 'd"
    where "G f = (if C.arr f then
                     terminal_arrow_from_functor.the_coext D C F (Go (C.cod f)) (\<epsilon>o (C.cod f))
                                  (Go (C.dom f)) (C f (\<epsilon>o (C.dom f)))
                  else D.null)"

    lemma G_ide:
    assumes "C.ide x"
    shows "G x = Go x"
    proof -
      interpret terminal_arrow_from_functor D C F "Go x" x "\<epsilon>o x"
        using assms ex_terminal_arrow Go_\<epsilon>o_terminal by blast
      have 1: "arrow_from_functor D C F (Go x) x (\<epsilon>o x)" ..
      have "is_coext (Go x) (\<epsilon>o x) (Go x)"
        using arrow D.ideD is_coext_def by auto
      hence "Go x = the_coext (Go x) (\<epsilon>o x)" using 1 the_coext_unique by blast
      moreover have "\<epsilon>o x = C x (\<epsilon>o (C.dom x))" using assms arrow by simp
      ultimately show ?thesis using assms G_def C.cod_dom C.ideD by metis
    qed

    lemma G_is_functor:
    shows "functor C D G"
    proof
      fix f :: 'c
      assume "\<not>C.arr f"
      thus "G f = D.null" using G_def by auto
      next
      fix f :: 'c
      assume f: "C.arr f"
      let ?x = "C.dom f"
      let ?x' = "C.cod f"
      interpret x\<epsilon>: terminal_arrow_from_functor D C F "Go ?x" "?x" "\<epsilon>o ?x"
        using f ex_terminal_arrow Go_\<epsilon>o_terminal by simp
      interpret x'\<epsilon>: terminal_arrow_from_functor D C F "Go ?x'" "?x'" "\<epsilon>o ?x'"
        using f ex_terminal_arrow Go_\<epsilon>o_terminal by simp
      have 1: "arrow_from_functor D C F (Go ?x) ?x' (C f (\<epsilon>o ?x))"
        apply unfold_locales using f x\<epsilon>.arrow by simp
      have "G f = x'\<epsilon>.the_coext (Go ?x) (C f (\<epsilon>o ?x))" using f G_def by simp
      hence Gf: "G f \<in> D.hom (Go ?x) (Go ?x') \<and> C f (\<epsilon>o ?x) = C (\<epsilon>o ?x') (F (G f))"
        using 1 x'\<epsilon>.the_coext_prop by simp
      show "D.arr (G f)" using Gf by auto
      show "D.dom (G f) = G ?x" using f Gf G_ide by auto
      show "D.cod (G f) = G ?x'" using f Gf G_ide by auto
      fix f' :: 'c
      assume f': "f' \<in> C.hom (C.cod f) (C.cod f')"
      let ?x'' = "C.cod f'"
      interpret x''\<epsilon>: terminal_arrow_from_functor D C F "Go ?x''" "?x''" "\<epsilon>o ?x''"
        using f' ex_terminal_arrow Go_\<epsilon>o_terminal by simp
      have 2: "arrow_from_functor D C F (Go ?x') ?x'' (C f' (\<epsilon>o ?x'))"
        apply unfold_locales using f' x'\<epsilon>.arrow by simp
      have "G f' = x''\<epsilon>.the_coext (Go ?x') (C f' (\<epsilon>o ?x'))"
        using f' G_def by simp
      hence Gf': "G f' \<in> D.hom (Go ?x') (Go ?x'') \<and> C f' (\<epsilon>o ?x') = C (\<epsilon>o ?x'') (F (G f'))"
        using 2 x''\<epsilon>.the_coext_prop by simp
      show "G (C f' f) = D (G f') (G f)"
      proof -
        have "x''\<epsilon>.is_coext (Go ?x) (C (C f' f) (\<epsilon>o ?x)) (D (G f') (G f))"
        proof -
          have "D (G f') (G f) \<in> D.hom (Go ?x) (Go ?x'')" using 1 2 Gf Gf' by simp
          moreover have "C (C f' f) (\<epsilon>o ?x) = C (\<epsilon>o ?x'') (F (D (G f') (G f)))"
          proof -
            have "C (C f' f) (\<epsilon>o ?x) = C f' (C f (\<epsilon>o ?x))"
              using f f' x\<epsilon>.arrow by simp
            also have "... = C (C f' (\<epsilon>o ?x')) (F (G f))"
              using f' Gf x'\<epsilon>.arrow preserves_cod by fastforce
            also have "... = C (\<epsilon>o ?x'') (F (D (G f') (G f)))"
              using Gf Gf' x''\<epsilon>.arrow by simp
            finally show ?thesis by auto
          qed
          ultimately show ?thesis using x''\<epsilon>.is_coext_def by auto
        qed
        moreover have "arrow_from_functor D C F (Go ?x) ?x'' (C (C f' f) (\<epsilon>o ?x))"
          apply unfold_locales using f f' x\<epsilon>.arrow by simp
        ultimately show ?thesis
          using f f' G_def x''\<epsilon>.the_coext_unique C.arr_comp C.cod_comp C.dom_comp by auto
      qed
    qed

    interpretation G: "functor" C D G using G_is_functor by auto

    lemma G_simp:
    assumes "C.arr f"
    shows "G f = terminal_arrow_from_functor.the_coext D C F (Go (C.cod f)) (\<epsilon>o (C.cod f))
                                                             (Go (C.dom f)) (C f (\<epsilon>o (C.dom f)))"
      using assms G_def by simp

    interpretation idC: identity_functor C ..
    interpretation GF: composite_functor C D C G F ..

    interpretation \<epsilon>: transformation_by_components C C GF.map C.map \<epsilon>o
    proof
      fix x :: 'c
      assume x: "C.ide x"
      show "\<epsilon>o x \<in> C.hom (GF.map x) (C.map x)"
      proof -
        interpret terminal_arrow_from_functor D C F "Go x" x "\<epsilon>o x"
          using x Go_\<epsilon>o_terminal ex_terminal_arrow by simp
        have "G x = Go x" using x G_ide by fast
        thus ?thesis using x arrow by simp
      qed
      next
      fix f :: 'c
      assume f: "C.arr f"
      show "C (\<epsilon>o (C.cod f)) (GF.map f) = C (C.map f) (\<epsilon>o (C.dom f))"
      proof -
        let ?x = "C.dom f"
        let ?x' = "C.cod f"
        interpret x\<epsilon>: terminal_arrow_from_functor D C F "Go ?x" ?x "\<epsilon>o ?x"
          using f Go_\<epsilon>o_terminal ex_terminal_arrow by simp
        interpret x'\<epsilon>: terminal_arrow_from_functor D C F "Go ?x'" ?x' "\<epsilon>o ?x'"
          using f Go_\<epsilon>o_terminal ex_terminal_arrow by simp
        have 1: "arrow_from_functor D C F (Go ?x) ?x' (C f (\<epsilon>o ?x))"
          apply unfold_locales using f x\<epsilon>.arrow by simp
        have "G f = x'\<epsilon>.the_coext (Go ?x) (C f (\<epsilon>o ?x))"
          using f G_simp by blast
        hence "x'\<epsilon>.is_coext (Go ?x) (C f (\<epsilon>o ?x)) (G f)"
          using 1 x'\<epsilon>.the_coext_prop x'\<epsilon>.is_coext_def by auto
        thus ?thesis
          using x'\<epsilon>.is_coext_def by (simp add: x'\<epsilon>.is_coext_def f)
      qed
    qed

    definition \<psi>
    where "\<psi> x h = C (\<epsilon>.map x) (F h)"

    lemma \<psi>_mapsto:
    assumes "C.ide x" and "g \<in> D.hom y (G x)"
    shows "\<psi> x g \<in> C.hom (F y) x"
      unfolding \<psi>_def using assms \<epsilon>.maps_ide_in_hom by auto

    lemma \<psi>_natural:
    assumes f: "f \<in> C.hom x x'" and g: "g \<in> D.hom y' y" and h: "h \<in> D.hom y (G x)"
    shows "C f (C (\<psi> x h) (F g)) = \<psi> x' (D (D (G f) h) g)"
    proof -
      have "C f (C (\<psi> x h) (F g)) = C f (C (C (\<epsilon>.map x) (F h)) (F g))"
        unfolding \<psi>_def by auto
      also have "... = C (C f (\<epsilon>.map x)) (C (F h) (F g))"
        using f g h \<epsilon>.preserves_hom [of x x x] by force
      also have "... = C (C f (\<epsilon>.map x)) (F (D h g))"
        using g h by simp
      also have "... = C (C (\<epsilon>.map x') (F (G f))) (F (D h g))"
        using f \<epsilon>.is_natural_1 \<epsilon>.is_natural_2 by auto
      also have "... = C (\<epsilon>.map x') (F (D (D (G f) h) g))"
        using f g h \<epsilon>.preserves_hom [of x' x' x'] by force
      also have "... = \<psi> x' (D (D (G f) h) g)"
        unfolding \<psi>_def by auto
      finally show ?thesis by auto
    qed

    lemma \<psi>_inverts_coext:
    assumes x: "C.ide x" and g: "g \<in> D.hom y (G x)"
    shows "arrow_from_functor.is_coext D C F (G x) (\<epsilon>.map x) y (\<psi> x g) g"
    proof -
      interpret x\<epsilon>: arrow_from_functor D C F "G x" x "\<epsilon>.map x"
        apply unfold_locales using x \<epsilon>.maps_ide_in_hom by auto
      show "x\<epsilon>.is_coext y (\<psi> x g) g"
        using x g \<psi>_def x\<epsilon>.is_coext_def G_ide by blast
    qed

    lemma \<psi>_invertible:
    assumes y: "D.ide y" and f: "f \<in> C.hom (F y) x"
    shows "\<exists>!g. g \<in> D.hom y (G x) \<and> \<psi> x g = f"
    proof
      have x: "C.ide x" using f by auto
      interpret x\<epsilon>: terminal_arrow_from_functor D C F "Go x" x "\<epsilon>o x"
        using x ex_terminal_arrow Go_\<epsilon>o_terminal by auto
      have 1: "arrow_from_functor D C F y x f"
        apply unfold_locales using y f apply auto done
      let ?g = "x\<epsilon>.the_coext y f"
      have "\<psi> x ?g = f"
        using 1 x y \<psi>_def x\<epsilon>.the_coext_prop G_ide \<psi>_inverts_coext x\<epsilon>.is_coext_def by simp
      thus "?g \<in> D.hom y (G x) \<and> \<psi> x ?g = f"
        using 1 x x\<epsilon>.the_coext_prop G_ide by simp
      show "\<And>g'. g' \<in> D.hom y (G x) \<and> \<psi> x g' = f \<Longrightarrow> g' = ?g"
        using 1 x y \<psi>_inverts_coext G_ide x\<epsilon>.the_coext_unique by force
    qed

    definition \<phi>
    where "\<phi> y f = (THE g. g \<in> D.hom y (G (C.cod f)) \<and> \<psi> (C.cod f) g = f)"

    lemma \<phi>_mapsto:
    assumes "D.ide y" and "f \<in> C.hom (F y) x"
    shows "\<phi> y f \<in> D.hom y (G x)"
      using assms \<psi>_invertible \<phi>_def theI' [of "\<lambda>g. g \<in> D.hom y (G x) \<and> \<psi> x g = f"]
      by simp

    lemma \<phi>_\<psi>:
    assumes "C.ide x" and "g \<in> D.hom y (G x)"
    shows "\<phi> y (\<psi> x g) = g"
    proof -
      have "C.cod (\<psi> x g) = x" using assms \<psi>_mapsto by fast
      hence "\<phi> y (\<psi> x g) = (THE g'. g' \<in> D.hom y (G x) \<and> \<psi> x g' = \<psi> x g)"
        using \<phi>_def by auto
      moreover have "\<exists>!g'. g' \<in> D.hom y (G x) \<and> \<psi> x g' = \<psi> x g"
        using assms \<psi>_mapsto \<psi>_invertible D.ide_dom by blast
      moreover have "g \<in> D.hom y (G x) \<and> \<psi> x g = \<psi> x g" using assms(2) by auto
      ultimately show "\<phi> y (\<psi> x g) = g" by auto
    qed

    lemma \<psi>_\<phi>:
    assumes "D.ide y" and "f \<in> C.hom (F y) x"
    shows "\<psi> x (\<phi> y f) = f"
      using assms \<psi>_invertible \<phi>_def theI' [of "\<lambda>g. g \<in> D.hom y (G x) \<and> \<psi> x g = f"]
      by simp

    lemma \<phi>_natural:
    assumes "f \<in> C.hom x x'" and "g \<in> D.hom y' y" and "h \<in> C.hom (F y) x"
    shows "\<phi> y' (C f (C h (F g))) = D (D (G f) (\<phi> y h)) g"
      using assms \<psi>_natural [of f x x' g y' y "\<phi> y h"] \<phi>_mapsto \<psi>_mapsto \<phi>_\<psi> \<psi>_\<phi>
      by force

    theorem induces_meta_adjunction:
    shows "meta_adjunction C D F G \<phi> \<psi>"
      apply (unfold_locales)
      using \<phi>_mapsto \<psi>_mapsto \<phi>_\<psi> \<psi>_\<phi> \<phi>_natural G.preserves_dom by auto

  end

  text{*
    A right adjoint functor induces a meta-adjunction, modulo the choice of a
    left adjoint and unit.
  *}

  context right_adjoint_functor
  begin

    definition Fo :: "'d \<Rightarrow> 'c"
    where "Fo y = (SOME x. \<exists>u. initial_arrow_to_functor C D G y x u)"

    definition \<eta>o :: "'d \<Rightarrow> 'd"
    where "\<eta>o y = (SOME u. initial_arrow_to_functor C D G y (Fo y) u)"

    lemma Fo_\<eta>o_initial:
    assumes "\<exists>x u. initial_arrow_to_functor C D G y x u"
    shows "initial_arrow_to_functor C D G y (Fo y) (\<eta>o y)"
      using assms Fo_def \<eta>o_def
            someI_ex [of "\<lambda>x. \<exists>u. initial_arrow_to_functor C D G y x u"]
            someI_ex [of "\<lambda>u. initial_arrow_to_functor C D G y (Fo y) u"]
      by simp

    text{*
      The left adjoint @{term F} to @{term g} takes each arrow @{term g} of @{term D}
      to the unique @{term C}-extension of @{term "D (\<eta>o (D.cod g)) g"}
      along @{term "\<eta>o (D.dom g)"}.
    *}

    definition F :: "'d \<Rightarrow> 'c"
    where "F g = (if D.arr g then
                     initial_arrow_to_functor.the_ext C D G (Fo (D.dom g)) (\<eta>o (D.dom g))
                                  (Fo (D.cod g)) (D (\<eta>o (D.cod g)) g)
                  else C.null)"

    lemma F_ide:
    assumes "D.ide y"
    shows "F y = Fo y"
    proof -
      interpret initial_arrow_to_functor C D G y "Fo y" "\<eta>o y"
        using assms initial_arrows_exist Fo_\<eta>o_initial by blast
      have 1: "arrow_to_functor C D G y (Fo y) (\<eta>o y)" ..
      have "is_ext (Fo y) (\<eta>o y) (Fo y)"
        using arrow is_ext_def by simp
      hence "Fo y = the_ext (Fo y) (\<eta>o y)" using 1 the_ext_unique by blast
      moreover have "\<eta>o y = D (\<eta>o (D.cod y)) y" using assms arrow by auto
      ultimately show ?thesis
        using assms F_def D.dom_cod D.ideD(1) D.ideD(3) by metis
    qed

    lemma F_is_functor:
    shows "functor D C F"
    proof
      fix g :: 'd
      assume "\<not>D.arr g"
      thus "F g = C.null" using F_def by auto
      next
      fix g :: 'd
      assume g: "D.arr g"
      let ?y = "D.dom g"
      let ?y' = "D.cod g"
      interpret y\<eta>: initial_arrow_to_functor C D G ?y "Fo ?y" "\<eta>o ?y"
        using g initial_arrows_exist Fo_\<eta>o_initial by simp
      interpret y'\<eta>: initial_arrow_to_functor C D G ?y' "Fo ?y'" "\<eta>o ?y'"
        using g initial_arrows_exist Fo_\<eta>o_initial by simp
      have 1: "arrow_to_functor C D G ?y (Fo ?y') (D (\<eta>o ?y') g)"
        apply unfold_locales using g y'\<eta>.arrow by simp
      have "F g = y\<eta>.the_ext (Fo ?y') (D (\<eta>o ?y') g)" using g F_def by simp
      hence Fg: "F g \<in> C.hom (Fo ?y) (Fo ?y') \<and> D (\<eta>o ?y') g = D (G (F g)) (\<eta>o ?y)"
        using 1 y\<eta>.the_ext_prop by simp
      show "C.arr (F g)" using Fg by auto
      show "C.dom (F g) = F ?y" using Fg g F_ide by auto
      show "C.cod (F g) = F ?y'" using Fg g F_ide by auto
      fix g' :: 'd
      assume g': "g' \<in> D.hom (D.cod g) (D.cod g')"
      let ?y'' = "D.cod g'"
      interpret y''\<eta>: initial_arrow_to_functor C D G ?y'' "Fo ?y''" "\<eta>o ?y''"
        using g' initial_arrows_exist Fo_\<eta>o_initial by simp
      have 2: "arrow_to_functor C D G ?y' (Fo ?y'') (D (\<eta>o ?y'') g')"
        apply unfold_locales using g' y''\<eta>.arrow by simp
      have "F g' = y'\<eta>.the_ext (Fo ?y'') (D (\<eta>o ?y'') g')"
        using g' F_def by simp
      hence Fg': "F g' \<in> C.hom (Fo ?y') (Fo ?y'') \<and> D (\<eta>o ?y'') g' = D (G (F g')) (\<eta>o ?y')"
        using 2 y'\<eta>.the_ext_prop by simp
      show "F (D g' g) = C (F g') (F g)"
      proof -
        have "y\<eta>.is_ext (Fo ?y'') (D (\<eta>o ?y'') (D g' g)) (C (F g') (F g))"
        proof -
          have "C (F g') (F g) \<in> C.hom (Fo ?y) (Fo ?y'')" using 1 2 Fg Fg' by simp
          moreover have "D (\<eta>o ?y'') (D g' g) = D (G (C (F g') (F g))) (\<eta>o ?y)"
          proof -
            have "D (\<eta>o ?y'') (D g' g) = D (D (G (F g')) (\<eta>o ?y')) g"
              using Fg' g g' y''\<eta>.arrow
              by (metis (mono_tags, lifting) D.comp_assoc mem_Collect_eq)
            also have "... = D (G (F g')) (D (\<eta>o ?y') g)"
              using g y'\<eta>.arrow Fg' y'\<eta>.arrow preserves_dom by fastforce
            also have "... = D (G (C (F g') (F g))) (\<eta>o ?y)"
              using Fg Fg' y\<eta>.arrow by simp
            finally show ?thesis by auto
          qed
          ultimately show ?thesis using y\<eta>.is_ext_def by auto
        qed
        moreover have "arrow_to_functor C D G ?y (Fo ?y'') (D (\<eta>o ?y'') (D g' g))"
          apply unfold_locales using g g' y''\<eta>.arrow by simp
        ultimately show ?thesis
          using g g' F_def y\<eta>.the_ext_unique D.arr_comp D.dom_comp D.cod_comp by auto
      qed
    qed

    interpretation F: "functor" D C F using F_is_functor by auto

    lemma F_simp:
    assumes "D.arr g"
    shows "F g = initial_arrow_to_functor.the_ext C D G (Fo (D.dom g)) (\<eta>o (D.dom g))
                                                        (Fo (D.cod g)) (D (\<eta>o (D.cod g)) g)"
      using assms F_def by simp

    interpretation FG: composite_functor D C D F G ..

    interpretation \<eta>: transformation_by_components D D D.map FG.map \<eta>o
    proof
      fix y :: 'd
      assume y: "D.ide y"
      show "\<eta>o y \<in> D.hom (D.map y) (FG.map y)"
      proof -
        interpret initial_arrow_to_functor C D G y "Fo y" "\<eta>o y"
          using y Fo_\<eta>o_initial initial_arrows_exist by simp
        have "F y = Fo y" using y F_ide by fast
        thus ?thesis using y arrow by simp
      qed
      next
      fix g :: 'd
      assume g: "D.arr g"
      show "D (\<eta>o (D.cod g)) (D.map g) = D (FG.map g) (\<eta>o (D.dom g))"
      proof -
        let ?y = "D.dom g"
        let ?y' = "D.cod g"
        interpret y\<eta>: initial_arrow_to_functor C D G ?y "Fo ?y" "\<eta>o ?y"
          using g Fo_\<eta>o_initial initial_arrows_exist by simp
        interpret y'\<eta>: initial_arrow_to_functor C D G ?y' "Fo ?y'" "\<eta>o ?y'"
          using g Fo_\<eta>o_initial initial_arrows_exist by simp
        have "arrow_to_functor C D G ?y (Fo ?y') (D (\<eta>o ?y') g)"
          apply unfold_locales using g y'\<eta>.arrow by simp
        moreover have "F g = y\<eta>.the_ext (Fo ?y') (D (\<eta>o ?y') g)"
          using g F_simp by blast
        ultimately have "y\<eta>.is_ext (Fo ?y') (D (\<eta>o ?y') g) (F g)"
          using y\<eta>.the_ext_prop y\<eta>.is_ext_def by auto
        thus ?thesis
          using y\<eta>.is_ext_def by (simp add: y\<eta>.is_ext_def g)
      qed
    qed

    definition \<phi>
    where "\<phi> y h = D (G h) (\<eta>.map y)"

    lemma \<phi>_mapsto:
    assumes y: "D.ide y" and f: "f \<in> C.hom (F y) x"
    shows "\<phi> y f \<in> D.hom y (G x)"
      unfolding \<phi>_def using assms \<eta>.maps_ide_in_hom by auto

    lemma \<phi>_natural:
    assumes f: "f \<in> C.hom x x'" and g: "g \<in> D.hom y' y" and h: "h \<in> C.hom (F y) x"
    shows "\<phi> y' (C f (C h (F g))) = D (D (G f) (\<phi> y h)) g"
    proof -
      have "D (D (G f) (\<phi> y h)) g = D (D (G f) (D (G h) (\<eta>.map y))) g"
        unfolding \<phi>_def by auto
      also have "... = D (D (G f) (G h)) (D (\<eta>.map y) g)"
        using f g h \<eta>.preserves_hom [of y y y] by force
      also have "... = D (G (C f h)) (D (G (F g)) (\<eta>.map y'))"
        using f g h \<eta>.is_natural_1 \<eta>.is_natural_2 preserves_comp by auto
      also have "... = D (G (C f (C h (F g)))) (\<eta>.map y')"
        using f g h \<eta>.preserves_hom [of y' y' y'] by force
      also have "... = \<phi> y' (C f (C h (F g)))"
        unfolding \<phi>_def by auto
      finally show ?thesis by auto
    qed

    lemma \<phi>_inverts_ext:
    assumes y: "D.ide y" and f: "f \<in> C.hom (F y) x"
    shows "arrow_to_functor.is_ext C D G (F y) (\<eta>.map y) x (\<phi> y f) f"
    proof -
      interpret y\<eta>: arrow_to_functor C D G y "F y" "\<eta>.map y"
        apply unfold_locales using y \<eta>.maps_ide_in_hom by auto
      show "y\<eta>.is_ext x (\<phi> y f) f"
        apply unfold_locales using f y \<phi>_def y\<eta>.is_ext_def F_ide by auto
    qed

    lemma \<phi>_invertible:
    assumes x: "C.ide x" and g: "g \<in> D.hom y (G x)"
    shows "\<exists>!f. f \<in> C.hom (F y) x \<and> \<phi> y f = g"
    proof
      have y: "D.ide y" using g by auto
      interpret y\<eta>: initial_arrow_to_functor C D G y "Fo y" "\<eta>o y"
        using y initial_arrows_exist Fo_\<eta>o_initial by auto
      have 1: "arrow_to_functor C D G y x g"
        apply unfold_locales using x g apply auto done
      let ?f = "y\<eta>.the_ext x g"
      have "\<phi> y ?f = g"
        using \<phi>_def y\<eta>.the_ext_prop 1 F_ide x y \<phi>_inverts_ext y\<eta>.is_ext_def by fastforce
      moreover have "?f \<in> C.hom (F y) x"
        using 1 y y\<eta>.the_ext_prop F_ide by simp
      ultimately show "?f \<in> C.hom (F y) x \<and> \<phi> y ?f = g" by auto
      show "\<And>f'. f' \<in> C.hom (F y) x \<and> \<phi> y f' = g \<Longrightarrow> f' = ?f"
        using 1 y \<phi>_inverts_ext y\<eta>.the_ext_unique F_ide by force
    qed

    definition \<psi>
    where "\<psi> x g = (THE f. f \<in> C.hom (F (D.dom g)) x \<and> \<phi> (D.dom g) f = g)"

    lemma \<psi>_mapsto:
    assumes "C.ide x" and "g \<in> D.hom y (G x)"
    shows "\<psi> x g \<in> C.hom (F y) x"
      using assms \<phi>_invertible \<psi>_def theI' [of "\<lambda>f. f \<in> C.hom (F y) x \<and> \<phi> y f = g"]
      by simp

    lemma \<psi>_\<phi>:
    assumes "D.ide y" and "f \<in> C.hom (F y) x"
    shows "\<psi> x (\<phi> y f) = f"
    proof -
      have "D.dom (\<phi> y f) = y" using assms \<phi>_mapsto by blast
      hence "\<psi> x (\<phi> y f) = (THE f'. f' \<in> C.hom (F y) x \<and> \<phi> y f' = \<phi> y f)"
        using \<psi>_def by auto
      moreover have "\<exists>!f'. f' \<in> C.hom (F y) x \<and> \<phi> y f' = \<phi> y f"
        using assms \<phi>_mapsto \<phi>_invertible C.ide_cod by blast
      ultimately show ?thesis using assms(2) by auto
    qed

    lemma \<phi>_\<psi>:
    assumes "C.ide x" and "g \<in> D.hom y (G x)"
    shows "\<phi> y (\<psi> x g) = g"
      using assms \<phi>_invertible \<psi>_def theI' [of "\<lambda>f. f \<in> C.hom (F y) x \<and> \<phi> y f = g"]
      by simp

    theorem induces_meta_adjunction:
    shows "meta_adjunction C D F G \<phi> \<psi>"
      apply (unfold_locales)
      using \<phi>_mapsto \<psi>_mapsto \<phi>_\<psi> \<psi>_\<phi> \<phi>_natural preserves_arr preserves_dom
      by auto

  end

  section "Meta-Adjunctions Induce Hom-Adjunctions"

  text{*
    To obtain a hom-adjunction from a meta-adjunction, we need to exhibit hom-functors
    from @{term C} and @{term D} to a common set category @{term S}, so it is necessary
    to apply an actual concrete construction of such a category.
    We use the category @{text SetCat} whose element type is the disjoint sum
    @{typ "('c+'d)"} of the arrow types of @{term C} and @{term D}.
  *}

  context meta_adjunction
  begin

    definition inC :: "'c \<Rightarrow> ('c+'d) SetCat.arr"
    where "inC \<equiv> UP o Inl"

    definition inD :: "'d \<Rightarrow> ('c+'d) SetCat.arr"
    where "inD \<equiv> UP o Inr"

    interpretation S: set_category "SetCat.comp :: ('c+'d) SetCat.arr comp"
      using SetCat.is_set_category by auto
    interpretation Cop: dual_category C ..
    interpretation Dop: dual_category D ..
    interpretation CopxC: product_category Cop.comp C ..
    interpretation DopxD: product_category Dop.comp D ..
    interpretation DopxC: product_category Dop.comp C ..
    interpretation HomC: hom_functor C "SetCat.comp :: ('c+'d) SetCat.arr comp" "\<lambda>_. inC"
      apply unfold_locales
      (* 2 *) unfolding inC_def using SetCat.UP_mapsto apply auto[1]
      (* 1 *) using SetCat.inj_UP by (metis (no_types, lifting) injD inj_Inl inj_comp inj_onI)
    interpretation HomD: hom_functor D "SetCat.comp :: ('c+'d) SetCat.arr comp" "\<lambda>_. inD"
      apply unfold_locales
      (* 2 *) unfolding inD_def using SetCat.UP_mapsto apply auto[1]
      (* 1 *) using SetCat.inj_UP by (metis (no_types, lifting) injD inj_Inr inj_comp inj_onI)
    interpretation Fop: dual_functor D C F ..
    interpretation FopxC: product_functor Dop.comp C Cop.comp C Fop.map C.map ..
    interpretation DopxG: product_functor Dop.comp C Dop.comp D Dop.map G ..
    interpretation Hom_FopxC: composite_functor DopxC.comp CopxC.comp SetCat.comp
                                                FopxC.map HomC.map ..
    interpretation Hom_DopxG: composite_functor DopxC.comp DopxD.comp SetCat.comp
                                                DopxG.map HomD.map ..

    lemma inC_\<psi> [simp]:
    assumes "C.ide b" and "C.ide a" and "x \<in> inC ` C.hom b a"
    shows "inC (HomC.\<psi> (b, a) x) = x"
      using assms by auto

    lemma \<psi>_inC [simp]:
    assumes "C.arr f"
    shows "HomC.\<psi> (C.dom f, C.cod f) (inC f) = f"
      using assms by simp

    lemma inD_\<psi> [simp]:
    assumes "D.ide b" and "D.ide a" and "x \<in> inD ` D.hom b a"
    shows "inD (HomD.\<psi> (b, a) x) = x"
      using assms by auto

    lemma \<psi>_inD [simp]:
    assumes "D.arr f"
    shows "HomD.\<psi> (D.dom f, D.cod f) (inD f) = f"
      using assms by simp

    lemma Hom_FopxC_simp:
    assumes "DopxC.arr gf"
    shows "Hom_FopxC.map gf =
              S.mkArr (HomC.set (F (D.cod (fst gf)), C.dom (snd gf)))
                      (HomC.set (F (D.dom (fst gf)), C.cod (snd gf)))            
                      (inC o (\<lambda>h. C (snd gf) (C h (F (fst gf))))
                           o HomC.\<psi> (F (D.cod (fst gf)), C.dom (snd gf)))"
      using assms HomC.map_def by simp

    lemma Hom_DopxG_simp:
    assumes "DopxC.arr gf"
    shows "Hom_DopxG.map gf =
              S.mkArr (HomD.set (D.cod (fst gf), G (C.dom (snd gf))))
                      (HomD.set (D.dom (fst gf), G (C.cod (snd gf))))           
                      (inD o (\<lambda>h. D (G (snd gf)) (D h (fst gf)))
                           o HomD.\<psi> (D.cod (fst gf), G (C.dom (snd gf))))"
      using assms HomD.map_def by simp
                      
    definition \<Phi>o
    where "\<Phi>o yx = S.mkArr (HomC.set (F (fst yx), snd yx))
                           (HomD.set (fst yx, G (snd yx)))
                           (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))"

    lemma \<Phi>o_in_hom:
    assumes yx: "DopxC.ide yx"
    shows "\<Phi>o yx \<in> S.hom (Hom_FopxC.map yx) (Hom_DopxG.map yx)"
    proof -
      have "Hom_FopxC.map yx = S.mkIde (HomC.set (F (fst yx), snd yx))"
        using yx HomC.map_ide by auto
      moreover have "Hom_DopxG.map yx = S.mkIde (HomD.set (fst yx, G (snd yx)))"
        using yx HomD.map_ide by auto
      moreover have "S.mkArr (HomC.set (F (fst yx), snd yx))
                             (HomD.set (fst yx, G (snd yx)))
                             (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))
                       \<in> S.hom (S.mkIde (HomC.set (F (fst yx), snd yx)))
                               (S.mkIde (HomD.set (fst yx, G (snd yx))))"
      proof (intro S.mkArr_in_hom)
        show "HomC.set (F (fst yx), snd yx) \<subseteq> S.Univ" using yx HomC.set_subset_Univ by simp
        show "HomD.set (fst yx, G (snd yx)) \<subseteq> S.Univ" using yx HomD.set_subset_Univ by simp
        show "inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx)
                 \<in> HomC.set (F (fst yx), snd yx) \<rightarrow> HomD.set (fst yx, G (snd yx))"
        proof
          fix x
          assume x: "x \<in> HomC.set (F (fst yx), snd yx)"
          show "(inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx)) x
                  \<in> HomD.set (fst yx, G (snd yx))"
            using x yx HomC.\<psi>_mapsto [of "F (fst yx)" "snd yx"]
                  \<phi>_mapsto [of "fst yx"]
                  HomD.\<phi>_mapsto [of "fst yx" "G (snd yx)"]
            by auto
        qed
      qed
      ultimately show ?thesis using \<Phi>o_def by auto
    qed

    interpretation \<Phi>: transformation_by_components DopxC.comp SetCat.comp
                                                   Hom_FopxC.map Hom_DopxG.map \<Phi>o
    proof
      fix yx
      assume yx: "DopxC.ide yx"
      show "\<Phi>o yx \<in> S.hom (Hom_FopxC.map yx) (Hom_DopxG.map yx)"
        using yx \<Phi>o_in_hom by auto
      next
      fix gf
      assume gf: "DopxC.arr gf"
      show "SetCat.comp (\<Phi>o (DopxC.cod gf)) (Hom_FopxC.map gf)
                = SetCat.comp (Hom_DopxG.map gf) (\<Phi>o (DopxC.dom gf))"
      proof -
        let ?g = "fst gf"
        let ?f = "snd gf"
        let ?x = "C.dom ?f"
        let ?x' = "C.cod ?f"
        let ?y = "D.cod ?g"
        let ?y' = "D.dom ?g"
        let ?Fy = "F ?y"
        let ?Fy' = "F ?y'"
        let ?Fg = "F ?g"
        let ?Gx = "G ?x"
        let ?Gx' = "G ?x'"
        let ?Gf = "G ?f"
        have 1: "S.arr (Hom_FopxC.map gf) \<and>
                 Hom_FopxC.map gf = S.mkArr (HomC.set (?Fy, ?x)) (HomC.set (?Fy', ?x'))
                                            (inC o (\<lambda>h. C ?f (C h ?Fg)) o HomC.\<psi> (?Fy, ?x))"
          using gf Hom_FopxC.preserves_arr Hom_FopxC_simp [of gf] by blast
        have 2: "S.arr (\<Phi>o (DopxC.cod gf)) \<and>
                 \<Phi>o (DopxC.cod gf) = S.mkArr (HomC.set (?Fy', ?x')) (HomD.set (?y', ?Gx'))
                                             (inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))"
          using gf \<Phi>o_in_hom [of "DopxC.cod gf"] \<Phi>o_def [of "DopxC.cod gf"] \<phi>_mapsto
          by auto
        have 3: "S.arr (\<Phi>o (DopxC.dom gf)) \<and>
                 \<Phi>o (DopxC.dom gf) = S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y, ?Gx))
                                             (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))"
          using gf \<Phi>o_in_hom [of "DopxC.dom gf"] \<Phi>o_def [of "DopxC.dom gf"] \<phi>_mapsto
          by auto
        have 4: "S.arr (Hom_DopxG.map gf) \<and>
                 Hom_DopxG.map gf = S.mkArr (HomD.set (?y, ?Gx)) (HomD.set (?y', ?Gx'))
                                            (inD o (\<lambda>h. D ?Gf (D h ?g)) o HomD.\<psi> (?y, ?Gx))"
          using gf Hom_DopxG.preserves_arr [of gf] Hom_DopxG_simp [of gf] by blast
        have 5: "S.arr (SetCat.comp (\<Phi>o (DopxC.cod gf)) (Hom_FopxC.map gf))
                 \<and> SetCat.comp (\<Phi>o (DopxC.cod gf)) (Hom_FopxC.map gf)
                     = S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y', ?Gx'))
                               ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                                 o (inC o (\<lambda>h. C ?f (C h ?Fg)) o HomC.\<psi> (?Fy, ?x)))"
        proof -
          have "S.seq (\<Phi>o (DopxC.cod gf)) (Hom_FopxC.map gf)"
            using gf 1 2 S.mkArr_in_hom
            by (metis (mono_tags, lifting) S.cod_mkArr S.dom_mkArr)
          thus ?thesis
            using S.arr_comp S.comp_mkArr 1 2 by metis
        qed
        have 6: "SetCat.comp (Hom_DopxG.map gf) (\<Phi>o (DopxC.dom gf))
                  = S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y', ?Gx'))
                            ((inD o (\<lambda>h. D ?Gf (D h ?g)) o HomD.\<psi> (?y, ?Gx))
                              o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x)))"
        proof -
          have "S.seq (Hom_DopxG.map gf) (\<Phi>o (DopxC.dom gf))"
            using gf 3 4 S.mkArr_in_hom
            by (metis (mono_tags, lifting) S.cod_mkArr S.dom_mkArr)
          thus ?thesis
            using 3 4 S.comp_mkArr by metis
        qed
        have 7: "restrict ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                           o (inC o (\<lambda>h. C ?f (C h ?Fg)) o HomC.\<psi> (?Fy, ?x))) (HomC.set (?Fy, ?x))
                   = restrict ((inD o (\<lambda>h. D ?Gf (D h ?g)) o HomD.\<psi> (?y, ?Gx))
                                o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))) (HomC.set (?Fy, ?x))"
        proof (intro restrict_ext)
          show "\<And>h. h \<in> HomC.set (?Fy, ?x) \<Longrightarrow>
                     ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                       o (inC o (\<lambda>h. C ?f (C h ?Fg)) o HomC.\<psi> (?Fy, ?x))) h
                       = ((inD o (\<lambda>h. D ?Gf (D h ?g)) o HomD.\<psi> (?y, ?Gx))
                           o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))) h"
          proof -
            fix h
            assume h: "h \<in> HomC.set (?Fy, ?x)"
            have \<psi>h: "HomC.\<psi> (?Fy, ?x) h \<in> C.hom ?Fy ?x"
              using gf h HomC.\<psi>_mapsto [of ?Fy ?x] CopxC.ide_char by auto
            show "((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                       o (inC o (\<lambda>h. C ?f (C h ?Fg)) o HomC.\<psi> (?Fy, ?x))) h
                       = ((inD o (\<lambda>h. D ?Gf (D h ?g)) o HomD.\<psi> (?y, ?Gx))
                           o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))) h"
            proof -
              have "((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                       o (inC o (\<lambda>h. C ?f (C h ?Fg)) o HomC.\<psi> (?Fy, ?x))) h
                      = inD (\<phi> ?y' (HomC.\<psi> (?Fy', ?x') (inC (C ?f (C (HomC.\<psi> (?Fy, ?x) h) ?Fg)))))"
                by simp
              also have "... = inD (\<phi> ?y' (C ?f (C (HomC.\<psi> (?Fy, ?x) h) ?Fg)))"
                using gf \<psi>h HomC.\<phi>_mapsto HomC.\<psi>_mapsto \<phi>_mapsto F.preserves_hom by simp
              also have "... = inD (D ?Gf (D (\<phi> ?y (HomC.\<psi> (?Fy, ?x) h)) ?g))"
                using gf \<psi>h naturality \<phi>_mapsto G.preserves_hom by simp
              also have "... =
                  inD (D ?Gf (D (HomD.\<psi> (?y, ?Gx) (inD (\<phi> ?y (HomC.\<psi> (?Fy, ?x) h)))) ?g))"
                using gf \<psi>h \<phi>_mapsto by simp
              also have "... = ((inD o (\<lambda>h. D ?Gf (D h ?g)) o HomD.\<psi> (?y, ?Gx))
                                o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))) h"
                by simp
              finally show ?thesis by auto
            qed
          qed
        qed
        have 8: "S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y', ?Gx'))
                         ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                           o (inC o (\<lambda>h. C ?f (C h ?Fg)) o HomC.\<psi> (?Fy, ?x)))
                    = S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y', ?Gx'))
                              ((inD o (\<lambda>h. D ?Gf (D h ?g)) o HomD.\<psi> (?y, ?Gx))
                                o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x)))"
        proof (intro S.mkArr_eqI')
          show "S.arr (S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y', ?Gx'))
                               ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                                o (inC o (\<lambda>h. C ?f (C h ?Fg)) o HomC.\<psi> (?Fy, ?x))))"
            using 5 by metis
          show "\<And>t. t \<in> HomC.set (?Fy, ?x) \<Longrightarrow>
                      ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                             o (inC o (\<lambda>h. C ?f (C h ?Fg)) o HomC.\<psi> (?Fy, ?x))) t
                      = ((inD o (\<lambda>h. D ?Gf (D h ?g)) o HomD.\<psi> (?y, ?Gx))
                              o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))) t"
            using 7 restrict_apply by fast
        qed
        show ?thesis using 5 6 8 by auto
      qed
    qed

    lemma \<Phi>_simp:
    assumes YX: "DopxC.ide yx"
    shows "\<Phi>.map yx = S.mkArr (HomC.set (F (fst yx), snd yx)) (HomD.set (fst yx, G (snd yx)))
                              (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))"
      using YX \<Phi>o_def by simp
      
    abbreviation \<Psi>o
    where "\<Psi>o yx \<equiv> S.mkArr (HomD.set (fst yx, G (snd yx))) (HomC.set (F (fst yx), snd yx))
                            (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))"

    lemma \<Psi>o_in_hom:
    assumes yx: "DopxC.ide yx"
    shows "\<Psi>o yx \<in> S.hom (Hom_DopxG.map yx) (Hom_FopxC.map yx)"
    proof -
      have "Hom_FopxC.map yx = S.mkIde (HomC.set (F (fst yx), snd yx))"
        using yx HomC.map_ide by auto
      moreover have "Hom_DopxG.map yx = S.mkIde (HomD.set (fst yx, G (snd yx)))"
        using yx HomD.map_ide by auto
      moreover have "S.mkArr (HomD.set (fst yx, G (snd yx))) (HomC.set (F (fst yx), snd yx))
                             (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))
                       \<in> S.hom (S.mkIde (HomD.set (fst yx, G (snd yx))))
                               (S.mkIde (HomC.set (F (fst yx), snd yx)))"
      proof (intro S.mkArr_in_hom)
        show "HomC.set (F (fst yx), snd yx) \<subseteq> S.Univ" using yx HomC.set_subset_Univ by simp
        show "HomD.set (fst yx, G (snd yx)) \<subseteq> S.Univ" using yx HomD.set_subset_Univ by simp
        show "inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx))
                 \<in> HomD.set (fst yx, G (snd yx)) \<rightarrow> HomC.set (F (fst yx), snd yx)"
        proof
          fix x
          assume x: "x \<in> HomD.set (fst yx, G (snd yx))"
          show "(inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx))) x
                  \<in> HomC.set (F (fst yx), snd yx)"
            using x yx HomD.\<psi>_mapsto [of "fst yx" "G (snd yx)"] \<psi>_mapsto [of "snd yx"]
                  HomC.\<phi>_mapsto [of "F (fst yx)" "snd yx"]
            by auto
        qed
      qed
      ultimately show ?thesis by auto
    qed

    lemma \<Phi>_inv:
    assumes yx: "DopxC.ide yx"
    shows "S.inverse_arrows (\<Phi>.map yx) (\<Psi>o yx)"
    proof -
      have 1: "\<Phi>.map yx \<in> S.hom (Hom_FopxC.map yx) (Hom_DopxG.map yx)"
        using yx DopxC.ideD \<Phi>.preserves_hom [of yx yx yx] by simp
      have 2: "\<Psi>o yx \<in> S.hom  (Hom_DopxG.map yx) (Hom_FopxC.map yx)"
        using yx \<Psi>o_in_hom [of yx] by simp
      have 3: "\<Phi>.map yx = S.mkArr (HomC.set (F (fst yx), snd yx))
                                   (HomD.set (fst yx, G (snd yx)))
                                   (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))"
        using yx \<Phi>_simp by blast
      have antipar: "S.antipar (\<Phi>.map yx) (\<Psi>o yx)"
        using 1 2 by simp
      moreover have "S.ide (SetCat.comp (\<Psi>o yx) (\<Phi>.map yx))"
      proof -
        have "SetCat.comp (\<Psi>o yx) (\<Phi>.map yx) =
                  S.mkArr (HomC.set (F (fst yx), snd yx)) (HomC.set (F (fst yx), snd yx))
                          ((inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))
                            o (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx)))"
          using 1 2 3 by simp
        also have "... = S.mkArr (HomC.set (F (fst yx), snd yx)) (HomC.set (F (fst yx), snd yx))
                                 (\<lambda>x. x)"
        proof -
          have "S.mkArr (HomC.set (F (fst yx), snd yx)) (HomC.set (F (fst yx), snd yx)) (\<lambda>x. x)
                  = ..."
          proof
            show "S.arr (S.mkArr (HomC.set (F (fst yx), snd yx)) (HomC.set (F (fst yx), snd yx))
                        (\<lambda>x. x))"
              using yx HomC.set_subset_Univ by simp
            show "\<And>x. x \<in> HomC.set (F (fst yx), snd yx) \<Longrightarrow>
                        x = ((inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))
                             o (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))) x"
            proof -
              fix x
              assume x: "x \<in> HomC.set (F (fst yx), snd yx)"
              have "((inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))
                             o (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))) x
                      = inC (\<psi> (snd yx) (HomD.\<psi> (fst yx, G (snd yx))
                              (inD (\<phi> (fst yx) (HomC.\<psi> (F (fst yx), snd yx) x)))))"
                by simp
              also have "... = inC (\<psi> (snd yx) (\<phi> (fst yx) (HomC.\<psi> (F (fst yx), snd yx) x)))"
              proof -
                have "\<phi> (fst yx) (HomC.\<psi> (F (fst yx), snd yx) x) \<in> D.hom (fst yx) (G (snd yx))"
                  using x yx HomC.\<psi>_mapsto [of "F (fst yx)" "snd yx"] \<phi>_mapsto by auto
                thus ?thesis by simp
              qed
              also have "... = inC (HomC.\<psi> (F (fst yx), snd yx) x)"
                using x yx HomC.\<psi>_mapsto [of "F (fst yx)" "snd yx"]
                      \<psi>_\<phi> [of "fst yx" "HomC.\<psi> (F (fst yx), snd yx) x" "snd yx"]
                by force
              also have "... = x" using x yx inC_\<psi> by simp
              finally show "x = ((inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))
                                   o (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))) x"
                by auto
            qed
          qed
          thus ?thesis by auto
        qed
        also have "... = S.mkIde (HomC.set (F (fst yx), snd yx))"
          using yx S.mkIde_as_mkArr HomC.set_subset_Univ
          by force
        finally have "SetCat.comp (\<Psi>o yx) (\<Phi>.map yx) = S.mkIde (HomC.set (F (fst yx), snd yx))"
          by auto
        thus ?thesis using yx HomC.set_subset_Univ by simp
      qed
      moreover have "S.ide (SetCat.comp (\<Phi>.map yx) (\<Psi>o yx))"
      proof -
        have "SetCat.comp (\<Phi>.map yx) (\<Psi>o yx) =
                  S.mkArr (HomD.set (fst yx, G (snd yx))) (HomD.set (fst yx, G (snd yx)))
                          ((inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))
                            o (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx))))"
          using 1 2 3 by simp
        also have "... = S.mkArr (HomD.set (fst yx, G (snd yx))) (HomD.set (fst yx, G (snd yx)))
                                 (\<lambda>x. x)"
        proof -
          have "S.mkArr (HomD.set (fst yx, G (snd yx))) (HomD.set (fst yx, G (snd yx))) (\<lambda>x. x)
                  = ..."
          proof
            show "S.arr (S.mkArr (HomD.set (fst yx, G (snd yx))) (HomD.set (fst yx, G (snd yx)))
                        (\<lambda>x. x))"
              using yx HomD.set_subset_Univ by simp
            show "\<And>x. x \<in> (HomD.set (fst yx, G (snd yx))) \<Longrightarrow>
                        x = ((inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))
                            o (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))) x"
            proof -
              fix x
              assume x: "x \<in> HomD.set (fst yx, G (snd yx))"
              have "((inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))
                          o (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))) x
                       = inD (\<phi> (fst yx) (HomC.\<psi> (F (fst yx), snd yx)
                            (inC (\<psi> (snd yx) (HomD.\<psi> (fst yx, G (snd yx)) x)))))"
                by simp
              also have "... = inD (\<phi> (fst yx) (\<psi> (snd yx) (HomD.\<psi> (fst yx, G (snd yx)) x)))"
              proof -
                have "\<psi> (snd yx) (HomD.\<psi> (fst yx, G (snd yx)) x) \<in> C.hom (F (fst yx)) (snd yx)"
                  using x yx HomD.\<psi>_mapsto [of "fst yx" "G (snd yx)"] \<psi>_mapsto by auto
                thus ?thesis by simp
              qed
              also have "... = inD (HomD.\<psi> (fst yx, G (snd yx)) x)"
                using x yx HomD.\<psi>_mapsto [of "fst yx" "G (snd yx)"]
                      \<phi>_\<psi> [of "snd yx" "HomD.\<psi> (fst yx, G (snd yx)) x" "fst yx"]
                by force
              also have "... = x" using x yx inD_\<psi> by simp
              finally show "x = ((inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))
                                   o (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))) x"
                by auto
            qed
          qed
          thus ?thesis by auto
        qed
        also have "... = S.mkIde (HomD.set (fst yx, G (snd yx)))"
          using yx S.mkIde_as_mkArr HomD.set_subset_Univ by force
        finally have "SetCat.comp (\<Phi>.map yx) (\<Psi>o yx) = S.mkIde (HomD.set (fst yx, G (snd yx)))"
          by auto
        thus ?thesis using yx HomD.set_subset_Univ by simp
      qed
      ultimately show ?thesis by blast
    qed

    interpretation \<Phi>: natural_isomorphism DopxC.comp SetCat.comp
                                          Hom_FopxC.map Hom_DopxG.map \<Phi>.map
      apply (unfold_locales) using \<Phi>_inv by blast

    interpretation \<Psi>: inverse_transformation DopxC.comp SetCat.comp
                           Hom_FopxC.map Hom_DopxG.map \<Phi>.map ..

    interpretation \<Phi>\<Psi>: inverse_transformations DopxC.comp SetCat.comp
                           Hom_FopxC.map Hom_DopxG.map \<Phi>.map \<Psi>.map
    proof
      fix yx
      assume "DopxC.ide yx"
      thus "S.inverse_arrows (\<Phi>.map yx) (\<Psi>.map yx)"
        using \<Psi>.inverts_components by simp
     qed

    abbreviation \<Phi> where "\<Phi> \<equiv> \<Phi>.map"
    abbreviation \<Psi> where "\<Psi> \<equiv> \<Psi>.map"

    abbreviation HomC where "HomC \<equiv> HomC.map"
    abbreviation \<phi>C where "\<phi>C \<equiv> \<lambda>_. inC"
    abbreviation HomD where "HomD \<equiv> HomD.map"
    abbreviation \<phi>D where "\<phi>D \<equiv> \<lambda>_. inD"

    theorem induces_hom_adjunction: "hom_adjunction C D SetCat.comp \<phi>C \<phi>D F G \<Phi> \<Psi>"
      apply (unfold_locales) by auto

    lemma \<Psi>_simp:
    assumes yx: "DopxC.ide yx"
    shows "\<Psi> yx = S.mkArr (HomD.set (fst yx, G (snd yx))) (HomC.set (F (fst yx), snd yx))
                          (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))"
      using assms \<Phi>o_def \<Phi>_inv S.inverse_unique by simp

    text{*
      The original @{term \<phi>} and @{term \<psi>} can be recovered from @{term \<Phi>} and @{term \<Psi>}.
    *}

    interpretation \<Phi>: set_valued_transformation DopxC.comp SetCat.comp
                                                Hom_FopxC.map Hom_DopxG.map \<Phi>.map ..
     
    interpretation \<Psi>: set_valued_transformation DopxC.comp SetCat.comp
                                                Hom_DopxG.map Hom_FopxC.map \<Psi>.map ..

    lemma \<phi>_in_terms_of_\<Phi>':
    assumes y: "D.ide y" and f: "f \<in> C.hom (F y) x"
    shows "\<phi> y f = (HomD.\<psi> (y, G x) o \<Phi>.FUN (y, x) o inC) f"
    proof -
      have x: "C.ide x" using f by auto
      have 1: "S.arr (\<Phi> (y, x))" using x y \<Phi>.preserves_arr by fastforce
      have 2: "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                  (inD o \<phi> y o HomC.\<psi> (F y, x))"
        using x y \<Phi>o_def by auto
      have "(HomD.\<psi> (y, G x) o \<Phi>.FUN (y, x) o inC) f =
              HomD.\<psi> (y, G x) (restrict (inD o \<phi> y o HomC.\<psi> (F y, x)) (HomC.set (F y, x)) (inC f))"
        using 1 2 by simp
      also have "... = \<phi> y f"
        using x y f HomC.\<phi>_mapsto [of "F y" x] \<phi>_mapsto [of y f x] HomC.\<psi>_mapsto [of "F y" x]
        by auto
      finally show ?thesis by auto
    qed

    lemma \<psi>_in_terms_of_\<Psi>':
    assumes x: "C.ide x" and g: "g \<in> D.hom y (G x)"
    shows "\<psi> x g = (HomC.\<psi> (F y, x) o \<Psi>.FUN (y, x) o inD) g"
    proof -
      have y: "D.ide y" using g by auto
      have 1: "S.arr (\<Psi> (y, x))" using x y \<Psi>.preserves_arr [of "(y, x)"] by simp
      have 2: "\<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                   (inC o \<psi> x o HomD.\<psi> (y, G x))"
        using x y \<Psi>_simp by force
      have "(HomC.\<psi> (F y, x) o \<Psi>.FUN (y, x) o inD) g =
              HomC.\<psi> (F y, x) (restrict (inC o \<psi> x o HomD.\<psi> (y, G x)) (HomD.set (y, G x)) (inD g))"
        using 1 2 by simp
      also have "... = \<psi> x g"
        using x y g HomD.\<phi>_mapsto [of y "G x"] \<psi>_mapsto [of x g y] HomD.\<psi>_mapsto [of y "G x"]
        by auto              
      finally show ?thesis by auto
    qed

  end

  section "Hom-Adjunctions Induce Meta-Adjunctions"

  context hom_adjunction
  begin

    definition \<phi> :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    where "\<phi> y h = (HomD.\<psi> (y, G (C.cod h)) o \<Phi>.FUN (y, C.cod h) o \<phi>C (F y, C.cod h)) h"
    
    definition \<psi> :: "'c \<Rightarrow> 'd \<Rightarrow> 'c"
    where "\<psi> x h = (HomC.\<psi> (F (D.dom h), x) o \<Psi>.FUN (D.dom h, x) o \<phi>D (D.dom h, G x)) h"

    lemma Hom_FopxC_map_simp:
    assumes "DopxC.arr gf"
    shows "Hom_FopxC.map gf =
              S.mkArr (HomC.set (F (D.cod (fst gf)), C.dom (snd gf)))
                      (HomC.set (F (D.dom (fst gf)), C.cod (snd gf)))            
                      (\<phi>C (F (D.dom (fst gf)), C.cod (snd gf))
                           o (\<lambda>h. C (snd gf) (C h (F (fst gf))))
                           o HomC.\<psi> (F (D.cod (fst gf)), C.dom (snd gf)))"
      using assms HomC.map_def by simp

    lemma Hom_DopxG_map_simp:
    assumes "DopxC.arr gf"
    shows "Hom_DopxG.map gf =
              S.mkArr (HomD.set (D.cod (fst gf), G (C.dom (snd gf))))
                      (HomD.set (D.dom (fst gf), G (C.cod (snd gf))))           
                      (\<phi>D (D.dom (fst gf), G (C.cod (snd gf)))
                           o (\<lambda>h. D (G (snd gf)) (D h (fst gf)))
                           o HomD.\<psi> (D.cod (fst gf), G (C.dom (snd gf))))"
      using assms HomD.map_def by simp
                      
    lemma \<Phi>_Fun_mapsto:
    assumes "D.ide y" and "f \<in> C.hom (F y) x"
    shows "\<Phi>.FUN (y, x) \<in> HomC.set (F y, x) \<rightarrow> HomD.set (y, G x)"
    proof -
      have "\<Phi>.FUN (y, x) \<in> \<Phi>.DOM (y, x) \<rightarrow> \<Phi>.COD (y, x)"
        using assms S.Fun_mapsto [of "\<Phi> (y, x)"] by auto
      thus ?thesis
        using assms HomC.set_map HomD.set_map by force
    qed

    lemma \<phi>_mapsto:
    assumes y: "D.ide y"
    shows "\<phi> y \<in> C.hom (F y) x \<rightarrow> D.hom y (G x)"
    proof
      fix h
      assume h: "h \<in> C.hom (F y) x"
      show "\<phi> y h \<in> D.hom y (G x)"
      proof -
        have "\<phi>C (F y, x) h \<in> HomC.set (F y, x)"
          using y h HomC.\<phi>_mapsto [of "F y" x] by auto
        hence "\<Phi>.FUN (y, x) (\<phi>C (F y, x) h) \<in> HomD.set (y, G x)"
          using h y \<Phi>_Fun_mapsto by fast
        thus ?thesis
          using y h \<phi>_def HomC.\<phi>_mapsto [of "F y" x] HomD.\<psi>_mapsto [of y "G x"] by auto
      qed
    qed

    lemma \<Phi>_simp:
    assumes "D.ide y" and "C.ide x"
    shows "S.arr (\<Phi> (y, x))"
    and "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                            (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
    proof -
      show 1: "S.arr (\<Phi> (y, x))" using assms by auto
      hence "\<Phi> (y, x) = S.mkArr (\<Phi>.DOM (y, x)) (\<Phi>.COD (y, x)) (\<Phi>.FUN (y, x))" by simp
      also have "... = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x)) (\<Phi>.FUN (y, x))"
        using assms HomC.set_map HomD.set_map by simp
      also have "... = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                               (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
      proof (intro S.mkArr_eqI')
        show "S.arr (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x)) (\<Phi>.FUN (y, x)))"
          using 1 calculation by presburger
        show "\<And>h. h \<in> HomC.set (F y, x) \<Longrightarrow>
                    \<Phi>.FUN (y, x) h = (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)) h"
        proof -
          fix h
          assume h: "h \<in> HomC.set (F y, x)"
          hence "\<psi>C (F y, x) h \<in> C.hom (F y) x"
            using assms HomC.\<psi>_mapsto [of "F y" x] by auto
          hence "(\<phi>D (y, G x) o \<phi> y o HomC.\<psi> (F y, x)) h =
                   \<phi>D (y, G x) (\<psi>D (y, G x) (\<Phi>.FUN (y, x) (\<phi>C (F y, x) (\<psi>C (F y, x) h))))"
            using h \<phi>_def by simp
          also have "... = \<phi>D (y, G x) (\<psi>D (y, G x) (\<Phi>.FUN (y, x) h))"
            using assms h HomC.\<phi>_\<psi> [of "F y" x h] \<Phi>_Fun_mapsto [of y "\<psi>C (F y, x) h" x]
            by simp
          also have "... = \<Phi>.FUN (y, x) h"
            using assms h \<Phi>_Fun_mapsto [of y "\<psi>C (F y, x) h" x]
                  HomC.\<psi>_mapsto [of "F y" x] HomD.\<phi>_\<psi> [of y "G x" "\<Phi>.FUN (y, x) h"]
            by fastforce
          finally show "\<Phi>.FUN (y, x) h = (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)) h" by auto
        qed
      qed
      finally show "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                       (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
        by force
    qed

    lemma \<Psi>_Fun_mapsto:
    assumes "C.ide x" and "g \<in> D.hom y (G x)"
    shows "\<Psi>.FUN (y, x) \<in> HomD.set (y, G x) \<rightarrow> HomC.set (F y, x)"
    proof -
      have "\<Psi>.FUN (y, x) \<in> \<Psi>.DOM (y, x) \<rightarrow> \<Psi>.COD (y, x)"
        using assms S.Fun_mapsto [of "\<Psi> (y, x)"] by auto
      thus ?thesis
        using assms HomC.set_map HomD.set_map by fastforce
    qed

    lemma \<psi>_mapsto:
    assumes x: "C.ide x"
    shows "\<psi> x \<in> D.hom y (G x) \<rightarrow> C.hom (F y) x"
    proof
      fix h
      assume h: "h \<in> D.hom y (G x)"
      show "\<psi> x h \<in> C.hom (F y) x"
      proof -
        have "\<phi>D (y, G x) h \<in> HomD.set (y, G x)"
          using x h HomD.\<phi>_mapsto [of y "G x"] by auto
        hence "\<Psi>.FUN (y, x) (\<phi>D (y, G x) h) \<in> HomC.set (F y, x)"
          using h x \<Psi>_Fun_mapsto by fast
        thus ?thesis
          using x h \<psi>_def HomD.\<phi>_mapsto [of y "G x"] HomC.\<psi>_mapsto [of "F y" x] by auto
      qed
    qed

    lemma \<Psi>_simp:
    assumes "D.ide y" and "C.ide x"
    shows "S.arr (\<Psi> (y, x))"
    and "\<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                            (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
    proof -
      show 1: "S.arr (\<Psi> (y, x))" using assms by auto
      hence "\<Psi> (y, x) = S.mkArr (\<Psi>.DOM (y, x)) (\<Psi>.COD (y, x)) (\<Psi>.FUN (y, x))" by simp
      also have "... = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x)) (\<Psi>.FUN (y, x))"
        using assms HomC.set_map HomD.set_map by simp
      also have "... = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                               (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
      proof (intro S.mkArr_eqI')
        show "S.arr (S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x)) (\<Psi>.FUN (y, x)))"
          using 1 calculation by presburger
        show "\<And>h. h \<in> HomD.set (y, G x) \<Longrightarrow>
                    \<Psi>.FUN (y, x) h = (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x)) h"
        proof -
          fix h
          assume h: "h \<in> HomD.set (y, G x)"
          hence "\<psi>D (y, G x) h \<in> D.hom y (G x)"
            using assms HomD.\<psi>_mapsto [of y "G x"] by auto
          hence "(\<phi>C (F y, x) o \<psi> x o HomD.\<psi> (y, G x)) h =
                   \<phi>C (F y, x) (\<psi>C (F y, x) (\<Psi>.FUN (y, x) (\<phi>D (y, G x) (\<psi>D (y, G x) h))))"
            using h \<psi>_def by simp
          also have "... = \<phi>C (F y, x) (\<psi>C (F y, x) (\<Psi>.FUN (y, x) h))"
            using assms h HomD.\<phi>_\<psi> [of y "G x" h] \<Psi>_Fun_mapsto [of x "\<psi>D (y, G x) h" y]
                  by simp
          also have "... = \<Psi>.FUN (y, x) h"
            using assms h \<Psi>_Fun_mapsto [of x "\<psi>D (y, G x) h" y] HomD.\<psi>_mapsto [of y "G x"]
                  HomC.\<phi>_\<psi> [of "F y" x "\<Psi>.FUN (y, x) h"]
            by fastforce
          finally show "\<Psi>.FUN (y, x) h = (\<phi>C (F y, x) o \<psi> x o HomD.\<psi> (y, G x)) h" by auto
        qed
      qed
      finally show "\<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                       (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
        by force
    qed

    text{*
      The length of the next proof stems from having to use properties of composition
      of arrows in @{term S} to infer properties of the composition of the corresponding
      functions.
    *}

    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi>
    proof
      fix y :: 'd and x :: 'c and h :: 'c
      assume y: "D.ide y" and h: "h \<in> C.hom (F y) x"
      have x: "C.ide x" using h by auto
      show "\<phi> y h \<in> D.hom y (G x)"
      proof -
        have "\<Phi>.FUN (y, x) \<in> HomC.set (F y, x) \<rightarrow> HomD.set (y, G x)"
          using y h \<Phi>_Fun_mapsto by blast
        thus ?thesis
          using x y h \<phi>_def [of y h] HomD.\<psi>_mapsto [of y "G x"] HomC.\<phi>_mapsto [of "F y" x]
          by auto
      qed
      show "\<psi> x (\<phi> y h) = h"
      proof -
        have 0: "restrict (\<lambda>h. h) (HomC.set (F y, x))
                   = restrict (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) (HomC.set (F y, x))"
        proof -
          have 1: "S.seq (\<Psi> (y, x)) (\<Phi> (y, x)) \<and> S.ide (S (\<Psi> (y, x)) (\<Phi> (y, x)))"
            using x y \<Phi>\<Psi>.inv by fastforce
          have 2: "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                      (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)) \<and>
                   \<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                      (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
            using x y \<Phi>_simp \<Psi>_simp by force
          have 3: "S (\<Psi> (y, x)) (\<Phi> (y, x))
                    = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                              (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x))"
          proof -
            have 4: "S.arr (S (\<Psi> (y, x)) (\<Phi> (y, x)))" using 1 by auto
            hence "S (\<Psi> (y, x)) (\<Phi> (y, x))
                     = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                               ((\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))
                                  o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))"
              using 1 2 by simp
            also have "... = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                                     (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x))"
            proof (intro S.mkArr_eqI')
              show "S.arr (S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                                   ((\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))
                                     o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))))"
                using 4 calculation by simp
              show "\<And>h. h \<in> HomC.set (F y, x) \<Longrightarrow>
                          ((\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))
                            o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))) h =
                          (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) h"
                using x y HomC.\<psi>_mapsto [of "F y" x] \<phi>_mapsto [of y] HomC.\<psi>_\<phi> [of "F y" x]
                by force
            qed
            finally show ?thesis by auto
          qed
          moreover have "S (\<Psi> (y, x)) (\<Phi> (y, x))
                             = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x)) (\<lambda>h. h)"
          proof -
            have "S (\<Psi> (y, x)) (\<Phi> (y, x)) = S.dom (S (\<Psi> (y, x)) (\<Phi> (y, x)))"
              using 1 by auto
            also have "... = S.dom (\<Phi> (y, x))"
              using 1 S.dom_comp by blast
            finally show ?thesis using 1 2 S.mkIde_as_mkArr by auto
          qed
          ultimately have 4: "S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                                      (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x))
                                = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x)) (\<lambda>h. h)"
            by auto
          have 5: "S.arr (S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                                  (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)))"
          proof -
            have "S.arr (S (\<Psi> (y, x)) (\<Phi> (y, x)))" 
              using 1 by fast
            thus ?thesis using 3 by metis
          qed
          hence "restrict (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) (HomC.set (F y, x))
                  = S.Fun (S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                         (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)))"
            by auto
          also have "... = restrict (\<lambda>h. h) (HomC.set (F y, x))"
            using 4 5 by auto
          finally show ?thesis by auto
        qed
        hence "\<phi>C (F y, x) h = (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) (\<phi>C (F y, x) h)"
          using x y h HomC.\<phi>_mapsto [of "F y" x] by fastforce
        hence "\<psi>C (F y, x) (\<phi>C (F y, x) h) =
                 \<psi>C (F y, x) ((\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) (\<phi>C (F y, x) h))"
          by simp
        hence "h = \<psi>C (F y, x) (\<phi>C (F y, x) (\<psi> x (\<phi> y (\<psi>C (F y, x) (\<phi>C (F y, x) h)))))"
          using x y h HomC.\<psi>_\<phi> [of "F y" x] by simp
        also have "... = \<psi> x (\<phi> y h)"
          using x y h HomC.\<psi>_\<phi> [of "F y" x] \<phi>_mapsto [of y] \<psi>_mapsto [of x] by force
        finally show ?thesis by auto
      qed
      next
      fix x :: 'c and h :: 'd and y :: 'd
      assume x: "C.ide x" and h: "h \<in> D.hom y (G x)"
      have y: "D.ide y" using h by auto
      show "\<psi> x h \<in> C.hom (F y) x" using x y h \<psi>_mapsto [of x y] by auto
      show "\<phi> y (\<psi> x h) = h"
      proof -
        have 0: "restrict (\<lambda>h. h) (HomD.set (y, G x))
                   = restrict (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) (HomD.set (y, G x))"
        proof -
          have 1: "S.seq (\<Phi> (y, x)) (\<Psi> (y, x)) \<and> S.ide (S (\<Phi> (y, x)) (\<Psi> (y, x)))"
            using x y \<Phi>\<Psi>.inv by fastforce
          have 2: "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                      (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)) \<and>
                   \<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                       (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
            using x h \<Phi>_simp \<Psi>_simp by force
          have 3: "S (\<Phi> (y, x)) (\<Psi> (y, x))
                     = S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                               (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x))"
          proof -
            have 4: "S.arr (S (\<Phi> (y, x)) (\<Psi> (y, x)))" using 1 by auto
            hence "S (\<Phi> (y, x)) (\<Psi> (y, x))
                     = S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                               ((\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))
                                 o (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x)))"
              using 1 2 by simp
            also have "... = S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                                     (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x))"
            proof
              show "S.arr (S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                                   ((\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))
                                     o (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))))"
                using 4 calculation by simp
              show "\<And>h. h \<in> HomD.set (y, G x) \<Longrightarrow>
                          ((\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))
                            o (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))) h =
                          (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) h"
                using x y HomD.\<psi>_mapsto [of y "G x"] \<psi>_mapsto [of x] HomD.\<psi>_\<phi> [of y "G x"]
                by force
            qed
            finally show ?thesis by auto
          qed
          moreover have "S (\<Phi> (y, x)) (\<Psi> (y, x)) =
                           S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x)) (\<lambda>h. h)"
          proof -
            have "S (\<Phi> (y, x)) (\<Psi> (y, x)) = S.dom (S (\<Phi> (y, x)) (\<Psi> (y, x)))"
              using 1 by auto
            also have "... = S.dom (\<Psi> (y, x))"
              using 1 S.dom_comp by blast
            finally show ?thesis using 1 2 S.mkIde_as_mkArr by auto
          qed
          ultimately have 4: "S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                                      (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x))
                                = S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x)) (\<lambda>h. h)"
            by auto
          have 5: "S.arr (S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                                  (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)))"
          proof -
            have "S.arr (S (\<Phi> (y, x)) (\<Psi> (y, x)))"
              using 1 by fast
            thus ?thesis using 3 by metis
          qed
          hence "restrict (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) (HomD.set (y, G x))
                  = S.Fun (S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                         (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)))"
            by auto
          also have "... = restrict (\<lambda>h. h) (HomD.set (y, G x))"
            using 4 5 by auto
          finally show ?thesis by auto
        qed
        hence "\<phi>D (y, G x) h = (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) (\<phi>D (y, G x) h)"
          using x y h HomD.\<phi>_mapsto [of y "G x"] by fastforce
        hence "\<psi>D (y, G x) (\<phi>D (y, G x) h) =
                \<psi>D (y, G x) ((\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) (\<phi>D (y, G x) h))"
          by simp
        hence "h = \<psi>D (y, G x) (\<phi>D (y, G x) (\<phi> y (\<psi> x (\<psi>D (y, G x) (\<phi>D (y, G x) h)))))"
          using x y h HomD.\<psi>_\<phi> [of y "G x"] by simp
        also have "... = \<phi> y (\<psi> x h)"
          using x y h HomD.\<psi>_\<phi> [of y "G x"] \<phi>_mapsto [of y] \<psi>_mapsto [of x] by force
        finally show ?thesis by auto
      qed
      next
      fix x :: 'c and x' :: 'c and y :: 'd and y' :: 'd
      and f :: 'c and g :: 'd and h :: 'c
      assume f: "f \<in> C.hom x x'" and g: "g \<in> D.hom y' y" and h: "h \<in> C.hom (F y) x"
      have x: "C.ide x" using f by auto
      have y: "D.ide y" using g by auto
      have x': "C.ide x'" using f by auto
      have y': "D.ide y'" using g by auto
      show "\<phi> y' (C f (C h (F g))) = D (G f) (D (\<phi> y h) g)"
      proof -
        have 0: "restrict ((\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))
                           o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                       (HomC.set (F y, x))
                = restrict ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                             o (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g)))) o \<psi>C (F y, x))
                           (HomC.set (F y, x))"
        proof -
          have 1: "S.arr (\<Phi> (y, x)) \<and>
                   \<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                      (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
                using x y \<Phi>_simp [of y x] by auto
          have 2: "S.arr (\<Phi> (y', x')) \<and>
                   \<Phi> (y', x') = S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x'))
                                        (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))"
                using x' y' \<Phi>_simp [of y' x'] by auto
          have 3: "S.arr (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                  ((\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))
                                    o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))))
                   \<and> S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                             ((\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))
                               o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                     = S (S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                  (\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x)))
                         (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                  (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))"
          proof -
            have 1: "S.seq (S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                  (\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x)))
                           (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                  (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))"
            proof -
              have "S.arr (Hom_DopxG.map (g, f))
                    \<and> Hom_DopxG.map (g, f)
                        = S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                  (\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))"
                using f g Hom_DopxG.preserves_arr [of "(g, f)"] Hom_DopxG_map_simp [of "(g, f)"]
                by fastforce
              thus ?thesis using 1 by force
            qed
            have "S.arr (S (S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                  (\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x)))
                           (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                  (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))))"
              using 1 S.arr_comp by presburger
            moreover have "S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                             ((\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))
                               o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                             = S (S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                          (\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x)))
                                 (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                          (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))"
              using 1 by fastforce
            ultimately show ?thesis by auto
          qed
          moreover have
             4: "S.arr (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                                  o (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x))))
                 \<and> S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                           ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                             o (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x)))
                     = S (S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x')) 
                                  (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x')))
                         (S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                  (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x)))"
          proof -
            have 5: "S.seq (S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x'))
                                    (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x')))
                           (S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                    (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x)))"
            proof -
              have "S.arr (Hom_FopxC.map (g, f)) \<and>
                    Hom_FopxC.map (g, f)
                          = S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                    (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x))"
                using f g Hom_FopxC.preserves_arr [of "(g, f)"] Hom_FopxC_map_simp [of "(g, f)"]
                by fastforce
              thus ?thesis using 2 by force
            qed
            have "S.arr (S (S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x'))
                                    (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x')))
                           (S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                    (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x))))"
              using 5 S.arr_comp by presburger
            moreover have "S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                   ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                                     o (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x)))
                             = S (S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x'))
                                          (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x')))
                                 (S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                          (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x)))"
              using 5 by fastforce
            ultimately show ?thesis by presburger
          qed
          moreover have 2: "S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                    ((\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))
                                      o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                             = S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                       ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                                         o (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x)))"
          proof -
            have "S (Hom_DopxG.map (g, f)) (\<Phi> (y, x)) = S (\<Phi> (y', x')) (Hom_FopxC.map (g, f))"
              using f g \<Phi>.is_natural_1 \<Phi>.is_natural_2 by fastforce
            moreover have "Hom_DopxG.map (g, f)
                             = S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                       (\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))"
              using f g Hom_DopxG_map_simp [of "(g, f)"] by auto
            moreover have "Hom_FopxC.map (g, f)
                             = S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                       (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x))"
              using f g Hom_FopxC_map_simp [of "(g, f)"] by auto
            ultimately show ?thesis using 1 2 3 4 by simp (* 15 sec *)
          qed
          ultimately have 6: "S.arr (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                             ((\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))
                                               o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))))"
            by fast
          hence "restrict ((\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))
                            o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                          (HomC.set (F y, x))
                  = S.Fun (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                  ((\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))
                                    o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))))"
            by simp
          also have "... = S.Fun (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                       ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                                         o (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x))))"
            using 2 by presburger
          also have "... = restrict ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                                      o (\<phi>C (F y', x') o (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x)))
                                    (HomC.set (F y, x))"
            using 4 S.Fun_mkArr by blast
          finally show ?thesis by auto
        qed
        hence 5: "((\<phi>D (y', G x') \<circ> (\<lambda>h. D (G f) (D h g)) \<circ> \<psi>D (y, G x))
                    \<circ> (\<phi>D (y, G x) \<circ> \<phi> y \<circ> \<psi>C (F y, x))) (\<phi>C (F y, x) h) =
                   (\<phi>D (y', G x') \<circ> \<phi> y' \<circ> \<psi>C (F y', x')
                     \<circ> (\<phi>C (F y', x') \<circ> (\<lambda>h. C f (C h (F g)))) \<circ> \<psi>C (F y, x)) (\<phi>C (F y, x) h)"
        proof -
          have "\<phi>C (F y, x) h \<in> HomC.set (F y, x)"
            using x y h HomC.\<phi>_mapsto [of "F y" x] by auto
          thus ?thesis
            using 0 h restr_eqE [of "(\<phi>D (y', G x') \<circ> (\<lambda>h. D (G f) (D h g)) \<circ> \<psi>D (y, G x))
                                      \<circ> (\<phi>D (y, G x) \<circ> \<phi> y \<circ> \<psi>C (F y, x))"
                                    "HomC.set (F y, x)"
                                    "(\<phi>D (y', G x') \<circ> \<phi> y' \<circ> \<psi>C (F y', x'))
                                       \<circ> (\<phi>C (F y', x') \<circ> (\<lambda>h. C f (C h (F g))) o \<psi>C (F y, x))"]
            by fast
        qed
        show ?thesis
        proof -
          have "\<phi> y' (C f (C h (F g))) =
                  \<psi>D (y', G x') (\<phi>D (y', G x') (\<phi> y' (\<psi>C (F y', x') (\<phi>C (F y', x')
                     (C f (C (\<psi>C (F y, x) (\<phi>C (F y, x) h)) (F g)))))))"
            using x y x' y' f g h \<phi>_mapsto [of y' x'] HomC.\<psi>_\<phi> [of "F y" x]
                  HomC.\<psi>_\<phi> [of "F y'" x'] HomD.\<psi>_\<phi> [of y' "G x'"]

          proof -
            have "\<psi>D (y', G x') (\<phi>D (y', G x') (\<phi> y' (\<psi>C (F y', x') (\<phi>C (F y', x')
                     (C f (C (\<psi>C (F y, x) (\<phi>C (F y, x) h)) (F g)))))))
                    = \<psi>D (y', G x') (\<phi>D (y', G x') (\<phi> y' (\<psi>C (F y', x') (\<phi>C (F y', x')
                         (C f (C h (F g)))))))"
              using x y h HomC.\<psi>_\<phi> [of "F y" x] by simp
            also have "... = \<psi>D (y', G x') (\<phi>D (y', G x') (\<phi> y' (C f (C h (F g)))))"
              using f g h by simp
            also have "... = \<phi> y' (C f (C h (F g)))"
            proof -
              have "\<phi> y' (C f (C h (F g))) \<in> D.hom y' (G x')"
                using f g h y' x' \<phi>_mapsto [of y' x'] by auto
              thus ?thesis by simp
            qed
            finally show ?thesis by auto
          qed
          also have "... = \<psi>D (y', G x') (\<phi>D (y', G x') (D (G f) (D (\<psi>D (y, G x)
                              (\<phi>D (y, G x) (\<phi> y (\<psi>C (F y, x) (\<phi>C (F y, x) h))))) g)))"
            using 5 by force
          also have "... = D (G f) (D (\<phi> y h) g)"
          proof -
            have \<phi>yh: "\<phi> y h \<in> D.hom y (G x)"
              using x y h \<phi>_mapsto [of y x] by auto
            have "\<psi>D (y', G x') (\<phi>D (y', G x') (D (G f) (D (\<psi>D (y, G x)
                     (\<phi>D (y, G x) (\<phi> y (\<psi>C (F y, x) (\<phi>C (F y, x) h))))) g))) =
                  \<psi>D (y', G x') (\<phi>D (y', G x') (D (G f) (D (\<psi>D (y, G x)
                     (\<phi>D (y, G x) (\<phi> y h))) g)))"   
              using x y f g h by auto
            also have "... = \<psi>D (y', G x') (\<phi>D (y', G x') (D (G f) (D (\<phi> y h) g)))"
              using \<phi>yh x' y' f g by simp
            also have "... = D (G f) (D (\<phi> y h) g)"
              using x y f g h \<phi>yh by simp
            finally show ?thesis by auto
          qed
          finally show ?thesis by auto
        qed
      qed
    qed

    theorem induces_meta_adjunction:
    shows "meta_adjunction C D F G \<phi> \<psi>" ..

  end

  section "Putting it All Together"

  text{*
    Combining the above results, an interpretation of any one of the locales:
    @{text left_adjoint_functor}, @{text right_adjoint_functor}, @{text meta_adjunction},
    @{text hom_adjunction}, and @{text unit_counit_adjunction} extends to an interpretation
    of @{text adjunction}.
  *}

  context meta_adjunction
  begin

    interpretation F: left_adjoint_functor D C F using has_left_adjoint_functor by auto
    interpretation G: right_adjoint_functor C D G using has_right_adjoint_functor by auto

    interpretation \<eta>\<epsilon>: unit_counit_adjunction C D F G \<eta> \<epsilon>
      using induces_unit_counit_adjunction by auto

    interpretation \<Phi>\<Psi>: hom_adjunction C D SetCat.comp \<phi>C \<phi>D F G \<Phi> \<Psi>
      using induces_hom_adjunction by auto

    theorem induces_adjunction:
    shows "adjunction C D SetCat.comp \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>"
      apply (unfold_locales)
      using \<epsilon>_map_simp \<eta>_map_simp \<phi>_in_terms_of_\<eta> \<phi>_in_terms_of_\<Phi>' \<psi>_in_terms_of_\<epsilon>
            \<psi>_in_terms_of_\<Psi>' \<Phi>_simp \<Psi>_simp
      by auto

  end

  sublocale meta_adjunction \<subseteq> adjunction C D SetCat.comp \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>
    using induces_adjunction by auto

  context unit_counit_adjunction
  begin

    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi> using induces_meta_adjunction by auto

    interpretation F: left_adjoint_functor D C F using \<phi>\<psi>.has_left_adjoint_functor by auto
    interpretation G: right_adjoint_functor C D G using \<phi>\<psi>.has_right_adjoint_functor by auto

    abbreviation HomC where "HomC \<equiv> \<phi>\<psi>.HomC"
    abbreviation \<phi>C where "\<phi>C \<equiv> \<phi>\<psi>.\<phi>C"
    abbreviation HomD where "HomD \<equiv> \<phi>\<psi>.HomD"
    abbreviation \<phi>D where "\<phi>D \<equiv> \<phi>\<psi>.\<phi>D"
    abbreviation \<Phi> where "\<Phi> \<equiv> \<phi>\<psi>.\<Phi>"
    abbreviation \<Psi> where "\<Psi> \<equiv> \<phi>\<psi>.\<Psi>"

    interpretation \<Phi>\<Psi>: hom_adjunction C D SetCat.comp \<phi>C \<phi>D F G \<Phi> \<Psi>
      using \<phi>\<psi>.induces_hom_adjunction by auto

    theorem induces_adjunction:
    shows "adjunction C D SetCat.comp \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>"
      apply (unfold_locales)
      using \<epsilon>_in_terms_of_\<psi> \<eta>_in_terms_of_\<phi> \<phi>\<psi>.\<phi>_in_terms_of_\<Phi>' \<psi>_def \<phi>\<psi>.\<psi>_in_terms_of_\<Psi>'
            \<phi>\<psi>.\<Phi>_simp \<phi>\<psi>.\<Psi>_simp \<phi>_def
      by auto

  end

  text{*
    The following fails, claiming ``roundup bound exceeded'':\\
  @{theory_text
  "sublocale unit_counit_adjunction \<subseteq> adjunction C D SetCat.comp \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>
     using induces_adjunction by auto"}
  *}
   
  context hom_adjunction
  begin
   
    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi>
      using induces_meta_adjunction by auto

    interpretation F: left_adjoint_functor D C F using \<phi>\<psi>.has_left_adjoint_functor by auto
    interpretation G: right_adjoint_functor C D G using \<phi>\<psi>.has_right_adjoint_functor by auto

    abbreviation \<eta> where "\<eta> \<equiv> \<phi>\<psi>.\<eta>"
    abbreviation \<epsilon> where "\<epsilon> \<equiv> \<phi>\<psi>.\<epsilon>"

    interpretation \<eta>\<epsilon>: unit_counit_adjunction C D F G \<eta> \<epsilon>
      using \<phi>\<psi>.induces_unit_counit_adjunction by auto

    theorem induces_adjunction:
    shows "adjunction C D S \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>"
    proof
      fix x
      assume "C.ide x"
      thus "\<epsilon> x = \<psi> x (G x)" using \<phi>\<psi>.\<epsilon>_map_simp by blast
      next
      fix y
      assume "D.ide y"
      thus "\<eta> y = \<phi> y (F y)" using \<phi>\<psi>.\<eta>_map_simp by blast
      fix x y f
      assume y: "D.ide y" and f: "f \<in> C.hom (F y) x"
      show "\<phi> y f = D (G f) (\<eta> y)" using y f using "\<phi>\<psi>.\<phi>_in_terms_of_\<eta>" by blast
      show "\<phi> y f = (\<psi>D (y, G x) o \<Phi>.FUN (y, x) o \<phi>C (F y, x)) f" using y f \<phi>_def by simp
      next
      fix x y g
      assume x: "C.ide x" and g: "g \<in> D.hom y (G x)"
      show "\<psi> x g = C (\<epsilon> x) (F g)" using x g "\<phi>\<psi>.\<psi>_in_terms_of_\<epsilon>" by blast
      show "\<psi> x g = (\<psi>C (F y, x) o \<Psi>.FUN (y, x) o \<phi>D(y, G x)) g" using x g \<psi>_def by fast
      next
      fix x y
      assume x: "C.ide x" and y: "D.ide y"
      show "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                               (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
        using x y \<Phi>_simp by fast
      show "\<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
        using x y \<Psi>_simp by fast
    qed

  end

  text{*
    The following fails for unknown reasons:\\
  @{theory_text
  "sublocale hom_adjunction \<subseteq> adjunction C D S \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>
    using induces_adjunction by auto"}
  *}

  context left_adjoint_functor
  begin

    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi>
      using induces_meta_adjunction by auto

    abbreviation HomC where "HomC \<equiv> \<phi>\<psi>.HomC"
    abbreviation \<phi>C where "\<phi>C \<equiv> \<phi>\<psi>.\<phi>C"
    abbreviation HomD where "HomD \<equiv> \<phi>\<psi>.HomD"
    abbreviation \<phi>D where "\<phi>D \<equiv> \<phi>\<psi>.\<phi>D"
    abbreviation \<eta> where "\<eta> \<equiv> \<phi>\<psi>.\<eta>"
    abbreviation \<epsilon> where "\<epsilon> \<equiv> \<phi>\<psi>.\<epsilon>"
    abbreviation \<Phi> where "\<Phi> \<equiv> \<phi>\<psi>.\<Phi>"
    abbreviation \<Psi> where "\<Psi> \<equiv> \<phi>\<psi>.\<Psi>"

    theorem induces_adjunction:
    shows "adjunction C D SetCat.comp \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>"
      using \<phi>\<psi>.induces_adjunction by auto

  end

  sublocale left_adjoint_functor \<subseteq> adjunction C D SetCat.comp \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>
    using induces_adjunction by auto

  context right_adjoint_functor
  begin

    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi>
      using induces_meta_adjunction by auto

    abbreviation HomC where "HomC \<equiv> \<phi>\<psi>.HomC"
    abbreviation \<phi>C where "\<phi>C \<equiv> \<phi>\<psi>.\<phi>C"
    abbreviation HomD where "HomD \<equiv> \<phi>\<psi>.HomD"
    abbreviation \<phi>D where "\<phi>D \<equiv> \<phi>\<psi>.\<phi>D"
    abbreviation \<eta> where "\<eta> \<equiv> \<phi>\<psi>.\<eta>"
    abbreviation \<epsilon> where "\<epsilon> \<equiv> \<phi>\<psi>.\<epsilon>"
    abbreviation \<Phi> where "\<Phi> \<equiv> \<phi>\<psi>.\<Phi>"
    abbreviation \<Psi> where "\<Psi> \<equiv> \<phi>\<psi>.\<Psi>"

    theorem induces_adjunction:
    shows "adjunction C D SetCat.comp \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>"
      using \<phi>\<psi>.induces_adjunction by auto

  end

  text{*
    The following fails, claiming ``roundup bound exceeded'':\\
  @{theory_text
  "sublocale right_adjoint_functor \<subseteq> adjunction C D SetCat.comp \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>
    using induces_adjunction by auto"}
  *}

  definition adjoint_functors
  where "adjoint_functors C D F G = (\<exists>\<phi> \<psi>. meta_adjunction C D F G \<phi> \<psi>)"

  section "Composition of Adjunctions"

  locale composite_adjunction =
    A: category A +
    B: category B +
    C: category C +
    F: "functor" B A F +
    G: "functor" A B G +
    F': "functor" C B F' +
    G': "functor" B C G' +
    FG: meta_adjunction A B F G \<phi> \<psi> +
    F'G': meta_adjunction B C F' G' \<phi>' \<psi>'
  for A :: "'a comp"
  and B :: "'b comp"
  and C :: "'c comp"
  and F :: "'b \<Rightarrow> 'a"
  and G :: "'a \<Rightarrow> 'b"
  and F' :: "'c \<Rightarrow> 'b"
  and G' :: "'b \<Rightarrow> 'c"
  and \<phi> :: "'b \<Rightarrow> 'a \<Rightarrow> 'b"
  and \<psi> :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"
  and \<phi>' :: "'c \<Rightarrow> 'b \<Rightarrow> 'c"
  and \<psi>' :: "'b \<Rightarrow> 'c \<Rightarrow> 'b"
  begin

    lemma is_meta_adjunction:
    shows "meta_adjunction A C (F o F') (G' o G) (\<lambda>z. \<phi>' z o \<phi> (F' z)) (\<lambda>x. \<psi> x o \<psi>' (G x))"
    proof -
      interpret G'oG: composite_functor A B C G G' ..
      interpret FoF': composite_functor C B A F' F ..
      show ?thesis
      proof
        fix y f x
        assume y: "C.ide y" and f: "f \<in> A.hom (FoF'.map y) x"
        show "(\<phi>' y \<circ> \<phi> (F' y)) f \<in> C.hom y (G'oG.map x)"
          using y f FG.\<phi>_mapsto F'G'.\<phi>_mapsto by simp
        show "(\<psi> x \<circ> \<psi>' (G x)) ((\<phi>' y \<circ> \<phi> (F' y)) f) = f"
          using y f FG.\<phi>_mapsto F'G'.\<phi>_mapsto FG.\<psi>_\<phi> F'G'.\<psi>_\<phi> by simp
        next
        fix x g y
        assume x: "A.ide x" and g: "g \<in> C.hom y (G'oG.map x)"
        show "(\<psi> x \<circ> \<psi>' (G x)) g \<in> A.hom (FoF'.map y) x"
          using x g FG.\<psi>_mapsto F'G'.\<psi>_mapsto by auto
        show "(\<phi>' y \<circ> \<phi> (F' y)) ((\<psi> x \<circ> \<psi>' (G x)) g) = g"
          using x g FG.\<psi>_mapsto F'G'.\<psi>_mapsto FG.\<phi>_\<psi> F'G'.\<phi>_\<psi> by simp
        next
        fix f x x' g y' y h
        assume f: "f \<in> A.hom x x'" and g: "g \<in> C.hom y' y"
        and h: "h \<in> A.hom (FoF'.map y) x"
        show "(\<phi>' y' \<circ> \<phi> (F' y')) (A f (A h (FoF'.map g))) = C (G'oG.map f) (C ((\<phi>' y \<circ> \<phi> (F' y)) h) g)"
          using f g h FG.naturality F'G'.naturality
                FG.\<phi>_mapsto F'G'.\<phi>_mapsto FG.\<psi>_mapsto F'G'.\<psi>_mapsto
          by auto
      qed
    qed

  end

  sublocale composite_adjunction \<subseteq> meta_adjunction A C "F o F'" "G' o G"
                                     "\<lambda>z. \<phi>' z o \<phi> (F' z)" "\<lambda>x. \<psi> x o \<psi>' (G x)"
    using is_meta_adjunction by auto

  context composite_adjunction
  begin

    interpretation K\<eta>H: natural_transformation C C "G' o F'" "G' o G o F o F'" "G' o FG.\<eta> o F'"
    proof -
      interpret \<eta>F': horizontal_composite C B B F' F' B.map "G o F" F' FG.\<eta> ..
      interpret G'\<eta>F': horizontal_composite C B C "B.map o F'" "G o F o F'" G' G' \<eta>F'.map G' ..
      have "natural_transformation C C (G' o (B.map o F')) (G' o (G o F o F')) (G' o (FG.\<eta> o F'))" ..
      moreover have "G' o (B.map o F') = G' o F'"
        using F'.functor_axioms by auto
      moreover have "G' o (G o F o F') = G' o G o F o F'" by auto
      moreover have "G' o (FG.\<eta> o F') = G' o FG.\<eta> o F'" by auto
      ultimately show "natural_transformation C C (G' o F') (G' o G o F o F') (G' o FG.\<eta> o F')"
        by auto
    qed
    interpretation G'\<eta>F'o\<eta>': vertical_composite C C C.map "G' o F'" "G' o G o F o F'"
                             F'G'.\<eta> "G' o FG.\<eta> o F'" ..

    interpretation F\<epsilon>G: natural_transformation A A "F o F' o G' o G" "F o G" "F o F'G'.\<epsilon> o G"
    proof -
      interpret F\<epsilon>': horizontal_composite B B A "F' o G'" B.map F F F'G'.\<epsilon> F ..
      interpret F\<epsilon>'G: horizontal_composite A B A G G "F o (F' o G')" "F o B.map" G F\<epsilon>'.map ..
      have "natural_transformation A A (F o (F' o G') o G) (F o B.map o G) F\<epsilon>'G.map" ..
      moreover have "F o B.map o G = F o G"
      proof -
        (* Here F.functor_axioms does not refer to functor F, why? *)
        have "functor B A F" ..
        thus ?thesis using Functor.comp_ide_dom by auto
      qed
      moreover have "F o (F' o G') o G = F o F' o G' o G" by auto
      ultimately show "natural_transformation A A (F o F' o G' o G) (F o G) (F o F'G'.\<epsilon> o G)"
        by auto
    qed
    interpretation \<epsilon>oF\<epsilon>'G: vertical_composite A A "F \<circ> F' \<circ> G' \<circ> G" "F o G" A.map
                             "F o F'G'.\<epsilon> o G" FG.\<epsilon> ..

    lemma \<eta>_char:
    shows "\<eta> = G'\<eta>F'o\<eta>'.map"
    proof (intro NaturalTransformation.eqI)
      show "natural_transformation C C C.map (G' o G o F o F') G'\<eta>F'o\<eta>'.map" ..
      show "natural_transformation C C C.map (G' o G o F o F') \<eta>"
      proof -
        have "natural_transformation C C C.map ((G' \<circ> G) \<circ> (F \<circ> F')) \<eta>" ..
        moreover have "(G' o G) o (F o F') = G' o G o F o F'" by auto
        ultimately show ?thesis by metis
      qed
      fix a
      assume a: "C.ide a"
      show "\<eta> a = G'\<eta>F'o\<eta>'.map a"
        using a \<eta>_map_simp [of a] FG.\<phi>_in_terms_of_\<eta> [of "F' a" "(F o F') a"]
              F'G'.\<phi>_in_terms_of_\<eta> [of a "FG.\<eta> (F' a)"] G'\<eta>F'o\<eta>'.map_def
        by fastforce
    qed

    lemma \<epsilon>_char:
    shows "\<epsilon> = \<epsilon>oF\<epsilon>'G.map"
    proof (intro NaturalTransformation.eqI)
      show "natural_transformation A A (F o F' o G' o G) A.map \<epsilon>"
      proof -
        have "natural_transformation A A ((F \<circ> F') \<circ> (G' \<circ> G)) A.map \<epsilon>" ..
        moreover have "(F o F') o (G' o G) = F o F' o G' o G" by auto
        ultimately show ?thesis by metis
      qed
      show "natural_transformation A A (F \<circ> F' \<circ> G' \<circ> G) A.map \<epsilon>oF\<epsilon>'G.map" ..
      fix a
      assume a: "A.ide a"
      show "\<epsilon> a = \<epsilon>oF\<epsilon>'G.map a"
        using a \<epsilon>_map_simp FG.\<psi>_in_terms_of_\<epsilon> F'G'.\<psi>_in_terms_of_\<epsilon> \<epsilon>oF\<epsilon>'G.map_def by auto
    qed

  end

  section "Right Adjoints are Unique up to Natural Isomorphism"

  text{*
    As an example of the use of the of the foregoing development, we show that two right adjoints
    to the same functor are naturally isomorphic.
  *}

  theorem two_right_adjoints_naturally_isomorphic:
  assumes "adjoint_functors C D F G" and "adjoint_functors C D F G'"
  shows "naturally_isomorphic C D G G'"
  proof -
    text{*
      For any object @{term x} of @{term C}, we have that @{text "\<epsilon> x \<in> C.hom (F (G x)) x"}
      is a terminal arrow from @{term F} to @{term x}, and similarly for @{text "\<epsilon>' x"}.
      We may therefore obtain the unique coextension @{text "\<tau> x \<in> D.hom (G x) (G' x)"}
      of @{text "\<epsilon> x"} along @{text "\<epsilon>' x"}.
      An explicit formula for @{text "\<tau> x"} is @{text "D (G' (\<epsilon> x)) (\<eta>' (G x))"}.
      Similarly, we obtain @{text "\<tau>' x = D (G (\<epsilon>' x)) (\<eta> (G' x)) \<in> D.hom (G' x) (G x)"}.
      We show these are the components of inverse natural transformations between
      @{term G} and @{term G'}.
    *}
    obtain \<phi> \<psi> where \<phi>\<psi>: "meta_adjunction C D F G \<phi> \<psi>"
      using assms adjoint_functors_def by blast
    obtain \<phi>' \<psi>' where \<phi>'\<psi>': "meta_adjunction C D F G' \<phi>' \<psi>'"
      using assms adjoint_functors_def by blast
    interpret Adj: meta_adjunction C D F G \<phi> \<psi> using \<phi>\<psi> by auto
    interpret Adj: adjunction C D SetCat.comp Adj.\<phi>C Adj.\<phi>D F G \<phi> \<psi> Adj.\<eta> Adj.\<epsilon> Adj.\<Phi> Adj.\<Psi>
      using Adj.induces_adjunction by auto
    interpret Adj': meta_adjunction C D F G' \<phi>' \<psi>' using \<phi>'\<psi>' by auto
    interpret Adj': adjunction C D SetCat.comp Adj'.\<phi>C Adj'.\<phi>D
                               F G' \<phi>' \<psi>' Adj'.\<eta> Adj'.\<epsilon> Adj'.\<Phi> Adj'.\<Psi>
      using Adj'.induces_adjunction by auto
    let ?\<tau>o = "\<lambda>a. D (G' (Adj.\<epsilon> a)) (Adj'.\<eta> (G a))"
    interpret \<tau>: transformation_by_components C D G G' ?\<tau>o
    proof
      show "\<And>a. Adj.C.ide a \<Longrightarrow> D (G' (Adj.\<epsilon> a)) (Adj'.\<eta> (G a)) \<in> Adj.D.hom (G a) (G' a)"
        by simp
      show "\<And>f. Adj.C.arr f \<Longrightarrow>
                   D (D (G' (Adj.\<epsilon> (Adj.C.cod f))) (Adj'.\<eta> (G (Adj.C.cod f)))) (G f) =
                             D (G' f) (D (G' (Adj.\<epsilon> (Adj.C.dom f))) (Adj'.\<eta> (G (Adj.C.dom f))))"
      proof -
        fix f
        assume f: "Adj.C.arr f"
        let ?x = "Adj.C.dom f"
        let ?x' = "Adj.C.cod f"
        have "D (D (G' (Adj.\<epsilon> ?x')) (Adj'.\<eta> (G ?x'))) (G f)
                       = D (G' (C (Adj.\<epsilon> ?x') (F (G f)))) (Adj'.\<eta> (G ?x))"
          using f Adj'.\<eta>.is_natural_1 [of "G f"] Adj'.\<eta>.is_natural_2 [of "G f"] by simp
        also have "... = D (G' (C f (Adj.\<epsilon> ?x))) (Adj'.\<eta> (G ?x))"
          using f Adj.\<epsilon>.is_natural_2 [of f] Adj.\<epsilon>.is_natural_1 [of f] by simp
        also have "... = D (G' f) (D (G' (Adj.\<epsilon> (Adj.C.dom f))) (Adj'.\<eta> (G (Adj.C.dom f))))"
          using f by simp
        finally show "D (D (G' (Adj.\<epsilon> ?x')) (Adj'.\<eta> (G ?x'))) (G f)
                         = D (G' f) (D (G' (Adj.\<epsilon> (Adj.C.dom f))) (Adj'.\<eta> (G (Adj.C.dom f))))"
          by auto
      qed
    qed
    interpret natural_isomorphism C D G G' \<tau>.map
    proof
      fix a
      assume a: "Adj.C.ide a"
      show "Adj.D.iso (\<tau>.map a)"
      proof
        show "Adj.D.inverse_arrows (\<tau>.map a) (\<phi> (G' a) (Adj'.\<epsilon> a))"
        proof
          have 1: "\<tau>.map a = D (G' (Adj.\<epsilon> a)) (Adj'.\<eta> (G a))"
            using a Adj'.\<phi>_in_terms_of_\<eta> by simp
          have antipar: "Adj.D.antipar (\<tau>.map a) (\<phi> (G' a) (Adj'.\<epsilon> a))"
            using a 1 Adj.\<phi>_mapsto Adj'.\<phi>_mapsto by auto
          text{*
            The proof that the two composites are identities is a modest diagram chase.
            This is a good example of the inference rules for the @{text category},
            @{text functor}, and @{text natural_transformation} locales in action.
            Isabelle is able to use the single hypothesis that @{text a} is an identity to
            implicitly fill in all the details that the various quantities are in fact arrows
            and that the indicated composites are all well-defined, as well as to apply
            associativity of composition.  In most cases, this is done by auto or simp without
            even mentioning any of the rules that are used.
$$\xymatrix{
        {G' a} \ar[dd]_{\eta'(G'a)} \ar[rr]^{\tau' a} \ar[dr]_{\eta(G'a)}
           && {G a} \ar[rr]^{\tau a} \ar[dr]_{\eta'(Ga)} && {G' a}                     \\
        & {GFG'a} \rrtwocell\omit{\omit(2)} \ar[ur]_{G(\epsilon' a)} \ar[dr]_{\eta'(GFG'a)}
           && {G'FGa} \drtwocell\omit{\omit(3)} \ar[ur]_{G'(\epsilon' a)} &            \\
        {G'FG'a} \urtwocell\omit{\omit(1)} \ar[rr]_{\eta'(GFG'a)} \ar@/_8ex/[rrrr]_{G'FG'a}
           && {G'FGFG'a} \dtwocell\omit{\omit(4)} \ar[ru]_{G'FG(\epsilon' a)} \ar[rr]_{G'(\epsilon(FG'a))}
           && {G'FG'a} \ar[uu]_{G'(\epsilon a')}                                       \\
           &&&&
}$$
          *}
          show "Adj.D.ide (D (\<tau>.map a) (\<phi> (G' a) (Adj'.\<epsilon> a)))"
          proof -
            have "D (\<tau>.map a) (\<phi> (G' a) (Adj'.\<epsilon> a)) = G' a"
            proof -
              have 1: "D (Adj'.\<eta> (G (F (G' a)))) (Adj.\<eta> (G' a))
                         = D (G' (F (Adj.\<eta> (G' a)))) (Adj'.\<eta> (G' a))"
                using a Adj'.\<eta>.is_natural_1 [of "Adj.\<eta> (G' a)"]
                      Adj'.\<eta>.is_natural_2 [of "Adj.\<eta> (G' a)"]
                by simp
              have 2: "D (Adj'.\<eta> (G a)) (G (Adj'.\<epsilon> a))
                         = D (G' (F (G (Adj'.\<epsilon> a)))) (Adj'.\<eta> (G (F (G' a))))"
                using a Adj'.\<eta>.is_natural_1 [of "G (Adj'.\<epsilon> a)"]
                      Adj'.\<eta>.is_natural_2 [of "G (Adj'.\<epsilon> a)"]
                by simp
              have 3: "D (G' (Adj.\<epsilon> a)) (G' (F (G (Adj'.\<epsilon> a))))
                         = D (G' (Adj'.\<epsilon> a)) (G' (Adj.\<epsilon> (F (G' a))))"
              proof -
                have "C (Adj.\<epsilon> a) (F (G (Adj'.\<epsilon> a))) = C (Adj'.\<epsilon> a) (Adj.\<epsilon> (F (G' a)))"
                  using a Adj.\<epsilon>.is_natural_1 [of "Adj'.\<epsilon> a"] Adj.\<epsilon>.is_natural_2 [of "Adj'.\<epsilon> a"]
                  by simp
                hence "G' (C (Adj.\<epsilon> a) (F (G (Adj'.\<epsilon> a)))) = G' (C (Adj'.\<epsilon> a) (Adj.\<epsilon> (F (G' a))))"
                  by presburger
                thus ?thesis using a by force
              qed
              have 4: "D (G' (Adj.\<epsilon> (F (G' a)))) (G' (F (Adj.\<eta> (G' a)))) = G' (F (G' a))"
              proof -
                have "D (G' (Adj.\<epsilon> (F (G' a)))) (G' (F (Adj.\<eta> (G' a))))
                         = G' (Adj.\<epsilon>FoF\<eta>.map (G' a))"
                  using a Adj.\<epsilon>FoF\<eta>.map_simp_1 [of "G' a"] by simp
                moreover have "Adj.\<epsilon>FoF\<eta>.map (G' a) = F (G' a)"
                  using a by (simp add: Adj.\<eta>\<epsilon>.triangle_F)
                ultimately show ?thesis by auto
              qed
              have "D (\<tau>.map a) (\<phi> (G' a) (Adj'.\<epsilon> a))
                          = D (G' (Adj.\<epsilon> a)) (D (D (Adj'.\<eta> (G a)) (G (Adj'.\<epsilon> a))) (Adj.\<eta> (G' a)))"
                using a \<tau>.map_simp_ide Adj.\<phi>_in_terms_of_\<eta> Adj'.\<phi>_in_terms_of_\<eta> by simp
              also have "... = D (G' (Adj.\<epsilon> a))
                                 (D (D (G' (F (G (Adj'.\<epsilon> a)))) (Adj'.\<eta> (G (F (G' a)))))
                                    (Adj.\<eta> (G' a)))"
                using a 2 by presburger
              also have "... = D (D (G' (Adj.\<epsilon> a)) (G' (F (G (Adj'.\<epsilon> a)))))
                                 (D (G' (F (Adj.\<eta> (G' a)))) (Adj'.\<eta> (G' a)))"
                using a 1 by simp (* 30 sec *)
              also have "... = D (G' (Adj'.\<epsilon> a))
                                 (D (D (G' (Adj.\<epsilon> (F (G' a)))) (G' (F (Adj.\<eta> (G' a)))))
                                    (Adj'.\<eta> (G' a)))"
                using a 3 by simp
              also have "... = D (G' (Adj'.\<epsilon> a)) (Adj'.\<eta> (G' a))"
                using a 4 by auto
              also have "... = G' a"
                using a Adj'.\<eta>\<epsilon>.triangle_G Adj'.G\<epsilon>o\<eta>G.map_simp_1 [of a] by simp
              finally show ?thesis by auto
            qed
            thus ?thesis using a antipar by simp
          qed
          show "Adj.D.ide (D (\<phi> (G' a) (Adj'.\<epsilon> a)) (\<tau>.map a))"
          proof -
            have "D (\<phi> (G' a) (Adj'.\<epsilon> a)) (\<tau>.map a) = G a"
            proof -
              have 1: "D (Adj.\<eta> (G' (F (G a)))) (Adj'.\<eta> (G a))
                         = D (G (F (Adj'.\<eta> (G a)))) (Adj.\<eta> (G a))"
                using a Adj.\<eta>.is_natural_1 [of "Adj'.\<eta> (G a)"]
                      Adj.\<eta>.is_natural_2 [of "Adj'.\<eta> (G a)"]
                by simp
              have 2: "D (Adj.\<eta> (G' a)) (G' (Adj.\<epsilon> a))
                         = D (G (F (G' (Adj.\<epsilon> a)))) (Adj.\<eta> (G' (F (G a))))"
                using a Adj.\<eta>.is_natural_1 [of "G' (Adj.\<epsilon> a)"]
                      Adj.\<eta>.is_natural_2 [of "G' (Adj.\<epsilon> a)"]
                by simp
              have 3: "D (G (Adj'.\<epsilon> a)) (G (F (G' (Adj.\<epsilon> a))))
                         = D (G (Adj.\<epsilon> a)) (G (Adj'.\<epsilon> (F (G a))))"
              proof -
                have "C (Adj'.\<epsilon> a) (F (G' (Adj.\<epsilon> a))) = C (Adj.\<epsilon> a) (Adj'.\<epsilon> (F (G a)))"
                  using a Adj'.\<epsilon>.is_natural_1 [of "Adj.\<epsilon> a"] Adj'.\<epsilon>.is_natural_2 [of "Adj.\<epsilon> a"]
                  by simp
                hence "G (C (Adj'.\<epsilon> a) (F (G' (Adj.\<epsilon> a)))) = G (C (Adj.\<epsilon> a) (Adj'.\<epsilon> (F (G a))))"
                  by presburger
                thus ?thesis using a by force
              qed
              have 4: "D (G (Adj'.\<epsilon> (F (G a)))) (G (F (Adj'.\<eta> (G a)))) = G (F (G a))"
              proof -
                have "D (G (Adj'.\<epsilon> (F (G a)))) (G (F (Adj'.\<eta> (G a))))
                         = G (Adj'.\<epsilon>FoF\<eta>.map (G a))"
                  using a Adj'.\<epsilon>FoF\<eta>.map_simp_1 [of "G a"] by simp
                moreover have "Adj'.\<epsilon>FoF\<eta>.map (G a) = F (G a)"
                  using a by (simp add: Adj'.\<eta>\<epsilon>.triangle_F)
                ultimately show ?thesis by auto
              qed
              have "D (\<phi> (G' a) (Adj'.\<epsilon> a)) (\<tau>.map a)
                          = D (G (Adj'.\<epsilon> a))
                                 (D (D (Adj.\<eta> (G' a)) (G' (Adj.\<epsilon> a))) (Adj'.\<eta> (G a)))"
                using a \<tau>.map_simp_ide Adj.\<phi>_in_terms_of_\<eta> Adj'.\<phi>_in_terms_of_\<eta> by simp
              also have "... = D (G (Adj'.\<epsilon> a))
                                 (D (D (G (F (G' (Adj.\<epsilon> a)))) (Adj.\<eta> (G' (F (G a)))))
                                    (Adj'.\<eta> (G a)))"
                using a 2 by presburger
              also have "... = D (D (G (Adj'.\<epsilon> a)) (G (F (G' (Adj.\<epsilon> a)))))
                                 (D (G (F (Adj'.\<eta> (G a)))) (Adj.\<eta> (G a)))"
                using a 1 by simp (* 30 sec *)
              also have "... = D (G (Adj.\<epsilon> a))
                                 (D (D (G (Adj'.\<epsilon> (F (G a)))) (G (F (Adj'.\<eta> (G a)))))
                                    (Adj.\<eta> (G a)))"
                using a 3 by simp
              also have "... = D (G (Adj.\<epsilon> a)) (Adj.\<eta> (G a))"
                using a 4 by auto
              also have "... = G a"
                using a Adj.\<eta>\<epsilon>.triangle_G Adj.G\<epsilon>o\<eta>G.map_simp_1 [of a] by simp
              finally show ?thesis by auto
            qed
            thus ?thesis using a by auto
          qed
        qed
      qed
    qed
    have "natural_isomorphism C D G G' \<tau>.map" ..
    thus "naturally_isomorphic C D G G'"
      using naturally_isomorphic_def by blast
  qed

end
