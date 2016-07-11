(*  Title:       FunctorCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter FunctorCategory

theory FunctorCategory
imports Category AbstractedCategory BinaryFunctor
begin

  text{*
    The functor category @{text "[A, B]"} is the category whose objects are functors
    from @{term A} to @{term B} and whose arrows correspond to natural transformations
    between these functors.
    Since the arrows of a functor category cannot (in the context of the present development)
    be directly identified with natural transformations, but rather only with natural
    transformations that have been equipped with their domain and codomain functors,
    and since there is no natural value to serve as @{term null},
    the construction here is a bit more involved than most of the other constructions
    on categories we have defined so far.
    What we do first is to construct a ``classical category'' whose objects are
    functors and whose arrows are natural transformations.  Then, we extract from this
    construction a partial composition using the standard result proved in the
    @{text "classical_category"} locale.  The effect of this standard result is to define
    arrows of the resulting category to be triples that consist of natural transformations
    equipped with their domain and codomain functors, injected into an option type
    in order to provide a value to be used as @{term null}.
    We then use the @{text abstracted_category} locale to lift the resulting category to an
    opaque arrow type, to avoid the possibility of a client of this theory inadvertently
    depending on the details of the concrete construction.
    Finally, we define a set of constructors for the opaque arrow type and characterize the
    resulting category in terms of these constructors so that the details of the concrete
    construction are no longer required and only the constructors and associated facts need
    be used.
  *}

  section "Construction"

  text{*
    In this section a construction for functor categories is given.
    For convenience, we proceed indirectly, by way of the @{text "classical_category"} locale,
    though the construction could also have been done directly.
    Some auxiliary definitions are involved, but these are declared ``private'' and in
    the end what is exported is an opaque arrow type, a partial composition operation on
    this arrow type defining the category, functions for constructing and destructing arrows,
    and facts that characterize the basic notions (domain, codomain, \emph{etc.}) in terms
    of these functions.
  *}

  locale functor_category =
    A: category A +
    B: category B
  for A :: "'a comp"
  and B :: "'b comp"
  begin

    context begin

      text{*
        First, we construct a ``classical category'' whose objects are functors and
        whose arrows are triples @{text "(\<tau>, (F, G))"}, where @{text F} and @{text G}
        are functors and @{text \<tau>} is a natural transformation from @{text F} to @{text G}.
      *}

      private abbreviation Dom'
      where "Dom' t \<equiv> fst (snd t)"

      private abbreviation Cod'
      where "Cod' t \<equiv> snd (snd t)"

      private abbreviation Fun'
      where "Fun' t \<equiv> fst t"

      private definition Obj'
      where "Obj' F \<equiv> functor A B F"

      private definition Arr'
      where "Arr' t \<equiv> natural_transformation A B (Dom' t) (Cod' t) (Fun' t)"

      private abbreviation Id'
      where "Id' F \<equiv> (F, (F, F))"

      private definition Comp'
      where "Comp' t s \<equiv> (vertical_composite.map A B (Fun' s) (Fun' t), (Dom' s, Cod' t))"

      interpretation CC: classical_category Obj' Arr' Dom' Cod' Id' Comp'
      proof
        fix F
        assume F: "Obj' F"
        show "Arr' (Id' F)"
          using F Arr'_def Obj'_def functor_is_transformation by simp
        show "Dom' (Id' F) = F" using F by (metis fst_conv snd_conv)
        show "Cod' (Id' F) = F" using F by (metis snd_conv)
        next
        fix t
        assume t: "Arr' t"
        interpret \<tau>: natural_transformation A B "Dom' t" "Cod' t" "Fun' t"
          using t Arr'_def by blast
        show "Obj' (Dom' t)" unfolding Obj'_def ..
        show "Obj' (Cod' t)" unfolding Obj'_def ..
        show "Comp' t (Id' (Dom' t)) = t"
          by (metis Comp'_def \<tau>.natural_transformation_axioms fst_conv prod.collapse snd_conv
                    vcomp_ide_dom)
        show "Comp' (Id' (Cod' t)) t = t"
          by (metis (no_types, lifting) Comp'_def \<tau>.natural_transformation_axioms fst_conv
                    prod.collapse snd_conv vcomp_ide_cod)
        fix s
        assume s: "Arr' s"
        and st: "Cod' s = Dom' t"
        show "Arr' (Comp' t s)"
        proof -
          interpret \<sigma>: natural_transformation A B "Dom' s" "Cod' s" "Fun' s"
            using s Arr'_def by blast
          interpret VC: vertical_composite A B "Dom' s" "Cod' s" "Cod' t" "Fun' s" "Fun' t"
            using s t st Arr'_def Obj'_def
            by (simp add: natural_transformation_def vertical_composite.intro)
          have "natural_transformation A B (Dom' s) (Cod' t) (Fun' (Comp' t s))"
            using VC.is_natural_transformation Comp'_def by (metis fst_conv)
          thus ?thesis using s t st Arr'_def Comp'_def by (metis fst_conv snd_conv)
        qed
        show "Dom' (Comp' t s) = Dom' s"
          using Comp'_def fst_conv snd_conv by metis
        show "Cod' (Comp' t s) = Cod' t"
          using Comp'_def snd_conv by metis
        fix r
        assume r: "Arr' r"
        and rs: "Cod' r = Dom' s"
        show "Comp' (Comp' t s) r = Comp' t (Comp' s r)"
        proof -
          have "natural_transformation A B (fst (snd t)) (snd (snd t)) (fst t)"
            using Arr'_def t by blast
          moreover have "natural_transformation A B (fst (snd s)) (snd (snd s)) (fst s)"
            using Arr'_def s by blast
          moreover have "natural_transformation A B (fst (snd r)) (snd (snd r)) (fst r)"
            using Arr'_def r by blast
          ultimately show ?thesis by (simp add: Comp'_def rs st)
        qed
      qed

      private lemma CC_is_classical_category:
      shows "classical_category Obj' Arr' Dom' Cod' Id' Comp'" ..

      text{*
        At this point, @{term CC.comp} is a partial composition that defines a category.
        The arrow type for this category is @{typ "(('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b)) option"},
        because the definition of @{term CC.comp} introduces an option type to provide
        a value to be used as @{term null}.  We next define a corresponding opaque arrow type.
      *}

      typedef ('c, 'd) arr = "UNIV :: (('c \<Rightarrow> 'd) * ('c \<Rightarrow> 'd) * ('c \<Rightarrow> 'd)) option set" ..

      text{*
        The category defined by @{term CC.comp} is then lifted to the opaque arrow type.
      *}

      interpretation AC: abstracted_category CC.comp Abs_arr Rep_arr UNIV
        using Rep_arr_inverse Abs_arr_inverse apply unfold_locales by auto

      text{*
        The function @{term AC.comp} is now the partial composition that defines the
        desired category.
      *}

      definition comp :: "('a, 'b) local.arr comp"
      where "comp \<equiv> AC.comp"

      lemma is_category:
      shows "category comp"
      proof -
        have "category AC.comp" ..
        thus "category comp" using comp_def by auto
      qed

      interpretation category comp
        using is_category by auto

      text{*
        We introduce a constructor @{text mkArr} for building an arrow from two
        functors and a natural transformation.
      *}

      definition mkArr :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) arr"
      where "mkArr F G \<tau> \<equiv> (if natural_transformation A B F G \<tau>
                            then Abs_arr (Some (\<tau>, (F, G))) else null)"

      abbreviation mkIde
      where "mkIde F \<equiv> mkArr F F F"

      text{*
        Destructors @{term Dom}, @{term Cod}, and @{term Fun} extract the components
        of an arrow.
      *}

      definition Dom :: "('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
      where "Dom t \<equiv> Dom' (the (Rep_arr t))"

      definition Cod :: "('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
      where "Cod t \<equiv> Cod' (the (Rep_arr t))"

      definition Fun :: "('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
      where "Fun t \<equiv> Fun' (the (Rep_arr t))"

      text{*
        Finally, we prove a set of facts that characterize the basic categorical notions
        in terms of the constructors and destructors.  These are the facts that will
        be exported.
      *}

      lemma null_char:
      shows "null = Abs_arr None"
        using comp_def AC.null_char CC.null_char by simp

      lemma arr_char:
      shows "arr f \<longleftrightarrow> f \<noteq> null \<and> natural_transformation A B (Dom f) (Cod f) (Fun f)"
        using comp_def not_arr_null Dom_def Cod_def Fun_def null_char AC.arr_char CC.arr_char
              Arr'_def Rep_arr_inverse
        by metis

      lemma dom_char:
      shows "dom f = (if arr f then mkIde (Dom f) else null)"
        using comp_def mkArr_def Dom_def arr_char null_char AC.arr_char AC.dom_char CC.dom_char
              functor_is_transformation natural_transformation_def
        by (metis (no_types, lifting))

      lemma dom_simp:
      assumes "arr t"
      shows "dom t = mkIde (Dom t)"
       using assms dom_char by auto

      lemma cod_char:
      shows "cod f = (if arr f then mkIde (Cod f) else null)"
        using comp_def mkArr_def Cod_def arr_char null_char AC.arr_char AC.cod_char CC.cod_char
              functor_is_transformation natural_transformation_def
        by (metis (no_types, lifting))

      lemma cod_simp:
      assumes "arr t"
      shows "cod t = mkIde (Cod t)"
        using assms cod_char by auto

      lemma Dom_mkArr [simp]:
      assumes "arr (mkArr F G \<tau>)"
      shows "Dom (mkArr F G \<tau>) = F"
        using assms arr_char mkArr_def Dom_def Abs_arr_inverse
        by (metis UNIV_I fst_conv option.sel snd_conv)

      lemma Cod_mkArr [simp]:
      assumes "arr (mkArr F G \<tau>)"
      shows "Cod (mkArr F G \<tau>) = G"
        using assms arr_char mkArr_def Cod_def Abs_arr_inverse
        by (metis UNIV_I option.sel snd_conv)

      lemma Fun_mkArr [simp]:
      assumes "arr (mkArr F G \<tau>)"
      shows "Fun (mkArr F G \<tau>) = \<tau>"
        using assms arr_char mkArr_def Fun_def Abs_arr_inverse
        by (metis UNIV_I fst_conv option.sel)

      lemma arr_mkArr [iff]:
      shows "arr (mkArr F G \<tau>) \<longleftrightarrow> natural_transformation A B F G \<tau>"
        using mkArr_def arr_char null_char Dom_def Cod_def Fun_def Abs_arr_inverse
              UNIV_I fst_conv snd_conv option.sel
        by (metis option.distinct(1))

      lemma mkArr_Fun:
      assumes "arr t"
      shows "mkArr (Dom t) (Cod t) (Fun t) = t"
        using assms arr_char [of t] mkArr_def [of "Dom t" "Cod t" "Fun t"]
        by (metis Cod_def Dom_def Fun_def Rep_arr_inverse null_char option.collapse prod.collapse)

      lemma seq_char:
      shows "seq g f \<longleftrightarrow> arr f \<and> arr g \<and> Cod f = Dom g"
      proof
        assume gf: "seq g f"
        have "Cod f = Dom g"
        proof -
          have 1: "arr (mkIde (Cod f))" using gf arr_dom_iff_arr cod_simp by metis
          have 2: "arr (mkIde (Dom g))" using gf arr_dom_iff_arr dom_simp by metis
          have "Cod f = Dom (mkIde (Cod f))" using 1 by simp
          also have "... = Dom (mkIde (Dom g))" using gf dom_simp cod_simp by auto
          also have "... = Dom g" using 2 by simp
          finally show ?thesis by auto
        qed
        thus "arr f \<and> arr g \<and> Cod f = Dom g" using gf by auto
        next
        assume gf: "arr f \<and> arr g \<and> Cod f = Dom g"
        thus "seq g f" using cod_char dom_char by presburger
      qed

      lemma comp_char:
      shows "comp g f = (if seq g f then
                           mkArr (Dom f) (Cod g) (vertical_composite.map A B (Fun f) (Fun g))
                         else null)"
      proof -
        have "\<not>seq g f \<Longrightarrow> comp g f = null"
          using comp_def AC.comp_char by auto
        moreover have
          "seq g f \<Longrightarrow>
             comp g f = mkArr (Dom f) (Cod g) (vertical_composite.map A B (Fun f) (Fun g))"
        proof -
          assume gf: "seq g f"
          interpret Fun_f: natural_transformation A B "Dom f" "Cod f" "Fun f"
            using gf arr_char by blast
          interpret Fun_g: natural_transformation A B "Cod f" "Cod g" "Fun g"
            using gf arr_char seq_char by simp
          interpret Fun_goFun_f: vertical_composite A B "Dom f" "Cod f" "Cod g" "Fun f" "Fun g" ..
          have "comp g f = Abs_arr (CC.comp (Rep_arr g) (Rep_arr f))"
            using gf comp_def AC.comp_char by simp
          also have "... = Abs_arr (Some (Comp' (the (Rep_arr g)) (the (Rep_arr f))))"
            using gf CC.comp_def arr_char Dom_def [of g] Cod_def [of f] null_char
                  arr_comp calculation
            by auto
          also have "... = Abs_arr (Some (Fun_goFun_f.map, (Dom f, Cod g)))"
            using Comp'_def [of "the (Rep_arr g)" "the (Rep_arr f)"] Dom_def Cod_def Fun_def
            by simp
          also have "... = mkArr (Dom f) (Cod g) Fun_goFun_f.map"
            using mkArr_def Fun_goFun_f.natural_transformation_axioms by presburger
          finally show ?thesis by auto
        qed
        ultimately show ?thesis by auto
      qed

      lemma comp_simp [simp]:
      assumes "seq t s"
      shows "comp t s = mkArr (Dom s) (Cod t) (vertical_composite.map A B (Fun s) (Fun t))"
        using assms comp_char by auto

      lemma ide_char [iff]:
      shows "ide t \<longleftrightarrow> t \<noteq> null \<and> functor A B (Fun t) \<and> Dom t = Fun t \<and> Cod t = Fun t"
      proof
        assume "ide t"
        thus "t \<noteq> null \<and> functor A B (Fun t) \<and> Dom t = Fun t \<and> Cod t = Fun t"
          by (metis Cod_mkArr Fun_mkArr arr_char dom_simp ideD(1) ideD(2)
                    natural_transformation_def)
        next
        assume "t \<noteq> null \<and> functor A B (Fun t) \<and> Dom t = Fun t \<and> Cod t = Fun t"
        thus "ide t"
          using CC.ide_char functor_is_transformation Arr'_def
                Cod_def Dom_def Fun_def comp_def null_char arr_char dom_char cod_char comp_simp
          by (metis mkArr_Fun ideI_cod)
      qed

    end

  end

  sublocale functor_category \<subseteq> category comp
    using is_category by auto

  section "Additional Properties"

  text{*
    In this section some additional facts are proved, which make it easier to
    work with the @{term "functor_category"} locale.
  *}

  context functor_category
  begin

    lemma ide_mkIde [simp]:
    assumes "functor A B F"
    shows "ide (mkIde F)"
    proof -
      have 1: "arr (mkIde F)"
        using assms arr_char functor_is_transformation by blast
      have "Dom (mkIde F) = F \<and> Cod (mkIde F) = F \<and> Fun (mkIde F) = F"
        using 1 Dom_mkArr Cod_mkArr Fun_mkArr by blast
      moreover have "mkIde F \<noteq> null"
       by (metis 1 not_arr_null)
      ultimately show ?thesis
        using assms ide_char [of "mkIde F"] by presburger
    qed

    lemma Dom_ide:
    assumes "ide a"
    shows "Dom a = Fun a"
      using assms Dom_def Fun_def ide_char by blast

    lemma Cod_ide:
    assumes "ide a"
    shows "Cod a = Fun a"
      using assms Cod_def Fun_def ide_char by blast

    lemma Dom_dom [simp]:
    assumes "arr f"
    shows "Dom (dom f) = Dom f"
      using assms dom_simp Dom_mkArr arr_dom_iff_arr by metis

    lemma Cod_dom [simp]:
    assumes "arr f"
    shows "Cod (dom f) = Dom f"
      using assms dom_simp Cod_mkArr arr_dom_iff_arr by metis

    lemma Dom_cod [simp]:
    assumes "arr f"
    shows "Dom (cod f) = Cod f"
      using assms cod_simp Dom_mkArr arr_cod_iff_arr by metis

    lemma Cod_cod [simp]:
    assumes "arr f"
    shows "Cod (cod f) = Cod f"
      using assms cod_simp Cod_mkArr arr_cod_iff_arr by metis

    lemma Fun_dom [simp]:
    assumes "arr t"
    shows "Fun (dom t) = Dom t"
    proof -
      (* TODO: Look into why this is not automatic. *)
      have "arr (dom t)" using assms arr_dom_iff_arr by blast
      hence "arr (dom t) \<and> dom t = mkIde (Dom t)" using assms dom_simp by simp
      thus ?thesis using assms dom_simp by simp
    qed

    lemma Fun_cod [simp]:
    assumes "arr t"
    shows "Fun (cod t) = Cod t"
    proof -
      have "arr (cod t)" using assms arr_cod_iff_arr by blast
      hence "arr (cod t) \<and> cod t = mkIde (Cod t)" using assms cod_simp by simp
      thus ?thesis using assms cod_simp by simp
    qed

    lemma Fun_comp [simp]:
    assumes "seq t' t" and "A.seq a' a"
    shows "Fun (comp t' t) (A a' a) = B (Fun t' a') (Fun t a)"
    proof -
      interpret t: natural_transformation A B "Dom t" "Cod t" "Fun t"
        using assms(1) arr_char by simp
      interpret t': natural_transformation A B "Cod t" "Cod t'" "Fun t'"
      proof -
        have "Cod t = Dom t'" using assms(1) Fun_dom [of t'] Fun_cod [of t] by simp
        thus "natural_transformation A B (Cod t) (Cod t') (Fun t')"
          using assms(1) arr_char by simp
      qed
      interpret t'ot: vertical_composite A B "Dom t" "Cod t" "Cod t'" "Fun t" "Fun t'" ..
      have "Fun (comp t' t) (A a' a) = t'ot.map (A a' a)"
        using assms comp_char Fun_mkArr arr_comp comp_simp by auto
      also have "... = B (t'ot.map a') (Dom t a)"
        using assms(2) t'ot.preserves_comp_2 by simp
      also have "... = B (B (Fun t' a') (Fun t (A.dom a'))) (Dom t a)"
        using assms(2) t'ot.map_simp_2 [of a'] by simp
      also have "... = B (Fun t' a') (B (Fun t (A.cod a)) (Dom t a))"
        using assms by simp
      also have "... = B (Fun t' a') (Fun t a)"
        using assms t.is_natural_2 by fastforce
      finally show ?thesis by auto
    qed

    lemma arr_eqI:
    assumes "arr t" and "arr t'" and "Dom t = Dom t'" and "Cod t = Cod t'" and "Fun t = Fun t'"
    shows "t = t'"
      using assms mkArr_Fun by metis

    lemma mkArr_eqI [intro]:
    assumes "arr (mkArr F G \<tau>)"
    and "F = F'" and "G = G'" and "\<tau> = \<tau>'"
    shows "mkArr F G \<tau> = mkArr F' G' \<tau>'"
      using assms arr_eqI by simp

    lemma mkArr_eqI' [intro]:
    assumes "arr (mkArr F G \<tau>)" and "\<tau> = \<tau>'"
    shows "mkArr F G \<tau> = mkArr F G \<tau>'"
      using assms arr_eqI by simp

    lemma comp_mkArr [simp]:
    assumes "arr (mkArr F G \<sigma>)" and "arr (mkArr G H \<tau>)"
    shows "comp (mkArr G H \<tau>) (mkArr F G \<sigma>) = mkArr F H (vertical_composite.map A B \<sigma> \<tau>)"
      using assms comp_char mkArr_Fun dom_simp cod_simp by simp

    lemma mkArr_in_hom:
    assumes "natural_transformation A B F G \<tau>"
    shows "mkArr F G \<tau> \<in> hom (mkIde F) (mkIde G)"
      using assms dom_simp cod_simp by simp

    lemma iso_char [iff]:
    shows "iso t \<longleftrightarrow> t \<noteq> null \<and> natural_isomorphism A B (Dom t) (Cod t) (Fun t)"
    proof
      assume t: "iso t"
      show "t \<noteq> null \<and> natural_isomorphism A B (Dom t) (Cod t) (Fun t)"
      proof
        show "t \<noteq> null" using t arr_char by auto
        from t obtain t' where t': "inverse_arrows t t'" by blast
        interpret \<tau>: natural_transformation A B "Dom t" "Cod t" "Fun t"
          using t arr_char iso_is_arr by auto
        interpret \<tau>': natural_transformation A B "Cod t" "Dom t" "Fun t'"
          using t' arr_char inverse_arrows_def seq_char by metis
        interpret \<tau>'o\<tau>: vertical_composite A B "Dom t" "Cod t" "Dom t" "Fun t" "Fun t'" ..
        interpret \<tau>o\<tau>': vertical_composite A B "Cod t" "Dom t" "Cod t" "Fun t'" "Fun t" ..
        show "natural_isomorphism A B (Dom t) (Cod t) (Fun t)"
        proof
          fix a
          assume a: "A.ide a"
          show "B.iso (Fun t a)"
          proof
            have "\<tau>'o\<tau>.map = Dom t \<and> \<tau>o\<tau>'.map = Cod t"
              using t t'
              by (metis (no_types, lifting) Fun_mkArr \<tau>.F.natural_transformation_axioms
                  \<tau>.G.natural_transformation_axioms cod_char dom_char functor_category.arr_mkArr
                  functor_category.comp_simp functor_category_axioms ide_comp_simp
                  inverse_arrowsD(1) inverse_arrowsD(2) inverse_arrowsD(3))
            thus "B.inverse_arrows (Fun t a) (Fun t' a)"
              using a \<tau>'o\<tau>.map_simp_1 \<tau>o\<tau>'.map_simp_1 B.inverse_arrows_def by auto
          qed
        qed
      qed
      next
      assume t: "t \<noteq> null \<and> natural_isomorphism A B (Dom t) (Cod t) (Fun t)"
      show "iso t"
      proof
        interpret \<tau>: natural_isomorphism A B "Dom t" "Cod t" "Fun t"
          using t by auto
        interpret \<tau>': inverse_transformation A B "Dom t" "Cod t" "Fun t" ..
        have 1: "vertical_composite.map A B (Fun t) \<tau>'.map = Dom t
                  \<and> vertical_composite.map A B \<tau>'.map (Fun t) = Cod t"
          using \<tau>.natural_isomorphism_axioms vertical_composite_inverse_iso
                vertical_composite_iso_inverse
          by blast
        show "inverse_arrows t (mkArr (Cod t) (Dom t) (\<tau>'.map))"
        proof -
          have "natural_transformation A B (Dom t) (Cod t) (Fun t)" ..
          hence "arr t \<and> arr (mkArr (Cod t) (Dom t) \<tau>'.map)"
            using t arr_char \<tau>'.natural_transformation_axioms by blast
          hence 2: "antipar t (mkArr (Cod t) (Dom t) \<tau>'.map)"
            using t by (simp add: cod_char dom_char)
          moreover have "ide (comp (mkArr (Cod t) (Dom t) \<tau>'.map) t)"
            using 1 2
            by (metis (no_types, lifting) Fun_mkArr arr_comp cod_comp comp_simp dom_simp
                functor_category.seq_char functor_category_axioms ideI_cod)
          moreover have "ide (comp t (mkArr (Cod t) (Dom t) \<tau>'.map))"
            using 1 2
            by (metis (no_types, lifting) Fun_mkArr arr_comp cod_simp comp_simp dom_comp
                functor_category.seq_char functor_category_axioms ideI_dom)
          ultimately show ?thesis
            using inverse_arrows_def [of t "mkArr (Cod t) (Dom t) (\<tau>'.map)"] by simp
        qed
      qed
    qed

  end

  section "Evaluation Functor"

  text{*
    This section defines the evaluation map that applies an arrow of the functor
    category @{text "[A, B]"} to an arrow of @{term A} to obtain an arrow of @{term B}
    and shows that it is functorial.
  *}

  locale evaluation_functor =
    A: category A +
    B: category B +
    A_B: functor_category A B +
    A_BxA: product_category A_B.comp A
  for A :: "'a comp"
  and B :: "'b comp"
  begin

    definition map
    where "map Fg \<equiv> if A_BxA.arr Fg then A_B.Fun (fst Fg) (snd Fg) else B.null"

    lemma map_simp:
    assumes "A_BxA.arr Fg"
    shows "map Fg = A_B.Fun (fst Fg) (snd Fg)"
      using assms map_def by auto

    lemma is_functor:
    shows "functor A_BxA.comp B map"
      apply unfold_locales
        using map_def apply auto[1]
    proof -
      fix Fg
      assume Fg: "A_BxA.arr Fg"
      let ?F = "fst Fg"
      have F: "A_B.arr ?F" using Fg by auto
      let ?g = "snd Fg"
      have g: "A.arr ?g" using Fg by auto
      have DomF: "A_B.Dom ?F = A_B.Fun (A_B.dom ?F)" using F A_B.Fun_dom by simp
      have CodF: "A_B.Cod ?F = A_B.Fun (A_B.cod ?F)" using F A_B.Fun_cod by simp
      interpret F: natural_transformation A B "A_B.Dom ?F" "A_B.Cod ?F" "A_B.Fun ?F"
        using Fg A_B.arr_char [of ?F] by blast
      show "B.arr (map Fg)" using Fg map_def by simp
      show "B.dom (map Fg) = map (A_BxA.dom Fg)"
        using Fg map_def DomF
        by (metis A_BxA.arr_dom_iff_arr A_BxA.dom_simp F.preserves_dom fst_conv g snd_conv)
      show "B.cod (map Fg) = map (A_BxA.cod Fg)"
        using Fg map_def CodF
       by (metis A_BxA.arr_cod_iff_arr A_BxA.cod_simp F.preserves_cod fst_conv g snd_conv)
      fix Fg'
      assume Fg': "Fg' \<in> A_BxA.hom (A_BxA.cod Fg) (A_BxA.cod Fg')"
      let ?F' = "fst Fg'"
      have F': "A_B.arr ?F'" using Fg' by auto
      let ?g' = "snd Fg'"
      have g': "A.arr ?g'" using Fg' by auto
      have DomF': "A_B.Dom ?F' = A_B.Fun (A_B.dom ?F')" using F' A_B.Fun_dom by simp
      have CodF': "A_B.Cod ?F' = A_B.Fun (A_B.cod ?F')" using F' A_B.Fun_cod by simp
      have seq_F'F: "A_B.seq ?F' ?F" using Fg Fg' by auto
      have seq_g'g: "A.seq ?g' ?g" using Fg Fg' by auto
      interpret F': natural_transformation A B "A_B.Cod ?F" "A_B.Cod ?F'" "A_B.Fun ?F'"
      proof -
        have "A_B.Cod ?F = A_B.Dom ?F'" using seq_F'F CodF DomF' by presburger
        thus "natural_transformation A B (A_B.Cod ?F) (A_B.Cod ?F') (A_B.Fun ?F')"
          using Fg' A_B.arr_char [of ?F'] by auto
      qed
      interpret F'oF: vertical_composite A B "A_B.Dom ?F" "A_B.Cod ?F" "A_B.Cod ?F'"
                                             "A_B.Fun ?F" "A_B.Fun ?F'" ..

      show "map (A_BxA.comp Fg' Fg) = B (map Fg') (map Fg)"
      proof -
        have 1: "A_BxA.seq Fg' Fg" using Fg Fg' by simp
        hence 2: "A_B.seq ?F' ?F" by auto
        have "map (A_BxA.comp Fg' Fg) = A_B.Fun (A_B.comp ?F' ?F) (A ?g' ?g)"
        proof -
          have "A_BxA.arr (A_BxA.comp Fg' Fg)" using 1 A_BxA.arr_comp by auto
          thus ?thesis using Fg Fg' map_def by simp
        qed
        also have "... = F'oF.map (A ?g' ?g)"
          using 2 A_B.comp_char A_B.Fun_mkArr A_B.arr_comp by auto
        also have "... = B (A_B.Fun ?F' (A.cod (A ?g' ?g))) (A_B.Fun ?F (A ?g' ?g))"
          using Fg Fg' F'oF.map_simp_1 by auto
        also have "... = B (A_B.Fun ?F' (A.cod ?g')) (A_B.Fun ?F (A ?g' ?g))"
          using seq_g'g by auto
        also have "... = B (A_B.Fun ?F' (A.cod ?g')) (B (A_B.Cod ?F ?g') (A_B.Fun ?F ?g))"
          using seq_g'g F.preserves_comp_1 [of ?g ?g'] CodF' by simp
        also have "... = B (B (A_B.Fun ?F' (A.cod ?g')) (A_B.Cod ?F ?g')) (A_B.Fun ?F ?g)"
          using Fg Fg' seq_g'g
          by (metis (no_types, lifting) B.comp_assoc F'oF.map_seq F.G.preserves_cod
              F.G.preserves_seq F.preserves_cod)
        also have "... = B (map Fg') (map Fg)" using Fg Fg' map_def by auto
        finally show ?thesis by auto
      qed
    qed

  end

  sublocale evaluation_functor \<subseteq> "functor" A_BxA.comp B map
    using is_functor by auto
  sublocale evaluation_functor \<subseteq> binary_functor A_B.comp A B map ..

  section "Currying"

  text{*
    This section defines the notion of currying of a natural transformation
    between binary functors, to obtain a natural transformation between
    functors into a functor category, along with the inverse operation of uncurrying.
    We have only proved here what is needed to establish the results
    in theory @{text Limit} about limits in functor categories and have not
    attempted to fully develop the functoriality and naturality properties of
    these notions.
  *}

  locale currying =
  A1: category A1 +
  A2: category A2 +
  B: category B
  for A1 :: "'a1 comp"
  and A2 :: "'a2 comp"
  and B :: "'b comp"
  begin

    interpretation A1xA2: product_category A1 A2 ..
    interpretation A2_B: functor_category A2 B ..
    interpretation A2_BxA2: product_category A2_B.comp A2 ..
    interpretation E: evaluation_functor A2 B ..

    text{*
      A proper definition for @{term curry} requires that it be parametrized by
      binary functors @{term F} and @{term G} that are the domain and codomain
      of the natural transformations to which it is being applied.
      Similar parameters are not needed in the case of @{term uncurry}.
    *}

    definition curry :: "('a1 \<times> 'a2 \<Rightarrow> 'b) \<Rightarrow> ('a1 \<times> 'a2 \<Rightarrow> 'b) \<Rightarrow> ('a1 \<times> 'a2 \<Rightarrow> 'b)
                           \<Rightarrow> 'a1 \<Rightarrow> ('a2, 'b) A2_B.arr"
    where "curry F G \<tau> f1 = (if A1.arr f1 then
                               A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                          (\<lambda>f2. \<tau> (f1, f2))
                             else A2_B.null)"

    definition uncurry :: "('a1 \<Rightarrow> ('a2, 'b) A2_B.arr) \<Rightarrow> 'a1 \<times> 'a2 \<Rightarrow> 'b"
    where "uncurry \<tau> f \<equiv> if A1xA2.arr f then E.map (\<tau> (fst f), snd f) else B.null"

    lemma curry_simp [simp]:
    assumes "A1.arr f1"
    shows "curry F G \<tau> f1 = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                       (\<lambda>f2. \<tau> (f1, f2))"
      using assms curry_def by auto

    lemma uncurry_simp [simp]:
    assumes "A1xA2.arr f"
    shows "uncurry \<tau> f = E.map (\<tau> (fst f), snd f)"
      using assms uncurry_def by auto

    lemma curry_in_hom:
    assumes f1: "A1.arr f1"
    and "natural_transformation A1xA2.comp B F G \<tau>"
    shows "curry F G \<tau> f1 \<in> A2_B.hom (curry F F F (A1.dom f1)) (curry G G G (A1.cod f1))"
    proof -
      interpret \<tau>: natural_transformation A1xA2.comp B F G \<tau> using assms by auto
      show ?thesis
      proof -
        interpret F_dom_f1: "functor" A2 B "\<lambda>f2. F (A1.dom f1, f2)"
          apply unfold_locales
          using f1 apply simp_all
        proof -
          fix f2 g2
          assume f2: "A2.arr f2" and g2: "A2.arr g2 \<and> A2.dom g2 = A2.cod f2"
          show "F (A1.dom f1, A2 g2 f2) = B (F (A1.dom f1, g2)) (F (A1.dom f1, f2))"
          proof -
            have "F (A1.dom f1, A2 g2 f2) = F (A1xA2.comp (A1.dom f1, g2) (A1.dom f1, f2))"
              using f1 f2 g2 by simp
            also have "... = B (F (A1.dom f1, g2)) (F (A1.dom f1, f2))"
              using f1 f2 g2 by fastforce
            finally show ?thesis by auto
          qed
        qed
        interpret G_cod_f1: "functor" A2 B "\<lambda>f2. G (A1.cod f1, f2)"
          apply unfold_locales
          using f1 apply simp_all
        proof -
          fix f2 g2
          assume f2: "A2.arr f2" and g2: "A2.arr g2 \<and> A2.dom g2 = A2.cod f2"
          show "G (A1.cod f1, A2 g2 f2) = B (G (A1.cod f1, g2)) (G (A1.cod f1, f2))"
          proof -
            have "G (A1.cod f1, A2 g2 f2) = G (A1xA2.comp (A1.cod f1, g2) (A1.cod f1, f2))"
              using f1 f2 g2 by simp
            also have "... = B (G (A1.cod f1, g2)) (G (A1.cod f1, f2))"
              using f1 f2 g2 by fastforce
            finally show ?thesis by auto
          qed
        qed
        have "natural_transformation A2 B (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                          (\<lambda>f2. \<tau> (f1, f2))"
          apply unfold_locales
          apply simp
        proof -
          fix f2
          assume f2: "A2.arr f2"
          show "B.dom (\<tau> (f1, f2)) = F (A1.dom f1, A2.dom f2)" using f1 f2 by simp
          show "B.cod (\<tau> (f1, f2)) = G (A1.cod f1, A2.cod f2)" using f1 f2 by simp
          show "B (G (A1.cod f1, f2)) (\<tau> (f1, A2.dom f2)) = \<tau> (f1, f2)"
            using f1 f2 \<tau>.preserves_comp_1 [of "(f1, A2.dom f2)" "(A1.cod f1, f2)"] by simp
          show "B (\<tau> (f1, A2.cod f2)) (F (A1.dom f1, f2)) = \<tau> (f1, f2)"
            using f1 f2 \<tau>.preserves_comp_2 [of "(A1.dom f1, f2)" "(f1, A2.cod f2)"] by simp
        qed
        thus "curry F G \<tau> f1 \<in> A2_B.hom (curry F F F (A1.dom f1)) (curry G G G (A1.cod f1))"
          using f1 curry_def [of F G \<tau> f1] A2_B.arr_mkArr A2_B.dom_simp A2_B.cod_simp by simp
      qed
    qed

    lemma curry_preserves_functors:
    assumes "functor A1xA2.comp B F"
    shows "functor A1 A2_B.comp (curry F F F)"
    proof -
      interpret F: "functor" A1xA2.comp B F using assms by auto
      interpret F: binary_functor A1 A2 B F ..
      show ?thesis
        apply unfold_locales
        using curry_def apply simp
      proof -
        fix f1
        assume f1: "A1.arr f1"
        show arr: "A2_B.arr (curry F F F f1)"
          using f1 curry_def F.fixing_arr_gives_natural_transformation_1 by simp
        show "A2_B.dom (curry F F F f1) = curry F F F (A1.dom f1)"
          using f1 curry_def F.fixing_arr_gives_natural_transformation_1 A2_B.dom_simp by simp
        show "A2_B.cod (curry F F F f1) = curry F F F (A1.cod f1)"
          using f1 curry_def F.fixing_arr_gives_natural_transformation_1 A2_B.cod_simp by simp
        fix g1
        assume g1: "g1 \<in> A1.hom (A1.cod f1) (A1.cod g1)"
        have "A2_B.arr (curry F F F g1)"
          using f1 g1 curry_def F.fixing_arr_gives_natural_transformation_1 by force
        thus "curry F F F (A1 g1 f1) = A2_B.comp (curry F F F g1) (curry F F F f1)"
          using f1 g1 arr curry_def F.preserves_comp_1
                A2_B.comp_char A2_B.dom_simp A2_B.cod_simp
          by simp
      qed
    qed

    lemma curry_preserves_transformations:
    assumes "natural_transformation A1xA2.comp B F G \<tau>"
    shows "natural_transformation A1 A2_B.comp (curry F F F) (curry G G G) (curry F G \<tau>)"
    proof -
      interpret \<tau>: natural_transformation A1xA2.comp B F G \<tau> using assms by auto
      interpret \<tau>: binary_functor_transformation A1 A2 B F G \<tau> ..
      interpret curry_F: "functor" A1 A2_B.comp "curry F F F"
        using curry_preserves_functors \<tau>.F.functor_axioms by simp
      interpret curry_G: "functor" A1 A2_B.comp "curry G G G"
        using curry_preserves_functors \<tau>.G.functor_axioms by simp
      show ?thesis
        apply unfold_locales
        using curry_def apply simp
      proof -
        fix f1
        assume f1: "A1.arr f1"
        show "A2_B.dom (curry F G \<tau> f1) = curry F F F (A1.dom f1)"
          using assms f1 curry_in_hom by simp
        show "A2_B.cod (curry F G \<tau> f1) = curry G G G (A1.cod f1)"
          using assms f1 curry_in_hom by simp
        show "A2_B.comp (curry G G G f1) (curry F G \<tau> (A1.dom f1)) = curry F G \<tau> f1"
        proof -
          interpret \<tau>_dom_f1: natural_transformation A2 B "\<lambda>f2. F (A1.dom f1, f2)"
                                "\<lambda>f2. G (A1.dom f1, f2)" "\<lambda>f2. \<tau> (A1.dom f1, f2)"
            using assms f1 curry_in_hom A2_B.arr_mkArr A1.ide_dom
                  \<tau>.fixing_ide_gives_natural_transformation_1
            by blast
          interpret G_f1: natural_transformation A2 B
                                "\<lambda>f2. G (A1.dom f1, f2)" "\<lambda>f2. G (A1.cod f1, f2)" "\<lambda>f2. G (f1, f2)"
            using f1 \<tau>.G.fixing_arr_gives_natural_transformation_1 by simp
          interpret G_f1o\<tau>_dom_f1: vertical_composite A2 B
                                     "\<lambda>f2. F (A1.dom f1, f2)" "\<lambda>f2. G (A1.dom f1, f2)"
                                     "\<lambda>f2. G (A1.cod f1, f2)"
                                     "\<lambda>f2. \<tau> (A1.dom f1, f2)" "\<lambda>f2. G (f1, f2)" ..
          have "A2_B.comp (curry G G G f1) (curry F G \<tau> (A1.dom f1))
                  = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2)) G_f1o\<tau>_dom_f1.map"
            using assms f1 curry_G.preserves_hom curry_in_hom [of "A1.dom f1"] curry_def
                  A2_B.comp_mkArr
            by force
          also have "... = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                      (\<lambda>f2. \<tau> (f1, f2))"
          proof (intro A2_B.mkArr_eqI)
            show "(\<lambda>f2. F (A1.dom f1, f2)) = (\<lambda>f2. F (A1.dom f1, f2))" by simp
            show "(\<lambda>f2. G (A1.cod f1, f2)) = (\<lambda>f2. G (A1.cod f1, f2))" by simp
            show "A2_B.arr (A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                       G_f1o\<tau>_dom_f1.map)"
              using A2_B.arr_mkArr G_f1o\<tau>_dom_f1.natural_transformation_axioms by blast
            show "G_f1o\<tau>_dom_f1.map = (\<lambda>f2. \<tau> (f1, f2))"
            proof
              fix f2
              have "\<not>A2.arr f2 \<Longrightarrow> G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
                using f1 by simp
              moreover have "A2.arr f2 \<Longrightarrow> G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
              proof -
                interpret \<tau>_f1: natural_transformation A2 B "\<lambda>f2. F (A1.dom f1, f2)"
                                  "\<lambda>f2. G (A1.cod f1, f2)" "\<lambda>f2. \<tau> (f1, f2)"
                  using assms f1 curry_in_hom A2_B.arr_mkArr by simp
                fix f2
                assume f2: "A2.arr f2"
                have "G_f1o\<tau>_dom_f1.map f2 = B (G (f1, f2)) (\<tau> (A1.dom f1, A2.dom f2))"
                  using f1 G_f1o\<tau>_dom_f1.map_simp_2 [of f2] by fastforce
                also have "... = B (B (G (A1.cod f1, f2)) (G (f1, A2.dom f2)))
                                   (\<tau> (A1.dom f1, A2.dom f2))"
                  using f1 f2 by simp
                also have "... = B (G (A1.cod f1, f2))
                                   (B (G (f1, A2.dom f2)) (\<tau> (A1.dom f1, A2.dom f2)))"
                  using f1 f2 by fastforce
                also have "... = \<tau> (f1, f2)"
                  using f1 f2 \<tau>.is_natural_1 [of "(f1, A2.dom f2)"] by simp
                finally show "G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2" by auto
              qed
              ultimately show "G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2" by blast
            qed
          qed
          also have "... = curry F G \<tau> f1" using f1 curry_def by simp
          finally show ?thesis by auto
        qed
        show "A2_B.comp (curry F G \<tau> (A1.cod f1)) (curry F F F f1) = curry F G \<tau> f1"
        proof -
          interpret \<tau>_cod_f1: natural_transformation A2 B "\<lambda>f2. F (A1.cod f1, f2)"
                                "\<lambda>f2. G (A1.cod f1, f2)" "\<lambda>f2. \<tau> (A1.cod f1, f2)"
            using assms f1 curry_in_hom A2_B.arr_mkArr A1.ide_cod
                  \<tau>.fixing_ide_gives_natural_transformation_1
            by blast
          interpret F_f1: natural_transformation A2 B
                                "\<lambda>f2. F (A1.dom f1, f2)" "\<lambda>f2. F (A1.cod f1, f2)" "\<lambda>f2. F (f1, f2)"
            using f1 \<tau>.F.fixing_arr_gives_natural_transformation_1 by simp
          interpret \<tau>_cod_f1oF_f1: vertical_composite A2 B
                                     "\<lambda>f2. F (A1.dom f1, f2)" "\<lambda>f2. F (A1.cod f1, f2)"
                                     "\<lambda>f2. G (A1.cod f1, f2)"
                                      "\<lambda>f2. F (f1, f2)" "\<lambda>f2. \<tau> (A1.cod f1, f2)" ..
          have "A2_B.comp (curry F G \<tau> (A1.cod f1)) (curry F F F f1) 
                  = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2)) \<tau>_cod_f1oF_f1.map"
          proof -
            have "curry F F F f1 = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. F (A1.cod f1, f2))
                                              (\<lambda>f2. F (f1, f2)) \<and>
                  curry F F F f1 \<in> A2_B.hom (curry F F F (A1.dom f1)) (curry F F F (A1.cod f1))"
              using f1 curry_F.preserves_hom by simp
            moreover have
                 "curry F G \<tau> (A1.dom f1) =
                    A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.dom f1, f2))
                               (\<lambda>f2. \<tau> (A1.dom f1, f2)) \<and>
                    curry F G \<tau> (A1.cod f1)
                              \<in> A2_B.hom (curry F F F (A1.cod f1)) (curry G G G (A1.cod f1))"
              using assms f1 curry_in_hom [of "A1.cod f1"] curry_def by simp
            ultimately show ?thesis
              using f1 curry_def A2_B.comp_mkArr by simp
          qed
          also have "... = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                      (\<lambda>f2. \<tau> (f1, f2))"
          proof (intro A2_B.mkArr_eqI)
            show "(\<lambda>f2. F (A1.dom f1, f2)) = (\<lambda>f2. F (A1.dom f1, f2))" by simp
            show "(\<lambda>f2. G (A1.cod f1, f2)) = (\<lambda>f2. G (A1.cod f1, f2))" by simp
            show "A2_B.arr (A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                       \<tau>_cod_f1oF_f1.map)"
              using A2_B.arr_mkArr \<tau>_cod_f1oF_f1.natural_transformation_axioms by blast
            show "\<tau>_cod_f1oF_f1.map = (\<lambda>f2. \<tau> (f1, f2))"
            proof
              fix f2
              have "\<not>A2.arr f2 \<Longrightarrow> \<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
                using f1 by simp
              moreover have "A2.arr f2 \<Longrightarrow> \<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
              proof -
                interpret \<tau>_f1: natural_transformation A2 B "\<lambda>f2. F (A1.dom f1, f2)"
                                  "\<lambda>f2. G (A1.cod f1, f2)" "\<lambda>f2. \<tau> (f1, f2)"
                  using assms f1 curry_in_hom A2_B.arr_mkArr by simp
                fix f2
                assume f2: "A2.arr f2"
                have "\<tau>_cod_f1oF_f1.map f2 = B (\<tau> (A1.cod f1, A2.cod f2)) (F (f1, f2))"
                  using f1 \<tau>_cod_f1oF_f1.map_simp_1 [of f2] by fastforce
                also have "... = B (B (\<tau> (A1.cod f1, A2.cod f2)) (F (f1, A2.cod f2)))
                                   (F (A1.dom f1, f2))"
                  using f1 f2 by fastforce
                also have "... = \<tau> (f1, f2)"
                  using f1 f2 \<tau>.is_natural_2 [of "(f1, A2.cod f2)"] by simp
                finally show "\<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2" by auto
              qed
              ultimately show "\<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2" by blast
            qed
          qed
          also have "... = curry F G \<tau> f1" using f1 curry_def by simp
          finally show ?thesis by auto
        qed
      qed
    qed

    lemma uncurry_preserves_functors:
    assumes "functor A1 A2_B.comp F"
    shows "functor A1xA2.comp B (uncurry F)"
    proof -
      interpret F: "functor" A1 A2_B.comp F using assms by auto
      show ?thesis
        apply unfold_locales
        using uncurry_def apply auto[1]
        using uncurry_def apply simp
      proof -
        fix f
        assume f: "A1xA2.arr f"
        let ?f1 = "fst f"
        let ?f2 = "snd f"
        have f1: "A1.arr ?f1" using f by simp
        have f2: "A2.arr ?f2" using f by simp
        show "B.dom (uncurry F f) = uncurry F (A1xA2.dom f)"
          using f uncurry_def F.preserves_dom by simp
        show "B.cod (uncurry F f) = uncurry F (A1xA2.cod f)"
          using f uncurry_def F.preserves_cod by simp
        fix g
        assume g: "g \<in> A1xA2.hom (A1xA2.cod f) (A1xA2.cod g)"
        let ?g1 = "fst g"
        let ?g2 = "snd g"
        have g1: "?g1 \<in> A1.hom (A1.cod ?f1) (A1.cod ?g1)" using f g by auto
        have g2: "?g2 \<in> A2.hom (A2.cod ?f2) (A2.cod ?g2)" using f g by auto
        have Ff1: "natural_transformation A2 B (A2_B.Dom (F ?f1)) (A2_B.Cod (F ?f1))
                                               (A2_B.Fun (F ?f1))"
          using f A2_B.arr_char [of "F ?f1"] by simp
        interpret Ff1: natural_transformation A2 B "A2_B.Dom (F ?f1)" "A2_B.Cod (F ?f1)"
                                                   "A2_B.Fun (F ?f1)"
          using Ff1 by auto
        have Fg1: "natural_transformation A2 B (A2_B.Cod (F ?f1)) (A2_B.Cod (F ?g1))
                                                (A2_B.Fun (F ?g1))"
          using f1 g1 A2_B.Fun_dom [of "F ?g1"] A2_B.Fun_cod [of "F ?f1"]
                F.preserves_dom F.preserves_cod g A2_B.arr_char [of "F ?g1"]
          by simp
        interpret Fg1: natural_transformation A2 B "A2_B.Cod (F ?f1)" "A2_B.Cod (F ?g1)"
                                                    "A2_B.Fun (F ?g1)"
          using Fg1 by auto
        interpret Fg1oFf1: vertical_composite A2 B
                              "A2_B.Dom (F ?f1)" "A2_B.Cod (F ?f1)" "A2_B.Cod (F ?g1)"
                              "A2_B.Fun (F ?f1)" "A2_B.Fun (F ?g1)" ..
        show "uncurry F (A1xA2.comp g f) = B (uncurry F g) (uncurry F f)"
        proof -
          have "uncurry F (A1xA2.comp g f) = E.map (F (A1 ?g1 ?f1), A2 ?g2 ?f2)"
            using f g uncurry_def by auto
          also have "... = A2_B.Fun (F (A1 ?g1 ?f1)) (A2 ?g2 ?f2)"
          proof -
            have "A2_BxA2.arr (F (A1 ?g1 ?f1), A2 ?g2 ?f2)"
            proof -
              have "A1.arr (A1 ?g1 ?f1)" using f1 g1 by simp
              hence "A2_B.arr (F (A1 ?g1 ?f1))" using F.preserves_arr by simp
              thus ?thesis using f2 g2 A2_BxA2.arr_char by simp
            qed
            thus ?thesis using E.map_simp by simp
          qed
          also have "... = B (A2_B.Fun (F ?g1) ?g2) (A2_B.Fun (F ?f1) ?f2)"
            using f1 g1 f2 g2 F.preserves_hom A2_B.Fun_comp by simp
          also have "... = B (uncurry F g) (uncurry F f)"
            using f g uncurry_def E.map_simp by simp
          finally show ?thesis by auto
        qed
      qed
    qed

    lemma uncurry_preserves_transformations:
    assumes "natural_transformation A1 A2_B.comp F G \<tau>"
    shows "natural_transformation A1xA2.comp B (uncurry F) (uncurry G) (uncurry \<tau>)"
    proof -
      interpret \<tau>: natural_transformation A1 A2_B.comp F G \<tau> using assms by auto
      interpret "functor" A1xA2.comp B "uncurry F"
        using \<tau>.F.functor_axioms uncurry_preserves_functors by blast
      interpret "functor" A1xA2.comp B "uncurry G"
        using \<tau>.G.functor_axioms uncurry_preserves_functors by blast
      show ?thesis
        apply unfold_locales
        using uncurry_def apply auto[1]
      proof -
        fix f
        assume f: "A1xA2.arr f"
        let ?f1 = "fst f"
        let ?f2 = "snd f"
        have f1: "A1.arr ?f1" using f by simp
        have f2: "A2.arr ?f2" using f by simp
        show "B.dom (uncurry \<tau> f) = uncurry F (A1xA2.dom f)"
          using f uncurry_def \<tau>.preserves_dom by simp
        show "B.cod (uncurry \<tau> f) = uncurry G (A1xA2.cod f)"
          using f uncurry_def \<tau>.preserves_cod by simp
        show "B (uncurry G f) (uncurry \<tau> (A1xA2.dom f)) = uncurry \<tau> f"
          using f \<tau>.preserves_hom \<tau>.G.preserves_dom uncurry_def
                E.preserves_comp [of "(\<tau> (A1.dom ?f1), A2.dom ?f2)" "(G ?f1, ?f2)"]
                \<tau>.is_natural_1 [of ?f1] A1xA2.comp_char
          by simp
        show "B (uncurry \<tau> (A1xA2.cod f)) (uncurry F f) = uncurry \<tau> f"
          using f \<tau>.preserves_hom \<tau>.F.preserves_cod uncurry_def
                E.preserves_comp [of "(F ?f1, ?f2)" "(\<tau> (A1.cod ?f1), A2.cod ?f2)"]
                \<tau>.is_natural_2 [of ?f1] A1xA2.comp_char
          by simp
      qed
    qed

    lemma uncurry_curry:
    assumes "natural_transformation A1xA2.comp B F G \<tau>"
    shows "uncurry (curry F G \<tau>) = \<tau>"
    proof
      interpret \<tau>: natural_transformation A1xA2.comp B F G \<tau> using assms by auto
      interpret curry_\<tau>: natural_transformation A1 A2_B.comp "curry F F F" "curry G G G"
                                                             "curry F G \<tau>"
        using assms curry_preserves_transformations by auto
      fix f
      have "\<not>A1xA2.arr f \<Longrightarrow> uncurry (curry F G \<tau>) f = \<tau> f"
        using curry_def uncurry_def \<tau>.is_extensional by auto
      moreover have "A1xA2.arr f \<Longrightarrow> uncurry (curry F G \<tau>) f = \<tau> f"
        using uncurry_def E.map_simp [of "(curry F G \<tau> (fst f), snd f)"]
              A1xA2.arr_char A2_BxA2.arr_char curry_def A1xA2.arr_char curry_\<tau>.preserves_arr
        by simp
      ultimately show "uncurry (curry F G \<tau>) f = \<tau> f" by blast
    qed

    lemma curry_uncurry:
    assumes "functor A1 A2_B.comp F" and "functor A1 A2_B.comp G"
    and "natural_transformation A1 A2_B.comp F G \<tau>"
    shows "curry (uncurry F) (uncurry G) (uncurry \<tau>) = \<tau>"
    proof
      interpret F: "functor" A1 A2_B.comp F using assms(1) by auto
      interpret G: "functor" A1 A2_B.comp G using assms(2) by auto
      interpret \<tau>: natural_transformation A1 A2_B.comp F G \<tau>
        using assms(3) by auto
      interpret uncurry_F: "functor" A1xA2.comp B "uncurry F"
        using F.functor_axioms uncurry_preserves_functors by auto
      interpret uncurry_G: "functor" A1xA2.comp B "uncurry G"
        using G.functor_axioms uncurry_preserves_functors by auto
      fix f1
      have "\<not>A1.arr f1 \<Longrightarrow> curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 = \<tau> f1"
        using curry_def uncurry_def by simp
      moreover have "A1.arr f1 \<Longrightarrow> curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 = \<tau> f1"
      proof -
        assume f1: "A1.arr f1"
        interpret uncurry_\<tau>: natural_transformation A1xA2.comp B "uncurry F" "uncurry G" "uncurry \<tau>"
          using \<tau>.natural_transformation_axioms uncurry_preserves_transformations [of F G \<tau>]
          by simp
        have "curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 =
                A2_B.mkArr (\<lambda>f2. uncurry F (A1.dom f1, f2)) (\<lambda>f2. uncurry G (A1.cod f1, f2))
                           (\<lambda>f2. uncurry \<tau> (f1, f2))"
          using f1 curry_def [of "uncurry F" "uncurry G" "uncurry \<tau>" f1] by simp
        also have "... = A2_B.mkArr (\<lambda>f2. uncurry F (A1.dom f1, f2))
                                    (\<lambda>f2. uncurry G (A1.cod f1, f2))
                                    (\<lambda>f2. E.map (\<tau> f1, f2))"
        proof -
          have "(\<lambda>f2. uncurry \<tau> (f1, f2)) = (\<lambda>f2. E.map (\<tau> f1, f2))"
            using f1 uncurry_def E.is_extensional by auto
          thus ?thesis by simp
        qed
        also have "... = \<tau> f1"
        proof -
          have "A2_B.Dom (\<tau> f1) = (\<lambda>f2. uncurry F (A1.dom f1, f2))"
          proof -
            have "A2_B.Dom (\<tau> f1) = A2_B.Fun (A2_B.dom (\<tau> f1))"
              using f1 A2_B.ide_char A2_B.Fun_dom \<tau>.preserves_arr A2_B.dom_simp by auto
            also have "... = A2_B.Fun (F (A1.dom f1))"
              using f1 \<tau>.preserves_dom by simp
            also have "... = (\<lambda>f2. uncurry F (A1.dom f1, f2))"
            proof
              fix f2
              interpret F_dom_f1: "functor" A2 B "A2_B.Fun (F (A1.dom f1))"
                using f1 A2_B.ide_char [of "F (A1.dom f1)"] F.preserves_ide by simp
              show "A2_B.Fun (F (A1.dom f1)) f2 = uncurry F (A1.dom f1, f2)"
                using f1 uncurry_def [of F] E.map_simp by force
            qed
            finally show ?thesis by auto
          qed
          moreover have "A2_B.Cod (\<tau> f1) = (\<lambda>f2. uncurry G (A1.cod f1, f2))"
          proof -
            have "A2_B.Cod (\<tau> f1) = A2_B.Fun (A2_B.cod (\<tau> f1))"
              using f1 A2_B.ide_char A2_B.Fun_cod \<tau>.preserves_arr A2_B.cod_simp by auto
            also have "... = A2_B.Fun (G (A1.cod f1))"
              using f1 \<tau>.preserves_cod by simp
            also have "... = (\<lambda>f2. uncurry G (A1.cod f1, f2))"
            proof
              fix f2
              interpret G_cod_f1: "functor" A2 B "A2_B.Fun (G (A1.cod f1))"
                using f1 A2_B.ide_char [of "G (A1.cod f1)"] G.preserves_ide by simp
              show "A2_B.Fun (G (A1.cod f1)) f2 = uncurry G (A1.cod f1, f2)"
                using f1 uncurry_def [of G] E.map_simp by force
            qed
            finally show ?thesis by auto
          qed
          moreover have "A2_B.Fun (\<tau> f1) = (\<lambda>f2. E.map (\<tau> f1, f2))"
          proof
            fix f2
            have "\<not>A2.arr f2 \<Longrightarrow> A2_B.Fun (\<tau> f1) f2 = (\<lambda>f2. E.map (\<tau> f1, f2)) f2"
              using f1 E.is_extensional A2_B.arr_char \<tau>.preserves_arr
                    natural_transformation.is_extensional
              by fastforce
            moreover have "A2.arr f2 \<Longrightarrow> A2_B.Fun (\<tau> f1) f2 = (\<lambda>f2. E.map (\<tau> f1, f2)) f2"
              using f1 E.map_simp [of "(\<tau> f1, f2)"] by simp
            ultimately show "A2_B.Fun (\<tau> f1) f2 = (\<lambda>f2. E.map (\<tau> f1, f2)) f2" by blast
          qed
          ultimately show ?thesis using A2_B.mkArr_Fun [of "\<tau> f1"] f1 \<tau>.preserves_arr [of f1]
            by metis
        qed
        finally show ?thesis by auto
      qed
      ultimately show "curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 = \<tau> f1" by blast
    qed

  end

  locale curried_functor =
     currying A1 A2 B +
     A1xA2: product_category A1 A2 +
     A2_B: functor_category A2 B +
     F: binary_functor A1 A2 B F
  for A1 :: "'a1 comp"
  and A2 :: "'a2 comp"
  and B :: "'b comp"
  and F :: "'a1 * 'a2 \<Rightarrow> 'b"
  begin

    definition map
    where "map \<equiv> curry F F F"

    lemma map_simp [simp]:
    assumes "A1.arr f1"
    shows "map f1 = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. F (A1.cod f1, f2)) (\<lambda>f2. F (f1, f2))"
      using assms map_def by auto

    lemma is_functor:
    shows "functor A1 A2_B.comp map"
      using F.functor_axioms map_def curry_preserves_functors by simp

  end

  sublocale curried_functor \<subseteq> "functor" A1 A2_B.comp map
    using is_functor by auto

  locale curried_functor' =
     A1: category A1 +
     A2: category A2 +
     currying A2 A1 B +
     F: binary_functor A1 A2 B F +
     A1_B: functor_category A1 B
  for A1 :: "'a1 comp"
  and A2 :: "'a2 comp"
  and B :: "'b comp"
  and F :: "'a1 * 'a2 \<Rightarrow> 'b"
  begin

    definition map
    where "map \<equiv> curry F.sym F.sym F.sym"

    lemma map_simp [simp]:
    assumes "A2.arr f2"
    shows "map f2 = A1_B.mkArr (\<lambda>f1. F (f1, A2.dom f2)) (\<lambda>f1. F (f1, A2.cod f2)) (\<lambda>f1. F (f1, f2))"
      using assms map_def by simp

    lemma is_functor:
    shows "functor A2 A1_B.comp map"
    proof -
      interpret A2xA1: product_category A2 A1 ..
      interpret F': binary_functor A2 A1 B F.sym
        using F.sym_is_binary_functor by simp
      have "functor A2xA1.comp B F.sym" ..
      thus ?thesis using map_def curry_preserves_functors by simp
    qed

  end

  sublocale curried_functor' \<subseteq> "functor" A2 A1_B.comp map
    using is_functor by auto

end

