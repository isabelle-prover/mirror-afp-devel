(*  Title:       Limit
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Limit

theory Limit
imports FreeCategory DiscreteCategory Adjunction
begin

  text{*
    This theory defines the notion of limit in terms of diagrams and cones and relates
    it to the concept of a representation of a functor.  The diagonal functor associated
    with a diagram shape @{term J} is defined and it is shown that a right adjoint to
    the diagonal functor gives limits of shape @{term J} and that a category has limits
    of shape @{term J} if and only if the diagonal functor is a left adjoint functor.
    Products and equalizers are defined as special cases of limits, and it is shown
    that a category with equalizers has limits of shape @{term J} if it has products
    indexed by the sets of objects and arrows of @{term J}.
    The existence of limits in a set category is investigated, and it is shown that
    every set category has equalizers and that a set category @{term S} has @{term I}-indexed
    products if and only if the universe of @{term S} ``admits @{term I}-indexed tupling.''
    The existence of limits in functor categories is also developed, showing that
    limits in functor categories are ``determined pointwise'' and that a functor category
    @{term "[A, B]"} has limits of shape @{term J} if @{term B} does.
    Finally, it is shown that the Yoneda functor preserves limits.

    This theory concerns itself only with limits; I have made no attempt to consider colimits.
    Although it would be possible to rework the entire development in dual form,
    it is possible that there is a more efficient way to dualize at least parts of it without
    repeating all the work.  This is something that deserves further thought.
  *}

  section "Representations of Functors"

  text{*
    A representation of a contravariant functor @{text "F: Cop \<rightarrow> S"}, where @{term S}
    is a set category that is the target of a hom-functor for @{term C}, consists of
    an object @{term a} of @{term C} and a natural isomorphism @{term "\<Phi>: Y a \<rightarrow> F"},
    where @{text "Y: C \<rightarrow> [Cop, S]"} is the Yoneda functor.
  *}

  locale representation_of_functor =
    C: category C +
    Cop: dual_category C +
    S: set_category S +
    F: "functor" Cop.comp S F +
    Hom: hom_functor C S \<phi> +
    Ya: yoneda_functor_fixed_object C S \<phi> a +
    natural_isomorphism Cop.comp S "Ya.Y a" F \<Phi>
    for C :: "'c comp"
    and S :: "'s comp"
    and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and F :: "'c \<Rightarrow> 's"
    and a :: 'c
    and \<Phi> :: "'c \<Rightarrow> 's"
  begin

     abbreviation Y where "Y \<equiv> Ya.Y"
     abbreviation \<psi> where "\<psi> \<equiv> Hom.\<psi>"

  end

  text{*
    Two representations of the same functor are uniquely isomorphic.
  *}

  locale two_representations_one_functor =
    C: category C +
    Cop: dual_category C +
    S: set_category S +
    F: set_valued_functor Cop.comp S F +
    yoneda_functor C S \<phi> +
    Ya: yoneda_functor_fixed_object C S \<phi> a +
    Ya': yoneda_functor_fixed_object C S \<phi> a' +
    \<Phi>: representation_of_functor C S \<phi> F a \<Phi> +
    \<Phi>': representation_of_functor C S \<phi> F a' \<Phi>'
    for C :: "'c comp"
    and S :: "'s comp"
    and F :: "'c \<Rightarrow> 's"
    and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and a :: 'c
    and \<Phi> :: "'c \<Rightarrow> 's"
    and a' :: 'c
    and \<Phi>' :: "'c \<Rightarrow> 's"
  begin

    interpretation \<Psi>: inverse_transformation Cop.comp S "Y a" F \<Phi> ..
    interpretation \<Psi>': inverse_transformation Cop.comp S "Y a'" F \<Phi>' ..
    interpretation \<Phi>\<Psi>': vertical_composite Cop.comp S "Y a" F "Y a'" \<Phi> \<Psi>'.map ..
    interpretation \<Phi>'\<Psi>: vertical_composite Cop.comp S "Y a'" F "Y a" \<Phi>' \<Psi>.map ..

    lemma are_uniquely_isomorphic:
      shows "\<exists>!\<phi>. \<phi> \<in> C.hom a a' \<and> C.iso \<phi> \<and> map \<phi> = Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
    proof -
      have "natural_isomorphism Cop.comp S (Y a) F \<Phi>" ..
      moreover have "natural_isomorphism Cop.comp S F (Y a') \<Psi>'.map" ..
      ultimately have 1: "natural_isomorphism Cop.comp S (Y a) (Y a') \<Phi>\<Psi>'.map"
        using NaturalTransformation.natural_isomorphisms_compose by blast
      interpret \<Phi>\<Psi>': natural_isomorphism Cop.comp S "Y a" "Y a'" \<Phi>\<Psi>'.map
        using 1 by auto

      have "natural_isomorphism Cop.comp S (Y a') F \<Phi>'" ..
      moreover have "natural_isomorphism Cop.comp S F (Y a) \<Psi>.map" ..
      ultimately have 2: "natural_isomorphism Cop.comp S (Y a') (Y a) \<Phi>'\<Psi>.map"
        using NaturalTransformation.natural_isomorphisms_compose by blast
      interpret \<Phi>'\<Psi>: natural_isomorphism Cop.comp S "Y a'" "Y a" \<Phi>'\<Psi>.map
        using 2 by auto

      interpret \<Phi>\<Psi>'_\<Phi>'\<Psi>: inverse_transformations Cop.comp S "Y a" "Y a'" \<Phi>\<Psi>'.map \<Phi>'\<Psi>.map
      proof
        fix x
        assume X: "Cop.ide x"
        show "S.inverse_arrows (\<Phi>\<Psi>'.map x) (\<Phi>'\<Psi>.map x)"
        proof
          have 1: "S.arr (\<Phi>\<Psi>'.map x) \<and> \<Phi>\<Psi>'.map x = S (\<Psi>'.map x) (\<Phi> x)"
            using X Cop.ideD \<Phi>\<Psi>'.preserves_arr [of x]
            by (simp add: \<Phi>\<Psi>'.map_simp_2)
          have 2: "S.arr (\<Phi>'\<Psi>.map x) \<and> \<Phi>'\<Psi>.map x = S (\<Psi>.map x) (\<Phi>' x)"
            using X Cop.ideD \<Phi>'\<Psi>.preserves_arr [of x]
            by (simp add: \<Phi>'\<Psi>.map_simp_1)
          show "S.ide (S (\<Phi>\<Psi>'.map x) (\<Phi>'\<Psi>.map x))"
            using 1 2 X \<Psi>.is_natural_2 \<Psi>'.inverts_components \<Psi>.inverts_components
            by (metis Cop.ideD(1) S.inverse_arrows_def \<Psi>'.is_natural_transformation
                      \<Psi>'.preserves_dom \<Psi>.preserves_dom category.inverse_arrows_compose
                      natural_transformation_def)
          show "S.ide (S (\<Phi>'\<Psi>.map x) (\<Phi>\<Psi>'.map x))"
            using 1 2 X \<Psi>'.inverts_components \<Psi>.inverts_components
            by (metis Cop.ideD(1) S.inverse_arrows_def \<Phi>'.preserves_cod \<Phi>.preserves_cod
                      \<Psi>'.is_natural_transformation category.inverse_arrows_compose
                      natural_transformation_def)
        qed
      qed

      have "Cop_S.inverse_arrows (Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map)
                                 (Cop_S.mkArr (Y a') (Y a) \<Phi>'\<Psi>.map)"
      proof -
        have Ya: "functor Cop.comp S (Y a)" ..
        have Ya': "functor Cop.comp S (Y a')" ..
        have \<Phi>\<Psi>': "natural_transformation Cop.comp S (Y a) (Y a') \<Phi>\<Psi>'.map" ..
        have \<Phi>'\<Psi>: "natural_transformation Cop.comp S (Y a') (Y a) \<Phi>'\<Psi>.map" ..
        show ?thesis
        proof (intro Cop_S.inverse_arrowsI)
          have 0: "inverse_transformations Cop.comp S (Y a) (Y a') \<Phi>\<Psi>'.map \<Phi>'\<Psi>.map" ..
          have 1: "Cop_S.antipar (Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map)
                                 (Cop_S.mkArr (Y a') (Y a) \<Phi>'\<Psi>.map)"
            using Ya Ya' \<Phi>\<Psi>' \<Phi>'\<Psi> Cop_S.dom_simp Cop_S.cod_simp by auto
          show "Cop_S.ide (Cop_S.comp (Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map)
                                      (Cop_S.mkArr (Y a') (Y a) \<Phi>'\<Psi>.map))"
            using 0 1 NaturalTransformation.inverse_transformations_inverse(2) Cop_S.comp_mkArr
            by (metis Cop_S.Dom_mkArr Cop_S.arr_comp Cop_S.cod_comp Cop_S.dom_simp Cop_S.ideI_cod)
          show "Cop_S.ide (Cop_S.comp (Cop_S.mkArr (Y a') (Y a) \<Phi>'\<Psi>.map)
                                      (Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map))"
            using 0 1 NaturalTransformation.inverse_transformations_inverse(1) Cop_S.comp_mkArr
            by (metis Cop_S.Dom_mkArr Cop_S.arr_comp Cop_S.cod_comp Cop_S.dom_simp Cop_S.ideI_cod)
        qed
      qed
      hence 3: "Cop_S.iso (Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map)" using Cop_S.isoI by blast
      hence "Cop_S.arr (Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map)" using Cop_S.iso_is_arr by blast
      hence "Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map \<in> Cop_S.hom (map a) (map a')"
        using Ya.ide_a Ya'.ide_a Cop_S.dom_simp Cop_S.cod_simp by simp
      hence "\<exists>f. f \<in> C.hom a a' \<and> map f = Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
        using Ya.ide_a Ya'.ide_a is_full Y_def Cop_S.iso_is_arr
              full_functor.is_full [of C Cop_S.comp map a' a "Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map"]
        by auto     
      from this obtain \<phi> where \<phi>: "\<phi> \<in> C.hom a a' \<and> map \<phi> = Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
        by blast
      from \<phi> have "C.iso \<phi>"
        using 3 reflects_iso [of \<phi> a a'] by simp
      hence EX: "\<exists>\<phi>. \<phi> \<in> C.hom a a' \<and> C.iso \<phi> \<and> map \<phi> = Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
        using \<phi> by blast
      have UN: "\<And>\<phi>'. \<phi>' \<in> C.hom a a' \<and> map \<phi>' = Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map \<Longrightarrow> \<phi>' = \<phi>"
      proof -
        fix \<phi>'
        assume \<phi>': "\<phi>' \<in> C.hom a a' \<and> map \<phi>' = Cop_S.mkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
        have "C.par \<phi> \<phi>' \<and> map \<phi> = map \<phi>'" using \<phi> \<phi>' by simp
        thus "\<phi>' = \<phi>" using is_faithful by fast
      qed
      from EX UN show ?thesis by auto
    qed

  end

  section "Diagrams and Cones"

  text{*
    A \emph{diagram} in a category @{term C} is a functor @{text "D: J \<rightarrow> C"}.
    We refer to the category @{term J} as the diagram \emph{shape}.
    Note that in the usual expositions of category theory that use set theory
    as their foundations, the shape @{term J} of a diagram is required to be
    a ``small'' category, where smallness means that the collection of objects
    of @{term J}, as well as each of the ``homs,'' is a set.
    However, in HOL there is no class of all sets, so it is not meaningful
    to speak of @{term J} as ``small'' in any kind of absolute sense.
    There is likely a meaningful notion of smallness of @{term J}
    \emph{relative to} @{term C} (the result below that states that a set
    category has @{term I}-indexed products if and only if its universe
    ``admits @{term I}-indexed tuples'' is suggestive of how this might
    be defined), but I haven't fully explored this idea at present.
  *}

  locale diagram =
    C: category C +
    J: category J +
    "functor" J C D
  for J :: "'j comp"
  and C :: "'c comp"
  and D :: "'j \<Rightarrow> 'c"
 
  lemma comp_diagram_functor:
  assumes "diagram J C D" and "functor J' J F"
  shows "diagram J' C (D o F)"
    by (meson assms(1) assms(2) diagram_def functor.axioms(1) functor_comp)
    
  text{*
    A \emph{cone} over a diagram @{text "D: J \<rightarrow> C"} is a natural transformation
    from a constant functor to @{term D}.  The value of the constant functor is
    the \emph{apex} of the cone.
  *}
  locale cone =
    C: category C +
    J: category J +
    D: diagram J C D +
    A: constant_functor J C a +
    natural_transformation J C A.map D \<chi>
  for J :: "'j comp"
  and C :: "'c comp"
  and D :: "'j \<Rightarrow> 'c"
  and a :: 'c
  and \<chi> :: "'j \<Rightarrow> 'c"
  begin

    lemma ide_apex:
    shows "C.ide a"
      using A.value_is_ide by auto

    lemma component_in_hom:
    assumes "J.arr j"
    shows "\<chi> j \<in> C.hom a (D (J.cod j))"
      using assms preserves_dom [of j] preserves_cod [of j] by simp

  end

  text{*
    A cone over diagram @{term D} is transformed into a cone over diagram @{term "D o F"}
    by pre-composing with @{term F}.
  *}

  lemma comp_cone_functor:
  assumes "cone J C D a \<chi>" and "functor J' J F"
  shows "cone J' C (D o F) a (\<chi> o F)"
  proof -
    interpret \<chi>: cone J C D a \<chi> using assms(1) by auto
    interpret F: "functor" J' J F using assms(2) by auto
    interpret A': constant_functor J' C a
      apply unfold_locales using \<chi>.A.value_is_ide by auto
    have "A'.map = (\<lambda>j'. if F.A.arr j' then a else \<chi>.C.null)"
      using A'.map_def by auto
    have 1: "\<chi>.A.map o F = A'.map"
      using \<chi>.A.map_def A'.map_def \<chi>.J.not_arr_null by auto
    interpret \<chi>': horizontal_composite J' J C F F \<chi>.A.map D F \<chi> ..
    interpret \<chi>': natural_transformation J' C A'.map "D o F" "\<chi> o F"
      using 1 \<chi>'.natural_transformation_axioms by auto
    show "cone J' C (D o F) a (\<chi> o F)" ..
  qed

  text{*
    A cone over diagram @{term D} can be transformed into a cone over a diagram @{term D'}
    by post-composing with a natural transformation from @{term D} to @{term D'}.
  *}

  lemma vcomp_transformation_cone:
  assumes "cone J C D a \<chi>"
  and "natural_transformation J C D D' \<tau>"
  shows "cone J C D' a (vertical_composite.map J C \<chi> \<tau>)"
  proof -
    interpret \<chi>: cone J C D a \<chi> using assms(1) by auto
    interpret \<tau>: natural_transformation J C D D' \<tau> using assms(2) by auto
    interpret \<tau>o\<chi>: vertical_composite J C \<chi>.A.map D D' \<chi> \<tau> ..
    interpret \<tau>o\<chi>: cone J C D' a \<tau>o\<chi>.map ..
    show ?thesis ..
  qed

  context "functor"
  begin

    lemma preserves_diagrams:
    fixes J :: "'j comp"
    assumes "diagram J A D"
    shows "diagram J B (F o D)"
    proof -
      interpret D: diagram J A D using assms by auto
      interpret FoD: composite_functor J A B D F ..
      show "diagram J B (F o D)" ..
    qed

    lemma preserves_cones:
    fixes J :: "'j comp"
    assumes "cone J A D a \<chi>"
    shows "cone J B (F o D) (F a) (F o \<chi>)"
    proof -
      interpret \<chi>: cone J A D a \<chi> using assms by auto
      interpret Fa: constant_functor J B "F a"
        apply unfold_locales using \<chi>.ide_apex by auto
      interpret \<chi>': horizontal_composite J A B \<chi>.A.map D F F \<chi> F ..
      have 1: "F o \<chi>.A.map = Fa.map"
        using \<chi>.A.map_def Fa.map_def A.not_arr_null by auto
      interpret \<chi>': natural_transformation J B Fa.map "F o D" "F o \<chi>"
        using 1 \<chi>'.natural_transformation_axioms by auto      
      show "cone J B (F o D) (F a) (F o \<chi>)" ..
    qed

  end

  context diagram
  begin

    abbreviation cone
    where "cone a \<chi> \<equiv> Limit.cone J C D a \<chi>"

    abbreviation cones :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) set"
    where "cones a \<equiv> { \<chi>. cone a \<chi> }"

    text{*
      An arrow @{term "f \<in> C.hom a' a"} induces by composition a transformation from
      cones with apex @{term a} to cones with apex @{term a'}.  This transformation
      is functorial in @{term f}.
    *}

    abbreviation cones_map :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) \<Rightarrow> ('j \<Rightarrow> 'c)"
    where "cones_map f \<equiv> (\<lambda>\<chi> \<in> cones (C.cod f). \<lambda>j. if J.arr j then C (\<chi> j) f else C.null)"

    lemma cones_map_mapsto:
    assumes "C.arr f"
    shows "cones_map f \<in> extensional (cones (C.cod f)) \<inter> (cones (C.cod f) \<rightarrow> cones (C.dom f))"
    proof
      show "cones_map f \<in> extensional (cones (C.cod f))" by blast
      show "cones_map f \<in> cones (C.cod f) \<rightarrow> cones (C.dom f)"
      proof
        fix \<chi>
        assume "\<chi> \<in> cones (C.cod f)"
        hence \<chi>: "cone (C.cod f) \<chi>" by auto
        interpret \<chi>: cone J C D "C.cod f" \<chi> using \<chi> by auto
        interpret B: constant_functor J C "C.dom f"
          apply unfold_locales using assms by auto
        have "cone (C.dom f) (\<lambda>j. if J.arr j then C (\<chi> j) f else C.null)"
          apply unfold_locales
          (* 5 *) using assms B.value_is_ide \<chi>.is_natural_1 \<chi>.is_natural_2 apply auto
          (* 1 *) using \<chi>.is_natural_1 (* TODO: Used to be done by auto, what happened? *)
                  by (metis C.comp_assoc J.arr_dom_iff_arr J.cod_dom \<chi>.A.map_simp
                            \<chi>.preserves_arr \<chi>.preserves_cod \<chi>.preserves_dom preserves_arr
                            preserves_dom)
        thus "(\<lambda>j. if J.arr j then C (\<chi> j) f else C.null) \<in> cones (C.dom f)" by auto
      qed
    qed

    lemma cones_map_ide:
    assumes "\<chi> \<in> cones a"
    shows "cones_map a \<chi> = \<chi>"
    proof -
      interpret \<chi>: cone J C D a \<chi> using assms by auto
      have "cones_map a \<chi> = (\<lambda>j. if J.arr j then C (\<chi> j) a else C.null)"
        using assms \<chi>.A.value_is_ide by fastforce
      moreover have "\<And>j. j \<in> Collect J.arr \<Longrightarrow> C.dom (\<chi> j) = a"
        using assms(1) by auto
      ultimately show ?thesis using assms C.comp_arr_dom \<chi>.preserves_arr by fastforce
    qed

    lemma cones_map_comp:
    assumes "C.seq f g"
    shows "cones_map (C f g) = restrict (cones_map g o cones_map f) (cones (C.cod f))"
    proof (intro restr_eqI)
      show "cones (C.cod (C f g)) = cones (C.cod f)" using assms by simp
      show "\<And>\<chi>. \<chi> \<in> cones (C.cod (C f g)) \<Longrightarrow>
                  (\<lambda>j. if J.arr j then C (\<chi> j) (C f g) else C.null)
                      = (cones_map g o cones_map f) \<chi>"
      proof -
        fix \<chi>
        assume \<chi>: "\<chi> \<in> cones (C.cod (C f g))"
        show "(\<lambda>j. if J.arr j then C (\<chi> j) (C f g) else C.null) = (cones_map g o cones_map f) \<chi>"
        proof -
          have "((cones_map g) o (cones_map f)) \<chi> = cones_map g (cones_map f \<chi>)"
            by force
          also have "... = (\<lambda>j. if J.arr j then
                              C ((\<lambda>j. if J.arr j then C (\<chi> j) f else C.null) j) g else C.null)"
            using assms \<chi> cones_map_mapsto [of f] by force
          also have "... = (\<lambda>j. if J.arr j then C (\<chi> j) (C f g) else C.null)"
          proof -
            have "\<And>j. J.arr j \<Longrightarrow> C (C (\<chi> j) f) g = C (\<chi> j) (C f g)"
            proof -
              interpret \<chi>: cone J C D "C.cod f" \<chi> using assms \<chi> by auto
              fix j
              assume j: "J.arr j"
              show "C (C (\<chi> j) f) g = C (\<chi> j) (C f g)"
                using assms \<chi> j by auto
            qed
            thus ?thesis by auto
          qed
          finally show ?thesis by auto
        qed
      qed
    qed

  end

  text{*
    Changing the apex of a cone by pre-composing with an arrow @{term f} commutes
    with changing the diagram of a cone by post-composing with a natural transformation.
  *}

  lemma cones_map_vcomp:
  assumes "diagram J C D" and "diagram J C D'"
  and "natural_transformation J C D D' \<tau>"
  and "cone J C D a \<chi>"
  and f: "f \<in> category.hom C a' a"
  shows "diagram.cones_map J C D' f (vertical_composite.map J C \<chi> \<tau>)
           = vertical_composite.map J C (diagram.cones_map J C D f \<chi>) \<tau>"
  proof -
    interpret D: diagram J C D using assms(1) by auto
    interpret D': diagram J C D' using assms(2) by auto
    interpret \<tau>: natural_transformation J C D D' \<tau> using assms(3) by auto
    interpret \<chi>: cone J C D a \<chi> using assms(4) by auto
    interpret \<tau>o\<chi>: vertical_composite J C \<chi>.A.map D D' \<chi> \<tau> ..
    interpret \<tau>o\<chi>: cone J C D' a \<tau>o\<chi>.map ..
    interpret \<chi>f: cone J C D a' "D.cones_map f \<chi>"
      using f \<chi>.cone_axioms D.cones_map_mapsto by blast
    interpret \<tau>o\<chi>f: vertical_composite J C \<chi>f.A.map D D' "D.cones_map f \<chi>" \<tau> ..
    interpret \<tau>o\<chi>_f: cone J C D' a' "D'.cones_map f \<tau>o\<chi>.map"
      using f \<tau>o\<chi>.cone_axioms D'.cones_map_mapsto [of f] by blast
    show "D'.cones_map f \<tau>o\<chi>.map = \<tau>o\<chi>f.map"
    proof (intro NaturalTransformation.eqI)
      show "natural_transformation J C \<chi>f.A.map D' (D'.cones_map f \<tau>o\<chi>.map)" ..
      show "natural_transformation J C \<chi>f.A.map D' \<tau>o\<chi>f.map" ..
      show "\<And>j. D.J.ide j \<Longrightarrow> D'.cones_map f \<tau>o\<chi>.map j = \<tau>o\<chi>f.map j"
      proof -
        fix j
        assume j: "D.J.ide j"
        have "D'.cones_map f \<tau>o\<chi>.map j = C (\<tau>o\<chi>.map j) f"
          using f \<tau>o\<chi>.cone_axioms \<tau>o\<chi>.map_simp_2 [of j] by simp
        also have "... = C (C (\<tau> j) (\<chi> (D.J.dom j))) f"
          using j \<tau>o\<chi>.map_simp_2 [of j] by simp
        also have "... = C (\<tau> j) (C (\<chi> (D.J.dom j)) f)"
          using j f by simp
        also have "... = \<tau>o\<chi>f.map j"
          using j f \<chi>.cone_axioms \<tau>o\<chi>f.map_simp_2 [of j] by simp
        finally show "D'.cones_map f \<tau>o\<chi>.map j = \<tau>o\<chi>f.map j" by auto
      qed
    qed
  qed

  text{*
    Given a diagram @{term D}, we can construct a contravariant set-valued functor,
    which takes each object @{term a} of @{term C} to the set of cones over @{term D}
    with apex @{term a}, and takes each arrow @{term f} of @{term C} to the function
    on cones over @{term D} induced by pre-composition with @{term f}.
    For this, we need to introduce a set category @{term S} whose universe is large
    enough to contain all the cones over @{term D}, and we need to have an explicit
    correspondence between cones and elements of the universe of @{term S}.
    A set category @{term S} equipped with an injective mapping
    @{term_type "\<iota> :: ('j => 'c) => 's"} serves this purpose.
  *}
  locale cones_functor =
    C: category C +
    Cop: dual_category C +
    J: category J +
    D: diagram J C D +
    S: concrete_set_category S UNIV \<iota>
  for J :: "'j comp"
  and C :: "'c comp"
  and D :: "'j \<Rightarrow> 'c"
  and S :: "'s comp"
  and \<iota> :: "('j \<Rightarrow> 'c) \<Rightarrow> 's"
  begin

    abbreviation \<o> where "\<o> \<equiv> S.\<o>"

    definition map :: "'c \<Rightarrow> 's"
    where "map = (\<lambda>f. if C.arr f then
                        S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom f))
                                (\<iota> o D.cones_map f o \<o>)
                      else S.null)"

    lemma map_simp [simp]:
    assumes "C.arr f"
    shows "map f = S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom f)) (\<iota> o D.cones_map f o \<o>)"
      using assms map_def by auto

    lemma arr_map:
    assumes "C.arr f"
    shows "S.arr (map f)"
    proof -
      have "\<iota> o D.cones_map f o \<o> \<in> \<iota> ` D.cones (C.cod f) \<rightarrow> \<iota> ` D.cones (C.dom f)"
        using assms S.\<o>_mapsto D.cones_map_mapsto [of f] S.\<iota>_mapsto by force
      thus ?thesis using assms S.\<iota>_mapsto by auto
    qed

    lemma map_ide:
    assumes "C.ide a"
    shows "map a = S.mkIde (\<iota> ` D.cones a)"
    proof -
      have "map a = S.mkArr (\<iota> ` D.cones a) (\<iota> ` D.cones a) (\<iota> o D.cones_map a o \<o>)"
        using assms map_simp by force
      also have "... = S.mkArr (\<iota> ` D.cones a) (\<iota> ` D.cones a) (\<lambda>x. x)"
        using S.\<iota>_mapsto D.cones_map_ide by force
      also have "... = S.mkIde (\<iota> ` D.cones a)"
        using assms S.mkIde_as_mkArr S.\<iota>_mapsto by blast
      finally show ?thesis by auto
    qed

    lemma map_preserves_dom:
    assumes "Cop.arr f"
    shows "map (Cop.dom f) = S.dom (map f)"
      using assms map_def map_ide arr_map D.cones_map_ide by auto

    lemma map_preserves_cod:
    assumes "Cop.arr f"
    shows "map (Cop.cod f) = S.cod (map f)"
      using assms map_def map_ide arr_map D.cones_map_ide by auto

    lemma map_preserves_comp:
    assumes "Cop.seq g f"
    shows "map (Cop.comp g f) = S (map g) (map f)"
    proof -
      have 0: "S.seq (map g) (map f)"
        using assms arr_map [of f] arr_map [of g] map_simp [of f] map_simp [of g]
        by fastforce
      have "map (Cop.comp g f) = S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom g))
                                         ((\<iota> o D.cones_map g o \<o>) o (\<iota> o D.cones_map f o \<o>))"
      proof -
        have 1: "S.arr (map (Cop.comp g f))"
          using assms arr_map [of "C f g"] by simp
        have "map (Cop.comp g f) =
                 S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom g))
                         (\<iota> o D.cones_map (C f g) o \<o>)"
          using assms map_simp [of "C f g"] by simp
        also have "... = S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom g))
                                 ((\<iota> o D.cones_map g o \<o>) o (\<iota> o D.cones_map f o \<o>))"
          using assms 1 calculation D.cones_map_mapsto [of "C f g"] D.cones_map_comp by auto
        finally show ?thesis by blast
      qed
      also have "... = S (map g) (map f)" using assms 0 by auto
      finally show ?thesis by auto
    qed

    lemma is_functor:
    shows "functor Cop.comp S map"
      apply (unfold_locales)
      using map_def arr_map map_preserves_dom map_preserves_cod map_preserves_comp
      by auto
    
  end

  sublocale cones_functor \<subseteq> "functor" Cop.comp S map using is_functor by auto
  sublocale cones_functor \<subseteq> set_valued_functor Cop.comp S map ..

  section Limits

  subsection "Limit Cones"

  text{*
    A \emph{limit cone} for a diagram @{term D} is a cone @{term \<chi>} over @{term D}
    with the universal property that any other cone @{term \<chi>'} over the diagram @{term D}
    factors uniquely through @{term \<chi>}.
  *}

  locale limit_cone =
    C: category C +
    J: category J +
    D: diagram J C D +
    cone J C D a \<chi>
  for J :: "'j comp"
  and C :: "'c comp"
  and D :: "'j \<Rightarrow> 'c"
  and a :: 'c
  and \<chi> :: "'j \<Rightarrow> 'c" +
  assumes is_universal: "cone J C D a' \<chi>' \<Longrightarrow> \<exists>!f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<chi>'"
  begin

    definition induced_arrow :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) \<Rightarrow> 'c"
    where "induced_arrow a' \<chi>' = (THE f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<chi>')"

    lemma induced_arrowI:
    assumes \<chi>': "\<chi>' \<in> D.cones a'"
    shows "induced_arrow a' \<chi>' \<in> C.hom a' a \<and> D.cones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
    proof -
      have "\<exists>!f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<chi>'"
        using assms \<chi>' is_universal by simp
      thus ?thesis
        using theI' [of "\<lambda>f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<chi>'"] induced_arrow_def
        by presburger
    qed

    lemma cones_map_induced_arrow:
    shows "induced_arrow a' \<in> D.cones a' \<rightarrow> C.hom a' a"
    and "\<And>\<chi>'. \<chi>' \<in> D.cones a' \<Longrightarrow> D.cones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
      using induced_arrowI apply simp
      using induced_arrowI by blast

    lemma induced_arrow_cones_map:
    assumes "C.ide a'"
    shows "(\<lambda>f. D.cones_map f \<chi>) \<in> C.hom a' a \<rightarrow> D.cones a'"
    and "\<And>f. f \<in> C.hom a' a \<Longrightarrow> induced_arrow a' (D.cones_map f \<chi>) = f"
    proof -
      have a': "C.ide a'" using assms by (simp add: cone.ide_apex)
      have cone_\<chi>: "cone J C D a \<chi>" ..
      show "(\<lambda>f. D.cones_map f \<chi>) \<in> C.hom a' a \<rightarrow> D.cones a'"
        using cone_\<chi> D.cones_map_mapsto by blast
      fix f
      assume f: "f \<in> C.hom a' a"
      show "induced_arrow a' (D.cones_map f \<chi>) = f"
      proof -
        have "D.cones_map f \<chi> \<in> D.cones a'"
          using f cone_\<chi> D.cones_map_mapsto [of f] by blast
        hence "\<exists>!f'. f' \<in> C.hom a' a \<and> D.cones_map f' \<chi> = D.cones_map f \<chi>"
          using assms is_universal by blast
        thus ?thesis
          using f induced_arrow_def
                the1_equality [of "\<lambda>f'. f' \<in> C.hom a' a \<and> D.cones_map f' \<chi> = D.cones_map f \<chi>"]
          by presburger
      qed
    qed

    text{*
      For a limit cone @{term \<chi>} with apex @{term a}, for each object @{term a'} the
      hom-set @{term "C.hom a' a"} is in bijective correspondence with the set of cones
      with apex @{term a'}.
    *}

    lemma bij_betw_hom_and_cones:
    assumes "C.ide a'"
    shows "bij_betw (\<lambda>f. D.cones_map f \<chi>) (C.hom a' a) (D.cones a')"
    proof (intro bij_betwI)
      show "(\<lambda>f. D.cones_map f \<chi>) \<in> C.hom a' a \<rightarrow> D.cones a'"
        using assms induced_arrow_cones_map by blast
      show "induced_arrow a' \<in> D.cones a' \<rightarrow> C.hom a' a"
        using assms cones_map_induced_arrow by blast
      show "\<And>f. f \<in> C.hom a' a \<Longrightarrow> induced_arrow a' (D.cones_map f \<chi>) = f"
        using assms induced_arrow_cones_map by blast
      show "\<And>\<chi>'. \<chi>' \<in> D.cones a' \<Longrightarrow> D.cones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
        using assms cones_map_induced_arrow by blast
    qed

    lemma induced_arrow_eqI:
    assumes "D.cone a' \<chi>'" and "f \<in> C.hom a' a" and "D.cones_map f \<chi> = \<chi>'"
    shows "induced_arrow a' \<chi>' = f"
      using assms is_universal [of a' \<chi>'] induced_arrow_def [of a' \<chi>']
            the1_equality [of "\<lambda>f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<chi>'" f]
      by presburger

    lemma induced_arrow_self:
    shows "induced_arrow a \<chi> = a"
    proof -
      have "a \<in> C.hom a a \<and> D.cones_map a \<chi> = \<chi>" using ide_apex cone_axioms by auto
      thus ?thesis using induced_arrow_eqI [of a \<chi>] cone_axioms by auto
    qed

  end

  context diagram
  begin

    abbreviation limit_cone
    where "limit_cone a \<chi> \<equiv> Limit.limit_cone J C D a \<chi>"

    text{*
      A diagram @{term D} has object @{term a} as a limit if @{term a} is the apex
      of some limit cone over @{term D}.
    *}

    abbreviation has_as_limit :: "'c \<Rightarrow> bool"
    where "has_as_limit a \<equiv> (\<exists>\<chi>. limit_cone a \<chi>)"

    abbreviation has_limit
    where "has_limit \<equiv> (\<exists>a \<chi>. limit_cone a \<chi>)"

    definition some_limit :: 'c
    where "some_limit = (SOME a. \<exists>\<chi>. limit_cone a \<chi>)"

    definition some_limit_cone :: "'j \<Rightarrow> 'c"
    where "some_limit_cone = (SOME \<chi>. limit_cone some_limit \<chi>)"

    lemma limit_cone_some_limit_cone:
    assumes has_limit
    shows "limit_cone some_limit some_limit_cone"
    proof -
      have "\<exists>a. has_as_limit a" using assms by simp
      hence "has_as_limit some_limit"
        using some_limit_def someI_ex [of "\<lambda>a. \<exists>\<chi>. limit_cone a \<chi>"] by simp
      thus "limit_cone some_limit some_limit_cone"
        using assms some_limit_cone_def someI_ex [of "\<lambda>\<chi>. limit_cone some_limit \<chi>"]
        by simp
    qed

    lemma ex_limitE:
    assumes "\<exists>a. has_as_limit a"
    obtains a \<chi> where "limit_cone a \<chi>"
    proof -
      have "\<exists>a \<chi>. limit_cone a \<chi>" using assms by blast
      thus ?thesis using that someI_ex by auto
    qed

  end

  subsection "Limits by Representation"

  text{*
    A limit for a diagram D can also be given by a representation @{text "(a, \<Phi>)"}
    of the cones functor.
  *}

  locale representation_of_cones_functor =
    C: category C +
    Cop: dual_category C +
    J: category J +
    D: diagram J C D +
    S: concrete_set_category S UNIV \<iota> +
    Cones: cones_functor J C D S \<iota> +
    Hom: hom_functor C S \<phi> +
    representation_of_functor C S \<phi> Cones.map a \<Phi>
  for J :: "'j comp"
  and C :: "'c comp"
  and D :: "'j \<Rightarrow> 'c"
  and S :: "'s comp"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  and \<iota> :: "('j \<Rightarrow> 'c) \<Rightarrow> 's"
  and a :: 'c
  and \<Phi> :: "'c \<Rightarrow> 's"

  subsection "Putting it all Together"

  text{*
    A ``limit situation'' combines and connects the ways of presenting a limit.
  *}

  locale limit_situation =
    C: category C +
    Cop: dual_category C +
    J: category J +
    D: diagram J C D +
    S: concrete_set_category S UNIV \<iota> +
    Cones: cones_functor J C D S \<iota> +
    Hom: hom_functor C S \<phi> +
    \<Phi>: representation_of_functor C S \<phi> Cones.map a \<Phi> +
    \<chi>: limit_cone J C D a \<chi>
  for J :: "'j comp"
  and C :: "'c comp"
  and D :: "'j \<Rightarrow> 'c"
  and S :: "'s comp"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  and \<iota> :: "('j \<Rightarrow> 'c) \<Rightarrow> 's"
  and a :: 'c
  and \<Phi> :: "'c \<Rightarrow> 's"
  and \<chi> :: "'j \<Rightarrow> 'c" +
  assumes \<chi>_in_terms_of_\<Phi>: "\<chi> = S.\<o> (S.Fun (\<Phi> a) (\<phi> (a, a) a))"
  and \<Phi>_in_terms_of_\<chi>:
     "Cop.ide a' \<Longrightarrow> \<Phi> a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a')
                                    (\<lambda>x. \<iota> (D.cones_map (Hom.\<psi> (a', a) x) \<chi>))"

  text (in limit_situation) {*
    The assumption @{prop \<chi>_in_terms_of_\<Phi>} states that the universal cone @{term \<chi>} is obtained
    by applying the function @{term "S.Fun (\<Phi> a)"} to the identity @{term a} of @{term C}
    (after taking into account the necessary coercions).
  *}

  text (in limit_situation) {*
    The assumption @{prop \<Phi>_in_terms_of_\<chi>} states that the component of @{term \<Phi>} at @{term a'}
    is the arrow of @{term S} corresponding to the function that takes an arrow
    @{term "f \<in> C.hom a' a"} and produces the cone with vertex @{term a'} obtained
    by transforming the universal cone @{term \<chi>} by @{term f}.
  *}

  subsection "Limit Cones Induce Limit Situations"

  text{*
    To obtain a limit situation from a limit cone, we need to introduce a set category
    that is large enough to contain the hom-sets of @{term C} as well as the cones
    over @{term D}.  We use the category of @{typ "('c + ('j \<Rightarrow> 'c))"}-sets for this.
  *}

  context limit_cone
  begin

    interpretation Cop: dual_category C ..
    interpretation CopxC: product_category Cop.comp C ..
    interpretation S: set_category "SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) SetCat.arr comp"
      using SetCat.is_set_category by auto

    interpretation S: concrete_set_category "SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) SetCat.arr comp"
                                            UNIV "UP o Inr"
      apply unfold_locales
      (* 2 *) using UP_mapsto apply auto[1]
      (* 1 *) using inj_UP inj_Inr inj_comp by metis

    interpretation Cones: cones_functor J C D "SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) SetCat.arr comp"
                                        "UP o Inr" ..

    interpretation Hom: hom_functor C "SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) SetCat.arr comp"
                                      "\<lambda>_. UP o Inl"
      apply (unfold_locales)
      (* 2 *) using UP_mapsto apply auto[1]
      (* 1 *) using SetCat.inj_UP injD inj_onI inj_Inl inj_comp by (metis (no_types, lifting))

    interpretation Y: yoneda_functor C "SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) SetCat.arr comp"
                                     "\<lambda>_. UP o Inl" ..
    interpretation Ya: yoneda_functor_fixed_object
                         C "SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) SetCat.arr comp"
                         "\<lambda>_. UP o Inl" a
      apply (unfold_locales) using ide_apex by auto

    abbreviation inl :: "'c \<Rightarrow> 'c + ('j \<Rightarrow> 'c)" where "inl \<equiv> Inl"
    abbreviation inr :: "('j \<Rightarrow> 'c) \<Rightarrow> 'c + ('j \<Rightarrow> 'c)" where "inr \<equiv> Inr"
    abbreviation \<iota> where "\<iota> \<equiv> UP o inr"
    abbreviation \<o> where "\<o> \<equiv> Cones.\<o>"
    abbreviation \<phi> where "\<phi> \<equiv> \<lambda>_. UP o inl"
    abbreviation \<psi> where "\<psi> \<equiv> Hom.\<psi>"
    abbreviation Y where "Y \<equiv> Y.Y"

    lemma Ya_ide:
    assumes a': "C.ide a'"
    shows "Y a a' = S.mkIde (Hom.set (a', a))"
      using assms ide_apex Y.Y_simp [of a] Hom.map_ide [of a' a] by simp

    lemma Ya_arr:
    assumes g: "C.arr g"
    shows "Y a g = S.mkArr (Hom.set (C.cod g, a)) (Hom.set (C.dom g, a))
                             (\<phi> (C.dom g, a) o Cop.comp g o \<psi> (C.cod g, a))"
      using ide_apex g Y.Y_ide_arr [of a g "C.dom g" "C.cod g"] by blast

    lemma cone_\<chi> [simp]:
    shows "\<chi> \<in> D.cones a"
      using cone_axioms by simp
    
    text{*
      For each object @{term a'} of @{term C} we have a function mapping @{term "C.hom a' a"}
      to the set of cones over @{term D} with apex @{term a'}, which takes
      @{term "f \<in> C.hom a' a"} to @{text \<chi>f}, where @{text \<chi>f} is the cone obtained by
      composing @{term \<chi>} with @{term f} (after accounting for coercions to and from the
      universe of @{term S}.  The corresponding arrows of @{term S} are the
      components of a natural isomorphism from @{term "Y a"} to @{text "Cones"}.
    *}

    definition \<Phi>o :: "'c \<Rightarrow> ('c + ('j \<Rightarrow> 'c)) SetCat.arr"
    where "\<Phi>o a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') (\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>))"

    lemma \<Phi>o_in_hom:
    assumes a': "C.ide a'"
    shows "\<Phi>o a' \<in> S.hom (S.mkIde (Hom.set (a', a))) (S.mkIde (\<iota> ` D.cones a'))"
    proof -
      have "S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') (\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>))
               \<in> S.hom (S.mkIde (Hom.set (a', a))) (S.mkIde (\<iota> ` D.cones a'))"
      proof -
        have "(\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)) \<in> Hom.set (a', a) \<rightarrow> \<iota> ` D.cones a'"
        proof
          fix x
          assume x: "x \<in> Hom.set (a', a)"
          hence "\<psi> (a', a) x \<in> C.hom a' a" using ide_apex a' Hom.\<psi>_mapsto by auto
          hence "D.cones_map (\<psi> (a', a) x) \<chi> \<in> D.cones a'"
            using ide_apex a' x D.cones_map_mapsto cone_\<chi> by force
          thus "\<iota> (D.cones_map (\<psi> (a', a) x) \<chi>) \<in> \<iota> ` D.cones a'" by simp
        qed
        moreover have "Hom.set (a', a) \<subseteq> S.Univ" using ide_apex a' Hom.set_subset_Univ by auto
        moreover have "\<iota> ` D.cones a' \<subseteq> S.Univ" using UP_mapsto by auto
        ultimately show ?thesis using S.mkArr_in_hom by simp
      qed
      thus ?thesis using \<Phi>o_def [of a'] by auto
    qed

    interpretation \<Phi>: transformation_by_components Cop.comp SetCat.comp "Y a" Cones.map \<Phi>o
    proof
      fix a'
      assume A': "Cop.ide a'"
      show "\<Phi>o a' \<in> S.hom (Y a a') (Cones.map a')"
        using A' Ya_ide [of a'] \<Phi>o_in_hom [of a'] Cones.map_ide [of a'] by auto
      next
      fix g
      assume g: "Cop.arr g"
      show "SetCat.comp (\<Phi>o (Cop.cod g)) (Y a g) = SetCat.comp (Cones.map g) (\<Phi>o (Cop.dom g))"
      proof -
        let ?A = "Hom.set (C.cod g, a)"
        let ?B = "Hom.set (C.dom g, a)"
        let ?B' = "\<iota> ` D.cones (C.cod g)"
        let ?C = "\<iota> ` D.cones (C.dom g)"
        let ?F = "\<phi> (C.dom g, a) o Cop.comp g o \<psi> (C.cod g, a)"
        let ?F' = "\<iota> o D.cones_map g o \<o>"
        let ?G = "\<lambda>x. \<iota> (D.cones_map (\<psi> (C.dom g, a) x) \<chi>)"
        let ?G' = "\<lambda>x. \<iota> (D.cones_map (\<psi> (C.cod g, a) x) \<chi>)"
        have "S.arr (Y a g) \<and> Y a g = S.mkArr ?A ?B ?F"
          using ide_apex g Ya.preserves_arr Ya_arr by blast
        moreover have "S.arr (\<Phi>o (Cop.cod g)) \<and> \<Phi>o (Cop.cod g) = S.mkArr ?B ?C ?G"
          using g \<Phi>o_in_hom [of "C.dom g"] \<Phi>o_def [of "C.dom g"] by auto
        ultimately have 1: "S.arr (SetCat.comp (\<Phi>o (Cop.cod g)) (Y a g)) \<and>
                            SetCat.comp (\<Phi>o (Cop.cod g)) (Y a g) = S.mkArr ?A ?C (?G o ?F)"
          using S.arr_comp [of "Y a g" "\<Phi>o (Cop.cod g)"] by auto
        have "S.arr (Cones.map g) \<and>
              Cones.map g = S.mkArr (\<iota> ` D.cones (C.cod g)) (\<iota> ` D.cones (C.dom g)) ?F'"
          using g Cones.preserves_arr Cones.map_simp by blast
        moreover have "S.arr (\<Phi>o (Cop.dom g)) \<and> \<Phi>o (Cop.dom g) = S.mkArr ?A ?B' ?G'"
          using g \<Phi>o_in_hom [of "C.cod g"] \<Phi>o_def [of "C.cod g"] by fastforce
        ultimately have 2: "S.arr (SetCat.comp (Cones.map g) (\<Phi>o (Cop.dom g))) \<and>
                            SetCat.comp (Cones.map g) (\<Phi>o (Cop.dom g)) = S.mkArr ?A ?C (?F' o ?G')"
          using S.arr_comp [of "\<Phi>o (Cop.dom g)" "Cones.map g"] by auto
        have "SetCat.comp (\<Phi>o (Cop.cod g)) (Y a g) = S.mkArr ?A ?C (?G o ?F)"
          using 1 by auto
        also have "... = S.mkArr ?A ?C (?F' o ?G')"
        proof (intro S.mkArr_eqI')
          show "S.arr (S.mkArr ?A ?C (?G o ?F))" using 1 by force
          show "\<And>x. x \<in> ?A \<Longrightarrow> (?G o ?F) x = (?F' o ?G') x"
          proof -
            fix x
            assume x: "x \<in> ?A"
            hence 1: "\<psi> (C.cod g, a) x \<in> C.hom (C.cod g) a"
              using ide_apex g Hom.\<psi>_mapsto [of "C.cod g" a] by auto
            have "(?G o ?F) x = \<iota> (D.cones_map (\<psi> (C.dom g, a)
                                  (\<phi> (C.dom g, a) (Cop.comp g (\<psi> (C.cod g, a) x)))) \<chi>)"
            proof - (* Why is it so balky with this proof? Some unification issue? *)
              have "(?G o ?F) x = ?G (?F x)" by simp
              moreover have 1: "... = \<iota> (D.cones_map (\<psi> (C.dom g, a) (?F x)) \<chi>)" by simp
              moreover have "... = \<iota> (D.cones_map (\<psi> (C.dom g, a)
                                     (\<phi> (C.dom g, a) (Cop.comp g (\<psi> (C.cod g, a) x)))) \<chi>)"
              proof -
                have "?F x = \<phi> (C.dom g, a) (Cop.comp g (\<psi> (C.cod g, a) x))" by simp
                thus ?thesis using 1 by metis
              qed
              ultimately show ?thesis by auto
            qed
            also have "... = \<iota> (D.cones_map (Cop.comp g (\<psi> (C.cod g, a) x)) \<chi>)"
            proof -
              have "Cop.comp g (\<psi> (C.cod g, a) x) \<in> C.hom (C.dom g) a" using g 1 by simp
              thus ?thesis using Hom.\<psi>_\<phi> by presburger
            qed
            also have "... = \<iota> (D.cones_map (C (\<psi> (C.cod g, a) x) g) \<chi>)"
            proof -
              have "Cop.comp g (\<psi> (C.cod g, a) x) = C (\<psi> (C.cod g, a) x) g" by auto
              thus ?thesis by presburger
            qed
            also have "... = \<iota> (D.cones_map g (D.cones_map (\<psi> (C.cod g, a) x) \<chi>))"
              using g x 1 cone_\<chi> D.cones_map_comp [of g "\<psi> (C.cod g, a) x"] by simp
            also have "... = \<iota> (D.cones_map g (\<o> (\<iota> (D.cones_map (\<psi> (C.cod g, a) x) \<chi>))))"
            proof -
              have "D.cones_map (\<psi> (C.cod g, a) x) \<chi> \<in> D.cones (C.cod g)"
                using 1 cone_\<chi> D.cones_map_mapsto [of "\<psi> (C.cod g, a) x"] by force
              thus ?thesis using S.\<o>_\<iota> by auto
            qed
            also have "... = (?F' o ?G') x" by simp
            finally show "(?G o ?F) x = (?F' o ?G') x" by auto
          qed
        qed
        also have "... = SetCat.comp (Cones.map g) (\<Phi>o (Cop.dom g))"
          using 2 by auto
       finally show ?thesis by auto
      qed
    qed

    interpretation \<Phi>: set_valued_transformation Cop.comp SetCat.comp "Y a" Cones.map \<Phi>.map ..
                                            
    interpretation \<Phi>: natural_isomorphism Cop.comp SetCat.comp "Y a" Cones.map \<Phi>.map
    proof
      fix a'
      assume a': "Cop.ide a'"
      show "S.iso (\<Phi>.map a')"
      proof -
        let ?F = "\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
        have bij: "bij_betw ?F (Hom.set (a', a)) (\<iota> ` D.cones a')"
        proof -
          have "\<And>x x'. \<lbrakk> x \<in> Hom.set (a', a); x' \<in> Hom.set (a', a);
                         \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>) \<rbrakk>
                            \<Longrightarrow> x = x'"
          proof -
            fix x x'
            assume x: "x \<in> Hom.set (a', a)" and x': "x' \<in> Hom.set (a', a)"
            and xx': "\<iota> (D.cones_map (\<psi> (a', a) x) \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>)"
            have \<psi>x: "\<psi> (a', a) x \<in> C.hom a' a" using x ide_apex a' Hom.\<psi>_mapsto by auto
            have \<psi>x': "\<psi> (a', a) x' \<in> C.hom a' a" using x' ide_apex a' Hom.\<psi>_mapsto by auto
            have 1: "\<exists>!f. f \<in> C.hom a' a \<and> \<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
            proof -
              have "D.cones_map (\<psi> (a', a) x) \<chi> \<in> D.cones a'"
                using \<psi>x a' cone_\<chi> D.cones_map_mapsto [of "\<psi> (a', a) x"] by force
              hence 2: "\<exists>!f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = D.cones_map (\<psi> (a', a) x) \<chi>"
                using a' is_universal by simp
              show "\<exists>!f. f \<in> C.hom a' a \<and> \<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
              proof -
                have "\<And>f. \<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)
                             \<longleftrightarrow> D.cones_map f \<chi> = D.cones_map (\<psi> (a', a) x) \<chi>"
                proof -
                  fix f :: 'c
                  have "D.cones_map f \<chi> = D.cones_map (\<psi> (a', a) x) \<chi>
                           \<longrightarrow> \<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                    by presburger
                  thus "(\<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>))
                            = (D.cones_map f \<chi> = D.cones_map (\<psi> (a', a) x) \<chi>)"
                    by (meson S.inj_\<iota> injD)
                 qed
                thus ?thesis using 2 by auto
              qed
            qed
            have 2: "\<exists>!x''. x'' \<in> Hom.set (a', a) \<and>
                            \<iota> (D.cones_map (\<psi> (a', a) x'') \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
            proof -
              from 1 obtain f'' where
                  f'': "f'' \<in> C.hom a' a \<and> \<iota> (D.cones_map f'' \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                by blast
              have "\<phi> (a', a) f'' \<in> Hom.set (a', a) \<and>
                    \<iota> (D.cones_map (\<psi> (a', a) (\<phi> (a', a) f'')) \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
              proof
                show "\<phi> (a', a) f'' \<in> Hom.set (a', a)" using f'' Hom.set_def by auto
                show "\<iota> (D.cones_map (\<psi> (a', a) (\<phi> (a', a) f'')) \<chi>) =
                         \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                  using f'' Hom.\<psi>_\<phi> [of f'' a' a] by presburger
              qed
              moreover have
                 "\<And>x''. x'' \<in> Hom.set (a', a) \<and>
                         \<iota> (D.cones_map (\<psi> (a', a) x'') \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)
                             \<Longrightarrow> x'' = \<phi> (a', a) f''"
              proof -
                fix x''
                assume x'': "x'' \<in> Hom.set (a', a) \<and>
                             \<iota> (D.cones_map (\<psi> (a', a) x'') \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                hence "\<psi> (a', a) x'' \<in> C.hom a' a \<and>
                       \<iota> (D.cones_map (\<psi> (a', a) x'') \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                  using ide_apex a' Hom.set_def Hom.\<psi>_mapsto [of a' a] by auto
                hence "\<psi> (a', a) x'' = f''"
                  using 1 f'' by auto
                hence "\<phi> (a', a) (\<psi> (a', a) x'') = \<phi> (a', a) f''"
                  by simp
                thus "x'' = \<phi> (a', a) f''"
                  using ide_apex a' x'' Hom.\<phi>_\<psi> [of a' a x''] by simp
              qed
              ultimately show ?thesis
                using ex1I [of "\<lambda>x'. x' \<in> Hom.set (a', a) \<and>
                                     \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>) =
                                        \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                               "\<phi> (a', a) f''"]
                by simp
            qed
            thus "x = x'" using x x' xx' by auto
          qed
          hence "inj_on ?F (Hom.set (a', a))"
            using inj_onI [of "Hom.set (a', a)" ?F] by auto 
          moreover have "?F ` Hom.set (a', a) = \<iota> ` D.cones a'"
          proof
            show "?F ` Hom.set (a', a) \<subseteq> \<iota> ` D.cones a'"
            proof
              fix X'
              assume X': "X' \<in> ?F ` Hom.set (a', a)"
              from this obtain x' where x': "x' \<in> Hom.set (a', a) \<and> ?F x' = X'" by blast
              show "X' \<in> \<iota> ` D.cones a'"
              proof -
                have "X' = \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>)" using x' by blast
                hence "X' = \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>)" using x' by force
                moreover have "\<psi> (a', a) x' \<in> C.hom a' a"
                  using ide_apex a' x' Hom.set_def Hom.\<psi>_\<phi> by auto
                ultimately show ?thesis
                  using x' cone_\<chi> D.cones_map_mapsto [of "\<psi> (a', a) x'"] by force
              qed
            qed
            show "\<iota> ` D.cones a' \<subseteq> ?F ` Hom.set (a', a)"
            proof
              fix X'
              assume X': "X' \<in> \<iota> ` D.cones a'"
              hence "\<o> X' \<in> \<o> ` \<iota> ` D.cones a'" by simp
              hence "\<o> X' \<in> D.cones a'"
                by (simp add: inj_UP inj_comp)
              hence "\<exists>!f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<o> X'"
                using a' is_universal by simp
              from this obtain f where "f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<o> X'"
                by auto
              hence f: "f \<in> C.hom a' a \<and> \<iota> (D.cones_map f \<chi>) = X'"
                using X' S.\<iota>_\<o> [of X'] by auto
              have "X' = ?F (\<phi> (a', a) f)"
                using f Hom.\<psi>_\<phi> [of f a' a] by presburger
              thus "X' \<in> ?F ` Hom.set (a', a)"
                using f Hom.set_def by fastforce
            qed
          qed
          ultimately show ?thesis
            using bij_betw_def [of ?F "Hom.set (a', a)" "\<iota> ` D.cones a'"] inj_on_def by auto
        qed
        let ?f = "S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') ?F"
        have iso: "S.iso ?f"
        proof -
          have "?F \<in> Hom.set (a', a) \<rightarrow> \<iota> ` D.cones a'"
            using bij bij_betw_imp_funcset by fast
          hence "S.arr ?f"
            using ide_apex a' Hom.set_subset_Univ [of a' a] S.\<iota>_mapsto
                  S.arr_mkArr [of "Hom.set (a', a)" "\<iota> ` D.cones a'" ?F]
            by auto
          thus ?thesis using bij S.iso_char by fastforce
        qed
        moreover have "?f = \<Phi>.map a'"
          using a' \<Phi>o_def by force
        finally show ?thesis by auto
      qed
    qed

    interpretation R: representation_of_functor
                         C "SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) SetCat.arr comp"
                         \<phi> Cones.map a \<Phi>.map ..

    lemma \<chi>_in_terms_of_\<Phi>:
    shows "\<chi> = \<o> (\<Phi>.FUN a (\<phi> (a, a) a))"
    proof -
      have "\<Phi>.FUN a (\<phi> (a, a) a) = 
              (\<lambda>x \<in> Hom.set (a, a). \<iota> (D.cones_map (\<psi> (a, a) x) \<chi>)) (\<phi> (a, a) a)"
        using ide_apex S.Fun_mkArr [of "Hom.set (a, a)" "\<iota> ` D.cones a"
                                      "\<lambda>x. \<iota> (D.cones_map (\<psi> (a, a) x) \<chi>)"]
              \<Phi>.map_simp_ide [of a] \<Phi>o_def [of a] \<Phi>.preserves_arr [of a]
        by simp
      also have "... = \<iota> (D.cones_map a \<chi>)"
      proof -
        have "\<phi> (a, a) a \<in> Hom.set (a, a)"
          using ide_apex Hom.\<phi>_mapsto [of a a] by auto
        hence "(\<lambda>x \<in> Hom.set (a, a). \<iota> (D.cones_map (\<psi> (a, a) x) \<chi>)) (\<phi> (a, a) a)
                  = \<iota> (D.cones_map (\<psi> (a, a) (\<phi> (a, a) a)) \<chi>)"
          using restrict_apply' [of "\<phi> (a, a) a" "Hom.set (a, a)"] by blast
        also have "... = \<iota> (D.cones_map a \<chi>)"
        proof -
          have "\<psi> (a, a) (\<phi> (a, a) a) = a"
            using ide_apex Hom.\<psi>_\<phi> [of a a a] by fast
          thus ?thesis by metis
        qed
        finally show ?thesis by auto
      qed
      finally have "\<Phi>.FUN a (\<phi> (a, a) a) = \<iota> (D.cones_map a \<chi>)" by auto
      also have "... = \<iota> \<chi>"
        using ide_apex D.cones_map_ide [of \<chi> a] cone_\<chi> by simp
      finally have "\<Phi>.FUN a (\<phi> (a, a) a) = \<iota> \<chi>" by blast
      hence "\<o> (\<Phi>.FUN a (\<phi> (a, a) a)) = \<o> (\<iota> \<chi>)" by simp
      thus ?thesis using cone_\<chi> S.\<o>_\<iota> by simp
    qed

    abbreviation Hom
    where "Hom \<equiv> Hom.map"

    abbreviation \<Phi>
    where "\<Phi> \<equiv> \<Phi>.map"

    lemma induces_limit_situation:
    shows "limit_situation J C D (SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) SetCat.arr comp) \<phi> \<iota> a \<Phi> \<chi>"
    proof
      show "\<chi> = \<o> (\<Phi>.FUN a (\<phi> (a, a) a))" using \<chi>_in_terms_of_\<Phi> by auto
      fix a'
      show "Cop.ide a' \<Longrightarrow>
               \<Phi>.map a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a')
                                  (\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>))"
        using \<Phi>.map_simp_ide [of a'] \<Phi>o_def [of a'] by presburger
    qed

  end

  sublocale limit_cone \<subseteq> limit_situation J C D "SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) SetCat.arr comp"
                                         \<phi> \<iota> a \<Phi> \<chi>
    using induces_limit_situation by auto

  subsection "Representations of the Cones Functor Induce Limit Situations"

  context representation_of_cones_functor
  begin

    interpretation \<Phi>: set_valued_transformation Cop.comp S "Y a" Cones.map \<Phi> ..
    interpretation \<Psi>: inverse_transformation Cop.comp S "Y a" Cones.map \<Phi> ..
    interpretation \<Psi>: set_valued_transformation Cop.comp S Cones.map "Y a" \<Psi>.map ..

    abbreviation \<o>
    where "\<o> \<equiv> Cones.\<o>"

    abbreviation \<chi>
    where "\<chi> \<equiv> \<o> (S.Fun (\<Phi> a) (\<phi> (a, a) a))"

    lemma Cones_SET_eq_\<iota>_img_cones:
    assumes "C.ide a'"
    shows "Cones.SET a' = \<iota> ` D.cones a'"
    proof -
      have "\<iota> ` D.cones a' \<subseteq> S.Univ" using S.\<iota>_mapsto by auto
      thus ?thesis using assms Cones.map_ide [of a'] by auto
    qed

    lemma \<iota>\<chi>:
    shows "\<iota> \<chi> = S.Fun (\<Phi> a) (\<phi> (a, a) a)"
      using Ya.ide_a S.Fun_mapsto [of "\<Phi> a"] Hom.\<phi>_mapsto [of a a]
            Cones_SET_eq_\<iota>_img_cones [of a] Hom.set_map [of a a]
      by force

    interpretation \<chi>: cone J C D a \<chi>
      using Ya.ide_a S.Fun_mapsto [of "\<Phi> a"] Hom.\<phi>_mapsto [of a a]
            Cones_SET_eq_\<iota>_img_cones Hom.set_map [of a a]
      by force

    lemma cone_\<chi>:
    shows "D.cone a \<chi>" ..

    lemma \<Phi>_FUN_simp:
    assumes a': "C.ide a'" and x: "x \<in> Hom.set (a', a)"
    shows "\<Phi>.FUN a' x = Cones.FUN (\<psi> (a', a) x) (\<iota> \<chi>)"
    proof -
      have \<psi>x: "\<psi> (a', a) x \<in> C.hom a' a"
        using Ya.ide_a a' x Hom.\<psi>_mapsto [of a' a] by blast
      have \<phi>a: "\<phi> (a, a) a \<in> Hom.set (a, a)" using Ya.ide_a Hom.\<phi>_mapsto [of a a] by auto
      have "\<Phi>.FUN a' x = (\<Phi>.FUN a' o Ya.FUN (\<psi> (a', a) x)) (\<phi> (a, a) a)"
        using Ya.Y_ide_arr [of a "\<psi> (a', a) x" a' a] Ya.ide_a S.Fun_mkArr \<psi>x \<phi>a
              Ya.preserves_arr [of "\<psi> (a', a) x"] a' x
        by fastforce
      also have "... = (Cones.FUN (\<psi> (a', a) x) o \<Phi>.FUN a) (\<phi> (a, a) a)"
      proof -
        have "(\<Phi>.FUN a' o Ya.FUN (\<psi> (a', a) x)) (\<phi> (a, a) a)
                = S.Fun (S (\<Phi> a') (Y a (\<psi> (a', a) x))) (\<phi> (a, a) a)"
          using \<psi>x a' \<phi>a Ya.ide_a Ya.map_simp Hom.set_map by simp
        also have "... = S.Fun (S (Cones.map (\<psi> (a', a) x)) (\<Phi> a)) (\<phi> (a, a) a)"
          using \<psi>x is_natural_1 [of "\<psi> (a', a) x"] is_natural_2 [of "\<psi> (a', a) x"] by simp
        also have "... = (Cones.FUN (\<psi> (a', a) x) o \<Phi>.FUN a) (\<phi> (a, a) a)"
          using Ya.ide_a a' \<psi>x \<phi>a preserves_hom [of a a a]
                Cones.preserves_hom [of "\<psi> (a', a) x" a a'] Hom.set_map
          by simp
        finally show ?thesis by simp
      qed
      also have "... = Cones.FUN (\<psi> (a', a) x) (\<iota> \<chi>)" using \<iota>\<chi> by simp
      finally show ?thesis by auto
    qed

    lemma \<chi>_is_universal:
    assumes "D.cone a' \<chi>'"
    shows "\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>')) \<in> C.hom a' a"
    and "D.cones_map (\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))) \<chi> = \<chi>'"
    and "\<lbrakk> f' \<in> C.hom a' a; D.cones_map f' \<chi> = \<chi>' \<rbrakk> \<Longrightarrow> f' = \<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))"
    proof -
      interpret \<chi>': cone J C D a' \<chi>' using assms by auto
      have a': "C.ide a'" using \<chi>'.ide_apex by simp
      have \<iota>\<chi>': "\<iota> \<chi>' \<in> Cones.SET a'" using assms a' Cones_SET_eq_\<iota>_img_cones by auto
      let ?f = "\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))"
      have A: "\<Psi>.FUN a' (\<iota> \<chi>') \<in> Hom.set (a', a)"
      proof -
        have "\<Psi>.FUN a' \<in> Cones.SET a' \<rightarrow> Ya.SET a'"
          using a' \<Psi>.preserves_hom [of a' a' a'] S.Fun_mapsto [of "\<Psi>.map a'"] by simp
        thus ?thesis using a' \<iota>\<chi>' Ya.ide_a Hom.set_map by auto
      qed
      show f: "?f \<in> C.hom a' a" using A a' Ya.ide_a Hom.\<psi>_mapsto [of a' a] by auto
      have E: "\<And>f. f \<in> C.hom a' a \<Longrightarrow> Cones.FUN f (\<iota> \<chi>) = \<Phi>.FUN a' (\<phi> (a', a) f)"
        using a' Ya.ide_a Hom.\<phi>_mapsto [of a' a] \<Phi>_FUN_simp [of a'] by fastforce
      show f\<chi>: "D.cones_map ?f \<chi> = \<chi>'"
      proof -
        have "D.cones_map ?f \<chi> = (\<o> o Cones.FUN ?f o \<iota>) \<chi>"
          using f Cones.preserves_arr [of ?f] cone_\<chi> by simp
        also have "... = \<o> (\<Phi>.FUN a' (\<phi> (a', a) (\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>')))))"
          using f E by simp
        also have "... = \<o> (\<Phi>.FUN a' (\<Psi>.FUN a' (\<iota> \<chi>')))" using Ya.ide_a a' A by simp
        also have "... = \<chi>'"
        proof -
          have "\<Phi>.FUN a' (\<Psi>.FUN a' (\<iota> \<chi>')) = compose (\<Psi>.DOM a') (\<Phi>.FUN a') (\<Psi>.FUN a') (\<iota> \<chi>')"
            using a' \<iota>\<chi>' Cones.map_ide [of a'] \<Psi>.preserves_hom [of a' a' a'] by simp
          also have "... = (\<lambda>x \<in> \<Psi>.DOM a'. x) (\<iota> \<chi>')"
            using a' \<Psi>.inverts_components S.inverse_arrows_char [of "\<Phi> a'" "\<Psi>.map a'"]
            by force
          also have "... = \<iota> \<chi>'"
            using a' \<iota>\<chi>' Cones.map_ide [of a'] \<Psi>.preserves_hom [of a' a' a'] by simp
          finally show ?thesis by auto
        qed
        finally show ?thesis by auto
      qed
      show "\<lbrakk> f' \<in> C.hom a' a; D.cones_map f' \<chi> = \<chi>' \<rbrakk> \<Longrightarrow> f' = ?f"
      proof -
        assume f': "f' \<in> C.hom a' a" and f'\<chi>: "D.cones_map f' \<chi> = \<chi>'"
        show "f' = ?f"
        proof -
          have 1: "\<phi> (a', a) f' \<in> Hom.set (a', a) \<and> \<phi> (a', a) ?f \<in> Hom.set (a', a)"
              using Ya.ide_a a' f f' Hom.\<phi>_mapsto by auto
          have "S.iso (\<Phi> a')" using \<chi>'.ide_apex components_are_iso by auto
          hence 2: "S.arr (\<Phi> a') \<and> bij_betw (\<Phi>.FUN a') (Hom.set (a', a)) (Cones.SET a')"
            using Ya.ide_a a' S.iso_char Hom.set_map by simp
          have "\<Phi>.FUN a' (\<phi> (a', a) f') = \<Phi>.FUN a' (\<phi> (a', a) ?f)"
            using f f' E [of f'] E [of ?f] cone_\<chi> Cones.preserves_arr [of f']
                  Cones.preserves_arr [of ?f] f\<chi> f'\<chi>
            by auto
          moreover have "inj_on (\<Phi>.FUN a') (Hom.set (a', a))"
            using 2 bij_betw_imp_inj_on by blast
          ultimately have 3: "\<phi> (a', a) f' = \<phi> (a', a) ?f"
            using 1 inj_on_def [of "\<Phi>.FUN a'" "Hom.set (a', a)"] by blast
          show ?thesis
            using Ya.ide_a a' Hom.\<phi>_local_bij [of a' a] 3 f f' inj_onD
                  bij_betw_imp_inj_on [of "\<phi> (a', a)" "C.hom a' a" "Hom.set (a', a)"]
            by fastforce
        qed
      qed
    qed

    interpretation \<chi>: limit_cone J C D a \<chi>
    proof
      show "\<And>a' \<chi>'. D.cone a' \<chi>' \<Longrightarrow> \<exists>!f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<chi>'"
      proof -
        fix a' \<chi>'
        assume 1: "D.cone a' \<chi>'"
        show "\<exists>!f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<chi>'"
        proof
          show "\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>')) \<in> C.hom a' a \<and>
                D.cones_map (\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))) \<chi> = \<chi>'"
            using 1 \<chi>_is_universal by blast
          show "\<And>f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<chi>' \<Longrightarrow> f = \<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))"
            using 1 \<chi>_is_universal by fast
        qed
      qed
    qed

    lemma \<chi>_is_limit_cone:
    shows "D.limit_cone a \<chi>" ..

    lemma induces_limit_situation:
    shows "limit_situation J C D S \<phi> \<iota> a \<Phi> \<chi>"
    proof
      show "\<chi> = \<chi>" by simp
      fix a'
      assume a': "Cop.ide a'"
      let ?F = "\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
      show "\<Phi> a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') ?F"
      proof -
        have 1: "\<Phi> a' \<in> S.hom (S.mkIde (Hom.set (a', a))) (S.mkIde (\<iota> ` D.cones a'))"
          using a' preserves_hom [of a' a' a'] Cones.map_ide [of a'] Ya.ide_a by simp
        moreover have "\<Phi>.DOM a' = Hom.set (a', a)"
          using 1 Hom.set_subset_Univ a' Ya.ide_a by simp
        moreover have "\<Phi>.COD a' = \<iota> ` D.cones a'"
          using a' Cones_SET_eq_\<iota>_img_cones by auto
        ultimately have 2: "\<Phi> a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') (\<Phi>.FUN a')"
          using S.mkArr_Fun [of "\<Phi> a'"] by simp
        also have "... = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') ?F"
        proof
          show "S.arr (S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') (\<Phi>.FUN a'))"
            using 1 2 by auto
          show "\<And>x. x \<in> Hom.set (a', a) \<Longrightarrow> \<Phi>.FUN a' x = ?F x"
          proof -
            fix x
            assume x: "x \<in> Hom.set (a', a)"
            hence \<psi>x: "\<psi> (a', a) x \<in> C.hom a' a"
              using a' Ya.ide_a Hom.\<psi>_mapsto [of a' a] by auto
            show "\<Phi>.FUN a' x = ?F x"
            proof -
              have "\<Phi>.FUN a' x = Cones.FUN (\<psi> (a', a) x) (\<iota> \<chi>)"
                using a' x \<Phi>_FUN_simp [of a' x] by simp
              moreover have "... = S.Fun (Cones.map (\<psi> (a', a) x)) (\<iota> \<chi>)" by simp
              moreover have
                 "... = restrict (\<iota> o D.cones_map (\<psi> (a', a) x) o \<o>) (\<iota> ` D.cones a) (\<iota> \<chi>)"
                using \<psi>x Cones.map_simp [of "\<psi> (a', a) x"] Cones.preserves_arr [of "\<psi> (a', a) x"]
                      Cones.map_simp [of "\<psi> (a', a) x"]
                      S.Fun_mkArr [of "\<iota> ` D.cones a" "\<iota> ` D.cones a'"
                                     "\<iota> o D.cones_map (\<psi> (a', a) x) o \<o>"]
                by auto
              (* "also" loops here if I try that style *)
              moreover have "... = ?F x" using cone_\<chi> by simp
              ultimately show ?thesis by simp
            qed
          qed
        qed
        finally show "\<Phi> a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') ?F" by auto
      qed
    qed

  end

  sublocale representation_of_cones_functor \<subseteq> limit_situation J C D S \<phi> \<iota> a \<Phi> \<chi>
    using induces_limit_situation by auto

  section "Categories with Limits"

  context category
  begin

    text{*
      A category @{term C} has limits of shape @{term J} if every diagram of shape @{term J}
      admits a limit cone.
    *}

    definition has_limits_of_shape
    where "has_limits_of_shape J \<equiv> \<forall>D. diagram J C D \<longrightarrow> (\<exists>a \<chi>. limit_cone J C D a \<chi>)"

    text{*
      A category has limits at a type @{typ 'j} if it has limits of shape @{term J}
      for every category @{term J} whose arrows are of type @{typ 'j}.
    *}

    definition has_limits
    where "has_limits (_ :: 'j) \<equiv> \<forall>J :: 'j comp. category J \<longrightarrow> has_limits_of_shape J"

    lemma has_limits_preserved_by_isomorphism:
    assumes "has_limits_of_shape J" and "isomorphic_categories J J'"
    shows "has_limits_of_shape J'"
    proof -
      interpret J: category J
        using assms(2) isomorphic_categories_def isomorphic_categories_axioms_def by auto
      interpret J': category J'
        using assms(2) isomorphic_categories_def isomorphic_categories_axioms_def by auto
      from assms(2) obtain \<phi> \<psi> where IF: "inverse_functors J J' \<phi> \<psi>"
        using isomorphic_categories_def isomorphic_categories_axioms_def by blast
      interpret IF: inverse_functors J J' \<phi> \<psi> using IF by auto
      have \<psi>\<phi>: "\<psi> o \<phi> = J.map" using IF.inv by metis
      have \<phi>\<psi>: "\<phi> o \<psi> = J'.map" using IF.inv' by metis
      have "\<And>D'. diagram J' C D' \<Longrightarrow> \<exists>a \<chi>. limit_cone J' C D' a \<chi>"
      proof -
        fix D'
        assume D': "diagram J' C D'"
        interpret D': diagram J' C D' using D' by auto
        interpret D: composite_functor J J' C \<phi> D' ..
        interpret D: diagram J C "D' o \<phi>" ..
        have D: "diagram J C (D' o \<phi>)" ..
        from assms(1) obtain a \<chi> where \<chi>: "D.limit_cone a \<chi>"
          using D has_limits_of_shape_def by blast
        interpret \<chi>: limit_cone J C "D' o \<phi>" a \<chi> using \<chi> by auto
        interpret A': constant_functor J' C a
          apply unfold_locales using \<chi>.ide_apex by auto
        have \<chi>o\<psi>: "cone J' C (D' o \<phi> o \<psi>) a (\<chi> o \<psi>)"
          using comp_cone_functor IF.G.functor_axioms \<chi>.cone_axioms by fastforce
        hence \<chi>o\<psi>: "cone J' C D' a (\<chi> o \<psi>)"
          using \<phi>\<psi> by (metis D'.functor_axioms Fun.comp_assoc comp_ide_dom)
        interpret \<chi>o\<psi>: cone J' C D' a "\<chi> o \<psi>" using \<chi>o\<psi> by auto
        interpret \<chi>o\<psi>: limit_cone J' C D' a "\<chi> o \<psi>"
        proof
          fix a' \<chi>'
          assume \<chi>': "D'.cone a' \<chi>'"
          interpret \<chi>': cone J' C D' a' \<chi>' using \<chi>' by auto
          have \<chi>'o\<phi>: "cone J C (D' o \<phi>) a' (\<chi>' o \<phi>)"
            using \<chi>' comp_cone_functor IF.F.functor_axioms by fastforce
          interpret \<chi>'o\<phi>: cone J C "D' o \<phi>" a' "\<chi>' o \<phi>" using \<chi>'o\<phi> by auto
          have "cone J C (D' o \<phi>) a' (\<chi>' o \<phi>)" ..
          hence 1: "\<exists>!f. f \<in> hom a' a \<and> D.cones_map f \<chi> = \<chi>' o \<phi>"
            using \<chi>.is_universal by simp
          show "\<exists>!f. f \<in> hom a' a \<and> D'.cones_map f (\<chi> o \<psi>) = \<chi>'"
          proof
            let ?f = "THE f. f \<in> hom a' a \<and> D.cones_map f \<chi> = \<chi>' o \<phi>"
            have f: "?f \<in> hom a' a \<and> D.cones_map ?f \<chi> = \<chi>' o \<phi>"
              using 1 theI' [of "\<lambda>f. f \<in> hom a' a \<and> D.cones_map f \<chi> = \<chi>' o \<phi>"] by blast
            have "D'.cones_map ?f (\<chi> o \<psi>) = \<chi>'"
            proof
              fix j'
              have "\<not>J'.arr j' \<Longrightarrow> D'.cones_map ?f (\<chi> o \<psi>) j' = \<chi>' j'"
                using f \<chi>o\<psi> \<chi>'.is_extensional by simp
              moreover have "J'.arr j' \<Longrightarrow> D'.cones_map ?f (\<chi> o \<psi>) j' = \<chi>' j'"
              proof -
                assume j': "J'.arr j'"
                have "D'.cones_map ?f (\<chi> o \<psi>) j' = C ((\<chi> o \<psi>) j') ?f"
                  using j' f \<chi>o\<psi> by simp
                also have "... = C (\<chi> (\<psi> j')) ?f" by simp
                also have "... = D.cones_map ?f \<chi> (\<psi> j')"
                  using j' f \<chi> \<chi>.cone_\<chi> by auto
                also have "... = (\<chi>' o \<phi>) (\<psi> j')"
                  using j' f \<chi> by metis
                also have "... = \<chi>' j'"
                  using j' \<phi>\<psi> by (metis Fun.comp_def J'.map_simp)
                finally show "D'.cones_map ?f (\<chi> o \<psi>) j' = \<chi>' j'" by auto
              qed
              ultimately show "D'.cones_map ?f (\<chi> o \<psi>) j' = \<chi>' j'" by blast
            qed
            thus "?f \<in> hom a' a \<and> D'.cones_map ?f (\<chi> o \<psi>) = \<chi>'" using f by auto
            fix f'
            assume f': "f' \<in> hom a' a \<and> D'.cones_map f' (\<chi> o \<psi>) = \<chi>'"
            have "D.cones_map f' \<chi> = \<chi>' o \<phi>"
            proof
              fix j
              have "\<not>J.arr j \<Longrightarrow> D.cones_map f' \<chi> j = (\<chi>' o \<phi>) j"
                using f' \<chi> \<chi>'o\<phi>.is_extensional \<chi>.cone_\<chi> mem_Collect_eq restrict_apply by auto
              moreover have "J.arr j \<Longrightarrow> D.cones_map f' \<chi> j = (\<chi>' o \<phi>) j"
              proof -
                assume j: "J.arr j"
                have "D.cones_map f' \<chi> j = C (\<chi> j) f'"
                  using j f' \<chi>.cone_\<chi> by auto
                also have "... = C ((\<chi> o \<psi>) (\<phi> j)) f'"
                  using j f' \<psi>\<phi> by (metis comp_apply J.map_simp)
                also have "... = D'.cones_map f' (\<chi> o \<psi>) (\<phi> j)"
                  using j f' \<chi>o\<psi> by simp
                also have "... = (\<chi>' o \<phi>) j"
                  using j f' by auto
                finally show "D.cones_map f' \<chi> j = (\<chi>' o \<phi>) j" by auto
              qed
              ultimately show "D.cones_map f' \<chi> j = (\<chi>' o \<phi>) j" by blast
            qed
            hence "f' \<in> hom a' a \<and> D.cones_map f' \<chi> = \<chi>' o \<phi>"
              using f' by auto
            moreover have "\<And>P x x'. (\<exists>!x. P x) \<and> P x \<and> P x' \<Longrightarrow> x = x'"
              by auto
            ultimately show "f' = ?f" using 1 f by blast
          qed
        qed
        have "limit_cone J' C D' a (\<chi> o \<psi>)" ..
        thus "\<exists>a \<chi>. limit_cone J' C D' a \<chi>" by blast
      qed
      thus ?thesis using has_limits_of_shape_def by auto
    qed

  end

  subsection "Diagonal Functors"

  text{*
    The existence of limits can also be expressed in terms of adjunctions: a category @{term C}
    has limits of shape @{term J} if the diagonal functor taking each object @{term a}
    in @{term C} to the constant-@{term a} diagram and each arrow @{text "f \<in> C.hom a a'"}
    to the constant-@{term f} natural transformation between diagrams is a left adjoint functor.
  *}

  locale diagonal_functor =
    C: category C +
    J: category J +
    J_C: functor_category J C
  for J :: "'j comp"
  and C :: "'c comp"
  begin

    definition map :: "'c \<Rightarrow> ('j, 'c) J_C.arr"
    where "map f = (if C.arr f then J_C.mkArr (constant_functor.map J C (C.dom f))
                                              (constant_functor.map J C (C.cod f))
                                              (constant_transformation.map J C f)
                               else J_C.null)"

    lemma is_functor:
    shows "functor C J_C.comp map"
    proof
      fix f
      assume F: "\<not>C.arr f"
      show "map f = J_C.null" using F map_def by simp
      next
      fix f
      assume F: "C.arr f"
      interpret Dom_f: constant_functor J C "C.dom f"
        apply unfold_locales using F by auto
      interpret Cod_f: constant_functor J C "C.cod f"
        apply unfold_locales using F by auto
      interpret Fun_f: constant_transformation J C f
        apply unfold_locales using F by auto
      have "constant_transformation J C f" ..
      show 1: "J_C.arr (map f)"
        using F map_def by (simp add: Fun_f.natural_transformation_axioms)
      show "J_C.dom (map f) = map (C.dom f)"
      proof -
        have "constant_transformation J C (C.dom f)"
          apply unfold_locales using F by auto
        hence "constant_transformation.map J C (C.dom f) = Dom_f.map"
          using Dom_f.map_def constant_transformation.map_def [of J C "C.dom f"] by auto
        thus ?thesis using F 1 by (simp add: map_def J_C.dom_simp)
      qed
      show "J_C.cod (map f) = map (C.cod f)"
      proof -
        have "constant_transformation J C (C.cod f)"
          apply unfold_locales using F by auto
        hence "constant_transformation.map J C (C.cod f) = Cod_f.map"
          using Cod_f.map_def constant_transformation.map_def [of J C "C.cod f"] by auto
        thus ?thesis using F 1 by (simp add: map_def J_C.cod_simp)
      qed
      fix g
      assume G: "g \<in> C.hom (C.cod f) (C.cod g)"
      interpret Cod_g: constant_functor J C "C.cod g"
        apply unfold_locales using G by auto
      interpret Fun_g: constant_transformation J C g
        apply unfold_locales using F G by auto
      interpret Fun_g: natural_transformation J C Cod_f.map Cod_g.map Fun_g.map
        apply unfold_locales using F G by simp_all
      interpret Fun_fg: vertical_composite J C Dom_f.map Cod_f.map Cod_g.map Fun_f.map Fun_g.map ..
      show "map (C g f) = J_C.comp (map g) (map f)"
      proof -
        have 2: "C.arr (C g f)" using F G by force
        hence "map (C g f) = J_C.mkArr Dom_f.map Cod_g.map
                                       (constant_transformation.map J C (C g f))"
          using F G map_def [of "C g f"] by simp
        also have "... = J_C.mkArr Dom_f.map Cod_g.map (\<lambda>j. if J.arr j then C g f else C.null)"
        proof -
          have "constant_transformation J C (C g f)"
            apply unfold_locales using 2 by auto
          thus ?thesis using constant_transformation.map_def by metis
        qed
        also have "... = J_C.comp (J_C.mkArr Cod_f.map Cod_g.map Fun_g.map)
                                  (J_C.mkArr Dom_f.map Cod_f.map Fun_f.map)"
        proof -
          have "J_C.comp (J_C.mkArr Cod_f.map Cod_g.map Fun_g.map)
                         (J_C.mkArr Dom_f.map Cod_f.map Fun_f.map)
                  = J_C.mkArr Dom_f.map Cod_g.map Fun_fg.map"
            using J_C.comp_char [of "map f" "map g"] J_C.comp_mkArr
                  Fun_f.natural_transformation_axioms Fun_g.natural_transformation_axioms
            by blast
          also have "... = J_C.mkArr Dom_f.map Cod_g.map
                                     (\<lambda>j. if J.arr j then C g f else C.null)"
          proof -
            have "Fun_fg.map = (\<lambda>j. if J.arr j then C g f else C.null)"
              using 1 F G Fun_fg.map_def by auto
            thus ?thesis by auto
          qed
          finally show ?thesis by auto
        qed
        also have "... = J_C.comp (map g) (map f)"
          using F G map_def by fastforce
        finally show ?thesis by auto
      qed
    qed

  end

  sublocale diagonal_functor \<subseteq> "functor" C J_C.comp map
    using is_functor by auto

  context diagonal_functor
  begin

    text{*
      The objects of @{term J_C} correspond bijectively to diagrams of shape @{term J}
      in @{term C}.
    *}

    lemma ide_determines_diagram:
    assumes "J_C.ide d"
    shows "diagram J C (J_C.Fun d)" and "J_C.mkIde (J_C.Fun d) = d"
    proof -
      interpret \<delta>: natural_transformation J C "J_C.Fun d" "J_C.Fun d" "J_C.Fun d"
        using assms J_C.ide_char [of d] J_C.arr_mkArr [of "J_C.Fun d" "J_C.Fun d" "J_C.Fun d"]
              J_C.mkArr_def
        by fastforce
      interpret D: "functor" J C "J_C.Fun d" ..
      show "diagram J C (J_C.Fun d)" ..
      show "J_C.mkIde (J_C.Fun d) = d"
        using assms J_C.ide_char by (metis J_C.mkArr_Fun J_C.ideD(1))
    qed

    lemma diagram_determines_ide:
    assumes "diagram J C D"
    shows "J_C.ide (J_C.mkIde D)" and "J_C.Fun (J_C.mkIde D) = D"
    proof -
      interpret D: diagram J C D using assms by auto
      show "J_C.ide (J_C.mkIde D)" using J_C.ide_char
        by (metis D.functor_axioms J_C.Cod_mkArr J_C.Dom_mkArr J_C.Fun_mkArr J_C.arr_mkArr
                  J_C.not_arr_null functor_is_transformation)
      thus "J_C.Fun (J_C.mkIde D) = D"
        using J_C.Fun_mkArr J_C.ideD(1) by blast
    qed

    lemma bij_betw_ide_diagram:
    shows "bij_betw J_C.Fun (Collect J_C.ide) (Collect (diagram J C))"
    proof (intro bij_betwI)
      show "J_C.Fun \<in> Collect J_C.ide \<rightarrow> Collect (diagram J C)"
        using ide_determines_diagram by blast
      show "J_C.mkIde \<in> Collect (diagram J C) \<rightarrow> Collect J_C.ide"
        using diagram_determines_ide by blast
      show "\<And>d. d \<in> Collect J_C.ide \<Longrightarrow> J_C.mkIde (J_C.Fun d) = d"
        using ide_determines_diagram by blast
      show "\<And>D. D \<in> Collect (diagram J C) \<Longrightarrow> J_C.Fun (J_C.mkIde D) = D"
        using diagram_determines_ide by blast
    qed

    text{*
      Arrows from from the diagonal functor correspond bijectively to cones.
    *}

    lemma arrow_determines_cone:
    assumes "J_C.ide d" and "arrow_from_functor C J_C.comp map a d x"
    shows "cone J C (J_C.Fun d) a (J_C.Fun x)"
    and "J_C.mkArr (constant_functor.map J C a) (J_C.Fun d) (J_C.Fun x) = x"
    proof -
      interpret D: diagram J C "J_C.Fun d"
        using assms ide_determines_diagram by auto
      interpret x: arrow_from_functor C J_C.comp map a d x
        using assms by auto
      interpret A: constant_functor J C a
        apply unfold_locales using x.arrow by auto
      interpret \<alpha>: constant_transformation J C a
        apply unfold_locales using x.arrow by auto
      have Dom_x: "J_C.Dom x = A.map"
      proof -
        have "J_C.dom x = map a" using x.arrow by blast
        hence "J_C.Fun (J_C.dom x) = J_C.Fun (map a)" by simp
        hence "J_C.Dom x = J_C.Fun (map a)" using x.arrow J_C.Fun_dom by fastforce
        moreover have "J_C.Fun (map a) = \<alpha>.map"
          using A.value_is_ide preserves_ide [of a] map_def [of a] J_C.Fun_mkArr
          by (metis J_C.arr_char J_C.ideD(1))
        ultimately show ?thesis using \<alpha>.map_def A.map_def by presburger
      qed
      have Cod_x: "J_C.Cod x = J_C.Fun d"
        using x.arrow J_C.cod_char by fastforce
      interpret \<chi>: natural_transformation J C A.map "J_C.Fun d" "J_C.Fun x"
        using x.arrow J_C.arr_char [of x] Dom_x Cod_x by force
      show "D.cone a (J_C.Fun x)" ..
      show "J_C.mkArr A.map (J_C.Fun d) (J_C.Fun x) = x"
        using x.arrow Dom_x Cod_x \<chi>.natural_transformation_axioms
        apply (intro J_C.arr_eqI)
        by auto        
    qed

    lemma cone_determines_arrow:
    assumes "J_C.ide d" and "cone J C (J_C.Fun d) a \<chi>"
    shows "arrow_from_functor C J_C.comp map a d
             (J_C.mkArr (constant_functor.map J C a) (J_C.Fun d) \<chi>)"
    and "J_C.Fun (J_C.mkArr (constant_functor.map J C a) (J_C.Fun d) \<chi>) = \<chi>"
    proof -
       interpret \<chi>: cone J C "J_C.Fun d" a \<chi> using assms(2) by auto
       let ?x = "J_C.mkArr \<chi>.A.map (J_C.Fun d) \<chi>"
       interpret x: arrow_from_functor C J_C.comp map a d ?x
         apply unfold_locales
         using \<chi>.A.value_is_ide map_def [of a] C.ideD(1) C.ideD(2) J_C.Dom_mkArr J_C.dom_char
               preserves_arr preserves_dom assms(1) ide_determines_diagram(2)
               J_C.mkArr_in_hom [of "\<chi>.A.map" "J_C.Fun d" \<chi>] \<chi>.natural_transformation_axioms
         by (metis (no_types, lifting) mem_Collect_eq)
       show "arrow_from_functor C J_C.comp map a d ?x" ..
       show "J_C.Fun (J_C.mkArr (constant_functor.map J C a) (J_C.Fun d) \<chi>) = \<chi>"
         by (simp add: \<chi>.natural_transformation_axioms)
    qed

    text{*
      Transforming a cone by composing at the apex with an arrow @{term g} corresponds,
      via the preceding bijections, to composition in @{term J_C} with the image of @{term g}
      under the diagonal functor.
    *}

    lemma cones_map_is_composition:
    assumes "g \<in> C.hom a' a" and "cone J C D a \<chi>"
    shows "J_C.mkArr (constant_functor.map J C a') D (diagram.cones_map J C D g \<chi>)
             = J_C.comp (J_C.mkArr (constant_functor.map J C a) D \<chi>) (map g)"
    proof -
      interpret A: constant_transformation J C a
        apply unfold_locales using assms(1) by auto
      interpret \<chi>: cone J C D a \<chi> using assms(2) by auto
      have cone_\<chi>: "cone J C D a \<chi>" ..
      interpret A': constant_transformation J C a'
        apply unfold_locales using assms(1) by auto
      let ?\<chi>' = "\<chi>.D.cones_map g \<chi>"
      interpret \<chi>': cone J C D a' ?\<chi>'
        using cone_\<chi> assms(1) \<chi>.D.cones_map_mapsto by blast
      let ?x = "J_C.mkArr \<chi>.A.map D \<chi>"
      let ?x' = "J_C.mkArr \<chi>'.A.map D ?\<chi>'"
      show "?x' = J_C.comp ?x (map g)"
      proof (intro J_C.arr_eqI)
        have x: "J_C.arr ?x"
          using \<chi>.natural_transformation_axioms J_C.arr_char [of ?x] by simp
        show x': "J_C.arr ?x'"
          using \<chi>'.natural_transformation_axioms J_C.arr_char [of ?x'] by simp
        have 3: "?x \<in> J_C.hom (map a) (J_C.mkIde D)"
        proof -
          have 1: "map a = J_C.mkIde A.map"
            using \<chi>.ide_apex A.equals_dom_if_value_is_ide A.equals_cod_if_value_is_ide
                  map_def [of a]
            by auto
          have "J_C.arr ?x" using x by blast
          moreover have "J_C.dom ?x = map a"
            using x J_C.dom_simp 1 x \<chi>.ide_apex A.equals_dom_if_value_is_ide \<chi>.D.functor_axioms
                    J_C.ide_char
            by auto
          moreover have "J_C.cod ?x = J_C.mkIde D" using x J_C.cod_simp by auto
          ultimately show ?thesis by fast
        qed
        have 4: "?x' \<in> J_C.hom (map a') (J_C.mkIde D)"
        proof -
          have 1: "map a' = J_C.mkIde A'.map"
            using \<chi>'.ide_apex A'.equals_dom_if_value_is_ide A'.equals_cod_if_value_is_ide
                  map_def [of a']
            by auto
          have "J_C.arr ?x'" using x' by blast
          moreover have "J_C.dom ?x' = map a'"
            using x' J_C.dom_simp 1 x' \<chi>'.ide_apex A'.equals_dom_if_value_is_ide \<chi>.D.functor_axioms
                    J_C.ide_char
            by simp
          moreover have "J_C.cod ?x' = J_C.mkIde D" using x' J_C.cod_simp by auto
          ultimately show ?thesis by fast
        qed
        have seq_xg: "J_C.seq ?x (map g)"
          using assms(1) 3 preserves_hom [of g] by auto
        show 2: "J_C.arr (J_C.comp ?x (map g))"
          using seq_xg J_C.arr_comp by blast
        show "J_C.Dom ?x' = J_C.Dom (J_C.comp ?x (map g))"
        proof -
          have "J_C.Dom ?x' = J_C.Dom (J_C.dom ?x')"
            using x' J_C.Dom_dom by presburger
          also have "... = J_C.Dom (map a')"
            using 4 by force
          also have "... = J_C.Dom (J_C.dom (J_C.comp ?x (map g)))"
            using assms(1) seq_xg J_C.dom_comp [of "map g" ?x] by simp
          also have "... = J_C.Dom (J_C.comp ?x (map g))"
            using seq_xg J_C.Dom_dom [of "J_C.comp ?x (map g)"] J_C.arr_comp by blast
          finally show ?thesis by auto
        qed
        show "J_C.Cod ?x' = J_C.Cod (J_C.comp ?x (map g))"
        proof -
          have "J_C.Cod ?x' = J_C.Cod (J_C.cod ?x')"
            using x' J_C.Cod_cod by presburger
          also have "... = J_C.Cod (J_C.mkIde D)"
            using 4 by force
          also have "... = J_C.Cod (J_C.cod (J_C.comp ?x (map g)))"
            using seq_xg J_C.cod_comp [of "map g" ?x] 3 by fastforce
          also have "... = J_C.Cod (J_C.comp ?x (map g))"
            using seq_xg J_C.Cod_cod [of "J_C.comp ?x (map g)"] J_C.arr_comp by blast
          finally show ?thesis by auto
        qed
        show "J_C.Fun ?x' = J_C.Fun (J_C.comp ?x (map g))"
        proof -
          interpret g: constant_transformation J C g
            apply unfold_locales using assms(1) by auto
          interpret \<chi>og: vertical_composite J C A'.map \<chi>.A.map D g.map \<chi>
            using assms(1)
            apply unfold_locales by auto
          have "J_C.Fun (J_C.comp ?x (map g)) = \<chi>og.map"
            using 2 J_C.comp_char [of ?x "map g"]
            by (metis J_C.Fun_mkArr J_C.arr_char diagonal_functor.map_def diagonal_functor_axioms)
          also have "... = J_C.Fun ?x'"
            using x' \<chi>og.map_def J_C.arr_char [of ?x'] natural_transformation.is_extensional
                  assms(1) cone_\<chi> \<chi>og.map_simp_2
            by fastforce
          finally show ?thesis by auto
        qed
      qed
    qed

    text{*
      Coextension along an arrow from a functor is equivalent to a transformation of cones.
    *}

    lemma coextension_iff_cones_map:
    assumes x: "arrow_from_functor C J_C.comp map a d x"
    and g: "g \<in> C.hom a' a"
    and x': "x' \<in> J_C.hom (map a') d"
    shows "arrow_from_functor.is_coext C J_C.comp map a x a' x' g
              \<longleftrightarrow> J_C.Fun x' = diagram.cones_map J C (J_C.Fun d) g (J_C.Fun x)"
    proof -
      interpret x: arrow_from_functor C J_C.comp map a d x
        using assms by auto
      interpret A': constant_functor J C a'
        apply unfold_locales using assms(2) by auto
      have x': "arrow_from_functor C J_C.comp map a' d x'"
        apply unfold_locales using A'.value_is_ide assms(3) by blast
      have d: "J_C.ide d" using J_C.ide_cod x.arrow by blast
      let ?D = "J_C.Fun d"
      let ?\<chi> = "J_C.Fun x"
      let ?\<chi>' = "J_C.Fun x'"
      interpret D: diagram J C ?D
        using ide_determines_diagram J_C.ide_cod x.arrow by blast
      interpret \<chi>: cone J C ?D a ?\<chi>
        using assms(1) d arrow_determines_cone by simp
      interpret \<gamma>: constant_transformation J C g
        apply unfold_locales using g \<chi>.ide_apex by auto
      interpret \<chi>og: vertical_composite J C A'.map \<chi>.A.map ?D \<gamma>.map ?\<chi>
        apply unfold_locales
        using g by auto
      show ?thesis
      proof
        assume 0: "x.is_coext a' x' g"
        show "?\<chi>' = D.cones_map g ?\<chi>"
        proof -
          have 1: "x' = J_C.comp x (map g)"
            using 0 x.is_coext_def by blast
          hence "?\<chi>' = J_C.Fun x'"
            using 0 x.is_coext_def [of a' x' g] by fast
          moreover have "... = D.cones_map g ?\<chi>"
          proof -
            have "J_C.mkArr A'.map (J_C.Fun d) (D.cones_map g (J_C.Fun x)) = J_C.comp x (map g)"
              using d g cones_map_is_composition [of g a' a ?D ?\<chi>]
                    arrow_determines_cone(2) \<chi>.cone_axioms x.arrow_from_functor_axioms
              by presburger
            hence f1: "J_C.mkArr A'.map (J_C.Fun d) (D.cones_map g (J_C.Fun x)) = x'"
              by (metis 1)
            have "J_C.arr (J_C.mkArr A'.map (J_C.Fun d) (D.cones_map g (J_C.Fun x)))"
              using 1 d g cones_map_is_composition [of g a' a ?D ?\<chi>] preserves_arr
                    arrow_determines_cone(2) \<chi>.cone_axioms x.arrow_from_functor_axioms
              using assms(3) mem_Collect_eq by auto
            thus ?thesis
              using f1 J_C.Fun_mkArr by blast
          qed
          ultimately show ?thesis by blast
        qed
        next
        assume X': "?\<chi>' = D.cones_map g ?\<chi>"
        show "x.is_coext a' x' g"
        proof -
          have 4: "J_C.seq x (map g)"
            using g x.arrow mem_Collect_eq preserves_arr preserves_cod by auto
          hence 1: "J_C.comp x (map g) =
                   J_C.mkArr (J_C.Dom (map g)) (J_C.Cod x)
                             (vertical_composite.map J C (J_C.Fun (map g)) ?\<chi>)"
            using J_C.comp_char [of x "map g"] by simp
          have 2: "vertical_composite.map J C (J_C.Fun (map g)) ?\<chi> = \<chi>og.map"
            by (simp add: map_def \<gamma>.value_is_arr \<gamma>.natural_transformation_axioms)
          have 3: "... = D.cones_map g ?\<chi>"
            using g \<chi>og.map_simp_2 \<chi>.cone_axioms by auto
          have "J_C.mkArr A'.map ?D ?\<chi>' = J_C.comp x (map g)"
          proof -
            have f1: "A'.map = J_C.Dom (map g)"
              using \<gamma>.natural_transformation_axioms map_def g by auto
            have "J_C.Fun d = J_C.Cod x"
              by (metis J_C.Cod_mkArr J_C.arr_mkArr \<chi>.natural_transformation_axioms
                        arrow_determines_cone(2) d x.arrow_from_functor_axioms)
            thus ?thesis using f1 X' 1 2 3 by presburger
          qed
          moreover have "J_C.mkArr A'.map ?D ?\<chi>' = x'"
            using d x' arrow_determines_cone [of d a' x'] by blast
          ultimately show ?thesis using g x.is_coext_def [of a' x' g]
            by simp
        qed
      qed
    qed

  end

  locale right_adjoint_to_diagonal_functor =
    C: category C +
    J: category J +
    J_C: functor_category J C +
    \<Delta>: diagonal_functor J C +
    "functor" J_C.comp C G +
    Adj: meta_adjunction J_C.comp C \<Delta>.map G \<phi> \<psi>
  for J :: "'j comp"
  and C :: "'c comp"
  and G :: "('j, 'c) functor_category.arr \<Rightarrow> 'c"
  and \<phi> :: "'c \<Rightarrow> ('j, 'c) functor_category.arr \<Rightarrow> 'c"
  and \<psi> :: "('j, 'c) functor_category.arr \<Rightarrow> 'c \<Rightarrow> ('j, 'c) functor_category.arr" +
  assumes adjoint: "adjoint_functors J_C.comp C \<Delta>.map G"
  begin

    text{*
      A right adjoint @{term G} to a diagonal functor maps each object @{term d} of @{term J_C}
     (corresponding to a diagram @{term D} of shape @{term J} in @{term C} to an object
     of @{term C}.  This object is the limit object, and the component at @{term d}
     of the counit of the adjunction determines the limit cone.
    *}

    lemma gives_limit_cones:
    assumes "diagram J C D"
    shows "limit_cone J C D (G (J_C.mkIde D)) (J_C.Fun (Adj.\<epsilon> (J_C.mkIde D)))"
    proof -
      interpret D: diagram J C D using assms by auto
      let ?d = "J_C.mkIde D"
      let ?a = "G ?d"
      let ?x = "Adj.\<epsilon> ?d"
      let ?\<chi> = "J_C.Fun ?x"
      have "diagram J C D" ..
      hence 1: "J_C.ide ?d" using \<Delta>.diagram_determines_ide [of D] by auto
      hence 2: "J_C.Fun (J_C.mkIde D) = D"
        using "1" J_C.Fun_mkArr J_C.ideD(1) by blast
      interpret x: terminal_arrow_from_functor C J_C.comp \<Delta>.map ?a ?d ?x
        apply unfold_locales
        (* 2 *) apply (metis (no_types, lifting) "1" preserves_ide Adj.\<epsilon>_in_terms_of_\<psi>
                       Adj.\<epsilon>o_def Adj.\<epsilon>o_mapsto mem_Collect_eq)
        (* 1 *) by (metis 1 Adj.has_terminal_arrows_from_functor(1)
                          terminal_arrow_from_functor.is_terminal)
      have 3: "arrow_from_functor C J_C.comp \<Delta>.map ?a ?d ?x" ..
      interpret \<chi>: cone J C D ?a ?\<chi>
        using 1 2 3 \<Delta>.arrow_determines_cone [of ?d] by auto
      have cone_\<chi>: "D.cone ?a ?\<chi>" ..
      interpret \<chi>: limit_cone J C D ?a ?\<chi>
      proof
        fix a' \<chi>'
        assume cone_\<chi>': "D.cone a' \<chi>'"
        interpret \<chi>': cone J C D a' \<chi>' using cone_\<chi>' by auto
        let ?x' = "J_C.mkArr \<chi>'.A.map D \<chi>'"
        interpret x': arrow_from_functor C J_C.comp \<Delta>.map a' ?d ?x'
          using 1 2 by (metis \<Delta>.cone_determines_arrow(1) cone_\<chi>')
        have "arrow_from_functor  C J_C.comp \<Delta>.map a' ?d ?x'" ..
        hence "\<exists>!g. x.is_coext a' ?x' g"
          using x.is_terminal by simp
        moreover have "\<And>g. g \<in> C.hom a' ?a \<Longrightarrow> x.is_coext a' ?x' g \<longleftrightarrow> D.cones_map g ?\<chi> = \<chi>'"
        proof -
          fix g
          assume G: "g \<in> C.hom a' ?a"
          show "x.is_coext a' ?x' g \<longleftrightarrow> D.cones_map g ?\<chi> = \<chi>'"
          proof -
            have "?x' \<in> J_C.hom (\<Delta>.map a') ?d"
            using x'.arrow by simp
            thus ?thesis
              using 3 G \<Delta>.coextension_iff_cones_map [of ?a ?d ?x g a' ?x']
              by (metis (no_types, lifting) "1" "2" \<Delta>.cone_determines_arrow(2) cone_\<chi>')
          qed
        qed
        moreover have "\<And>g. x.is_coext a' ?x' g \<Longrightarrow> g \<in> C.hom a' ?a"
          using x.is_coext_def by simp
        ultimately show "\<exists>!g. g \<in> C.hom a' ?a \<and> D.cones_map g ?\<chi> = \<chi>'"
          by blast
      qed
      show "D.limit_cone ?a ?\<chi>" ..
    qed

    corollary gives_limits:
    assumes "diagram J C D"
    shows "diagram.has_as_limit J C D (G (J_C.mkIde D))"
      using assms gives_limit_cones by fastforce

  end

  lemma (in category) has_limits_iff_left_adjoint_diagonal:
  assumes "category J"
  shows "has_limits_of_shape J \<longleftrightarrow>
           left_adjoint_functor C (functor_category.comp J C) (diagonal_functor.map J C)"
  proof -
    interpret J: category J using assms by auto
    interpret J_C: functor_category J C ..
    interpret \<Delta>: diagonal_functor J C ..
    show ?thesis
    proof
      assume A: "left_adjoint_functor C J_C.comp \<Delta>.map"
      interpret \<Delta>: left_adjoint_functor C J_C.comp \<Delta>.map using A by auto
      interpret Adj: meta_adjunction J_C.comp C \<Delta>.map \<Delta>.G \<Delta>.\<phi> \<Delta>.\<psi>
        using \<Delta>.induces_meta_adjunction by auto
      have "meta_adjunction J_C.comp C \<Delta>.map \<Delta>.G \<Delta>.\<phi> \<Delta>.\<psi>" ..
      hence 1: "adjoint_functors J_C.comp C \<Delta>.map \<Delta>.G"
        using adjoint_functors_def by blast
      interpret G: right_adjoint_to_diagonal_functor J C \<Delta>.G \<Delta>.\<phi> \<Delta>.\<psi>
        apply unfold_locales using 1 by auto
      have "\<And>D. diagram J C D \<Longrightarrow> \<exists>a. diagram.has_as_limit J C D a"
        using A G.gives_limits by blast
      hence "\<And>D. diagram J C D \<Longrightarrow> \<exists>a \<chi>. limit_cone J C D a \<chi>"
        by metis
      thus "has_limits_of_shape J" using has_limits_of_shape_def by blast
      next
      text{*
        If @{term "has_limits J"}, then every diagram @{term D} from @{term J} to @{term C}
        has a limit cone.  This means that, for every object @{term d} of the functor category
        @{term J_C}, there exists an object @{term a} of @{term C} and a terminal arrow from
        @{text "\<Delta> a"} to @{term d} in @{term J_C}.  The terminal arrow is given by the limit cone.
      *}
      assume A: "has_limits_of_shape J"
      show "left_adjoint_functor C J_C.comp \<Delta>.map"
      proof
        fix d
        assume D: "J_C.ide d"
        interpret D: diagram J C "J_C.Fun d"
          using D \<Delta>.ide_determines_diagram by auto
        let ?D = "J_C.Fun d"
        have "diagram J C (J_C.Fun d)" ..
        from this obtain a \<chi> where limit: "limit_cone J C ?D a \<chi>"
          using A has_limits_of_shape_def by blast
        interpret \<chi>: limit_cone J C ?D a \<chi> using limit by auto
        have cone_\<chi>: "cone J C ?D a \<chi>" ..
        let ?x = "J_C.mkArr \<chi>.A.map ?D \<chi>"
        interpret x: arrow_from_functor C J_C.comp \<Delta>.map a d ?x
          using D cone_\<chi> \<Delta>.cone_determines_arrow by auto
        have "terminal_arrow_from_functor C J_C.comp \<Delta>.map a d ?x"
        proof
          show "\<And>a' x'. arrow_from_functor C J_C.comp \<Delta>.map a' d x' \<Longrightarrow> \<exists>!g. x.is_coext a' x' g"
          proof
            fix a' x'
            assume x': "arrow_from_functor C J_C.comp \<Delta>.map a' d x'"
            interpret x': arrow_from_functor C J_C.comp \<Delta>.map a' d x' using x' by auto
            interpret A': constant_functor J C a'
              apply unfold_locales by (simp add: x'.arrow)
            let ?\<chi>' = "J_C.Fun x'"
            interpret \<chi>': cone J C ?D a' ?\<chi>'
              using D x' \<Delta>.arrow_determines_cone [of d a' x'] by auto
            have cone_\<chi>': "cone J C ?D a' ?\<chi>'" ..
            let ?g = "\<chi>.induced_arrow a' ?\<chi>'"
            show "x.is_coext a' x' ?g"
            proof (unfold x.is_coext_def)
              have 1: "?g \<in> hom a' a \<and> D.cones_map ?g \<chi> = ?\<chi>'"
                using \<chi>.induced_arrow_def [of a' ?\<chi>']
                      \<chi>.is_universal [of a' "J_C.Fun x'"] cone_\<chi>'
                      theI' [of "\<lambda>f. f \<in> hom a' a \<and> D.cones_map f \<chi> = ?\<chi>'"]
                by presburger
              hence 2: "x' = J_C.comp ?x (\<Delta>.map ?g)"
              proof -
                have "x' = J_C.mkArr A'.map ?D ?\<chi>'"
                  using D \<Delta>.arrow_determines_cone(2) x'.arrow_from_functor_axioms by auto
                thus ?thesis
                  using 1 cone_\<chi> \<Delta>.cones_map_is_composition [of ?g a' a ?D \<chi>] by auto
              qed
              show "?g \<in> hom a' a \<and> x' = J_C.comp ?x (\<Delta>.map ?g)"
                using 1 2 by auto
            qed
            next
            fix a' x' g
            assume A: "arrow_from_functor C J_C.comp \<Delta>.map a' d x'"
            and X: "x.is_coext a' x' g"
            let ?\<chi>' = "J_C.Fun x'"
            interpret \<chi>': cone J C "J_C.Fun d" a' ?\<chi>' 
              using D A \<Delta>.arrow_determines_cone by auto
            have cone_\<chi>': "cone J C (J_C.Fun d) a' ?\<chi>'" ..
            let ?g = "\<chi>.induced_arrow a' ?\<chi>'"
            show "g = ?g"
            proof -
              have "g \<in> hom a' a \<and> D.cones_map g \<chi> = ?\<chi>'"
              proof
                show G: "g \<in> hom a' a" using X x.is_coext_def by blast
                show "D.cones_map g \<chi> = ?\<chi>'"
                proof -
                  have 1: "x' = J_C.comp ?x (\<Delta>.map g)"
                    using X x.is_coext_def by blast
                  hence "?\<chi>' = J_C.Fun (J_C.comp ?x (\<Delta>.map g))"
                    using X x.is_coext_def [of a' x' g] by fast
                  also have "... = D.cones_map g \<chi>"
                    using 1 G cone_\<chi> \<Delta>.cones_map_is_composition [of g a' a ?D \<chi>]
                    by (metis (no_types, lifting) A D J_C.Fun_mkArr J_C.arr_mkArr
                        \<Delta>.arrow_determines_cone(2) \<chi>'.natural_transformation_axioms)  
                  finally show ?thesis by auto
                qed
              qed
              thus ?thesis
                using cone_\<chi>' \<chi>.is_universal [of a' ?\<chi>'] \<chi>.induced_arrow_def [of a' ?\<chi>']
                      theI_unique [of "\<lambda>g. g \<in> hom a' a \<and> D.cones_map g \<chi> = ?\<chi>'" g]
                by presburger
            qed
          qed
        qed
        thus "\<exists>a x. terminal_arrow_from_functor C J_C.comp \<Delta>.map a d x" by auto
      qed
    qed
  qed

  section "Right Adjoint Functors Preserve Limits"

  context right_adjoint_functor
  begin

    lemma preserves_limits:
    fixes J :: "'j comp"
    assumes "diagram J C E" and "diagram.has_as_limit J C E a"
    shows "diagram.has_as_limit J D (G o E) (G a)"
    proof -
      text{*
        From the assumption that @{term E} has a limit, obtain a limit cone @{term \<chi>}.
      *}
      interpret J: category J using assms(1) diagram_def by auto
      interpret E: diagram J C E using assms(1) by auto
      from assms(2) obtain \<chi> where \<chi>: "limit_cone J C E a \<chi>" by auto
      interpret \<chi>: limit_cone J C E a \<chi> using \<chi> by auto
      have a: "C.ide a" using \<chi>.ide_apex by auto
      text{*
        Form the @{term E}-image @{text GE} of the diagram @{term E}.
      *}
      interpret GE: composite_functor J C D E G ..
      interpret GE: diagram J D GE.map ..
      text{* Let @{text G\<chi>} be the @{term G}-image of the cone @{term \<chi>},
             and note that it is a cone over @{text GE}. *}
      let ?G\<chi> = "G o \<chi>"
      interpret G\<chi>: cone J D GE.map "G a" ?G\<chi>
      proof -
        have "E.cone a \<chi>" ..
        thus "cone J D GE.map (G a) ?G\<chi>" using preserves_cones by blast
      qed
      text{*
        Claim that @{text G\<chi>} is a limit cone for diagram @{text GE}.
      *}
      interpret G\<chi>: limit_cone J D GE.map "G a" ?G\<chi>
      proof
        text {*
          Let @{term \<kappa>} be an arbitrary cone over @{text GE}.
        *}
        fix b \<kappa>
        assume \<kappa>: "GE.cone b \<kappa>"
        interpret \<kappa>: cone J D GE.map b \<kappa> using \<kappa> by auto
        interpret Fb: constant_functor J C "F b"
          apply unfold_locales
          by (meson F_is_functor \<kappa>.ide_apex functor.preserves_ide)
        interpret Adj: meta_adjunction C D F G \<phi> \<psi>
          using induces_meta_adjunction by auto
        text{*
          For each arrow @{term j} of @{term J}, let @{term "\<chi>' j"} be defined to be
          the adjunct of @{term "\<chi> j"}.  We claim that @{term \<chi>'} is a cone over @{term E}.
        *}
        let ?\<chi>' = "\<lambda>j. if J.arr j then C (Adj.\<epsilon> (C.cod (E j))) (F (\<kappa> j)) else C.null"
        have cone_\<chi>': "E.cone (F b) ?\<chi>'"
        proof
          show "\<And>j. \<not>J.arr j \<Longrightarrow> ?\<chi>' j = C.null" by simp
          fix j
          assume j: "J.arr j"
          show "C.dom (?\<chi>' j) = Fb.map (J.dom j)" using j \<psi>_mapsto by simp
          show "C.cod (?\<chi>' j) = E (J.cod j)" using j \<psi>_mapsto by simp
          show "C (E j) (?\<chi>' (J.dom j)) = ?\<chi>' j"
          proof -
            have "C (E j) (?\<chi>' (J.dom j)) = C (C (E j) (Adj.\<epsilon> (E (J.dom j)))) (F (\<kappa> (J.dom j)))"
              using j by simp
            also have "... = C (Adj.\<epsilon> (E (J.cod j))) (F (\<kappa> j))"
            proof -
              have "C (C (E j) (Adj.\<epsilon> (E (J.dom j)))) (F (\<kappa> (J.dom j)))
                       = C (C (Adj.\<epsilon> (C.cod (E j))) (Adj.FG.map (E j))) (F (\<kappa> (J.dom j)))"
                using j Adj.\<epsilon>.is_natural_1 [of "E j"] Adj.\<epsilon>.is_natural_2 [of "E j"]
                by fastforce
              also have "... = C (Adj.\<epsilon> (C.cod (E j))) (C (Adj.FG.map (E j)) (F (\<kappa> (J.dom j))))"
                using j by simp
              also have "... = C (Adj.\<epsilon> (E (J.cod j))) (F (\<kappa> j))"
              proof -
                have "C (Adj.FG.map (E j)) (F (\<kappa> (J.dom j))) = F (D (GE.map j) (\<kappa> (J.dom j)))"
                  using j by simp
                hence "C (Adj.FG.map (E j)) (F (\<kappa> (J.dom j))) = F (\<kappa> j)"
                  using j \<kappa>.is_natural_1 [of j] by metis
                thus ?thesis using j by simp
              qed
              finally show ?thesis by auto
            qed
            also have "... = ?\<chi>' j"
              using j by simp
            finally show ?thesis by auto
          qed
          show "C (?\<chi>' (J.cod j)) (Fb.map j) = ?\<chi>' j"
          proof -
            have "C (?\<chi>' (J.cod j)) (Fb.map j) = C (Adj.\<epsilon> (E (J.cod j))) (F (\<kappa> (J.cod j)))"
              using j Fb.value_is_ide by simp
            also have "... = C (Adj.\<epsilon> (E (J.cod j))) (F (\<kappa> j))"
              using j \<kappa>.is_natural_1 [of j] \<kappa>.is_natural_2 [of j]
                    Adj.\<epsilon>.is_natural_1 [of "E j"] Adj.\<epsilon>.is_natural_2 [of "E j"]
              by (metis J.arr_cod_iff_arr J.cod_cod \<kappa>.A.map_simp \<kappa>.is_natural_2)
            also have "... = ?\<chi>' j" using j by simp
            finally show ?thesis by auto
          qed
        qed
        text{*
          Using the universal property of the limit cone @{term \<chi>}, obtain the unique arrow
          @{term f} that transforms @{term \<chi>} into @{term \<chi>'}.
        *}
        from this \<chi>.is_universal [of "F b" ?\<chi>'] obtain f
          where f: "f \<in> C.hom (F b) a \<and> E.cones_map f \<chi> = ?\<chi>'"
          by auto
        text{*
          Let @{term g} be the adjunct of @{term f}, and show that @{term g} transforms
          @{term G\<chi>} into @{term \<kappa>}.
        *}
        let ?g = "D (G f) (Adj.\<eta> b)"
        have 1: "?g \<in> D.hom b (G a)" using f \<kappa>.ide_apex by auto
        moreover have "GE.cones_map ?g ?G\<chi> = \<kappa>"
        proof
          fix j
          have "\<not>J.arr j \<Longrightarrow> GE.cones_map ?g ?G\<chi> j = \<kappa> j"
            using 1 G\<chi>.cone_axioms by auto
          moreover have "J.arr j \<Longrightarrow> GE.cones_map ?g ?G\<chi> j = \<kappa> j"
          proof -
            fix j
            assume j: "J.arr j"
            have "GE.cones_map ?g ?G\<chi> j = D (G (\<chi> j)) ?g"
              using j 1 G\<chi>.cone_axioms mem_Collect_eq restrict_apply by auto
            moreover have "... = D (G (C (\<chi> j) f)) (Adj.\<eta> b)"
              using j f \<kappa>.ide_apex Fb.value_is_ide Adj.\<eta>.preserves_hom by auto
            moreover have "... = D (G ((E.cones_map f \<chi>) j)) (Adj.\<eta> b)"
              using j f \<chi>.cone_\<chi> mem_Collect_eq restrict_apply by auto
            moreover have "... = D (G (?\<chi>' j)) (Adj.\<eta> b)"
              using j f by presburger
            moreover have "... = D (D (G (Adj.\<epsilon> (C.cod (E j)))) (G (F (\<kappa> j)))) (Adj.\<eta> b)"
              using j f by simp
            moreover have "... = D (G (Adj.\<epsilon> (C.cod (E j)))) (D (G (F (\<kappa> j))) (Adj.\<eta> b))"
              using j by (metis D.comp_assoc' D.comp_null(1) D.comp_null(2) D.match_1 D.match_2)
            moreover have "... = D (G (Adj.\<epsilon> (C.cod (E j)))) (D (Adj.\<eta> (D.cod (GE.map j))) (\<kappa> j))"
              using j Adj.\<eta>.is_natural_1 [of "\<kappa> j"] Adj.\<eta>.is_natural_2 [of "\<kappa> j"] by simp
            moreover have "... = D (D (G (Adj.\<epsilon> (C.cod (E j)))) (Adj.\<eta> (D.cod (GE.map j)))) (\<kappa> j)"
              using j by simp
            moreover have "... = D (D.cod (\<kappa> j)) (\<kappa> j)"
            proof -
              have "D (G (Adj.\<epsilon> (C.cod (E j)))) (Adj.\<eta> (D.cod (GE.map j))) = D.cod (\<kappa> j)"
                using j Adj.\<eta>\<epsilon>.triangle_G Adj.G\<epsilon>o\<eta>G.map_simp_1
                        Adj.G\<epsilon>o\<eta>G.vertical_composite_axioms Adj.\<epsilon>_in_terms_of_\<psi> Adj.\<epsilon>o_def
                        Adj.\<eta>_in_terms_of_\<phi> Adj.\<eta>o_def Adj.unit_counit_G E.preserves_arr
                        GE.preserves_arr \<kappa>.preserves_cod GE.preserves_cod 
                        category.ide_cod o_apply preserves_cod vertical_composite_def
                by force
              thus ?thesis by simp
            qed
            moreover have "... = \<kappa> j"
              using j by simp
            ultimately show "GE.cones_map ?g ?G\<chi> j = \<kappa> j" by metis
          qed
          ultimately show "GE.cones_map ?g ?G\<chi> j = \<kappa> j" by auto
        qed
        ultimately have "?g \<in> D.hom b (G a) \<and> GE.cones_map ?g ?G\<chi> = \<kappa>" by auto
        text{*
          It remains to be shown that @{term g} is the unique such arrow.
          Given any @{term g'} that transforms @{term G\<chi>} into @{term \<kappa>},
          its adjunct transforms @{term \<chi>} into @{term \<chi>'}.
          The adjunct of @{term g'} is therefore equal to @{term f},
          which implies @{term g'} = @{term g}.
        *}
        moreover have "\<And>g'. g' \<in> D.hom b (G a) \<and> GE.cones_map g' ?G\<chi> = \<kappa> \<Longrightarrow> g' = ?g"
        proof -
          fix g'
          assume G': "g' \<in> D.hom b (G a) \<and> GE.cones_map g' ?G\<chi> = \<kappa>"
          have 1: "\<psi> a g' \<in> C.hom (F b) a"
            using G' a \<psi>_mapsto [of a g' b] by simp
          have 2: "E.cones_map (\<psi> a g') \<chi> = ?\<chi>'"
          proof
            fix j
            have "\<not>J.arr j \<Longrightarrow> E.cones_map (\<psi> a g') \<chi> j = ?\<chi>' j"
              using 1 \<chi>.cone_axioms by simp
            moreover have "J.arr j \<Longrightarrow> E.cones_map (\<psi> a g') \<chi> j = ?\<chi>' j"
            proof -
              fix j
              assume j: "J.arr j"
              have "E.cones_map (\<psi> a g') \<chi> j = C (\<chi> j) (\<psi> a g')"
                using 1 \<chi>.cone_axioms by simp
              also have "... = C (C (\<chi> j) (Adj.\<epsilon> a)) (F g')"
                using j a G' Adj.\<psi>_in_terms_of_\<epsilon> [of a g'] by simp
              also have "... = C (C (Adj.\<epsilon> (C.cod (E j))) (F (G (\<chi> j)))) (F g')"
                using j a G' Adj.\<epsilon>.is_natural_1 [of "\<chi> j"] Adj.\<epsilon>.is_natural_2 [of "\<chi> j"]
                by simp
              also have "... = C (Adj.\<epsilon> (C.cod (E j))) (F (\<kappa> j))"
                using j a G' G\<chi>.cone_axioms by auto
              finally show "E.cones_map (\<psi> a g') \<chi> j = ?\<chi>' j" by (simp add: j)
            qed
            ultimately show "E.cones_map (\<psi> a g') \<chi> j = ?\<chi>' j" by auto
          qed
          have "\<psi> a g' = f"
          proof -
            have "\<exists>!f. f \<in> C.hom (F b) a \<and> E.cones_map f \<chi> = ?\<chi>'"
              using cone_\<chi>' \<chi>.is_universal [of "F b" ?\<chi>'] by simp
            moreover have "\<psi> a g' \<in> C.hom (F b) a \<and> E.cones_map (\<psi> a g') \<chi> = ?\<chi>'"
              using 1 2 by simp
            ultimately show ?thesis
              using ex1E [of "\<lambda>f. f \<in> C.hom (F b) a \<and> E.cones_map f \<chi> = ?\<chi>'" "\<psi> a g' = f"]
              using "1" "2" Adj.\<epsilon>.is_extensional C.comp_null(2) C.ex_un_null \<chi>.cone_axioms f
                    mem_Collect_eq restrict_apply
              by blast
          qed
          hence "\<phi> b (\<psi> a g') = \<phi> b f" by auto
          hence "g' = \<phi> b f" using \<chi>.ide_apex G' by (simp add: \<phi>_\<psi>)
          moreover have "?g = \<phi> b f" using f Adj.\<phi>_in_terms_of_\<eta> \<kappa>.ide_apex by simp
          ultimately show "g' = ?g" by presburger
        qed
        ultimately show "\<exists>!g. g \<in> D.hom b (G a) \<and> GE.cones_map g ?G\<chi> = \<kappa>" by blast
      qed
      have "GE.limit_cone (G a) ?G\<chi>" ..
      thus ?thesis by auto
    qed

  end

  section "Special Kinds of Limits"

  subsection "Terminal Objects"

  text{*
   An object of a category @{term C} is a terminal object if and only if it is a limit of the
   empty diagram in @{term C}.
  *}

  locale empty_diagram =
    diagram J C D
  for J :: "'j comp"
  and C :: "'c comp"
  and D :: "'j \<Rightarrow> 'c" +
  assumes is_empty: "\<not>J.arr j"
  begin

    lemma has_as_limit_iff_terminal:
    shows "has_as_limit a \<longleftrightarrow> C.terminal a"
    proof
      assume a: "has_as_limit a"
      show "C.terminal a"
      proof
        have "\<exists>\<chi>. limit_cone a \<chi>" using a by auto
        from this obtain \<chi> where \<chi>: "limit_cone a \<chi>" by blast
        interpret \<chi>: limit_cone J C D a \<chi> using \<chi> by auto
        have cone_\<chi>: "cone a \<chi>" ..
        show "C.ide a" using \<chi>.ide_apex by auto
        have 1: "\<chi> = (\<lambda>j. C.null)" using is_empty by auto
        show "\<And>a'. C.ide a' \<Longrightarrow> \<exists>!f. f \<in> C.hom a' a"
        proof -
          fix a'
          assume a': "C.ide a'"
          interpret A': constant_functor J C a'
            apply unfold_locales using a' by auto
          let ?\<chi>' = "\<lambda>j. C.null"
          have cone_\<chi>': "cone a' ?\<chi>'"
            using a' is_empty apply unfold_locales by auto
          hence "\<exists>!f. f \<in> C.hom a' a \<and> cones_map f \<chi> = ?\<chi>'"
            using \<chi>.is_universal [of a' ?\<chi>'] by presburger
          moreover have "\<And>f. f \<in> C.hom a' a \<Longrightarrow> cones_map f \<chi> = ?\<chi>'"
            using 1 cone_\<chi> by auto
          ultimately show "\<exists>!f. f \<in> C.hom a' a" by blast
        qed
      qed
      next
      assume a: "C.terminal a"
      show "has_as_limit a"
      proof -
        let ?\<chi> = "\<lambda>j. C.null"
        have "C.ide a" using a C.terminal_def by simp
        interpret A: constant_functor J C a
          apply unfold_locales using `C.ide a` by simp
        interpret \<chi>: cone J C D a ?\<chi>
          using `C.ide a` is_empty apply unfold_locales by auto
        have cone_\<chi>: "cone a ?\<chi>" .. 
        have 1: "\<And>a' \<chi>'. cone a' \<chi>' \<Longrightarrow> \<chi>' = (\<lambda>j. C.null)"
        proof -
          fix a' \<chi>'
          assume \<chi>': "cone a' \<chi>'"
          interpret \<chi>': cone J C D a' \<chi>' using \<chi>' by auto
          show "\<chi>' = (\<lambda>j. C.null)"
            using is_empty \<chi>'.is_extensional by metis
        qed
        have "limit_cone a ?\<chi>"
        proof
          fix a' \<chi>'
          assume \<chi>': "cone a' \<chi>'"
          have 2: "\<chi>' = (\<lambda>j. C.null)" using 1 \<chi>' by simp
          interpret \<chi>': cone J C D a' \<chi>' using \<chi>' by auto
          have "\<exists>!f. f \<in> C.hom a' a" using a C.terminal_def \<chi>'.ide_apex by simp
          moreover have "\<And>f. f \<in> C.hom a' a \<Longrightarrow> cones_map f ?\<chi> = \<chi>'"
           using 1 2 cones_map_mapsto cone_\<chi> \<chi>'.cone_axioms mem_Collect_eq by blast
          ultimately show "\<exists>!f. f \<in> C.hom a' a \<and> cones_map f (\<lambda>j. C.null) = \<chi>'"
            by blast
        qed
        thus ?thesis by auto
      qed
    qed

  end

  subsection "Products"

  text{*
    A \emph{product} in a category @{term C} is a limit of a discrete diagram in @{term C}.
  *}

  locale discrete_diagram =
    J: category J +
    diagram J C D
  for J :: "'j comp"
  and C :: "'c comp"
  and D :: "'j \<Rightarrow> 'c" +
  assumes is_discrete: "J.arr = J.ide"
  begin

    abbreviation mkCone
    where "mkCone F \<equiv> (\<lambda>j. if J.arr j then F j else C.null)"

    lemma cone_mkCone:
    assumes "C.ide a" and "\<And>j. J.arr j \<Longrightarrow> F j \<in> C.hom a (D j)"
    shows "cone a (mkCone F)"
    proof -
      interpret A: constant_functor J C a
        apply unfold_locales using assms(1) by auto
      show "cone a (mkCone F)"
        apply unfold_locales
        (* 5 *) using assms(1) apply simp_all
        (* 4 *) using assms is_discrete by auto
    qed

    lemma mkCone_cone:
    assumes "cone a \<pi>"
    shows "mkCone \<pi> = \<pi>"
    proof -
      interpret \<pi>: cone J C D a \<pi>
        using assms by auto
      show "mkCone \<pi> = \<pi>" by auto
    qed

  end

  text{*
    The following locale constructs a discrete diagram in a category @{term C},
    given an index set @{term I} and a function @{term D} mapping @{term I}
    to objects of @{term C}.  Here we construct the diagram shape @{term J}
    using a discrete category construction that allows us to directly identify
    the objects of @{term J} with the elements of @{term I}, however this construction
    can only be applied in case the set @{term I} is not the universe of its
    element type.
  *}

  locale discrete_diagram_from_map =
    J: DiscreteCategory.discrete_category I +
    C: category C
  for I :: "'i set"
  and C :: "'c comp"
  and D :: "'i \<Rightarrow> 'c" +
  assumes maps_to_ide: "i \<in> I \<Longrightarrow> C.ide (D i)"
  begin

    definition map
    where "map j \<equiv> if J.arr j then D j else C.null"

  end

  sublocale discrete_diagram_from_map \<subseteq> discrete_diagram J.comp C map
    apply unfold_locales
    using map_def maps_to_ide J.arr_char by auto

  locale product_cone =
    J: category J +
    C: category C +
    D: discrete_diagram J C D +
    limit_cone J C D a \<pi>
  for J :: "'j comp"
  and C :: "'c comp"
  and D :: "'j \<Rightarrow> 'c"
  and a :: 'c
  and \<pi> :: "'j \<Rightarrow> 'c"
  begin

    lemma is_cone:
    shows "D.cone a \<pi>" ..

    text{*
      The following versions of @{prop is_universal} and @{prop induced_arrowI}
      from the @{text limit_cone} locale are specialized to the case in which the
      underlying diagram is a product diagram.
    *}

    lemma is_universal':
    assumes "C.ide b" and "\<And>j. J.arr j \<Longrightarrow> F j \<in> C.hom b (D j)"
    shows "\<exists>!f. f \<in> C.hom b a \<and> (\<forall>j. J.arr j \<longrightarrow> C (\<pi> j) f = F j)"
    proof -
      let ?\<chi> = "D.mkCone F"
      interpret B: constant_functor J C b
        apply unfold_locales using assms(1) by auto
      have cone_\<chi>: "D.cone b ?\<chi>"
        using assms
        apply unfold_locales
        using assms(1) D.is_discrete by auto
      interpret \<chi>: cone J C D b ?\<chi> using cone_\<chi> by auto
      have "\<exists>!f. f \<in> C.hom b a \<and> D.cones_map f \<pi> = ?\<chi>"
        using cone_\<chi> is_universal by presburger
      moreover have
           "\<And>f. f \<in> C.hom b a \<Longrightarrow>
                  D.cones_map f \<pi> = ?\<chi> \<longleftrightarrow>
                    (\<forall>j. J.arr j \<longrightarrow> C (\<pi> j) f = F j)"
      proof -
        fix f
        assume f: "f \<in> C.hom b a"
        show "D.cones_map f \<pi> = ?\<chi> \<longleftrightarrow> 
                (\<forall>j. J.arr j \<longrightarrow> C (\<pi> j) f = F j)"
        proof
          assume 1: "D.cones_map f \<pi> = ?\<chi>"
          show "\<forall>j. J.arr j \<longrightarrow> C (\<pi> j) f = F j"
         proof -
            have "\<And>j. J.arr j \<Longrightarrow> C (\<pi> j) f = F j"
            proof -
              fix j
              assume j: "J.arr j"
              have "C (\<pi> j) f = D.cones_map f \<pi> j"
                using j f cone_axioms by simp
              also have "... = ?\<chi> j" using 1 by presburger
              also have "... = F j" using j by simp
              finally show "C (\<pi> j) f = F j" by auto
            qed
            thus ?thesis by auto
          qed
          next
          assume 1: "\<forall>j. J.arr j \<longrightarrow> C (\<pi> j) f = F j"
          show "D.cones_map f \<pi> = ?\<chi>"
            using 1 f is_cone \<chi>.is_extensional D.is_discrete is_cone cone_\<chi> by auto
        qed
      qed
      ultimately show ?thesis by blast
    qed

    abbreviation induced_arrow' :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) \<Rightarrow> 'c"
    where "induced_arrow' b F \<equiv> induced_arrow b (D.mkCone F)"

    lemma induced_arrowI':
    assumes "C.ide b" and "\<And>j. J.arr j \<Longrightarrow> F j \<in> C.hom b (D j)"
    shows "\<And>j. J.arr j \<Longrightarrow> C (\<pi> j) (induced_arrow' b F) = F j"
    proof -
      interpret B: constant_functor J C b
        apply unfold_locales using assms(1) by auto
      interpret \<chi>: cone J C D b "D.mkCone F"
        using assms D.cone_mkCone by blast
      have cone_\<chi>: "D.cone b (D.mkCone F)" ..
      hence 1: "D.cones_map (induced_arrow' b F) \<pi> = D.mkCone F"
        using induced_arrowI by blast
      fix j
      assume j: "J.arr j"
      have "C (\<pi> j) (induced_arrow b (D.mkCone F)) = D.cones_map (induced_arrow' b F) \<pi> j"
        using assms(1) j cone_\<chi> is_cone induced_arrowI [of "D.mkCone F" b] restrict_apply
        by simp
      also have "... = D.mkCone F j"
        using 1 by simp
      also have "... = F j"
        using j by auto
      finally show "C (\<pi> j) (induced_arrow' b F) = F j"
        by auto
    qed

  end

  context discrete_diagram
  begin

    lemma product_coneI:
    assumes "limit_cone a \<pi>" 
    shows "product_cone J C D a \<pi>"
    proof -
      interpret L: limit_cone J C D a \<pi>
        using assms by auto
      show "product_cone J C D a \<pi>" ..
    qed

  end

  context category
  begin

    definition has_as_product
    where "has_as_product J D a \<equiv> (\<exists>\<pi>. product_cone J C D a \<pi>)"

    text{*
      A category has @{term I}-indexed products for an @{typ 'i}-set @{term I}
      if every @{term I}-indexed discrete diagram has a product.
      In order to reap the benefits of being able to directly identify the elements
      of a set I with the objects of discrete category it generates (thereby avoiding
      the use of coercion maps), it is necessary to assume that @{term "I \<noteq> UNIV"}.
      If we want to assert that a category has products indexed by the universe of
      some type @{typ 'i}, we have to pass to a larger type, such as @{typ "'i option"}.
    *}

    definition has_products
    where "has_products (I :: 'i set) \<equiv>
             I \<noteq> UNIV \<and>
             (\<forall>D. diagram (DiscreteCategory.discrete_category.comp I) C D
                    \<longrightarrow> (\<exists>a. has_as_product (DiscreteCategory.discrete_category.comp I) D a))"

    lemma ex_productE:
    assumes "\<exists>a. has_as_product J D a"
    obtains a \<pi> where "product_cone J C D a \<pi>"
      using assms has_as_product_def someI_ex [of "\<lambda>a. has_as_product J D a"] by metis

    lemma has_products_if_has_limits:
    assumes "has_limits (undefined :: 'j)" and "I \<noteq> (UNIV :: 'j set)"
    shows "has_products I"
    proof (unfold has_products_def)
      interpret J: DiscreteCategory.discrete_category I
        apply unfold_locales using assms(2) by auto
      have "\<And>D. diagram J.comp C D \<Longrightarrow> \<exists>a. has_as_product J.comp D a"
      proof -
        fix D
        assume D: "diagram J.comp C D"
        interpret D: diagram J.comp C D using D by auto
        interpret D: discrete_diagram J.comp C D
          apply unfold_locales using J.is_discrete by auto
        obtain a \<pi> where \<pi>: "D.limit_cone a \<pi>"
          using assms(1) has_limits_def has_limits_of_shape_def [of J.comp] D J.is_category
          by metis
        have "product_cone J.comp C D a \<pi>"
          using \<pi> D.product_coneI by auto
        hence "has_as_product J.comp D a"
          using has_as_product_def by blast
        thus "\<exists>a. has_as_product J.comp D a"
          by auto
      qed
      thus "I \<noteq> UNIV \<and> (\<forall>D. diagram J.comp C D \<longrightarrow> (\<exists>a. has_as_product J.comp D a))"
        using assms(2) by auto
    qed

  end

  subsection "Equalizers"

  text{*
    An \emph{equalizer} in a category @{term C} is a limit of a parallel pair
    of arrows in @{term C}.
  *}

  locale parallel_pair_diagram =
    J: parallel_pair +
    C: category C
  for C :: "'c comp"
  and f0 :: 'c
  and f1 :: 'c +
  assumes is_parallel: "C.par f0 f1"
  begin

    definition map
    where "map \<equiv> (\<lambda>j. if j = J.Zero then C.dom f0
                       else if j = J.One then C.cod f0
                       else if j = J.j0 then f0
                       else if j = J.j1 then f1
                       else C.null)"

  end

  sublocale parallel_pair_diagram \<subseteq> diagram J.comp C map
    apply unfold_locales
    (* 5 *) apply (simp add: J.arr_char map_def)
    (* 4 *) using map_def is_parallel J.arr_char apply auto[1]
    (* 3 *) using map_def is_parallel J.arr_char J.cod_simp J.dom_simp apply auto[1]
    proof -
      fix j
      assume j: "J.arr j"
      show "C.cod (map j) = map (J.cod j)"
      proof -
        have "j = J.Zero \<or> j = J.One \<Longrightarrow> ?thesis" using is_parallel map_def by auto
        moreover have "j = J.j0 \<or> j = J.j1 \<Longrightarrow> ?thesis"
          using is_parallel map_def J.Zero_not_eq_j0 J.One_not_eq_j0 J.Zero_not_eq_One
                J.Zero_not_eq_j1 J.One_not_eq_j1 J.Zero_not_eq_One J.cod_simp
          by presburger
        ultimately show ?thesis using j J.arr_char by fast
      qed
      fix j'
      assume j': "j' \<in> J.hom (J.cod j) (J.cod j')"
      show "map (J.comp j' j) = C (map j') (map j)"
      proof -
        have jj': "J.seq j' j" using j j' by force
        hence 1: "(j = J.Zero \<and> j' \<noteq> J.One) \<or> (j \<noteq> J.Zero \<and> j' = J.One)"
          using J.seq_char by blast
        have "j = J.Zero \<and> j' \<noteq> J.One \<Longrightarrow> ?thesis"
          using jj' map_def is_parallel J.arr_char J.cod_simp J.dom_simp J.seq_char by simp
        moreover have "j \<noteq> J.Zero \<and> j' = J.One \<Longrightarrow> ?thesis"
          using jj' J.ide_char map_def J.Zero_not_eq_One \<open>C.cod (map j) = map (J.cod j)\<close>
                is_parallel
          by auto
        ultimately show ?thesis using 1 by auto
      qed
    qed

  context parallel_pair_diagram
  begin

    definition mkCone
    where "mkCone e \<equiv> \<lambda>j. if J.arr j then if j = J.Zero then e else C f0 e else C.null"

    abbreviation is_equalized_by
    where "is_equalized_by e \<equiv> C.seq f0 e \<and> C f0 e = C f1 e"

    abbreviation has_as_equalizer
    where "has_as_equalizer e \<equiv> limit_cone (C.dom e) (mkCone e)"

    lemma cone_mkCone:
    assumes "is_equalized_by e"
    shows "cone (C.dom e) (mkCone e)"
    proof -
      interpret E: constant_functor J.comp C "C.dom e"
        apply unfold_locales using assms by auto
      show "cone (C.dom e) (mkCone e)"
        using E.value_is_ide apply unfold_locales
        (* 5 *) apply simp_all
        (* 5 *) using assms mkCone_def apply simp
        (* 4 *) using assms mkCone_def apply (metis (no_types, lifting) C.dom_comp)
      proof -
        fix j
        assume j: "J.arr j"
        have "(J.arr j \<longrightarrow> J.cod j \<noteq> J.dom j) \<longleftrightarrow>
              (J.arr j \<longrightarrow> (j \<noteq> J.Zero \<or> j = J.One) \<and> (j = J.Zero \<or> j \<noteq> J.One))"
          using J.seq_char by blast
        (* The next two might be useful lemmas in parallel_pair_diagram. *)
        moreover have "\<forall>a. if a = J.j0 \<or> a = J.j1 then J.dom a = J.Zero
                           else if J.arr a then J.dom a = a else J.dom a = J.null"
          using J.dom_char by presburger
        moreover have "\<forall>a. if a = J.j0 \<or> a = J.j1 then J.cod a = J.One
                           else if J.arr a then J.cod a = a else J.cod a = J.null"
          using J.cod_char by presburger
        ultimately show "C.cod (mkCone e j) = map (J.cod j)"
          using j by (metis C.cod_comp map_def assms mkCone_def)
        next
        show "\<And>j. C.ide (C.dom e) \<Longrightarrow> J.arr j \<Longrightarrow> C (map j) (mkCone e (J.dom j)) = mkCone e j"
        proof -
          fix j :: J.arr
          assume j: "J.arr j"
          have f2: "\<forall>a. if a = J.Zero then map a = C.dom f0
                        else if a = J.One then map a = C.cod f0
                        else if a = J.j0 then map a = f0
                        else if a = J.j1 then map a = f1
                        else map a = C.null"
            using map_def by presburger
          hence f3: "map j = f1 \<or> j = J.One \<or> j = J.Zero \<or> j = J.j0"
            using j by (meson J.arr_char)
          have "j = J.Zero \<or> C (map j) (mkCone e (J.dom j)) = mkCone e j"
            using j f3 f2
            by (metis C.arr_cod_iff_arr C.comp_assoc C.comp_cod_arr C.dom_cod
                      J.arr_char J.dom_simp(2) J.dom_simp(3) J.dom_simp(4) assms mkCone_def)
          hence "C (map j) (mkCone e (J.dom j)) = mkCone e j"
            using f2 j by (metis C.comp_cod_arr J.dom_simp(1) assms mkCone_def)
          thus "C (map j) (mkCone e (J.dom j)) = mkCone e j" by blast
        qed
        next
        show "\<And>j. C.ide (C.dom e) \<Longrightarrow> J.arr j \<Longrightarrow> C (mkCone e (J.cod j)) (C.dom e) = mkCone e j"
        proof -
          fix j
          assume j: "J.arr j"
          show "C (mkCone e (J.cod j)) (C.dom e) = mkCone e j"
          proof -
            have "j = J.Zero \<or> j = J.One \<Longrightarrow> ?thesis"
              using assms mkCone_def
              by (metis (no_types, lifting) C.arr_comp C.comp_arr_dom C.comp_assoc'
                  C.not_arr_null J.cod_simp(1) J.cod_simp(2) j)
            moreover have "j = J.j0 \<or> j = J.j1 \<Longrightarrow> ?thesis"
              using assms mkCone_def
              by (metis (no_types, lifting) C.arr_comp C.comp_arr_dom C.dom_comp J.arr_char
                  J.cod_char J.seq_char)
            ultimately show ?thesis using j J.arr_char by blast
          qed
        qed
      qed
    qed

    lemma is_equalized_by_cone:
    assumes "cone a \<chi>"
    shows "is_equalized_by (\<chi> (J.Zero))"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      show ?thesis
        by (metis J.arr_char J.cod_char J.dom_char J.j0_not_eq_j1 J.seq_char Limit.cone_def
                  \<chi>.cone_axioms \<chi>.is_natural_1 \<chi>.is_natural_2 \<chi>.preserves_arr \<chi>.preserves_cod
                  constant_functor.map_simp is_parallel parallel_pair_diagram.map_def
                  parallel_pair_diagram_axioms)
    qed

    lemma mkCone_cone:
    assumes "cone a \<chi>"
    shows "mkCone (\<chi> J.Zero) = \<chi>"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      have 1: "is_equalized_by (\<chi> J.Zero)"
        using assms is_equalized_by_cone by blast
      show ?thesis
      proof
        fix j
        have "j = J.Zero \<Longrightarrow> mkCone (\<chi> J.Zero) j = \<chi> j"
          using mkCone_def by simp
        moreover have "j = J.One \<or> j = J.j0 \<or> j = J.j1 \<Longrightarrow> mkCone (\<chi> J.Zero) j = \<chi> j"
          using J.arr_char J.cod_char J.dom_char J.seq_char mkCone_def
                \<chi>.is_natural_1 \<chi>.is_natural_2 \<chi>.A.map_simp map_def
          by (metis (no_types, lifting))
        ultimately have "J.arr j \<Longrightarrow> mkCone (\<chi> J.Zero) j = \<chi> j"
          using J.arr_char by auto
        thus "mkCone (\<chi> J.Zero) j = \<chi> j"
          using mkCone_def by fastforce
      qed
    qed

  end

  locale equalizer_cone =
    J: parallel_pair +
    C: category C +
    D: parallel_pair_diagram C f0 f1 +
    limit_cone J.comp C D.map "C.dom e" "D.mkCone e"
  for C :: "'c comp"
  and f0 :: 'c
  and f1 :: 'c
  and e :: 'c
  begin

    lemma equalizes:
    shows "D.is_equalized_by e"
    proof
      show "C.seq f0 e"
        using D.map_def D.is_parallel J.arr_char J.cod_char J.dom_char J.seq_char preserves_arr
              D.mkCone_def C.arr_compD(3)
        by metis
      show "C f0 e = C f1 e"
          using D.mkCone_def [of e] J.Zero_not_eq_j1
                J.dom_char D.mkCone_def [of e] J.arr_char is_natural_1 [of J.j1]
                D.map_def J.cod_char J.j0_not_eq_j1 J.seq_char
          by metis
    qed

    lemma is_universal':
    assumes "D.is_equalized_by e'"
    shows "\<exists>!h. h \<in> C.hom (C.dom e') (C.dom e) \<and> C e h = e'"
    proof -
      have "D.cone (C.dom e') (D.mkCone e')"
        using assms D.cone_mkCone by blast
      moreover have 0: "D.cone (C.dom e) (D.mkCone e)" ..
      ultimately have 1: "\<exists>!h. h \<in> C.hom (C.dom e') (C.dom e) \<and>
                               D.cones_map h (D.mkCone e) = D.mkCone e'"
        using is_universal [of "C.dom e'" "D.mkCone e'"] by auto
      have 2: "\<And>h. h \<in> C.hom (C.dom e') (C.dom e) \<Longrightarrow>
                    D.cones_map h (D.mkCone e) = D.mkCone e' \<longleftrightarrow> C e h = e'"
      proof -
        fix h
        assume h: "h \<in> C.hom (C.dom e') (C.dom e)"
        show "D.cones_map h (D.mkCone e) = D.mkCone e' \<longleftrightarrow> C e h = e'"
        proof
          assume 3: "D.cones_map h (D.mkCone e) = D.mkCone e'"
          show "C e h = e'"
          proof -
            have "e' = D.mkCone e' J.Zero"
              using D.mkCone_def J.arr_char by simp
            also have "... = D.cones_map h (D.mkCone e) J.Zero"
              using 3 by simp
            also have "... = C e h"
              using 0 h D.mkCone_def J.arr_char by auto
            finally show ?thesis by auto
          qed
          next
          assume e': "C e h = e'"
          show "D.cones_map h (D.mkCone e) = D.mkCone e'"
          proof
            fix j
            have "\<not>J.arr j \<Longrightarrow> D.cones_map h (D.mkCone e) j = D.mkCone e' j"
              using h cone_axioms D.mkCone_def [of e'] by auto
            moreover have "j = J.Zero \<Longrightarrow> D.cones_map h (D.mkCone e) j = D.mkCone e' j"
              using h e' cone_\<chi> D.mkCone_def [of e] D.mkCone_def [of e'] J.arr_char [of J.Zero]
              by force
            moreover have "J.arr j \<and> j \<noteq> J.Zero \<Longrightarrow> D.cones_map h (D.mkCone e) j = D.mkCone e' j"
            proof -
              assume j: "J.arr j \<and> j \<noteq> J.Zero"
              have "D.cones_map h (D.mkCone e) j = C (D.mkCone e j) h"
                using j h equalizes D.mkCone_def [of e] D.cone_mkCone [of e]
                      J.arr_char J.Zero_not_eq_One J.Zero_not_eq_j0 J.Zero_not_eq_j1
                by auto
              also have "... = C (C f0 e) h"
                using j D.mkCone_def [of e] J.arr_char J.Zero_not_eq_One J.Zero_not_eq_j0
                      J.Zero_not_eq_j1
                by metis
              also have "... = C f0 (C e h)"
                using h equalizes by blast
              also have "... = D.mkCone e' j"
                using j e' h equalizes D.mkCone_def [of e'] J.arr_char [of J.One] J.Zero_not_eq_One
                by presburger
              finally show ?thesis by auto
            qed
            ultimately show "D.cones_map h (D.mkCone e) j = D.mkCone e' j" by blast
          qed
        qed
      qed
      thus ?thesis using 1 by blast
    qed

    lemma induced_arrowI':
    assumes "D.is_equalized_by e'"
    shows "induced_arrow (C.dom e') (D.mkCone e') \<in> C.hom (C.dom e') (C.dom e) \<and>
           C e (induced_arrow (C.dom e') (D.mkCone e')) = e'"
    proof -
      interpret A': constant_functor J.comp C "C.dom e'"
        apply unfold_locales using assms by auto
      have cone: "D.cone (C.dom e') (D.mkCone e')"
        apply unfold_locales
        (* 5 *) using A'.value_is_ide apply simp_all
        (* 5 *) using assms D.mkCone_def apply simp
        (* 4 *) using assms D.mkCone_def apply (metis C.dom_comp)
        (* 3 *) using assms D.mkCone_def apply (metis C.cod_comp equalizes preserves_cod)
        (* 2 *) using assms D.mkCone_def
        (* 1 *) apply (meson D.cone_mkCone Limit.cone_def natural_transformation.is_natural_1)
                using assms A'.map_simp D.cone_mkCone Limit.cone_def
                      natural_transformation.is_natural_2
                by (metis (full_types))
      have "C e (induced_arrow (C.dom e') (D.mkCone e')) =
              D.cones_map (induced_arrow (C.dom e') (D.mkCone e')) (D.mkCone e) J.Zero"
        using cone J.arr_char D.mkCone_def cone_\<chi> induced_arrowI mem_Collect_eq restrict_apply'
        by auto
      also have "... = e'"
      proof -
        have "D.cones_map (induced_arrow (C.dom e') (D.mkCone e')) (D.mkCone e) = D.mkCone e'"
          using cone induced_arrowI by blast
        thus ?thesis
          using J.arr_char D.mkCone_def by simp
      qed
      finally have "C e (induced_arrow (C.dom e') (D.mkCone e')) = e'"
        by auto
      thus ?thesis using cone induced_arrowI by simp
    qed

  end

  context category
  begin

    definition has_as_equalizer
    where "has_as_equalizer f0 f1 e \<equiv> par f0 f1 \<and> parallel_pair_diagram.has_as_equalizer C f0 f1 e"

    definition has_equalizers
    where "has_equalizers = (\<forall>f0 f1. par f0 f1 \<longrightarrow> (\<exists>e. has_as_equalizer f0 f1 e))"

  end

  section "Limits by Products and Equalizers"
 
  text{*
    A category with equalizers has limits of shape @{term J} if it has products
    indexed by the set of arrows of @{term J} and the set of objects of @{term J}.
    The proof is patterned after \cite{MacLane}, Theorem 2, page 109:
    \begin{quotation}
       ``The limit of @{text "F: J \<rightarrow> C"} is the equalizer @{text e}
       of @{text "f, g: \<Pi>\<^sub>i F\<^sub>i \<rightarrow> \<Pi>\<^sub>u F\<^sub>c\<^sub>o\<^sub>d \<^sub>u (u \<in> arr J, i \<in> J)"}
       where @{text "p\<^sub>u f = p\<^sub>c\<^sub>o\<^sub>d \<^sub>u"}, @{text "p\<^sub>u g = F\<^sub>u o p\<^sub>d\<^sub>o\<^sub>m \<^sub>u"};
       the limiting cone @{text \<mu>} is @{text "\<mu>\<^sub>j = p\<^sub>j e"}, for @{text "j \<in> J"}.''
    \end{quotation}
  *}

  locale category_with_equalizers =
    category C
  for C :: "'c comp" +
  assumes has_equalizers: "has_equalizers"
  begin

    lemma has_limits_if_has_products:
    fixes J :: "'j comp"
    assumes "category J" and "has_products (Collect (category.ide J))"
    and "has_products (Collect (partial_magma.arr J))"
    shows "has_limits_of_shape J"
    proof (unfold has_limits_of_shape_def)
      interpret J: category J using assms(1) by auto
      have "\<And>D. diagram J C D \<Longrightarrow> (\<exists>a \<chi>. limit_cone J C D a \<chi>)"
      proof -
        fix D
        assume D: "diagram J C D"
        interpret D: diagram J C D using D by auto

        text{*
          First, construct the two required products and their cones.
        *}
        interpret Obj: DiscreteCategory.discrete_category "Collect J.ide"
          apply unfold_locales using J.not_arr_null J.ideD(1) mem_Collect_eq by blast
        interpret \<Delta>o: discrete_diagram_from_map "Collect J.ide" C D
          apply unfold_locales using D.preserves_ide by auto
        have "\<exists>p. has_as_product Obj.comp \<Delta>o.map p"
          using assms(2) \<Delta>o.diagram_axioms has_products_def [of "Collect J.ide"] by metis
        from this obtain \<Pi>o \<pi>o where \<pi>o: "product_cone Obj.comp C \<Delta>o.map \<Pi>o \<pi>o"
           using ex_productE [of Obj.comp \<Delta>o.map] by auto
        interpret \<pi>o: product_cone Obj.comp C \<Delta>o.map \<Pi>o \<pi>o using \<pi>o by auto
        have \<pi>o_in_hom: "\<And>j. Obj.arr j \<Longrightarrow> \<pi>o j \<in> hom \<Pi>o (D j)"
          using \<pi>o.preserves_arr \<pi>o.preserves_dom \<pi>o.preserves_cod \<Delta>o.map_def by auto

        interpret Arr: DiscreteCategory.discrete_category "Collect J.arr"
          apply unfold_locales using J.not_arr_null by auto
        interpret \<Delta>a: discrete_diagram_from_map "Collect J.arr" C "D o J.cod"
          apply unfold_locales by auto
        have "discrete_diagram Arr.comp C \<Delta>a.map" ..
        hence "\<exists>p. has_as_product Arr.comp \<Delta>a.map p"
          using assms(3) has_products_def [of "Collect J.arr"]
          by (simp add: discrete_diagram_def subsetI)
        from this obtain \<Pi>a \<pi>a where \<pi>a: "product_cone Arr.comp C \<Delta>a.map \<Pi>a \<pi>a"
          using ex_productE [of Arr.comp \<Delta>a.map] by auto
        interpret \<pi>a: product_cone Arr.comp C \<Delta>a.map \<Pi>a \<pi>a using \<pi>a by auto
        have \<pi>a_in_hom: "\<And>j. Arr.arr j \<Longrightarrow> \<pi>a j \<in> hom \<Pi>a (D (J.cod j))"
          using \<pi>a.preserves_arr \<pi>a.preserves_cod \<pi>a.preserves_dom \<Delta>a.map_def by auto

        text{*
           Next, construct a parallel pair of arrows @{text "f, g: \<Pi>o \<rightarrow> \<Pi>a"}
           that expresses the commutativity constraints imposed by the diagram.
        *}
        interpret \<Pi>o: constant_functor Arr.comp C \<Pi>o
          apply unfold_locales using \<pi>o.ide_apex by auto
        let ?\<chi> = "\<lambda>j. if Arr.arr j then \<pi>o (J.cod j) else null"
        interpret \<chi>: cone Arr.comp C \<Delta>a.map \<Pi>o ?\<chi>
          apply unfold_locales
          using \<pi>o.ide_apex \<pi>o_in_hom \<Delta>a.map_def \<Delta>o.map_def \<Delta>o.is_discrete by auto
        let ?f = "\<pi>a.induced_arrow \<Pi>o ?\<chi>"
        have f: "?f \<in> hom \<Pi>o \<Pi>a \<and> \<Delta>a.cones_map ?f \<pi>a = ?\<chi>"
          using \<chi>.cone_axioms \<pi>a.induced_arrowI by blast
        have ff: "\<And>j. J.arr j \<Longrightarrow> C (\<pi>a j) ?f = \<pi>o (J.cod j)"
        proof -
          fix j
          assume j: "J.arr j"
          have "C (\<pi>a j) ?f = \<Delta>a.cones_map ?f \<pi>a j"
            using f j \<pi>a.cone_axioms by simp
          also have "... = ?\<chi> j"
            using f j by presburger
          also have "... = \<pi>o (J.cod j)"
            using j by fastforce
          finally show "C (\<pi>a j) ?f = \<pi>o (J.cod j)" by auto
        qed

        let ?\<chi>' = "\<lambda>j. if Arr.arr j then C (D j) (\<pi>o (J.dom j)) else null"
        interpret \<chi>': cone Arr.comp C \<Delta>a.map \<Pi>o ?\<chi>'
          apply unfold_locales
          using \<pi>o.ide_apex \<pi>o_in_hom \<Delta>o.map_def \<Delta>a.map_def by auto
        let ?g = "\<pi>a.induced_arrow \<Pi>o ?\<chi>'"
        have g: "?g \<in> hom \<Pi>o \<Pi>a \<and> \<Delta>a.cones_map ?g \<pi>a = ?\<chi>'"
          using \<chi>'.cone_axioms \<pi>a.induced_arrowI by blast
        have gg: "\<And>j. J.arr j \<Longrightarrow> C (\<pi>a j) ?g = C (D j) (\<pi>o (J.dom j))"
        proof -
          fix j
          assume j: "J.arr j"
          have "C (\<pi>a j) ?g = \<Delta>a.cones_map ?g \<pi>a j"
            using g j \<pi>a.cone_axioms by simp
          also have "... = ?\<chi>' j"
            using g j by presburger
          also have "... = C (D j) (\<pi>o (J.dom j))"
            using j by fastforce
          finally show "C (\<pi>a j) ?g = C (D j) (\<pi>o (J.dom j))" by auto
        qed

        interpret PP: parallel_pair_diagram C ?f ?g
          (*
           * TODO: Investigate why there are trivial proof obligations here
           * that should probably have been hidden by the parallel_pair locale.
           *)
          apply unfold_locales using f g by auto
        have "par ?f ?g" using f g by auto
        from this obtain e where equ: "PP.has_as_equalizer e"
          using has_equalizers has_equalizers_def has_as_equalizer_def by blast
        interpret EQU: limit_cone PP.J.comp C PP.map "dom e" "PP.mkCone e"
          using equ by auto
        interpret EQU: equalizer_cone C ?f ?g e ..

        text{*
          An arrow @{term h} with @{term "cod h = \<Pi>o"} equalizes @{term f} and @{term g}
          if and only if it satisfies the commutativity condition required for a cone over
          @{term D}.
        *}
        have E: "\<And>h. h \<in> hom (dom h) \<Pi>o \<Longrightarrow>
                   C ?f h = C ?g h \<longleftrightarrow> (\<forall>j. J.arr j \<longrightarrow> C (?\<chi> j) h = C (?\<chi>' j) h)"
        proof
          fix h
          assume h: "h \<in> hom (dom h) \<Pi>o"
          show "C ?f h = C ?g h \<Longrightarrow> \<forall>j. J.arr j \<longrightarrow> C (?\<chi> j) h = C (?\<chi>' j) h"
          proof -
            assume E: "C ?f h = C ?g h"
            have "\<And>j. J.arr j \<Longrightarrow> C (?\<chi> j) h = C (?\<chi>' j) h"
            proof -
              fix j
              assume j: "J.arr j"
              have "C (?\<chi> j) h = C (\<Delta>a.cones_map ?f \<pi>a j) h"
                using j f by presburger
              also have "... = C (\<pi>a j) (C ?f h)"
                using j f h \<pi>a \<pi>a.cone_axioms \<Delta>a.map_def \<Delta>a.preserves_ide \<pi>a.cone_\<chi> ideD(1)
                      mem_Collect_eq not_arr_null restrict_apply
                by auto
              also have "... = C (\<pi>a j) (C ?g h)"
                using j E by simp
              also have "... = C (\<Delta>a.cones_map ?g \<pi>a j) h"
                using j g h \<pi>a \<pi>a.cone_axioms \<Delta>a.map_def \<Delta>a.preserves_ide \<pi>a.cone_\<chi> ideD(1)
                      mem_Collect_eq not_arr_null restrict_apply
                by auto
              also have "... = C (?\<chi>' j) h"
                using j g by presburger
              finally show "C (?\<chi> j) h = C (?\<chi>' j) h" by auto
            qed
            thus "\<forall>j. J.arr j \<longrightarrow> C (?\<chi> j) h = C (?\<chi>' j) h" by blast
          qed
          show "\<forall>j. J.arr j \<longrightarrow> C (?\<chi> j) h = C (?\<chi>' j) h \<Longrightarrow> C ?f h = C ?g h"
          proof -
            assume 1: "\<forall>j. J.arr j \<longrightarrow> C (?\<chi> j) h = C (?\<chi>' j) h"
            have 2: "\<And>j. j \<in> Collect J.arr \<Longrightarrow> C (\<pi>a j) (C ?f h) = C (\<pi>a j) (C ?g h)"
            proof -
              fix j
              assume j: "j \<in> Collect J.arr"
              have "C (\<pi>a j) (C ?f h) = C (C (\<pi>a j) ?f) h"
                using j f h \<pi>a by simp
              also have "... = C (?\<chi> j) h"
              proof -
                have "C (\<pi>a j) ?f = \<Delta>a.cones_map ?f \<pi>a j"
                  using j f \<pi>a.cone_axioms \<Delta>a.map_def \<Delta>a.preserves_ide \<pi>a.cone_\<chi> ideD(1)
                        mem_Collect_eq not_arr_null restrict_apply
                  by auto
                thus ?thesis using f by presburger
              qed
              also have "... = C (?\<chi>' j) h"
                using 1 j by auto
              also have "... = C (C (\<pi>a j) ?g) h"
              proof -
                have "C (\<pi>a j) ?g = \<Delta>a.cones_map ?g \<pi>a j"
                  using j g \<pi>a.cone_axioms \<Delta>a.map_def \<Delta>a.preserves_ide \<pi>a.cone_\<chi> ideD(1)
                        mem_Collect_eq not_arr_null restrict_apply
                  by auto
                thus ?thesis using g by presburger
              qed
              also have "... = C (\<pi>a j) (C ?g h)"
                using j g h \<pi>a by simp
              finally show "C (\<pi>a j) (C ?f h) = C (\<pi>a j) (C ?g h)"
                by auto
            qed
            show "C ?f h = C ?g h"
            proof -
              have "\<And>j. j \<in> Collect J.arr \<Longrightarrow> C (\<pi>a j) (C ?f h) \<in> hom (dom h) ((D o J.cod) j)"
                using f h \<pi>a_in_hom by simp
              hence 3: "\<exists>!k. k \<in> hom (dom h) \<Pi>a \<and>
                             (\<forall>j. j \<in> Collect J.arr \<longrightarrow> C (\<pi>a j) k = C (\<pi>a j) (C ?f h))"
                using h \<pi>a \<pi>a.is_universal' [of "dom h" "\<lambda>j. C (\<pi>a j) (C ?f h)"] \<Delta>a.map_def
                by simp
              have 4: "\<And>P x x'. \<exists>!k. P k x \<Longrightarrow> P x x \<Longrightarrow> P x' x \<Longrightarrow> x' = x" by auto
              let ?P = "\<lambda> k x. k \<in> hom (dom h) \<Pi>a \<and>
                                   (\<forall>j. j \<in> Collect J.arr \<longrightarrow> C (\<pi>a j) k = C (\<pi>a j) x)"
              have "?P (C ?g h) (C ?g h)" using g h by force
              moreover have "?P (C ?f h) (C ?g h)" using 2 f g h by force
              ultimately show ?thesis using 3 4 [of ?P "C ?f h" "C ?g h"] by presburger
            qed
          qed
        qed
        have E': "\<And>e. e \<in> hom (dom e) \<Pi>o \<Longrightarrow>
                   C ?f e = C ?g e \<longleftrightarrow>
                     (\<forall>j. J.arr j \<longrightarrow>
                           C (C (D (J.cod j)) (C (\<pi>o (J.cod j)) e)) (dom e)
                              = C (D j) (C (\<pi>o (J.dom j)) e))"
        proof -
          have 1: "\<And>e j. e \<in> hom (dom e) \<Pi>o \<Longrightarrow> J.arr j \<Longrightarrow>
                           C (?\<chi> j) e = C (C (D (J.cod j)) (C (\<pi>o (J.cod j)) e)) (dom e)"
              using f D.preserves_ide \<pi>o_in_hom by auto
          have 2: "\<And>e j. e \<in> hom (dom e) \<Pi>o \<Longrightarrow> J.arr j \<Longrightarrow>
                           C (?\<chi>' j) e = C (D j) (C (\<pi>o (J.dom j)) e)"
              using g \<pi>o_in_hom by simp
          show "\<And>e. e \<in> hom (dom e) \<Pi>o \<Longrightarrow>
                   C ?f e = C ?g e \<longleftrightarrow>
                     (\<forall>j. J.arr j \<longrightarrow>
                           C (C (D (J.cod j)) (C (\<pi>o (J.cod j)) e)) (dom e)
                              = C (D j) (C (\<pi>o (J.dom j)) e))"
            using 1 2 E by presburger
        qed
        text{*
          The composites of @{term e} with the projections from the product @{term \<Pi>o}
          determine a limit cone @{term \<mu>} for @{term D}.  The component of @{term \<mu>}
          at an object @{term j} of @{term J} is the composite @{term "C (\<pi>o j) e"}.
          However, we need to extend @{term \<mu>} to all arrows @{term j} of @{term J},
          so the correct definition is @{term "\<mu> j = C (D j) (C (\<pi>o (J.dom j)) e)"}.
        *}
        have e: "e \<in> hom (dom e) \<Pi>o \<and> C ?f e = C ?g e"
          using f EQU.equalizes by simp
        interpret domE: constant_functor J C "dom e"
          apply unfold_locales using e by simp
        let ?\<mu> = "\<lambda>j. if J.arr j then C (D j) (C (\<pi>o (J.dom j)) e) else null"
        have \<mu>: "\<And>j. J.arr j \<Longrightarrow> ?\<mu> j \<in> hom (dom e) (D (J.cod j))"
          using e \<pi>o_in_hom by simp
        interpret \<mu>: cone J C D "dom e" ?\<mu>
          apply unfold_locales
          (* 5 *) apply simp
        proof -
          fix j
          assume j: "J.arr j"
          show "dom (?\<mu> j) = domE.map (J.dom j)" using j \<mu> domE.map_simp by force
          show "cod (?\<mu> j) = D (J.cod j)" using j \<mu> D.preserves_cod by simp
          show "C (D j) (?\<mu> (J.dom j)) = ?\<mu> j" using j e \<pi>o_in_hom D.preserves_hom by fastforce
          show "C (?\<mu> (J.cod j)) (domE.map j) = ?\<mu> j" using j e E' by auto
        qed
        text{*
          If @{term \<tau>} is any cone over @{term D} then @{term \<tau>} restricts to a cone over
          @{term \<Delta>o} for which the induced arrow to @{term \<Pi>o} equalizes @{term f} and @{term g}.
        *}
        have R: "\<And>a \<tau>. cone J C D a \<tau> \<Longrightarrow>
                        cone Obj.comp C \<Delta>o.map a (\<Delta>o.mkCone \<tau>) \<and>
                        C ?f (\<pi>o.induced_arrow a (\<Delta>o.mkCone \<tau>))
                           = C ?g (\<pi>o.induced_arrow a (\<Delta>o.mkCone \<tau>))"
        proof -
          fix a \<tau>
          assume cone_\<tau>: "cone J C D a \<tau>"
          interpret \<tau>: cone J C D a \<tau> using cone_\<tau> by auto
          interpret A: constant_functor Obj.comp C a
            apply unfold_locales using \<tau>.ide_apex by auto
          interpret \<tau>o: cone Obj.comp C \<Delta>o.map a "\<Delta>o.mkCone \<tau>"
            apply unfold_locales
            (* 5 *) using A.value_is_ide apply simp_all
            (* 2 *) using \<Delta>o.map_def by auto
          let ?e = "\<pi>o.induced_arrow a (\<Delta>o.mkCone \<tau>)"
          have mkCone_\<tau>: "\<Delta>o.mkCone \<tau> \<in> \<Delta>o.cones a"
          proof -
            have "\<And>j. Obj.arr j \<Longrightarrow> \<tau> j \<in> hom a (\<Delta>o.map j)"
              using Obj.arr_char \<tau>.preserves_hom \<tau>.A.map_def restrict_apply \<Delta>o.map_def
              by simp
            thus ?thesis
              using \<tau>.ide_apex \<Delta>o.cone_mkCone [of a \<tau>] by simp
          qed
          have e: "?e \<in> hom a \<Pi>o"
            using mkCone_\<tau> \<pi>o.induced_arrowI [of "\<Delta>o.mkCone \<tau>" a] by simp
          have ee: "\<And>j. J.ide j \<Longrightarrow> C (\<pi>o j) ?e = \<tau> j"
          proof -
            fix j
            assume j: "J.ide j"
            have "C (\<pi>o j) ?e = \<Delta>o.cones_map ?e \<pi>o j"
              using j e \<pi>o.cone_axioms by simp
            also have "... = \<Delta>o.mkCone \<tau> j"
              using j mkCone_\<tau> \<pi>o.induced_arrowI [of "\<Delta>o.mkCone \<tau>" a] by fastforce
            also have "... = \<tau> j"
              using j by simp
            finally show "C (\<pi>o j) ?e = \<tau> j" by auto
          qed
          have "\<And>j. J.arr j \<Longrightarrow> C (C (D (J.cod j)) (C (\<pi>o (J.cod j)) ?e)) (dom ?e)
                                   = C (D j) (C (\<pi>o (J.dom j)) ?e)"
          proof -
            fix j
            assume j: "J.arr j"
            have 1: "\<pi>o (J.cod j) \<in> hom \<Pi>o (D (J.cod j))" using j \<pi>o_in_hom by simp
            have "C (C (D (J.cod j)) (C (\<pi>o (J.cod j)) ?e)) (dom ?e)
                    = C (D (J.cod j)) (C (\<pi>o (J.cod j)) ?e)"
            proof -
              have "arr ?e" using e by blast
              moreover have "seq (D (J.cod j)) (\<pi>o (J.cod j))" using j e 1 by simp
              moreover have "seq (\<pi>o (J.cod j)) ?e" using j e 1 by blast
              ultimately show ?thesis by auto
            qed
            also have "... = C (\<pi>o (J.cod j)) ?e"
              using j e 1 D.preserves_ide [of "J.cod j"] by simp
            also have "... = C (D j) (C (\<pi>o (J.dom j)) ?e)"
              using j ee \<tau>.is_natural_1 [of j] \<tau>.is_natural_2 [of j] \<tau>.A.map_simp [of j]
                    \<tau>.ide_apex
              by simp
            finally show "C (C (D (J.cod j)) (C (\<pi>o (J.cod j)) ?e)) (dom ?e)
                            = C (D j) (C (\<pi>o (J.dom j)) ?e)"
              by auto
          qed
          hence "C ?f ?e = C ?g ?e"
            using E' \<pi>o.induced_arrowI \<tau>o.cone_axioms mem_Collect_eq by blast
          thus "cone Obj.comp C \<Delta>o.map a (\<Delta>o.mkCone \<tau>) \<and> C ?f ?e = C ?g ?e"
            using \<tau>o.cone_axioms by auto
        qed
        text{*
          Finally, show that @{term \<mu>} is a limit cone.
        *}
        interpret \<mu>: limit_cone J C D "dom e" ?\<mu>
        proof
          fix a \<tau>
          assume cone_\<tau>: "cone J C D a \<tau>"
          interpret \<tau>: cone J C D a \<tau> using cone_\<tau> by auto
          interpret A: constant_functor Obj.comp C a
            apply unfold_locales using \<tau>.ide_apex by auto
          have cone_\<tau>o: "cone Obj.comp C \<Delta>o.map a (\<Delta>o.mkCone \<tau>)"
            apply unfold_locales
            (* 5 *) using A.value_is_ide apply simp_all
            (* 2 *) using \<Delta>o.map_def by auto
          show "\<exists>!h. h \<in> hom a (dom e) \<and> D.cones_map h ?\<mu> = \<tau>"
          proof
            let ?e' = "\<pi>o.induced_arrow a (\<Delta>o.mkCone \<tau>)"
            have e': "?e' \<in> hom a \<Pi>o \<and> C ?f ?e' = C ?g ?e' \<and>
                     \<Delta>o.cones_map ?e' \<pi>o = \<Delta>o.mkCone \<tau>"
              using cone_\<tau> R \<pi>o.induced_arrowI [of "\<Delta>o.mkCone \<tau>" a] by auto
            have equ: "PP.is_equalized_by ?e'" using e' f by simp
            let ?h = "EQU.induced_arrow a (PP.mkCone ?e')"
            have h: "?h \<in> hom a (dom e) \<and> PP.cones_map ?h (PP.mkCone e) = PP.mkCone ?e'"
              using EQU.induced_arrowI [of "PP.mkCone ?e'" a] PP.cone_mkCone [of ?e'] e' equ
              by fastforce
            have 3: "D.cones_map ?h ?\<mu> = \<tau>"
            proof
              fix j
              have "\<not>J.arr j \<Longrightarrow> D.cones_map ?h ?\<mu> j = \<tau> j"
                using h \<mu>.cone_axioms cone_\<tau> by simp
              moreover have "J.arr j \<Longrightarrow> D.cones_map ?h ?\<mu> j = \<tau> j"
              proof -
                fix j
                assume j: "J.arr j"
                have "D.cones_map ?h ?\<mu> j = C (?\<mu> j) ?h"
                  using h j \<mu>.cone_axioms by simp
                also have "... = C (C (D j) (C (\<pi>o (J.dom j)) e)) ?h"
                  by simp
                also have "... = C (D j) (C (C (\<pi>o (J.dom j)) e) ?h)"
                  using j e h \<pi>o_in_hom by simp
                also have "... = C (D j) (\<tau> (J.dom j))"
                proof -
                  have "C (C (\<pi>o (J.dom j)) e) ?h = \<tau> (J.dom j)"
                  proof -
                    have "C (C (\<pi>o (J.dom j)) e) ?h = C (\<pi>o (J.dom j)) (C e ?h)"
                      using j e h \<pi>o by auto
                    also have "... = C (\<pi>o (J.dom j)) ?e'"
                      using e e' h EQU.induced_arrowI' [of ?e'] EQU.equalizes by simp
                    also have "... = \<Delta>o.cones_map ?e' \<pi>o (J.dom j)"
                      using j e' \<pi>o.cone_axioms by simp
                    also have "... = \<Delta>o.mkCone \<tau> (J.dom j)"
                      using j e' by presburger
                    also have "... = \<tau> (J.dom j)"
                      using j by simp
                    finally show ?thesis by auto
                  qed
                  thus ?thesis by simp
                qed
                also have "... = \<tau> j"
                  using j \<tau>.is_natural_1 by simp
                finally show "D.cones_map ?h ?\<mu> j = \<tau> j" by auto
              qed
              ultimately show "D.cones_map ?h ?\<mu> j = \<tau> j" by auto
            qed
            show "?h \<in> hom a (dom e) \<and> D.cones_map ?h ?\<mu> = \<tau>"
              using h 3 by simp
            show "\<And>h'. h' \<in> hom a (dom e) \<and> D.cones_map h' ?\<mu> = \<tau> \<Longrightarrow> h' = ?h"
            proof -
              fix h'
              assume h': "h' \<in> hom a (dom e) \<and> D.cones_map h' ?\<mu> = \<tau>"
              show "h' = ?h"
              proof -
                have 1: "C e h' \<in> hom a \<Pi>o \<and> C ?f (C e h') = C ?g (C e h') \<and>
                         \<Delta>o.cones_map (C e h') \<pi>o = \<Delta>o.mkCone \<tau>"
                proof -
                  have 2: "C e h' \<in> hom a \<Pi>o" using h' e by simp
                  moreover have "C ?f (C e h') = C ?g (C e h')"
                  proof -
                    have 1: "seq ?f e \<and> seq ?g e \<and> seq e h'" using e f g h' by simp
                    hence "C ?f (C e h') = C (C ?f e) h'"
                      using comp_assoc [of e h' ?f] by force
                    also have "... = C (C ?g e) h'"
                      using EQU.equalizes by presburger
                    also have "... = C ?g (C e h')"
                      using 1 comp_assoc [of e h' ?g] by blast
                    finally show ?thesis by auto
                  qed
                  moreover have "\<Delta>o.cones_map (C e h') \<pi>o = \<Delta>o.mkCone \<tau>"
                  proof
                    have "\<Delta>o.cones_map (C e h') \<pi>o = \<Delta>o.cones_map h' (\<Delta>o.cones_map e \<pi>o)"
                      using 2 \<pi>o.cone_axioms e h' \<Delta>o.cones_map_comp [of h' e] by simp
                    fix j
                    have "\<not>Obj.arr j \<Longrightarrow> \<Delta>o.cones_map (C e h') \<pi>o j = \<Delta>o.mkCone \<tau> j"
                      using 2 e h' \<pi>o.cone_axioms by simp
                    moreover have "Obj.arr j \<Longrightarrow> \<Delta>o.cones_map (C e h') \<pi>o j = \<Delta>o.mkCone \<tau> j"
                    proof -
                      assume j: "Obj.arr j"
                      have "\<Delta>o.cones_map (C e h') \<pi>o j = C (\<pi>o j) (C e h')"
                        using 2 j e h' \<pi>o.cone_axioms by auto
                      also have "... = C (C (\<pi>o j) e) h'"
                        using j e h' \<pi>o by simp
                      also have "... = C (\<Delta>o.mkCone ?\<mu> j) h'"
                        using j e h' \<pi>o_in_hom by auto
                      also have "... = \<Delta>o.mkCone \<tau> j"
                        using j h' J.ideD(1) \<mu>.cone_axioms mem_Collect_eq by auto
                      finally show "\<Delta>o.cones_map (C e h') \<pi>o j = \<Delta>o.mkCone \<tau> j" by auto
                    qed
                    ultimately show "\<Delta>o.cones_map (C e h') \<pi>o j = \<Delta>o.mkCone \<tau> j" by auto
                  qed
                  ultimately show ?thesis by auto
                qed
                hence "C e h' = ?e'"
                  using cone_\<tau>o e' \<pi>o.is_universal [of a "\<Delta>o.mkCone \<tau>"] \<pi>o by blast
                thus "h' = ?h"
                  using 1 h' EQU.is_universal' [of "C e h'"] EQU.induced_arrowI' [of ?e'] equ
                  by auto
              qed
            qed
          qed
        qed
        have "limit_cone J C D (dom e) ?\<mu>" ..
        thus "\<exists>a \<mu>. limit_cone J C D a \<mu>" by auto
      qed
      thus "\<forall>D. diagram J C D \<longrightarrow> (\<exists>a \<mu>. limit_cone J C D a \<mu>)" by blast
    qed

  end

  section "Limits in a Set Category"

  text{*
    In this section, we consider the special case of limits in a set category.
  *}

  locale diagram_in_set_category =
    J: category J +
    S: set_category S +
    diagram J S D
  for J :: "'j comp"
  and S :: "'s comp"
  and D :: "'j \<Rightarrow> 's"
  begin

    text{*
      An object @{term a} of a set category @{term S} is a limit of a diagram in @{term S}
      if and only if there is a bijection between the set @{term "S.hom S.unity a"} of points
      of @{term a} and the set of cones over the diagram that have apex @{term S.unity}.
    *}

    lemma limits_are_sets_of_cones:
    shows "has_as_limit a \<longleftrightarrow> S.ide a \<and> (\<exists>\<phi>. bij_betw \<phi> (S.hom S.unity a) (cones S.unity))"
    proof
      text{*
        If @{text "has_limit a"}, then by the universal property of the limit cone,
        composition in @{term S} yields a bijection between @{term "S.hom S.unity a"}
        and @{term "cones S.unity"}.
      *}
      assume a: "has_as_limit a"
      hence "S.ide a"
        using limit_cone_def cone.ide_apex by metis
      from a obtain \<chi> where \<chi>: "limit_cone a \<chi>" by auto
      interpret \<chi>: limit_cone J S D a \<chi> using \<chi> by auto
      have "bij_betw (\<lambda>f. cones_map f \<chi>) (S.hom S.unity a) (cones S.unity)"
        using \<chi>.bij_betw_hom_and_cones S.ide_unity by simp
      thus "S.ide a \<and> (\<exists>\<phi>. bij_betw \<phi> (S.hom S.unity a) (cones S.unity))"
        using `S.ide a` by blast
      next
      text{*
        Conversely, an arbitrary bijection @{term \<phi>} between @{term "S.hom S.unity a"}
        and cones unity extends pointwise to a natural bijection @{term "\<Phi> a'"} between
        @{term "S.hom a' a"} and @{term "cones a'"}, showing that @{term a} is a limit.

        In more detail, the hypotheses give us a correspondence between points of @{term a}
        and cones with apex @{term "S.unity"}.  We extend this to a correspondence between
        functions to @{term a} and general cones, with each arrow from @{term a'} to @{term a}
        determining a cone with apex @{term a'}.  If @{term "f \<in> hom a' a"} then composition
        with @{term f} takes each point @{term y} of @{term a'} to the point @{term "S f y"}
        of @{term a}.  To this we may apply the given bijection @{term \<phi>} to obtain
        @{term "\<phi> (S f y) \<in> cones S.unity"}.  The component @{term "\<phi> (S f y) j"} at @{term j}
        of this cone is a point of @{term "S.cod (D j)"}.  Thus, @{term "f \<in> hom a' a"} determines
        a cone @{term \<chi>f} with apex @{term a'} whose component at @{term j} is the
        unique arrow @{term "\<chi>f j"} of @{term S} such that @{term "\<chi>f j \<in> hom a' (cod (D j))"}
        and @{term "S (\<chi>f j) y = \<phi> (S f y) j"} for all points @{term y} of @{term a'}.
        The cone @{term \<chi>a} corresponding to @{term "a \<in> S.hom a a"} is then a limit cone.
      *}
      assume a: "S.ide a \<and> (\<exists>\<phi>. bij_betw \<phi> (S.hom S.unity a) (cones S.unity))"
      hence "S.ide a" by auto
      show "has_as_limit a"
      proof -
        from a obtain \<phi> where \<phi>: "bij_betw \<phi> (S.hom S.unity a) (cones S.unity)" by blast
        have X: "\<And>f j y. \<lbrakk> f \<in> S.hom (S.dom f) a; J.arr j; y \<in> S.hom S.unity (S.dom f) \<rbrakk>
                                \<Longrightarrow> \<phi> (S f y) j \<in> S.hom S.unity (S.cod (D j))"
        proof -
          fix f j y
          assume f: "f \<in> S.hom (S.dom f) a" and j: "J.arr j" and y: "y \<in> S.hom S.unity (S.dom f)"
          interpret \<chi>: cone J S D S.unity "\<phi> (S f y)"
          proof -
            have "S f y \<in> S.hom S.unity a" using f y by auto
            hence "\<phi> (S f y) \<in> cones S.unity"
              using \<phi> bij_betw_imp_funcset funcset_mem by blast
            thus "cone S.unity (\<phi> (S f y))" by simp
          qed
          show "\<phi> (S f y) j \<in> S.hom S.unity (S.cod (D j))" using j by simp
        qed
        text{*
          We want to define the component @{term "\<chi>j \<in> S.hom (S.dom f) (S.cod (D j))"}
          at @{term j} of a cone by specifying how it acts by composition on points
          @{term "y \<in> S.hom S.unity (S.dom f)"}.  We can do this because @{term S}
          is a set category.
        *}
        let ?P = "\<lambda>f j \<chi>j. \<chi>j \<in> S.hom (S.dom f) (S.cod (D j)) \<and>
                           (\<forall>y. y \<in> S.hom S.unity (S.dom f) \<longrightarrow> S \<chi>j y = \<phi> (S f y) j)"
        let ?\<chi> = "\<lambda>f j. if J.arr j then (THE \<chi>j. ?P f j \<chi>j) else S.null"
        have \<chi>: "\<And>f j. \<lbrakk> f \<in> S.hom (S.dom f) a; J.arr j \<rbrakk> \<Longrightarrow> ?P f j (?\<chi> f j)"
        proof -
          fix b f j
          assume f: "f \<in> S.hom (S.dom f) a" and j: "J.arr j"
          interpret B: constant_functor J S "S.dom f"
            apply unfold_locales using f by auto
          have "(\<lambda>y. \<phi> (S f y) j) \<in> S.hom S.unity (S.dom f) \<rightarrow> S.hom S.unity (S.cod (D j))"
            using f j X [of f j] Pi_I' by simp
          hence "\<exists>!\<chi>j. ?P f j \<chi>j"
            using f j S.fun_complete' [of "S.dom f" "S.cod (D j)" "\<lambda>y. \<phi> (S f y) j"] by simp
          thus "?P f j (?\<chi> f j)" using j theI' [of "?P f j"] by simp
        qed
        text{*
          The arrows @{term "\<chi> f j"} are in fact the components of a cone with apex
          @{term "S.dom f"}.
        *}
        have cone: "\<And>f. f \<in> S.hom (S.dom f) a \<Longrightarrow> cone (S.dom f) (?\<chi> f)"
        proof -
          fix f
          assume f: "f \<in> S.hom (S.dom f) a"
          interpret B: constant_functor J S "S.dom f"
            apply unfold_locales using f by auto
          show "cone (S.dom f) (?\<chi> f)"
          proof
            show "\<And>j. \<not>J.arr j \<Longrightarrow> ?\<chi> f j = S.null" by simp
            fix j
            assume j: "J.arr j"
            have 0: "?\<chi> f j \<in> S.hom (S.dom f) (S.cod (D j))" using f j \<chi> by simp
            show "S.dom (?\<chi> f j) = B.map (J.dom j)" using f j \<chi> by simp
            show "S.cod (?\<chi> f j) = D (J.cod j)" using f j \<chi> by simp
            have par1: "S.par (S (D j) (?\<chi> f (J.dom j))) (?\<chi> f j)"
              using f j \<chi> [of f "J.dom j"] \<chi> [of f j] by simp
            have par2: "S.par (S (?\<chi> f (J.cod j)) (B.map j)) (?\<chi> f j)"
                using f j \<chi> [of f "J.cod j"] \<chi> [of f j] by simp
            have nat: "\<And>y. y \<in> S.hom S.unity (S.dom f) \<Longrightarrow>
                              S (S (D j) (?\<chi> f (J.dom j))) y = S (?\<chi> f j) y \<and>
                              S (S (?\<chi> f (J.cod j)) (B.map j)) y = S (?\<chi> f j) y"
            proof -
              fix y
              assume y: "y \<in> S.hom S.unity (S.dom f)"
              show "S (S (D j) (?\<chi> f (J.dom j))) y = S (?\<chi> f j) y \<and>
                    S (S (?\<chi> f (J.cod j)) (B.map j)) y = S (?\<chi> f j) y"
              proof
                have 1: "\<phi> (S f y) \<in> cones S.unity"
                  using f y \<phi> bij_betw_imp_funcset PiE
                        S.arr_comp S.cod_comp S.dom_comp mem_Collect_eq
                  by fastforce
                interpret \<chi>: cone J S D S.unity "\<phi> (S f y)"
                  using 1 by simp
                have "S (S (D j) (?\<chi> f (J.dom j))) y = S (D j) (S (?\<chi> f (J.dom j)) y)"
                  using 0 par1 y S.comp_assoc' S.comp_null(2) S.match_1 S.not_arr_null
                  by (metis (no_types, lifting) )
                also have "... = S (D j) (\<phi> (S f y) (J.dom j))"
                  using f y \<chi> [of f "J.dom j"] by simp
                also have "... = \<phi> (S f y) j" using j by blast
                also have "... = S (?\<chi> f j) y"
                  using f j y \<chi> [of f j] by presburger
                finally show "S (S (D j) (?\<chi> f (J.dom j))) y = S (?\<chi> f j) y" by auto
                have "S (S (?\<chi> f (J.cod j)) (B.map j)) y = S (?\<chi> f (J.cod j)) y"
                  using j B.map_simp f \<chi> [of f "J.cod j"] by auto
                also have "... = \<phi> (S f y) (J.cod j)"
                  using f y \<chi> [of f "J.cod j"] by simp
                also have "... = \<phi> (S f y) j"
                  using j by (metis J.ideD(1) J.cod_cod J.ide_cod \<chi>.A.map_simp \<chi>.is_natural_2)
                also have "... = S (?\<chi> f j) y"
                  using f y \<chi> [of f j] by simp
                finally show "S (S (?\<chi> f (J.cod j)) (B.map j)) y = S (?\<chi> f j) y" by auto
              qed
            qed
            show "S (D j) (?\<chi> f (J.dom j)) = ?\<chi> f j"
              apply (intro S.arr_eqI' [of "S (D j) (?\<chi> f (J.dom j))" "?\<chi> f j"])
              using par1 nat f j \<chi> by auto
            show "S (?\<chi> f (J.cod j)) (B.map j) = ?\<chi> f j"
              apply (intro S.arr_eqI' [of "S (?\<chi> f (J.cod j)) (B.map j)" "?\<chi> f j"])
              using par2 nat f j \<chi> by auto
          qed
        qed
        interpret \<chi>a: cone J S D a "?\<chi> a" using a cone [of a] by auto
        text{*
          Finally, show that @{text "\<chi> a"} is a limit cone.
        *}
        interpret \<chi>a: limit_cone J S D a "?\<chi> a"
        proof
          fix a' \<chi>'
          assume cone_\<chi>': "cone a' \<chi>'"
          interpret \<chi>': cone J S D a' \<chi>' using cone_\<chi>' by auto
          show "\<exists>!f. f \<in> S.hom a' a \<and> cones_map f (?\<chi> a) = \<chi>'"
          proof
            let ?\<psi> = "inv_into (S.hom S.unity a) \<phi>"
            have \<psi>: "?\<psi> \<in> cones S.unity \<rightarrow> S.hom S.unity a"
              using \<phi> bij_betw_inv_into bij_betwE by blast
            let ?P = "\<lambda>f. f \<in> S.hom a' a \<and>
                          (\<forall>y. y \<in> S.hom S.unity a' \<longrightarrow> S f y = ?\<psi> (cones_map y \<chi>'))"
            have 1: "\<exists>!f. ?P f"
            proof -
              have "(\<lambda>y. ?\<psi> (cones_map y \<chi>')) \<in> S.hom S.unity a' \<rightarrow> S.hom S.unity a"
                using cone_\<chi>' cones_map_mapsto \<psi> by force
              thus ?thesis
                 using S.fun_complete' [of a' a "\<lambda>y. ?\<psi> (cones_map y \<chi>')"] a \<chi>'.ide_apex
                 by simp
            qed
            let ?f = "THE f. ?P f"
            have f: "?P ?f" using 1 theI' [of ?P] by simp
            show "?f \<in> S.hom a' a \<and> cones_map ?f (?\<chi> a) = \<chi>'"
            proof
              show 0: "?f \<in> S.hom a' a" using f by auto
              show "cones_map ?f (?\<chi> a) = \<chi>'"
              proof
                fix j
                have "\<not>J.arr j \<Longrightarrow> cones_map ?f (?\<chi> a) j = \<chi>' j"
                  using f a \<chi>'.is_extensional by (simp add: \<chi>a.cone_axioms restrict_apply')
                moreover have "J.arr j \<Longrightarrow> cones_map ?f (?\<chi> a) j = \<chi>' j"
                proof -
                  assume j: "J.arr j"
                  show "cones_map ?f (?\<chi> a) j = \<chi>' j"
                  proof (intro S.arr_eqI' [of "cones_map ?f (?\<chi> a) j" "\<chi>' j"])
                    have 1: "cones_map ?f (?\<chi> a) j \<in> S.hom a' (D (J.cod j))"
                      using 0 \<chi>a.cone_axioms j \<chi>a.preserves_hom by force
                    show par: "S.par (cones_map ?f (?\<chi> a) j) (\<chi>' j)"
                      using 1 \<chi>'.preserves_hom j by simp (* 20 sec *)
                   fix y
                    assume "y \<in> S.hom S.unity (S.dom (cones_map ?f (?\<chi> a) j))"
                    hence y: "y \<in> S.hom S.unity a'"
                      using 0 \<chi>a.cone_axioms j \<chi>a.preserves_hom by force
                    have 1: "?\<chi> a j \<in> S.hom a (D (J.cod j))"
                      using j \<chi>a.preserves_hom by simp
                    have 2: "S ?f y \<in> S.hom S.unity a"
                      using 0 y by auto
                    have "S (cones_map ?f (?\<chi> a) j) y = S (S (?\<chi> a j) ?f) y"
                      using 2 f j a \<chi>a.cone_axioms by simp
                    also have "... = S (?\<chi> a j) (S ?f y)"
                      using 1 f y by simp
                    also have "... = \<phi> (S a (S ?f y)) j"
                      using 1 2 a f j y \<chi> [of a] by simp
                    also have "... = \<phi> (S ?f y) j"
                      using a 2 y by auto
                    also have "... = \<phi> (?\<psi> (cones_map y \<chi>')) j"
                      using j y f by simp
                    also have "... = cones_map y \<chi>' j"
                    proof -
                      have "cones_map y \<chi>' \<in> cones S.unity"
                        using cone_\<chi>' y cones_map_mapsto [of y] by force
                      hence "\<phi> (?\<psi> (cones_map y \<chi>')) = cones_map y \<chi>'"
                        using \<phi> bij_betw_inv_into_right [of \<phi>] by simp
                      thus ?thesis by auto
                    qed
                    also have "... = S (\<chi>' j) y"
                      using cone_\<chi>' j y by simp
                    finally show "S (cones_map ?f (?\<chi> a) j) y = S (\<chi>' j) y"
                      by auto
                  qed
                qed
                ultimately show "cones_map ?f (?\<chi> a) j = \<chi>' j" by blast
              qed
            qed
            show "\<And>f'. f' \<in> S.hom a' a \<and> cones_map f' (?\<chi> a) = \<chi>' \<Longrightarrow> f' = ?f"
            proof -
              fix f'
              assume f': "f' \<in> S.hom a' a \<and> cones_map f' (?\<chi> a) = \<chi>'"
              show "f' = ?f"
              proof (intro S.arr_eqI' [of f' ?f])
                show "S.par f' ?f" using f f' by simp
                show "\<And>y'. y' \<in> S.hom S.unity (S.dom f') \<Longrightarrow> S f' y' = S ?f y'"
                proof -
                  fix y'
                  assume y': "y' \<in> S.hom S.unity (S.dom f')"
                  have 0: "\<phi> (S f' y') = cones_map y' \<chi>'"
                  proof
                    fix j
                    have 1: "S f' y' \<in> S.hom S.unity a" using f' y' by simp
                    hence 2: "\<phi> (S f' y') \<in> cones S.unity"
                      using \<phi> bij_betw_imp_funcset [of \<phi> "S.hom S.unity a" "cones S.unity"]
                      by auto
                    interpret \<chi>'': cone J S D S.unity "\<phi> (S f' y')" using 2 by auto
                    have "\<not>J.arr j \<Longrightarrow> \<phi> (S f' y') j = cones_map y' \<chi>' j"
                      using f' y' cone_\<chi>' \<chi>''.is_extensional mem_Collect_eq restrict_apply by auto
                    moreover have "J.arr j \<Longrightarrow> \<phi> (S f' y') j = cones_map y' \<chi>' j"
                    proof -
                      assume j: "J.arr j"
                      have 3: "?\<chi> a j \<in> S.hom a (D (J.cod j))"
                        using j \<chi>a.preserves_hom by simp
                      have "\<phi> (S f' y') j = \<phi> (S a (S f' y')) j"
                        using a f' y' j by simp
                      also have "... = S (?\<chi> a j) (S f' y')"
                        using 1 3 \<chi> [of a] a f' y' j by simp
                      also have "... = S (S (?\<chi> a j) f') y'"
                        using 3 a f' y' j by simp
                      also have "... = S (cones_map f' (?\<chi> a) j) y'"
                        using f' y' j \<chi>a.cone_axioms by simp
                      also have "... = S (\<chi>' j) y'"
                        using f' by blast
                      also have "... = cones_map y' \<chi>' j"
                        using y' j cone_\<chi>' f' mem_Collect_eq restrict_apply by auto
                      finally show "\<phi> (S f' y') j = cones_map y' \<chi>' j" by auto
                    qed
                    ultimately show "\<phi> (S f' y') j = cones_map y' \<chi>' j" by auto
                  qed
                  hence "S f' y' = ?\<psi> (cones_map y' \<chi>')"
                    using \<phi> 1 cone_\<chi>' f' y'
                          bij_betw_inv_into_left [of \<phi> "S.hom S.unity a" "cones S.unity" "S f' y'"]
                    by simp
                  moreover have "S ?f y' = ?\<psi> (cones_map y' \<chi>')"
                    using 0 1 f f' y' \<phi>
                          bij_betw_inv_into_left [of \<phi> "S.hom S.unity a" "cones S.unity"
                                                       "S ?f y'"]
                    by simp
                  ultimately show "S f' y' = S ?f y'" by auto
                qed
              qed
            qed
          qed
        qed
        have "limit_cone a (?\<chi> a)" ..
        thus ?thesis by auto
      qed
    qed

  end

  context set_category
  begin

    text{*
      A set category has an equalizer for any parallel pair of arrows.
    *}

    lemma has_equalizers:
    shows "has_equalizers"
    proof (unfold has_equalizers_def)
      have "\<And>f0 f1. par f0 f1 \<Longrightarrow> \<exists>e. has_as_equalizer f0 f1 e"
      proof -
        fix f0 f1
        assume par: "par f0 f1"
        interpret J: parallel_pair
          apply unfold_locales by auto
        interpret PP: parallel_pair_diagram S f0 f1
          apply unfold_locales using par by auto
        interpret PP: diagram_in_set_category J.comp S PP.map ..
        text{*
          Let @{term a} be the object corresponding to the set of all images of equalizing points
          of @{term "dom f0"}, and let @{term e} be the inclusion of @{term a} in @{term "dom f0"}.
        *}
        let ?a = "mkIde (img ` {e. e \<in> hom unity (dom f0) \<and> S f0 e = S f1 e})"
        have "{e. e \<in> hom unity (dom f0) \<and> S f0 e = S f1 e} \<subseteq> hom unity (dom f0)"
          by auto
        hence 1: "img ` {e. e \<in> hom unity (dom f0) \<and> S f0 e = S f1 e} \<subseteq> Univ"
          using img_point_in_Univ by auto
        have ide_a: "ide ?a" using 1 by auto
        have set_a: "set ?a = img ` {e. e \<in> hom unity (dom f0) \<and> S f0 e = S f1 e}"
          using 1 by simp
        have incl_in_a: "incl_in ?a (dom f0)"
        proof -
          have "ide (dom f0)"
            using PP.is_parallel by simp
          moreover have "set ?a \<subseteq> set (dom f0)"
          proof -
            have "set ?a = img ` {e. e \<in> hom unity (dom f0) \<and> S f0 e = S f1 e}"
              using set_mkIde img_point_in_Univ
              by (metis (no_types, lifting) arr_mkIde ideD(1) ide_a)
            thus ?thesis
              using imageE img_point_elem_set mem_Collect_eq subsetI by auto
          qed
          ultimately show ?thesis
            using incl_in_def `ide ?a` by simp
        qed
        text{*
          Then @{term "set a"} is in bijective correspondence with @{term "PP.cones unity"}.
        *}
        let ?\<phi> = "\<lambda>t. PP.mkCone (mkPoint (dom f0) t)"
        let ?\<psi> = "\<lambda>\<chi>. img (\<chi> (J.Zero))"
        have bij: "bij_betw ?\<phi> (set ?a) (PP.cones unity)"
        proof (intro bij_betwI)
          show "?\<phi> \<in> set ?a \<rightarrow> PP.cones unity"
          proof
            fix t
            assume t: "t \<in> set ?a"
            hence 1: "t \<in> img ` {e. e \<in> hom unity (dom f0) \<and> S f0 e = S f1 e}"
              using set_a by blast
            then have 2: "mkPoint (dom f0) t \<in> hom unity (dom f0)"
              using mkPoint_in_hom imageE mem_Collect_eq mkPoint_img(2) by auto
            with 1 have 3: "mkPoint (dom f0) t \<in> {e. e \<in> hom unity (dom f0) \<and> S f0 e = S f1 e}"
              using mkPoint_img(2) by auto
            then have "PP.is_equalized_by (mkPoint (dom f0) t)"
              using CollectD par by blast
            thus "PP.mkCone (mkPoint (dom f0) t) \<in> PP.cones unity"
              using 2 PP.cone_mkCone [of "mkPoint (dom f0) t"] by simp
          qed
          show "?\<psi> \<in> PP.cones unity \<rightarrow> set ?a"
          proof
            fix \<chi>
            assume \<chi>: "\<chi> \<in> PP.cones unity"
            interpret \<chi>: cone J.comp S PP.map unity \<chi> using \<chi> by auto
            have "\<chi> (J.Zero) \<in> hom unity (dom f0) \<and> S f0 (\<chi> (J.Zero)) = S f1 (\<chi> (J.Zero))"
              using \<chi> PP.map_def PP.is_equalized_by_cone
              by (simp add: J.arr_char J.dom_char \<chi>.A.map_def \<chi>.natural_transformation_axioms
                  natural_transformation.preserves_dom)
            hence "img (\<chi> (J.Zero)) \<in> set ?a"
              using set_a by simp
            thus "?\<psi> \<chi> \<in> set ?a" by blast
          qed
          show "\<And>t. t \<in> set ?a \<Longrightarrow> ?\<psi> (?\<phi> t) = t"
            using set_a J.arr_char PP.mkCone_def imageE mem_Collect_eq mkPoint_img(2) by auto
          show "\<And>\<chi>. \<chi> \<in> PP.cones unity \<Longrightarrow> ?\<phi> (?\<psi> \<chi>) = \<chi>"
          proof -
            fix \<chi>
            assume \<chi>: "\<chi> \<in> PP.cones unity"
            interpret \<chi>: cone J.comp S PP.map unity \<chi> using \<chi> by auto
            have "\<chi> (J.Zero) \<in> hom unity (dom f0) \<and> S f0 (\<chi> (J.Zero)) = S f1 (\<chi> (J.Zero))"
              using \<chi> PP.map_def PP.is_equalized_by_cone
              by (simp add: J.arr_char J.dom_char \<chi>.A.map_def \<chi>.natural_transformation_axioms
                  natural_transformation.preserves_dom)
            hence "img (\<chi> (J.Zero)) \<in> set ?a"
              using set_a by simp
            hence "img (\<chi> (J.Zero)) \<in> set (dom f0)"
              using incl_in_a incl_in_def by auto
            hence "mkPoint (dom f0) (img (\<chi> J.Zero)) = \<chi> J.Zero"
              using mkPoint_img(2) [of "\<chi> J.Zero" "dom f0"]
                    \<open>\<chi> J.Zero \<in> hom unity (local.dom f0) \<and> S f0 (\<chi> J.Zero) = S f1 (\<chi> J.Zero)\<close>
              by blast
            hence "?\<phi> (?\<psi> \<chi>) = PP.mkCone (\<chi> J.Zero)" by simp
            also have "... = \<chi>"
              using \<chi> PP.mkCone_cone by simp
            finally show "?\<phi> (?\<psi> \<chi>) = \<chi>" by auto
          qed
        qed
        text{*
          It follows that @{term a} is a limit of @{text PP}, and that the limit cone gives an
          equalizer of @{term f0} and @{term f1}.
        *}
        have "\<exists>\<mu>. bij_betw \<mu> (hom unity ?a) (set ?a)"
          using bij_betw_points_and_set [of ?a] ide_a by auto
        from this obtain \<mu> where \<mu>: "bij_betw \<mu> (hom unity ?a) (set ?a)" by blast
        have "bij_betw (?\<phi> o \<mu>) (hom unity ?a) (PP.cones unity)"
          using bij \<mu> bij_betw_comp_iff by blast
        hence "\<exists>\<phi>. bij_betw \<phi> (hom unity ?a) (PP.cones unity)" by auto
        hence "PP.has_as_limit ?a"
          using ide_a PP.limits_are_sets_of_cones [of ?a] by simp
        (* TODO: The rest of this is kind of cumbersome, and needs to be looked into. *)
        from this obtain \<epsilon> where \<epsilon>: "limit_cone J.comp S PP.map ?a \<epsilon>" by auto
        interpret \<epsilon>: limit_cone J.comp S PP.map ?a \<epsilon> using \<epsilon> by auto
        have "cone J.comp S PP.map ?a \<epsilon>" ..
        hence "PP.mkCone (\<epsilon> (J.Zero)) = \<epsilon>"
          using \<epsilon> PP.mkCone_cone [of ?a \<epsilon>] by simp
        moreover have "dom (\<epsilon> (J.Zero)) = ?a"
          using J.ide_char \<epsilon>.preserves_hom [of J.Zero J.Zero J.Zero] \<epsilon>.A.map_def by simp
        ultimately have "PP.has_as_equalizer (\<epsilon> J.Zero)"
          using \<epsilon> by simp
        thus "\<exists>e. has_as_equalizer f0 f1 e"
          using par has_as_equalizer_def by auto   
      qed
      thus "\<forall>f0 f1. par f0 f1 \<longrightarrow> (\<exists>e. has_as_equalizer f0 f1 e)" by auto
    qed

  end

  sublocale set_category \<subseteq> category_with_equalizers S
    apply unfold_locales using has_equalizers by auto

  context set_category
  begin

    text{*
      The aim of the next results is to characterize the conditions under which a set
      category has products.  In a traditional development of category theory,
      one shows that the category \textbf{Set} of \emph{all} sets has all small
      (\emph{i.e.}~set-indexed) products.  In the present context we do not have a
      category of \emph{all} sets, but rather only a category of all sets with
      elements at a particular type.  Clearly, we cannot expect such a category
      to have products indexed by arbitrarily large sets.  The existence of
      @{term I}-indexed products in a set category @{term S} implies that the universe
      @{text S.Univ} of @{term S} must be large enough to admit the formation of
      @{term I}-tuples of its elements.  Conversely, for a set category @{term S}
      the the ability to form @{term I}-tuples in @{term Univ} implies that
      @{term S} has @{term I}-indexed products.  Below we make this precise by
      defining the notion of when a set category @{term S} ``admits @{term I}-indexed tupling''
      and we show that @{term S} has @{term I}-indexed products if and only if it admits
      @{term I}-indexed tupling.

      The definition of ``@{term S} admits @{term I}-indexed tupling'' says that
      there is an injective map, from the space of extensional functions from
      @{term I} to @{term Univ}, to @{term Univ}.  However for a convenient
      statement and proof of the desired result, the definition of extensional
      function from theory @{theory FuncSet} needs to be modified.
      The theory @{theory FuncSet} uses the definite, but arbitrarily chosen value
      @{term undefined} as the value to be assumed by an extensional function outside
      of its domain.  In the context of the @{text set_category}, though, it is
      more natural to use @{text S.unity}, which is guaranteed to be an element of the
      universe of @{term S}, for this purpose.  Doing things that way makes it simpler to
      establish a bijective correspondence between cones over @{term D} with apex
      @{term unity} and the set of extensional functions @{term d} that map
      each arrow @{term j} of @{term J} to an element @{term "d j"} of @{term "set (D j)"}.
      Possibly it makes sense to go back and make this change in @{text set_category},
      but that would mean completely abandoning @{theory FuncSet} and essentially
      introducing a duplicate version for use with @{text set_category}.
      As a compromise, what I have done here is to locally redefine the few notions from
      @{theory FuncSet} that I need in order to prove the next set of results.
    *}

    definition extensional
    where "extensional A \<equiv> {f. \<forall>x. x \<notin> A \<longrightarrow> f x = unity}"

    abbreviation PiE
    where "PiE A B \<equiv> Pi A B \<inter> extensional A"

    abbreviation restrict
    where "restrict f A \<equiv> \<lambda>x. if x \<in> A then f x else unity"

    lemma extensionalI [intro]:
    assumes "\<And>x. x \<notin> A \<Longrightarrow> f x = unity"
    shows "f \<in> extensional A"
      using assms extensional_def by auto

    lemma extensional_arb:
    assumes "f \<in> extensional A" and "x \<notin> A"
    shows "f x = unity"
      using assms extensional_def by fast

    lemma extensional_monotone:
    assumes "A \<subseteq> B"
    shows "extensional A \<subseteq> extensional B"
    proof
      fix f
      assume f: "f \<in> extensional A"
      have 1: "\<forall>x. x \<notin> A \<longrightarrow> f x = unity" using f extensional_def by fast
      hence "\<forall>x. x \<notin> B \<longrightarrow> f x = unity" using assms by auto
      thus "f \<in> extensional B" using extensional_def by blast
    qed

    lemma PiE_mono: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x) \<Longrightarrow> PiE A B \<subseteq> PiE A C"
      by auto

  end

  locale discrete_diagram_in_set_category =
    S: set_category S +
    discrete_diagram J S D +
    diagram_in_set_category J S D
  for J :: "'j comp"
  and S :: "'s comp"
  and D :: "'j \<Rightarrow> 's"
  begin

    text{*
      For @{term D} a discrete diagram in a set category, there is a bijective correspondence
      between cones over @{term D} with apex unity and the set of extensional functions @{term d}
      that map each arrow @{term j} of @{term J} to an element of @{term "S.set (D j)"}.
    *}

    abbreviation I
    where "I \<equiv> Collect J.arr"

    definition funToCone
    where "funToCone F \<equiv> \<lambda>j. if J.arr j then S.mkPoint (D j) (F j) else S.null"

    definition coneToFun
    where "coneToFun \<chi> \<equiv> \<lambda>j. if J.arr j then S.img (\<chi> j) else S.unity"

    lemma funToCone_mapsto:
    shows "funToCone \<in> S.PiE I (S.set o D) \<rightarrow> cones S.unity"
    proof
      fix F
      assume F: "F \<in> S.PiE I (S.set o D)"
      interpret U: constant_functor J S S.unity
        apply unfold_locales using S.ide_unity by auto
      have 1: "S.ide (S.mkIde S.Univ)" by simp
      have "cone S.unity (funToCone F)"
      proof
        show "\<And>j. \<not>J.arr j \<Longrightarrow> funToCone F j = S.null"
          using funToCone_def by simp
        fix j
        assume j: "J.arr j"
        have "funToCone F j = S.mkPoint (D j) (F j)"
          using j funToCone_def by simp
        moreover have "... \<in> S.hom S.unity (D j)"
        proof -
          have "F j \<in> S.set (D j)"
            using F j by auto
          thus ?thesis
            using j is_discrete S.img_mkPoint(1) [of "D j"] by auto
        qed
        ultimately have 2: "funToCone F j \<in> S.hom S.unity (D j)" by auto
        show 3: "S.dom (funToCone F j) = U.map (J.dom j)"
          using 2 j U.map_simp by simp
        show 4: "S.cod (funToCone F j) = D (J.cod j)"
          using 2 j is_discrete by simp
        show "S (D j) (funToCone F (J.dom j)) = funToCone F j"
          using 4 j is_discrete by simp
        show "S (funToCone F (J.cod j)) (U.map j) = funToCone F j"
          using 3 j is_discrete U.map_simp by simp
      qed
      thus "funToCone F \<in> cones S.unity" by auto
    qed

    lemma coneToFun_mapsto:
    shows "coneToFun \<in> cones S.unity \<rightarrow> S.PiE I (S.set o D)"
    proof
      fix \<chi>
      assume \<chi>: "\<chi> \<in> cones S.unity"
      interpret \<chi>: cone J S D S.unity \<chi> using \<chi> by auto
      show "coneToFun \<chi> \<in> S.PiE I (S.set o D)"
      proof
        show "coneToFun \<chi> \<in> Pi I (S.set o D)"
        proof
          fix i
          assume i: "i \<in> I"
          show "coneToFun \<chi> i \<in> (S.set o D) i"
          proof -
            have "(S.set o D) i = S.set (D i)" by simp
            moreover have "\<chi> i \<in> S.hom S.unity (D i)"
              using i is_discrete \<chi>.component_in_hom by auto
            ultimately show ?thesis
              using i S.mkPoint_img(1) [of "D i"] coneToFun_def [of \<chi>]
              by (simp add: S.img_point_elem_set restrict_apply')
          qed
        qed
        show "coneToFun \<chi> \<in> S.extensional I"
        proof
          fix x
          show "x \<notin> I \<Longrightarrow> coneToFun \<chi> x = S.unity"
            using coneToFun_def by simp
        qed
      qed
    qed

    lemma funToCone_coneToFun:
    assumes "\<chi> \<in> cones S.unity"
    shows "funToCone (coneToFun \<chi>) = \<chi>"
    proof
      interpret \<chi>: cone J S D S.unity \<chi> using assms by auto
      fix j
      have "\<not>J.arr j \<Longrightarrow> funToCone (coneToFun \<chi>) j = \<chi> j"
        using funToCone_def \<chi>.is_extensional by simp
      moreover have "J.arr j \<Longrightarrow> funToCone (coneToFun \<chi>) j = \<chi> j"
      proof -
        assume j: "J.arr j"
        have "funToCone (coneToFun \<chi>) j = S.mkPoint (D j) (coneToFun \<chi> j)"
          using j funToCone_def by auto
        also have "... = S.mkPoint (D j) (S.img (\<chi> j))"
          using j coneToFun_def [of \<chi>] by simp
        also have "... = \<chi> j"
          using j S.mkPoint_img(2) [of "\<chi> j"] \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                \<chi>.A.map_simp [of "J.dom j"] is_discrete
                preserves_ide [of j] J.ideD(3) \<chi>.component_in_hom
          by auto
        finally show "funToCone (coneToFun \<chi>) j = \<chi> j" by auto
      qed
      ultimately show "funToCone (coneToFun \<chi>) j = \<chi> j" by blast
    qed

    lemma coneToFun_funToCone:
    assumes "F \<in> S.PiE I (S.set o D)"
    shows "coneToFun (funToCone F) = F"
    proof
      fix i
      have "i \<notin> I \<Longrightarrow> coneToFun (funToCone F) i = F i"
      proof -
        assume i: "i \<notin> I"
        have "coneToFun (funToCone F) i = S.unity"
          using i coneToFun_def by simp
        also have "... = F i"
          using i assms S.extensional_arb [of F I i] by auto
        finally show ?thesis by auto
      qed
      moreover have "i \<in> I \<Longrightarrow> coneToFun (funToCone F) i = F i"
      proof -
        assume i: "i \<in> I"
        have "coneToFun (funToCone F) i = S.img (funToCone F i)"
          using i coneToFun_def by simp
        also have "... = S.img (S.mkPoint (D i) (F i))"
          using i funToCone_def by auto
        also have "... = F i"
        proof -
          have 1: "F i \<in> S.set (D i)"
            using assms i by auto
          then show ?thesis
            using i is_discrete by (simp add: S.img_mkPoint(2))
        qed
        finally show "coneToFun (funToCone F) i = F i" by auto
      qed
      ultimately show "coneToFun (funToCone F) i = F i" by auto
    qed

    lemma bij_coneToFun:
    shows "bij_betw coneToFun (cones S.unity) (S.PiE I (S.set o D))"
      using coneToFun_mapsto funToCone_mapsto funToCone_coneToFun coneToFun_funToCone bij_betwI
      by blast

    lemma bij_funToCone:
    shows "bij_betw funToCone (S.PiE I (S.set o D)) (cones S.unity)"
      using coneToFun_mapsto funToCone_mapsto funToCone_coneToFun coneToFun_funToCone bij_betwI
      by blast
 
  end

  context set_category
  begin

    text{*
      A set category admits @{term I}-indexed tupling if there is an injective map that takes
      each extensional function from @{term I} to @{term Univ} to an element of @{term Univ}.
    *}

    definition admits_tupling
    where "admits_tupling I \<equiv> \<exists>\<pi>. \<pi> \<in> PiE I (\<lambda>_. Univ) \<rightarrow> Univ \<and> inj_on \<pi> (PiE I (\<lambda>_. Univ))"

    lemma admits_tupling_monotone:
    assumes "admits_tupling I" and "I' \<subseteq> I"
    shows "admits_tupling I'"
    proof -
      from assms(1) obtain \<pi> where \<pi>: "\<pi> \<in> PiE I (\<lambda>_. Univ) \<rightarrow> Univ \<and> inj_on \<pi> (PiE I (\<lambda>_. Univ))"
        using admits_tupling_def by blast
      have "\<pi> \<in> PiE I' (\<lambda>_. Univ) \<rightarrow> Univ"
      proof
        fix f
        assume f: "f \<in> PiE I' (\<lambda>_. Univ)"
        have "f \<in> PiE I (\<lambda>_. Univ)"
          using assms(2) f extensional_def [of I'] terminal_unity extensional_monotone by auto
        thus "\<pi> f \<in> Univ" using \<pi> by auto
      qed
      moreover have "inj_on \<pi> (PiE I' (\<lambda>_. Univ))"
      proof -
        have 1: "\<And>F A A'. inj_on F A \<and> A' \<subseteq> A \<Longrightarrow> inj_on F A'"
          using subset_inj_on by blast
        moreover have "PiE I' (\<lambda>_. Univ) \<subseteq> PiE I (\<lambda>_. Univ)"
          using assms(2) terminal_unity extensional_def [of I'] extensional_def [of I'] by auto
        ultimately show ?thesis using \<pi> assms(2) by blast
      qed
      ultimately show ?thesis using admits_tupling_def by auto
    qed

    lemma has_products_iff_admits_tupling:
    fixes I :: "'i set"
    shows "has_products I \<longleftrightarrow> I \<noteq> UNIV \<and> admits_tupling I"
    proof
      text{*
        If S has @{term I}-indexed products, then for every @{term I}-indexed
        discrete diagram @{term D} in @{term S} there is an object @{term \<Pi>D}
        of @{term S} whose points are in bijective correspondence with the set of cones
        over @{term D} with apex @{term unity}.  In particular this is true for
        the diagram @{term D} that assigns to each element of @{term I} the
        ``universal object'' @{term "mkIde Univ"}.
      *}
      assume has_products: "has_products I"
      have I: "I \<noteq> UNIV" using has_products has_products_def by auto
      interpret J: DiscreteCategory.discrete_category I
        apply (unfold_locales) using has_products has_products_def by auto
      let ?D = "\<lambda>i. mkIde Univ"
      interpret D: discrete_diagram_from_map I S ?D
        apply unfold_locales by auto
      interpret D: discrete_diagram_in_set_category J.comp S D.map ..
      have "discrete_diagram J.comp S D.map" ..
      from this obtain \<Pi>D \<chi> where \<chi>: "product_cone J.comp S D.map \<Pi>D \<chi>"
        using has_products has_products_def [of I] ex_productE [of "J.comp" D.map]
              D.diagram_axioms
        by auto
      interpret \<chi>: product_cone J.comp S D.map \<Pi>D \<chi>
        using \<chi> by auto
      have "limit_cone J.comp S D.map \<Pi>D \<chi>" ..
      hence "D.has_as_limit \<Pi>D" by auto
      hence \<Pi>D: "ide \<Pi>D \<and> (\<exists>\<phi>. bij_betw \<phi> (hom unity \<Pi>D) (D.cones unity))"
        using D.limits_are_sets_of_cones by simp
      from this obtain \<phi> where \<phi>: "bij_betw \<phi> (hom unity \<Pi>D) (D.cones unity)"
        by blast
      have \<phi>': "inv_into (hom unity \<Pi>D) \<phi> \<in> D.cones unity \<rightarrow> hom unity \<Pi>D
                  \<and> inj_on (inv_into (hom unity \<Pi>D) \<phi>) (D.cones unity)"
        using \<phi> bij_betw_inv_into [of \<phi> "hom unity \<Pi>D" "D.cones unity"] bij_betw_imp_inj_on
              bij_betw_imp_funcset
        by blast
      let ?\<pi> = "img o (inv_into (hom unity \<Pi>D) \<phi>) o D.funToCone"
      have 1: "D.funToCone \<in> PiE I (set o D.map) \<rightarrow> D.cones unity"
        using D.funToCone_mapsto extensional_def [of I] by auto
      have 2: "inv_into (hom unity \<Pi>D) \<phi> \<in> D.cones unity \<rightarrow> hom unity \<Pi>D"
        using \<phi>' by auto
      have 3: "img \<in> hom unity \<Pi>D \<rightarrow> Univ"
        using img_point_in_Univ by fast
      have 4: "inj_on D.funToCone (PiE I (set o D.map))"
      proof -
        have "D.I = I" by auto
        thus ?thesis
          using D.bij_funToCone bij_betw_imp_inj_on by auto
      qed
      have 5: "inj_on (inv_into (hom unity \<Pi>D) \<phi>) (D.cones unity)"
        using \<phi>' by auto
      have 6: "inj_on img (hom unity \<Pi>D)"
        using \<Pi>D bij_betw_points_and_set [of \<Pi>D]
              bij_betw_imp_inj_on [of img "hom unity \<Pi>D" "set \<Pi>D"]
        by simp
      have "?\<pi> \<in> PiE I (set o D.map) \<rightarrow> Univ"
      proof -
        have "(inv_into (hom unity \<Pi>D) \<phi>) o D.funToCone
                  \<in> PiE I (set o D.map) \<rightarrow> hom unity \<Pi>D"
          using 1 2 by auto
        have "img o (inv_into (hom unity \<Pi>D) \<phi>) \<in> D.cones unity \<rightarrow> Univ"
          using 2 3 by auto
        thus ?thesis using 1 by auto
      qed
      moreover have "inj_on ?\<pi> (PiE I (set o D.map))"
      proof -
        have 7: "\<And>A B C D F G H. F \<in> A \<rightarrow> B \<and> G \<in> B \<rightarrow> C \<and> H \<in> C \<rightarrow> D
                      \<and> inj_on F A \<and> inj_on G B \<and> inj_on H C
                    \<Longrightarrow> inj_on (H o G o F) A"
        proof (intro inj_onI)
          fix A :: "'a set" and B :: "'b set" and C :: "'c set" and D :: "'d set"
          and F :: "'a \<Rightarrow> 'b" and G :: "'b \<Rightarrow> 'c" and H :: "'c \<Rightarrow> 'd"
          assume a1: "F \<in> A \<rightarrow> B \<and> G \<in> B \<rightarrow> C \<and> H \<in> C \<rightarrow> D \<and>
                      inj_on F A \<and> inj_on G B \<and> inj_on H C"
          fix a a'
          assume a: "a \<in> A" and a': "a' \<in> A" and eq: "(H o G o F) a = (H o G o F) a'"
          have "H (G (F a)) = H (G (F a'))" using eq by simp
          moreover have "G (F a) \<in> C \<and> G (F a') \<in> C" using a a' a1 by auto
          ultimately have "G (F a) = G (F a')" using a1 inj_onD by metis
          moreover have "F a \<in> B \<and> F a' \<in> B" using a a' a1 by auto
          ultimately have "F a = F a'" using a1 inj_onD by metis
          thus "a = a'" using a a' a1 inj_onD by metis
        qed
        show ?thesis
          using 1 2 3 4 5 6 7 [of D.funToCone "PiE I (set o D.map)" "D.cones unity"
                                  "inv_into (hom unity \<Pi>D) \<phi>" "hom unity \<Pi>D"
                                  img Univ]
          by fastforce
      qed
      moreover have "PiE I (set o D.map) = PiE I (\<lambda>x. Univ)"
      proof -
        have "\<And>i. i \<in> I \<Longrightarrow> (set o D.map) i = Univ"
          using J.arr_char D.map_def by simp
        thus ?thesis by blast
      qed
      ultimately have "?\<pi> \<in> (PiE I (\<lambda>x. Univ)) \<rightarrow> Univ \<and> inj_on ?\<pi> (PiE I (\<lambda>x. Univ))"
        by auto
      thus "I \<noteq> UNIV \<and> admits_tupling I"
        using I admits_tupling_def by auto
      next
      assume ex_\<pi>: "I \<noteq> UNIV \<and> admits_tupling I"
      interpret J: DiscreteCategory.discrete_category I
        apply (unfold_locales) using ex_\<pi> has_products_def by auto
      show "has_products I"
      proof (unfold has_products_def)
        from ex_\<pi> obtain \<pi> where \<pi>: "\<pi> \<in> (PiE I (\<lambda>x. Univ)) \<rightarrow> Univ \<and> inj_on \<pi> (PiE I (\<lambda>x. Univ))"
          using admits_tupling_def by blast
        text{*
          Given an @{term I}-indexed discrete diagram @{term D}, obtain the object @{term \<Pi>D}
          of @{term S} corresponding to the set @{term "\<pi> ` PiE I D"} of all @{term "\<pi> d"}
          where @{text "d \<in> d \<in> J \<rightarrow>\<^sub>E Univ"} and @{term "d i \<in> D i"} for all @{term "i \<in> I"}.
          The elements of @{term \<Pi>D} are in bijective correspondence with the set of cones
          over @{term D}, hence @{term \<Pi>D} is a limit of @{term D}.
        *}
        have "\<And>D. diagram J.comp S D \<Longrightarrow> \<exists>\<Pi>D. has_as_product J.comp D \<Pi>D"
        proof
          fix D
          assume D: "diagram J.comp S D"
          interpret D: diagram J.comp S D using D by auto
          interpret D: discrete_diagram J.comp S D
            apply unfold_locales using J.is_discrete by auto
          interpret D: discrete_diagram_in_set_category J.comp S D ..
          let ?\<Pi>D = "mkIde (\<pi> ` PiE I (set o D))"
          have "ide ?\<Pi>D"
          proof -
            have "set o D \<in> I \<rightarrow> Pow Univ"
              using Pow_iff incl_in_def o_apply elem_set_implies_incl_in
                    set_subset_Univ subsetI
              by auto
            hence "\<pi> ` PiE I (set o D) \<subseteq> Univ"
              using \<pi> by blast
            thus ?thesis using \<pi> ide_mkIde by simp
          qed
          hence set_\<Pi>D: "\<pi> ` PiE I (set o D) = set ?\<Pi>D"
            using `ide ?\<Pi>D` by (metis ideD(1) arr_mkIde set_mkIde)
          text{*
            The elements of @{term \<Pi>D} are all values of the form @{term "\<pi> d"},
            where @{term d} satisfies @{term "d i \<in> set (D i)"} for all @{term "i \<in> I"}.
            Such @{term d} correspond bijectively to cones.
            Since @{term \<pi>} is injective, the values @{term "\<pi> d"} correspond bijectively to cones.
          *}
          let ?\<phi> = "mkPoint ?\<Pi>D o \<pi> o D.coneToFun"
          let ?\<phi>' = "D.funToCone o inv_into (PiE I (set o D)) \<pi> o img"
          have 1: "\<pi> \<in> PiE I (set o D) \<rightarrow> set ?\<Pi>D \<and> inj_on \<pi> (PiE I (set o D))"
          proof -
            have "PiE I (set o D) \<subseteq> PiE I (\<lambda>x. Univ)"
              using set_subset_Univ elem_set_implies_incl_in elem_set_implies_set_eq_singleton
                    incl_in_def PiE_mono
              by (metis D.preserves_ide J.discrete_category_axioms comp_apply
                        discrete_category.ide_char)
            thus ?thesis using \<pi> subset_inj_on set_\<Pi>D Pi_I' imageI by fastforce
          qed
          have 2: "inv_into (PiE I (set o D)) \<pi> \<in> set ?\<Pi>D \<rightarrow> PiE I (set o D)"
          proof
            fix y
            assume y: "y \<in> set ?\<Pi>D"
            have "y \<in> \<pi> ` (PiE I (set o D))" using y set_\<Pi>D by auto
            thus "inv_into (PiE I (set o D)) \<pi> y \<in> PiE I (set o D)"
              using inv_into_into [of y \<pi> "PiE I (set o D)"] by simp
          qed
          have 3: "\<And>x. x \<in> set ?\<Pi>D \<Longrightarrow> \<pi> (inv_into (PiE I (set o D)) \<pi> x) = x"
            using set_\<Pi>D by (simp add: f_inv_into_f)
          have 4: "\<And>d. d \<in> PiE I (set o D) \<Longrightarrow> inv_into (PiE I (set o D)) \<pi> (\<pi> d) = d"
            using 1 by auto
          have "D.I = I" by auto
          have "bij_betw ?\<phi> (D.cones unity) (hom unity ?\<Pi>D)"
          proof (intro bij_betwI)
            show "?\<phi> \<in> D.cones unity \<rightarrow> hom unity ?\<Pi>D"
            proof
              fix \<chi>
              assume \<chi>: "\<chi> \<in> D.cones unity"
              show "?\<phi> \<chi> \<in> hom unity ?\<Pi>D"
                using \<chi> D.coneToFun_mapsto 1 mkPoint_in_hom [of ?\<Pi>D] `ide ?\<Pi>D` `D.I = I`
                by fastforce
            qed
            show "?\<phi>' \<in> hom unity ?\<Pi>D \<rightarrow> D.cones unity"
            proof
              fix x
              assume x: "x \<in> hom unity ?\<Pi>D"
              show "?\<phi>' x \<in> D.cones unity" using x img_point_elem_set 2 D.funToCone_mapsto
                   `D.I = I`
                by fastforce
            qed
            show "\<And>x. x \<in> hom unity ?\<Pi>D \<Longrightarrow> ?\<phi> (?\<phi>' x) = x"
            proof -
              fix x
              assume x: "x \<in> hom unity ?\<Pi>D"
              show "?\<phi> (?\<phi>' x) = x"
              proof -
                have "D.coneToFun (D.funToCone (inv_into (PiE I (set o D)) \<pi> (img x)))
                          = inv_into (PiE I (set o D)) \<pi> (img x)"
                  using x img_point_elem_set set_\<Pi>D D.coneToFun_funToCone 1 `D.I = I`
                  by fastforce
                hence "\<pi> (D.coneToFun (D.funToCone (inv_into (PiE I (set o D)) \<pi> (img x))))
                          = img x"
                  using x img_point_elem_set set_\<Pi>D 3 by fastforce
                hence "mkPoint ?\<Pi>D (\<pi> (D.coneToFun (D.funToCone
                                       (inv_into (PiE I (set o D)) \<pi> (img x)))))
                          = x"
                  using x mkPoint_img `ide ?\<Pi>D` by presburger
                thus ?thesis by auto
              qed
            qed
            show "\<And>\<chi>. \<chi> \<in> D.cones unity \<Longrightarrow> ?\<phi>' (?\<phi> \<chi>) = \<chi>"
            proof -
              fix \<chi>
              assume \<chi>: "\<chi> \<in> D.cones unity"
              show "?\<phi>' (?\<phi> \<chi>) = \<chi>"
              proof -
                have "img (mkPoint ?\<Pi>D (\<pi> (D.coneToFun \<chi>))) = \<pi> (D.coneToFun \<chi>)"
                  using \<chi> D.coneToFun_mapsto 1 img_mkPoint `ide ?\<Pi>D` `D.I = I`
                  by fastforce
                hence "inv_into (PiE I (set o D)) \<pi>
                         (img (mkPoint ?\<Pi>D (\<pi> (D.coneToFun \<chi>)))) = D.coneToFun \<chi>"
                  using \<chi> D.coneToFun_mapsto 4 `D.I = I` by fastforce
                hence "D.funToCone (inv_into (PiE I (set o D)) \<pi>
                                      (img (mkPoint ?\<Pi>D (\<pi> (D.coneToFun \<chi>))))) = \<chi>"
                  using \<chi> D.funToCone_coneToFun by auto
                thus ?thesis by auto
              qed
            qed
          qed
          hence "bij_betw (inv_into (D.cones unity) ?\<phi>) (hom unity ?\<Pi>D) (D.cones unity)"
            using bij_betw_inv_into by blast
          hence "\<exists>\<phi>. bij_betw \<phi> (hom unity ?\<Pi>D) (D.cones unity)" by blast
          hence "D.has_as_limit ?\<Pi>D"
            using `ide ?\<Pi>D` D.limits_are_sets_of_cones [of ?\<Pi>D] by simp
          from this obtain \<chi> where \<chi>: "limit_cone J.comp S D ?\<Pi>D \<chi>" by blast
          interpret \<chi>: limit_cone J.comp S D ?\<Pi>D \<chi> using \<chi> by auto
          interpret P: product_cone J.comp S D ?\<Pi>D \<chi>
            using \<chi> D.product_coneI [of ?\<Pi>D \<chi>] by blast
          have "product_cone J.comp S D ?\<Pi>D \<chi>" ..
          thus "has_as_product J.comp D ?\<Pi>D"
            using has_as_product_def by auto
        qed
        thus "I \<noteq> UNIV \<and> (\<forall>D. diagram J.comp S D \<longrightarrow> (\<exists>\<Pi>D. has_as_product J.comp D \<Pi>D))"
          using ex_\<pi> by simp
      qed
    qed

    text{*
      Characterization of the completeness properties enjoyed by a set category:
      A set category @{term S} has all limits at a type @{typ 'j}, if and only if @{term S}
      admits @{term I}-indexed tupling for all @{typ 'j}-sets @{term I} such that
      @{term "I \<noteq> UNIV"}.
    *}

    theorem has_limits_iff_admits_tupling:
    shows "has_limits (undefined :: 'j) \<longleftrightarrow> (\<forall>I :: 'j set. I \<noteq> UNIV \<longrightarrow> admits_tupling I)"
    proof
      assume has_limits: "has_limits (undefined :: 'j)"
      show "\<forall>I :: 'j set. I \<noteq> UNIV \<longrightarrow> admits_tupling I"
      proof
        fix I :: "'j set"
        show "I \<noteq> UNIV \<longrightarrow> admits_tupling I"
        proof
          assume I: "I \<noteq> UNIV"
          have "has_products I" using I has_limits has_products_if_has_limits by auto
          thus "admits_tupling I"
            using has_products_iff_admits_tupling [of I] by simp
        qed
      qed
      next
      assume admits_tupling: "\<forall>I :: 'j set. I \<noteq> UNIV \<longrightarrow> admits_tupling I"
      show "has_limits (undefined :: 'j)"
      proof -
        have 1: "\<And>I :: 'j set. I \<noteq> UNIV \<Longrightarrow> has_products I"
          using admits_tupling has_products_iff_admits_tupling by auto
        have "\<And>J :: 'j comp. category J \<Longrightarrow> has_products (Collect (partial_magma.arr J))"
        proof -
          fix J :: "'j comp"
          assume J: "category J"
          interpret J: category J using J by auto
          have "Collect J.arr \<noteq> UNIV" using J.not_arr_null by auto
          thus "has_products (Collect J.arr)"
            using 1 by simp
        qed
        hence "\<And>J :: 'j comp. category J \<Longrightarrow> has_limits_of_shape J"
          using has_limits_if_has_products
          by (metis UNIV_I 1 category.axioms(1) mem_Collect_eq
                    category.ideD(1) partial_magma.not_arr_null)
        thus "has_limits (undefined :: 'j)"
          using has_limits_def by metis
      qed
    qed

  end

  section "Limits in Functor Categories"

  text{*
    In this section, we consider the special case of limits in functor categories,
    with the objective of showing that limits in a functor category @{text "[A, B]"}
    are given pointwise, and that @{text "[A, B]"} has all limits that @{term B} has.
  *}

  locale parametrized_diagram =
    J: category J +
    A: category A +
    B: category B +
    JxA: product_category J A +
    binary_functor J A B D
  for J :: "'j comp"
  and A :: "'a comp"
  and B :: "'b comp"
  and D :: "'j * 'a \<Rightarrow> 'b"
  begin

    text{*
      A choice of limit cone for each diagram @{text "D (-, a)"}, where @{term a}
      is an object of @{term A}, extends to a functor @{text "L: A \<rightarrow> B"},
      where the action of @{term L} on arrows of @{term A} is determined by universality.
     *}

    abbreviation L
    where "L \<equiv> \<lambda>l \<chi>. \<lambda>a. if A.arr a then
                            limit_cone.induced_arrow J B (\<lambda>j. D (j, A.cod a))
                              (l (A.cod a)) (\<chi> (A.cod a))
                              (l (A.dom a)) (vertical_composite.map J B
                                               (\<chi> (A.dom a)) (\<lambda>j. D (j, a)))
                          else B.null"

    abbreviation P
    where "P \<equiv> \<lambda>l \<chi>. \<lambda>a f. f \<in> B.hom (l (A.dom a)) (l (A.cod a)) \<and>
                           diagram.cones_map J B (\<lambda>j. D (j, A.cod a)) f (\<chi> (A.cod a))
                                = vertical_composite.map J B (\<chi> (A.dom a)) (\<lambda>j. D (j, a))"

    lemma L_arr:
    assumes "\<forall>a. A.ide a \<longrightarrow> limit_cone J B (\<lambda>j. D (j, a)) (l a) (\<chi> a)"
    shows "\<And>a. A.arr a \<Longrightarrow> (\<exists>!f. P l \<chi> a f) \<and> P l \<chi> a (L l \<chi> a)"
    proof
      fix a
      assume a: "A.arr a"
      interpret \<chi>_dom_a: limit_cone J B "\<lambda>j. D (j, A.dom a)" "l (A.dom a)" "\<chi> (A.dom a)"
        using a assms by auto
      interpret \<chi>_cod_a: limit_cone J B "\<lambda>j. D (j, A.cod a)" "l (A.cod a)" "\<chi> (A.cod a)"
        using a assms by auto
      interpret Da: natural_transformation J B "\<lambda>j. D (j, A.dom a)" "\<lambda>j. D (j, A.cod a)"
                                               "\<lambda>j. D (j, a)"
        using a fixing_arr_gives_natural_transformation_2 by simp
      interpret Dao\<chi>_dom_a: vertical_composite J B
                              \<chi>_dom_a.A.map "\<lambda>j. D (j, A.dom a)" "\<lambda>j. D (j, A.cod a)"
                              "\<chi> (A.dom a)" "\<lambda>j. D (j, a)" ..
      interpret Dao\<chi>_dom_a: cone J B "\<lambda>j. D (j, A.cod a)" "l (A.dom a)" Dao\<chi>_dom_a.map ..
      show "P l \<chi> a (L l \<chi> a)"
        using a Dao\<chi>_dom_a.cone_axioms \<chi>_cod_a.induced_arrowI [of Dao\<chi>_dom_a.map "l (A.dom a)"]
        by auto
      show "\<exists>!f. P l \<chi> a f"
        using \<chi>_cod_a.is_universal [of "l (A.dom a)" Dao\<chi>_dom_a.map] Dao\<chi>_dom_a.cone_axioms
        by fast
    qed

    lemma L_ide:
    assumes "\<forall>a. A.ide a \<longrightarrow> limit_cone J B (\<lambda>j. D (j, a)) (l a) (\<chi> a)"
    shows "\<And>a. A.ide a \<Longrightarrow> L l \<chi> a = l a"
    proof -
      let ?L = "L l \<chi>"
      let ?P = "P l \<chi>"
      fix a
      assume a: "A.ide a"
      interpret \<chi>a: limit_cone J B "\<lambda>j. D (j, a)" "l a" "\<chi> a" using a assms by auto
      have Pa: "?P a = (\<lambda>f. f \<in> B.hom (l a) (l a) \<and>
                            diagram.cones_map J B (\<lambda>j. D (j, a)) f (\<chi> a) = \<chi> a)"
        using a vcomp_ide_dom [of J B \<chi>a.A.map "\<lambda>j. D (j, a)" "\<lambda>j. D (j, a)"]
              \<chi>a.natural_transformation_axioms
        by force
      have "?P a (?L a)" using assms a L_arr [of l \<chi> a] by fastforce
      moreover have "?P a (l a)"
      proof -
        have "?P a (l a) \<longleftrightarrow> l a \<in> B.hom (l a) (l a) \<and> \<chi>a.D.cones_map (l a) (\<chi> a) = \<chi> a"
          using Pa by meson
        thus ?thesis
          using a \<chi>a.ide_apex \<chi>a.cone_axioms \<chi>a.D.cones_map_ide [of "\<chi> a" "l a"] by simp
      qed
      moreover have "\<exists>!f. ?P a f"
        using a Pa \<chi>a.is_universal [of "l a" "\<chi> a"] \<chi>a.cone_axioms by presburger
      ultimately show "?L a = l a" by fast
    qed

    lemma chosen_limits_induce_functor:
    assumes "\<forall>a. A.ide a \<longrightarrow> limit_cone J B (\<lambda>j. D (j, a)) (l a) (\<chi> a)"
    shows "functor A B (L l \<chi>)"
    proof -
      let ?L = "L l \<chi>"
      let ?P = "\<lambda>a. \<lambda>f. f \<in> B.hom (l (A.dom a)) (l (A.cod a)) \<and>
                        diagram.cones_map J B (\<lambda>j. D (j, A.cod a)) f (\<chi> (A.cod a))
                             = vertical_composite.map J B (\<chi> (A.dom a)) (\<lambda>j. D (j, a))"
      interpret L: "functor" A B ?L
        apply unfold_locales
        (* 5 *) apply auto[1]
      proof -
        fix a
        assume a: "A.arr a"
        show "B.arr (?L a)" using assms a L_arr by simp
        show "B.dom (?L a) = ?L (A.dom a)" using assms a L_arr L_ide [of l \<chi> "A.dom a"] by auto
        show "B.cod (?L a) = ?L (A.cod a)" using assms a L_arr L_ide [of l \<chi> "A.cod a"] by auto
        fix a'
        assume a': "a' \<in> A.hom (A.cod a) (A.cod a')"
        have a'a: "A.seq a' a" using a a' by auto
        interpret \<chi>_dom_a: limit_cone J B "\<lambda>j. D (j, A.dom a)" "l (A.dom a)" "\<chi> (A.dom a)"
          using a assms by auto
        interpret \<chi>_cod_a: limit_cone J B "\<lambda>j. D (j, A.cod a)" "l (A.cod a)" "\<chi> (A.cod a)"
          using a'a assms by auto
        interpret \<chi>_dom_a'a: limit_cone J B "\<lambda>j. D (j, A.dom (A a' a))" "l (A.dom (A a' a))"
                                            "\<chi> (A.dom (A a' a))"
          using a'a assms by auto
        interpret \<chi>_cod_a'a: limit_cone J B "\<lambda>j. D (j, A.cod (A a' a))" "l (A.cod (A a' a))"
                                            "\<chi> (A.cod (A a' a))"
          using a'a assms by auto
        interpret Da: natural_transformation J B "\<lambda>j. D (j, A.dom a)" "\<lambda>j. D (j, A.cod a)"
                                                 "\<lambda>j. D (j, a)"
          using a fixing_arr_gives_natural_transformation_2 by simp
        interpret Da': natural_transformation J B "\<lambda>j. D (j, A.cod a)" "\<lambda>j. D (j, A.cod (A a' a))"
                                                  "\<lambda>j. D (j, a')"
          using a a'a fixing_arr_gives_natural_transformation_2 by simp
        interpret Da'o\<chi>_cod_a: vertical_composite J B
                                 \<chi>_cod_a.A.map "\<lambda>j. D (j, A.cod a)" "\<lambda>j. D (j, A.cod (A a' a))"
                                 "\<chi> (A.cod a)" "\<lambda>j. D (j, a')" ..
        interpret Da'o\<chi>_cod_a: cone J B "\<lambda>j. D (j, A.cod (A a' a))" "l (A.cod a)" Da'o\<chi>_cod_a.map ..
        interpret Da'a: natural_transformation J B
                          "\<lambda>j. D (j, A.dom (A a' a))" "\<lambda>j. D (j, A.cod (A a' a))"
                          "\<lambda>j. D (j, A a' a)"
          using a'a fixing_arr_gives_natural_transformation_2 [of "A a' a"] by auto
        interpret Da'ao\<chi>_dom_a'a:
            vertical_composite J B \<chi>_dom_a'a.A.map "\<lambda>j. D (j, A.dom (A a' a))"
                                   "\<lambda>j. D (j, A.cod (A a' a))" "\<chi> (A.dom (A a' a))"
                                   "\<lambda>j. D (j, A a' a)" ..
        interpret Da'ao\<chi>_dom_a'a: cone J B "\<lambda>j. D (j, A.cod (A a' a))"
                                       "l (A.dom (A a' a))" Da'ao\<chi>_dom_a'a.map ..
        show "?L (A a' a) = B (?L a') (?L a)"
        proof -
          have "?P (A a' a) (?L (A a' a))" using assms a'a L_arr [of l \<chi> "A a' a"] by fastforce
          moreover have "?P (A a' a) (B (?L a') (?L a))"
          proof
            have La: "?L a \<in> B.hom (l (A.dom a)) (l (A.cod a))"
              using assms a L_arr [of l \<chi> a] by presburger
            moreover have La': "?L a' \<in> B.hom (l (A.cod a)) (l (A.cod a'))"
              using assms a a' L_arr [of l \<chi> a'] by simp
            ultimately have seq: "B.seq (?L a') (?L a)" by simp
            thus La'_La: "B (?L a') (?L a) \<in> B.hom (l (A.dom (A a' a))) (l (A.cod (A a' a)))"
              using a a' La La' by simp
            show "\<chi>_cod_a'a.D.cones_map (B (?L a') (?L a)) (\<chi> (A.cod (A a' a)))
                    = Da'ao\<chi>_dom_a'a.map"
            proof -
              have "\<chi>_cod_a'a.D.cones_map (B (?L a') (?L a)) (\<chi> (A.cod (A a' a)))
                       = (\<chi>_cod_a'a.D.cones_map (?L a) o \<chi>_cod_a'a.D.cones_map (?L a'))
                           (\<chi> (A.cod a'))"
                using seq a'a \<chi>_cod_a'a.cone_axioms La'
                      \<chi>_cod_a'a.D.cones_map_comp [of "?L a" "?L a'"]
                      restrict_apply' [of "\<chi> (A.cod a')" "\<chi>_cod_a'a.D.cones (l (A.cod a'))"
                                          "\<chi>_cod_a'a.D.cones_map (?L a)
                                            o \<chi>_cod_a'a.D.cones_map (?L a')"]
                by auto
              also have "... = \<chi>_cod_a'a.D.cones_map (?L a)
                                   (\<chi>_cod_a'a.D.cones_map (?L a') (\<chi> (A.cod a')))"
                  by simp
              also have "... = \<chi>_cod_a'a.D.cones_map (?L a) Da'o\<chi>_cod_a.map"
              proof -
                have "?P a' (?L a')" using assms a' L_arr [of l \<chi> a'] by fast
                moreover have
                    "?P a' = (\<lambda>f. f \<in> B.hom (l (A.cod a)) (l (A.cod a')) \<and>
                                  \<chi>_cod_a'a.D.cones_map f (\<chi> (A.cod a')) = Da'o\<chi>_cod_a.map)"
                  using a'a by simp
                ultimately show ?thesis using a'a by force
              qed
              also have "... = vertical_composite.map J B
                                 (\<chi>_cod_a.D.cones_map (?L a) (\<chi> (A.cod a)))
                                 (\<lambda>j. D (j, a'))"
                using assms \<chi>_cod_a.D.diagram_axioms \<chi>_cod_a'a.D.diagram_axioms
                      Da'.natural_transformation_axioms \<chi>_cod_a.cone_axioms
                      L_arr [of l \<chi> a] a a' a'a
                      cones_map_vcomp [of J B "\<lambda>j. D (j, A.cod a)" "\<lambda>j. D (j, A.cod (A a' a))"
                                          "\<lambda>j. D (j, a')" "l (A.cod a)" "\<chi> (A.cod a)"
                                          "?L a"]
                by blast
              also have "... = vertical_composite.map J B
                                 (vertical_composite.map J B (\<chi> (A.dom a)) (\<lambda>j. D (j, a)))
                                 (\<lambda>j. D (j, a'))"
                using assms a L_arr [of l \<chi> a] by presburger
              also have "... = vertical_composite.map J B (\<chi> (A.dom a))
                                 (vertical_composite.map J B (\<lambda>j. D (j, a)) (\<lambda>j. D (j, a')))"
              proof -
                have "natural_transformation J B \<chi>_dom_a.A.map (\<lambda>j. D (j, A.dom a))
                                                 (\<chi> (A.dom a))" ..
                moreover have "natural_transformation J B (\<lambda>j. D (j, A.dom a)) (\<lambda>j. D (j, A.cod a))
                                                          (\<lambda>j. D (j, a))" ..
                moreover have "natural_transformation J B (\<lambda>j. D (j, A.cod a)) (\<lambda>j. D (j, A.cod a'))
                                                          (\<lambda>j. D (j, a'))"
                proof -
                  have "natural_transformation J B (\<lambda>j. D (j, A.cod a)) (\<lambda>j. D (j, A.cod (A a' a)))
                                                   (\<lambda>j. D (j, a'))" ..
                  thus ?thesis using a'a by simp
                qed
                ultimately show ?thesis
                  using vcomp_assoc [of J B \<chi>_dom_a.A.map "\<lambda>j. D (j, A.dom a)" "\<chi> (A.dom a)"
                                        "\<lambda>j. D (j, A.cod a)" "\<lambda>j. D (j, a)"
                                        "\<lambda>j. D (j, A.cod a')" "\<lambda>j. D (j, a')"]
                  by simp
              qed
              also have "... = vertical_composite.map J B (\<chi> (A.dom (A a' a))) (\<lambda>j. D (j, A a' a))"
                using a'a preserves_comp_2 by simp
              finally show ?thesis by auto
            qed
          qed
          moreover have "\<exists>!f. ?P (A a' a) f"
            using \<chi>_cod_a'a.is_universal
                    [of "l (A.dom (A a' a))"
                        "vertical_composite.map J B (\<chi> (A.dom (A a' a))) (\<lambda>j. D (j, A a' a))"]
                  Da'ao\<chi>_dom_a'a.cone_axioms
            by fast
          ultimately show ?thesis by blast
        qed
      qed
      show ?thesis ..
    qed

  end

  locale diagram_in_functor_category =
    A: category A +
    B: category B +
    A_B: functor_category A B +
    diagram J A_B.comp D
  for A :: "'a comp"
  and B :: "'b comp"
  and J :: "'j comp"
  and D :: "'j \<Rightarrow> ('a, 'b) functor_category.arr"
  begin

    interpretation JxA: product_category J A ..
    interpretation A_BxA: product_category A_B.comp A ..
    interpretation E: evaluation_functor A B ..
    interpretation Curry: currying J A B ..

    text{*
      Evaluation of a functor or natural transformation from @{term J} to @{text "[A, B]"}
      at an arrow @{term a} of @{term A}.
    *}

    abbreviation at
    where "at a \<tau> \<equiv> \<lambda>j. Curry.uncurry \<tau> (j, a)"

    lemma at_simp:
    assumes "A.arr a" and "J.arr j" and "A_B.arr (\<tau> j)"
    shows "at a \<tau> j = A_B.Fun (\<tau> j) a"
      using assms Curry.uncurry_def E.map_simp by simp

    lemma functor_at_ide_is_functor:
    assumes "functor J A_B.comp F" and "A.ide a"
    shows "functor J B (at a F)"
    proof -
      interpret uncurry_F: "functor" JxA.comp B "Curry.uncurry F"
        using assms(1) Curry.uncurry_preserves_functors [of F] by simp
      interpret uncurry_F: binary_functor J A B "Curry.uncurry F" ..
      show ?thesis using assms(2) uncurry_F.fixing_ide_gives_functor_2 by simp
    qed

    lemma functor_at_arr_is_transformation:
    assumes "functor J A_B.comp F" and "A.arr a"
    shows "natural_transformation J B (at (A.dom a) F) (at (A.cod a) F) (at a F)"
    proof -
      interpret uncurry_F: "functor" JxA.comp B "Curry.uncurry F"
        using assms(1) Curry.uncurry_preserves_functors [of F] by simp
      interpret uncurry_F: binary_functor J A B "Curry.uncurry F" ..
      show ?thesis
        using assms(2) uncurry_F.fixing_arr_gives_natural_transformation_2 by simp
    qed

    lemma transformation_at_ide_is_transformation:
    assumes "natural_transformation J A_B.comp F G \<tau>" and "A.ide a"
    shows "natural_transformation J B (at a F) (at a G) (at a \<tau>)"
    proof -
      interpret \<tau>: natural_transformation J A_B.comp F G \<tau> using assms(1) by auto
      interpret uncurry_F: "functor" JxA.comp B "Curry.uncurry F"
        using Curry.uncurry_preserves_functors [of F] \<tau>.F.functor_axioms by simp
      interpret uncurry_f: binary_functor J A B "Curry.uncurry F" ..
      interpret uncurry_G: "functor" JxA.comp B "Curry.uncurry G"
        using Curry.uncurry_preserves_functors [of G] \<tau>.G.functor_axioms by simp
      interpret uncurry_G: binary_functor J A B "Curry.uncurry G" ..
      interpret uncurry_\<tau>: natural_transformation JxA.comp B "Curry.uncurry F" "Curry.uncurry G"
                                                  "Curry.uncurry \<tau>"
        using Curry.uncurry_preserves_transformations \<tau>.natural_transformation_axioms
        by simp
      interpret uncurry_\<tau>: binary_functor_transformation J A B
                            "Curry.uncurry F" "Curry.uncurry G" "Curry.uncurry \<tau>" ..
      show ?thesis
        using assms(2) uncurry_\<tau>.fixing_ide_gives_natural_transformation_2 by simp
    qed

    lemma constant_at_ide_is_constant:
    assumes "cone x \<chi>" and a: "A.ide a"
    shows "at a (constant_functor.map J A_B.comp x) = constant_functor.map J B (A_B.Fun x a)"
    proof -
      interpret \<chi>: cone J A_B.comp D x \<chi> using assms(1) by auto
      have x: "A_B.ide x" using \<chi>.ide_apex by auto
      interpret Fun_x: "functor" A B "A_B.Fun x"
        using x A_B.ide_char by simp
      interpret Da: "functor" J B "at a D"
        using a functor_at_ide_is_functor functor_axioms by blast
      interpret Da: diagram J B "at a D" ..
      interpret Xa: constant_functor J B "A_B.Fun x a"
        apply unfold_locales using a Fun_x.preserves_ide [of a] by simp
      show "at a \<chi>.A.map = Xa.map"
        using a x Curry.uncurry_def E.map_def by auto
    qed

    lemma at_ide_is_diagram:
    assumes a: "A.ide a"
    shows "diagram J B (at a D)"
    proof -
      interpret Da: "functor" J B "at a D"
        using a functor_at_ide_is_functor functor_axioms by simp
      show ?thesis ..
    qed

    lemma cone_at_ide_is_cone:
    assumes "cone x \<chi>" and a: "A.ide a"
    shows "diagram.cone J B (at a D) (A_B.Fun x a) (at a \<chi>)"
    proof -
      interpret \<chi>: cone J A_B.comp D x \<chi> using assms(1) by auto
      have x: "A_B.ide x" using \<chi>.ide_apex by auto
      interpret Fun_x: "functor" A B "A_B.Fun x"
        using x A_B.ide_char by simp
      interpret Da: diagram J B "at a D" using a at_ide_is_diagram by auto
      interpret Xa: constant_functor J B "A_B.Fun x a"
        apply unfold_locales using a by simp
      interpret \<chi>a: natural_transformation J B Xa.map "at a D" "at a \<chi>"
      proof -
        have "natural_transformation J B (at a \<chi>.A.map) (at a D) (at a \<chi>)"
          using a transformation_at_ide_is_transformation [of \<chi>.A.map D \<chi> a]
                \<chi>.natural_transformation_axioms
          by simp
        moreover have "Xa.map = at a \<chi>.A.map"
          using constant_at_ide_is_constant [of x \<chi> a] assms(1) x a by simp
        ultimately show "natural_transformation J B Xa.map (at a D) (at a \<chi>)"
          by presburger
      qed
      interpret \<chi>a: cone J B "at a D" "A_B.Fun x a" "at a \<chi>" ..
      show cone_\<chi>a: "Da.cone (A_B.Fun x a) (at a \<chi>)" ..
    qed

    lemma at_preserves_comp:
    assumes "A.seq a' a"
    shows "at (A a' a) D = vertical_composite.map J B (at a D) (at a' D)"
    proof -
      interpret Da: natural_transformation J B "at (A.dom a) D" "at (A.cod a) D" "at a D"
      proof -
        have "functor J A_B.comp D" ..
        thus "natural_transformation J B (at (A.dom a) D) (at (A.cod a) D) (at a D)"
          using assms functor_at_arr_is_transformation [of D a] by auto
      qed
      interpret Da': natural_transformation J B "at (A.cod a) D" "at (A.cod a') D" "at a' D"
      proof -
        have "functor J A_B.comp D" ..
        thus "natural_transformation J B (at (A.cod a) D) (at (A.cod a') D) (at a' D)"
          using assms functor_at_arr_is_transformation [of D a'] by auto
      qed
      interpret Da'oDa: vertical_composite J B "at (A.dom a) D" "at (A.cod a) D" "at (A.cod a') D"
                                               "at a D" "at a' D" ..
      interpret Da'a: natural_transformation J B "at (A.dom a) D" "at (A.cod a') D" "at (A a' a) D"
      proof -
        have "functor J A_B.comp D" ..
        thus "natural_transformation J B (at (A.dom a) D) (at (A.cod a') D) (at (A a' a) D)"
          using assms functor_at_arr_is_transformation [of D "A a' a"] by auto
      qed
      show "at (A a' a) D = Da'oDa.map"
      proof (intro NaturalTransformation.eqI)
        show "natural_transformation J B (at (A.dom a) D) (at (A.cod a') D) Da'oDa.map" ..
        show "natural_transformation J B (at (A.dom a) D) (at (A.cod a') D) (at (A a' a) D)" ..
        show "\<And>j. J.ide j \<Longrightarrow> at (A a' a) D j = Da'oDa.map j"
        proof -
          fix j
          assume j: "J.ide j"
          interpret Dj: "functor" A B "A_B.Fun (D j)"
            using j preserves_ide [of j] A_B.ide_char [of "D j"] by simp
          show "at (A a' a) D j = Da'oDa.map j"
            using assms j Dj.preserves_comp at_simp Da'oDa.map_simp_ide [of j] by simp
        qed
      qed
    qed

    lemma cones_map_pointwise:
    assumes "cone x \<chi>" and "cone x' \<chi>'"
    and f: "f \<in> A_B.hom x' x"
    shows "cones_map f \<chi> = \<chi>' \<longleftrightarrow>
             (\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Fun f a) (at a \<chi>) = at a \<chi>')"
    proof
      interpret \<chi>: cone J A_B.comp D x \<chi> using assms(1) by auto
      interpret \<chi>': cone J A_B.comp D x' \<chi>' using assms(2) by auto
      have x: "A_B.ide x" using \<chi>.ide_apex by auto
      have x': "A_B.ide x'" using \<chi>'.ide_apex by auto
      interpret \<chi>f: cone J A_B.comp D x' "cones_map f \<chi>"
        using x' f assms(1) cones_map_mapsto by blast
      interpret Fun_x: "functor" A B "A_B.Fun x" using x A_B.ide_char by simp
      interpret Fun_x': "functor" A B "A_B.Fun x'" using x' A_B.ide_char by simp
      show "cones_map f \<chi> = \<chi>' \<Longrightarrow>
              (\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Fun f a) (at a \<chi>) = at a \<chi>')"
      proof -
        assume \<chi>': "cones_map f \<chi> = \<chi>'"
        have "\<And>a. A.ide a \<Longrightarrow> diagram.cones_map J B (at a D) (A_B.Fun f a) (at a \<chi>) = at a \<chi>'"
        proof -
          fix a
          assume a: "A.ide a"
          interpret Da: diagram J B "at a D" using a at_ide_is_diagram by auto
          have cone_\<chi>a: "Da.cone (A_B.Fun x a) (at a \<chi>)"
            using a assms(1) cone_at_ide_is_cone by simp
          interpret \<chi>a: cone J B "at a D" "A_B.Fun x a" "at a \<chi>"
            using cone_\<chi>a by auto
          have cone_\<chi>'a: "Da.cone (A_B.Fun x' a) (at a \<chi>')"
            using a assms(2) cone_at_ide_is_cone by simp
          interpret \<chi>'a: cone J B "at a D" "A_B.Fun x' a" "at a \<chi>'"
            using cone_\<chi>'a by auto
          have 1: "A_B.Fun f a \<in> B.hom (A_B.Fun x' a) (A_B.Fun x a)"
            using f a A_B.arr_char [of f] A_B.Fun_cod A_B.Fun_dom mem_Collect_eq
                  natural_transformation.preserves_hom
            by fastforce
          interpret \<chi>fa: cone J B "at a D" "A_B.Fun x' a" "Da.cones_map (A_B.Fun f a) (at a \<chi>)"
            using 1 cone_\<chi>a Da.cones_map_mapsto [of "A_B.Fun f a"] by force
          show "Da.cones_map (A_B.Fun f a) (at a \<chi>) = at a \<chi>'"
          proof
            fix j
            have "\<not>J.arr j \<Longrightarrow> Da.cones_map (A_B.Fun f a) (at a \<chi>) j = at a \<chi>' j"
              using \<chi>'a.is_extensional [of j] \<chi>fa.is_extensional [of j] by simp
            moreover have "J.arr j \<Longrightarrow> Da.cones_map (A_B.Fun f a) (at a \<chi>) j = at a \<chi>' j"
              using a f 1 assms(1) cone_\<chi>a \<chi>' Curry.uncurry_def E.map_simp
                    \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                    A_B.Fun_comp [of f "\<chi> j" a a] \<chi>.A.map_simp [of "J.dom j"] A_B.dom_simp
              by auto
            ultimately show "Da.cones_map (A_B.Fun f a) (at a \<chi>) j = at a \<chi>' j" by blast
          qed
        qed
        thus "\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Fun f a) (at a \<chi>) = at a \<chi>'"
          by simp
      qed
      show "\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Fun f a) (at a \<chi>) = at a \<chi>'
              \<Longrightarrow> cones_map f \<chi> = \<chi>'"
      proof -
        assume A: "\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Fun f a) (at a \<chi>) = at a \<chi>'"
        show "cones_map f \<chi> = \<chi>'"
        proof (intro NaturalTransformation.eqI)
          show "natural_transformation J A_B.comp \<chi>'.A.map D (cones_map f \<chi>)" ..
          show "natural_transformation J A_B.comp \<chi>'.A.map D \<chi>'" ..
          show "\<And>j. J.ide j \<Longrightarrow> cones_map f \<chi> j = \<chi>' j"
          proof (intro A_B.arr_eqI)
            fix j
            assume j: "J.ide j"
            show "A_B.arr (cones_map f \<chi> j)" using j \<chi>f.preserves_arr [of j] by simp
            show "A_B.arr (\<chi>' j)" using j \<chi>'.preserves_arr [of j] by simp
            have Dom_\<chi>f_j: "A_B.Dom (cones_map f \<chi> j) = A_B.Fun x'"
              using x' j A_B.Fun_dom [of "cones_map f \<chi> j"] \<chi>'.A.map_simp [of "J.dom j"]
                    \<chi>f.preserves_hom [of j "J.dom j" "J.cod j"]
              by auto
            also have Dom_\<chi>'_j: "... = A_B.Dom (\<chi>' j)"
              using x' j A_B.Fun_dom [of "\<chi>' j"] \<chi>'.preserves_hom [of j "J.dom j" "J.cod j"]
                    \<chi>'.A.map_simp [of "J.dom j"]
              by simp
            finally show "A_B.Dom (cones_map f \<chi> j) = A_B.Dom (\<chi>' j)" by auto
            have Cod_\<chi>f_j: "A_B.Cod (cones_map f \<chi> j) = A_B.Fun (D (J.cod j))"
              using j A_B.Fun_cod [of "cones_map f \<chi> j"]
                    \<chi>f.preserves_hom [of j "J.dom j" "J.cod j"] A_B.cod_simp
              by auto
            also have Cod_\<chi>'_j: "... = A_B.Cod (\<chi>' j)"
              using j A_B.Fun_cod [of "\<chi>' j"] \<chi>'.preserves_hom [of j "J.dom j" "J.cod j"]
              by simp
            finally show "A_B.Cod (cones_map f \<chi> j) = A_B.Cod (\<chi>' j)" by auto
            show "A_B.Fun (cones_map f \<chi> j) = A_B.Fun (\<chi>' j)"
            proof (intro NaturalTransformation.eqI)
              interpret \<chi>fj: natural_transformation A B "A_B.Fun x'" "A_B.Fun (D (J.cod j))"
                                                    "A_B.Fun (cones_map f \<chi> j)"
                using j \<chi>f.preserves_arr [of j] A_B.arr_char [of "cones_map f \<chi> j"]
                      Dom_\<chi>f_j Cod_\<chi>f_j
                by simp
              show "natural_transformation A B (A_B.Fun x') (A_B.Fun (D (J.cod j)))
                                           (A_B.Fun (cones_map f \<chi> j))" ..
              interpret \<chi>'j: natural_transformation A B "A_B.Fun x'" "A_B.Fun (D (J.cod j))"
                                                   "A_B.Fun (\<chi>' j)"
                using j \<chi>'.preserves_arr [of j] A_B.arr_char [of "\<chi>' j"] Dom_\<chi>'_j Cod_\<chi>'_j
                by simp
              show "natural_transformation A B (A_B.Fun x') (A_B.Fun (D (J.cod j)))
                                           (A_B.Fun (\<chi>' j))" ..
              show "\<And>a. A.ide a \<Longrightarrow> A_B.Fun (cones_map f \<chi> j) a = A_B.Fun (\<chi>' j) a"
              proof -
                fix a
                assume a: "A.ide a"
                interpret Da: diagram J B "at a D" using a at_ide_is_diagram by auto
                have cone_\<chi>a: "Da.cone (A_B.Fun x a) (at a \<chi>)"
                  using a assms(1) cone_at_ide_is_cone by simp
                interpret \<chi>a: cone J B "at a D" "A_B.Fun x a" "at a \<chi>"
                  using cone_\<chi>a by auto
                have fa: "A_B.Fun f a \<in> B.hom (A_B.Fun x' a) (A_B.Fun x a)"
                  using a f A_B.arr_char [of f] A_B.Fun_dom A_B.Fun_cod
                        natural_transformation.preserves_hom
                  by fastforce
                have "A_B.Fun (cones_map f \<chi> j) a = Da.cones_map (A_B.Fun f a) (at a \<chi>) j"
                proof -
                  have "A_B.Fun (cones_map f \<chi> j) a = A_B.Fun (A_B.comp (\<chi> j) f) a"
                    using assms(1) f \<chi>.preserves_arr by simp
                  also have "... = B (A_B.Fun (\<chi> j) a) (A_B.Fun f a)"
                    using f j a \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                          A_B.Fun_comp [of f "\<chi> j" a a] \<chi>.A.map_simp [of "J.dom j"]
                    by simp
                  also have "... = Da.cones_map (A_B.Fun f a) (at a \<chi>) j"
                    using j a cone_\<chi>a fa Curry.uncurry_def E.map_simp by simp
                  finally show ?thesis by auto
                qed
                also have "... = at a \<chi>' j" using j a A by simp
                also have "... = A_B.Fun (\<chi>' j) a"
                  using j a Curry.uncurry_def E.map_simp by simp
                finally show "A_B.Fun (cones_map f \<chi> j) a = A_B.Fun (\<chi>' j) a" by auto
              qed
            qed
          qed
        qed
      qed
    qed
       
    text{*
      If @{term \<chi>} is a cone with apex @{term a} over @{term D}, then @{term \<chi>}
      is a limit cone if, for each object @{term x} of @{term X}, the cone obtained
      by evaluating @{term \<chi>} at @{term x} is a limit cone with apex @{term "A_B.Fun a x"}
      for the diagram in @{term C} obtained by evaluating @{term D} at @{term x}.
    *}

    lemma cone_is_limit_if_pointwise_limit:
    assumes cone_\<chi>: "cone x \<chi>"
    and "\<forall>a. A.ide a \<longrightarrow> diagram.limit_cone J B (at a D) (A_B.Fun x a) (at a \<chi>)"
    shows "limit_cone x \<chi>"
    proof -
      interpret \<chi>: cone J A_B.comp D x \<chi> using assms by auto
      have x: "A_B.ide x" using \<chi>.ide_apex by auto
      show "limit_cone x \<chi>"
      proof
        fix x' \<chi>'
        assume cone_\<chi>': "cone x' \<chi>'"
        interpret \<chi>': cone J A_B.comp D x' \<chi>' using cone_\<chi>' by auto
        have x': "A_B.ide x'" using \<chi>'.ide_apex by auto
        text{*
          The universality of the limit cone @{text "at a \<chi>"} yields, for each object
          @{text a} of @{text A}, a unique arrow @{text fa} that transforms
          @{text "at a \<chi>"} to @{text "at a \<chi>'"}.
        *}
        have EU: "\<And>a. A.ide a \<Longrightarrow>
                        \<exists>!fa. fa \<in> B.hom (A_B.Fun x' a) (A_B.Fun x a) \<and>
                                   diagram.cones_map J B (at a D) fa (at a \<chi>) = at a \<chi>'"
        proof -
          fix a
          assume a: "A.ide a"
          interpret Da: diagram J B "at a D" using a at_ide_is_diagram by auto
          interpret \<chi>a: limit_cone J B "at a D" "A_B.Fun x a" "at a \<chi>"
            using assms(2) a by auto
          interpret \<chi>'a: cone J B "at a D" "A_B.Fun x' a" "at a \<chi>'"
            using a cone_\<chi>' cone_at_ide_is_cone by auto
          have "Da.cone (A_B.Fun x' a) (at a \<chi>')" ..
          thus "\<exists>!fa. fa \<in> B.hom (A_B.Fun x' a) (A_B.Fun x a) \<and>
                      Da.cones_map fa (at a \<chi>) = at a \<chi>'"
            using \<chi>a.is_universal by simp
        qed
        text{*
          Our objective is to show the existence of a unique arrow @{text f} that transforms
          @{text \<chi>} into @{text \<chi>'}.  We obtain @{text f} by bundling the arrows @{text fa}
          of @{text C} and proving that this yields a natural transformation from @{text X}
          to @{text C}, hence an arrow of @{text "[X, C]"}.
        *}
        show "\<exists>!f. f \<in> A_B.hom x' x \<and> cones_map f \<chi> = \<chi>'"
        proof
          let ?P = "\<lambda>a fa. fa \<in> B.hom (A_B.Fun x' a) (A_B.Fun x a) \<and>
                           diagram.cones_map J B (at a D) fa (at a \<chi>) = at a \<chi>'"
          have AaPa: "\<And>a. A.ide a \<Longrightarrow> ?P a (THE fa. ?P a fa)"
          proof -
            fix a
            assume a: "A.ide a"
            have "\<exists>!fa. ?P a fa" using a EU by simp
            thus "?P a (THE fa. ?P a fa)" using a theI' [of "?P a"] by fastforce
          qed
          let ?Fun_f = "\<lambda>a. if A.ide a then (THE fa. ?P a fa) else B.null"
          interpret Fun_x: "functor" A B "\<lambda>a. A_B.Fun x a"
            using x A_B.ide_char [of x] by simp
          interpret Fun_x': "functor" A B "\<lambda>a. A_B.Fun x' a"
            using x' A_B.ide_char [of x'] by simp
          text{*
            The arrows @{text "Fun_f a"} are the components of a natural transformation.
            It is more work to verify the naturality than it seems like it ought to be.
          *}
          interpret \<phi>: transformation_by_components A B
                         "\<lambda>a. A_B.Fun x' a" "\<lambda>a. A_B.Fun x a" ?Fun_f
          proof
            fix a
            assume a: "A.ide a"
            show "?Fun_f a \<in> B.hom (A_B.Fun x' a) (A_B.Fun x a)" using a AaPa by simp
            next
            fix a
            assume a: "A.arr a"
            text{*
\newcommand\xdom{\mathop{\rm dom}}
\newcommand\xcod{\mathop{\rm cod}}
$$\xymatrix{
  {x_{\xdom a}} \drtwocell\omit{\omit(A)} \ar[d]_{\chi_{\xdom a}} \ar[r]^{x_a} & {x_{\xcod a}}
     \ar[d]^{\chi_{\xcod a}} \\
  {D_{\xdom a}} \ar[r]^{D_a} & {D_{\xcod a}} \\
  {x'_{\xdom a}} \urtwocell\omit{\omit(B)} \ar@/^5em/[uu]^{f_{\xdom a}}_{\hspace{1em}(C)} \ar[u]^{\chi'_{\xdom a}}
     \ar[r]_{x'_a} & {x'_{\xcod a}} \ar[u]_{x'_{\xcod a}} \ar@/_5em/[uu]_{f_{\xcod a}}
}$$
            *}
            let ?x_dom_a = "A_B.Fun x (A.dom a)"
            let ?x_cod_a = "A_B.Fun x (A.cod a)"
            let ?x_a = "A_B.Fun x a"
            have x_a: "?x_a \<in> B.hom ?x_dom_a ?x_cod_a"
              using a x A_B.ide_char by simp
            have x_dom_a: "B.ide ?x_dom_a" using a by simp
            have x_cod_a: "B.ide ?x_cod_a" using a by simp
            let ?x'_dom_a = "A_B.Fun x' (A.dom a)"
            let ?x'_cod_a = "A_B.Fun x' (A.cod a)"
            let ?x'_a = "A_B.Fun x' a"
            have x'_a: "?x'_a \<in> B.hom ?x'_dom_a ?x'_cod_a"
              using a x' A_B.ide_char by simp
            have x'_dom_a: "B.ide ?x'_dom_a" using a by simp
            have x'_cod_a: "B.ide ?x'_cod_a" using a by simp
            let ?f_dom_a = "?Fun_f (A.dom a)"
            let ?f_cod_a = "?Fun_f (A.cod a)"
            have f_dom_a: "?f_dom_a \<in> B.hom ?x'_dom_a ?x_dom_a" using a AaPa by simp
            have f_cod_a: "?f_cod_a \<in> B.hom ?x'_cod_a ?x_cod_a" using a AaPa by simp
            interpret D_dom_a: diagram J B "at (A.dom a) D" using a at_ide_is_diagram by simp
            interpret D_cod_a: diagram J B "at (A.cod a) D" using a at_ide_is_diagram by simp
            interpret Da: natural_transformation J B "at (A.dom a) D" "at (A.cod a) D" "at a D"
              using a functor_axioms functor_at_arr_is_transformation by simp
            interpret \<chi>_dom_a: limit_cone J B "at (A.dom a) D" "A_B.Fun x (A.dom a)"
                                              "at (A.dom a) \<chi>"
              using assms(2) a by auto
            interpret \<chi>_cod_a: limit_cone J B "at (A.cod a) D" "A_B.Fun x (A.cod a)"
                                              "at (A.cod a) \<chi>"
              using assms(2) a by auto
            interpret \<chi>'_dom_a: cone J B "at (A.dom a) D" "A_B.Fun x' (A.dom a)" "at (A.dom a) \<chi>'"
              using a cone_\<chi>' cone_at_ide_is_cone by auto
            interpret \<chi>'_cod_a: cone J B "at (A.cod a) D" "A_B.Fun x' (A.cod a)" "at (A.cod a) \<chi>'"
              using a cone_\<chi>' cone_at_ide_is_cone by auto
            text{*
              Now construct cones with apexes @{text "x_dom_a"} and @{text "x'_dom_a"}
              over @{term "at (A.cod a) D"} by forming the vertical composites of
              @{term "at (A.dom a) \<chi>"} and @{term "at (A.cod a) \<chi>'"} with the natural
              transformation @{term "at a D"}.
            *}
            interpret Dao\<chi>_dom_a: vertical_composite J B
                                    \<chi>_dom_a.A.map "at (A.dom a) D" "at (A.cod a) D"
                                    "at (A.dom a) \<chi>" "at a D" ..
            interpret Dao\<chi>_dom_a: cone J B "at (A.cod a) D" ?x_dom_a Dao\<chi>_dom_a.map
              using \<chi>_dom_a.cone_axioms Da.natural_transformation_axioms vcomp_transformation_cone
              by metis
            interpret Dao\<chi>'_dom_a: vertical_composite J B
                                     \<chi>'_dom_a.A.map "at (A.dom a) D" "at (A.cod a) D"
                                     "at (A.dom a) \<chi>'" "at a D" ..
            interpret Dao\<chi>'_dom_a: cone J B "at (A.cod a) D" ?x'_dom_a Dao\<chi>'_dom_a.map
              using \<chi>'_dom_a.cone_axioms Da.natural_transformation_axioms vcomp_transformation_cone
              by metis
            have Dao\<chi>_dom_a: "D_cod_a.cone ?x_dom_a Dao\<chi>_dom_a.map" ..
            have Dao\<chi>'_dom_a: "D_cod_a.cone ?x'_dom_a Dao\<chi>'_dom_a.map" ..
            text{*
              These cones are also obtained by transforming the cones @{term "at (A.cod a) \<chi>"}
              and @{term "at (A.cod a) \<chi>'"} by @{text x_a} and @{text x'_a}, respectively.
            *}
            have A: "Dao\<chi>_dom_a.map = D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>)"
            proof
              fix j
              have "\<not>J.arr j \<Longrightarrow> Dao\<chi>_dom_a.map j = D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>) j"
                using Dao\<chi>_dom_a.is_extensional [of j] \<chi>_cod_a.cone_axioms x_a by force
              moreover have
                   "J.arr j \<Longrightarrow> Dao\<chi>_dom_a.map j = D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>) j"
                  using Dao\<chi>_dom_a.map_simp_2 a x Curry.uncurry_def \<chi>.preserves_hom preserves_dom
                        E.preserves_comp [of "(\<chi> (J.dom j), A.dom a)" "(D j, a)"]
                        E.preserves_comp [of "(x, a)" "(\<chi> j, A.cod a)"] E.map_simp
                        \<chi>.is_natural_1 [of j] \<chi>.is_natural_2 [of j]
                        \<chi>.A.preserves_hom preserves_cod \<chi>_cod_a.cone_axioms
                  by simp
              ultimately show "Dao\<chi>_dom_a.map j = D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>) j"
                by blast
            qed
            have B: "Dao\<chi>'_dom_a.map = D_cod_a.cones_map ?x'_a (at (A.cod a) \<chi>')"
            proof
              fix j
              have "\<not>J.arr j \<Longrightarrow> Dao\<chi>'_dom_a.map j = D_cod_a.cones_map ?x'_a (at (A.cod a) \<chi>') j"
                using Dao\<chi>'_dom_a.is_extensional [of j] \<chi>'_cod_a.cone_axioms x'_a by force
              moreover have
                   "J.arr j \<Longrightarrow> Dao\<chi>'_dom_a.map j = D_cod_a.cones_map ?x'_a (at (A.cod a) \<chi>') j"
                using Dao\<chi>'_dom_a.map_simp_2 a x' \<chi>'.preserves_hom preserves_dom preserves_cod
                      E.preserves_comp [of "(\<chi>' (J.dom j), A.dom a)" "(D j, a)"]
                      E.preserves_comp [of "(x', a)" "(\<chi>' j, A.cod a)"]
                      \<chi>'.is_natural_1 [of j] \<chi>'.is_natural_2 [of j]
                      \<chi>'.A.preserves_hom \<chi>'_cod_a.cone_axioms
                      Curry.uncurry_def E.map_simp
                by simp
              ultimately show "Dao\<chi>'_dom_a.map j = D_cod_a.cones_map ?x'_a (at (A.cod a) \<chi>') j"
                by blast
            qed
            text{*
              Next, we show that @{text f_dom_a}, which is the unique arrow that transforms
              @{text \<chi>_dom_a} into @{text \<chi>'_dom_a}, is also the unique arrow that transforms
              @{text Dao\<chi>_dom_a} into @{text Dao\<chi>'_dom_a}.
            *}
            have C: "D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map = Dao\<chi>'_dom_a.map"
            proof (intro NaturalTransformation.eqI)
              show "natural_transformation J B \<chi>'_dom_a.A.map (at (A.cod a) D) Dao\<chi>'_dom_a.map" ..
              show "natural_transformation J B \<chi>'_dom_a.A.map (at (A.cod a) D)
                      (D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map)"
              proof -
                interpret \<kappa>: cone J B "at (A.cod a) D" ?x'_dom_a
                                  "D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map"
                proof -
                  have 1: "\<And>b b' f. \<lbrakk> f \<in> B.hom b' b; D_cod_a.cone b Dao\<chi>_dom_a.map \<rbrakk>
                                     \<Longrightarrow> D_cod_a.cone b' (D_cod_a.cones_map f Dao\<chi>_dom_a.map)"
                    using D_cod_a.cones_map_mapsto by blast
                  have "D_cod_a.cone ?x_dom_a Dao\<chi>_dom_a.map" ..
                  thus "D_cod_a.cone ?x'_dom_a (D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map)"
                    using f_dom_a 1 [of ?f_dom_a ?x'_dom_a ?x_dom_a] by simp
                qed
                show ?thesis ..
              qed
              show "\<And>j. J.ide j \<Longrightarrow>
                          D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map j = Dao\<chi>'_dom_a.map j"
              proof -
                fix j
                assume j: "J.ide j"
                have "D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map j = B (Dao\<chi>_dom_a.map j) ?f_dom_a"
                  using j f_dom_a Dao\<chi>_dom_a.cone_axioms by simp
                also have "... = B (B (at a D j) (at (A.dom a) \<chi> j)) ?f_dom_a"
                  using j Dao\<chi>_dom_a.map_simp_ide [of j] by simp
                also have "... = B (at a D j) (B (at (A.dom a) \<chi> j) ?f_dom_a)"
                  using j Da.preserves_hom [of j] \<chi>_dom_a.preserves_hom f_dom_a by auto
                also have "... = B (at a D j) (D_dom_a.cones_map ?f_dom_a (at (A.dom a) \<chi>) j)"
                  using j a \<chi>_dom_a.cone_axioms f_dom_a by simp
                also have "... = B (at a D j) (at (A.dom a) \<chi>' j)"
                proof -
                  have "D_dom_a.cones_map ?f_dom_a (at (A.dom a) \<chi>) = at (A.dom a) \<chi>'"
                    using a AaPa [of "A.dom a"] by auto
                  thus ?thesis by simp
                qed
                also have "... = Dao\<chi>'_dom_a.map j"
                  using j Dao\<chi>'_dom_a.map_simp_ide by simp
                finally show "D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map j = Dao\<chi>'_dom_a.map j"
                  by auto
              qed
            qed
            text{*
              Naturality amounts to showing that @{text "C f_cod_a x'_a = C x_a f_dom_a"}.
              To do this, we show that both arrows transform @{term "at (A.cod a) \<chi>"}
              into @{text Dao\<chi>'_cod_a}, thus they are equal by the universality of
              @{term "at (A.cod a) \<chi>"}.
            *}
            have "\<exists>!fa. fa \<in> B.hom ?x'_dom_a ?x_cod_a \<and>
                        D_cod_a.cones_map fa (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
              using Dao\<chi>'_dom_a.cone_axioms a \<chi>_cod_a.is_universal [of ?x'_dom_a Dao\<chi>'_dom_a.map]
              by fast
            moreover have
                 "B ?f_cod_a ?x'_a \<in> B.hom ?x'_dom_a ?x_cod_a \<and>
                  D_cod_a.cones_map (B ?f_cod_a ?x'_a) (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
            proof
              show "B ?f_cod_a ?x'_a \<in> B.hom ?x'_dom_a ?x_cod_a"
                using f_cod_a x'_a by simp
              show "D_cod_a.cones_map (B ?f_cod_a ?x'_a) (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
              proof -
                have 1: "B.seq ?f_cod_a ?x'_a" using f_cod_a x'_a by simp
                hence "D_cod_a.cones_map (B ?f_cod_a ?x'_a) (at (A.cod a) \<chi>)
                         = restrict (D_cod_a.cones_map ?x'_a o D_cod_a.cones_map ?f_cod_a)
                                    (D_cod_a.cones (?x_cod_a))
                                    (at (A.cod a) \<chi>)"
                  using D_cod_a.cones_map_comp [of ?x'_a ?f_cod_a] f_cod_a
                  by simp (* 30 sec *)
                also have "... = D_cod_a.cones_map ?x'_a
                                   (D_cod_a.cones_map ?f_cod_a (at (A.cod a) \<chi>))"
                  using \<chi>_cod_a.cone_axioms by simp
                also have "... = Dao\<chi>'_dom_a.map"
                  using 1 a B AaPa [of "A.cod a"] B.not_arr_null by presburger
                finally show ?thesis by auto
              qed
            qed
            moreover have
                 "B ?x_a ?f_dom_a \<in> B.hom ?x'_dom_a ?x_cod_a \<and>
                  D_cod_a.cones_map (B ?x_a ?f_dom_a) (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
            proof
              show "B ?x_a ?f_dom_a \<in> B.hom ?x'_dom_a ?x_cod_a"
                using f_dom_a x_a by simp
              show "D_cod_a.cones_map (B ?x_a ?f_dom_a) (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
              proof -
                have "B.seq ?x_a ?f_dom_a" using f_dom_a x_a by simp
                hence "D_cod_a.cones_map (B ?x_a ?f_dom_a) (at (A.cod a) \<chi>)
                         = restrict (D_cod_a.cones_map ?f_dom_a o D_cod_a.cones_map ?x_a)
                                    (D_cod_a.cones (?x_cod_a))
                                    (at (A.cod a) \<chi>)"
                  using D_cod_a.cones_map_comp [of ?f_dom_a ?x_a] x_a
                  by simp
                also have "... = D_cod_a.cones_map ?f_dom_a
                                   (D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>))"
                  using \<chi>_cod_a.cone_axioms by simp
                also have "... = Dao\<chi>'_dom_a.map"
                  using A C a AaPa [of "A.dom a"] by presburger
                finally show ?thesis by auto
              qed
            qed
            ultimately show "B ?f_cod_a ?x'_a = B ?x_a ?f_dom_a"
              using a \<chi>_cod_a.is_universal [of ?x'_dom_a Dao\<chi>'_dom_a.map] by blast
          qed
          text{*
            The arrow from @{term x'} to @{term x} in @{text "[A, B]"} determined by
            the natural transformation @{text \<phi>} transforms @{term \<chi>} into @{term \<chi>'}.
            Moreover, it is the unique such arrow, since the components of @{text \<phi>}
            are each determined by universality.
          *}
          let ?f = "A_B.mkArr (\<lambda>a. A_B.Fun x' a) (\<lambda>a. A_B.Fun x a) \<phi>.map"
          have f_in_hom: "?f \<in> A_B.hom x' x"
          proof -
            have arr_f: "A_B.arr ?f"
              using x' x A_B.arr_mkArr [of "A_B.Fun x'" "A_B.Fun x" \<phi>.map]
                    \<phi>.natural_transformation_axioms
              by simp
            moreover have "A_B.mkIde (\<lambda>a. A_B.Fun x a) = x"
              using x A_B.ide_char [of x] A_B.mkArr_Fun A_B.ideD(1) by metis
            moreover have "A_B.mkIde (\<lambda>a. A_B.Fun x' a) = x'"
              using x' A_B.ide_char [of x'] A_B.mkArr_Fun A_B.ideD(1) by metis
            ultimately show ?thesis
              using A_B.dom_char [of ?f] A_B.cod_char [of ?f] by simp
          qed
          have Fun_f: "\<And>a. A.ide a \<Longrightarrow> A_B.Fun ?f a = (THE fa. ?P a fa)"
            using f_in_hom \<phi>.map_simp_ide A_B.Fun_mkArr [of "A_B.Fun x'" "A_B.Fun x" \<phi>.map]
            by fastforce
          have cones_map_f: "cones_map ?f \<chi> = \<chi>'"
            using AaPa Fun_f at_ide_is_diagram assms(2) x x' cone_\<chi> cone_\<chi>' f_in_hom Fun_f
                  cones_map_pointwise [of x \<chi> x' \<chi>' ?f]
            by presburger
          show "?f \<in> A_B.hom x' x \<and> cones_map ?f \<chi> = \<chi>'" using f_in_hom cones_map_f by auto
          show "\<And>f'. f' \<in> A_B.hom x' x \<and> cones_map f' \<chi> = \<chi>' \<Longrightarrow> f' = ?f"
          proof -
            fix f'
            assume f': "f' \<in> A_B.hom x' x \<and> cones_map f' \<chi> = \<chi>'"
            have 0: "\<And>a. A.ide a \<Longrightarrow>
                           diagram.cones_map J B (at a D) (A_B.Fun f' a) (at a \<chi>) = at a \<chi>'"
              using f' cone_\<chi> cone_\<chi>' cones_map_pointwise by blast
            have "f' = A_B.mkArr (A_B.Dom f') (A_B.Cod f') (A_B.Fun f')"
              using f' A_B.mkArr_Fun by simp
            also have "... = ?f"
            proof
              show "A_B.arr (A_B.mkArr (A_B.Dom f') (A_B.Cod f') (A_B.Fun f'))"
                using f' calculation by simp
              show 1: "A_B.Dom f' = A_B.Fun x'" using f' A_B.Fun_dom by auto
              show 2: "A_B.Cod f' = A_B.Fun x" using f' A_B.Fun_cod by auto
              show "A_B.Fun f' = \<phi>.map"
              proof (intro NaturalTransformation.eqI)
                show "natural_transformation A B (A_B.Fun x') (A_B.Fun x) \<phi>.map" ..
                show "natural_transformation A B (A_B.Fun x') (A_B.Fun x) (A_B.Fun f')"
                  using f' 1 2 A_B.arr_char by simp
                show "\<And>a. A.ide a \<Longrightarrow> A_B.Fun f' a = \<phi>.map a"
                proof -
                  fix a
                  assume a: "A.ide a"
                  interpret Da: diagram J B "at a D" using a at_ide_is_diagram by auto
                  have "A_B.Fun f' a \<in> B.hom (A_B.Fun x' a) (A_B.Fun x a)"
                    using a f' x x' A_B.arr_char [of f'] A_B.Fun_dom A_B.Fun_cod
                          natural_transformation.preserves_hom
                    by fastforce
                  hence "?P a (A_B.Fun f' a)" using a 0 [of a] by simp
                  moreover have "?P a (\<phi>.map a)"
                    using a \<phi>.map_simp_ide Fun_f AaPa [of a] by presburger
                  ultimately show "A_B.Fun f' a = \<phi>.map a" using a EU by blast
                qed
              qed
            qed
            finally show "f' = ?f" by auto
          qed
        qed
      qed
    qed

  end

  context functor_category
  begin

    text{*
      A functor category @{text "[A, B]"} has limits of shape @{term J} whenever @{term B}
      has limits of shape @{term J}.
    *}

    lemma has_limits_of_shape_if_target_does:
    assumes "category (J :: 'j comp)"
    and "B.has_limits_of_shape J"
    shows "has_limits_of_shape J"
    proof (unfold has_limits_of_shape_def)
      have "\<And>D. diagram J comp D \<Longrightarrow> (\<exists>x \<chi>. limit_cone J comp D x \<chi>)"
      proof -
        fix D
        assume D: "diagram J comp D"
        interpret J: category J using assms(1) by auto
        interpret JxA: product_category J A ..
        interpret D: diagram J comp D using D by auto
        interpret D: diagram_in_functor_category A B J D ..
        interpret Curry: currying J A B ..
        text{*
          Given diagram @{term D} in @{text "[A, B]"}, choose for each object @{text a}
          of @{text A} a limit cone @{text "(la, \<chi>a)"} for @{text "at a D"} in @{text B}.
        *}
        let ?l = "\<lambda>a. diagram.some_limit J B (D.at a D)"
        let ?\<chi> = "\<lambda>a. diagram.some_limit_cone J B (D.at a D)"
        have l\<chi>: "\<And>a. A.ide a \<Longrightarrow> diagram.limit_cone J B (D.at a D) (?l a) (?\<chi> a)"
        proof -
          fix a
          assume a: "A.ide a"
          interpret Da: diagram J B "D.at a D"
            using a D.at_ide_is_diagram by blast
          show "limit_cone J B (D.at a D) (?l a) (?\<chi> a)"
            using assms(2) B.has_limits_of_shape_def Da.diagram_axioms
                  Da.limit_cone_some_limit_cone
            by auto
        qed
        text{*
          The choice of limit cones induces a limit functor from @{text A} to @{text B}.
        *}
        interpret uncurry_D: diagram JxA.comp B "Curry.uncurry D"
        proof -
          interpret "functor" JxA.comp B "Curry.uncurry D"
            using D.functor_axioms Curry.uncurry_preserves_functors by simp
          interpret binary_functor J A B "Curry.uncurry D" ..
          show "diagram JxA.comp B (Curry.uncurry D)" ..
        qed
        interpret uncurry_D: parametrized_diagram J A B "Curry.uncurry D" ..
        let ?L = "uncurry_D.L ?l ?\<chi>"
        let ?P = "uncurry_D.P ?l ?\<chi>"
        interpret L: "functor" A B ?L
          using l\<chi> uncurry_D.chosen_limits_induce_functor [of ?l ?\<chi>] by simp
        have L_ide: "\<And>a. A.ide a \<Longrightarrow> ?L a = ?l a"
          using uncurry_D.L_ide l\<chi> by fastforce
        have L_arr: "\<And>a. A.arr a \<Longrightarrow> (\<exists>!f. ?P a f) \<and> ?P a (?L a)"
          using uncurry_D.L_arr [of ?l ?\<chi>] l\<chi> by presburger
        text{*
          The functor @{text L} extends to a functor @{text L'} from @{text "JxA"}
          to @{text B} that is constant on @{text J}.
        *}
        let ?L' = "\<lambda>ja. if JxA.arr ja then ?L (snd ja) else B.null"
        let ?P' = "\<lambda>ja. ?P (snd ja)"
        interpret L': "functor" JxA.comp B ?L'
          apply unfold_locales
          (* 5 *) apply auto[1]
          (* 4 *) using L.preserves_arr apply simp
          (* 3 *) using L.preserves_dom apply simp
          (* 2 *) using L.preserves_cod apply simp
          (* 1 *) using L.preserves_comp by auto
        have L'_arr: "\<And>ja. JxA.arr ja \<Longrightarrow> (\<exists>!f. ?P' ja f) \<and> ?P' ja (?L' ja)"
        proof -
          fix ja
          assume ja: "JxA.arr ja"
          have "A.arr (snd ja)" using ja by blast
          thus "(\<exists>!f. ?P' ja f) \<and> ?P' ja (?L' ja)"
            using ja L_arr [of "snd ja"] by presburger
        qed
        have L'_ide: "\<And>ja. \<lbrakk> J.arr (fst ja); A.ide (snd ja) \<rbrakk> \<Longrightarrow> ?L' ja = ?l (snd ja)"
          using L_ide l\<chi> by force
        text{*
          The map that takes an object @{text "(j, a)"} of @{text "JxA"} to the component
          @{text "\<chi> a j"} of the limit cone @{text "\<chi> a"} is a natural transformation
          from @{text L} to uncurry @{text D}.
        *}
        let ?\<chi>' = "\<lambda>ja. ?\<chi> (snd ja) (fst ja)"
        interpret \<chi>': transformation_by_components JxA.comp B ?L' "Curry.uncurry D" ?\<chi>'
        proof
          fix ja
          assume ja: "JxA.ide ja"
          let ?j = "fst ja"
          let ?a = "snd ja"
          interpret \<chi>a: limit_cone J B "D.at ?a D" "?l ?a" "?\<chi> ?a"
            using ja l\<chi> [of ?a] by blast
          show "?\<chi>' ja \<in> B.hom (?L' ja) (Curry.uncurry D ja)"
            using ja L'_ide [of ja] by simp
          next
          fix ja
          assume ja: "JxA.arr ja"
          let ?j = "fst ja"
          let ?a = "snd ja"
          have j: "J.arr ?j" using ja by simp
          have a: "A.arr ?a" using ja by simp
          interpret D_dom_a: diagram J B "D.at (A.dom ?a) D"
            using a D.at_ide_is_diagram by auto
          interpret D_cod_a: diagram J B "D.at (A.cod ?a) D"
            using a D.at_ide_is_diagram by auto
          interpret Da: natural_transformation J B "D.at (A.dom ?a) D" "D.at (A.cod ?a) D"
                                                   "D.at ?a D"
            using a D.functor_axioms D.functor_at_arr_is_transformation by simp
          interpret \<chi>_dom_a: limit_cone J B "D.at (A.dom ?a) D" "?l (A.dom ?a)" "?\<chi> (A.dom ?a)"
            using a l\<chi> [of "A.dom ?a"] by simp
          interpret \<chi>_cod_a: limit_cone J B "D.at (A.cod ?a) D" "?l (A.cod ?a)" "?\<chi> (A.cod ?a)"
            using a l\<chi> [of "A.cod ?a"] by simp
          interpret Dao\<chi>_dom_a: vertical_composite J B
                                  \<chi>_dom_a.A.map "D.at (A.dom ?a) D" "D.at (A.cod ?a) D"
                                  "?\<chi> (A.dom ?a)" "D.at ?a D" ..
          interpret Dao\<chi>_dom_a: cone J B "D.at (A.cod ?a) D" "?l (A.dom ?a)" Dao\<chi>_dom_a.map ..
          show "B (?\<chi>' (JxA.cod ja)) (?L' ja) = B (Curry.uncurry D ja) (?\<chi>' (JxA.dom ja))"
          proof -
            have "B (?\<chi>' (JxA.cod ja)) (?L' ja) = B (?\<chi> (A.cod ?a) (J.cod ?j)) (?L' ja)"
              using ja by fastforce
            also have "... = D_cod_a.cones_map (?L' ja) (?\<chi> (A.cod ?a)) (J.cod ?j)"
              using ja L'_arr [of ja] \<chi>_cod_a.cone_axioms by simp
            also have "... = Dao\<chi>_dom_a.map (J.cod ?j)"
              using ja \<chi>_cod_a.induced_arrowI [of Dao\<chi>_dom_a.map "?l (A.dom ?a)"]
                    Dao\<chi>_dom_a.cone_axioms L'_arr [of ja]
              by presburger
            also have "... = B (D.at ?a D (J.cod ?j)) (D_dom_a.some_limit_cone (J.cod ?j))"
              using ja Dao\<chi>_dom_a.map_simp_ide [of "J.cod ?j"] by fastforce
            also have "... = B (D.at ?a D (J.cod ?j))
                               (B (D.at (A.dom ?a) D ?j) (?\<chi>' (JxA.dom ja)))"
              using ja \<chi>_dom_a.is_natural_1 [of ?j] \<chi>_dom_a.is_natural_2 [of ?j]
                    \<chi>_dom_a.ide_apex by simp
            also have "... = B (B (D.at ?a D (J.cod ?j)) (D.at (A.dom ?a) D ?j))
                               (?\<chi>' (JxA.dom ja))"
              using ja D_dom_a.preserves_hom Da.preserves_hom by auto
            also have "... = B (D.at ?a D ?j) (?\<chi>' (JxA.dom ja))"
            proof -
              have "B (D.at ?a D (J.cod ?j)) (D.at (A.dom ?a) D ?j) =
                      B (Fun (D (J.cod ?j)) ?a) (Fun (D ?j) (A.dom ?a))"
                using ja D.at_simp by auto
              also have "... = Fun (comp (D (J.cod ?j)) (D ?j)) (A ?a (A.dom ?a))"
                using ja Fun_comp [of "D ?j" "D (J.cod ?j)" "A.dom ?a" ?a] D.preserves_hom
                by simp
              also have "... = D.at ?a D ?j"
                using ja D.at_simp [of ?a] dom_simp by force
              finally show ?thesis by auto
           qed
           also have "... = B (Curry.uncurry D ja) (?\<chi>' (JxA.dom ja))"
             using Curry.uncurry_def by simp
           finally show ?thesis by auto
         qed
       qed
       text{*
         Since @{text \<chi>'} is constant on @{text J}, @{text "curry \<chi>'"} is a cone over @{text D}.
       *}
       interpret constL: constant_functor J comp "mkIde ?L"
       proof
         show "ide (mkIde ?L)"
           using ideI_dom L.natural_transformation_axioms mkArr_in_hom [of ?L ?L ?L]
         by blast
       qed
       (* TODO: This seems a little too involved. *)
       have curry_L': "constL.map = Curry.curry ?L' ?L' ?L'"
       proof
         fix j
         have "\<not>J.arr j \<Longrightarrow> constL.map j = Curry.curry ?L' ?L' ?L' j"
           using Curry.curry_def by simp
         moreover have "J.arr j \<Longrightarrow> constL.map j = Curry.curry ?L' ?L' ?L' j"
         proof -
           assume j: "J.arr j"
           show "constL.map j = Curry.curry ?L' ?L' ?L' j"
           proof -
             have "constL.map j = mkIde ?L" using j constL.map_simp by simp
             moreover have "... = mkArr ?L ?L ?L" by simp
             moreover have "... = mkArr (\<lambda>a. ?L' (J.dom j, a)) (\<lambda>a. ?L' (J.cod j, a))
                                        (\<lambda>a. ?L' (j, a))"
             proof (intro mkArr_eqI)
               show "arr (mkArr ?L ?L ?L)"
                 using constL.value_is_ide ideD(1) by blast
               show "?L = (\<lambda>a. ?L' (J.dom j, a))" using j by auto
               show "?L = (\<lambda>a. ?L' (J.cod j, a))" using j by auto
               show "?L = (\<lambda>a. ?L' (j, a))" using j by auto
             qed
             moreover have "... = Curry.curry ?L' ?L' ?L' j"
               using j Curry.curry_def [of ?L' ?L' ?L' j] by auto
             ultimately show ?thesis by force
           qed
         qed
         ultimately show "constL.map j = Curry.curry ?L' ?L' ?L' j" by blast
       qed
       hence uncurry_constL: "Curry.uncurry constL.map = ?L'"
         using L'.natural_transformation_axioms Curry.uncurry_curry [of ?L' ?L' ?L'] by simp
       interpret curry_\<chi>': natural_transformation J comp constL.map D
                             "Curry.curry ?L' (Curry.uncurry D) \<chi>'.map"
       proof -
         have 1: "Curry.curry (Curry.uncurry D) (Curry.uncurry D) (Curry.uncurry D) = D"
           using Curry.curry_uncurry [of D D] D.functor_axioms D.natural_transformation_axioms
           by blast
         thus "natural_transformation J comp constL.map D
                 (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map)"
           using Curry.curry_preserves_transformations curry_L' \<chi>'.natural_transformation_axioms
           by force
       qed
       interpret curry_\<chi>': cone J comp D "mkIde ?L" "Curry.curry ?L' (Curry.uncurry D) \<chi>'.map" ..
       text{*
         The value of @{text curry_\<chi>'} at each object @{text a} of @{text A} is the
         limit cone @{text "\<chi> a"}, hence @{text "curry_\<chi>'"} is a limit cone.
       *}
       have 1: "\<And>a. A.ide a \<Longrightarrow> D.at a (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map) = ?\<chi> a"
       proof -
         fix a
         assume a: "A.ide a"
         have "D.at a (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map) =
                 (\<lambda>j. Curry.uncurry (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map) (j, a))"
           using a by simp
         moreover have "... = (\<lambda>j. \<chi>'.map (j, a))"
           using a Curry.uncurry_curry [of ?L' "Curry.uncurry D" \<chi>'.map]
                 \<chi>'.natural_transformation_axioms
           by simp
         moreover have "... = ?\<chi> a"
         proof (intro NaturalTransformation.eqI)
           interpret \<chi>a: limit_cone J B "D.at a D" "?l a" "?\<chi> a" using a l\<chi> by simp
           interpret \<chi>': binary_functor_transformation J A B ?L' "Curry.uncurry D" \<chi>'.map ..
           show "natural_transformation J B \<chi>a.A.map (D.at a D) (?\<chi> a)" ..
           show "natural_transformation J B \<chi>a.A.map (D.at a D) (\<lambda>j. \<chi>'.map (j, a))"
           proof -
             have "\<chi>a.A.map = (\<lambda>j. ?L' (j, a))"
               using a \<chi>a.A.map_def L'_ide by auto
             thus ?thesis
               using a \<chi>'.fixing_ide_gives_natural_transformation_2 [of a] by simp
           qed
           fix j
           assume j: "J.ide j"
           show "\<chi>'.map (j, a) = ?\<chi> a j"
             using a j \<chi>'.map_simp_ide [of "(j, a)"] by simp
         qed
         ultimately show "D.at a (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map) = ?\<chi> a" by simp
       qed
       hence 2: "\<And>a. A.ide a \<Longrightarrow> diagram.limit_cone J B (D.at a D) (?l a)
                                (D.at a (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map))"
         using l\<chi> by simp
       hence "limit_cone J comp D (mkIde ?L) (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map)"
       proof -
         have "\<And>a. A.ide a \<Longrightarrow> Fun (mkIde ?L) a = ?l a"
           using L.functor_axioms L_ide by simp
         thus ?thesis
           using 1 2 curry_\<chi>'.cone_axioms curry_L'
                 D.cone_is_limit_if_pointwise_limit
                   [of "mkIde ?L" "Curry.curry ?L' (Curry.uncurry D) \<chi>'.map"]
           by simp
       qed
       thus "\<exists>x \<chi>. limit_cone J local.comp D x \<chi>" by blast
     qed
     thus "\<forall>D. diagram J comp D \<longrightarrow> (\<exists>x \<chi>. limit_cone J local.comp D x \<chi>)" by blast
    qed

    lemma has_limits_if_target_does:
    assumes "B.has_limits (undefined :: 'j)"
    shows "has_limits (undefined :: 'j)"
      using assms B.has_limits_def has_limits_def has_limits_of_shape_if_target_does by fast

  end

  section "The Yoneda Functor Preserves Limits"

  text{*
    In this section, we show that the Yoneda functor from @{text C} to @{text "[Cop, S]"}
    preserves limits.
  *}

  context yoneda_functor
  begin

    lemma preserves_limits:
    fixes J :: "'j comp"
    assumes "diagram J C D" and "diagram.has_as_limit J C D a"
    shows "diagram.has_as_limit J Cop_S.comp (map o D) (map a)"
    proof -
      text{*
        The basic idea of the proof is as follows:
        If @{text \<chi>} is a limit cone in @{text C}, then for every object @{text a'}
        of @{text Cop} the evaluation of @{text "Y o \<chi>"} at @{text a'} is a limit cone
        in @{text S}.  By the results on limits in functor categories,
        this implies that @{text "Y o \<chi>"} is a limit cone in @{text "[Cop, S]"}.
      *}
      interpret J: category J using assms(1) diagram_def by auto
      interpret D: diagram J C D using assms(1) by auto
      from assms(2) obtain \<chi> where \<chi>: "D.limit_cone a \<chi>" by blast
      interpret \<chi>: limit_cone J C D a \<chi> using \<chi> by auto
      have a: "C.ide a" using \<chi>.ide_apex by auto
      interpret YoD: diagram J Cop_S.comp "map o D"
        using D.diagram_axioms functor_axioms preserves_diagrams [of J D] by simp
      interpret YoD: diagram_in_functor_category Cop.comp S J "map o D" ..
      interpret Yo\<chi>: cone J Cop_S.comp "map o D" "map a" "map o \<chi>"
        using \<chi>.cone_axioms preserves_cones [of J D a \<chi>] by blast
      have "\<And>a'. C.ide a' \<Longrightarrow>
                   limit_cone J S (YoD.at a' (map o D))
                                  (Cop_S.Fun (map a) a') (YoD.at a' (map o \<chi>))"
      proof -
        fix a'
        assume a': "C.ide a'"
        interpret A': constant_functor J C a'
          apply unfold_locales using a' by auto
        interpret YoD_a': diagram J S "YoD.at a' (map o D)"
          using a' YoD.at_ide_is_diagram by simp
        interpret Yo\<chi>_a': cone J S "YoD.at a' (map o D)"
                                   "Cop_S.Fun (map a) a'" "YoD.at a' (map o \<chi>)"
          using a' YoD.cone_at_ide_is_cone [of "map a" "map o \<chi>" a' ] Yo\<chi>.cone_axioms by blast
        have eval_at_ide: "\<And>j. J.ide j \<Longrightarrow> YoD.at a' (map \<circ> D) j = Hom.map (a', D j)"
        proof -
          fix j
          assume j: "J.ide j"
          have "YoD.at a' (map \<circ> D) j = Cop_S.Fun (map (D j)) a'"
            using a' j YoD.at_simp [of a' j "map o D"] YoD.preserves_arr [of j] by auto
          also have "... = Y (D j) a'" using Y_def by simp
          also have "... = Hom.map (a', D j)" using a' j D.preserves_arr by simp
          finally show "YoD.at a' (map \<circ> D) j = Hom.map (a', D j)" by auto
        qed
        have eval_at_arr: "\<And>j. J.arr j \<Longrightarrow> YoD.at a' (map \<circ> \<chi>) j = Hom.map (a', \<chi> j)"
        proof -
          fix j
          assume j: "J.arr j"
          have "YoD.at a' (map \<circ> \<chi>) j = Cop_S.Fun ((map o \<chi>) j) a'"
            using a' j YoD.at_simp [of a' j "map o \<chi>"] preserves_arr \<chi>.preserves_arr [of j]
            by fastforce
          also have "... = Y (\<chi> j) a'" using Y_def by simp
            also have "... = Hom.map (a', \<chi> j)" using a' j \<chi>.preserves_arr by simp
          finally show "YoD.at a' (map \<circ> \<chi>) j = Hom.map (a', \<chi> j)" by auto
        qed
        have Fun_map_a_a': "Cop_S.Fun (map a) a' = Hom.map (a', a)"
          using a a' map_simp [of a] preserves_arr [of a]
                Cop_S.Fun_mkArr [of "\<lambda>f1. Hom.map (f1, C.dom a)" "\<lambda>f1. Hom.map (f1, C.cod a)"
                                    "\<lambda>f1. Hom.map (f1, a)"]
          by simp
        show "limit_cone J S (YoD.at a' (map o D))
                             (Cop_S.Fun (map a) a') (YoD.at a' (map o \<chi>))"
        proof
          fix x \<sigma>
          assume \<sigma>: "YoD_a'.cone x \<sigma>"
          interpret \<sigma>: cone J S "YoD.at a' (map o D)" x \<sigma> using \<sigma> by auto
          have x: "S.ide x" using \<sigma>.ide_apex by simp
          text{*
            For each object @{text j} of @{text J}, the component @{text "\<sigma> j"}
            is an arrow in @{text "S.hom x (Hom.map (a', D j))"}.
            Each element @{text "e \<in> S.set x"} therefore determines an arrow
            @{text "\<psi> (a', D j) (S.Fun (\<sigma> j) e) \<in> C.hom a' (D j)"}.
            These arrows are the components of a cone @{text "\<kappa> e"} over @{term D}
            with apex @{term a'}.
          *}
          have \<sigma>j: "\<And>j. J.ide j \<Longrightarrow> \<sigma> j \<in> S.hom x (Hom.map (a', D j))"
            using eval_at_ide \<sigma>.preserves_hom by simp
          have \<kappa>: "\<And>e. e \<in> S.set x \<Longrightarrow>
                        transformation_by_components J C A'.map D (\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e))"
          proof -
            fix e
            assume e: "e \<in> S.set x"
            show "transformation_by_components J C A'.map D (\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e))"
            proof
              fix j
              assume j: "J.ide j"
              show "\<psi> (a', D j) (S.Fun (\<sigma> j) e) \<in> C.hom (A'.map j) (D j)"
                using j e \<sigma>j S.Fun_mapsto [of "\<sigma> j"] \<sigma>.preserves_hom [of j j j] \<sigma>.ide_apex
                      Hom.\<psi>_mapsto [of "A'.map j" "D j"] A'.preserves_ide Hom.set_map
                by auto
              next
              fix j
              assume j: "J.arr j"
              show "C (\<psi> (a', D (J.cod j)) (S.Fun (\<sigma> (J.cod j)) e)) (A'.map j) =
                      C (D j) (\<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e))"
              proof -
                have 1: "Y (D j) a' = 
                          S.mkArr (Hom.set (a', D (J.dom j))) (Hom.set (a', D (J.cod j)))
                                  (\<phi> (a', D (J.cod j)) \<circ> C (D j) \<circ> \<psi> (a', D (J.dom j)))"
                  using j a' D.preserves_hom [of j "J.dom j" "J.cod j"]
                        Y_arr_ide [of a' "D j" "D (J.dom j)" "D (J.cod j)"] by simp
                have "C (\<psi> (a', D (J.cod j)) (S.Fun (\<sigma> (J.cod j)) e)) (A'.map j) =
                        C (\<psi> (a', D (J.cod j)) (S.Fun (\<sigma> (J.cod j)) e)) a'"
                  using A'.map_simp j by simp
                also have "... = \<psi> (a', D (J.cod j)) (S.Fun (\<sigma> (J.cod j)) e)"
                  using j e \<sigma>j [of "J.cod j"] S.Fun_mapsto [of "\<sigma> (J.cod j)"]
                        \<sigma>.preserves_arr [of "J.cod j" ]a' j Hom.\<psi>_mapsto [of a' "D (J.cod j)"]
                        Hom.set_map
                  by force
                also have "... = \<psi> (a', D (J.cod j)) (S.Fun (Y (D j) a') (S.Fun (\<sigma> (J.dom j)) e))"
                proof -
                  have "S.Fun (Y (D j) a') (S.Fun (\<sigma> (J.dom j)) e) =
                          (S.Fun (Y (D j) a') o S.Fun (\<sigma> (J.dom j))) e"
                    by simp
                  also have "... = S.Fun (S (Y (D j) a') (\<sigma> (J.dom j))) e"
                    using 1 j a' Y_arr_ide [of a' "D j"] \<sigma>j [of "J.dom j"] e
                          S.Fun_comp [of "\<sigma> (J.dom j)" "Y (D j) a'"]
                    by force
                  also have "... = S.Fun (\<sigma> (J.cod j)) e"
                    using j \<sigma>.is_natural_1 [of j] \<sigma>.is_natural_2 [of j] \<sigma>.ide_apex
                          a' YoD.at_simp [of a' j "map o D"] YoD.preserves_arr [of j]
                          Y_def [of "D j"]
                    by fastforce
                  finally have "S.Fun (Y (D j) a') (S.Fun (\<sigma> (J.dom j)) e) = S.Fun (\<sigma> (J.cod j)) e"
                    by auto
                  thus ?thesis by simp
                qed
                also have "... = C (D j) (\<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e))"
                proof -
                  have "\<psi> (a', D (J.cod j)) (S.Fun (Y (D j) a') (S.Fun (\<sigma> (J.dom j)) e))
                           = C (D j) (\<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e))"
                  proof -
                    have "S.Fun (Y (D j) a') (S.Fun (\<sigma> (J.dom j)) e) =
                             \<phi> (a', D (J.cod j))
                               (C (D j) (\<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e)))"
                       using 1 a' j e \<sigma>j D.preserves_hom [of j "J.dom j" "J.cod j"]
                             Y_arr_ide [of a' "D j" "D (J.dom j)" "D (J.cod j)"]
                             S.Fun_mkArr restrict_apply A'.map_simp [of j]
                             S.Fun_mapsto [of "\<sigma> (J.dom j)"]
                       by auto
                    moreover have "C (D j) (\<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e))
                                      \<in> C.hom a' (D (J.cod j))"
                    proof -
                      have "\<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e) \<in> C.hom a' (D (J.dom j))"
                        using a' j e \<sigma>j Hom.\<psi>_mapsto [of a' "D (J.dom j)"]
                              D.preserves_ide [of "J.dom j"]
                              S.Fun_mapsto [of "\<sigma> (J.dom j)"] Hom.set_map
                        by auto
                      thus ?thesis using j D.preserves_hom by simp
                    qed
                    ultimately show ?thesis using a' j Hom.\<psi>_\<phi> by simp
                  qed
                  thus ?thesis by simp
                qed
                finally show ?thesis by auto
              qed
            qed
          qed
          let ?\<kappa> = "\<lambda>e. transformation_by_components.map J C A'.map
                          (\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e))"
          have cone_\<kappa>e: "\<And>e. e \<in> S.set x \<Longrightarrow> D.cone a' (?\<kappa> e)"
          proof -
            fix e
            assume e: "e \<in> S.set x"
            interpret \<kappa>e: transformation_by_components J C A'.map D
                            "\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e)"
              using e \<kappa> by blast
            show "D.cone a' (?\<kappa> e)" ..
          qed
          text{*
            Since @{text "\<kappa> e"} is a cone for each element @{text e} of @{text "S.set x"},
            by the universal property of the limit cone @{text \<chi>} there is a unique arrow
            @{text "fe \<in> C.hom a' a"} that transforms @{text \<chi>} to @{text "\<kappa> e"}.
          *}
          have ex_fe: "\<And>e. e \<in> S.set x \<Longrightarrow> \<exists>!fe. fe \<in> C.hom a' a \<and> D.cones_map fe \<chi> = ?\<kappa> e"
            using cone_\<kappa>e \<chi>.is_universal by presburger
          text{*
            The map taking @{text "e \<in> S.set x"} to @{text "fe \<in> C.hom a' a"}
            determines an arrow @{text "f \<in> S.hom x (Hom (a', a))"} that
            transforms the cone obtained by evaluating @{text "Y o \<chi>"} at @{text a'}
            to the cone @{text \<sigma>}.
          *}
          let ?f = "S.mkArr (S.set x) (Hom.set (a', a))
                            (\<lambda>e. \<phi> (a', a) (\<chi>.induced_arrow a' (?\<kappa> e)))"
          have 0: "(\<lambda>e. \<phi> (a', a) (\<chi>.induced_arrow a' (?\<kappa> e))) \<in> S.set x \<rightarrow> Hom.set (a', a)"
          proof
            fix e
            assume e: "e \<in> S.set x"
            interpret \<kappa>e: cone J C D a' "?\<kappa> e" using e cone_\<kappa>e by simp
            have "\<chi>.induced_arrow a' (?\<kappa> e) \<in> C.hom a' a"
              using a a' e ex_fe [of e] \<chi>.induced_arrowI [of "?\<kappa> e" a']
                    \<kappa>e.cone_axioms
              by simp
            thus "\<phi> (a', a) (\<chi>.induced_arrow a' (?\<kappa> e)) \<in> Hom.set (a', a)"
              using a a' Hom.\<phi>_mapsto [of a' a] by auto
          qed
          hence f: "?f \<in> S.hom x (Hom.map (a', a))"
            using a a' \<sigma>.ide_apex S.arr_mkArr [of "S.set x" "Hom.set (a', a)"]
                  Hom.set_subset_Univ [of a' a] by simp
          have "YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) = \<sigma>"
          proof (intro NaturalTransformation.eqI)
            show "natural_transformation J S \<sigma>.A.map (YoD.at a' (map o D)) \<sigma>"
              using \<sigma>.natural_transformation_axioms by auto
            have 1: "S.cod ?f = Cop_S.Fun (map a) a'"
              using f Fun_map_a_a' by force
            interpret YoD_a'of: cone J S "YoD.at a' (map o D)" x
                                     "YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>))"
              using a a' f Yo\<chi>_a'.cone_axioms YoD_a'.cones_map_mapsto [of ?f]
                    map_simp [of a] Cop_S.Fun_mkArr preserves_arr [of a]
              by force
            show "natural_transformation J S \<sigma>.A.map (YoD.at a' (map o D))
                                         (YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)))" ..
            fix j
            assume j: "J.ide j"
            have "YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) j = S (YoD.at a' (map o \<chi>) j) ?f"
              using Fun_map_a_a' f j Yo\<chi>_a'.cone_axioms by fastforce
            also have "S (YoD.at a' (map o \<chi>) j) ?f = \<sigma> j"
            proof (intro S.arr_eqI)
              show "S.par (S (YoD.at a' (map o \<chi>) j) ?f) (\<sigma> j)"
                using 1 f j x YoD_a'.preserves_hom by force
              show "S.Fun (S (YoD.at a' (map o \<chi>) j) ?f) = S.Fun (\<sigma> j)"
              proof
                fix e
                have "e \<notin> S.set x \<Longrightarrow> S.Fun (S (YoD.at a' (map o \<chi>) j) ?f) e = S.Fun (\<sigma> j) e"
                proof -
                  assume e: "e \<notin> S.set x"
                  have "S.Fun (S (YoD.at a' (map o \<chi>) j) ?f) e = undefined"
                    using 1 e f j x YoD_a'.preserves_hom S.Fun_mapsto 
                          extensional_arb [of "S.Fun (S (YoD.at a' (map o \<chi>) j) ?f)" "S.set x" e]
                    by fastforce
                  also have "... = S.Fun (\<sigma> j) e"
                  proof -
                    have "\<sigma> j \<in> S.hom x (YoD.at a' (map o D) (J.cod j))"
                      using j \<sigma>.preserves_hom [of j "J.dom j" "J.cod j"] \<sigma>.A.map_simp [of j]
                      by force
                    thus ?thesis
                      using e S.Fun_mapsto extensional_arb by fastforce
                  qed
                  finally show ?thesis by auto
                qed
                moreover have "e \<in> S.set x \<Longrightarrow>
                                 S.Fun (S (YoD.at a' (map o \<chi>) j) ?f) e = S.Fun (\<sigma> j) e"
                proof -
                  assume e: "e \<in> S.set x"
                  interpret \<kappa>e: transformation_by_components J C A'.map D
                                  "\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e)"
                    using e \<kappa> by blast
                  interpret \<kappa>e: cone J C D a' "?\<kappa> e" using e cone_\<kappa>e by simp
                  have induced_arrow: "\<chi>.induced_arrow a' (?\<kappa> e) \<in> C.hom a' a"
                    using a a' e ex_fe [of e] \<chi>.induced_arrowI [of "?\<kappa> e" a'] \<kappa>e.cone_axioms
                    by simp
                  have "S.Fun (S (YoD.at a' (map o \<chi>) j) ?f) e =
                          restrict (S.Fun (YoD.at a' (map o \<chi>) j) o S.Fun ?f) (S.set x) e"
                    using 1 e f j S.Fun_comp [of ?f "YoD.at a' (map o \<chi>) j"]
                          YoD_a'.preserves_hom
                    by force
                  also have "... = (\<phi> (a', D j) o C (\<chi> j) o \<psi> (a', a)) (S.Fun ?f e)"
                    using j a' f e x \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                          \<chi>.A.map_simp [of "J.dom j"] Hom.map_simp_2 [of a' "\<chi> j"]
                          S.Fun_mkArr [of "Hom.set (a', a)" "Hom.set (a', D j)"
                                         "\<phi> (a', D j) o C (\<chi> j) o \<psi> (a', a)"]
                          restrict_apply [of "\<phi> (a', D j) o C (\<chi> j) o \<psi> (a', a)"
                                             "Hom.set (a', a)" "S.Fun ?f e"]
                          Hom.preserves_arr [of "(a', \<chi> j)"] eval_at_arr
                    by auto
                  also have "... = (\<phi> (a', D j) o C (\<chi> j) o \<psi> (a', a))
                                     (\<phi> (a', a) (\<chi>.induced_arrow a' (?\<kappa> e)))"
                    using e f S.Fun_mkArr [of "S.set x" "Hom.set (a', a)"
                                             "\<lambda>e. \<phi> (a', a) (\<chi>.induced_arrow a' (?\<kappa> e))"]
                    by fastforce
                  also have "... = \<phi> (a', D j) (D.cones_map (\<chi>.induced_arrow a' (?\<kappa> e)) \<chi> j)"
                      using a a' e j 0 Hom.\<psi>_\<phi> [of "\<chi>.induced_arrow a' (?\<kappa> e)" a' a] induced_arrow
                            \<chi>.cone_axioms
                      by auto
                  also have "... = \<phi> (a', D j) (?\<kappa> e j)"
                    using \<chi>.induced_arrowI [of "?\<kappa> e" a'] \<kappa>e.cone_axioms by fastforce
                  also have "... = \<phi> (a', D j) (\<psi> (a', D j) (S.Fun (\<sigma> j) e))"
                    using j \<kappa>e.map_def [of j] by simp
                  also have "... = S.Fun (\<sigma> j) e"
                    using a' e x j eval_at_ide \<sigma>.preserves_hom [of j j j] S.Fun_mapsto [of "\<sigma> j"]
                          \<sigma>.A.map_simp [of j] D.preserves_arr Hom.\<phi>_\<psi> [of a' "D j" "S.Fun (\<sigma> j) e"]
                          Hom.set_map
                    by fastforce
                  finally show "S.Fun (S (YoD.at a' (map o \<chi>) j) ?f) e = S.Fun (\<sigma> j) e"
                    by auto
                qed
                ultimately show "S.Fun (S (YoD.at a' (map o \<chi>) j) ?f) e = S.Fun (\<sigma> j) e"
                  by auto
              qed
            qed
            finally show "YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) j = \<sigma> j" by auto
          qed
          hence ff: "?f \<in> S.hom x (Hom.map (a', a)) \<and> YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) = \<sigma>"
            using f by auto
          text{*
            Any other arrow @{text "f' \<in> S.hom x (Hom.map (a', a))"} that
            transforms the cone obtained by evaluating @{text "Y o \<chi>"} at @{term a'}
            to the cone @{term \<sigma>}, must equal @{text f}, showing that @{text f}
            is unique.
          *}
          moreover have "\<And>f'. f' \<in> S.hom x (Hom.map (a', a)) \<and>
                              YoD_a'.cones_map f' (YoD.at a' (map o \<chi>)) = \<sigma>
                                \<Longrightarrow> f' = ?f"
          proof -
            fix f'
            assume f': "f' \<in> S.hom x (Hom.map (a', a)) \<and>
                        YoD_a'.cones_map f' (YoD.at a' (map o \<chi>)) = \<sigma>"
            show "f' = ?f"
            proof (intro S.arr_eqI)
              show "S.par f' ?f" using f f' by simp
              show "S.Fun f' = S.Fun ?f"
              proof
                fix e
                have "e \<notin> S.set x \<Longrightarrow> S.Fun f' e = S.Fun ?f e"
                  using f f' x S.Fun_mapsto extensional_arb by fastforce
                moreover have "e \<in> S.set x \<Longrightarrow> S.Fun f' e = S.Fun ?f e"
                proof -
                  assume e: "e \<in> S.set x"
                  have 1: "\<psi> (a', a) (S.Fun f' e) \<in> C.hom a' a"
                    using a a' e f' S.Fun_mapsto [of f'] Hom.\<psi>_mapsto [of a' a] Hom.set_map
                    by auto
                  have 2: "\<psi> (a', a) (S.Fun ?f e) \<in> C.hom a' a"
                    using a a' e f S.Fun_mapsto [of ?f] Hom.\<psi>_mapsto [of a' a] by auto
                  interpret \<chi>ofe: cone J C D a' "D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi>"
                    using 2 \<chi>.cone_axioms D.cones_map_mapsto [of "\<psi> (a', a) (S.Fun ?f e)"]
                    by force
                  have f'e: "S.Fun f' e \<in> Hom.set (a', a)"
                    using a a' f' e x S.Fun_mapsto [of f'] Hom.set_map by auto
                  have fe: "S.Fun ?f e \<in> Hom.set (a', a)"
                    using f e x S.Fun_mapsto [of ?f] by auto
                  have A: "\<And>h j. h \<in> C.hom a' a \<Longrightarrow> J.arr j \<Longrightarrow>
                                   S.Fun (YoD.at a' (map o \<chi>) j) (\<phi> (a', a) h)
                                     = \<phi> (a', D (J.cod j)) (C (\<chi> j) h)"
                  proof -
                    fix h j
                    assume j: "J.arr j"
                    assume h: "h \<in> C.hom a' a"
                    have "S.Fun (YoD.at a' (map o \<chi>) j) = S.Fun (Y (\<chi> j) a')"
                      using a' j YoD.at_simp [of a' j "map o \<chi>"] Y_def [of "\<chi> j"]
                            Yo\<chi>.preserves_arr [of j]
                      by simp
                    also have "... = restrict (\<phi> (a', D (J.cod j)) \<circ> C (\<chi> j) \<circ> \<psi> (a', a))
                                              (Hom.set (a', a))"
                    proof -
                      have "S.arr (Y (\<chi> j) a') \<and>
                            Y (\<chi> j) a' = S.mkArr (Hom.set (a', a)) (Hom.set (a', D (J.cod j)))
                                                 (\<phi> (a', D (J.cod j)) \<circ> C (\<chi> j) \<circ> \<psi> (a', a))"
                        using a' j \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                              Y_arr_ide [of a' "\<chi> j" a "D (J.cod j)"]
                              \<chi>.A.map_simp [of "J.dom j"]
                        by fastforce
                      thus ?thesis
                        using S.Fun_mkArr [of "Hom.set (a', a)" "Hom.set (a', D (J.cod j))"
                                             "\<phi> (a', D (J.cod j)) \<circ> C (\<chi> j) \<circ> \<psi> (a', a)"]
                        by metis
                    qed
                    finally have "S.Fun (YoD.at a' (map o \<chi>) j)
                                    = restrict (\<phi> (a', D (J.cod j)) \<circ> C (\<chi> j) \<circ> \<psi> (a', a))
                                               (Hom.set (a', a))"
                      by auto
                    hence "S.Fun (YoD.at a' (map o \<chi>) j) (\<phi> (a', a) h)
                              = (\<phi> (a', D (J.cod j)) \<circ> C (\<chi> j) \<circ> \<psi> (a', a)) (\<phi> (a', a) h)"
                      using a a' h Hom.\<phi>_mapsto by auto
                    also have "... = \<phi> (a', D (J.cod j)) (C (\<chi> j) h)"
                      using a a' h Hom.\<psi>_\<phi> by simp
                    finally show "S.Fun (YoD.at a' (map o \<chi>) j) (\<phi> (a', a) h)
                                    = \<phi> (a', D (J.cod j)) (C (\<chi> j) h)"
                      by auto
                  qed
                  have "D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> =
                          D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi>"
                  proof
                    fix j
                    have "\<not>J.arr j \<Longrightarrow> D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                                          D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                      using 1 2 \<chi>.cone_axioms by simp
                    moreover have "J.arr j \<Longrightarrow> D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                                                  D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                    proof -
                      assume j: "J.arr j"
                      have 3: "S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun f' e) = S.Fun (\<sigma> j) e"
                        using Fun_map_a_a' a a' j f' e x
                              Yo\<chi>_a'.preserves_hom [of j "J.dom j" "J.cod j"]
                              Yo\<chi>_a'.A.map_simp [of "J.dom j"] eval_at_ide [of "J.cod j"]
                              Yo\<chi>_a'.cone_axioms
                         by auto
                      have 4: "S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun ?f e) = S.Fun (\<sigma> j) e"
                      proof -
                        have "S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun ?f e)
                                = (S.Fun (YoD.at a' (map o \<chi>) j) o S.Fun ?f) e"
                          by simp
                        also have "... = S.Fun (S (YoD.at a' (map o \<chi>) j) ?f) e"
                          using Fun_map_a_a' a a' j f e x
                                Yo\<chi>_a'.preserves_hom [of j "J.dom j" "J.cod j"]
                                Yo\<chi>_a'.A.map_simp [of "J.dom j"] eval_at_ide [of "J.cod j"]
                          by force
                        also have "... = S.Fun (\<sigma> j) e"
                        proof -
                          have "S (YoD.at a' (map o \<chi>) j) ?f =
                                  YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) j"
                            using j f Yo\<chi>_a'.cone_axioms Fun_map_a_a' by simp
                          thus ?thesis using j ff by presburger
                        qed
                        finally show ?thesis by auto
                      qed
                      have "D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                              C (\<chi> j) (\<psi> (a', a) (S.Fun f' e))"
                        using j 1 \<chi>.cone_axioms by simp
                      also have "... = \<psi> (a', D (J.cod j)) (S.Fun (\<sigma> j) e)"
                      proof -
                        have "\<psi> (a', D (J.cod j)) (S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun f' e)) =
                                \<psi> (a', D (J.cod j))
                                  (\<phi> (a', D (J.cod j)) (C (\<chi> j) (\<psi> (a', a) (S.Fun f' e))))"
                          using j a a' f'e A [of "\<psi> (a', a) (S.Fun f' e)" j]
                                Hom.\<phi>_\<psi> [of a' a "S.Fun f' e"] Hom.\<psi>_mapsto [of a' a]
                          by force
                        moreover have "C (\<chi> j) (\<psi> (a', a) (S.Fun f' e)) \<in> C.hom a' (D (J.cod j))"
                          using a a' j f'e Hom.\<psi>_mapsto [of a' a]
                                \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                                \<chi>.A.map_simp [of "J.cod j"]
                          by force
                        ultimately show ?thesis
                          using a a' 3 4 Hom.\<psi>_\<phi> [of a' "D (J.cod j)"] by auto
                      qed
                      also have "... = C (\<chi> j) (\<psi> (a', a) (S.Fun ?f e))"
                      proof -
                        have "S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun ?f e) =
                                \<phi> (a', D (J.cod j)) (C (\<chi> j) (\<psi> (a', a) (S.Fun ?f e)))"
                          using j a a' fe A [of "\<psi> (a', a) (S.Fun ?f e)" j]
                                Hom.\<phi>_\<psi> [of a' a "S.Fun ?f e"] Hom.\<psi>_mapsto [of a' a]
                          by auto
                        hence "\<psi> (a', D (J.cod j)) (S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun ?f e)) =
                                \<psi> (a', D (J.cod j))
                                  (\<phi> (a', D (J.cod j)) (C (\<chi> j) (\<psi> (a', a) (S.Fun ?f e))))"
                          by simp
                        moreover have "C (\<chi> j) (\<psi> (a', a) (S.Fun ?f e)) \<in> C.hom a' (D (J.cod j))"
                          using a a' j fe Hom.\<psi>_mapsto [of a' a]
                                \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                                \<chi>.A.map_simp [of "J.cod j"]
                          by force
                        ultimately show ?thesis
                          using a a' 3 4 Hom.\<psi>_\<phi> [of a' "D (J.cod j)"] by auto
                      qed
                      also have "... = D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                        using j 2 \<chi>.cone_axioms by simp
                      finally show "D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                                      D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                        by auto
                    qed
                    ultimately show "D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                                       D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                      by auto
                  qed
                  hence "\<psi> (a', a) (S.Fun f' e) = \<psi> (a', a) (S.Fun ?f e)"
                    using 1 2 \<chi>ofe.cone_axioms \<chi>.cone_axioms \<chi>.is_universal by fast
                  hence "\<phi> (a', a) (\<psi> (a', a) (S.Fun f' e)) = \<phi> (a', a) (\<psi> (a', a) (S.Fun ?f e))"
                    by simp
                  thus "S.Fun f' e = S.Fun ?f e"
                    using a a' fe f'e Hom.\<phi>_\<psi> [of a' a] by force
                qed
                ultimately show "S.Fun f' e = S.Fun ?f e" by auto
              qed
            qed
          qed
          ultimately have "\<exists>!f. f \<in> S.hom x (Hom.map (a', a)) \<and>
                                YoD_a'.cones_map f (YoD.at a' (map o \<chi>)) = \<sigma>"
            using ex1I [of "\<lambda>f. f \<in> S.hom x (Hom.map (a', a)) \<and>
                                YoD_a'.cones_map f (YoD.at a' (map o \<chi>)) = \<sigma>"]
            by presburger
          thus "\<exists>!f. f \<in> S.hom x (Cop_S.Fun (map a) a') \<and>
                     YoD_a'.cones_map f (YoD.at a' (map o \<chi>)) = \<sigma>"
            using a a' Y_def [of a] by simp
        qed
      qed
      thus "YoD.has_as_limit (map a)"
        using YoD.cone_is_limit_if_pointwise_limit Yo\<chi>.cone_axioms by auto
    qed

  end

end
