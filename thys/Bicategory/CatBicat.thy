(*  Title:       CatBicat
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2021
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Bicategory of Categories"

text \<open>
  In this section we construct a bicategory whose objects correspond to categories having arrows
  in a given type, whose 1-cells correspond to functors between such categories, and whose 2-cells
  correspond to natural transformations between such functors.  We show that the bicategory that
  results from the construction is strict.
\<close>

theory CatBicat
imports Bicategory.Strictness ConcreteBicategory
begin

  locale catbicat
  begin

    abbreviation ARR
    where "ARR A B \<equiv> partial_composition.arr (functor_category.comp A B)"

    abbreviation MKARR
    where "MKARR \<equiv> concrete_category.MkArr"

    abbreviation MAP
    where "MAP \<equiv> concrete_category.Map"

    abbreviation DOM
    where "DOM \<equiv> concrete_category.Dom"

    abbreviation COD
    where "COD \<equiv> concrete_category.Cod"

    abbreviation NULL
    where "NULL \<equiv> concrete_category.Null"

    abbreviation OBJ
    where "OBJ \<equiv> Collect category"

    abbreviation HOM
    where "HOM \<equiv> functor_category.comp"

    abbreviation COMP
    where "COMP C B A \<mu> \<nu> \<equiv> if ARR B C \<mu> \<and> ARR A B \<nu>
                            then MKARR (DOM \<mu> o DOM \<nu>) (COD \<mu> o COD \<nu>) (MAP \<mu> o MAP \<nu>)
                            else NULL"

    abbreviation ID
    where "ID A \<equiv> MKARR (identity_functor.map A) (identity_functor.map A)
                         (identity_functor.map A)"

    abbreviation ASSOC
    where "ASSOC D C B A \<tau> \<mu> \<nu> \<equiv>
             if ARR C D \<tau> \<and> ARR B C \<mu> \<and> ARR A B \<nu> then
               MKARR (DOM \<tau> o DOM \<mu> o DOM \<nu>) (COD \<tau> o COD \<mu> o COD \<nu>)
                     (MAP \<tau> o MAP \<mu> o MAP \<nu>)
             else NULL"

    text \<open>
      Although we are using the \<open>concrete_bicategory\<close> construction to take care of some
      of the details, the proof is still awkward, because the locale assumptions we need to
      verify are all conditioned on universally quantified entities being in the set \<open>OBJ\<close>,
      and we cannot create interpretations to unpack these conditions until we are within
      a proof context where these entities have been fixed and the conditions have been
      introduced as assumptions.
      So, for example, to prove that \<open>COMP\<close> has the required functoriality property,
      we have to fix \<open>A\<close>, \<open>B\<close>, and \<open>C\<close> and introduce assumptions \<open>A \<in> OBJ\<close>, \<open>B \<in> OBJ\<close>,
      and \<open>C \<in> OBJ\<close>, and only then can we use these assumptions to interpret \<open>A\<close>, \<open>B\<close>,
      and \<open>C\<close> as categories and \<open>HOM A B\<close>, \<open>HOM B C\<close>, and \<open>HOM A C\<close> as functor categories.
      We have to go into a still deeper proof context before we can fix particular arguments
      \<open>\<mu>\<close> and \<open>\<nu>\<close> to \<open>COMP C B A\<close>, introduce the assumptions that they are arrows of
      their respective hom-categories, and finally use those assumptions to interpret them
      as natural transformations.  At that point, we are finally in a position to apply
      the already-proved interchange law for natural transformations, which is the essential
      core of the functoriality property we need to show.
    \<close>

    sublocale concrete_bicategory OBJ HOM ID COMP ID ASSOC
    proof (unfold concrete_bicategory_def, intro conjI allI impI)
      show 1: "\<And>(A :: 'a comp) (B :: 'a comp). \<lbrakk> A \<in> OBJ; B \<in> OBJ \<rbrakk> \<Longrightarrow> category (HOM A B)"
        using functor_category_def functor_category.is_category by auto
      show COMP:
           "\<And>(A :: 'a comp) (B :: 'a comp) (C :: 'a comp).
             \<lbrakk> A \<in> OBJ; B \<in> OBJ; C \<in> OBJ \<rbrakk>
                \<Longrightarrow> binary_functor (HOM B C) (HOM A B) (HOM A C)
                                   (\<lambda>(\<mu>, \<nu>). COMP C B A \<mu> \<nu>)"
      proof -
        fix A :: "'a comp" and B :: "'a comp" and C :: "'a comp"
        assume A: "A \<in> OBJ" and B: "B \<in> OBJ" and C: "C \<in> OBJ"
        let ?COMP = "\<lambda>(\<mu>, \<nu>). COMP C B A \<mu> \<nu>"
        interpret A: category A using A by simp
        interpret B: category B using B by simp
        interpret C: category C using C by simp
        interpret BC: functor_category B C ..
        interpret AB: functor_category A B ..
        interpret AC: functor_category A C ..
        interpret BC_AB: product_category BC.comp AB.comp ..
        show "binary_functor (HOM B C) (HOM A B) (HOM A C) (\<lambda>(\<mu>, \<nu>). COMP C B A \<mu> \<nu>)"
        proof
          show "\<And>\<mu>\<nu>. \<not> BC_AB.arr \<mu>\<nu> \<Longrightarrow> ?COMP \<mu>\<nu> = AC.null"
            using BC_AB.arr_char AC.null_char AC.arr_MkArr by auto
          fix \<mu>\<nu>
          assume \<mu>\<nu>: "BC_AB.arr \<mu>\<nu>"
          interpret \<mu>: natural_transformation B C
                         \<open>AC.Dom (fst \<mu>\<nu>)\<close> \<open>AC.Cod (fst \<mu>\<nu>)\<close> \<open>MAP (fst \<mu>\<nu>)\<close>
            using \<mu>\<nu> BC.arr_char [of "fst \<mu>\<nu>"] by simp
          interpret \<nu>: natural_transformation A B
                         \<open>AC.Dom (snd \<mu>\<nu>)\<close> \<open>AC.Cod (snd \<mu>\<nu>)\<close> \<open>MAP (snd \<mu>\<nu>)\<close>
            using \<mu>\<nu> AB.arr_char [of "snd \<mu>\<nu>"] by simp
          interpret \<mu>\<nu>: natural_transformation A C
                          \<open>AC.Dom (fst \<mu>\<nu>) o AC.Dom (snd \<mu>\<nu>)\<close>
                          \<open>AC.Cod (fst \<mu>\<nu>) o AC.Cod (snd \<mu>\<nu>)\<close>
                          \<open>MAP (fst \<mu>\<nu>) o MAP (snd \<mu>\<nu>)\<close>
            using \<mu>.natural_transformation_axioms \<nu>.natural_transformation_axioms
                  horizontal_composite
            by blast
          show "AC.arr (?COMP \<mu>\<nu>)"
            using \<mu>\<nu> BC_AB.arr_char \<mu>\<nu>.natural_transformation_axioms
                  \<mu>\<nu>.F.functor_axioms \<mu>\<nu>.G.functor_axioms AC.arr_MkArr
            by (cases \<mu>\<nu>) simp
          show "AC.dom (?COMP \<mu>\<nu>) = ?COMP (BC_AB.dom \<mu>\<nu>)"
            using \<mu>\<nu> BC_AB.arr_char \<mu>\<nu>.natural_transformation_axioms
                  \<mu>\<nu>.F.functor_axioms \<mu>\<nu>.G.functor_axioms AC.arr_MkArr
            by (cases \<mu>\<nu>) simp
          show "AC.cod (?COMP \<mu>\<nu>) = ?COMP (BC_AB.cod \<mu>\<nu>)"
            using \<mu>\<nu> BC_AB.arr_char \<mu>\<nu>.natural_transformation_axioms
                  \<mu>\<nu>.F.functor_axioms \<mu>\<nu>.G.functor_axioms AC.arr_MkArr
            by (cases \<mu>\<nu>) simp
          next
          fix \<mu>\<nu> \<sigma>\<tau>
          assume seq: "BC_AB.seq \<mu>\<nu> \<sigma>\<tau>"
          interpret \<mu>: natural_transformation B C
                         \<open>BC.Dom (fst \<mu>\<nu>)\<close> \<open>BC.Cod (fst \<mu>\<nu>)\<close> \<open>MAP (fst \<mu>\<nu>)\<close>
            using seq BC_AB.seq_char BC_AB.arr_char BC.arr_char [of "fst \<mu>\<nu>"] AB.arr_char
            by auto
          interpret \<nu>: natural_transformation A B
                         \<open>AB.Dom (snd \<mu>\<nu>)\<close> \<open>AB.Cod (snd \<mu>\<nu>)\<close> \<open>MAP (snd \<mu>\<nu>)\<close>
            using seq BC_AB.seq_char BC_AB.arr_char BC.arr_char AB.arr_char [of "snd \<mu>\<nu>"]
            by auto
          interpret \<mu>\<nu>: natural_transformation A C
                          \<open>AC.Dom (fst \<mu>\<nu>) o AC.Dom (snd \<mu>\<nu>)\<close>
                          \<open>AC.Cod (fst \<mu>\<nu>) o AC.Cod (snd \<mu>\<nu>)\<close>
                          \<open>MAP (fst \<mu>\<nu>) o MAP (snd \<mu>\<nu>)\<close>
            using \<mu>.natural_transformation_axioms \<nu>.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret \<sigma>: natural_transformation B C
                         \<open>BC.Dom (fst \<sigma>\<tau>)\<close> \<open>BC.Cod (fst \<sigma>\<tau>)\<close> \<open>MAP (fst \<sigma>\<tau>)\<close>
            using seq BC_AB.seq_char BC_AB.arr_char BC.arr_char [of "fst \<sigma>\<tau>"] AB.arr_char
            by auto
          interpret \<tau>: natural_transformation A B
                         \<open>AB.Dom (snd \<sigma>\<tau>)\<close> \<open>AB.Cod (snd \<sigma>\<tau>)\<close> \<open>MAP (snd \<sigma>\<tau>)\<close>
            using seq BC_AB.seq_char BC_AB.arr_char BC.arr_char AB.arr_char [of "snd \<sigma>\<tau>"]
            by auto
          interpret \<sigma>\<tau>: natural_transformation A C
                          \<open>AC.Dom (fst \<sigma>\<tau>) o AC.Dom (snd \<sigma>\<tau>)\<close>
                          \<open>AC.Cod (fst \<sigma>\<tau>) o AC.Cod (snd \<sigma>\<tau>)\<close>
                          \<open>MAP (fst \<sigma>\<tau>) o MAP (snd \<sigma>\<tau>)\<close>
            using \<sigma>.natural_transformation_axioms \<tau>.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret \<mu>o\<sigma>: vertical_composite B C
                           \<open>BC.Dom (fst \<sigma>\<tau>)\<close> \<open>BC.Cod (fst \<sigma>\<tau>)\<close> \<open>BC.Cod (fst \<mu>\<nu>)\<close>
                           \<open>MAP (fst \<sigma>\<tau>)\<close> \<open>MAP (fst \<mu>\<nu>)\<close>
            using seq BC_AB.seq_char BC.seq_char \<mu>.natural_transformation_axioms
            by intro_locales (simp add: natural_transformation_def)
          interpret \<nu>o\<tau>: vertical_composite A B
                           \<open>AB.Dom (snd \<sigma>\<tau>)\<close> \<open>AB.Cod (snd \<sigma>\<tau>)\<close> \<open>AB.Cod (snd \<mu>\<nu>)\<close>
                           \<open>MAP (snd \<sigma>\<tau>)\<close> \<open>MAP (snd \<mu>\<nu>)\<close>
            using seq BC_AB.seq_char AB.seq_char \<nu>.natural_transformation_axioms
            by intro_locales (simp add: natural_transformation_def)

          show "?COMP (BC_AB.comp \<mu>\<nu> \<sigma>\<tau>) = AC.comp (?COMP \<mu>\<nu>) (?COMP \<sigma>\<tau>)"
          proof -
            have "?COMP (BC_AB.comp \<mu>\<nu> \<sigma>\<tau>) =
                  AC.MkArr
                    (BC.Dom (fst (BC_AB.comp \<mu>\<nu> \<sigma>\<tau>)) \<circ> AB.Dom (snd (BC_AB.comp \<mu>\<nu> \<sigma>\<tau>)))
                    (BC.Cod (fst (BC_AB.comp \<mu>\<nu> \<sigma>\<tau>)) \<circ> AB.Cod (snd (BC_AB.comp \<mu>\<nu> \<sigma>\<tau>)))
                    (BC.Map (fst (BC_AB.comp \<mu>\<nu> \<sigma>\<tau>)) \<circ> AB.Map (snd (BC_AB.comp \<mu>\<nu> \<sigma>\<tau>)))"
              using seq BC_AB.arr_char by (cases "BC_AB.comp \<mu>\<nu> \<sigma>\<tau>", simp)
            also have
              "... =
               AC.MkArr
                (BC.Dom (fst \<sigma>\<tau>) \<circ> AB.Dom (snd \<sigma>\<tau>)) (BC.Cod (fst \<mu>\<nu>) \<circ> AB.Cod (snd \<mu>\<nu>))
                (vertical_composite.map B C (BC.Map (fst \<sigma>\<tau>)) (AB.Map (fst \<mu>\<nu>)) \<circ>
                 vertical_composite.map A B (BC.Map (snd \<sigma>\<tau>)) (AB.Map (snd \<mu>\<nu>)))"
              using seq BC_AB.comp_char BC_AB.seq_char BC_AB.arr_char BC.seq_char AB.seq_char
                    BC.Dom_comp BC.Cod_comp BC.Map_comp
                    AB.Dom_comp AB.Cod_comp AB.Map_comp
              by auto  (* 7 sec *)
            also have "... = AC.MkArr
                               (BC.Dom (fst \<sigma>\<tau>) \<circ> AB.Dom (snd \<sigma>\<tau>))
                               (BC.Cod (fst \<mu>\<nu>) \<circ> AB.Cod (snd \<mu>\<nu>))
                               (vertical_composite.map A C
                                  (AC.Map (fst \<sigma>\<tau>) \<circ> AC.Map (snd \<sigma>\<tau>))
                                  (AC.Map (fst \<mu>\<nu>) \<circ> AC.Map (snd \<mu>\<nu>)))"
              using \<sigma>.natural_transformation_axioms \<tau>.natural_transformation_axioms
                    \<mu>.natural_transformation_axioms \<nu>.natural_transformation_axioms
                    \<mu>o\<sigma>.\<tau>.natural_transformation_axioms \<nu>o\<tau>.\<tau>.natural_transformation_axioms
                    interchange
              by blast
            also have "... = AC.comp (AC.MkArr (AC.Dom (fst \<mu>\<nu>) \<circ> AC.Dom (snd \<mu>\<nu>))
                                               (AC.Cod (fst \<mu>\<nu>) \<circ> AC.Cod (snd \<mu>\<nu>))
                                               (AC.Map (fst \<mu>\<nu>) \<circ> AC.Map (snd \<mu>\<nu>)))
                                     (AC.MkArr (AC.Dom (fst \<sigma>\<tau>) \<circ> AC.Dom (snd \<sigma>\<tau>))
                                     (AC.Cod (fst \<sigma>\<tau>) \<circ> AC.Cod (snd \<sigma>\<tau>))
                                     (AC.Map (fst \<sigma>\<tau>) \<circ> AC.Map (snd \<sigma>\<tau>)))"
              using seq BC_AB.seq_char BC.seq_char AB.seq_char AC.comp_MkArr
                    \<sigma>\<tau>.natural_transformation_axioms \<mu>\<nu>.natural_transformation_axioms
              by simp
            also have "... = AC.comp (?COMP \<mu>\<nu>) (?COMP \<sigma>\<tau>)"
              using seq BC_AB.seq_char BC_AB.arr_char BC.seq_char AB.seq_char
                    BC.Dom_comp BC.Cod_comp BC.Map_comp
                    AB.Dom_comp AB.Cod_comp AB.Map_comp
              by (cases \<mu>\<nu>, cases \<sigma>\<tau>) simp
            finally show ?thesis by blast
          qed
        qed
      qed  
      show 2: "\<And>(A :: 'a comp). A \<in> OBJ \<Longrightarrow> partial_composition.ide (HOM A A) (ID A)"
        using concrete_category.ide_MkIde functor_category.is_concrete_category
              functor_category_def identity_functor.intro identity_functor.is_functor
        by fastforce
      show "\<And>(A :: 'a comp). A \<in> OBJ
                \<Longrightarrow> partial_composition.in_hom (HOM A A) (ID A)
                                         (COMP A A A (ID A) (ID A)) (ID A)"
      proof -
        fix A :: "'a comp"
        assume A: "A \<in> OBJ"
        interpret A: category A
          using A by simp
        interpret AA: functor_category A A ..
        show "AA.in_hom (ID A) (COMP A A A (ID A) (ID A)) (ID A)"
          using A.is_functor by force
      qed
      show "\<And>(A :: 'a comp). A \<in> OBJ \<Longrightarrow> category.iso (HOM A A) (ID A)"
        by (simp add: 1 2 category.ide_is_iso)
      show "\<And>(A :: 'a comp) (B :: 'a comp) (C :: 'a comp) (D :: 'a comp).
              \<lbrakk> A \<in> OBJ; B \<in> OBJ; C \<in> OBJ; D \<in> OBJ \<rbrakk>
                 \<Longrightarrow> natural_isomorphism
                       (product_category.comp
                          (HOM C D) (product_category.comp (HOM B C) (HOM A B)))
                       (HOM A D)
                       (\<lambda>(f, g, h). COMP D B A (COMP D C B f g) h)
                       (\<lambda>(f, g, h). COMP D C A f (COMP C B A g h))
                       (\<lambda>(f, g, h). ASSOC D C B A f g h)"
      proof -
        fix A :: "'a comp" and B :: "'a comp" and C :: "'a comp" and D :: "'a comp"
        assume A: "A \<in> OBJ" and B: "B \<in> OBJ" and C: "C \<in> OBJ" and D: "D \<in> OBJ"
        interpret A: category A using A by simp
        interpret B: category B using B by simp
        interpret C: category C using C by simp
        interpret D: category D using D by simp
        interpret AB: functor_category A B ..
        interpret BC: functor_category B C ..
        interpret CD: functor_category C D ..
        interpret AD: functor_category A D ..
        interpret BD: functor_category B D ..
        interpret AC: functor_category A C ..
        interpret BC_AB: product_category BC.comp AB.comp ..
        interpret CD_BC_AB: product_category CD.comp BC_AB.comp ..

        let ?L = "\<lambda>(f, g, h). COMP D B A (COMP D C B f g) h"
        let ?R = "\<lambda>(f, g, h). COMP D C A f (COMP C B A g h)"
        let ?A = "\<lambda>(f, g, h). ASSOC D C B A f g h"

        have *:
          "\<And>fgh fgh'. CD_BC_AB.seq fgh fgh' \<Longrightarrow>
              AD.comp
                (AD.MkArr
                  (CD.Dom (fst fgh) \<circ> BC.Dom (fst (snd fgh)) \<circ> AB.Dom (snd (snd fgh)))
                  (CD.Cod (fst fgh) \<circ> BC.Cod (fst (snd fgh)) \<circ> AB.Cod (snd (snd fgh)))
                  (CD.Map (fst fgh) \<circ> BC.Map (fst (snd fgh)) \<circ> AB.Map (snd (snd fgh))))
                (AD.MkArr
                  (CD.Dom (fst fgh') \<circ> BC.Dom (fst (snd fgh')) \<circ> AB.Dom (snd (snd fgh')))
                  (CD.Cod (fst fgh') \<circ> BC.Cod (fst (snd fgh')) \<circ> AB.Cod (snd (snd fgh')))
                  (CD.Map (fst fgh') \<circ> BC.Map (fst (snd fgh')) \<circ> AB.Map (snd (snd fgh')))) =
              AD.MkArr (AD.Dom (fst fgh') \<circ> AD.Dom (BC.comp (fst (snd fgh)) (fst (snd fgh')))
                          \<circ> AD.Dom (AB.comp (snd (snd fgh)) (snd (snd fgh'))))
                       (AD.Cod (fst fgh) \<circ> AD.Cod (BC.comp (fst (snd fgh)) (fst (snd fgh')))
                          \<circ> AD.Cod (AB.comp (snd (snd fgh)) (snd (snd fgh'))))
                       (vertical_composite.map C D (AD.Map (fst fgh')) (AD.Map (fst fgh))
                          \<circ> AD.Map (BC.comp (fst (snd fgh)) (fst (snd fgh')))
                          \<circ> AD.Map (AB.comp (snd (snd fgh)) (snd (snd fgh'))))"
        proof -
          fix fgh fgh'
          assume seq: "CD_BC_AB.seq fgh fgh'"
          have fgh: "CD_BC_AB.arr fgh"
            using seq by blast
          have fgh': "CD_BC_AB.arr fgh'"
            using seq by blast

          let ?f = "fst (fgh)" and ?g = "fst (snd (fgh))" and ?h = "snd (snd fgh)"
          let ?f' = "fst (fgh')" and ?g' = "fst (snd (fgh'))" and ?h' = "snd (snd fgh')"
          let ?LHS = "AD.comp
                        (AD.MkArr (CD.Dom ?f \<circ> BC.Dom ?g \<circ> AB.Dom ?h)
                                  (CD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                                  (CD.Map ?f \<circ> BC.Map ?g \<circ> AB.Map ?h))
                        (AD.MkArr (CD.Dom ?f' \<circ> BC.Dom ?g' \<circ> AB.Dom ?h')
                                  (CD.Cod ?f' \<circ> BC.Cod ?g' \<circ> AB.Cod ?h')
                                  (CD.Map ?f' \<circ> BC.Map ?g' \<circ> AB.Map ?h'))"
          let ?RHS = "AD.MkArr
                        (AD.Dom ?f' \<circ> AD.Dom (BC.comp ?g ?g') \<circ> AD.Dom (AB.comp ?h ?h'))
                        (AD.Cod ?f \<circ> AD.Cod (BC.comp ?g ?g') \<circ> AD.Cod (AB.comp ?h ?h'))
                        (vertical_composite.map C D (AD.Map ?f') (AD.Map ?f)
                           \<circ> AD.Map (BC.comp ?g ?g') \<circ> AD.Map (AB.comp ?h ?h'))"

          interpret f: natural_transformation C D \<open>CD.Dom ?f\<close> \<open>CD.Cod ?f\<close> \<open>MAP ?f\<close>
            using fgh CD_BC_AB.arr_char CD.arr_char by simp
          interpret g: natural_transformation B C \<open>BC.Dom ?g\<close> \<open>BC.Cod ?g\<close> \<open>MAP ?g\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char BC.arr_char by simp
          interpret h: natural_transformation A B \<open>AB.Dom ?h\<close> \<open>AB.Cod ?h\<close> \<open>MAP ?h\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char by simp
          interpret fg: natural_transformation B D
                           \<open>CD.Dom ?f o BC.Dom ?g\<close> \<open>CD.Cod ?f o BC.Cod ?g\<close> \<open>MAP ?f o MAP ?g\<close>
            using f.natural_transformation_axioms g.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret fgh: natural_transformation A D
                           \<open>CD.Dom ?f o BC.Dom ?g o AB.Dom ?h\<close>
                           \<open>CD.Cod ?f o BC.Cod ?g o AB.Cod ?h\<close>
                           \<open>MAP ?f o MAP ?g o MAP ?h\<close>
            using f.natural_transformation_axioms g.natural_transformation_axioms
                  h.natural_transformation_axioms horizontal_composite
            by blast
          interpret f': natural_transformation C D \<open>CD.Dom ?f'\<close> \<open>CD.Cod ?f'\<close> \<open>MAP ?f'\<close>
            using fgh' CD_BC_AB.arr_char CD.arr_char by simp
          interpret g': natural_transformation B C \<open>BC.Dom ?g'\<close> \<open>BC.Cod ?g'\<close> \<open>MAP ?g'\<close>
            using fgh' CD_BC_AB.arr_char BC_AB.arr_char BC.arr_char by simp
          interpret h': natural_transformation A B \<open>AB.Dom ?h'\<close> \<open>AB.Cod ?h'\<close> \<open>MAP ?h'\<close>
            using fgh' CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char by simp
          interpret fg': natural_transformation B D
                           \<open>CD.Dom ?f' o BC.Dom ?g'\<close> \<open>CD.Cod ?f' o BC.Cod ?g'\<close>
                           \<open>MAP ?f' o MAP ?g'\<close>
            using f'.natural_transformation_axioms g'.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret fgh': natural_transformation A D
                           \<open>CD.Dom ?f' o BC.Dom ?g' o AB.Dom ?h'\<close>
                           \<open>CD.Cod ?f' o BC.Cod ?g' o AB.Cod ?h'\<close>
                           \<open>MAP ?f' o MAP ?g' o MAP ?h'\<close>
            using f'.natural_transformation_axioms g'.natural_transformation_axioms
                  h'.natural_transformation_axioms horizontal_composite
            by blast
          interpret ff': vertical_composite C D \<open>CD.Dom ?f'\<close> \<open>CD.Cod ?f'\<close> \<open>CD.Cod ?f\<close>
                            \<open>MAP ?f'\<close> \<open>MAP ?f\<close>
            using seq CD_BC_AB.seq_char [of fgh fgh'] CD.seq_char [of ?f ?f']
                  f.natural_transformation_axioms f'.natural_transformation_axioms
                  C.category_axioms D.category_axioms
                  f'.F.functor_axioms f'.G.functor_axioms f.G.functor_axioms
            by (metis vertical_composite.intro)
          interpret gg': vertical_composite B C \<open>BC.Dom ?g'\<close> \<open>BC.Cod ?g'\<close> \<open>BC.Cod ?g\<close>
                           \<open>MAP ?g'\<close> \<open>MAP ?g\<close>
            using seq CD_BC_AB.seq_char [of fgh fgh'] BC_AB.seq_char BC.seq_char [of ?g ?g']
                  g.natural_transformation_axioms g'.natural_transformation_axioms
                  B.category_axioms C.category_axioms
                  g'.F.functor_axioms g'.G.functor_axioms g.G.functor_axioms
            by (metis vertical_composite.intro)
          interpret hh': vertical_composite A B \<open>AB.Dom ?h'\<close> \<open>AB.Cod ?h'\<close> \<open>AB.Cod ?h\<close>
                           \<open>MAP ?h'\<close> \<open>MAP ?h\<close>
            using seq CD_BC_AB.seq_char [of fgh fgh'] BC_AB.seq_char AB.seq_char [of ?h ?h']
                  h.natural_transformation_axioms h'.natural_transformation_axioms
                  A.category_axioms B.category_axioms
                  h'.F.functor_axioms h'.G.functor_axioms h.G.functor_axioms
            by (metis vertical_composite.intro)

          have "?LHS = AD.MkArr
                         (CD.Dom ?f' \<circ> BC.Dom ?g' \<circ> AB.Dom ?h')
                         (CD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                         (vertical_composite.map A D
                            (CD.Map ?f' \<circ> BC.Map ?g' \<circ> AB.Map ?h')
                            (CD.Map ?f \<circ> BC.Map ?g \<circ> AB.Map ?h))"
            using AD.comp_MkArr [of "CD.Dom ?f' \<circ> BC.Dom ?g' \<circ> AB.Dom ?h'"
                                    "CD.Cod ?f' \<circ> BC.Cod ?g' \<circ> AB.Cod ?h'"
                                    "CD.Map ?f' \<circ> BC.Map ?g' \<circ> AB.Map ?h'"
                                    "CD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h"
                                    "CD.Map ?f \<circ> BC.Map ?g \<circ> AB.Map ?h"]
            using seq CD_BC_AB.seq_char CD.seq_char BC_AB.seq_char AB.arr_char
                  BD.seq_char AB.seq_char BC.seq_char fg.natural_transformation_axioms
                  fg'.natural_transformation_axioms fgh'.natural_transformation_axioms
                  fgh.natural_transformation_axioms
            by auto
          also have "... = AD.MkArr
                             (CD.Dom ?f' \<circ> BC.Dom ?g' \<circ> AB.Dom ?h')
                             (CD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                             (vertical_composite.map C D (CD.Map ?f') (CD.Map ?f)
                                \<circ> vertical_composite.map B C (BC.Map ?g') (BC.Map ?g)
                                o vertical_composite.map A B (AB.Map ?h') (AB.Map ?h))"
          proof -
            have "vertical_composite.map A D
                    (CD.Map ?f' \<circ> BC.Map ?g' \<circ> AB.Map ?h')
                    (CD.Map ?f \<circ> BC.Map ?g \<circ> AB.Map ?h) =
                  vertical_composite.map C D (CD.Map ?f') (CD.Map ?f)
                    \<circ> vertical_composite.map B C (BC.Map ?g') (BC.Map ?g)
                    o vertical_composite.map A B (AB.Map ?h') (AB.Map ?h)"
              using interchange
                      [of B C "BC.Dom ?g'" "BC.Cod ?g'" "BC.Map ?g'"
                          "BC.Cod ?g" "BC.Map ?g" D
                          "CD.Dom ?f'" "CD.Cod ?f'" "CD.Map ?f'"
                          "CD.Cod ?f"  "CD.Map ?f"]
                    interchange
                    f'.natural_transformation_axioms ff'.\<tau>.natural_transformation_axioms
                    g'.natural_transformation_axioms gg'.\<tau>.natural_transformation_axioms
                    fg'.natural_transformation_axioms
                    gg'.\<tau>.natural_transformation_axioms h'.natural_transformation_axioms
                    hh'.\<tau>.natural_transformation_axioms horizontal_composite
              by (metis (no_types, lifting))  (* 20 sec *)
            thus ?thesis by simp
          qed
          also have "... = ?RHS"
            by (metis (no_types, lifting) AB.Cod_comp AB.Dom_comp AB.Map_comp'
                AB.seq_char BC.Cod_comp BC.Dom_comp BC.Map_comp' BC.seq_char
                BC_AB.seq_char CD_BC_AB.seqE\<^sub>P\<^sub>C seq)
          finally show "?LHS = ?RHS" by fastforce
        qed

        interpret L: "functor" CD_BC_AB.comp AD.comp ?L
        proof
          interpret CD_BC: product_category CD.comp BC.comp ..
          interpret BD: functor_category B D ..
          fix fgh
          show "\<not> CD_BC_AB.arr fgh \<Longrightarrow> ?L fgh = AD.null"
            using AD.null_char BD.null_char by (cases fgh, auto)
          assume fgh: "CD_BC_AB.arr fgh"
          let ?f = "fst (fgh)" and ?g = "fst (snd (fgh))" and ?h = "snd (snd fgh)"
          interpret f: natural_transformation C D \<open>CD.Dom ?f\<close> \<open>CD.Cod ?f\<close> \<open>MAP ?f\<close>
            using fgh CD_BC_AB.arr_char CD.arr_char by simp
          interpret g: natural_transformation B C \<open>BC.Dom ?g\<close> \<open>BC.Cod ?g\<close> \<open>MAP ?g\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char BC.arr_char by simp
          interpret h: natural_transformation A B \<open>AB.Dom ?h\<close> \<open>AB.Cod ?h\<close> \<open>MAP ?h\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char by simp
          interpret fg: natural_transformation B D
                           \<open>CD.Dom ?f o BC.Dom ?g\<close> \<open>CD.Cod ?f o BC.Cod ?g\<close> \<open>MAP ?f o MAP ?g\<close>
            using f.natural_transformation_axioms g.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret fgh: natural_transformation A D
                           \<open>CD.Dom ?f o BC.Dom ?g o AB.Dom ?h\<close>
                           \<open>CD.Cod ?f o BC.Cod ?g o AB.Cod ?h\<close>
                           \<open>MAP ?f o MAP ?g o MAP ?h\<close>
            using f.natural_transformation_axioms g.natural_transformation_axioms
                  h.natural_transformation_axioms horizontal_composite
            by blast
          show 1: "AD.arr (?L fgh)"
            using fgh CD_BC_AB.arr_char CD.arr_char BC_AB.arr_char BC.arr_char AB.arr_char
                  fg.natural_transformation_axioms fgh.natural_transformation_axioms
                  fgh.F.functor_axioms fgh.G.functor_axioms AD.arr_char
            by (cases fgh, auto)
          show "AD.dom (?L fgh) = ?L (CD_BC_AB.dom fgh)"
            using fgh 1 fg.natural_transformation_axioms fg.F.functor_axioms
            by (cases fgh, auto)
          show "AD.cod (?L fgh) = ?L (CD_BC_AB.cod fgh)"
            using fgh 1 fg.natural_transformation_axioms fg.G.functor_axioms
            by (cases fgh, auto)
          next
          (*
           * TODO: It might be worth it to change the axioms for functor so that the assumption
           * for this case is "arr fgh \<and> arr fgh' \<and> dom fgh = cod fgh'".  That would allow
           * proofs to overlap this last case with the rest when convenient, like here.
           *)
          fix fgh fgh'
          assume seq: "CD_BC_AB.seq fgh fgh'"
          have fgh: "CD_BC_AB.arr fgh"
            using seq by blast
          have fgh': "CD_BC_AB.arr fgh'"
            using seq by blast
          let ?f = "fst (fgh)" and ?g = "fst (snd (fgh))" and ?h = "snd (snd fgh)"
          interpret f: natural_transformation C D \<open>CD.Dom ?f\<close> \<open>CD.Cod ?f\<close> \<open>MAP ?f\<close>
            using fgh CD_BC_AB.arr_char CD.arr_char by simp
          interpret g: natural_transformation B C \<open>BC.Dom ?g\<close> \<open>BC.Cod ?g\<close> \<open>MAP ?g\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char BC.arr_char by simp
          interpret h: natural_transformation A B \<open>AB.Dom ?h\<close> \<open>AB.Cod ?h\<close> \<open>MAP ?h\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char by simp
          interpret fg: natural_transformation B D
                           \<open>CD.Dom ?f o BC.Dom ?g\<close> \<open>CD.Cod ?f o BC.Cod ?g\<close> \<open>MAP ?f o MAP ?g\<close>
            using f.natural_transformation_axioms g.natural_transformation_axioms
                  horizontal_composite
            by blast
          let ?f' = "fst (fgh')" and ?g' = "fst (snd (fgh'))" and ?h' = "snd (snd fgh')"
          interpret f': natural_transformation C D \<open>CD.Dom ?f'\<close> \<open>CD.Cod ?f'\<close> \<open>MAP ?f'\<close>
            using fgh' CD_BC_AB.arr_char CD.arr_char by simp
          interpret g': natural_transformation B C \<open>BC.Dom ?g'\<close> \<open>BC.Cod ?g'\<close> \<open>MAP ?g'\<close>
            using fgh' CD_BC_AB.arr_char BC_AB.arr_char BC.arr_char by simp
          interpret h': natural_transformation A B \<open>AB.Dom ?h'\<close> \<open>AB.Cod ?h'\<close> \<open>MAP ?h'\<close>
            using fgh' CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char by simp
          interpret fg': natural_transformation B D
                           \<open>CD.Dom ?f' o BC.Dom ?g'\<close> \<open>CD.Cod ?f' o BC.Cod ?g'\<close>
                           \<open>MAP ?f' o MAP ?g'\<close>
            using f'.natural_transformation_axioms g'.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret ff': vertical_composite C D \<open>CD.Dom ?f'\<close> \<open>CD.Cod ?f'\<close> \<open>CD.Cod ?f\<close>
                            \<open>MAP ?f'\<close> \<open>MAP ?f\<close>
            using seq CD_BC_AB.seq_char [of fgh fgh'] CD.seq_char [of ?f ?f']
                  f.natural_transformation_axioms f'.natural_transformation_axioms
                  C.category_axioms D.category_axioms
                  f'.F.functor_axioms f'.G.functor_axioms f.G.functor_axioms
            by (unfold vertical_composite_def) presburger
          interpret gg': vertical_composite B C \<open>CD.Dom ?g'\<close> \<open>CD.Cod ?g'\<close> \<open>CD.Cod ?g\<close>
                            \<open>MAP ?g'\<close> \<open>MAP ?g\<close>
            using seq CD_BC_AB.seq_char [of fgh fgh'] CD.seq_char [of ?g ?g']
                  g.natural_transformation_axioms g'.natural_transformation_axioms
                  C.category_axioms D.category_axioms
            by (unfold vertical_composite_def)
               (metis BC.seq_char BC_AB.seqE\<^sub>P\<^sub>C natural_transformation_def)
          interpret gg'off': natural_transformation B D
                               \<open>AC.Dom (fst fgh') \<circ> AC.Dom (fst (snd fgh'))\<close>
                               \<open>AC.Cod (fst fgh) \<circ> AC.Cod (fst (snd fgh))\<close> \<open>ff'.map \<circ> gg'.map\<close>
            by (meson ff'.natural_transformation_axioms gg'.natural_transformation_axioms
                horizontal_composite)
           
          show "?L (CD_BC_AB.comp fgh fgh') = AD.comp (?L fgh) (?L fgh')"
          proof -
            have "AD.comp (?L fgh) (?L fgh') =
                  AD.comp
                    (AD.MkArr (CD.Dom ?f \<circ> BC.Dom ?g \<circ> AB.Dom ?h)
                              (CD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                              (CD.Map ?f \<circ> BC.Map ?g \<circ> AB.Map ?h))
                    (AD.MkArr (CD.Dom ?f' \<circ> BC.Dom ?g' \<circ> AB.Dom ?h')
                              (CD.Cod ?f' \<circ> BC.Cod ?g' \<circ> AB.Cod ?h')
                              (CD.Map ?f' \<circ> BC.Map ?g' \<circ> AB.Map ?h'))"
              using seq CD_BC_AB.seq_char CD.seq_char BC_AB.seq_char AB.arr_char
                    BD.seq_char AB.seq_char BC.seq_char fg.natural_transformation_axioms
                    fg'.natural_transformation_axioms
              by (cases fgh, cases fgh') auto  (* 20 sec *)
            also have "... =
                       AD.MkArr
                         (AD.Dom ?f' \<circ> AD.Dom (BC.comp ?g ?g') \<circ> AD.Dom (AB.comp ?h ?h'))
                         (AD.Cod ?f \<circ> AD.Cod (BC.comp ?g ?g') \<circ> AD.Cod (AB.comp ?h ?h'))
                         (vertical_composite.map C D (AD.Map ?f') (AD.Map ?f)
                            \<circ> AD.Map (BC.comp ?g ?g')
                            \<circ> AD.Map (AB.comp ?h ?h'))"
              using seq * [of fgh fgh'] by blast
            also have "... = ?L (CD_BC_AB.comp fgh fgh')"
              using fgh fgh' CD_BC_AB.comp_char CD.seq_char BC_AB.comp_char
                    BC.seq_char AB.seq_char gg'off'.natural_transformation_axioms
              apply simp
              by (metis (no_types, lifting) BC_AB.seqE\<^sub>P\<^sub>C CD_BC_AB.seqE\<^sub>P\<^sub>C seq)
            finally show ?thesis by argo
          qed
        qed

        interpret R: "functor" CD_BC_AB.comp AD.comp ?R
        proof
          interpret CD_BC: product_category CD.comp BC.comp ..
          interpret AC: functor_category A C ..
          fix fgh
          show "\<not> CD_BC_AB.arr fgh \<Longrightarrow> ?R fgh = AD.null"
            using AD.null_char AC.null_char by (cases fgh, auto)
          assume fgh: "CD_BC_AB.arr fgh"
          let ?f = "fst (fgh)" and ?g = "fst (snd (fgh))" and ?h = "snd (snd fgh)"
          interpret f: natural_transformation C D \<open>CD.Dom ?f\<close> \<open>CD.Cod ?f\<close> \<open>MAP ?f\<close>
            using fgh CD_BC_AB.arr_char CD.arr_char by simp
          interpret g: natural_transformation B C \<open>BC.Dom ?g\<close> \<open>BC.Cod ?g\<close> \<open>MAP ?g\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char BC.arr_char by simp
          interpret h: natural_transformation A B \<open>AB.Dom ?h\<close> \<open>AB.Cod ?h\<close> \<open>MAP ?h\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char by simp
          interpret fg: natural_transformation B D
                           \<open>CD.Dom ?f o BC.Dom ?g\<close> \<open>CD.Cod ?f o BC.Cod ?g\<close> \<open>MAP ?f o MAP ?g\<close>
            using f.natural_transformation_axioms g.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret gh: natural_transformation A C
                           \<open>BC.Dom ?g o AB.Dom ?h\<close> \<open>BC.Cod ?g o AB.Cod ?h\<close>
                           \<open>MAP ?g o MAP ?h\<close>
            using g.natural_transformation_axioms h.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret fgh: natural_transformation A D
                           \<open>CD.Dom ?f o (BC.Dom ?g o AB.Dom ?h)\<close>
                           \<open>CD.Cod ?f o (BC.Cod ?g o AB.Cod ?h)\<close>
                           \<open>MAP ?f o (MAP ?g o MAP ?h)\<close>
            using f.natural_transformation_axioms g.natural_transformation_axioms
                  h.natural_transformation_axioms horizontal_composite
            by blast
          show 1: "AD.arr (?R fgh)"
            using fgh CD_BC_AB.arr_char AB.arr_char CD_BC.arr_char CD.arr_char BC.arr_char
                  gh.natural_transformation_axioms fgh.natural_transformation_axioms
                  fgh.F.functor_axioms fgh.G.functor_axioms AD.arr_char AC.arr_char
            by (cases fgh) (simp add: natural_transformation_def)
          show "AD.dom (?R fgh) = ?R (CD_BC_AB.dom fgh)"
            using fgh 1 gh.natural_transformation_axioms gh.F.functor_axioms
            by (cases fgh) auto
          show "AD.cod (?R fgh) = ?R (CD_BC_AB.cod fgh)"
            using fgh 1 gh.natural_transformation_axioms gh.G.functor_axioms
            by (cases fgh) auto
          next
          fix fgh fgh'
          assume seq: "CD_BC_AB.seq fgh fgh'"
          have fgh: "CD_BC_AB.arr fgh"
            using seq by blast
          have fgh': "CD_BC_AB.arr fgh'"
            using seq by blast
          let ?f = "fst (fgh)" and ?g = "fst (snd (fgh))" and ?h = "snd (snd fgh)"
          have f: "CD.arr ?f" and g: "BC.arr ?g" and h: "AB.arr ?h"
            using fgh by simp_all
          interpret f: natural_transformation C D \<open>CD.Dom ?f\<close> \<open>CD.Cod ?f\<close> \<open>MAP ?f\<close>
            using fgh CD_BC_AB.arr_char CD.arr_char by simp
          interpret g: natural_transformation B C \<open>BC.Dom ?g\<close> \<open>BC.Cod ?g\<close> \<open>MAP ?g\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char BC.arr_char by simp
          interpret h: natural_transformation A B \<open>AB.Dom ?h\<close> \<open>AB.Cod ?h\<close> \<open>MAP ?h\<close>
            using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char by simp
          interpret gh: natural_transformation A C
                           \<open>BC.Dom ?g o AB.Dom ?h\<close> \<open>BC.Cod ?g o AB.Cod ?h\<close>
                           \<open>MAP ?g o MAP ?h\<close>
            using g.natural_transformation_axioms h.natural_transformation_axioms
                  horizontal_composite
            by blast
          let ?f' = "fst (fgh')" and ?g' = "fst (snd (fgh'))" and ?h' = "snd (snd fgh')"
          have f': "CD.arr ?f'" and g': "BC.arr ?g'" and h': "AB.arr ?h'"
            using fgh' by simp_all
          interpret f': natural_transformation C D \<open>CD.Dom ?f'\<close> \<open>CD.Cod ?f'\<close> \<open>MAP ?f'\<close>
            using seq CD_BC_AB.arr_char CD.arr_char by blast
          interpret g': natural_transformation B C \<open>BC.Dom ?g'\<close> \<open>BC.Cod ?g'\<close> \<open>MAP ?g'\<close>
            using seq CD_BC_AB.arr_char BC_AB.arr_char BC.arr_char by blast
          interpret h': natural_transformation A B \<open>AB.Dom ?h'\<close> \<open>AB.Cod ?h'\<close> \<open>MAP ?h'\<close>
            using seq CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char by blast
          interpret gh': natural_transformation A C
                           \<open>BC.Dom ?g' o AB.Dom ?h'\<close> \<open>BC.Cod ?g' o AB.Cod ?h'\<close>
                           \<open>MAP ?g' o MAP ?h'\<close>
            using g'.natural_transformation_axioms h'.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret fg': natural_transformation B D
                           \<open>CD.Dom ?f' o BC.Dom ?g'\<close> \<open>CD.Cod ?f' o BC.Cod ?g'\<close>
                           \<open>MAP ?f' o MAP ?g'\<close>
            using f'.natural_transformation_axioms g'.natural_transformation_axioms
                  horizontal_composite
            by blast
          interpret ff': vertical_composite C D \<open>CD.Dom ?f'\<close> \<open>CD.Cod ?f'\<close> \<open>CD.Cod ?f\<close>
                            \<open>MAP ?f'\<close> \<open>MAP ?f\<close>
            using seq CD_BC_AB.seq_char [of fgh fgh'] CD.seq_char [of ?f ?f']
                  f.natural_transformation_axioms f'.natural_transformation_axioms
                  C.category_axioms D.category_axioms
                  f'.F.functor_axioms f'.G.functor_axioms f.G.functor_axioms
            by (metis vertical_composite.intro)
          interpret gg': vertical_composite B C \<open>BC.Dom ?g'\<close> \<open>BC.Cod ?g'\<close> \<open>BC.Cod ?g\<close>
                           \<open>MAP ?g'\<close> \<open>MAP ?g\<close>
            using seq CD_BC_AB.seq_char [of fgh fgh'] BC_AB.seq_char BC.seq_char [of ?g ?g']
                  g.natural_transformation_axioms g'.natural_transformation_axioms
                  B.category_axioms C.category_axioms
                  g'.F.functor_axioms g'.G.functor_axioms g.G.functor_axioms
            by (metis vertical_composite.intro)
          interpret hh': vertical_composite A B \<open>AB.Dom ?h'\<close> \<open>AB.Cod ?h'\<close> \<open>AB.Cod ?h\<close>
                           \<open>MAP ?h'\<close> \<open>MAP ?h\<close>
            using seq CD_BC_AB.seq_char [of fgh fgh'] BC_AB.seq_char AB.seq_char [of ?h ?h']
                  h.natural_transformation_axioms h'.natural_transformation_axioms
                  A.category_axioms B.category_axioms
                  h'.F.functor_axioms h'.G.functor_axioms h.G.functor_axioms
            by (metis vertical_composite.intro)

          show "?R (CD_BC_AB.comp fgh fgh') = AD.comp (?R fgh) (?R fgh')"
          proof -
            have "AD.comp (?R fgh) (?R fgh') =
                  AD.comp
                    (AD.MkArr (CD.Dom ?f \<circ> BC.Dom ?g \<circ> AB.Dom ?h)
                              (CD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                              (CD.Map ?f \<circ> BC.Map ?g \<circ> AB.Map ?h))
                    (AD.MkArr (CD.Dom ?f' \<circ> BC.Dom ?g' \<circ> AB.Dom ?h')
                              (CD.Cod ?f' \<circ> BC.Cod ?g' \<circ> AB.Cod ?h')
                              (CD.Map ?f' \<circ> BC.Map ?g' \<circ> AB.Map ?h'))"
              using fgh fgh' gh.natural_transformation_axioms gh'.natural_transformation_axioms
              apply (cases fgh, cases fgh')
              by (simp add: o_assoc)
            also have "... =
                       AD.MkArr
                         (AD.Dom ?f' \<circ> AD.Dom (BC.comp ?g ?g') \<circ> AD.Dom (AB.comp ?h ?h'))
                         (AD.Cod ?f \<circ> AD.Cod (BC.comp ?g ?g') \<circ> AD.Cod (AB.comp ?h ?h'))
                         (vertical_composite.map C D (AD.Map ?f') (AD.Map ?f)
                            \<circ> AD.Map (BC.comp ?g ?g')
                            \<circ> AD.Map (AB.comp ?h ?h'))"
              using seq * [of fgh fgh'] by blast
            also have "... = AD.MkArr
                               (AD.Dom ?f' \<circ> BC.Dom ?g' \<circ> AB.Dom ?h')
                               (AD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                               (vertical_composite.map C D (AD.Map ?f') (AD.Map ?f)
                                  \<circ> AD.Map (BC.comp ?g ?g')
                                  \<circ> AD.Map (AB.comp ?h ?h'))"
              using seq CD_BC_AB.seq_char BC_AB.seq_char BC.Dom_comp AB.Dom_comp
                    BC.Cod_comp AB.Cod_comp BC.seq_char AB.seq_char
              by (simp add: o_assoc)
            also have "... = AD.MkArr
                               (AD.Dom ?f' \<circ> BC.Dom ?g' \<circ> AB.Dom ?h')
                               (AD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                               (vertical_composite.map C D (AD.Map ?f') (AD.Map ?f) o
                                vertical_composite.map B C (BC.Map ?g') (BC.Map ?g) o
                                vertical_composite.map A B (AB.Map ?h') (AB.Map ?h))"
              using seq CD_BC_AB.seq_char BC_AB.seq_char BC.Map_comp AB.Map_comp
                    BC.seq_char AB.seq_char
              by (cases fgh) simp
            also have "... = AD.MkArr
                               (AD.Dom ?f' \<circ> BC.Dom ?g' \<circ> AB.Dom ?h')
                               (AD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                               (CD.Map (CD.comp ?f ?f') o BC.Map (BC.comp ?g ?g')
                                  o AB.Map (AB.comp ?h ?h'))"
              using seq CD_BC_AB.seq_char BC_AB.seq_char CD.Map_comp BC.Map_comp
                    AB.Map_comp CD.seq_char BC.seq_char AB.seq_char
              by simp
            also have
                "... =
                 AD.MkArr
                   (CD.Dom (CD.comp ?f ?f') \<circ> (BC.Dom (BC.comp ?g ?g') \<circ> AB.Dom (AB.comp ?h ?h')))
                   (CD.Cod (CD.comp ?f ?f') \<circ> (BC.Cod (BC.comp ?g ?g') \<circ> AB.Cod (AB.comp ?h ?h')))
                   (CD.Map (CD.comp ?f ?f') \<circ> (BC.Map (BC.comp ?g ?g') \<circ> AB.Map (AB.comp ?h ?h')))"
              using seq CD_BC_AB.seq_char BC_AB.seq_char BC.Dom_comp AB.Dom_comp
                    BC.Cod_comp AB.Cod_comp CD.seq_char BC.seq_char AB.seq_char
              by (cases fgh) (simp add: o_assoc)
            also have "... = ?R (CD.comp ?f ?f', BC.comp ?g ?g', AB.comp ?h ?h')"
            proof -
              have "CD.seq ?f ?f' \<and> BC.seq ?g ?g' \<and> AB.seq ?h ?h'"
                using seq CD_BC_AB.seq_char BC_AB.seq_char CD.seq_char BC.seq_char AB.seq_char
                by simp
              moreover have "natural_transformation A C
                               (AC.Dom (BC.comp ?g ?g') \<circ> AC.Dom (AB.comp ?h ?h'))
                               (AC.Cod (BC.comp ?g ?g') \<circ> AC.Cod (AB.comp ?h ?h'))
                               (AC.Map (BC.comp ?g ?g') \<circ> AC.Map (AB.comp ?h ?h'))"
                using horizontal_composite calculation by blast
              ultimately show ?thesis by simp
            qed
            also have "... = ?R (CD_BC_AB.comp fgh fgh')"
              using seq fgh fgh' CD_BC_AB.comp_simp BC_AB.comp_simp CD_BC_AB.seq_char
                    BC_AB.seq_char
              by (cases fgh) simp
            finally show ?thesis by argo
          qed
        qed

        interpret A: natural_transformation CD_BC_AB.comp AD.comp ?L ?R ?A
        proof
          interpret CD_BC: product_category CD.comp BC.comp ..
          fix fgh
          show "\<not> CD_BC_AB.arr fgh \<Longrightarrow> ?A fgh = AD.null"
            using AD.null_char BD.null_char by (cases fgh, auto)
          assume fgh: "CD_BC_AB.arr fgh"
          show "AD.dom (?A fgh) = ?L (CD_BC_AB.dom fgh)"
            using fgh AD.dom_char AB.arr_char BC.arr_char CD.arr_char
                  AB.dom_char BC.dom_char CD.dom_char
            apply (cases fgh) apply simp
            by (metis (no_types, lifting) functor_is_transformation horizontal_composite)
          show "AD.cod (?A fgh) = ?R (CD_BC_AB.cod fgh)"
            using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char BC.arr_char CD.arr_char
                  AD.cod_char AB.arr_char BC.arr_char CD.arr_char
                  AB.cod_char BC.cod_char CD.cod_char
            apply (cases fgh)
            apply (simp add: o_assoc)
            by (metis (no_types, lifting) functor_is_transformation horizontal_composite)
          show "AD.comp (?A (CD_BC_AB.cod fgh)) (?L fgh) = ?A fgh"
          proof -
            let ?f = "fst fgh" and ?g = "fst (snd fgh)" and ?h = "snd (snd fgh)"
            have 1: "natural_transformation B D
                       (CD.Dom ?f \<circ> BC.Dom ?g) (CD.Cod ?f \<circ> BC.Cod ?g)
                       (CD.Map ?f \<circ> BC.Map ?g)"
              using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char BC.arr_char CD.arr_char
              apply (cases fgh)
              apply (simp add: o_assoc)
              by (metis (no_types, lifting) horizontal_composite)
            have 2: "natural_transformation A D (AC.Dom ?f \<circ> AC.Dom ?g \<circ> AC.Dom ?h)
                       (AC.Cod ?f \<circ> AC.Cod ?g \<circ> AC.Cod ?h)
                       (AC.Map ?f \<circ> AC.Map ?g \<circ> AC.Map ?h)"
              using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char BC.arr_char
                    CD.arr_char
              apply (cases fgh)
              apply (simp add: o_assoc)
              by (metis (no_types, lifting) horizontal_composite)
            have "AD.comp (?A (CD_BC_AB.cod fgh)) (?L fgh) =
                  AD.comp (AD.MkIde (CD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h))
                          (AD.MkArr (CD.Dom ?f \<circ> BC.Dom ?g \<circ> AB.Dom ?h)
                                    (CD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                                    (CD.Map ?f \<circ> BC.Map ?g \<circ> AB.Map ?h))"
              using 1 2 fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char BC.arr_char CD.arr_char
              apply (cases fgh)
              apply (simp add: o_assoc)
              by (metis AB.cod_char BC.MkIde_Cod CD.arr.simps(2) CD.arr_cod_iff_arr)
            also have "... = ?A fgh"
              using 2 fgh
              by (cases fgh) (simp add: o_assoc AD.comp_cod_arr)
            finally show ?thesis by simp
          qed
          show "AD.comp (?R fgh) (?A (CD_BC_AB.dom fgh)) = ?A fgh"
          proof -
            let ?f = "fst fgh" and ?g = "fst (snd fgh)" and ?h = "snd (snd fgh)"
            have 1: "natural_transformation A C
                       (AC.Dom ?g \<circ> AC.Dom ?h) (AC.Cod ?g \<circ> AC.Cod ?h)
                       (AC.Map ?g \<circ> AC.Map ?h)"
              using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char BC.arr_char CD.arr_char
              apply (cases fgh)
              apply (simp add: o_assoc)
              by (metis (no_types, lifting) horizontal_composite)
            have 2: "natural_transformation A D (AC.Dom ?f \<circ> AC.Dom ?g \<circ> AC.Dom ?h)
                       (AC.Cod ?f \<circ> AC.Cod ?g \<circ> AC.Cod ?h)
                       (AC.Map ?f \<circ> AC.Map ?g \<circ> AC.Map ?h)"
              using fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char BC.arr_char CD.arr_char
              apply (cases fgh)
              apply (simp add: o_assoc)
              by (metis (no_types, lifting) horizontal_composite)
            have "AD.comp (?R fgh) (?A (CD_BC_AB.dom fgh)) =
                  AD.comp (AD.MkArr (CD.Dom ?f \<circ> BC.Dom ?g \<circ> AB.Dom ?h)
                                    (CD.Cod ?f \<circ> BC.Cod ?g \<circ> AB.Cod ?h)
                                    (CD.Map ?f \<circ> BC.Map ?g \<circ> AB.Map ?h))
                          (AD.MkIde (CD.Dom ?f \<circ> BC.Dom ?g \<circ> AB.Dom ?h))"
              using 1 2 fgh CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char BC.arr_char
                    CD.arr_char
              apply (cases fgh)
              apply (simp add: o_assoc)
              by (metis AB.dom_char BC.MkIde_Dom CD.arr.simps(2) CD.arr_dom_iff_arr)
            also have "... = ?A fgh"
              using 2 fgh
              by (cases fgh) (simp add: o_assoc AD.comp_arr_dom)
            finally show ?thesis by simp
          qed
        qed
        show "natural_isomorphism CD_BC_AB.comp AD.comp ?L ?R ?A"
        proof
          fix abc
          assume abc: "CD_BC_AB.ide abc"
          show "AD.iso (?A abc)"
          proof -
            interpret A_abc: natural_transformation A D
                               \<open>BD.Dom (?A abc)\<close> \<open>BD.Cod (?A abc)\<close> \<open>BD.Map (?A abc)\<close>
              using abc CD_BC_AB.ideD(1) CD_BC_AB.arr_char BC_AB.arr_char AB.arr_char
                    BC.arr_char CD.arr_char
              apply (cases abc)
              apply (simp add: o_assoc)
              by (metis AB.null_char BC.null_char CD.null_char functor_is_transformation
                  horizontal_composite)
            interpret A_abc: natural_isomorphism A D
                               \<open>BD.Dom (?A abc)\<close> \<open>BD.Cod (?A abc)\<close> \<open>BD.Map (?A abc)\<close>
            proof -
              have "\<And>a'. A.ide a' \<Longrightarrow> D.iso (CD.Map (fst abc)
                                                    (BC.Map (fst (snd abc))
                                                            (AB.Map (snd (snd abc)) a')))"
              proof -
                fix a'
                assume a': "A.ide a'"
                have "BC.ide (fst (snd abc)) \<and> AB.ide (snd (snd abc))"
                  using abc by force
                hence "C.iso (AC.Map (fst (snd abc)) (AC.Map (snd (snd abc)) a'))"
                  using a' by (metis (no_types) A.ide_is_iso AB.ide_char BC.ide_char
                      functor.preserves_iso)
                thus "D.iso (AC.Map (fst abc) (AC.Map (fst (snd abc))
                            (AC.Map (snd (snd abc)) a')))"
                  by (meson CD.ide_char CD_BC_AB.ide_char\<^sub>P\<^sub>C abc functor.preserves_iso)
              qed
              thus "natural_isomorphism A D
                               (BD.Dom (?A abc)) (BD.Cod (?A abc)) (BD.Map (?A abc))"
                apply unfold_locales
                using abc CD_BC_AB.iso_char BC_AB.iso_char A.ide_is_iso functor.preserves_iso
                by (cases abc) simp
            qed
            have "?A abc \<noteq> AD.null"
              using abc
              by (metis (no_types, lifting) A.preserves_reflects_arr AD.not_arr_null
                  CD_BC_AB.ideD(1))
            moreover have "natural_isomorphism A D
                             (BD.Dom (?A abc)) (BD.Cod (?A abc)) (BD.Map (?A abc))"
              ..
            ultimately show ?thesis by simp
          qed
        qed
      qed
      show "\<And>(A :: 'a comp) (B :: 'a comp). \<lbrakk> A \<in> OBJ; B \<in> OBJ \<rbrakk>
               \<Longrightarrow> fully_faithful_functor (HOM A B) (HOM A B)
                         (\<lambda>f. if partial_composition.arr (HOM A B) f
                              then COMP B B A (ID B) f
                              else partial_magma.null (HOM A B))"
      proof -
        fix A :: "'a comp" and B :: "'a comp"
        assume A: "A \<in> OBJ" and B: "B \<in> OBJ"
        interpret A: category A using A by simp
        interpret B: category B using B by simp
        interpret AB: functor_category A B ..
        interpret BB: functor_category B B ..
        let ?L = "\<lambda>f. if partial_composition.arr (HOM A B) f
                      then COMP B B A (ID B) f
                      else partial_magma.null (HOM A B)"
        have "?L = AB.map"
          using AB.arr_char B.functor_axioms AB.MkArr_Map AB.is_extensional by force
        thus "fully_faithful_functor AB.comp AB.comp ?L"
          by (simp add: AB.is_fully_faithful)
      qed
      show "\<And>(A :: 'a comp) (B :: 'a comp). \<lbrakk> A \<in> OBJ; B \<in> OBJ \<rbrakk>
                   \<Longrightarrow> fully_faithful_functor (HOM A B) (HOM A B)
                         (\<lambda>f. if partial_composition.arr (HOM A B) f
                              then COMP B A A f (ID A)
                              else partial_magma.null (HOM A B))"
      proof -
        fix A :: "'a comp" and B :: "'a comp"
        assume A: "A \<in> OBJ" and B: "B \<in> OBJ"
        interpret A: category A using A by simp
        interpret B: category B using B by simp
        interpret AB: functor_category A B ..
        interpret AA: functor_category A A ..
        interpret BB: functor_category B B ..
        let ?R = "\<lambda>f. if partial_composition.arr (HOM A B) f
                      then COMP B A A f (ID A)
                      else partial_magma.null (HOM A B)"
        have "?R = AB.map"
        proof
          fix f
          have "\<not> AB.arr f \<Longrightarrow> ?R f = AB.map f"
            using AB.is_extensional by simp
          moreover have "AB.arr f \<Longrightarrow> ?R f = AB.map f"
          proof -
            assume f: "AB.arr f"
            have "?R f =
                  BB.MkArr (BB.Dom f \<circ> A.map) (BB.Cod f \<circ> A.map) (BB.Map f \<circ> A.map)"
              using f AB.arr_char BB.ide_MkIde BB.arr_char A.functor_axioms by simp
            also have "... = AB.map f"
              using f AB.arr_char AB.MkArr_Map by force
            finally show "?R f = AB.map f" by blast
          qed
          ultimately show "?R f = AB.map f" by blast
        qed
        thus "fully_faithful_functor AB.comp AB.comp ?R"
          by (simp add: AB.is_fully_faithful)
      qed
      show "\<And>(A :: 'a comp) (B :: 'a comp) (C :: 'a comp) (D :: 'a comp) (E :: 'a comp) f g h k.
            \<lbrakk> A \<in> OBJ; B \<in> OBJ; C \<in> OBJ; D \<in> OBJ; E \<in> OBJ;
              partial_composition.ide (HOM D E) f; partial_composition.ide (HOM C D) g;
              partial_composition.ide (HOM B C) h; partial_composition.ide (HOM A B) k \<rbrakk> \<Longrightarrow>
              HOM A E (COMP E D A f (ASSOC D C B A g h k))
                      (HOM A E (ASSOC E D B A f (COMP D C B g h) k)
                               (COMP E B A (ASSOC E D C B f g h) k)) =
              HOM A E (ASSOC E D C A f g (COMP C B A h k))
                      (ASSOC E C B A (COMP E D C f g) h k)"
      proof -
        fix A :: "'a comp" and B :: "'a comp" and C :: "'a comp"
          and D :: "'a comp" and E :: "'a comp"
        fix f g h k
        assume A: "A \<in> OBJ" and B: "B \<in> OBJ" and C: "C \<in> OBJ"
          and D: "D \<in> OBJ" and E: "E \<in> OBJ"
        assume f: "partial_composition.ide (HOM D E) f"
        assume g: "partial_composition.ide (HOM C D) g"
        assume h: "partial_composition.ide (HOM B C) h"
        assume k: "partial_composition.ide (HOM A B) k"
        interpret A: category A using A by simp
        interpret B: category B using B by simp
        interpret C: category C using C by simp
        interpret D: category D using D by simp
        interpret E: category E using E by simp
        interpret AB: functor_category A B ..
        interpret BC: functor_category B C ..
        interpret CD: functor_category C D ..
        interpret DE: functor_category D E ..
        interpret BD: functor_category B D ..
        interpret AD: functor_category A D ..
        interpret CE: functor_category C E ..
        interpret AC: functor_category A C ..
        interpret BE: functor_category B E ..
        interpret AE: functor_category A E ..
        interpret f: natural_transformation D E \<open>DE.Dom f\<close> \<open>DE.Cod f\<close> \<open>MAP f\<close>
          using f DE.arr_char by simp
        interpret g: natural_transformation C D \<open>CD.Dom g\<close> \<open>CD.Cod g\<close> \<open>MAP g\<close>
          using g CD.arr_char by simp
        interpret h: natural_transformation B C \<open>BC.Dom h\<close> \<open>BC.Cod h\<close> \<open>MAP h\<close>
          using h BC.arr_char by simp
        interpret k: natural_transformation A B \<open>AB.Dom k\<close> \<open>AB.Cod k\<close> \<open>MAP k\<close>
          using k AB.arr_char by simp
        have 0: "natural_transformation A E
                  (DE.Map f \<circ> CD.Map g \<circ> BC.Map h \<circ> AB.Map k)
                  (DE.Map f \<circ> CD.Map g \<circ> BC.Map h \<circ> AB.Map k)
                  (DE.Map f \<circ> CD.Map g \<circ> BC.Map h \<circ> AB.Map k)"
          using f.natural_transformation_axioms g.natural_transformation_axioms
                h.natural_transformation_axioms k.natural_transformation_axioms
                f g h k AB.ide_char BC.ide_char CD.ide_char DE.ide_char
                horizontal_composite
          by (metis (no_types, lifting))
        have 1: "natural_transformation B D
                   (CD.Map g \<circ> BC.Map h) (CD.Map g \<circ> BC.Map h) (CD.Map g \<circ> BC.Map h)"
          using g.natural_transformation_axioms h.natural_transformation_axioms
                g h BC.ide_char CD.ide_char horizontal_composite
          by (metis (no_types, lifting))
        have 2: "natural_transformation B E
                   (DE.Map f \<circ> CD.Map g \<circ> BC.Map h)
                   (DE.Map f \<circ> CD.Map g \<circ> BC.Map h)
                   (DE.Map f \<circ> CD.Map g \<circ> BC.Map h)"
          using 1 f.natural_transformation_axioms f DE.ide_char horizontal_composite o_assoc
          by (metis (no_types, lifting))
        have 3: "natural_transformation A C
                   (BC.Map h \<circ> AB.Map k) (BC.Map h \<circ> AB.Map k) (BC.Map h \<circ> AB.Map k)"
          using k.natural_transformation_axioms h.natural_transformation_axioms
                k h AB.ide_char BC.ide_char horizontal_composite
          by metis
        have 4: "natural_transformation C E
                   (DE.Map f \<circ> CD.Map g) (DE.Map f \<circ> CD.Map g) (DE.Map f \<circ> CD.Map g)"
          using f g f.natural_transformation_axioms g.natural_transformation_axioms
                CD.ide_char DE.ide_char horizontal_composite
          by metis

        have "HOM A E (COMP E D A f (ASSOC D C B A g h k))
                      (HOM A E (ASSOC E D B A f (COMP D C B g h) k)
                               (COMP E B A (ASSOC E D C B f g h) k)) =
              AE.MkIde (DE.Map f \<circ> CD.Map g \<circ> BC.Map h \<circ> AB.Map k)"
        proof -
          have "functor B E (DE.Map f \<circ> CD.Map g \<circ> BC.Map h)"
            using 2 natural_transformation_def by blast
          moreover have "functor A D (CD.Map g \<circ> BC.Map h \<circ> AB.Map k)"
            using k 1 AB.ide_char horizontal_composite k.natural_transformation_axioms
                  natural_transformation_def
            by (metis (no_types, lifting))
          ultimately show ?thesis
            using f g h k 0 1 2 by (simp add: o_assoc)
        qed
        also have "... = HOM A E (ASSOC E D C A f g (COMP C B A h k))
                                 (ASSOC E C B A (COMP E D C f g) h k)"
          using f g h k 0 3 4 AC.ide_MkIde CE.ide_MkIde
          by (simp add: o_assoc)
        finally show "HOM A E (COMP E D A f (ASSOC D C B A g h k))
                              (HOM A E (ASSOC E D B A f (COMP D C B g h) k)
                                       (COMP E B A (ASSOC E D C B f g h) k)) =
                      HOM A E (ASSOC E D C A f g (COMP C B A h k))
                              (ASSOC E C B A (COMP E D C f g) h k)"
          by blast
      qed
    qed  (* 15 sec *)

    lemma is_concrete_bicategory:
    shows "concrete_bicategory OBJ HOM ID COMP ID ASSOC"
      ..

    lemma unit_simp:
    assumes "obj a"
    shows "\<i> a = a"
      by (metis (mono_tags, lifting) \<i>_def assms obj_char)

    lemma assoc_simp:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "\<a> f g h = hcomp f (hcomp g h)"
    proof -
      let ?A = "Src h" and ?B = "Trg h" and ?C = "Trg g" and ?D = "Trg f"
      have 1: "Src f = Trg g \<and> Src g = Trg h"
        using assms by (simp add: src_def trg_def)
      interpret A: category ?A using assms Src_in_Obj [of h] by simp
      interpret B: category ?B using assms Trg_in_Obj [of h] by simp
      interpret C: category ?C using assms Trg_in_Obj [of g] by simp
      interpret D: category ?D using assms Trg_in_Obj [of f] by simp
      interpret AB: functor_category ?A ?B ..
      interpret BC: functor_category ?B ?C ..
      interpret CD: functor_category ?C ?D ..
      interpret AD: functor_category ?A ?D ..
      interpret BC_AB: product_category BC.comp AB.comp ..
      interpret CD_BC_AB: product_category CD.comp BC_AB.comp ..
      interpret f: "functor" ?C ?D \<open>CD.Map (Map f)\<close>
        using assms 1 ide_char'' [of f] arr_char [of f] CD.ide_char by simp
      interpret g: "functor" ?B ?C \<open>BC.Map (Map g)\<close>
        using assms 1 ide_char'' [of g] arr_char [of g] CD.ide_char by simp
      interpret h: "functor" ?A ?B \<open>AB.Map (Map h)\<close>
        using assms 1 ide_char'' [of h] arr_char [of h] CD.ide_char by simp
      have "\<a> f g h = MkCell ?A ?D
                        (AD.MkArr (AD.Dom (Map f) \<circ> AD.Dom (Map g) \<circ> AD.Dom (Map h))
                         (AD.Cod (Map f) \<circ> AD.Cod (Map g) \<circ> AD.Cod (Map h))
                         (AD.Map (Map f) \<circ> AD.Map (Map g) \<circ> AD.Map (Map h)))"
        using assms 1 ide_char'' \<a>_simp_ide [of f g h]
              arr_char [of f] arr_char [of g] arr_char [of h]   
        by simp
      moreover have "AD.ide (AD.MkArr
                              (CD.Dom (Map f) \<circ> BC.Dom (Map g) \<circ> AB.Dom (Map h))
                              (CD.Cod (Map f) \<circ> BC.Cod (Map g) \<circ> AB.Cod (Map h))
                              (CD.Map (Map f) \<circ> BC.Map (Map g) \<circ> AB.Map (Map h)))"
      proof -
        have "functor ?A ?D (CD.Map (Map f) \<circ> BC.Map (Map g) \<circ> AB.Map (Map h))"
          using f.functor_axioms g.functor_axioms h.functor_axioms functor_comp by blast
        hence "AD.ide (AD.MkArr (CD.Map (Map f) \<circ> BC.Map (Map g) \<circ> AB.Map (Map h))
                                (CD.Map (Map f) \<circ> BC.Map (Map g) \<circ> AB.Map (Map h))
                                (CD.Map (Map f) \<circ> BC.Map (Map g) \<circ> AB.Map (Map h)))"
          using AD.ide_char AD.null_char by simp
        thus ?thesis
          using assms 1
                ide_char'' [of f] CD.ide_char [of "Map f"]
                ide_char'' [of g] BC.ide_char [of "Map g"]
                ide_char'' [of h] AB.ide_char [of "Map h"]
          by presburger
      qed
      moreover have "arr (\<a> f g h)"
        using assms by simp
      ultimately have "ide (\<a> f g h)"
        using ide_char''' [of "\<a> f g h"] by auto
      hence "\<a> f g h = cod (\<a> f g h)"
        by simp
      thus "\<a> f g h = hcomp f (hcomp g h)"
        using assms by simp
    qed

    lemma is_strict_bicategory:
    shows "strict_bicategory vcomp hcomp \<a> \<i> src trg"
    proof -
      have "\<And>f :: ('a comp, ('a, 'a) functor_category.arr) cell. ide f \<Longrightarrow> hcomp f (src f) = f"
      proof -
        fix f :: "('a comp, ('a, 'a) functor_category.arr) cell"
        assume f: "ide f"
        let ?A = "Src f" and ?B = "Trg f"
        interpret A: category ?A
          using f Src_in_Obj [of f] by simp
        interpret B: category ?B
          using f Trg_in_Obj [of f] by simp
        interpret AA: functor_category ?A ?A ..
        interpret AB: functor_category ?A ?B ..
        have 1: "functor ?A ?B (AB.Cod (Map f)) \<and> functor ?A ?B (AB.Dom (Map f)) \<and>
                 functor ?A ?B (AB.Map (Map f))"
          using f ide_char''' AB.ide_char [of "Map f"] ide_char'' [of f] arr_char [of f]
          by auto
        have "hcomp f (src f) = MkCell ?A ?B (Map f)"
          unfolding hcomp_def src_def
          using f 1 AB.arr_char AB.null_char AB.ide_char
                obj_MkObj [of "Src f"] obj_def functor_is_transformation ide_char'''
                AB.ide_MkIde Src_in_Obj [of f] obj_MkObj obj_def AB.null_char arr_Map [of f]
                A.functor_axioms AB.MkArr_Map arr_Map
          by auto
        also have "... = f"
          using f MkCell_Map [of f] not_arr_null ideD(1) [of f] by fastforce
        finally show "hcomp f (src f) = f" by blast
      qed
      moreover have
        "\<And>f :: ('a comp, ('a, 'a) functor_category.arr) cell. ide f \<Longrightarrow> hcomp (trg f) f = f"
      proof -
        fix f :: "('a comp, ('a, 'a) functor_category.arr) cell"
        assume f: "ide f"
        let ?A = "Src f" and ?B = "Trg f"
        interpret A: category ?A
          using f Src_in_Obj [of f] by simp
        interpret B: category ?B
          using f Trg_in_Obj [of f] by simp
        interpret BB: functor_category ?B ?B ..
        interpret AB: functor_category ?A ?B ..
        have 1: "functor ?A ?B (AB.Cod (Map f)) \<and> functor ?A ?B (AB.Dom (Map f)) \<and>
                 functor ?A ?B (AB.Map (Map f))"
          using f ide_char''' AB.ide_char [of "Map f"] ide_char'' [of f] arr_char [of f]
          by auto
        have "hcomp (trg f) f = MkCell ?A ?B (Map f)"
          unfolding hcomp_def trg_def
          using f 1 AB.arr_char AB.null_char AB.ide_char
                obj_MkObj [of "Trg f"] obj_def functor_is_transformation ide_char'''
                AB.ide_MkIde Trg_in_Obj [of f] obj_MkObj obj_def AB.null_char arr_Map [of f]
                B.functor_axioms AB.MkArr_Map arr_Map
          by auto
        also have "... = f"
          using f MkCell_Map [of f] not_arr_null ideD(1) [of f] by fastforce
        finally show "hcomp (trg f) f = f" by blast
      qed
      moreover have "\<And>a. obj a \<Longrightarrow> ide (\<i> a)"
        using \<i>_def by (metis (mono_tags, lifting) obj_MkObj_Src objE obj_def)
      moreover have "\<And>(f :: ('a comp, ('a, 'a) functor_category.arr) cell) g h.
                         \<lbrakk> ide f; ide g; ide h; src f = trg g; src g = trg h \<rbrakk> \<Longrightarrow> ide (\<a> f g h)"
        by (simp add: assoc_simp)
      ultimately show ?thesis
        using is_strict_if by blast
    qed

    sublocale strict_bicategory vcomp hcomp \<a> \<i> src trg
      using is_strict_bicategory by simp

  end

end
