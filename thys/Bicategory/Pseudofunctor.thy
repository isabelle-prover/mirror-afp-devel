(*  Title:       Pseudofunctor
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Pseudofunctors"

theory Pseudofunctor
imports MonoidalCategory.MonoidalFunctor Bicategory Subbicategory InternalEquivalence Coherence
begin

  text \<open>
    The traditional definition of a pseudofunctor \<open>F : C \<rightarrow> D\<close> between bicategories \<open>C\<close> and \<open>D\<close>
    is in terms of two maps: an ``object map'' \<open>F\<^sub>o\<close> that takes objects of \<open>C\<close> to objects of \<open>D\<close>
    and an ``arrow map'' \<open>F\<^sub>a\<close> that assigns to each pair of objects \<open>a\<close> and \<open>b\<close> of \<open>C\<close>
    a functor \<open>F\<^sub>a a b\<close> from the hom-category \<open>hom\<^sub>C a b\<close> to the hom-category \<open>hom\<^sub>D (F\<^sub>o a) (F\<^sub>o b)\<close>.
    In addition, there is assigned to each object \<open>a\<close> of \<open>C\<close> an invertible 2-cell
    \<open>\<guillemotleft>\<Psi> a : F\<^sub>o a \<Rightarrow>\<^sub>D (F\<^sub>a a a) a\<guillemotright>\<close>, and to each pair \<open>(f, g)\<close> of composable 1-cells of C there
    is assigned an invertible 2-cell \<open>\<guillemotleft>\<Phi> (f, g) : F g \<star> F f \<Rightarrow> F (g \<star> f)\<guillemotright>\<close>, all subject to
    naturality and coherence conditions.

    In keeping with the ``object-free'' style in which we have been working, we do not wish
    to adopt a definition of pseudofunctor that distinguishes between objects and other
    arrows.  Instead, we would like to understand a pseudofunctor as an ordinary functor between
    (vertical) categories that weakly preserves horizontal composition in a suitable sense.
    So, we take as a starting point that a pseudofunctor \<open>F : C \<rightarrow> D\<close> is a functor from
    \<open>C\<close> to \<open>D\<close>, when these are regarded as ordinary categories with respect to vertical
    composition.  Next, \<open>F\<close> should preserve source and target, but only ``weakly''
    (up to isomorphism, rather than ``on the nose'').
    Weak preservation of horizontal composition is expressed by specifying, for each horizontally
    composable pair of vertical identities \<open>(f, g)\<close> of \<open>C\<close>, a ``compositor''
    \<open>\<guillemotleft>\<Phi> (f, g) : F g \<star> F f \<Rightarrow> F (g \<star> f)\<guillemotright>\<close> in \<open>D\<close>, such that the \<open>\<Phi> (f, g)\<close> are the components
    of a natural isomorphism.
    Associators must also be weakly preserved by F; this is expressed by a coherence
    condition that relates an associator \<open>\<a>\<^sub>C[f, g, h]\<close> in \<open>C\<close>, its image \<open>F \<a>\<^sub>C[f, g, h]\<close>,
    the associator \<open>\<a>\<^sub>D[F f, F g, F h]\<close> in \<open>D\<close> and compositors involving \<open>f\<close>, \<open>g\<close>, and \<open>h\<close>.
    As regards the weak preservation of unitors, just as for monoidal functors,
    which are in fact pseudofunctors between one-object bicategories, it is only necessary
    to assume that \<open>F \<i>\<^sub>C[a]\<close> and \<open>\<i>\<^sub>D[F a]\<close> are isomorphic in \<open>D\<close> for each object \<open>a\<close> of \<open>C\<close>,
    for there is then a canonical way to obtain, for each \<open>a\<close>, an isomorphism
    \<open>\<guillemotleft>\<Psi> a : src (F a) \<rightarrow> F a\<guillemotright>\<close> that satisfies the usual coherence conditions relating the
    unitors and the associators.  Note that the map \<open>a \<mapsto> src (F a)\<close> amounts to the traditional
    ``object map'' \<open>F\<^sub>o\<close>, so that this becomes a derived notion, rather than a primitive one.
  \<close>

  subsection "Weak Arrows of Homs"

  text \<open>
    We begin with a locale that defines a functor between ``horizontal homs'' that preserves
    source and target up to isomorphism.
  \<close>

  locale weak_arrow_of_homs =
    C: horizontal_homs C src\<^sub>C trg\<^sub>C +
    D: horizontal_homs D src\<^sub>D trg\<^sub>D +
    "functor" C D F
  for C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd" +
  assumes weakly_preserves_src: "\<And>\<mu>. C.arr \<mu> \<Longrightarrow> D.isomorphic (F (src\<^sub>C \<mu>)) (src\<^sub>D (F \<mu>))"
  and weakly_preserves_trg: "\<And>\<mu>. C.arr \<mu> \<Longrightarrow> D.isomorphic (F (trg\<^sub>C \<mu>)) (trg\<^sub>D (F \<mu>))"
  begin

    lemma isomorphic_src:
    assumes "C.obj a"
    shows "D.isomorphic (src\<^sub>D (F a)) (F a)"
      using assms weakly_preserves_src C.obj_def D.isomorphic_symmetric by force

    lemma isomorphic_trg:
    assumes "C.obj a"
    shows "D.isomorphic (trg\<^sub>D (F a)) (F a)"
      using assms weakly_preserves_trg C.objE
      by (metis C.obj_def D.isomorphic_symmetric)

    abbreviation (input) hseq\<^sub>C
    where "hseq\<^sub>C \<mu> \<nu> \<equiv> C.arr \<mu> \<and> C.arr \<nu> \<and> src\<^sub>C \<mu> = trg\<^sub>C \<nu>"

    abbreviation (input) hseq\<^sub>D
    where "hseq\<^sub>D \<mu> \<nu> \<equiv> D.arr \<mu> \<and> D.arr \<nu> \<and> src\<^sub>D \<mu> = trg\<^sub>D \<nu>"

    lemma preserves_hseq:
    assumes "hseq\<^sub>C \<mu> \<nu>"
    shows "hseq\<^sub>D (F \<mu>) (F \<nu>)"
    proof -
      have "src\<^sub>C \<mu> = trg\<^sub>C \<nu>"
        using assms by auto
      hence "D.isomorphic (F (src\<^sub>C \<mu>)) (trg\<^sub>D (F \<nu>))"
        using assms weakly_preserves_trg by auto
      moreover have "D.isomorphic (src\<^sub>D (F \<mu>)) (F (src\<^sub>C \<mu>))"
        using assms weakly_preserves_src D.isomorphic_symmetric by blast
      ultimately have "D.isomorphic (src\<^sub>D (F \<mu>)) (trg\<^sub>D (F \<nu>))"
        using D.isomorphic_transitive by blast
      hence "src\<^sub>D (F \<mu>) = trg\<^sub>D (F \<nu>)"
        using assms D.isomorphic_objects_are_equal by auto
      thus ?thesis
        using assms by auto
    qed

    text \<open>
      Though \<open>F\<close> does not preserve objects ``on the nose'', we can recover from it the
      usual ``object map'', which does.
      It is slightly confusing at first to get used to the idea that applying the
      object map of a weak arrow of homs to an object does not give the same thing
      as applying the underlying functor, but rather only something isomorphic to it.

      The following defines the object map associated with \<open>F\<close>.
    \<close>

    definition map\<^sub>0
    where "map\<^sub>0 a \<equiv> src\<^sub>D (F a)"

    lemma map\<^sub>0_simps [simp]:
    assumes "C.obj a"
    shows "D.obj (map\<^sub>0 a)"
    and "src\<^sub>D (map\<^sub>0 a) = map\<^sub>0 a" and "trg\<^sub>D (map\<^sub>0 a) = map\<^sub>0 a"
    and "D.dom (map\<^sub>0 a) = map\<^sub>0 a" and "D.cod (map\<^sub>0 a) = map\<^sub>0 a"
      using assms map\<^sub>0_def by auto

    lemma preserves_src [simp]:
    assumes "C.arr \<mu>"
    shows "src\<^sub>D (F \<mu>) = map\<^sub>0 (src\<^sub>C \<mu>)"
      using assms
      by (metis C.src.preserves_arr C.src_src C.trg_src map\<^sub>0_def preserves_hseq)

    lemma preserves_trg [simp]:
    assumes "C.arr \<mu>"
    shows "trg\<^sub>D (F \<mu>) = map\<^sub>0 (trg\<^sub>C \<mu>)"
      using assms map\<^sub>0_def preserves_hseq C.src_trg C.trg.preserves_arr by presburger

    lemma preserves_hhom [intro]:
    assumes "C.arr \<mu>"
    shows "D.in_hhom (F \<mu>) (map\<^sub>0 (src\<^sub>C \<mu>)) (map\<^sub>0 (trg\<^sub>C \<mu>))"
      using assms by simp

    text \<open>
      We define here the lifting of \<open>F\<close> to a functor \<open>FF: CC \<rightarrow> DD\<close>.
      We need this to define the domains and codomains of the compositors.
    \<close>

    definition FF
    where "FF \<equiv> \<lambda>\<mu>\<nu>. if C.VV.arr \<mu>\<nu> then (F (fst \<mu>\<nu>), F (snd \<mu>\<nu>)) else D.VV.null"

    sublocale FF: "functor" C.VV.comp D.VV.comp FF
    proof -
      have 1: "\<And>\<mu>\<nu>. C.VV.arr \<mu>\<nu> \<Longrightarrow> D.VV.arr (FF \<mu>\<nu>)"
        unfolding FF_def using C.VV.arr_char D.VV.arr_char preserves_hseq by simp
      show "functor C.VV.comp D.VV.comp FF"
      proof
        fix \<mu>\<nu>
        show "\<not> C.VV.arr \<mu>\<nu> \<Longrightarrow> FF \<mu>\<nu> = D.VV.null"
          using FF_def by simp
        show "C.VV.arr \<mu>\<nu> \<Longrightarrow> D.VV.arr (FF \<mu>\<nu>)"
          using 1 by simp
        assume \<mu>\<nu>: "C.VV.arr \<mu>\<nu>"
        show "D.VV.dom (FF \<mu>\<nu>) = FF (C.VV.dom \<mu>\<nu>)"
          using \<mu>\<nu> 1 FF_def C.VV.arr_char D.VV.arr_char by simp
        show "D.VV.cod (FF \<mu>\<nu>) = FF (C.VV.cod \<mu>\<nu>)"
          using \<mu>\<nu> 1 FF_def C.VV.arr_char D.VV.arr_char by simp
        next
        fix \<mu>\<nu> \<tau>\<pi>
        assume 2: "C.VV.seq \<mu>\<nu> \<tau>\<pi>"
        show "FF (C.VV.comp \<mu>\<nu> \<tau>\<pi>) = D.VV.comp (FF \<mu>\<nu>) (FF \<tau>\<pi>)"
        proof -
          have "FF (C.VV.comp \<mu>\<nu> \<tau>\<pi>) = (F (fst \<mu>\<nu>) \<cdot>\<^sub>D F (fst \<tau>\<pi>), F (snd \<mu>\<nu>) \<cdot>\<^sub>D F (snd \<tau>\<pi>))"
            using 1 2 FF_def C.VV.comp_char C.VxV.comp_char C.VV.arr_char
            by (metis (no_types, lifting) C.VV.seq_char C.VxV.seqE fst_conv preserves_comp_2 snd_conv)
          also have "... = D.VV.comp (FF \<mu>\<nu>) (FF \<tau>\<pi>)"
            using 1 2 FF_def D.VV.comp_char D.VxV.comp_char C.VV.arr_char D.VV.arr_char
                  C.VV.seq_char C.VxV.seqE preserves_seq
            by (simp, meson)
          finally show ?thesis by simp
        qed
      qed
    qed

    lemma functor_FF:
    shows "functor C.VV.comp D.VV.comp FF"
      ..

  end

  subsection "Definition of Pseudofunctors"

  text \<open>
    I don't much like the term "pseudofunctor", which is suggestive of something that
    is ``not really'' a functor.  In the development here we can see that a pseudofunctor
    is really a \emph{bona fide} functor with respect to vertical composition,
    which happens to have in addition a weak preservation property with respect to
    horizontal composition.
    This weak preservation of horizontal composition is captured by extra structure,
    the ``compositors'', which are the components of a natural transformation.
    So ``pseudofunctor'' is really a misnomer; it's an actual functor that has been equipped
    with additional structure relating to horizontal composition.  I would use the term
    ``bifunctor'' for such a thing, but it seems to not be generally accepted and also tends
    to conflict with the usage of that term to refer to an ordinary functor of two
    arguments; which I have called a ``binary functor''.  Sadly, there seem to be no other
    plausible choices of terminology, other than simply ``functor''
    (recommended on n-Lab @{url \<open>https://ncatlab.org/nlab/show/pseudofunctor\<close>}),
    but that is not workable here because we need a name that does not clash with that
    used for an ordinary functor between categories.
  \<close>

  locale pseudofunctor =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    weak_arrow_of_homs V\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D src\<^sub>D trg\<^sub>D F +
    FoH\<^sub>C: composite_functor C.VV.comp V\<^sub>C V\<^sub>D \<open>\<lambda>\<mu>\<nu>. H\<^sub>C (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> F +
    H\<^sub>DoFF: composite_functor C.VV.comp D.VV.comp V\<^sub>D
             FF \<open>\<lambda>\<mu>\<nu>. H\<^sub>D (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> +
    \<Phi>: natural_isomorphism C.VV.comp V\<^sub>D H\<^sub>DoFF.map FoH\<^sub>C.map \<Phi>
  for V\<^sub>C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd"
  and \<Phi> :: "'c * 'c \<Rightarrow> 'd" +
  assumes assoc_coherence:
            "\<lbrakk> C.ide f; C.ide g; C.ide h; src\<^sub>C f = trg\<^sub>C g; src\<^sub>C g = trg\<^sub>C h \<rbrakk> \<Longrightarrow>
               F \<a>\<^sub>C[f, g, h] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) =
               \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h]"
  begin

    no_notation C.in_hom                  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    no_notation D.in_hom                  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")
    notation C.in_hhom                    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    notation C.in_hom                     ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>C _\<guillemotright>")
    notation D.in_hhom                    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")
    notation D.in_hom                     ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>D _\<guillemotright>")

    notation C.lunit                      ("\<l>\<^sub>C[_]")
    notation C.runit                      ("\<r>\<^sub>C[_]")
    notation C.lunit'                     ("\<l>\<^sub>C\<^sup>-\<^sup>1[_]")
    notation C.runit'                     ("\<r>\<^sub>C\<^sup>-\<^sup>1[_]")
    notation C.\<a>'                         ("\<a>\<^sub>C\<^sup>-\<^sup>1[_, _, _]")
    notation D.lunit                      ("\<l>\<^sub>D[_]")
    notation D.runit                      ("\<r>\<^sub>D[_]")
    notation D.lunit'                     ("\<l>\<^sub>D\<^sup>-\<^sup>1[_]")
    notation D.runit'                     ("\<r>\<^sub>D\<^sup>-\<^sup>1[_]")
    notation D.\<a>'                         ("\<a>\<^sub>D\<^sup>-\<^sup>1[_, _, _]")

    lemma weakly_preserves_objects:
    assumes "C.obj a"
    shows "D.isomorphic (map\<^sub>0 a) (F a)"
      using assms weakly_preserves_src [of a] D.isomorphic_symmetric by auto

    lemma \<Phi>_in_hom [intro]:
    assumes "C.ide a" and "C.ide b" and "src\<^sub>C a = trg\<^sub>C b"
    shows "\<guillemotleft>\<Phi> (a, b) : map\<^sub>0 (src\<^sub>C b) \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C a)\<guillemotright>"
    and "\<guillemotleft>\<Phi> (a, b) : F a \<star>\<^sub>D F b \<Rightarrow>\<^sub>D F (a \<star>\<^sub>C b)\<guillemotright>"
    proof -
      show "\<guillemotleft>\<Phi> (a, b) : F a \<star>\<^sub>D F b \<Rightarrow>\<^sub>D F (a \<star>\<^sub>C b)\<guillemotright>"
      proof -
        have "H\<^sub>DoFF.map (a, b) = F a \<star>\<^sub>D F b"
          using assms C.VV.ide_char FF_def by auto
        moreover have "FoH\<^sub>C.map (a, b) = F (a \<star>\<^sub>C b)"
          using assms C.VV.ide_char by simp
        ultimately show ?thesis
          using assms C.VV.ide_char \<Phi>.preserves_hom
          apply simp
          by (metis (no_types, lifting) C.VV.ideI C.VV.ide_in_hom C.VxV.ide_Ide C.ideD(1)
              fst_conv snd_conv)
      qed
      show "\<guillemotleft>\<Phi> (a, b) : map\<^sub>0 (src\<^sub>C b) \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C a)\<guillemotright>"
      proof -
        have "C.hseq a b"
          by (simp add: assms(1-3))
        thus ?thesis
          by (metis C.src_hcomp C.trg_hcomp D.in_hhom_def D.in_homE D.src_cod D.trg_cod
              \<open>\<guillemotleft>\<Phi> (a, b) : F a \<star>\<^sub>D F b \<Rightarrow>\<^sub>D F (a \<star>\<^sub>C b)\<guillemotright>\<close> preserves_src preserves_trg)
      qed
    qed

    lemma \<Phi>_simps [simp]:
    assumes "C.ide f" and "C.ide g" and "src\<^sub>C f = trg\<^sub>C g"
    shows "D.arr (\<Phi> (f, g))"
    and "src\<^sub>D (\<Phi> (f, g)) = src\<^sub>D (F g)" and "trg\<^sub>D (\<Phi> (f, g)) = trg\<^sub>D (F f)"
    and "D.dom (\<Phi> (f, g)) = F f \<star>\<^sub>D F g" and "D.cod (\<Phi> (f, g)) = F (f \<star>\<^sub>C g)"
    and "D.iso (\<Phi> (f, g))"
    proof -
      show "D.arr (\<Phi> (f, g))"
        using assms \<Phi>_in_hom by auto
      show "src\<^sub>D (\<Phi> (f, g)) = src\<^sub>D (F g)"
        using assms \<Phi>_in_hom by auto
      show "trg\<^sub>D (\<Phi> (f, g)) = trg\<^sub>D (F f)"
        using assms \<Phi>_in_hom by auto
      show "D.dom (\<Phi> (f, g)) = F f \<star>\<^sub>D F g"
        using assms \<Phi>_in_hom by blast
      show "D.cod (\<Phi> (f, g)) = F (f \<star>\<^sub>C g)"
        using assms \<Phi>_in_hom by blast
      show "D.iso (\<Phi> (f, g))"
        using assms C.VV.ide_char C.VV.arr_char by simp
    qed

    lemma \<Phi>_components_are_iso:
    assumes "C.ide f" and "C.ide g" and "src\<^sub>C f = trg\<^sub>C g"
    shows "D.iso (\<Phi> (f, g))"
      using assms C.VV.ide_char C.VV.arr_char by simp

    lemma weakly_preserves_hcomp:
    assumes "C.ide f" and "C.ide g" and "src\<^sub>C f = trg\<^sub>C g"
    shows "D.isomorphic (F f \<star>\<^sub>D F g) (F (f \<star>\<^sub>C g))"
      using assms D.isomorphic_def by auto

    text \<open>
      The following defines the image of the unit isomorphism \<open>\<i>\<^sub>C[a]\<close> under \<open>F\<close>.
      We will use \<open>(F a, \<i>[a])\<close> as an ``alternate unit'', to substitute for
      \<open>(src\<^sub>D (F a), \<i>\<^sub>D[src\<^sub>D (F a)])\<close>.
    \<close>

    abbreviation (input) \<i>  ("\<i>[_]")
    where "\<i>[a] \<equiv> F \<i>\<^sub>C[a] \<cdot>\<^sub>D \<Phi> (a, a)"

    lemma \<i>_in_hom [intro]:
    assumes "C.obj a"
    shows "\<guillemotleft>F \<i>\<^sub>C[a] \<cdot>\<^sub>D \<Phi> (a, a) : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>\<i>[a] : F a \<star>\<^sub>D F a \<Rightarrow>\<^sub>D F a\<guillemotright>"
    proof (unfold map\<^sub>0_def)
      show "\<guillemotleft>F \<i>\<^sub>C[a] \<cdot>\<^sub>D \<Phi> (a, a) : F a \<star>\<^sub>D F a \<Rightarrow>\<^sub>D F a\<guillemotright>"
        using assms preserves_hom \<Phi>_in_hom
        by (intro D.comp_in_homI, auto)
      show "\<guillemotleft>F \<i>\<^sub>C[a] \<cdot>\<^sub>D \<Phi> (a, a) : src\<^sub>D (F a) \<rightarrow>\<^sub>D src\<^sub>D (F a)\<guillemotright>"
        using assms C.VV.arr_char
        by (intro D.vcomp_in_hhom D.seqI, auto)
    qed

    lemma \<i>_simps [simp]:
    assumes "C.obj a"
    shows "D.arr (\<i> a)"
    and "src\<^sub>D \<i>[a] = map\<^sub>0 a" and "trg\<^sub>D \<i>[a] = map\<^sub>0 a"
    and "D.dom \<i>[a] = F a \<star>\<^sub>D F a" and "D.cod \<i>[a] = F a"
    proof -
      show "src\<^sub>D \<i>[a] = map\<^sub>0 a"
        unfolding map\<^sub>0_def
        using assms \<i>_in_hom D.src_cod [of "F a"]
        by (metis C.unit_simps(1) C.unit_simps(5) D.arrI D.src_vcomp D.vseq_implies_hpar(1)
            is_natural_2 preserves_arr)
      show "trg\<^sub>D \<i>[a] = map\<^sub>0 a"
        unfolding map\<^sub>0_def
        using assms \<i>_in_hom D.trg_cod [of "F a"]
        by (metis C.obj_def C.unit_simps(1) C.unit_simps(3) D.arrI D.trg_vcomp preserves_hseq)
      show "D.arr \<i>[a]"
        using assms \<i>_in_hom by auto
      show "D.dom \<i>[a] = F a \<star>\<^sub>D F a"
        using assms \<i>_in_hom by auto
      show "D.cod \<i>[a] = F a"
        using assms \<i>_in_hom by auto
    qed

    lemma iso_\<i>:
    assumes "C.obj a"
    shows "D.iso \<i>[a]"
    proof -
      have "D.iso (\<Phi> (a, a))"
        using assms by auto
      moreover have "D.iso (F \<i>\<^sub>C[a])"
        using assms C.iso_unit preserves_iso by simp
      moreover have "D.seq (F \<i>\<^sub>C[a]) (\<Phi> (a, a))"
        using assms C.obj_self_composable(1) C.seq_if_composable by blast
      ultimately show ?thesis by auto
    qed

  end

  context pseudofunctor
  begin

    text \<open>
      If \<open>a\<close> is an object of \<open>C\<close> and we have an isomorphism \<open>\<guillemotleft>\<Phi> (a, a) : F a \<star>\<^sub>D F a \<Rightarrow>\<^sub>D F (a \<star>\<^sub>C a)\<guillemotright>\<close>,
      then there is a canonical way to define a compatible isomorphism \<open>\<guillemotleft>\<Psi> a : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>\<close>.
      Specifically, we take \<open>\<Psi> a\<close> to be the unique isomorphism \<open>\<guillemotleft>\<psi> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>\<close> such that
      \<open>\<psi> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D \<psi>)\<close>.
    \<close>

    definition \<Psi>
    where "\<Psi> a \<equiv> THE \<psi>. \<guillemotleft>\<psi> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright> \<and> D.iso \<psi> \<and>
                         \<psi> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D \<psi>)"

    lemma \<Psi>_char:
    assumes "C.obj a"
    shows "\<guillemotleft>\<Psi> a : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>" and "D.iso (\<Psi> a)"
    and "\<Psi> a \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<Psi> a \<star>\<^sub>D \<Psi> a)"
    and "\<exists>!\<psi>. \<guillemotleft>\<psi> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright> \<and> D.iso \<psi> \<and> \<psi> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D \<psi>)"
    proof -
      let ?P = "\<lambda>\<psi>. \<guillemotleft>\<psi> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright> \<and> D.iso \<psi> \<and> \<psi> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D \<psi>)"
      show "\<exists>!\<psi>. ?P \<psi>"
      proof -
        have "D.obj (map\<^sub>0 a)"
          using assms by simp
        moreover have "D.isomorphic (map\<^sub>0 a) (F a)"
          unfolding map\<^sub>0_def
          using assms isomorphic_src by simp
        ultimately show ?thesis
          using assms D.unit_unique_upto_unique_iso \<Phi>.preserves_hom \<i>_in_hom iso_\<i> by simp
      qed
      hence 1: "?P (\<Psi> a)"
        using assms \<Psi>_def the1I2 [of ?P ?P] by simp
      show "\<guillemotleft>\<Psi> a : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>" using 1 by simp
      show "D.iso (\<Psi> a)" using 1 by simp
      show "\<Psi> a \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<Psi> a \<star>\<^sub>D \<Psi> a)"
        using 1 by simp
    qed

    lemma \<Psi>_simps [simp]:
    assumes "C.obj a"
    shows "D.arr (\<Psi> a)"
    and "src\<^sub>D (\<Psi> a) = map\<^sub>0 a" and "trg\<^sub>D (\<Psi> a) = map\<^sub>0 a"
    and "D.dom (\<Psi> a) = map\<^sub>0 a" and "D.cod (\<Psi> a) = F a"
    proof -
      show "D.arr (\<Psi> a)"
        using assms \<Psi>_char(1) by auto
      show 1: "D.dom (\<Psi> a) = map\<^sub>0 a"
        using assms \<Psi>_char(1) by auto
      show 2: "D.cod (\<Psi> a) = F a"
        using assms \<Psi>_char(1) by auto
      show "src\<^sub>D (\<Psi> a) = map\<^sub>0 a"
        using assms 1 D.src_dom
        unfolding map\<^sub>0_def
        by (metis C.obj_def D.arr_dom_iff_arr D.src.preserves_reflects_arr D.src_src preserves_arr)
      show "trg\<^sub>D (\<Psi> a) = map\<^sub>0 a"
        unfolding map\<^sub>0_def
        using assms 2 \<Psi>_char
        by (metis "1" D.trg_dom map\<^sub>0_def map\<^sub>0_simps(3) \<open>D.arr (\<Psi> a)\<close>)
    qed

    lemma \<Psi>_in_hom [intro]:
    assumes "C.obj a"
    shows "\<guillemotleft>\<Psi> a : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>\<Psi> a : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>"
      using assms by auto

    lemma \<Psi>_eqI:
    assumes "C.obj a" and "\<guillemotleft>\<mu>: map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>" and "D.iso \<mu>"
    and "\<mu> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i> a \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D \<mu>)"
    shows "\<mu> = \<Psi> a"
      using assms \<Psi>_def \<Psi>_char
            the1_equality [of "\<lambda>\<mu>. \<guillemotleft>\<mu> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright> \<and> D.iso \<mu> \<and>
                                   \<mu> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D \<mu>)" \<mu>]
      by simp

    text \<open>
      The following defines the unique isomorphism satisfying the characteristic conditions
      for the left unitor \<open>\<l>\<^sub>D[trg\<^sub>D (F f)]\<close>, but using the ``alternate unit'' \<open>\<i>[trg\<^sub>C f]\<close>
      instead of \<open>\<i>\<^sub>D[trg\<^sub>D (F f)]\<close>, which is used to define \<open>\<l>\<^sub>D[trg\<^sub>D (F f)]\<close>.
    \<close>

    definition lF
    where "lF f \<equiv> THE \<mu>. \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright> \<and>
                         F (trg\<^sub>C f) \<star>\<^sub>D \<mu> =(\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"

    lemma lF_char:
    assumes "C.ide f"
    shows "\<guillemotleft>lF f : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright>"
    and "F (trg\<^sub>C f) \<star>\<^sub>D lF f = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
    and "\<exists>!\<mu>. \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright> \<and>
                   F (trg\<^sub>C f) \<star>\<^sub>D \<mu> = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
    proof -
      let ?P = "\<lambda>\<mu>. \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright> \<and>
                     F (trg\<^sub>C f) \<star>\<^sub>D \<mu> = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
      show "\<exists>!\<mu>. ?P \<mu>"
      proof -
        interpret Df: prebicategory \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<a>\<^sub>D
          using D.is_prebicategory by simp
        interpret S: subcategory \<open>(\<cdot>\<^sub>D)\<close> \<open>Df.left (F (trg\<^sub>C f))\<close>
          using assms Df.left_hom_is_subcategory by simp
        interpret Df: left_hom \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<open>F (trg\<^sub>C f)\<close>
          using assms D.weak_unit_char
          apply unfold_locales by simp
        interpret Df: left_hom_with_unit \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<a>\<^sub>D \<open>\<i>[trg\<^sub>C f]\<close> \<open>F (trg\<^sub>C f)\<close>
        proof
          show "Df.weak_unit (F (trg\<^sub>C f))"
            using assms D.weak_unit_char
            by (metis C.ideD(1) C.trg.preserves_reflects_arr C.trg_trg weakly_preserves_trg)
          show "\<guillemotleft>\<i>[trg\<^sub>C f] : F (trg\<^sub>C f) \<star>\<^sub>D F (trg\<^sub>C f) \<Rightarrow>\<^sub>D F (trg\<^sub>C f)\<guillemotright>"
            using assms \<i>_in_hom by simp
          show "D.iso \<i>[trg\<^sub>C f]"
            using assms iso_\<i> by simp
        qed
        have "\<exists>!\<mu>. \<guillemotleft>\<mu> : Df.L (F f) \<Rightarrow>\<^sub>S F f\<guillemotright> \<and>
                   Df.L \<mu> = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>S \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
        proof -
          have "Df.left (F (trg\<^sub>C f)) (F f)"
            using assms weakly_preserves_src D.isomorphic_def D.hseq_char D.hseq_char'
                  Df.left_def
            by fastforce
          thus ?thesis
            using assms Df.lunit_char(3) S.ide_char S.arr_char by simp
        qed
        moreover have "Df.L (F f) = F (trg\<^sub>C f) \<star>\<^sub>D F f"
          using assms by (simp add: Df.H\<^sub>L_def)
        moreover have "\<And>\<mu>. Df.L \<mu> = F (trg\<^sub>C f) \<star>\<^sub>D \<mu>"
          using Df.H\<^sub>L_def by simp
        moreover have "(\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>S \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f] =
                       (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
          by (metis (no_types, lifting) D.assoc'_eq_inv_assoc D.ext D.hseqE D.seqE
              D.vconn_implies_hpar(1) D.vconn_implies_hpar(3) Df.characteristic_iso(4)
              Df.equivalence_functor_L Df.iso_unit(2) S.comp_simp S.ext S.ide_char
              S.in_hom_char S.iso_is_arr S.null_char calculation(1) category.ide_cod
              category.in_homE equivalence_functor_def)
        moreover have "\<And>\<mu>. \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright> \<longleftrightarrow>
                            \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>S F f\<guillemotright>"
          using assms S.in_hom_char S.arr_char
          by (metis D.in_homE Df.hom_connected(2) Df.left_def calculation(1) calculation(2))
        ultimately show ?thesis by simp
      qed
      hence 1: "?P (lF f)"
        using lF_def the1I2 [of ?P ?P] by simp
      show "\<guillemotleft>lF f : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright>"
        using 1 by simp
      show "F (trg\<^sub>C f) \<star>\<^sub>D lF f = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
        using 1 by simp
    qed

    lemma lF_simps [simp]:
    assumes "C.ide f"
    shows "D.arr (lF f)"
    and "src\<^sub>D (lF f) = map\<^sub>0 (src\<^sub>C f)" and "trg\<^sub>D (lF f) = map\<^sub>0 (trg\<^sub>C f)"
    and "D.dom (lF f) = F (trg\<^sub>C f) \<star>\<^sub>D F f" and "D.cod (lF f) = F f"
    proof -
      show "D.arr (lF f)"
        using assms lF_char(1) by auto
      show "D.dom (lF f) = F (trg\<^sub>C f) \<star>\<^sub>D F f"
        using assms lF_char(1) by auto
      show "D.cod (lF f) = F f"
        using assms lF_char(1) by auto
      show "src\<^sub>D (lF f) = map\<^sub>0 (src\<^sub>C f)"
        unfolding map\<^sub>0_def
        using assms \<open>D.arr (lF f)\<close> \<open>D.cod (lF f) = F f\<close> D.src_cod by fastforce
      show "trg\<^sub>D (lF f) = map\<^sub>0 (trg\<^sub>C f)"
        using assms \<open>D.arr (lF f)\<close> \<open>D.cod (lF f) = F f\<close> D.trg_cod by fastforce
    qed

    text \<open>
      \sloppypar
      The next two lemmas generalize the eponymous results from
      @{theory MonoidalCategory.MonoidalFunctor}.  See the proofs of those results for diagrams.
    \<close>

    lemma lunit_coherence1:
    assumes "C.ide f"
    shows "\<l>\<^sub>D[F f] \<cdot>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f) = lF f"
    proof -
      let ?b = "trg\<^sub>C f"
      have 1: "trg\<^sub>D (F f) = map\<^sub>0 ?b"
        using assms by simp
      have "lF f \<cdot>\<^sub>D (\<Psi> ?b \<star>\<^sub>D F f) = \<l>\<^sub>D[F f]"
      proof -
        have "D.par (lF f \<cdot>\<^sub>D (\<Psi> ?b \<star>\<^sub>D F f)) \<l>\<^sub>D[F f]"
          using assms 1 D.lunit_in_hom \<Psi>_char(1-2) lF_char(1) D.ideD(1) by auto
        moreover have "map\<^sub>0 ?b \<star>\<^sub>D (lF f \<cdot>\<^sub>D (\<Psi> ?b \<star>\<^sub>D F f)) = map\<^sub>0 ?b \<star>\<^sub>D \<l>\<^sub>D[F f]"
        proof -
          have "map\<^sub>0 ?b \<star>\<^sub>D (lF f \<cdot>\<^sub>D (\<Psi> ?b \<star>\<^sub>D F f)) =
                (map\<^sub>0 ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D (map\<^sub>0 ?b \<star>\<^sub>D \<Psi> ?b \<star>\<^sub>D F f)"
            using assms D.objE [of "map\<^sub>0 (trg\<^sub>C f)"]
                  D.whisker_left [of "map\<^sub>0 ?b" "lF f" "\<Psi> ?b \<star>\<^sub>D F f"]
            by auto
          also have "... = (map\<^sub>0 ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D
                             (D.inv (\<Psi> ?b) \<star>\<^sub>D F ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<Psi> ?b \<star>\<^sub>D \<Psi> ?b \<star>\<^sub>D F f)"
          proof -
            have "(D.inv (\<Psi> ?b) \<star>\<^sub>D F ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<Psi> ?b \<star>\<^sub>D \<Psi> ?b \<star>\<^sub>D F f) =
                  D.inv (\<Psi> ?b) \<cdot>\<^sub>D \<Psi> ?b \<star>\<^sub>D F ?b \<cdot>\<^sub>D \<Psi> ?b \<star>\<^sub>D F f \<cdot>\<^sub>D F f"
              using assms \<Psi>_char(1-2)
                    D.interchange [of "F ?b" "\<Psi> ?b" "F f" "F f"]
                    D.interchange [of "D.inv (\<Psi> ?b)" "\<Psi> ?b" "F ?b \<star>\<^sub>D F f" "\<Psi> ?b \<star>\<^sub>D F f"]
              by simp
            also have "... = map\<^sub>0 ?b \<star>\<^sub>D \<Psi> ?b \<star>\<^sub>D F f"
              using assms \<Psi>_char(1-2) [of ?b] D.comp_arr_dom D.comp_cod_arr D.comp_inv_arr
              by (simp add: D.inv_is_inverse)
            finally show ?thesis by simp
          qed
          also have "... = (D.inv (\<Psi> ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D (\<Psi> ?b \<star>\<^sub>D \<Psi> ?b \<star>\<^sub>D F f)"
          proof -
            have "(map\<^sub>0 ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D (D.inv (\<Psi> ?b) \<star>\<^sub>D F ?b \<star>\<^sub>D F f) =
                  (D.inv (\<Psi> ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f)"
            proof -
              have "(map\<^sub>0 ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D (D.inv (\<Psi> ?b) \<star>\<^sub>D F ?b \<star>\<^sub>D F f) = D.inv (\<Psi> ?b) \<star>\<^sub>D lF f"
                using assms \<Psi>_char(1-2) lF_char(1) D.comp_arr_dom D.comp_cod_arr
                      D.interchange [of "map\<^sub>0 ?b" "D.inv (\<Psi> ?b)" "lF f" "F ?b \<star>\<^sub>D F f"]
                by simp
              also have "... = D.inv (\<Psi> ?b) \<cdot>\<^sub>D F ?b \<star>\<^sub>D F f \<cdot>\<^sub>D lF f"
                using assms \<Psi>_char(1-2) lF_char(1) D.comp_arr_dom D.comp_cod_arr
                      D.inv_in_hom
                by auto
              also have "... = (D.inv (\<Psi> ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f)"
                using assms \<Psi>_char(1-2) lF_char(1) D.inv_in_hom
                      D.interchange [of "D.inv (\<Psi> ?b)" "F ?b" "F f" "lF f"]
                by simp
              finally show ?thesis by simp
            qed
            thus ?thesis
              using assms \<Psi>_char(1-2) D.inv_in_hom D.comp_assoc by metis
          qed
          also have "... = (D.inv (\<Psi> ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f] \<cdot>\<^sub>D
                           (\<Psi> ?b \<star>\<^sub>D \<Psi> ?b \<star>\<^sub>D F f)"
            using assms \<Psi>_char(1-2) lF_char(2) D.comp_assoc by auto
          also have "... = ((D.inv (\<Psi> ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D ((\<Psi> ?b \<star>\<^sub>D \<Psi> ?b) \<star>\<^sub>D F f))
                             \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 ?b, map\<^sub>0 ?b, F f]"
            using assms \<Psi>_char(1-2) D.assoc'_naturality [of "\<Psi> ?b" "\<Psi> ?b" "F f"] D.comp_assoc
            by (simp add: \<open>trg\<^sub>D (F f) = map\<^sub>0 (trg\<^sub>C f)\<close>)
          also have "... = (\<i>\<^sub>D[map\<^sub>0 ?b] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 ?b, map\<^sub>0 ?b, F f]"
          proof -
            have "((D.inv (\<Psi> ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D ((\<Psi> ?b \<star>\<^sub>D \<Psi> ?b) \<star>\<^sub>D F f)) =
                  \<i>\<^sub>D[map\<^sub>0 ?b] \<star>\<^sub>D F f"
            proof -
              have "((D.inv (\<Psi> ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D ((\<Psi> ?b \<star>\<^sub>D \<Psi> ?b) \<star>\<^sub>D F f)) =
                    D.inv (\<Psi> ?b) \<cdot>\<^sub>D \<Psi> ?b \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 ?b] \<star>\<^sub>D F f"
                using assms 1 D.unit_in_hom D.whisker_right [of "F f"] \<Psi>_char(2-3)
                      D.invert_side_of_triangle(1)
                by (metis C.ideD(1) C.obj_trg D.seqI' map\<^sub>0_simps(1) \<Psi>_in_hom(2) preserves_ide)
              also have "... = \<i>\<^sub>D[map\<^sub>0 ?b] \<star>\<^sub>D F f"
              proof -
                have "(D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D \<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 ?b] = \<i>\<^sub>D[map\<^sub>0 ?b]"
                  by (simp add: D.comp_cod_arr D.comp_inv_arr D.inv_is_inverse \<Psi>_char(2) assms)
                thus ?thesis
                  by (simp add: D.comp_assoc)
              qed
              finally show ?thesis by blast
            qed
            thus ?thesis by simp
          qed
          also have "... = map\<^sub>0 ?b \<star>\<^sub>D \<l>\<^sub>D[F f]"
            using assms D.lunit_char [of "F f"] \<open>trg\<^sub>D (F f) = map\<^sub>0 ?b\<close> by simp
          finally show ?thesis by blast
        qed
        ultimately show ?thesis
          using assms D.L.is_faithful
          by (metis D.trg_cod D.trg_vcomp D.vseq_implies_hpar(2) lF_simps(3))
      qed
      thus ?thesis
        using assms 1 \<Psi>_char(1-2) C.ideD(1) C.obj_trg D.inverse_arrows_hcomp(1)
              D.invert_side_of_triangle(2) D.lunit_simps(1) \<Psi>_simps(2) preserves_ide
              D.iso_hcomp components_are_iso
        by metis
    qed

    lemma lunit_coherence2:
    assumes "C.ide f"
    shows "lF f = F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f)"
    proof -
      let ?b = "trg\<^sub>C f"
      have "D.par (F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (?b, f)) (lF f)"
        using assms \<Phi>_in_hom [of ?b f] lF_simps by auto
      moreover have "F ?b \<star>\<^sub>D F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (?b, f) = F ?b \<star>\<^sub>D lF f"
      proof -
        have "F ?b \<star>\<^sub>D F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (?b, f) = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D \<Phi> (?b, f))"
          using assms \<Phi>_in_hom D.whisker_left [of "F ?b" "F \<l>\<^sub>C[f]" "\<Phi> (?b, f)"]
          by (simp add: calculation)
        also have "... = F ?b \<star>\<^sub>D lF f"
        proof -
          have "(F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D \<Phi> (?b, f))
                  = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D
                    \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
          proof -
            have 1: "D.seq (F \<a>\<^sub>C[trg\<^sub>C f, trg\<^sub>C f, f])
                           (\<Phi> (trg\<^sub>C f \<star>\<^sub>C trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Phi> (trg\<^sub>C f, trg\<^sub>C f) \<star>\<^sub>D F f))"
              using assms by fastforce
            hence 2: "D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D
                         (\<Phi> (?b, ?b) \<star>\<^sub>D F f)
                        = (F ?b \<star>\<^sub>D \<Phi> (?b, f)) \<cdot>\<^sub>D \<a>\<^sub>D[F ?b, F ?b, F f]"
              using assms \<Phi>_in_hom assoc_coherence \<Phi>_components_are_iso
                    D.invert_side_of_triangle(1)
                      [of "F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D (\<Phi> (?b, ?b) \<star>\<^sub>D F f)"
                          "\<Phi> (?b, ?b \<star>\<^sub>C f)"
                          "(F ?b \<star>\<^sub>D \<Phi> (?b, f)) \<cdot>\<^sub>D \<a>\<^sub>D[F ?b, F ?b, F f]"]
                    C.ideD(1) C.ide_hcomp C.trg_hcomp C.trg_trg C.src_trg C.trg.preserves_ide
              by metis
            hence "F ?b \<star>\<^sub>D \<Phi> (?b, f)
                      = (D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D
                        (\<Phi> (?b, ?b) \<star>\<^sub>D F f)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            proof -
              have "D.seq (D.inv (\<Phi> (trg\<^sub>C f, trg\<^sub>C f \<star>\<^sub>C f)))
                          (F \<a>\<^sub>C[trg\<^sub>C f, trg\<^sub>C f, f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f \<star>\<^sub>C trg\<^sub>C f, f) \<cdot>\<^sub>D
                             (\<Phi> (trg\<^sub>C f, trg\<^sub>C f) \<star>\<^sub>D F f))"
                using assms 1 D.hseq_char by auto
              moreover have "(F (trg\<^sub>C f) \<star>\<^sub>D \<Phi> (trg\<^sub>C f, f)) \<cdot>\<^sub>D \<a>\<^sub>D[F (trg\<^sub>C f), F (trg\<^sub>C f), F f] =
                             D.inv (\<Phi> (trg\<^sub>C f, trg\<^sub>C f \<star>\<^sub>C f)) \<cdot>\<^sub>D
                               F \<a>\<^sub>C[trg\<^sub>C f, trg\<^sub>C f, f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f \<star>\<^sub>C trg\<^sub>C f, f) \<cdot>\<^sub>D
                               (\<Phi> (trg\<^sub>C f, trg\<^sub>C f) \<star>\<^sub>D F f)"
                using assms 2 by simp
              ultimately show ?thesis
                using assms
                      D.invert_side_of_triangle(2)
                        [of "D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D
                             (\<Phi> (?b, ?b) \<star>\<^sub>D F f)"
                            "F ?b \<star>\<^sub>D \<Phi> (?b, f)" "\<a>\<^sub>D[F ?b, F ?b, F f]"]
                by fastforce
            qed
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           (D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D F (\<i>\<^sub>C[?b] \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
          proof -
            have 1: "F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) = F (\<i>\<^sub>C[?b] \<star>\<^sub>C f) \<cdot>\<^sub>D D.inv (F \<a>\<^sub>C[?b, ?b, f])"
              using assms C.lunit_char(1-2) C.unit_in_hom preserves_inv by auto
            have "F \<a>\<^sub>C[?b, ?b, f] = D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D F (\<i>\<^sub>C[?b] \<star>\<^sub>C f)"
            proof -
              have "F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D D.inv (F (\<i>\<^sub>C[?b] \<star>\<^sub>C f)) =
                    D.inv (F (\<i>\<^sub>C[?b] \<star>\<^sub>C f) \<cdot>\<^sub>D D.inv (F \<a>\<^sub>C[?b, ?b, f]))"
                using assms D.iso_inv_iso
                by (simp add: C.iso_unit D.inv_comp)
              thus ?thesis
                using assms 1 D.invert_side_of_triangle D.iso_inv_iso
                by (metis C.iso_hcomp C.ideD(1) C.ide_is_iso C.iso_lunit C.iso_unit
                    C.lunit_simps(3) C.obj_trg C.src_trg C.trg.components_are_iso
                    C.unit_simps(2) D.arr_inv D.inv_inv preserves_iso)
            qed
            thus ?thesis by argo
          qed
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D (F (\<i>\<^sub>C[?b] \<star>\<^sub>C f) \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f)) \<cdot>\<^sub>D
                           (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            using D.comp_assoc by auto
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D (\<Phi> (?b, f) \<cdot>\<^sub>D (F \<i>\<^sub>C[?b] \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                           (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            using assms \<Phi>.naturality [of "(\<i>\<^sub>C[?b], f)"] FF_def C.VV.arr_char C.VV.cod_char
                  C.VV.dom_char
            by simp
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f) \<cdot>\<^sub>D
                           ((F \<i>\<^sub>C[?b] \<star>\<^sub>D F f)) \<cdot>\<^sub>D (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            using D.comp_assoc by auto
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            using assms by (simp add: D.comp_assoc D.whisker_right)
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D
                           (D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f)) \<cdot>\<^sub>D
                           (F ?b \<star>\<^sub>D lF f)"
          proof -
            have "(\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f] = F ?b \<star>\<^sub>D lF f"
              using assms lF_char by auto
            thus ?thesis
              using assms D.inv_is_inverse \<i>_in_hom \<Phi>_in_hom D.invert_side_of_triangle(2)
              by (simp add: D.comp_assoc)
          qed
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f)"
          proof -
            have "D.inv (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) =
                  D.inv (((F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f))) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f))"
              using assms D.comp_inv_arr D.comp_inv_arr' \<Phi>_simps(4)
                    D.comp_arr_dom D.comp_assoc
              by simp
            also have "... = D.inv (D.inv (\<Phi> (?b, f)) \<cdot>\<^sub>D F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f))"
            proof -
              have 1: "\<Phi> (?b, f) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) = F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f)"
                using assms \<Phi>.naturality [of "(?b, \<l>\<^sub>C[f])"] FF_def C.VV.arr_char
                      C.VV.cod_char D.VV.null_char
                by simp
              have "(F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) =
                    D.inv (\<Phi> (?b, f)) \<cdot>\<^sub>D F (?b \<star>\<^sub>C \<l>\<^sub>C[f])"
              proof -
                have "D.seq (\<Phi> (?b, f)) (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f])"
                  using assms \<Phi>_in_hom(2) [of ?b f] by auto
                moreover have "D.iso (\<Phi> (?b, f)) \<and> D.iso (\<Phi> (?b, ?b \<star>\<^sub>C f))"
                  using assms by simp
                ultimately show ?thesis
                using 1 D.invert_opposite_sides_of_square by simp
              qed
              thus ?thesis
                using D.comp_assoc by auto
            qed
            also have "... = D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D \<Phi> (?b, f)"
            proof -
              have "D.iso (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f))"
                using assms D.isos_compose C.VV.arr_char C.iso_lunit by simp
              moreover have "D.iso (D.inv (\<Phi> (?b, f)))"
                using assms D.iso_inv_iso by simp
              moreover have "D.seq (D.inv (\<Phi> (?b, f))) (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f))"
                using assms C.VV.arr_char by simp
              ultimately show ?thesis
                using assms D.inv_comp by simp
            qed
            also have "... = D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f)"
            proof -
              have "D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f)) =
                    D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]))"
                using assms D.isos_compose C.VV.arr_char C.iso_lunit D.inv_comp by simp
              thus ?thesis using D.comp_assoc by simp
            qed
            finally have "D.inv (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f])
                            = D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f)"
              by blast
            thus ?thesis by argo
          qed
          also have "... = ((F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f])) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f)"
            using D.comp_assoc by simp
          also have "... = F ?b \<star>\<^sub>D lF f"
            using assms D.comp_arr_inv' [of "F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]"] D.comp_cod_arr by simp
          finally show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis
        using assms D.L.is_faithful
        by (metis D.in_homI lF_char(2-3) lF_simps(4-5))
    qed

    lemma lunit_coherence:
    assumes "C.ide f"
    shows "\<l>\<^sub>D[F f] = F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)"
    proof -
      have 1: "\<l>\<^sub>D[F f] \<cdot>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f) = F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f)"
        using assms lunit_coherence1 lunit_coherence2 by simp
      have "\<l>\<^sub>D[F f] = (F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f)) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)"
      proof -
        have "D.seq (F \<l>\<^sub>C[f]) (\<Phi> (trg\<^sub>C f, f))"
          using assms \<Phi>_in_hom [of "trg\<^sub>C f" f] C.unit_in_vhom by auto
        moreover have "D.iso (D.inv (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f))"
          using assms \<Psi>_char D.iso_inv_iso \<Psi>_char(1-2)
          by (simp add: preserves_hseq)
        ultimately show ?thesis
          using assms 1 \<Psi>_char(2) D.iso_inv_iso \<Phi>_in_hom D.inv_inv
                D.invert_side_of_triangle(2)
                  [of "F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f)" "\<l>\<^sub>D[F f]" "D.inv (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)"]
          by auto
      qed
      thus ?thesis
        using assms \<Psi>_char(1) D.comp_assoc by auto
    qed

    text \<open>
      We postpone proving the dual version of this result until after we have developed
      the notion of the ``op bicategory'' in the next section.
    \<close>

  end

  subsection "Pseudofunctors and Opposite Bicategories"

  text \<open>
    There are three duals to a bicategory:
    \begin{enumerate}
      \item ``op'': sources and targets are exchanged;
      \item ``co'': domains and codomains are exchanged;
      \item ``co-op'': both sources and targets and domains and codomains are exchanged.
    \end{enumerate}
    Here we consider the "op" case.
  \<close>

  locale op_bicategory =
    B: bicategory V H\<^sub>B \<a>\<^sub>B \<i> src\<^sub>B trg\<^sub>B
  for V :: "'a comp"               (infixr "\<cdot>" 55)
  and H\<^sub>B :: "'a comp"              (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>\<^sub>B[_, _, _]")
  and \<i> :: "'a \<Rightarrow> 'a"               ("\<i>[_]")
  and src\<^sub>B :: "'a \<Rightarrow> 'a"
  and trg\<^sub>B :: "'a \<Rightarrow> 'a"
  begin

    abbreviation H  (infixr "\<star>" 53)
    where "H f g \<equiv> H\<^sub>B g f"

    abbreviation src
    where "src \<equiv> trg\<^sub>B"

    abbreviation trg
    where "trg \<equiv> src\<^sub>B"

    interpretation horizontal_homs V src trg
      by (unfold_locales, auto)

    interpretation H: "functor" VV.comp V \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close>
      using VV.arr_char
      apply unfold_locales
          apply (metis (no_types, lifting) B.hseqE B.hseq_char')
         apply auto[3]
      using VV.comp_char VV.seq_char VV.arr_char B.VxV.comp_char B.interchange
      by (metis (no_types, lifting) B.VxV.seqE fst_conv snd_conv)

    interpretation horizontal_composition V H src trg
      by (unfold_locales, auto)

    abbreviation UP
    where "UP \<mu>\<nu>\<tau> \<equiv> if B.VVV.arr \<mu>\<nu>\<tau> then
                       (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)
                    else VVV.null"

    abbreviation DN
    where "DN \<mu>\<nu>\<tau> \<equiv> if VVV.arr \<mu>\<nu>\<tau> then
                         (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)
                      else B.VVV.null"

    lemma VVV_arr_char:
    shows "VVV.arr \<mu>\<nu>\<tau> \<longleftrightarrow> B.VVV.arr (DN \<mu>\<nu>\<tau>)"
      using VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char B.VVV.not_arr_null
      by auto

    lemma VVV_ide_char:
    shows "VVV.ide \<mu>\<nu>\<tau> \<longleftrightarrow> B.VVV.ide (DN \<mu>\<nu>\<tau>)"
    proof -
      have "VVV.ide \<mu>\<nu>\<tau> \<longleftrightarrow> VVV.arr \<mu>\<nu>\<tau> \<and> B.VxVxV.ide \<mu>\<nu>\<tau>"
        using VVV.ide_char by simp
      also have "... \<longleftrightarrow> B.VVV.arr (DN \<mu>\<nu>\<tau>) \<and> B.VxVxV.ide (DN \<mu>\<nu>\<tau>)"
        using VVV_arr_char B.VxVxV.ide_char by auto
      also have "... \<longleftrightarrow> B.VVV.ide (DN \<mu>\<nu>\<tau>)"
        using B.VVV.ide_char [of "DN \<mu>\<nu>\<tau>"] by blast
      finally show ?thesis by fast
    qed

    lemma VVV_dom_char:
    shows "VVV.dom \<mu>\<nu>\<tau> = UP (B.VVV.dom (DN \<mu>\<nu>\<tau>))"
    proof (cases "VVV.arr \<mu>\<nu>\<tau>")
      show "\<not> VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> VVV.dom \<mu>\<nu>\<tau> = UP (B.VVV.dom (DN \<mu>\<nu>\<tau>))"
        using VVV.dom_def VVV.has_domain_iff_arr VVV_arr_char B.VVV.dom_null
        by auto
      show "VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> VVV.dom \<mu>\<nu>\<tau> = UP (B.VVV.dom (DN \<mu>\<nu>\<tau>))"
      proof -
        assume \<mu>\<nu>\<tau>: "VVV.arr \<mu>\<nu>\<tau>"
        have "VVV.dom \<mu>\<nu>\<tau> =
              (B.dom (fst \<mu>\<nu>\<tau>), B.dom (fst (snd \<mu>\<nu>\<tau>)), B.dom (snd (snd \<mu>\<nu>\<tau>)))"
          using \<mu>\<nu>\<tau> VVV.dom_char VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char
          by simp
        also have "... = UP (B.dom (snd (snd \<mu>\<nu>\<tau>)), B.dom (fst (snd \<mu>\<nu>\<tau>)), B.dom (fst \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> VVV_arr_char B.VV.arr_char B.VVV.arr_char B.arr_dom_iff_arr src_dom
                trg_dom
          apply simp
          by (metis (no_types, lifting) src_dom trg_dom VV.arrE VVV.arrE)
        also have "... = UP (B.VVV.dom (DN \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> B.VVV.dom_char B.VVV.arr_char B.VV.arr_char VVV.arr_char VV.arr_char
          by simp
        finally show ?thesis by blast
      qed
    qed

    lemma VVV_cod_char:
    shows "VVV.cod \<mu>\<nu>\<tau> = UP (B.VVV.cod (DN \<mu>\<nu>\<tau>))"
    proof (cases "VVV.arr \<mu>\<nu>\<tau>")
      show "\<not> VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> VVV.cod \<mu>\<nu>\<tau> = UP (B.VVV.cod (DN \<mu>\<nu>\<tau>))"
        using VVV.cod_def VVV.has_codomain_iff_arr VVV_arr_char B.VVV.cod_null
        by auto
      show "VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> VVV.cod \<mu>\<nu>\<tau> = UP (B.VVV.cod (DN \<mu>\<nu>\<tau>))"
      proof -
        assume \<mu>\<nu>\<tau>: "VVV.arr \<mu>\<nu>\<tau>"
        have "VVV.cod \<mu>\<nu>\<tau> = (B.cod (fst \<mu>\<nu>\<tau>), B.cod (fst (snd \<mu>\<nu>\<tau>)), B.cod (snd (snd \<mu>\<nu>\<tau>)))"
          using \<mu>\<nu>\<tau> VVV.cod_char VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char
          by simp
        also have "... = UP (B.cod (snd (snd \<mu>\<nu>\<tau>)), B.cod (fst (snd \<mu>\<nu>\<tau>)), B.cod (fst \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> VVV_arr_char B.VV.arr_char B.VVV.arr_char
          apply simp
          by (metis (no_types, lifting) B.arr_cod_iff_arr src_cod trg_cod VV.arrE VVV.arrE)
        also have "... = UP (B.VVV.cod (DN \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> B.VVV.cod_char B.VVV.arr_char B.VV.arr_char VVV.arr_char VV.arr_char
          by simp
        finally show ?thesis by blast
      qed
    qed

    lemma HoHV_char:
    shows "HoHV \<mu>\<nu>\<tau> = B.HoVH (DN \<mu>\<nu>\<tau>)"
     using HoHV_def B.HoVH_def VVV_arr_char by simp

    lemma HoVH_char:
    shows "HoVH \<mu>\<nu>\<tau> = B.HoHV (DN \<mu>\<nu>\<tau>)"
      using HoVH_def B.HoHV_def VVV_arr_char by simp

    definition \<a>   ("\<a>[_, _, _]")
    where "\<a>[\<mu>, \<nu>, \<tau>] \<equiv> B.\<alpha>' (DN (\<mu>, \<nu>, \<tau>))"

    interpretation natural_isomorphism VVV.comp \<open>(\<cdot>)\<close> HoHV HoVH
                     \<open>\<lambda>\<mu>\<nu>\<tau>. \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]\<close>
    proof
      fix \<mu>\<nu>\<tau>
      show "\<not> VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)] = B.null"
        using VVV.arr_char B.VVV.arr_char \<a>_def B.\<alpha>'.is_extensional by auto
      assume \<mu>\<nu>\<tau>: "VVV.arr \<mu>\<nu>\<tau>"
      show "B.dom \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)] = HoHV (VVV.dom \<mu>\<nu>\<tau>)"
      proof -
        have "HoHV (VVV.dom \<mu>\<nu>\<tau>) =
              (B.dom (fst \<mu>\<nu>\<tau>) \<star> B.dom (fst (snd \<mu>\<nu>\<tau>))) \<star> B.dom (snd (snd \<mu>\<nu>\<tau>))"
          unfolding HoHV_def B.VxVxV.dom_char
          using \<mu>\<nu>\<tau> VVV.arr_char VVV.dom_char VV.arr_char by simp
        also have "... = B.HoVH (B.VVV.dom (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>))"
          unfolding B.HoVH_def B.VxVxV.dom_char
          using \<mu>\<nu>\<tau> B.VVV.dom_char B.VxVxV.dom_char B.VVV.arr_char B.VV.arr_char
          apply simp
          by (metis (no_types, lifting) VV.arr_char VVV.arrE)
        also have "... = B.dom (B.\<alpha>' (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> B.\<alpha>'.preserves_dom VVV_arr_char by presburger
        also have "... = B.dom \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
          using \<mu>\<nu>\<tau> \<a>_def by simp
        finally show ?thesis by simp
      qed
      show "B.cod \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)] = HoVH (VVV.cod \<mu>\<nu>\<tau>)"
      proof -
        have "HoVH (VVV.cod \<mu>\<nu>\<tau>) =
              B.cod (fst \<mu>\<nu>\<tau>) \<star> B.cod (fst (snd \<mu>\<nu>\<tau>)) \<star> B.cod (snd (snd \<mu>\<nu>\<tau>))"
          unfolding HoVH_def B.VxVxV.cod_char
          using \<mu>\<nu>\<tau> VVV.arr_char VVV.cod_char VV.arr_char by simp
        also have "... = B.HoHV (B.VVV.cod (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>))"
          unfolding B.HoHV_def B.VxVxV.cod_char
          using \<mu>\<nu>\<tau> B.VVV.cod_char B.VxVxV.cod_char B.VVV.arr_char B.VV.arr_char
          apply simp
          by (metis (no_types, lifting) VV.arr_char VVV.arrE)
        also have "... = B.cod (B.\<alpha>' (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> B.\<alpha>'.preserves_cod VVV_arr_char by presburger
        also have "... = B.cod \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
          using \<mu>\<nu>\<tau> \<a>_def by simp
        finally show ?thesis by simp
      qed
      show "HoVH \<mu>\<nu>\<tau> \<cdot>
              \<a>[fst (VVV.dom \<mu>\<nu>\<tau>), fst (snd (VVV.dom \<mu>\<nu>\<tau>)), snd (snd (VVV.dom \<mu>\<nu>\<tau>))] =
            \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
      proof -
        have "HoVH \<mu>\<nu>\<tau> \<cdot>
                \<a>[fst (VVV.dom \<mu>\<nu>\<tau>), fst (snd (VVV.dom \<mu>\<nu>\<tau>)), snd (snd (VVV.dom \<mu>\<nu>\<tau>))] =
              HoVH \<mu>\<nu>\<tau> \<cdot> B.\<alpha>' (B.VVV.dom (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>))"
          unfolding \<a>_def
          using \<mu>\<nu>\<tau> VVV.arr_char VV.arr_char VVV.dom_char B.VVV.arr_char B.VVV.dom_char
          by auto
        also have "... = B.\<alpha>' (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)"
          using B.\<alpha>'.is_natural_1 VVV_arr_char \<mu>\<nu>\<tau> HoVH_char by presburger
        also have "... = \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
          using \<mu>\<nu>\<tau> \<a>_def by simp
        finally show ?thesis by blast
      qed
      show "\<a>[fst (VVV.cod \<mu>\<nu>\<tau>), fst (snd (VVV.cod \<mu>\<nu>\<tau>)), snd (snd (VVV.cod \<mu>\<nu>\<tau>))] \<cdot>
              HoHV \<mu>\<nu>\<tau> =
            \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))"
      proof -
        have "\<a>[fst (VVV.cod \<mu>\<nu>\<tau>), fst (snd (VVV.cod \<mu>\<nu>\<tau>)), snd (snd (VVV.cod \<mu>\<nu>\<tau>))] \<cdot>
                HoHV \<mu>\<nu>\<tau> =
              B.\<alpha>' (B.VVV.cod (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)) \<cdot> HoHV \<mu>\<nu>\<tau>"
          unfolding \<a>_def
          using \<mu>\<nu>\<tau> VVV.arr_char VV.arr_char VVV.cod_char B.VVV.arr_char B.VVV.cod_char
          by auto
        also have "... = B.\<alpha>' (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)"
          using B.\<alpha>'.is_natural_2 VVV_arr_char \<mu>\<nu>\<tau> HoHV_char by presburger
        also have "... = \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
          using \<mu>\<nu>\<tau> \<a>_def by simp
        finally show ?thesis by blast
      qed
      next
      fix \<mu>\<nu>\<tau>
      assume \<mu>\<nu>\<tau>: "VVV.ide \<mu>\<nu>\<tau>"
      show "B.iso \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
      proof -
        have "B.VVV.ide (DN \<mu>\<nu>\<tau>)"
          using \<mu>\<nu>\<tau> VVV_ide_char by blast
        thus ?thesis
          using \<mu>\<nu>\<tau> \<a>_def B.\<alpha>'.components_are_iso by auto
      qed
    qed

    sublocale bicategory V H \<a> \<i> src trg
    proof
      show "\<And>a. obj a \<Longrightarrow> \<guillemotleft>\<i> a : H a a \<rightarrow>\<^sub>B a\<guillemotright>"
        using obj_def objE B.obj_def B.objE B.unit_in_hom by meson
      show "\<And>a. obj a \<Longrightarrow> B.iso (\<i> a)"
        using obj_def objE B.obj_def B.objE B.iso_unit by meson
      show "\<And>f g h k. \<lbrakk> B.ide f; B.ide g; B.ide h; B.ide k;
                        src f = trg g; src g = trg h; src h = trg k \<rbrakk> \<Longrightarrow>
              (f \<star> \<a>[g, h, k]) \<cdot> \<a>[f, g \<star> h, k] \<cdot> (\<a>[f, g, h] \<star> k) = \<a>[f, g, h \<star> k] \<cdot> \<a>[f \<star> g, h, k]"
        unfolding \<a>_def
        using B.\<a>'_def B.comp_assoc B.pentagon' VVV.arr_char VV.arr_char by simp
    qed

    proposition is_bicategory:
    shows "bicategory V H \<a> \<i> src trg"
      ..

    lemma assoc_ide_simp:
    assumes "B.ide f" and "B.ide g" and "B.ide h"
    and "src f = trg g" and "src g = trg h"
    shows "\<a>[f, g, h] = B.\<a>' h g f"
      using assms \<a>_def B.\<a>'_def by fastforce

    lemma lunit_ide_simp:
    assumes "B.ide f"
    shows "lunit f = B.runit f"
    proof (intro B.runit_eqI)
      show "B.ide f" by fact
      show "\<guillemotleft>lunit f : H (trg f) f \<rightarrow>\<^sub>B f\<guillemotright>"
        using assms by simp
      show "trg f \<star> lunit f = (\<i>[trg f] \<star> f) \<cdot> \<a>\<^sub>B[f, trg f, trg f]"
      proof -
        have "trg f \<star> lunit f = (\<i>[trg f] \<star> f) \<cdot> \<a>' (trg f) (trg f) f"
          using assms lunit_char(1-2) [of f] by simp
        moreover have "\<a>' (trg f) (trg f) f = \<a>\<^sub>B[f, trg f, trg f]"
        proof (unfold \<a>'_def)
          have 1: "VVV.ide (trg f, trg f, f)"
            using assms VVV.ide_char VVV.arr_char VV.arr_char by simp
          have "\<alpha>' (trg f, trg f, f) = B.inv \<a>[trg f, trg f, f]"
            using 1 B.\<alpha>'.inverts_components by simp
          also have "... = B.inv (B.\<alpha>' (f, trg f, trg f))"
            unfolding \<a>_def using 1 by simp
          also have "... = \<a>\<^sub>B[f, trg f, trg f]"
            using 1 B.VVV.ide_char B.VVV.arr_char B.VV.arr_char VVV.ide_char
                  VVV.arr_char VV.arr_char B.\<alpha>'.inverts_components B.\<alpha>_def
            by force
          finally show "\<alpha>' (trg f, trg f, f) = \<a>\<^sub>B[f, trg f, trg f]"
            by blast
        qed
        ultimately show ?thesis by simp
      qed
    qed

    lemma runit_ide_simp:
    assumes "B.ide f"
    shows "runit f = B.lunit f"
      using assms runit_char(1-2) [of f] B.\<a>'_def assoc_ide_simp
      apply (intro B.lunit_eqI)
      by simp_all

  end

  context pseudofunctor
  begin

    interpretation C': op_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C ..
    interpretation D': op_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D ..

    notation C'.H  (infixr "\<star>\<^sub>C\<^sup>o\<^sup>p" 53)
    notation D'.H  (infixr "\<star>\<^sub>D\<^sup>o\<^sup>p" 53)

    interpretation F': weak_arrow_of_homs V\<^sub>C C'.src C'.trg V\<^sub>D D'.src D'.trg F
      apply unfold_locales
      using weakly_preserves_src weakly_preserves_trg by simp_all
    interpretation H\<^sub>D'oFF: composite_functor C'.VV.comp D'.VV.comp V\<^sub>D F'.FF
                             \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>D\<^sup>o\<^sup>p snd \<mu>\<nu>\<close> ..
    interpretation FoH\<^sub>C': composite_functor C'.VV.comp V\<^sub>C V\<^sub>D
                             \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>C\<^sup>o\<^sup>p snd \<mu>\<nu>\<close> F
      ..
    interpretation \<Phi>': natural_isomorphism C'.VV.comp V\<^sub>D H\<^sub>D'oFF.map FoH\<^sub>C'.map
                                           \<open>\<lambda>f. \<Phi> (snd f, fst f)\<close>
      using C.VV.arr_char C'.VV.arr_char C'.VV.ide_char C.VV.ide_char FF_def F'.FF_def
            \<Phi>.is_extensional \<Phi>.is_natural_1 \<Phi>.is_natural_2
      apply unfold_locales by auto
    interpretation F': pseudofunctor V\<^sub>C C'.H C'.\<a> \<i>\<^sub>C C'.src C'.trg
                                     V\<^sub>D D'.H D'.\<a> \<i>\<^sub>D D'.src D'.trg
                                     F \<open>\<lambda>f. \<Phi> (snd f, fst f)\<close>
    proof
      fix f g h
      assume f: "C.ide f" and g: "C.ide g" and h: "C.ide h"
      and fg: "C'.src f = C'.trg g" and gh: "C'.src g = C'.trg h"
      have "F (C'.\<a> f g h) \<cdot>\<^sub>D \<Phi> (h, f \<star>\<^sub>C\<^sup>o\<^sup>p g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D\<^sup>o\<^sup>p F h) =
            \<Phi> (g \<star>\<^sub>C\<^sup>o\<^sup>p h, f) \<cdot>\<^sub>D (F f \<star>\<^sub>D\<^sup>o\<^sup>p \<Phi> (h, g)) \<cdot>\<^sub>D D'.\<a> (F f) (F g) (F h)"
      proof -
        have "F (\<a>\<^sub>C h g f) \<cdot>\<^sub>D \<Phi> (g \<star>\<^sub>C\<^sup>o\<^sup>p h, f) \<cdot>\<^sub>D (F f \<star>\<^sub>D\<^sup>o\<^sup>p \<Phi> (h, g)) =
                       (\<Phi> (h, f \<star>\<^sub>C\<^sup>o\<^sup>p g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D\<^sup>o\<^sup>p F h)) \<cdot>\<^sub>D \<a>\<^sub>D (F h) (F g) (F f)"
          using f g h fg gh assoc_coherence D.comp_assoc by simp
        moreover have "D.seq (F \<a>\<^sub>C[h, g, f]) (\<Phi> (g \<star>\<^sub>C\<^sup>o\<^sup>p h, f) \<cdot>\<^sub>D (F f \<star>\<^sub>D\<^sup>o\<^sup>p \<Phi> (h, g)))"
        proof -
          have "\<guillemotleft>F (\<a>\<^sub>C h g f) : F ((h \<star>\<^sub>C g) \<star>\<^sub>C f) \<Rightarrow>\<^sub>D F (h \<star>\<^sub>C g \<star>\<^sub>C f)\<guillemotright>"
            using f g h fg gh preserves_hom C.assoc_in_hom(2) by simp
          moreover have "\<guillemotleft>\<Phi> (g \<star>\<^sub>C\<^sup>o\<^sup>p h, f) : F (h \<star>\<^sub>C g) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F ((h \<star>\<^sub>C g) \<star>\<^sub>C f)\<guillemotright>"
            using f g h fg gh by auto
          moreover have "\<guillemotleft>F f \<star>\<^sub>D\<^sup>o\<^sup>p \<Phi> (h, g) : (F h \<star>\<^sub>D F g) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F (h \<star>\<^sub>C g) \<star>\<^sub>D F f\<guillemotright>"
            using f g h fg gh C.VV.in_hom_char FF_def C.VV.arr_char by auto
          ultimately show ?thesis by auto
        qed
        moreover have "D.iso (F \<a>\<^sub>C[h, g, f])"
          using f g h fg gh by simp
        moreover have "D.iso \<a>\<^sub>D[F h, F g, F f]"
          using f g h fg gh by simp
        moreover have "D.inv (F \<a>\<^sub>C[h, g, f]) = F (C'.\<a> f g h)"
          using f g h fg gh
          by (simp add: C'.assoc_ide_simp preserves_inv)
        moreover have "D.inv \<a>\<^sub>D[F h, F g, F f] = D'.\<a> (F f) (F g) (F h)"
          using f g h fg gh
          by (simp add: D'.assoc_ide_simp)
        ultimately show ?thesis
          using D.invert_opposite_sides_of_square
                  [of "F (\<a>\<^sub>C h g f)" "\<Phi> (g \<star>\<^sub>C\<^sup>o\<^sup>p h, f) \<cdot>\<^sub>D (F f \<star>\<^sub>D\<^sup>o\<^sup>p \<Phi> (h, g))"
                      "\<Phi> (h, f \<star>\<^sub>C\<^sup>o\<^sup>p g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D\<^sup>o\<^sup>p F h)" "\<a>\<^sub>D (F h) (F g) (F f)"]
                D.comp_assoc
          by simp
      qed
      thus "F (C'.\<a> f g h) \<cdot>\<^sub>D \<Phi> (snd (f \<star>\<^sub>C\<^sup>o\<^sup>p g, h), fst (f \<star>\<^sub>C\<^sup>o\<^sup>p g, h)) \<cdot>\<^sub>D
              (\<Phi> (snd (f, g), fst (f, g)) \<star>\<^sub>D\<^sup>o\<^sup>p F h) =
            \<Phi> (snd (f, g \<star>\<^sub>C\<^sup>o\<^sup>p h), fst (f, g \<star>\<^sub>C\<^sup>o\<^sup>p h)) \<cdot>\<^sub>D (F f \<star>\<^sub>D\<^sup>o\<^sup>p \<Phi> (snd (g, h), fst (g, h))) \<cdot>\<^sub>D
              D'.\<a> (F f) (F g) (F h)"
        using f g h fg gh by simp
    qed

    lemma induces_pseudofunctor_between_opposites:
    shows "pseudofunctor (\<cdot>\<^sub>C) (\<star>\<^sub>C\<^sup>o\<^sup>p) C'.\<a> \<i>\<^sub>C C'.src C'.trg
                         (\<cdot>\<^sub>D) (\<star>\<^sub>D\<^sup>o\<^sup>p) D'.\<a> \<i>\<^sub>D D'.src D'.trg
                         F (\<lambda>f. \<Phi> (snd f, fst f))"
      ..

    text \<open>
      It is now easy to dualize the coherence condition for \<open>F\<close> with respect to
      left unitors to obtain the corresponding condition for right unitors.
    \<close>

    lemma runit_coherence:
    assumes "C.ide f"
    shows "\<r>\<^sub>D[F f] = F \<r>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f))"
    proof -
      have "C'.lunit f = \<r>\<^sub>C[f]"
        using assms C'.lunit_ide_simp by simp
      moreover have "D'.lunit (F f) = \<r>\<^sub>D[F f]"
        using assms D'.lunit_ide_simp by simp
      moreover have "F'.\<Psi> (src\<^sub>C f) = \<Psi> (src\<^sub>C f)"
        using assms F'.\<Psi>_char F'.preserves_trg
        by (intro \<Psi>_eqI, auto)
      moreover have "D'.lunit (F f) =
                     F (C'.lunit f) \<cdot>\<^sub>D \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D F'.\<Psi> (src\<^sub>C f))"
        using assms F'.lunit_coherence by simp
      ultimately show ?thesis by simp
    qed

  end

  subsection "Preservation Properties"

  text \<open>
    The objective of this section is to establish explicit formulas for the result
    of applying a pseudofunctor to expressions of various forms.
  \<close>

  context pseudofunctor
  begin

    lemma preserves_lunit:
    assumes "C.ide f"
    shows "F \<l>\<^sub>C[f] = \<l>\<^sub>D[F f] \<cdot>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f))"
    and "F \<l>\<^sub>C\<^sup>-\<^sup>1[f] = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f]"
    proof -
      have "\<l>\<^sub>D[F f] \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)) = F \<l>\<^sub>C[f]"
      proof -
        have "D.arr \<l>\<^sub>D[F f]"
          using assms by simp
        moreover have "\<l>\<^sub>D[F f] = F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)"
          using assms lunit_coherence by simp
        moreover have "D.iso (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f))"
          using assms \<Psi>_char D.iso_hcomp FF_def
          by (intro D.isos_compose D.seqI, auto)
        ultimately show ?thesis
          using assms
                D.invert_side_of_triangle(2)
                  [of "\<l>\<^sub>D[F f]" "F \<l>\<^sub>C[f]" "\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)"]
          by metis
      qed
      moreover have "D.inv (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)) =
                      (D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f))"
        using assms C.VV.arr_char \<Psi>_char FF_def D.inv_comp by simp
      ultimately show "F \<l>\<^sub>C[f] =
                       \<l>\<^sub>D[F f] \<cdot>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f))"
        by simp
      hence "F \<l>\<^sub>C\<^sup>-\<^sup>1[f] =
             D.inv (\<l>\<^sub>D[F f] \<cdot>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f)))"
        using assms preserves_inv by simp
      also have "... = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f]"
      proof -
        have "\<guillemotleft>\<l>\<^sub>D[F f] : map\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright> \<and> D.iso \<l>\<^sub>D[F f]"
          using assms by simp
        moreover have "\<guillemotleft>D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f :
                          F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F f\<guillemotright> \<and>
                       D.iso (D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f)"
          using assms \<Psi>_char [of "trg\<^sub>C f"] D.iso_inv_iso
          by (intro conjI D.hcomp_in_vhom, auto)
        moreover have
          "\<guillemotleft>D.inv (\<Phi> (trg\<^sub>C f, f)) : F (trg\<^sub>C f \<star>\<^sub>C f) \<Rightarrow>\<^sub>D F (trg\<^sub>C f) \<star>\<^sub>D F f\<guillemotright> \<and>
           D.iso (D.inv (\<Phi> (trg\<^sub>C f, f)))"
          using assms \<Phi>_in_hom D.iso_inv_iso by simp
        moreover have "D.inv (D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f) = \<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f"
          using assms \<Psi>_char [of "trg\<^sub>C f"] D.iso_inv_iso by simp
        ultimately show ?thesis
          using assms D.iso_inv_iso D.comp_assoc D.iso_hcomp D.isos_compose
          apply (elim conjE D.in_homE)
          by (auto simp add: D.inv_comp)
      qed
      finally show "F \<l>\<^sub>C\<^sup>-\<^sup>1[f] = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f]"
        by simp
    qed

    lemma preserves_runit:
    assumes "C.ide f"
    shows "F \<r>\<^sub>C[f] = \<r>\<^sub>D[F f] \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
    and "F \<r>\<^sub>C\<^sup>-\<^sup>1[f] = \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F f]"
    proof -
      have "F \<r>\<^sub>C[f] = \<r>\<^sub>D[F f] \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f)))"
      proof -
        have "\<r>\<^sub>D[F f] = F \<r>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f))"
          using assms runit_coherence [of f] by simp
        moreover have "D.iso (\<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f)))"
          using assms \<Psi>_char D.iso_hcomp FF_def
          apply (intro D.isos_compose D.seqI) by auto
        moreover have "D.arr \<r>\<^sub>D[F f]"
          using assms by simp
        ultimately show ?thesis
          using assms D.invert_side_of_triangle(2)
                  [of "\<r>\<^sub>D[F f]" "F \<r>\<^sub>C[f]" "\<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f))"]
          by metis
      qed
      moreover have "D.inv (\<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f))) =
                      (F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
        using assms C.VV.arr_char \<Psi>_char D.iso_hcomp FF_def D.inv_comp by simp
      ultimately show "F \<r>\<^sub>C[f] =
                       \<r>\<^sub>D[F f] \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
        by simp
      hence "F \<r>\<^sub>C\<^sup>-\<^sup>1[f] =
             D.inv (\<r>\<^sub>D[F f] \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f)))"
        using assms preserves_inv C.iso_runit by simp
      also have "... = \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F f]"
      proof -
        have "\<guillemotleft>\<r>\<^sub>D[F f] : F f \<star>\<^sub>D map\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D F f\<guillemotright> \<and> D.iso \<r>\<^sub>D[F f]"
          using assms D.iso_runit by simp
        moreover have "\<guillemotleft>F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f)) :
                          F f \<star>\<^sub>D F (src\<^sub>C f) \<Rightarrow>\<^sub>D F f \<star>\<^sub>D map\<^sub>0 (src\<^sub>C f)\<guillemotright> \<and>
                       D.iso (F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f)))"
          using assms \<Psi>_char [of "src\<^sub>C f"] D.iso_inv_iso
          apply (intro conjI D.hcomp_in_vhom) by auto
        moreover have
          "\<guillemotleft>D.inv (\<Phi> (f, src\<^sub>C f)) : F (f \<star>\<^sub>C src\<^sub>C f) \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F (src\<^sub>C f)\<guillemotright> \<and>
           D.iso (D.inv (\<Phi> (f, src\<^sub>C f)))"
          using assms \<Phi>_in_hom D.iso_inv_iso by simp
        moreover have "D.inv (F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))) = F f \<star>\<^sub>D \<Psi> (src\<^sub>C f)"
          using assms \<Psi>_char [of "src\<^sub>C f"] D.iso_inv_iso by simp
        ultimately show ?thesis
          using assms D.inv_comp D.iso_inv_iso D.comp_assoc D.isos_compose
          apply (elim conjE D.in_homE)
          by (auto simp add: D.inv_comp)
      qed
      finally show "F \<r>\<^sub>C\<^sup>-\<^sup>1[f] = \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F f]"
        by simp
    qed

    lemma preserves_assoc:
    assumes "C.ide f" and "C.ide g" and "C.ide h"
    and "src\<^sub>C f = trg\<^sub>C g" and "src\<^sub>C g = trg\<^sub>C h"
    shows "F \<a>\<^sub>C[f, g, h] = \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h] \<cdot>\<^sub>D
                            (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
    and "F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, h] = \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F h] \<cdot>\<^sub>D
                            (F f \<star>\<^sub>D D.inv (\<Phi> (g, h))) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C h))"
    proof -
      have "F \<a>\<^sub>C[f, g, h] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) =
            \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h]"
        using assms assoc_coherence [of f g h] by simp
      moreover have "D.seq (\<Phi> (f, g \<star>\<^sub>C h)) ((F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h])"
        using assms C.VV.arr_char FF_def by auto
      moreover have 1: "D.iso (\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h))"
        using assms C.VV.arr_char FF_def by auto
      moreover have "D.inv (\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h)) =
                    (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
        using assms 1 C.VV.arr_char FF_def D.inv_comp by simp
      ultimately show 1: "F \<a>\<^sub>C[f, g, h] =
                          \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h] \<cdot>\<^sub>D
                            (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
        using D.invert_side_of_triangle(2)
                [of "\<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h]"
                    "F \<a>\<^sub>C[f, g, h]" "\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h)"]
              D.comp_assoc
        by simp
      hence "F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, h] =
             D.inv (\<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h] \<cdot>\<^sub>D
               (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h)))"
        using assms preserves_inv by simp
      also have "... = \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F h] \<cdot>\<^sub>D
                         (F f \<star>\<^sub>D D.inv (\<Phi> (g, h))) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C h))"
      proof -
        have "\<guillemotleft>\<Phi> (f, g \<star>\<^sub>C h) : F f \<star>\<^sub>D F (g \<star>\<^sub>C h) \<Rightarrow>\<^sub>D F (f \<star>\<^sub>C g \<star>\<^sub>C h)\<guillemotright> \<and> D.iso (\<Phi> (f, g \<star>\<^sub>C h))"
          using assms by auto
        moreover have "\<guillemotleft>F f \<star>\<^sub>D \<Phi> (g, h) : F f \<star>\<^sub>D F g \<star>\<^sub>D F h \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F (g \<star>\<^sub>C h)\<guillemotright> \<and>
                       D.iso (F f \<star>\<^sub>D \<Phi> (g, h))"
          using assms
          by (intro conjI D.hcomp_in_vhom, auto)
        moreover have "\<guillemotleft>\<a>\<^sub>D[F f, F g, F h] : (F f \<star>\<^sub>D F g) \<star>\<^sub>D F h \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F g \<star>\<^sub>D F h\<guillemotright> \<and>
                       D.iso \<a>\<^sub>D[F f, F g, F h]"
          using assms by auto
        moreover have
          "\<guillemotleft>D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h : F (f \<star>\<^sub>C g) \<star>\<^sub>D F h \<Rightarrow>\<^sub>D (F f \<star>\<^sub>D F g) \<star>\<^sub>D F h\<guillemotright> \<and>
           D.iso (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h)"
          using assms D.iso_inv_iso by auto
        moreover have
          "\<guillemotleft>D.inv (\<Phi> (f \<star>\<^sub>C g, h)) : F ((f \<star>\<^sub>C g) \<star>\<^sub>C h) \<Rightarrow>\<^sub>D F (f \<star>\<^sub>C g) \<star>\<^sub>D F h\<guillemotright> \<and>
           D.iso (D.inv (\<Phi> (f \<star>\<^sub>C g, h)))"
          using assms D.iso_inv_iso by auto
        ultimately show ?thesis
          using assms D.isos_compose D.comp_assoc D.iso_inv_iso
          apply (elim conjE D.in_homE)
          by (auto simp add: D.inv_comp)
      qed
      finally show "F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, h] =
                    \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F h] \<cdot>\<^sub>D
                      (F f \<star>\<^sub>D D.inv (\<Phi> (g, h))) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C h))"
        by simp
    qed

    lemma preserves_hcomp:
    assumes "C.hseq \<mu> \<nu>"
    shows "F (\<mu> \<star>\<^sub>C \<nu>) =
           \<Phi> (C.cod \<mu>, C.cod \<nu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D F \<nu>) \<cdot>\<^sub>D D.inv (\<Phi> (C.dom \<mu>, C.dom \<nu>))"
    proof -
      have "F (\<mu> \<star>\<^sub>C \<nu>) \<cdot>\<^sub>D \<Phi> (C.dom \<mu>, C.dom \<nu>) = \<Phi> (C.cod \<mu>, C.cod \<nu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D F \<nu>)"
        using assms \<Phi>.naturality C.VV.arr_char C.VV.cod_char FF_def by auto
      thus ?thesis
        by (metis (no_types) assms C.hcomp_simps(3) C.hseqE C.ide_dom C.src_dom C.trg_dom
            D.comp_arr_inv' D.comp_assoc \<Phi>_components_are_iso \<Phi>_simps(5) is_natural_1)
    qed

    lemma preserves_adjunction_data:
    assumes "adjunction_data_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
    shows "adjunction_data_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             (F f) (F g) (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))
             (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
    proof
      interpret adjunction_data_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>
        using assms by auto
      show "D.ide (F f)"
        using preserves_ide by simp
      show "D.ide (F g)"
        using preserves_ide by simp
      show "\<guillemotleft>D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) : src\<^sub>D (F f) \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F f\<guillemotright>"
        using antipar C.VV.ide_char C.VV.arr_char \<Phi>_in_hom(2) \<Psi>_in_hom FF_def by auto
      show "\<guillemotleft>D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) : F f \<star>\<^sub>D F g \<Rightarrow>\<^sub>D src\<^sub>D (F g)\<guillemotright>"
        using antipar C.VV.ide_char C.VV.arr_char FF_def \<Phi>_in_hom(2) \<Psi>_in_hom(2)
              \<Psi>_char(2)
        by auto
    qed

    lemma preserves_equivalence:
    assumes "equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
    shows "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             (F f) (F g) (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))
             (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
    proof -
      interpret equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>
        using assms by auto
      interpret A: adjunction_data_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                     \<open>F f\<close> \<open>F g\<close> \<open>D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)\<close>
                     \<open>D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)\<close>
        using adjunction_data_in_bicategory_axioms preserves_adjunction_data by auto
      show "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             (F f) (F g) (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))
             (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
      proof
        show "D.iso (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))"
          using antipar D.iso_inv_iso FF_def unit_is_iso
                preserves_iso \<Psi>_char(2) D.isos_compose
          by simp
        show "D.iso (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
          using antipar \<Psi>_char(2) C.VV.ide_char C.VV.arr_char FF_def
                D.iso_inv_iso D.isos_compose
          by auto
      qed
    qed

    lemma preserves_equivalence_maps:
    assumes "C.equivalence_map f"
    shows "D.equivalence_map (F f)"
    proof -
      obtain g \<eta> \<epsilon> where E: "equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
        using assms C.equivalence_map_def by auto
      interpret E: equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>
        using E by auto
      have E': "equivalence_in_bicategory (\<cdot>\<^sub>D) (\<star>\<^sub>D) \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g)
                  (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))
                  (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
        using E preserves_equivalence by auto
      moreover have "src\<^sub>D (F f) = map\<^sub>0 (src\<^sub>C f) \<and> trg\<^sub>D (F f) = map\<^sub>0 (trg\<^sub>C f)"
        using assms C.equivalence_map_def map\<^sub>0_simps by simp
      ultimately show ?thesis
        using D.equivalence_map_def by auto
    qed

    lemma preserves_equivalent_objects:
    assumes "C.equivalent_objects a b"
    shows "D.equivalent_objects (map\<^sub>0 a) (map\<^sub>0 b)"
    proof -
      obtain f where f: "\<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright> \<and> C.equivalence_map f"
        using assms C.equivalent_objects_def by auto
      have "\<guillemotleft>F f : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 b\<guillemotright> \<and> D.equivalence_map (F f)"
        using f preserves_equivalence_maps by auto
      thus ?thesis
        using D.equivalent_objects_def by auto
    qed

  end

  subsection "Identity Pseudofunctors"

  locale identity_pseudofunctor =
    B: bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
  for V\<^sub>B :: "'b comp"                    (infixr "\<cdot>\<^sub>B" 55)
  and H\<^sub>B :: "'b comp"                   (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"       ("\<a>\<^sub>B[_, _, _]")
  and \<i>\<^sub>B :: "'b \<Rightarrow> 'b"                   ("\<i>\<^sub>B[_]")
  and src\<^sub>B :: "'b \<Rightarrow> 'b"
  and trg\<^sub>B :: "'b \<Rightarrow> 'b"
  begin

    text\<open>
      The underlying vertical functor is just the identity functor on the vertical category,
      which is already available as \<open>B.map\<close>.
    \<close>

    abbreviation map
    where "map \<equiv> B.map"

    interpretation I: weak_arrow_of_homs V\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B src\<^sub>B trg\<^sub>B map
    proof
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> B.isomorphic (map (src\<^sub>B \<mu>)) (src\<^sub>B (map \<mu>))"
        by (simp add: B.isomorphic_reflexive)
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> B.isomorphic (map (trg\<^sub>B \<mu>)) (trg\<^sub>B (map \<mu>))"
        by (simp add: B.isomorphic_reflexive)
    qed

    interpretation II: "functor" B.VV.comp B.VV.comp I.FF
      using I.functor_FF by simp

    interpretation H\<^sub>BoII: composite_functor B.VV.comp B.VV.comp V\<^sub>B I.FF \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>\<close>
      ..
    interpretation IoH\<^sub>B: composite_functor B.VV.comp V\<^sub>B V\<^sub>B \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>\<close> map
      ..

    text\<open>
      The horizontal composition provides the compositor.
    \<close>

    abbreviation cmp
    where "cmp \<equiv> \<lambda>\<mu>\<nu>. H\<^sub>B (fst \<mu>\<nu>) (snd \<mu>\<nu>)"

    interpretation cmp: natural_transformation B.VV.comp V\<^sub>B H\<^sub>BoII.map IoH\<^sub>B.map cmp
    proof
      show "\<And>\<mu>\<nu>. \<not> B.VV.arr \<mu>\<nu> \<Longrightarrow> cmp \<mu>\<nu> = B.null"
        using B.VV.arr_char by (meson B.hseqE B.hseq_char')
      fix \<mu>\<nu>
      assume \<mu>\<nu>: "B.VV.arr \<mu>\<nu>"
      show "B.dom (cmp \<mu>\<nu>) = H\<^sub>BoII.map (B.VV.dom \<mu>\<nu>)"
        using \<mu>\<nu> B.VV.arr_char I.FF_def by simp
      show "B.cod (cmp \<mu>\<nu>) = IoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)"
        using \<mu>\<nu> B.VV.arr_char I.FF_def by simp
      show "IoH\<^sub>B.map \<mu>\<nu> \<cdot>\<^sub>B cmp (B.VV.dom \<mu>\<nu>) = cmp \<mu>\<nu>"
        using \<mu>\<nu> B.VV.arr_char B.H.is_natural_1 by auto
      show "cmp (B.VV.cod \<mu>\<nu>) \<cdot>\<^sub>B H\<^sub>BoII.map \<mu>\<nu> = cmp \<mu>\<nu>"
        using \<mu>\<nu> B.VV.arr_char B.H.is_natural_2 I.FF_def by auto
    qed

    interpretation cmp: natural_isomorphism B.VV.comp V\<^sub>B H\<^sub>BoII.map IoH\<^sub>B.map cmp
      by unfold_locales simp

    sublocale pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B map cmp
      apply unfold_locales
      by (metis B.assoc_is_natural_2 B.assoc_naturality B.assoc_simps(1) B.comp_ide_self
          B.hcomp_simps(1) B.ide_char B.ide_hcomp B.map_simp fst_conv snd_conv)

    lemma is_pseudofunctor:
    shows "pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B map cmp"
      ..

  end

  subsection "Composition of Pseudofunctors"

  text \<open>
    In this section, we show how pseudofunctors may be composed.  The main work is to
    establish the coherence condition for associativity.
  \<close>

  locale composite_pseudofunctor =
    B: bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B +
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F +
    G: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G
  for V\<^sub>B :: "'b comp"                    (infixr "\<cdot>\<^sub>B" 55)
  and H\<^sub>B :: "'b comp"                   (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"       ("\<a>\<^sub>B[_, _, _]")
  and \<i>\<^sub>B :: "'b \<Rightarrow> 'b"                   ("\<i>\<^sub>B[_]")
  and src\<^sub>B :: "'b \<Rightarrow> 'b"
  and trg\<^sub>B :: "'b \<Rightarrow> 'b"
  and V\<^sub>C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'b \<Rightarrow> 'c"
  and \<Phi>\<^sub>F :: "'b * 'b \<Rightarrow> 'c"
  and G :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>G :: "'c * 'c \<Rightarrow> 'd"
  begin

    interpretation GF: composite_functor V\<^sub>B V\<^sub>C V\<^sub>D F G ..

    interpretation GF: weak_arrow_of_homs V\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D src\<^sub>D trg\<^sub>D \<open>G o F\<close>
    proof
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> D.isomorphic ((G o F) (src\<^sub>B \<mu>)) (src\<^sub>D ((G o F) \<mu>))"
      proof -
        fix \<mu>
        assume \<mu>: "B.arr \<mu>"
        show "D.isomorphic ((G o F) (src\<^sub>B \<mu>)) (src\<^sub>D ((G o F) \<mu>))"
        proof -
          have "(G o F) (src\<^sub>B \<mu>) = G (F (src\<^sub>B \<mu>))"
            using \<mu> by simp
          also have "D.isomorphic ... (G (src\<^sub>C (F \<mu>)))"
            using \<mu> F.weakly_preserves_src G.preserves_iso
            by (meson C.isomorphicE D.isomorphic_def G.preserves_hom)
          also have "D.isomorphic ... (src\<^sub>D (G (F \<mu>)))"
            using \<mu> G.weakly_preserves_src by blast
          also have "... = src\<^sub>D ((G o F) \<mu>)"
            by simp
          finally show ?thesis by blast
        qed
      qed
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> D.isomorphic ((G o F) (trg\<^sub>B \<mu>)) (trg\<^sub>D ((G o F) \<mu>))"
      proof -
        fix \<mu>
        assume \<mu>: "B.arr \<mu>"
        show "D.isomorphic ((G o F) (trg\<^sub>B \<mu>)) (trg\<^sub>D ((G o F) \<mu>))"
        proof -
          have "(G o F) (trg\<^sub>B \<mu>) = G (F (trg\<^sub>B \<mu>))"
            using \<mu> by simp
          also have "D.isomorphic ... (G (trg\<^sub>C (F \<mu>)))"
            using \<mu> F.weakly_preserves_trg G.preserves_iso
            by (meson C.isomorphicE D.isomorphic_def G.preserves_hom)
          also have "D.isomorphic ... (trg\<^sub>D (G (F \<mu>)))"
            using \<mu> G.weakly_preserves_trg by blast
          also have "... = trg\<^sub>D ((G o F) \<mu>)"
            by simp
          finally show ?thesis by blast
        qed
      qed
    qed

    interpretation H\<^sub>DoGF_GF: composite_functor B.VV.comp D.VV.comp V\<^sub>D GF.FF \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>D snd \<mu>\<nu>\<close>
      ..
    interpretation GFoH\<^sub>B: composite_functor B.VV.comp V\<^sub>B V\<^sub>D \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>\<close> \<open>G o F\<close>
      ..

    definition \<Phi>
    where "\<Phi> \<mu>\<nu> = (if B.VV.arr \<mu>\<nu> then
                      G (F (H\<^sub>B (fst \<mu>\<nu>) (snd \<mu>\<nu>))) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) \<cdot>\<^sub>D
                        \<Phi>\<^sub>G (F (B.dom (fst \<mu>\<nu>)), F (B.dom (snd \<mu>\<nu>)))
                   else D.null)"

    lemma \<Phi>_in_hom [intro]:
    assumes "B.VV.arr \<mu>\<nu>"
    shows "\<guillemotleft>\<Phi> \<mu>\<nu> : H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>) \<Rightarrow>\<^sub>D GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)\<guillemotright>"
    proof -
      have "\<Phi> \<mu>\<nu> = G (F (H\<^sub>B (fst \<mu>\<nu>) (snd \<mu>\<nu>))) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) \<cdot>\<^sub>D
                     \<Phi>\<^sub>G (F (B.dom (fst \<mu>\<nu>)), F (B.dom (snd \<mu>\<nu>)))"
        using assms \<Phi>_def by simp
      moreover have "\<guillemotleft> ... : H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>) \<Rightarrow>\<^sub>D GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)\<guillemotright>"
      proof (intro D.comp_in_homI)
        show "\<guillemotleft>\<Phi>\<^sub>G (F (B.dom (fst \<mu>\<nu>)), F (B.dom (snd \<mu>\<nu>))) :
                 H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>) \<Rightarrow>\<^sub>D G (F (B.dom (fst \<mu>\<nu>)) \<star>\<^sub>C F (B.dom (snd \<mu>\<nu>)))\<guillemotright>"
          using assms F.FF_def GF.FF_def B.VV.arr_char by auto
        show "\<guillemotleft>G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) :
                 G (F (B.dom (fst \<mu>\<nu>)) \<star>\<^sub>C F (B.dom (snd \<mu>\<nu>))) \<Rightarrow>\<^sub>D GFoH\<^sub>B.map (B.VV.dom \<mu>\<nu>)\<guillemotright>"
          using assms B.VV.arr_char F.FF_def by auto
        show "\<guillemotleft>G (F (fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>)) : GFoH\<^sub>B.map (B.VV.dom \<mu>\<nu>) \<Rightarrow>\<^sub>D GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)\<guillemotright>"
        proof -
          have "B.VV.in_hom \<mu>\<nu> (B.VV.dom \<mu>\<nu>) (B.VV.cod \<mu>\<nu>)"
            using assms by auto
          thus ?thesis by auto
        qed
      qed
      ultimately show ?thesis by argo
    qed

    lemma \<Phi>_simps [simp]:
    assumes "B.VV.arr \<mu>\<nu>"
    shows "D.arr (\<Phi> \<mu>\<nu>)"
    and "D.dom (\<Phi> \<mu>\<nu>) = H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>)"
    and "D.cod (\<Phi> \<mu>\<nu>) = GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)"
      using assms \<Phi>_in_hom by blast+

    interpretation \<Phi>: natural_transformation B.VV.comp V\<^sub>D H\<^sub>DoGF_GF.map GFoH\<^sub>B.map \<Phi>
    proof
      show "\<And>\<mu>\<nu>. \<not> B.VV.arr \<mu>\<nu> \<Longrightarrow> \<Phi> \<mu>\<nu> = D.null"
        unfolding \<Phi>_def by simp
      fix \<mu>\<nu>
      assume \<mu>\<nu>: "B.VV.arr \<mu>\<nu>"
      show "D.dom (\<Phi> \<mu>\<nu>) = H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>)"
        using \<mu>\<nu> \<Phi>_in_hom by blast
      show "D.cod (\<Phi> \<mu>\<nu>) = GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)"
        using \<mu>\<nu> \<Phi>_in_hom by blast
      show "GFoH\<^sub>B.map \<mu>\<nu> \<cdot>\<^sub>D \<Phi> (B.VV.dom \<mu>\<nu>) = \<Phi> \<mu>\<nu>"
        unfolding \<Phi>_def
        using \<mu>\<nu> B.VV.ide_char B.VV.arr_char D.comp_ide_arr B.VV.dom_char D.comp_assoc
              GF.is_natural_1
        apply simp
        by (metis (no_types, lifting) B.H.preserves_arr B.hcomp_simps(3))
      show "\<Phi> (B.VV.cod \<mu>\<nu>) \<cdot>\<^sub>D H\<^sub>DoGF_GF.map \<mu>\<nu> = \<Phi> \<mu>\<nu>"
      proof -
        have "\<Phi> (B.VV.cod \<mu>\<nu>) \<cdot>\<^sub>D H\<^sub>DoGF_GF.map \<mu>\<nu> =
              (G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                  \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>)))) \<cdot>\<^sub>D
                    (fst (GF.FF \<mu>\<nu>) \<star>\<^sub>D snd (GF.FF \<mu>\<nu>))"
          unfolding \<Phi>_def
          using \<mu>\<nu> B.VV.arr_char by simp
        also have "... = (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                            \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>)))) \<cdot>\<^sub>D
                               (fst (GF.FF \<mu>\<nu>) \<star>\<^sub>D snd (GF.FF \<mu>\<nu>))"
        proof -
          have "D.ide (G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))))"
            using \<mu>\<nu> B.VV.arr_char by simp
          moreover have "D.seq (G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))))
                               (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                                  \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>))))"
            using \<mu>\<nu> B.VV.arr_char B.VV.dom_char B.VV.cod_char F.FF_def
            apply (intro D.seqI)
                apply auto
          proof -
            show "G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))) =
                  D.cod (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                    \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>))))"
            proof -
              have "D.seq (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))))
                          (\<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>))))"
              proof
                show "\<guillemotleft>\<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>))) :
                         G (F (B.cod (fst \<mu>\<nu>))) \<star>\<^sub>D G (F (B.cod (snd \<mu>\<nu>)))
                            \<Rightarrow>\<^sub>D G (F (B.cod (fst \<mu>\<nu>)) \<star>\<^sub>C F (B.cod (snd \<mu>\<nu>)))\<guillemotright>"
                  using \<mu>\<nu> B.VV.arr_char by auto
                show "\<guillemotleft>G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) :
                         G (F (B.cod (fst \<mu>\<nu>)) \<star>\<^sub>C F (B.cod (snd \<mu>\<nu>)))
                            \<Rightarrow>\<^sub>D G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)))\<guillemotright>"
                  using \<mu>\<nu> B.VV.arr_char
                  by (simp add: F.\<Phi>_in_hom(2) G.preserves_hom)
              qed
              thus ?thesis
                using \<mu>\<nu> B.VV.arr_char by simp
            qed
          qed
          ultimately show ?thesis
            using \<mu>\<nu> D.comp_ide_arr [of "G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)))"
                                        "G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                                           \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>)))"]
            by simp
        qed
        also have "... = G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                            (\<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                               (fst (GF.FF \<mu>\<nu>) \<star>\<^sub>D snd (GF.FF \<mu>\<nu>)))"
          using D.comp_assoc by simp
        also have "... = G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (C.VV.cod (F.FF \<mu>\<nu>)) \<cdot>\<^sub>D G.H\<^sub>DoFF.map (F.FF \<mu>\<nu>)"
          using \<mu>\<nu> B.VV.arr_char F.FF_def G.FF_def GF.FF_def by auto
        also have "... = G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                           G.FoH\<^sub>C.map (F.FF \<mu>\<nu>) \<cdot>\<^sub>D \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
          using \<mu>\<nu> B.VV.arr_char G.\<Phi>.naturality by simp
        also have "... = (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                           G.FoH\<^sub>C.map (F.FF \<mu>\<nu>)) \<cdot>\<^sub>D \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
          using D.comp_assoc by simp
        also have "... = (G (\<Phi>\<^sub>F (B.VV.cod \<mu>\<nu>) \<cdot>\<^sub>C F.H\<^sub>DoFF.map \<mu>\<nu>)) \<cdot>\<^sub>D \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
        proof -
          have "(B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>)) = B.VV.cod \<mu>\<nu>"
            using \<mu>\<nu> B.VV.arr_char by simp
          moreover have "G.FoH\<^sub>C.map (F.FF \<mu>\<nu>) = G (F.H\<^sub>DoFF.map \<mu>\<nu>)"
            using \<mu>\<nu> F.FF_def by simp
          moreover have "G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D G (F.H\<^sub>DoFF.map \<mu>\<nu>) =
                         G (\<Phi>\<^sub>F (B.VV.cod \<mu>\<nu>) \<cdot>\<^sub>C F.H\<^sub>DoFF.map \<mu>\<nu>)"
            using \<mu>\<nu> B.VV.arr_char
            by (metis (no_types, lifting) F.\<Phi>.is_natural_2 F.\<Phi>.preserves_reflects_arr
                G.preserves_comp calculation(1))
          ultimately show ?thesis by argo
        qed
        also have "... = G (F.FoH\<^sub>C.map \<mu>\<nu> \<cdot>\<^sub>C \<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) \<cdot>\<^sub>D \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
          using \<mu>\<nu> F.\<Phi>.naturality [of \<mu>\<nu>] F.FF_def by simp
        also have "... = G (F.FoH\<^sub>C.map \<mu>\<nu>) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) \<cdot>\<^sub>D \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
        proof -
          have "G (F.FoH\<^sub>C.map \<mu>\<nu> \<cdot>\<^sub>C \<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) = G (F.FoH\<^sub>C.map \<mu>\<nu>) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>))"
            using \<mu>\<nu>
            by (metis (mono_tags, lifting) F.\<Phi>.is_natural_1 F.\<Phi>.preserves_reflects_arr
                G.preserves_comp)
          thus ?thesis
            using \<mu>\<nu> D.comp_assoc by simp
        qed
        also have "... = \<Phi> \<mu>\<nu>"
          using \<mu>\<nu> B.VV.arr_char \<Phi>_def F.FF_def F.FF.preserves_dom by auto
        finally show ?thesis by simp
      qed
    qed

    interpretation \<Phi>: natural_isomorphism B.VV.comp V\<^sub>D H\<^sub>DoGF_GF.map GFoH\<^sub>B.map \<Phi>
    proof
      show "\<And>hk. B.VV.ide hk \<Longrightarrow> D.iso (\<Phi> hk)"
      proof -
        fix hk
        assume hk: "B.VV.ide hk"
        have "D.iso (G (F (fst hk \<star>\<^sub>B snd hk)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom hk)) \<cdot>\<^sub>D
                       \<Phi>\<^sub>G (F (B.dom (fst hk)), F (B.dom (snd hk))))"
        proof (intro D.isos_compose)
          show "D.iso (\<Phi>\<^sub>G (F (B.dom (fst hk)), F (B.dom (snd hk))))"
            using hk G.\<Phi>.components_are_iso [of "(F (B.dom (fst hk)), F (B.dom (snd hk)))"]
                  C.VV.ide_char B.VV.arr_char B.VV.dom_char
            by (metis (no_types, lifting) B.VV.ideD(1) B.VV.ideD(2) B.VxV.dom_char
                F.FF_def F.FF.components_are_iso G.\<Phi>.preserves_iso fst_conv snd_conv)
          show "D.iso (G (\<Phi>\<^sub>F (B.VV.dom hk)))"
            using hk F.\<Phi>.components_are_iso B.VV.arr_char B.VV.dom_char B.VV.ideD(2) by auto
          show "D.seq (G (\<Phi>\<^sub>F (B.VV.dom hk))) (\<Phi>\<^sub>G (F (B.dom (fst hk)), F (B.dom (snd hk))))"
            using hk B.VV.arr_char B.VV.ide_char B.VV.dom_char C.VV.arr_char F.FF_def
            by auto
          show "D.iso (G (F (fst hk \<star>\<^sub>B snd hk)))"
            using hk F.\<Phi>.components_are_iso B.VV.arr_char by simp
          show "D.seq (G (F (fst hk \<star>\<^sub>B snd hk)))
                      (G (\<Phi>\<^sub>F (B.VV.dom hk)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F (B.dom (fst hk)), F (B.dom (snd hk))))"
            using hk B.VV.arr_char B.VV.dom_char
            by (metis (no_types, lifting) B.VV.ideD(1) \<Phi>_def \<Phi>_simps(1))
        qed
        thus "D.iso (\<Phi> hk)"
          unfolding \<Phi>_def using hk by simp
      qed
    qed

    sublocale pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>G o F\<close> \<Phi>
    proof
      fix f g h
      assume f: "B.ide f" and g: "B.ide g" and h: "B.ide h"
      assume fg: "src\<^sub>B f = trg\<^sub>B g" and gh: "src\<^sub>B g = trg\<^sub>B h"
      show "GF.map \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>B g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D GF.map h) =
            \<Phi> (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (GF.map f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[GF.map f, GF.map g, GF.map h]"
      proof -
        have "GF.map \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>B g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D GF.map h) =
              G (F \<a>\<^sub>B[f, g, h]) \<cdot>\<^sub>D
                (G (F ((f \<star>\<^sub>B g) \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h)) \<cdot>\<^sub>D
                  (G (F (f \<star>\<^sub>B g)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          unfolding \<Phi>_def
          using f g h fg gh B.VV.arr_char by simp
        also have "... = G (F \<a>\<^sub>B[f, g, h]) \<cdot>\<^sub>D
                          (G (\<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h)) \<cdot>\<^sub>D
                            (G (F (f \<star>\<^sub>B g)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh D.comp_ide_arr D.comp_assoc
          by (metis B.ideD(1) B.ide_hcomp B.src_hcomp F.\<Phi>_simps(1) F.\<Phi>_simps(5) G.is_natural_2)
        also have "... = G (F \<a>\<^sub>B[f, g, h]) \<cdot>\<^sub>D
                          (G (\<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h)) \<cdot>\<^sub>D
                            (G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          by (metis (no_types) D.comp_assoc F.\<Phi>_simps(1) F.\<Phi>_simps(5) G.is_natural_2 f fg g)
        also have "... = (G (F \<a>\<^sub>B[f, g, h]) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f \<star>\<^sub>B g, h))) \<cdot>\<^sub>D
                            \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using D.comp_assoc by simp
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D
                            \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh B.VV.arr_char by simp
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D
                            \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g)) \<star>\<^sub>D G (F h)) \<cdot>\<^sub>D
                              (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh B.VV.arr_char C.VV.arr_char F.FF_def D.whisker_right
          by auto
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D
                          (\<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g)) \<star>\<^sub>D G (F h))) \<cdot>\<^sub>D
                            (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using D.comp_assoc by simp
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D
                          (G (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h)) \<cdot>\<^sub>D
                            (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
        proof -
          have "\<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) = \<Phi>\<^sub>G (C.VV.cod (\<Phi>\<^sub>F (f, g), F h))"
            using f g h fg gh B.VV.arr_char C.VV.arr_char by simp
          moreover have "G (\<Phi>\<^sub>F (f, g)) \<star>\<^sub>D G (F h) = G.H\<^sub>DoFF.map (\<Phi>\<^sub>F (f, g), F h)"
            using f g h fg gh B.VV.arr_char C.VV.arr_char G.FF_def by simp
          moreover have "G.FoH\<^sub>C.map (\<Phi>\<^sub>F (f, g), F h) = G (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h)"
            using f g h fg gh B.VV.arr_char by simp
          moreover have "\<Phi>\<^sub>G (C.VV.dom (\<Phi>\<^sub>F (f, g), F h)) = \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h)"
            using f g h fg gh C.VV.arr_char F.\<Phi>_in_hom [of f g] by auto
          ultimately show ?thesis
            using f g h fg gh B.VV.arr_char G.\<Phi>.naturality
            by (metis (mono_tags, lifting) C.VV.arr_cod_iff_arr C.VV.arr_dom_iff_arr
                G.FoH\<^sub>C.is_extensional G.H\<^sub>DoFF.is_extensional G.\<Phi>.is_extensional)
        qed
        also have "... = (G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using D.comp_assoc by simp
        also have "... = G ((F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>C (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h)) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh B.VV.arr_char F.FF_def by auto
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h) \<cdot>\<^sub>C (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h)) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using C.comp_assoc by simp
        also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[F f, F g, F h]) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh F.assoc_coherence [of f g h] by simp
        also have "... = G ((\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>C \<a>\<^sub>C[F f, F g, F h]) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using C.comp_assoc by simp
        also have "... = (G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D G \<a>\<^sub>C[F f, F g, F h]) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh B.VV.arr_char F.FF_def by auto
        also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                           G \<a>\<^sub>C[F f, F g, F h] \<cdot>\<^sub>D \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using D.comp_assoc by simp
        also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[G (F f), G (F g), G (F h)]"
          using f g h fg gh G.assoc_coherence [of "F f" "F g" "F h"] by simp
        also have "... = (G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))) \<cdot>\<^sub>D
                             \<a>\<^sub>D[G (F f), G (F g), G (F h)]"
          using D.comp_assoc by simp
        also have "... = (\<Phi> (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi> (g, h))) \<cdot>\<^sub>D \<a>\<^sub>D[G (F f), G (F g), G (F h)]"
        proof -
          have "G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                  \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h)) =
                \<Phi> (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi> (g, h))"
          proof -
            have "\<Phi> (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi> (g, h)) =
                  (G (F (f \<star>\<^sub>B g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h))) \<cdot>\<^sub>D
                    (G (F f) \<star>\<^sub>D G (F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              unfolding \<Phi>_def
              using f g h fg gh B.VV.arr_char by simp
            also have "... = (G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h))) \<cdot>\<^sub>D
                               (G (F f) \<star>\<^sub>D G (F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
            proof -
              have "G (F (f \<star>\<^sub>B g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h))"
                using f g h fg gh B.VV.arr_char D.comp_ide_arr by simp
              thus ?thesis
                using D.comp_assoc by metis
            qed
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (G (F f) \<star>\<^sub>D G (F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using D.comp_assoc by simp
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (G (F f) \<star>\<^sub>D G (\<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
            proof -
              have "G (F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (g, h)) = G (\<Phi>\<^sub>F (g, h))"
                using f g h fg gh B.VV.arr_char D.comp_ide_arr by simp
              thus ?thesis
                using D.comp_assoc by metis
            qed
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (G (F f) \<star>\<^sub>D G (\<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using f g h fg gh
                    D.whisker_left [of "G (F f)" "G (\<Phi>\<^sub>F (g, h))" "\<Phi>\<^sub>G (F g, F h)"]
              by fastforce
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (\<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D G (\<Phi>\<^sub>F (g, h)))) \<cdot>\<^sub>D
                                 (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using D.comp_assoc by simp
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (G (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h)) \<cdot>\<^sub>D
                                 (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
            proof -
              have "\<Phi>\<^sub>G (C.VV.cod (F f, \<Phi>\<^sub>F (g, h))) = \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h))"
                using f g h fg gh B.VV.arr_char C.VV.cod_char by auto
              moreover have "G.H\<^sub>DoFF.map (F f, \<Phi>\<^sub>F (g, h)) = G (F f) \<star>\<^sub>D G (\<Phi>\<^sub>F (g, h))"
                using f g h fg gh B.VV.arr_char G.FF_def by auto
              moreover have "G.FoH\<^sub>C.map (F f, \<Phi>\<^sub>F (g, h)) = G (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))"
                using f g h fg gh B.VV.arr_char C.VV.arr_char by simp
              moreover have "C.VV.dom (F f, \<Phi>\<^sub>F (g, h)) = (F f, F g \<star>\<^sub>C F h)"
                using f g h fg gh B.VV.arr_char C.VV.arr_char C.VV.dom_char F.\<Phi>_in_hom [of g h]
                by auto
              ultimately show ?thesis
                using f g h fg gh B.VV.arr_char C.VV.arr_char
                      G.\<Phi>.naturality [of "(F f, \<Phi>\<^sub>F (g, h))"]
                by simp
            qed
            also have "... = (G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D (G (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h)))) \<cdot>\<^sub>D
                               \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using D.comp_assoc by simp
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                               \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using f g h fg gh B.VV.arr_char
              by (metis (no_types, lifting) B.assoc_simps(1) C.comp_assoc C.seqE
                  F.preserves_assoc(1) F.preserves_reflects_arr G.preserves_comp)
            finally show ?thesis by simp
          qed
          thus ?thesis by simp
        qed
        also have "... = \<Phi> (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[G (F f), G (F g), G (F h)]"
          using D.comp_assoc by simp
        finally show ?thesis by simp
      qed
    qed

    lemma is_pseudofunctor:
    shows "pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (G o F) \<Phi>"
      ..

  end

  subsection "Equivalence Pseudofunctors"

  text \<open>
    In this section, we define ``equivalence pseudofunctors'', which are pseudofunctors
    that can be extended to an equivalence of bicategories.  My purpose at the moment
    is just to have some way to establish that bicategories are equivalent and not to
    go so far as to give a full and proper development of equivalence of bicategories
    (which would involve the further definition of pseudonatural transformations and so on),
    nor even to prove that the pseudofunctors in an equivalence of bicategories are in fact
    ``equivalence pseudofunctors'' according to the definition given here.
    So in some sense the results we ultimately prove depend on one's having taken for
    granted that the definition given here is ``correct''.  This is not entirely vacuous,
    because the definition does have some subtleties and it took me awhile to work the bugs
    out of the formalization.  However, enough is proved using the definition that I think
    it is not difficult to accept it as correct.  Future work can go back and give a fuller
    development to provide even more confidence.

    \sloppypar
    It is asserted on the ``nLab'' \cite{nlab-equivalence-of-2-categories}
    that a pseudofunctor is part of an equivalence of bicategories if and only if it is
    essentially surjective on objects, essentially full on 1-cells (here: ``identities'')
    and fully faithful on 2-cells (here: ``arrows'').
    To turn this into a formal definition, it is necessary to find the proper way to express
    formally the notions involved.  ``Essentially surjective on objects'' is perhaps the
    most complex of these, as it involves internal equivalences between objects.

    The definition below requires that an equivalence pseudofunctor be (globally) faithful
    with respect to vertical composition.  Traditional formulations do not consider a
    pseudofunctor as a single global functor, so we have to consider whether this condition
    is too strong.  In fact, a pseudofunctor (as defined here) is locally faithful if and
    only if it is globally faithful.
  \<close>

  context pseudofunctor
  begin

    definition locally_faithful
    where "locally_faithful \<equiv>
           \<forall>f g \<mu> \<mu>'. \<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C g\<guillemotright> \<and> \<guillemotleft>\<mu>' : f \<Rightarrow>\<^sub>C g\<guillemotright> \<and> F \<mu> = F \<mu>' \<longrightarrow> \<mu> = \<mu>'"

    lemma locally_faithful_iff_faithful:
    shows "locally_faithful \<longleftrightarrow> faithful_functor V\<^sub>C V\<^sub>D F"
    proof
      show "faithful_functor V\<^sub>C V\<^sub>D F \<Longrightarrow> locally_faithful"
      proof -
        assume 1: "faithful_functor V\<^sub>C V\<^sub>D F"
        interpret faithful_functor V\<^sub>C V\<^sub>D F
          using 1 by blast
        show "locally_faithful"
          unfolding locally_faithful_def using is_faithful by blast
      qed
      show "locally_faithful \<Longrightarrow> faithful_functor V\<^sub>C V\<^sub>D F"
      proof -
        assume 1: "locally_faithful"
        show "faithful_functor V\<^sub>C V\<^sub>D F"
        proof
          fix \<mu> \<mu>'
          assume par: "C.par \<mu> \<mu>'" and eq: "F \<mu> = F \<mu>'"
          obtain f g where fg: "\<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C g\<guillemotright> \<and> \<guillemotleft>\<mu>' : f \<Rightarrow>\<^sub>C g\<guillemotright>"
            using par by auto
          show "\<mu> = \<mu>'"
            using 1 fg locally_faithful_def eq by simp
        qed
      qed
    qed

  end

  text \<open>
    In contrast, it is not true that a pseudofunctor that is locally full is also
    globally full, because we can have \<open>\<guillemotleft>\<nu> : F h \<Rightarrow>\<^sub>D F k\<guillemotright>\<close> even if \<open>h\<close> and \<open>k\<close>
    are not in the same hom-category.  So it would be a mistake to require that an
    equivalence functor be globally full.
  \<close>

  locale equivalence_pseudofunctor =
    pseudofunctor +
    faithful_functor V\<^sub>C V\<^sub>D F +
  assumes biessentially_surjective_on_objects:
            "D.obj a' \<Longrightarrow> \<exists>a. C.obj a \<and> D.equivalent_objects (map\<^sub>0 a) a'"
  and locally_essentially_surjective:
            "\<lbrakk> C.obj a; C.obj b; \<guillemotleft>g : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 b\<guillemotright>; D.ide g \<rbrakk> \<Longrightarrow>
                \<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright> \<and> C.ide f \<and> D.isomorphic (F f) g"
  and locally_full:
            "\<lbrakk> C.ide f; C.ide f'; src\<^sub>C f = src\<^sub>C f'; trg\<^sub>C f = trg\<^sub>C f'; \<guillemotleft>\<nu> : F f \<Rightarrow>\<^sub>D F f'\<guillemotright> \<rbrakk> \<Longrightarrow>
                \<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C f'\<guillemotright> \<and> F \<mu> = \<nu>"
  begin

    lemma reflects_ide:
    assumes "C.endo \<mu>" and "D.ide (F \<mu>)"
    shows "C.ide \<mu>"
      using assms is_faithful [of "C.dom \<mu>" \<mu>] C.ide_char'
      by (metis C.arr_dom C.cod_dom C.dom_dom C.seqE D.ide_char preserves_dom)

    lemma reflects_iso:
    assumes "C.arr \<mu>" and "D.iso (F \<mu>)"
    shows "C.iso \<mu>"
    proof -
      obtain \<mu>' where \<mu>': "\<guillemotleft>\<mu>' : C.cod \<mu> \<Rightarrow>\<^sub>C C.dom \<mu>\<guillemotright> \<and> F \<mu>' = D.inv (F \<mu>)"
        using assms locally_full [of "C.cod \<mu>" "C.dom \<mu>" "D.inv (F \<mu>)"]
              D.inv_in_hom C.in_homE preserves_hom C.in_homI
        by auto
      have "C.inverse_arrows \<mu> \<mu>'"
      proof
        have "D.ide (F (\<mu>' \<cdot>\<^sub>C \<mu>))"
          using assms \<mu>'
          by (metis (no_types, lifting) C.dom_comp C.in_homE C.seqI D.comp_inv_arr'
              D.ide_char' preserves_arr preserves_comp preserves_dom)
        moreover have "C.endo (\<mu>' \<cdot>\<^sub>C \<mu>)"
          using assms \<mu>' by auto
        ultimately show "C.ide (\<mu>' \<cdot>\<^sub>C \<mu>)"
          using assms \<mu>' reflects_ide by blast
        have "D.ide (F (\<mu> \<cdot>\<^sub>C \<mu>'))"
          using assms \<mu>'
          by (metis C.ide_compE D.comp_arr_inv' D.dom_cod D.ide_char' \<open>C.ide (\<mu>' \<cdot>\<^sub>C \<mu>)\<close>
              preserves_arr preserves_comp_2)
        moreover have "C.endo (\<mu> \<cdot>\<^sub>C \<mu>')"
          using assms \<mu>' by auto
        ultimately show "C.ide (\<mu> \<cdot>\<^sub>C \<mu>')"
          using assms reflects_ide by blast
      qed
      thus ?thesis by auto
    qed

    lemma reflects_equivalence:
    assumes "C.ide f" and "C.ide g"
    and "\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>" and "\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>"
    and "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g)
           (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))
           (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
    shows "equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
    proof -
      interpret E': equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F f\<close> \<open>F g\<close>
                      \<open>D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)\<close>
                      \<open>D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)\<close>
        using assms by auto
      show ?thesis
      proof
        show "C.ide f"
          using assms(1) by simp
        show "C.ide g"
          using assms(2) by simp
        show "\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>"
          using assms(3) by simp
        show "\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>"
          using assms(4) by simp
        have 0: "src\<^sub>C f = trg\<^sub>C g \<and> src\<^sub>C g = trg\<^sub>C f"
          using `\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>`
          by (metis C.hseqE C.ideD(1) C.ide_cod C.ide_dom C.in_homE assms(4))
        show "C.iso \<eta>"
        proof -
          have "D.iso (F \<eta>)"
          proof -
            have 1:  "\<guillemotleft>D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) : map\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F f\<guillemotright>"
              using `C.ide f` `C.ide g` `\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>`
                    \<Psi>_char \<Phi>_in_hom \<Phi>_components_are_iso
              by (metis (mono_tags, lifting) C.ideD(1) E'.unit_in_vhom preserves_src)
            have 2: "D.iso (\<Phi> (g, f)) \<and> \<guillemotleft>\<Phi> (g, f) : F g \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C f)\<guillemotright>"
              using 0 `C.ide f` `C.ide g` \<Phi>_in_hom by simp
            have 3: "D.iso (D.inv (\<Psi> (src\<^sub>C f))) \<and>
                     \<guillemotleft>D.inv (\<Psi> (src\<^sub>C f)) : F (src\<^sub>C f) \<Rightarrow>\<^sub>D map\<^sub>0 (src\<^sub>C f)\<guillemotright>"
               using `C.ide f` \<Psi>_char D.iso_inv_iso by simp
            have "D.iso (\<Phi> (g, f) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)) \<cdot>\<^sub>D
                    D.inv (\<Psi> (src\<^sub>C f)))"
              using 1 2 3 E'.unit_is_iso D.isos_compose by blast
            moreover have "\<Phi> (g, f) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)) \<cdot>\<^sub>D
                             D.inv (\<Psi> (src\<^sub>C f)) =
                           F \<eta>"
            proof -
              have "\<Phi> (g, f) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)) \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f)) =
                    (\<Phi> (g, f) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f))) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D (\<Psi> (src\<^sub>C f)) \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f)))"
                using D.comp_assoc by simp
              also have "... = F (g \<star>\<^sub>C f) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D F (src\<^sub>C f)"
                using 2 3 D.comp_arr_inv D.comp_inv_arr D.inv_is_inverse
                by (metis C.ideD(1) C.obj_src D.comp_assoc D.dom_inv D.in_homE \<Psi>_char(2)
                          assms(1))
              also have "... = F \<eta>"
                using `\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>` D.comp_arr_dom D.comp_cod_arr by auto
              finally show ?thesis by simp
            qed
            ultimately show ?thesis by simp
          qed
          thus ?thesis
            using assms reflects_iso by auto
        qed
        show "C.iso \<epsilon>"
        proof -
          have "D.iso (F \<epsilon>)"
          proof -
            have 1:  "\<guillemotleft>D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) : F f \<star>\<^sub>D F g \<Rightarrow>\<^sub>D map\<^sub>0 (src\<^sub>C g)\<guillemotright>"
              using `C.ide f` `C.ide g` `\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>`
                    \<Psi>_char \<Phi>_in_hom \<Phi>_components_are_iso
              by (metis (mono_tags, lifting) C.ideD(1) E'.counit_in_vhom preserves_src)
            have 2: "D.iso (D.inv (\<Phi> (f, g))) \<and>
                     \<guillemotleft>D.inv (\<Phi> (f, g)) : F (f \<star>\<^sub>C g) \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F g\<guillemotright>"
              using 0 `C.ide f` `C.ide g` `\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>` \<Phi>_in_hom(2)
                    D.inv_in_hom D.iso_inv_iso
              by simp
            have 3: "D.iso (\<Psi> (trg\<^sub>C f)) \<and> \<guillemotleft>\<Psi> (trg\<^sub>C f) : map\<^sub>0 (trg\<^sub>C f) \<Rightarrow>\<^sub>D F (trg\<^sub>C f)\<guillemotright>"
               using `C.ide f` \<Psi>_char by simp
            have
              "D.iso (\<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D D.inv (\<Phi> (f, g)))"
              using 0 1 2 3 E'.counit_is_iso D.isos_compose
              by (metis D.arrI D.cod_comp D.cod_inv D.seqI D.seqI')
            moreover have "\<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                             D.inv (\<Phi> (f, g)) =
                           F \<epsilon>"
            proof -
              have "\<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                      D.inv (\<Phi> (f, g)) =
                    (\<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f))) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D (\<Phi> (f, g) \<cdot>\<^sub>D D.inv (\<Phi> (f, g)))"
                using D.comp_assoc by simp
              also have "... = F (trg\<^sub>C f) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D F (f \<star>\<^sub>C g)"
                using 0 2 3 D.comp_arr_inv D.comp_inv_arr D.inv_is_inverse D.iso_inv_iso
                by (simp add: C.VV.arr_char C.VV.ide_char assms(1) assms(2))
              also have "... = F \<epsilon>"
                using 0 `\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>` D.comp_arr_dom D.comp_cod_arr by auto
              finally show ?thesis by simp
            qed
            ultimately show ?thesis by simp
          qed
          thus ?thesis
            using assms reflects_iso by auto
        qed
      qed
    qed

    lemma reflects_equivalence_map:
    assumes "C.ide f" and "D.equivalence_map (F f)"
    shows "C.equivalence_map f"
    proof -
      obtain g' \<phi> \<psi> where E': "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) g' \<phi> \<psi>"
        using assms D.equivalence_map_def by auto
      interpret E': equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F f\<close> g' \<phi> \<psi>
        using E' by auto
      obtain g where g: "\<guillemotleft>g : trg\<^sub>C f \<rightarrow>\<^sub>C src\<^sub>C f\<guillemotright> \<and> C.ide g \<and> D.isomorphic (F g) g'"
        using assms E'.antipar locally_essentially_surjective [of "trg\<^sub>C f" "src\<^sub>C f" g']
        by auto
      obtain \<mu> where \<mu>: "\<guillemotleft>\<mu> : g' \<Rightarrow>\<^sub>D F g\<guillemotright> \<and> D.iso \<mu>"
        using g D.isomorphic_def D.isomorphic_symmetric by blast
      have E'': "equivalence_in_bicategory (\<cdot>\<^sub>D) (\<star>\<^sub>D) \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g)
                   ((F g \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D F f) \<cdot>\<^sub>D \<phi>)
                   (\<psi> \<cdot>\<^sub>D (D.inv (F f) \<star>\<^sub>D g') \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<mu>))"
        using assms \<mu> E'.equivalence_in_bicategory_axioms D.ide_is_iso
              D.equivalence_respects_iso [of "F f" g' \<phi> \<psi> "F f" "F f" \<mu> "F g"]
        by auto
      interpret E'': equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F f\<close> \<open>F g\<close>
                       \<open>(F g \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D F f) \<cdot>\<^sub>D \<phi>\<close>
                       \<open>\<psi> \<cdot>\<^sub>D (D.inv (F f) \<star>\<^sub>D g') \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<mu>)\<close>
        using E'' by auto
      let ?\<eta>' = "\<Phi> (g, f) \<cdot>\<^sub>D (F g \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D F f) \<cdot>\<^sub>D \<phi> \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))"
      have \<eta>': "\<guillemotleft>?\<eta>' : F (src\<^sub>C f) \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C f)\<guillemotright>"
      proof (intro D.comp_in_homI)
        show "\<guillemotleft>D.inv (\<Psi> (src\<^sub>C f)) : F (src\<^sub>C f) \<Rightarrow>\<^sub>D src\<^sub>D (F f)\<guillemotright>"
          using assms \<Psi>_char by simp
        show "\<guillemotleft>\<phi> : src\<^sub>D (F f) \<Rightarrow>\<^sub>D g' \<star>\<^sub>D F f\<guillemotright>"
          using g E'.unit_in_hom(2) by simp
        show "\<guillemotleft>\<mu> \<star>\<^sub>D F f : g' \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F f\<guillemotright>"
          using assms g \<mu> E'.antipar E''.antipar by blast
        show "\<guillemotleft>F g \<star>\<^sub>D F f : F g \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F f\<guillemotright>"
          using assms g E''.antipar by auto
        show "\<guillemotleft>\<Phi> (g, f) : F g \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C f)\<guillemotright>"
          using assms g \<Phi>_in_hom by auto
      qed
      have iso_\<eta>': "D.iso ?\<eta>'"
      proof -
        have "D.iso (\<Phi> (g, f))"
          using assms g by auto
        thus ?thesis
          using assms g \<mu> E'.antipar E''.antipar \<Phi>_in_hom \<Psi>_char
                E'.unit_in_hom D.iso_inv_iso E'.unit_is_iso \<eta>'
          by (intro D.isos_compose) auto
      qed
      let ?\<epsilon>' = "\<Psi> (src\<^sub>C g) \<cdot>\<^sub>D \<psi> \<cdot>\<^sub>D (D.inv (F f) \<star>\<^sub>D g') \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<mu>) \<cdot>\<^sub>D D.inv (\<Phi> (f, g))"
      have \<epsilon>': "\<guillemotleft>?\<epsilon>' : F (f \<star>\<^sub>C g) \<Rightarrow>\<^sub>D F (trg\<^sub>C f)\<guillemotright>"
      proof (intro D.comp_in_homI)
        show "\<guillemotleft>D.inv (\<Phi> (f, g)) : F (f \<star>\<^sub>C g) \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F g\<guillemotright>"
          using assms g \<Phi>_in_hom C.VV.ide_char C.VV.arr_char by auto
        show "\<guillemotleft>F f \<star>\<^sub>D D.inv \<mu> : F f \<star>\<^sub>D F g \<Rightarrow>\<^sub>D F f \<star>\<^sub>D g'\<guillemotright>"
          using assms g \<mu> E'.antipar E''.antipar D.ide_in_hom(2) by auto
        show "\<guillemotleft>D.inv (F f) \<star>\<^sub>D g' : F f \<star>\<^sub>D g' \<Rightarrow>\<^sub>D F f \<star>\<^sub>D g'\<guillemotright>"
          using assms E'.antipar E''.antipar D.ide_is_iso
          by (simp add: D.ide_in_hom(2))
        show "\<guillemotleft>\<psi> :  F f \<star>\<^sub>D g' \<Rightarrow>\<^sub>D trg\<^sub>D (F f)\<guillemotright>"
          using E'.counit_in_hom by simp
        show "\<guillemotleft>\<Psi> (src\<^sub>C g) : trg\<^sub>D (F f) \<Rightarrow>\<^sub>D F (trg\<^sub>C f)\<guillemotright>"
          using assms g \<Psi>_char E'.antipar by auto
      qed
      have iso_\<epsilon>': "D.iso ?\<epsilon>'"
      proof -
        have "D.iso (\<Phi> (f, g))"
          using assms g C.VV.ide_char C.VV.arr_char by auto
        thus ?thesis
          using assms g \<mu> E'.antipar E''.antipar \<Phi>_in_hom \<Psi>_char
                E'.counit_in_hom D.iso_inv_iso E'.counit_is_iso \<epsilon>'
          by (metis C.ideD(1) C.obj_src D.arrI D.iso_hcomp D.hseq_char D.ide_is_iso
              D.isos_compose D.seqE E'.ide_right components_are_iso)
      qed
      obtain \<eta> where \<eta>: "\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright> \<and> F \<eta> = ?\<eta>'"
        using assms g E'.antipar \<eta>' locally_full [of "src\<^sub>C f" "g \<star>\<^sub>C f" ?\<eta>']
        by (metis C.ide_hcomp C.ideD(1) C.in_hhomE C.src.preserves_ide C.hcomp_simps(1-2)
            C.src_trg C.trg_trg)
      have iso_\<eta>: "C.iso \<eta>"
        using \<eta> \<eta>' iso_\<eta>' reflects_iso by auto
      have 1: "\<exists>\<epsilon>. \<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright> \<and> F \<epsilon> = ?\<epsilon>'"
      proof -
        have "C.ide (f \<star>\<^sub>C g)"
          using assms g by auto
        moreover have "C.ide (src\<^sub>C g)"
          using assms g by simp
        moreover have "src\<^sub>C (f \<star>\<^sub>C g) = src\<^sub>C (src\<^sub>C g)"
          using assms g by auto
        moreover have "trg\<^sub>C (f \<star>\<^sub>C g) = trg\<^sub>C (src\<^sub>C g)"
          using assms g by auto
        ultimately show ?thesis
          using locally_full [of "f \<star>\<^sub>C g" "src\<^sub>C g" ?\<epsilon>']
          by (metis C.in_hhomE \<epsilon>' g)
      qed
      obtain \<epsilon> where \<epsilon>: "\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright> \<and> F \<epsilon> = ?\<epsilon>'"
        using 1 by blast
      have iso_\<epsilon>: "C.iso \<epsilon>"
        using \<epsilon> \<epsilon>' iso_\<epsilon>' reflects_iso by auto
      have "equivalence_in_bicategory (\<cdot>\<^sub>C) (\<star>\<^sub>C) \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
        using assms g \<eta> \<epsilon> iso_\<eta> iso_\<epsilon> by (unfold_locales, auto)
      thus ?thesis
        using C.equivalence_map_def by auto
    qed

    lemma reflects_equivalent_objects:
    assumes "C.obj a" and "C.obj b" and "D.equivalent_objects (map\<^sub>0 a) (map\<^sub>0 b)"
    shows "C.equivalent_objects a b"
    proof -
      obtain f' where f': "\<guillemotleft>f' : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 b\<guillemotright> \<and> D.equivalence_map f'"
        using assms D.equivalent_objects_def D.equivalence_map_def by auto
      obtain f where f: "\<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright> \<and> C.ide f \<and> D.isomorphic (F f) f'"
        using assms f' locally_essentially_surjective [of a b f'] D.equivalence_map_is_ide
        by auto
      have "D.equivalence_map (F f)"
        using f f' D.equivalence_map_preserved_by_iso [of f' "F f"] D.isomorphic_symmetric
        by simp
      hence "C.equivalence_map f"
        using f f' reflects_equivalence_map [of f] by simp
      thus ?thesis
        using f C.equivalent_objects_def by auto
    qed

  end

  text\<open>
    For each pair of objects \<open>a\<close>, \<open>b\<close> of \<open>C\<close>, an equivalence pseudofunctor restricts
    to an equivalence of categories between \<open>C.hhom a b\<close> and \<open>D.hhom (map\<^sub>0 a) (map\<^sub>0 b)\<close>.
  \<close>

  locale equivalence_pseudofunctor_at_hom =
    equivalence_pseudofunctor +
  fixes a :: 'a and b :: 'a
  assumes obj_a: "C.obj a"
  and obj_b: "C.obj b"
  begin

    interpretation hhom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : a \<rightarrow>\<^sub>C b\<guillemotright>\<close>
      using C.hhom_is_subcategory by simp
    interpretation hhom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 b\<guillemotright>\<close>
      using D.hhom_is_subcategory by simp

    lemma is_equivalence_functor:
    shows "equivalence_functor hhom\<^sub>C.comp hhom\<^sub>D.comp (\<lambda>\<mu>. if hhom\<^sub>C.arr \<mu> then F \<mu> else D.null)"
    proof -
      interpret "functor" hhom\<^sub>C.comp hhom\<^sub>D.comp \<open>\<lambda>\<mu>. if hhom\<^sub>C.arr \<mu> then F \<mu> else D.null\<close>
        using hhom\<^sub>C.arr_char hhom\<^sub>D.arr_char hhom\<^sub>C.dom_char hhom\<^sub>D.dom_char
              hhom\<^sub>C.cod_char hhom\<^sub>D.cod_char hhom\<^sub>C.seq_char hhom\<^sub>C.comp_char hhom\<^sub>D.comp_char
        by unfold_locales auto
      interpret fully_faithful_and_essentially_surjective_functor
                  hhom\<^sub>C.comp hhom\<^sub>D.comp \<open>\<lambda>\<mu>. if hhom\<^sub>C.arr \<mu> then F \<mu> else D.null\<close>
      proof
        show "\<And>\<mu> \<mu>'. \<lbrakk>hhom\<^sub>C.par \<mu> \<mu>';
                      (if hhom\<^sub>C.arr \<mu> then F \<mu> else D.null) =
                      (if hhom\<^sub>C.arr \<mu>' then F \<mu>' else D.null)\<rbrakk>
                         \<Longrightarrow> \<mu> = \<mu>'"
          using is_faithful hhom\<^sub>C.dom_char hhom\<^sub>D.dom_char hhom\<^sub>C.cod_char hhom\<^sub>D.cod_char
          by (metis C.in_hhom_def hhom\<^sub>C.arrE)
        show "\<And>f f' \<nu>. \<lbrakk>hhom\<^sub>C.ide f; hhom\<^sub>C.ide f';
                         hhom\<^sub>D.in_hom \<nu> (if hhom\<^sub>C.arr f' then F f' else D.null)
                                       (if hhom\<^sub>C.arr f then F f else D.null)\<rbrakk>
                 \<Longrightarrow> \<exists>\<mu>. hhom\<^sub>C.in_hom \<mu> f' f \<and> (if hhom\<^sub>C.arr \<mu> then F \<mu> else D.null) = \<nu>"
        proof -
          fix f f' \<nu>
          assume f: "hhom\<^sub>C.ide f" and f': "hhom\<^sub>C.ide f'"
          assume "hhom\<^sub>D.in_hom \<nu> (if hhom\<^sub>C.arr f' then F f' else D.null)
                                (if hhom\<^sub>C.arr f then F f else D.null)"
          hence \<nu>: "hhom\<^sub>D.in_hom \<nu> (F f') (F f)"
            using f f' by simp
          have "\<exists>\<mu>. hhom\<^sub>C.in_hom \<mu> f' f \<and> F \<mu> = \<nu>"
          proof -
            have 1: "src\<^sub>C f' = src\<^sub>C f \<and> trg\<^sub>C f' = trg\<^sub>C f"
              using f f' hhom\<^sub>C.ide_char by (metis C.in_hhomE hhom\<^sub>C.arrE)
            hence ex: "\<exists>\<mu>. C.in_hom \<mu> f' f \<and> F \<mu> = \<nu>"
              using f f' \<nu> hhom\<^sub>C.in_hom_char hhom\<^sub>D.in_hom_char hhom\<^sub>C.ide_char locally_full by simp
            obtain \<mu> where \<mu>: "C.in_hom \<mu> f' f \<and> F \<mu> = \<nu>"
              using ex by blast
            have "hhom\<^sub>C.in_hom \<mu> f' f"
            proof -
              have 2: "hhom\<^sub>C.arr f' \<and> hhom\<^sub>C.arr f"
                using f f' hhom\<^sub>C.arr_char hhom\<^sub>C.ide_char by simp
              moreover have "hhom\<^sub>C.arr \<mu>"
                using \<mu> 1 2 hhom\<^sub>C.arr_char C.arrI C.vconn_implies_hpar(1-2) by auto
              ultimately show ?thesis
                using f f' \<mu> hhom\<^sub>C.arr_char hhom\<^sub>C.ide_char hhom\<^sub>C.in_hom_char by simp
            qed
            thus ?thesis
              using \<mu> by auto
          qed
          thus "\<exists>\<mu>. hhom\<^sub>C.in_hom \<mu> f' f \<and> (if hhom\<^sub>C.arr \<mu> then F \<mu> else D.null) = \<nu>"
            by auto
        qed
        show "\<And>g. hhom\<^sub>D.ide g \<Longrightarrow>
                    \<exists>f. hhom\<^sub>C.ide f \<and> hhom\<^sub>D.isomorphic (if hhom\<^sub>C.arr f then F f else D.null) g"
        proof -
          fix g
          assume g: "hhom\<^sub>D.ide g"
          show "\<exists>f. hhom\<^sub>C.ide f \<and> hhom\<^sub>D.isomorphic (if hhom\<^sub>C.arr f then F f else D.null) g"
          proof -
            have "C.obj a \<and> C.obj b"
              using obj_a obj_b by simp
            moreover have 1: "D.ide g \<and> \<guillemotleft>g : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 b\<guillemotright>"
              using g obj_a obj_b hhom\<^sub>D.ide_char by auto
            ultimately have 2: "\<exists>f. C.in_hhom f a b \<and> C.ide f \<and> D.isomorphic (F f) g"
              using locally_essentially_surjective [of a b g] by simp
            obtain f \<phi> where f: "C.in_hhom f a b \<and> C.ide f \<and> D.in_hom \<phi> (F f) g \<and> D.iso \<phi>"
              using 2 by auto
            have "hhom\<^sub>C.ide f"
              using f hhom\<^sub>C.ide_char hhom\<^sub>C.arr_char by simp
            moreover have "hhom\<^sub>D.isomorphic (F f) g"
            proof -
              have "hhom\<^sub>D.arr \<phi> \<and> hhom\<^sub>D.arr (D.inv \<phi>)"
                using f 1 hhom\<^sub>D.arr_char D.in_hhom_def by auto
              hence "hhom\<^sub>D.in_hom \<phi> (F f) g \<and> hhom\<^sub>D.iso \<phi>"
                using f g hhom\<^sub>D.in_hom_char hhom\<^sub>D.iso_char hhom\<^sub>C.arr_char hhom\<^sub>D.arr_char
                      hhom\<^sub>D.ideD(1) preserves_arr
                by simp
              thus ?thesis
                unfolding hhom\<^sub>D.isomorphic_def by blast
            qed
            ultimately show "\<exists>f. hhom\<^sub>C.ide f \<and>
                                 hhom\<^sub>D.isomorphic (if hhom\<^sub>C.arr f then F f else D.null) g"
              by force
          qed
        qed
      qed
      show ?thesis ..
    qed

  end

  context identity_pseudofunctor
  begin

    sublocale equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B map cmp
    proof
      show "\<And>f f'. \<lbrakk>B.par f f'; map f = map f'\<rbrakk> \<Longrightarrow> f = f'"
        by simp
      show "\<And>a'. B.obj a' \<Longrightarrow> \<exists>a. B.obj a \<and> B.equivalent_objects (map\<^sub>0 a) a'"
      proof -
        fix a'
        assume a': "B.obj a'"
        have "B.obj a' \<and> B.equivalent_objects (map\<^sub>0 a') a'"
          using a' by (simp add: B.equivalent_objects_reflexive B.obj_def map\<^sub>0_def)
        thus "\<exists>a. B.obj a \<and> B.equivalent_objects (map\<^sub>0 a) a'" by auto
      qed
      show "\<And>a b g. \<lbrakk>B.obj a; B.obj b; B.in_hhom g (map\<^sub>0 a) (map\<^sub>0 b); B.ide g\<rbrakk>
                       \<Longrightarrow> \<exists>f. B.in_hhom f a b \<and> B.ide f \<and> B.isomorphic (map f) g"
        using B.isomorphic_reflexive B.obj_def map\<^sub>0_def by auto
      show "\<And>f f' \<nu>. \<lbrakk>B.ide f; B.ide f'; src\<^sub>B f = src\<^sub>B f'; trg\<^sub>B f = trg\<^sub>B f';
                      \<guillemotleft>\<nu> : map f \<rightarrow>\<^sub>B map f'\<guillemotright>\<rbrakk>
                       \<Longrightarrow> \<exists>\<mu>. \<guillemotleft>\<mu> : f \<rightarrow>\<^sub>B f'\<guillemotright> \<and> map \<mu> = \<nu>"
        using B.arrI by auto
     qed

     lemma is_equivalence_pseudofunctor:
     shows "equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B map cmp"
       ..

  end

  locale composite_equivalence_pseudofunctor =
    composite_pseudofunctor +
    F: equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F +
    G: equivalence_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G
  begin

    interpretation faithful_functor V\<^sub>B V\<^sub>D \<open>G o F\<close>
      using F.faithful_functor_axioms G.faithful_functor_axioms faithful_functors_compose
      by blast

    interpretation equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>G o F\<close> \<Phi>
    proof
      show "\<And>c. D.obj c \<Longrightarrow> \<exists>a. B.obj a \<and> D.equivalent_objects (map\<^sub>0 a) c"
      proof -
        fix c
        assume c: "D.obj c"
        obtain b where b: "C.obj b \<and> D.equivalent_objects (G.map\<^sub>0 b) c"
          using c G.biessentially_surjective_on_objects by auto
        obtain a where a: "B.obj a \<and> C.equivalent_objects (F.map\<^sub>0 a) b"
          using b F.biessentially_surjective_on_objects by auto
        have "D.equivalent_objects (map\<^sub>0 a) c"
        proof -
          have "map\<^sub>0 a = G.map\<^sub>0 (F.map\<^sub>0 a)"
            using a map\<^sub>0_def by auto
          also have "D.equivalent_objects ... (G.map\<^sub>0 b)"
            using a G.preserves_equivalent_objects by simp
          also have "D.equivalent_objects ... c"
            using b by simp
          finally show ?thesis by simp
        qed
        thus "\<exists>a. B.obj a \<and> D.equivalent_objects (map\<^sub>0 a) c"
          using a by auto
      qed
      show "\<And>a a' h. \<lbrakk>B.obj a; B.obj a'; \<guillemotleft>h : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a'\<guillemotright>; D.ide h\<rbrakk>
                 \<Longrightarrow> \<exists>f. B.in_hhom f a a' \<and> B.ide f \<and> D.isomorphic ((G \<circ> F) f) h"
      proof -
        fix a a' h
        assume a: "B.obj a" and a': "B.obj a'"
        and h_in_hom: "\<guillemotleft>h : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a'\<guillemotright>" and ide_h: "D.ide h"
        obtain g where g: "C.in_hhom g (F.map\<^sub>0 a) (F.map\<^sub>0 a') \<and> C.ide g \<and> D.isomorphic (G g) h"
          using a a' h_in_hom ide_h map\<^sub>0_def B.obj_def
                G.locally_essentially_surjective [of "F.map\<^sub>0 a" "F.map\<^sub>0 a'" h]
          by auto
        obtain f where f: "B.in_hhom f a a' \<and> B.ide f \<and> C.isomorphic (F f) g"
          using a a' g F.locally_essentially_surjective by blast
        have "D.isomorphic ((G o F) f) h"
        proof -
          have "(G o F) f = G (F f)"
            by simp
          also have "D.isomorphic ... (G g)"
            using f G.preserves_iso D.isomorphic_def by blast
          also have "D.isomorphic ... h"
            using g by simp
          finally show "D.isomorphic ((G \<circ> F) f) h" by simp
        qed
        thus "\<exists>f. B.in_hhom f a a' \<and> B.ide f \<and> D.isomorphic ((G \<circ> F) f) h"
          using f by auto
      qed
      show "\<And>f f' \<nu>. \<lbrakk>B.ide f; B.ide f'; src\<^sub>B f = src\<^sub>B f'; trg\<^sub>B f = trg\<^sub>B f';
                       \<guillemotleft>\<nu> : (G \<circ> F) f \<Rightarrow>\<^sub>D (G \<circ> F) f'\<guillemotright>\<rbrakk>
                 \<Longrightarrow> \<exists>\<tau>. \<guillemotleft>\<tau> : f \<rightarrow>\<^sub>B f'\<guillemotright> \<and> (G \<circ> F) \<tau> = \<nu>"
      proof -
        fix f f' \<nu>
        assume f: "B.ide f" and f': "B.ide f'"
        and src: "src\<^sub>B f = src\<^sub>B f'" and trg: "trg\<^sub>B f = trg\<^sub>B f'"
        and \<nu>: "\<guillemotleft>\<nu> : (G \<circ> F) f \<Rightarrow>\<^sub>D (G \<circ> F) f'\<guillemotright>"
        have \<nu>: "\<guillemotleft>\<nu> : G (F f) \<Rightarrow>\<^sub>D G (F f')\<guillemotright>"
          using \<nu> by simp
        have 1: "src\<^sub>C (F f) = src\<^sub>C (F f') \<and> trg\<^sub>C (F f) = trg\<^sub>C (F f')"
          using f f' src trg by simp
        have 2: "\<exists>\<mu>. \<guillemotleft>\<mu> : F f \<Rightarrow>\<^sub>C F f'\<guillemotright> \<and> G \<mu> = \<nu>"
          using f f' 1 \<nu> G.locally_full [of "F f" "F f'" \<nu>] F.preserves_ide by simp
        obtain \<mu> where \<mu>: "\<guillemotleft>\<mu> : F f \<Rightarrow>\<^sub>C F f'\<guillemotright> \<and> G \<mu> = \<nu>"
          using 2 by auto
        obtain \<tau> where \<tau>: "\<guillemotleft>\<tau> : f \<rightarrow>\<^sub>B f'\<guillemotright> \<and> F \<tau> = \<mu>"
          using f f' src trg 2 \<mu> F.locally_full [of f f' \<mu>] by blast
        show "\<exists>\<tau>. \<guillemotleft>\<tau> : f \<rightarrow>\<^sub>B f'\<guillemotright> \<and> (G \<circ> F) \<tau> = \<nu>"
          using \<mu> \<tau> by auto
      qed
    qed

    sublocale equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>G o F\<close> \<Phi> ..

    lemma is_equivalence_pseudofunctor:
    shows "equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (G o F) \<Phi>"
      ..

  end

  text \<open>
    As previously stated, I have been trying to avoid, as part of the current project,
    a full development of pseudonatural transformations and equivalences of bicategories.
    I have chosen instead to define the notion of an equivalence pseudofunctor and to
    define two bicategories to be equivalent if there exists an equivalence pseudofunctor
    between them.  However I cannot avoid needing to show that the relation of ``equivalence''
    so defined is at least a symmetric relation.  To do that requires showing how
    to construct, given an equivalence pseudofunctor, an equivalence pseudofunctor going
    in the opposite direction.  That is the purpose of the next section.  A fuller development
    would define the notion ``equivalence of bicategories'' in terms of pseudofunctors and
    pseudonatural equivalences and would show that a pseudofunctor is an equivalence
    pseudofunctor if and only if it extends to an equivalence of bicategories.
    I am leaving such a development for future work.
  \<close>

  locale converse_equivalence_pseudofunctor =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: equivalence_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F
  for V\<^sub>C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>F :: "'c * 'c \<Rightarrow> 'd"
  begin

    notation C.isomorphic (infix "\<cong>\<^sub>C" 50)
    notation D.isomorphic (infix "\<cong>\<^sub>D" 50)

    (*
     * TODO: export a neutral name for the defined pseudofunctor, such as "map" or "this".
     *)

    text \<open>
      Specification of the object map of the converse pseudofunctor uses surjectivity
      on objects up to equivalence, and will in general involve a choice.
    \<close>

    definition G\<^sub>0
    where "G\<^sub>0 a' \<equiv> SOME a. C.obj a \<and> D.equivalent_objects a' (F.map\<^sub>0 a)"

    lemma G\<^sub>0_preserves_obj:
    assumes "D.obj a'"
    shows "C.obj (G\<^sub>0 a')"
    and "D.equivalent_objects a' (F.map\<^sub>0 (G\<^sub>0 a'))"
      using assms G\<^sub>0_def F.biessentially_surjective_on_objects [of a']
            someI_ex [of "\<lambda>a. C.obj a \<and> D.equivalent_objects a' (F.map\<^sub>0 a)"]
            D.equivalent_objects_symmetric
      by auto

    text \<open>
      We obtain, for each object \<open>a'\<close> of \<open>D\<close>, the data for an equivalence between
      \<open>F.map\<^sub>0 (G\<^sub>0 a')\<close> and \<open>a'\<close>.
    \<close>

    definition e
    where "e a' \<equiv> SOME e. \<guillemotleft>e : a' \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 a')\<guillemotright> \<and> D.equivalence_map e"

    definition d
    where "d a' \<equiv> SOME d. D.equivalence_pair (e a') d"

    lemma equivalence_map_e:
    assumes "D.obj a'"
    shows "\<guillemotleft>e a' : a' \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 a')\<guillemotright> \<and> D.equivalence_map (e a')"
    proof -
      have "C.obj (G\<^sub>0 a') \<and> D.equivalent_objects a' (F.map\<^sub>0 (G\<^sub>0 a'))"
        using assms G\<^sub>0_preserves_obj by simp
      hence "\<exists>e d \<eta> \<epsilon>. \<guillemotleft>e : a' \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 a')\<guillemotright> \<and>
                          equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D e d \<eta> \<epsilon>"
        using D.equivalent_objects_def D.equivalence_map_def by auto
      thus ?thesis
        using e_def D.equivalence_map_def
              someI_ex [of "\<lambda>e. \<guillemotleft>e : a' \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 a')\<guillemotright> \<and> D.equivalence_map e"]
        by simp
    qed

    lemma e_in_hom [intro]:
    assumes "D.obj a'"
    shows "\<guillemotleft>e a' : a' \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 a')\<guillemotright>"
      using assms equivalence_map_e by simp

    lemma e_simps [simp]:
    assumes "D.obj a'"
    shows "D.ide (e a')" and "D.equivalence_map (e a')"
    and "src\<^sub>D (e a') = a'" and "trg\<^sub>D (e a') = F.map\<^sub>0 (G\<^sub>0 a')"
    proof -
      show "D.equivalence_map (e a')"
        using assms equivalence_map_e by simp
      thus "D.ide (e a')"
        using assms D.equivalence_map_is_ide by simp
      show "src\<^sub>D (e a') = a'"
        using assms e_in_hom by auto
      show "trg\<^sub>D (e a') = F.map\<^sub>0 (G\<^sub>0 a')"
        using assms e_in_hom by auto
    qed

    lemma equivalence_map_d:
    assumes "D.obj a'"
    shows "D.equivalence_pair (e a') (d a')"
    and "\<guillemotleft>d a' : F.map\<^sub>0 (G\<^sub>0 a') \<rightarrow>\<^sub>D a'\<guillemotright> \<and> D.equivalence_map (d a')"
    proof -
      have "\<exists>d. D.equivalence_pair (e a') d"
        using assms equivalence_map_e D.equivalence_map_def D.equivalence_pair_def
        by (meson D.equivalent_objects_def D.equivalent_objects_symmetric)
      thus 1: "D.equivalence_pair (e a') (d a')"
        using d_def someI_ex [of "\<lambda>d. D.equivalence_pair (e a') d"] by simp
      obtain \<eta> \<epsilon> where \<eta>\<epsilon>: "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (e a') (d a') \<eta> \<epsilon>"
        using 1 D.equivalence_pair_def by auto
      interpret equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>e a'\<close> \<open>d a'\<close> \<eta> \<epsilon>
        using \<eta>\<epsilon> by simp
      show "\<guillemotleft>d a' : F.map\<^sub>0 (G\<^sub>0 a') \<rightarrow>\<^sub>D a'\<guillemotright> \<and> D.equivalence_map (d a')"
        using assms antipar D.equivalence_map_def dual_equivalence by auto
    qed

    lemma d_in_hom [intro]:
    assumes "D.obj a'"
    shows "\<guillemotleft>d a' : F.map\<^sub>0 (G\<^sub>0 a') \<rightarrow>\<^sub>D a'\<guillemotright>"
      using assms equivalence_map_d by simp

    lemma d_simps [simp]:
    assumes "D.obj a'"
    shows "D.ide (d a')"
    and "src\<^sub>D (d a') = F.map\<^sub>0 (G\<^sub>0 a')" and "trg\<^sub>D (d a') = a'"
    proof -
      show "D.ide (d a')"
        using assms equivalence_map_d D.equivalence_map_is_ide by simp
      show "src\<^sub>D (d a') = F.map\<^sub>0 (G\<^sub>0 a')"
        using assms d_in_hom by auto
      show "trg\<^sub>D (d a') = a'"
        using assms d_in_hom by auto
    qed

    text \<open>
      Next, we specify how the converse pseudofunctor behaves on identities (1-cells).
      This uses local essential surjectivity and also involves a choice.
    \<close>

    definition G\<^sub>1
    where "G\<^sub>1 f' \<equiv> SOME f. C.ide f \<and> \<guillemotleft>f : G\<^sub>0 (src\<^sub>D f') \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D f')\<guillemotright> \<and>
                           F f \<cong>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')"

    lemma FG\<^sub>1_iso:
    assumes "D.ide f'"
    shows "C.ide (G\<^sub>1 f')"
    and "\<guillemotleft>G\<^sub>1 f' : G\<^sub>0 (src\<^sub>D f') \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D f')\<guillemotright>"
    and "F (G\<^sub>1 f') \<cong>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')"
    proof -
      have "\<exists>f. C.ide f \<and> \<guillemotleft>f : G\<^sub>0 (src\<^sub>D f') \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D f')\<guillemotright> \<and>
                F f \<cong>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')"
        using assms
              F.locally_essentially_surjective
                [of "G\<^sub>0 (src\<^sub>D f')" "G\<^sub>0 (trg\<^sub>D f')" "e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')"]
              G\<^sub>0_preserves_obj D.equivalent_objects_def
        by auto
      hence 1: "C.ide (G\<^sub>1 f') \<and> \<guillemotleft>G\<^sub>1 f' : G\<^sub>0 (src\<^sub>D f') \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D f')\<guillemotright> \<and>
                F (G\<^sub>1 f') \<cong>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')"
        using G\<^sub>1_def someI_ex [of "\<lambda>f. C.ide f \<and> \<guillemotleft>f : G\<^sub>0 (src\<^sub>D f') \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D f')\<guillemotright> \<and>
                                       F f \<cong>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')"]
        by simp
      show "C.ide (G\<^sub>1 f')"
        using 1 by simp
      show "\<guillemotleft>G\<^sub>1 f' : G\<^sub>0 (src\<^sub>D f') \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D f')\<guillemotright>"
        using 1 by simp
      show "F (G\<^sub>1 f') \<cong>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')"
        using 1 by simp
    qed

    text \<open>
      We need to choose a specific isomorphism between \<open>F (G\<^sub>1 f')\<close> and
      \<open>e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')\<close>.
    \<close>

    definition \<phi>
    where "\<phi> f' \<equiv> SOME \<phi>. \<guillemotleft>\<phi> : F (G\<^sub>1 f') \<Rightarrow>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')\<guillemotright> \<and> D.iso \<phi>"

    lemma \<phi>_props:
    assumes "D.ide f'"
    shows "\<guillemotleft>\<phi> f' : F (G\<^sub>1 f') \<Rightarrow>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')\<guillemotright>"
    and "D.iso (\<phi> f')"
    proof -
      have "\<exists>\<phi>. \<guillemotleft>\<phi> : F (G\<^sub>1 f') \<Rightarrow>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')\<guillemotright> \<and> D.iso \<phi>"
        using assms FG\<^sub>1_iso by blast
      hence 1: "\<guillemotleft>\<phi> f' : F (G\<^sub>1 f') \<Rightarrow>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')\<guillemotright> \<and> D.iso (\<phi> f')"
        using \<phi>_def
              someI_ex [of "\<lambda>\<phi>. \<guillemotleft>\<phi> : F (G\<^sub>1 f') \<Rightarrow>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')\<guillemotright> \<and> D.iso \<phi>"]
        by simp
      show "\<guillemotleft>\<phi> f' : F (G\<^sub>1 f') \<Rightarrow>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')\<guillemotright>"
        using 1 by simp
      show "D.iso (\<phi> f')"
        using 1 by simp
    qed

    text \<open>
      The behavior of the converse pseudofunctor on arrows (2-cells) is now determined
      by local fullness.  We have used indefinite choice in the definition here,
      but in fact the choice is unique due to faithfulness.
    \<close>

    definition G
    where "G \<mu>' \<equiv> if D.arr \<mu>' then
                     SOME \<mu>. \<guillemotleft>\<mu> : G\<^sub>1 (D.dom \<mu>') \<Rightarrow>\<^sub>C G\<^sub>1 (D.cod \<mu>')\<guillemotright> \<and>
                             F \<mu> = D.inv (\<phi> (D.cod \<mu>')) \<cdot>\<^sub>D
                                     (e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')) \<cdot>\<^sub>D \<phi> (D.dom \<mu>')
                   else
                     C.null"

    lemma FG_eq:
    assumes "D.arr \<mu>'"
    shows "\<guillemotleft>G \<mu>' : G\<^sub>1 (D.dom \<mu>') \<Rightarrow>\<^sub>C G\<^sub>1 (D.cod \<mu>')\<guillemotright>"
    and "F (G \<mu>') = D.inv (\<phi> (D.cod \<mu>')) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')) \<cdot>\<^sub>D \<phi> (D.dom \<mu>')"
    proof -
      have "C.ide (G\<^sub>1 (D.dom \<mu>'))"
        using assms FG\<^sub>1_iso by simp
      moreover have "C.ide (G\<^sub>1 (D.cod \<mu>'))"
        using assms FG\<^sub>1_iso by simp
      moreover have "src\<^sub>C (G\<^sub>1 (D.dom \<mu>')) = src\<^sub>C (G\<^sub>1 (D.cod \<mu>'))"
        using assms FG\<^sub>1_iso
        by (metis C.in_hhomE D.ide_cod D.ide_dom D.src_cod D.src_dom)
      moreover have "trg\<^sub>C (G\<^sub>1 (D.dom \<mu>')) = trg\<^sub>C (G\<^sub>1 (D.cod \<mu>'))"
        using assms FG\<^sub>1_iso
        by (metis C.in_hhomE D.ide_cod D.ide_dom D.trg_cod D.trg_dom)
      moreover have
        "\<guillemotleft>D.inv (\<phi> (D.cod \<mu>')) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')) \<cdot>\<^sub>D \<phi> (D.dom \<mu>') :
            F (G\<^sub>1 (D.dom \<mu>')) \<Rightarrow>\<^sub>D F (G\<^sub>1 (D.cod \<mu>'))\<guillemotright>"
      proof (intro D.comp_in_homI)
        show "\<guillemotleft>\<phi> (D.dom \<mu>') :
                 F (G\<^sub>1 (D.dom \<mu>')) \<Rightarrow>\<^sub>D
                   e (trg\<^sub>D (D.dom \<mu>')) \<star>\<^sub>D D.dom \<mu>' \<star>\<^sub>D d (src\<^sub>D (D.dom \<mu>'))\<guillemotright>"
          using assms \<phi>_props [of "D.dom \<mu>'"] by simp
        show "\<guillemotleft>e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>') :
                 e (trg\<^sub>D (D.dom \<mu>')) \<star>\<^sub>D D.dom \<mu>' \<star>\<^sub>D d (src\<^sub>D (D.dom \<mu>')) \<Rightarrow>\<^sub>D
                 e (trg\<^sub>D (D.cod \<mu>')) \<star>\<^sub>D D.cod \<mu>' \<star>\<^sub>D d (src\<^sub>D (D.cod \<mu>'))\<guillemotright>"
          using assms by (intro D.hcomp_in_vhom, auto)
        show "\<guillemotleft>D.inv (\<phi> (D.cod \<mu>')) :
                 e (trg\<^sub>D (D.cod \<mu>')) \<star>\<^sub>D D.cod \<mu>' \<star>\<^sub>D d (src\<^sub>D (D.cod \<mu>')) \<Rightarrow>\<^sub>D F (G\<^sub>1 (D.cod \<mu>'))\<guillemotright>"
          using assms \<phi>_props D.ide_cod D.inv_in_hom by presburger
      qed
      ultimately have
        "\<exists>\<mu>. \<guillemotleft>\<mu> : G\<^sub>1 (D.dom \<mu>') \<Rightarrow>\<^sub>C G\<^sub>1 (D.cod \<mu>')\<guillemotright> \<and>
             F \<mu> = D.inv (\<phi> (D.cod \<mu>')) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')) \<cdot>\<^sub>D \<phi> (D.dom \<mu>')"
        by (simp add: F.locally_full)
      hence 1: "\<guillemotleft>G \<mu>' : G\<^sub>1 (D.dom \<mu>') \<Rightarrow>\<^sub>C G\<^sub>1 (D.cod \<mu>')\<guillemotright> \<and>
                F (G \<mu>') =
                D.inv (\<phi> (D.cod \<mu>')) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')) \<cdot>\<^sub>D \<phi> (D.dom \<mu>')"
        using assms G_def
              someI_ex [of "\<lambda>\<mu>. \<guillemotleft>\<mu> : G\<^sub>1 (D.dom \<mu>') \<Rightarrow>\<^sub>C G\<^sub>1 (D.cod \<mu>')\<guillemotright> \<and>
                                F \<mu> = D.inv (\<phi> (D.cod \<mu>')) \<cdot>\<^sub>D
                                        (e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')) \<cdot>\<^sub>D \<phi> (D.dom \<mu>')"]
        by simp
      show "\<guillemotleft>G \<mu>' : G\<^sub>1 (D.dom \<mu>') \<Rightarrow>\<^sub>C G\<^sub>1 (D.cod \<mu>')\<guillemotright>"
        using 1 by simp
      show "F (G \<mu>') = D.inv (\<phi> (D.cod \<mu>')) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')) \<cdot>\<^sub>D \<phi> (D.dom \<mu>')"
        using 1 by simp
    qed

    lemma G_ide:
    assumes "D.ide f'"
    shows "G f' = G\<^sub>1 f'"
    proof -
      have "F (G f') =
            D.inv (\<phi> (D.cod f')) \<cdot>\<^sub>D (e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')) \<cdot>\<^sub>D \<phi> (D.dom f')"
        using assms FG_eq by simp
      also have "... = D.inv (\<phi> f') \<cdot>\<^sub>D \<phi> f'"
        using assms \<phi>_props [of f'] D.comp_cod_arr by auto
      also have "... = F (G\<^sub>1 f')"
        using assms \<phi>_props D.comp_inv_arr' by auto
      finally have "F (G f') = F (G\<^sub>1 f')" by simp
      thus ?thesis
        using assms FG_eq FG\<^sub>1_iso F.is_faithful
        by (metis C.ideD(3) C.in_homE D.ideD(1-3) F.locally_reflects_ide F.preserves_ide)
    qed

    lemma G_in_hom [intro]:
    assumes "D.arr \<mu>'"
    shows "\<guillemotleft>G \<mu>' : G\<^sub>0 (src\<^sub>D \<mu>') \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D \<mu>')\<guillemotright>"
    and "\<guillemotleft>G \<mu>' : G (D.dom \<mu>') \<Rightarrow>\<^sub>C G (D.cod \<mu>')\<guillemotright>"
    proof -
      show "\<guillemotleft>G \<mu>' : G (D.dom \<mu>') \<Rightarrow>\<^sub>C G (D.cod \<mu>')\<guillemotright>"
        using assms FG_eq G_ide by simp
      thus "\<guillemotleft>G \<mu>' : G\<^sub>0 (src\<^sub>D \<mu>') \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D \<mu>')\<guillemotright>"
        using assms FG\<^sub>1_iso G_ide
        by (metis C.arrI C.ide_in_hom(2) C.in_hhom_def C.seqI' C.vseq_implies_hpar(1)
            C.vseq_implies_hpar(2) D.ide_dom D.src_dom D.trg_dom)
    qed

    lemma G_simps [simp]:
    assumes "D.arr \<mu>'"
    shows "C.arr (G \<mu>')"
    and "src\<^sub>C (G \<mu>') = G\<^sub>0 (src\<^sub>D \<mu>')" and "trg\<^sub>C (G \<mu>') = G\<^sub>0 (trg\<^sub>D \<mu>')"
    and "C.dom (G \<mu>') = G (D.dom \<mu>')" and "C.cod (G \<mu>') = G (D.cod \<mu>')"
      using assms G_in_hom by auto

    lemma \<phi>_in_hom [intro]:
    assumes "D.ide f'"
    shows "\<guillemotleft>\<phi> f' : F.map\<^sub>0 (G\<^sub>0 (src\<^sub>D f')) \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 (trg\<^sub>D f'))\<guillemotright>"
    and "\<guillemotleft>\<phi> f' : F (G f') \<Rightarrow>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')\<guillemotright>"
    proof -
      show "\<guillemotleft>\<phi> f' : F (G f') \<Rightarrow>\<^sub>D e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')\<guillemotright>"
        using assms \<phi>_props G_ide by auto
      thus "\<guillemotleft>\<phi> f' : F.map\<^sub>0 (G\<^sub>0 (src\<^sub>D f')) \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 (trg\<^sub>D f'))\<guillemotright>"
        using assms \<phi>_props d_simps e_simps
              D.src_cod [of "\<phi> f'"] D.trg_cod [of "\<phi> f'"]
        by fastforce
    qed

    lemma \<phi>_simps [simp]:
    assumes "D.ide f'"
    shows "D.arr (\<phi> f')"
    and "src\<^sub>D (\<phi> f') = F.map\<^sub>0 (G\<^sub>0 (src\<^sub>D f'))" and "trg\<^sub>D (\<phi> f') = F.map\<^sub>0 (G\<^sub>0 (trg\<^sub>D f'))"
    and "D.dom (\<phi> f') = F (G f')" and "D.cod (\<phi> f') = e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')"
      using assms \<phi>_in_hom by auto

    interpretation G: "functor" V\<^sub>D V\<^sub>C G
    proof
      show "\<And>\<mu>'. \<not> D.arr \<mu>' \<Longrightarrow> G \<mu>' = C.null"
        using G_def by simp
      show A: "\<And>\<mu>'. D.arr \<mu>' \<Longrightarrow> C.arr (G \<mu>')"
        by simp
      show D: "\<And>\<mu>'. D.arr \<mu>' \<Longrightarrow> C.dom (G \<mu>') = G (D.dom \<mu>')"
        by simp
      show C: "\<And>\<mu>'. D.arr \<mu>' \<Longrightarrow> C.cod (G \<mu>') = G (D.cod \<mu>')"
        by simp
      show "\<And>\<mu> \<nu>. D.seq \<mu> \<nu> \<Longrightarrow> G (\<mu> \<cdot>\<^sub>D \<nu>) = G \<mu> \<cdot>\<^sub>C G \<nu>"
      proof -
        fix \<mu> \<nu>
        assume \<mu>\<nu>: "D.seq \<mu> \<nu>"
        have \<mu>: "\<guillemotleft>\<mu> : src\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>) \<rightarrow>\<^sub>D trg\<^sub>D \<mu>\<guillemotright>"
          using \<mu>\<nu> D.vseq_implies_hpar
          by (intro D.in_hhomI, auto)
        have \<nu>: "\<guillemotleft>\<nu> : src\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>) \<rightarrow>\<^sub>D trg\<^sub>D \<nu>\<guillemotright>"
          using \<mu>\<nu> D.vseq_implies_hpar
          by (intro D.in_hhomI, auto)
        have "F (G (\<mu> \<cdot>\<^sub>D \<nu>)) =
              D.inv (\<phi> (D.cod (\<mu> \<cdot>\<^sub>D \<nu>))) \<cdot>\<^sub>D
                (e (trg\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>)) \<star>\<^sub>D \<mu> \<cdot>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>))) \<cdot>\<^sub>D
                \<phi> (D.dom (\<mu> \<cdot>\<^sub>D \<nu>))"
          using \<mu>\<nu> FG_eq by simp
        also have "... =
                   D.inv (\<phi> (D.cod (\<mu> \<cdot>\<^sub>D \<nu>))) \<cdot>\<^sub>D
                     (e (trg\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>)) \<star>\<^sub>D (\<mu> \<star>\<^sub>D d (src\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>))) \<cdot>\<^sub>D (\<nu> \<star>\<^sub>D d (src\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>)))) \<cdot>\<^sub>D
                     \<phi> (D.dom (\<mu> \<cdot>\<^sub>D \<nu>))"
          using \<mu>\<nu> D.whisker_right D.obj_src d_simps(1) by presburger
        also have "... = D.inv (\<phi> (D.cod (\<mu> \<cdot>\<^sub>D \<nu>))) \<cdot>\<^sub>D
                           ((e (trg\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>)) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>))) \<cdot>\<^sub>D
                           (e (trg\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>)) \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>)))) \<cdot>\<^sub>D
                           \<phi> (D.dom (\<mu> \<cdot>\<^sub>D \<nu>))"
        proof -
          have "D.seq (\<mu> \<star>\<^sub>D d (src\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>))) (\<nu> \<star>\<^sub>D d (src\<^sub>D (\<mu> \<cdot>\<^sub>D \<nu>)))"
            using \<mu> \<nu> \<mu>\<nu> D.obj_src d_simps(1) by fastforce
          thus ?thesis
            using \<mu>\<nu> D.obj_src D.obj_trg D.whisker_left e_simps(1) by presburger
        qed
        also have "... = D.inv (\<phi> (D.cod \<mu>)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D \<nu>) \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D
                           \<phi> (D.dom \<nu>)"
          using \<mu>\<nu> D.vseq_implies_hpar(1) D.vseq_implies_hpar(2) D.comp_assoc by auto
        also have "... = D.inv (\<phi> (D.cod \<mu>)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D
                           (\<phi> (D.dom \<mu>) \<cdot>\<^sub>D D.inv (\<phi> (D.cod \<nu>))) \<cdot>\<^sub>D
                           (e (trg\<^sub>D \<nu>) \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D
                           \<phi> (D.dom \<nu>)"
        proof -
          have "\<phi> (D.dom \<mu>) \<cdot>\<^sub>D D.inv (\<phi> (D.cod \<nu>)) =
                D.cod ((e (trg\<^sub>D \<nu>) \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D \<phi> (D.dom \<nu>))"
            using \<mu> \<nu> D.obj_src D.obj_trg \<mu>\<nu> \<phi>_props D.comp_arr_inv' D.ide_cod by auto
          thus ?thesis
            using \<mu>\<nu> \<phi>_props D.comp_cod_arr
            by (metis D.seqE A calculation F.preserves_arr)
        qed
        also have "... =
                   (D.inv (\<phi> (D.cod \<mu>)) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<phi> (D.dom \<mu>)) \<cdot>\<^sub>D
                   (D.inv (\<phi> (D.cod \<nu>)) \<cdot>\<^sub>D (e (trg\<^sub>D \<nu>) \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D \<phi> (D.dom \<nu>))"
          using D.comp_assoc by simp
        also have "... = F (G \<mu> \<cdot>\<^sub>C G \<nu>)"
          using \<mu>\<nu> A D C FG_eq D.seqE by auto
        finally have "F (G (\<mu> \<cdot>\<^sub>D \<nu>)) = F (G \<mu> \<cdot>\<^sub>C G \<nu>)"
          by simp
        moreover have "C.par (G (\<mu> \<cdot>\<^sub>D \<nu>)) (G \<mu> \<cdot>\<^sub>C G \<nu>)"
          using \<mu>\<nu> A D C by fastforce
        ultimately show "G (\<mu> \<cdot>\<^sub>D \<nu>) = G \<mu> \<cdot>\<^sub>C G \<nu>"
          using F.is_faithful by blast
      qed
    qed

    definition \<eta>
    where "\<eta> a' \<equiv>
           SOME \<eta>. \<exists>\<epsilon>. equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (e a') (d a') \<eta> \<epsilon>"

    definition \<epsilon>
    where "\<epsilon> a' \<equiv>
           SOME \<epsilon>. equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (e a') (d a') (\<eta> a') \<epsilon>"

    lemma equivalence_ed\<eta>\<epsilon>:
    assumes "D.obj a'"
    shows "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (e a') (d a') (\<eta> a') (\<epsilon> a')"
    proof -
      have 1: "\<exists>\<eta> \<epsilon>. equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (e a') (d a') \<eta> \<epsilon>"
        using assms equivalence_map_d D.equivalence_pair_def by simp
      thus ?thesis
        using \<eta>_def \<epsilon>_def
              someI_ex
                 [of "\<lambda>\<eta>. \<exists>\<epsilon>. equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (e a') (d a') \<eta> \<epsilon>"]
              someI_ex
                 [of "\<lambda>\<epsilon>. equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (e a') (d a') (\<eta> a') \<epsilon>"]
        by simp
    qed

    lemma \<eta>_in_hom [intro]:
    assumes "D.obj a'"
    shows "\<guillemotleft>\<eta> a' : src\<^sub>D (e a') \<rightarrow>\<^sub>D src\<^sub>D (e a')\<guillemotright>"
    and "\<guillemotleft>\<eta> a' : src\<^sub>D (e a') \<Rightarrow>\<^sub>D d a' \<star>\<^sub>D e a'\<guillemotright>"
    proof -
      interpret equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>e a'\<close> \<open>d a'\<close> \<open>\<eta> a'\<close> \<open>\<epsilon> a'\<close>
        using assms equivalence_ed\<eta>\<epsilon> by simp
      show "\<guillemotleft>\<eta> a' : src\<^sub>D (e a') \<rightarrow>\<^sub>D src\<^sub>D (e a')\<guillemotright>"
        by simp
      show "\<guillemotleft>\<eta> a' : src\<^sub>D (e a') \<Rightarrow>\<^sub>D d a' \<star>\<^sub>D e a'\<guillemotright>"
        by auto
    qed

    lemma iso_\<eta>:
    assumes "D.obj a'"
    shows "D.iso (\<eta> a')"
      using assms
      by (meson equivalence_ed\<eta>\<epsilon> equivalence_in_bicategory.unit_is_iso)

    lemma \<epsilon>_in_hom [intro]:
    assumes "D.obj a'"
    shows "\<guillemotleft>\<epsilon> a' : trg\<^sub>D (e a') \<rightarrow>\<^sub>D trg\<^sub>D (e a')\<guillemotright>"
    and "\<guillemotleft>\<epsilon> a' : e a' \<star>\<^sub>D d a' \<Rightarrow>\<^sub>D trg\<^sub>D (e a')\<guillemotright>"
    proof -
      interpret equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>e a'\<close> \<open>d a'\<close> \<open>\<eta> a'\<close> \<open>\<epsilon> a'\<close>
        using assms equivalence_ed\<eta>\<epsilon> by simp
      show "\<guillemotleft>\<epsilon> a' : trg\<^sub>D (e a') \<rightarrow>\<^sub>D trg\<^sub>D (e a')\<guillemotright>"
        by simp
      show "\<guillemotleft>\<epsilon> a' : e a' \<star>\<^sub>D d a' \<Rightarrow>\<^sub>D trg\<^sub>D (e a')\<guillemotright>"
        by auto
    qed

    lemma iso_\<epsilon>:
    assumes "D.obj a'"
    shows "D.iso (\<epsilon> a')"
      using assms
      by (meson equivalence_ed\<eta>\<epsilon> equivalence_in_bicategory.counit_is_iso)

    interpretation G: weak_arrow_of_homs V\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C src\<^sub>C trg\<^sub>C G
    proof
      fix \<mu>'
      assume \<mu>': "D.arr \<mu>'"
      show "G (src\<^sub>D \<mu>') \<cong>\<^sub>C src\<^sub>C (G \<mu>')"
      proof -
        interpret e_src: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                           \<open>e (src\<^sub>D \<mu>')\<close> \<open>d (src\<^sub>D \<mu>')\<close> \<open>\<eta> (src\<^sub>D \<mu>')\<close> \<open>\<epsilon> (src\<^sub>D \<mu>')\<close>
        using \<mu>' equivalence_ed\<eta>\<epsilon> by simp
        have 1: "F (G (src\<^sub>D \<mu>')) \<cong>\<^sub>D F (src\<^sub>C (G \<mu>'))"
        proof -
          have "F (G (src\<^sub>D \<mu>')) \<cong>\<^sub>D F (G\<^sub>1 (src\<^sub>D \<mu>'))"
            using \<mu>' FG\<^sub>1_iso
            by (simp add: D.isomorphic_reflexive G_ide)
          also have "F (G\<^sub>1 (src\<^sub>D \<mu>')) \<cong>\<^sub>D e (src\<^sub>D \<mu>') \<star>\<^sub>D src\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')"
            using \<mu>' FG\<^sub>1_iso [of "src\<^sub>D \<mu>'"] by simp
          also have "D.isomorphic ... (F.map\<^sub>0 (G\<^sub>0 (src\<^sub>D \<mu>')))"
          proof -
            have "\<guillemotleft>\<epsilon> (src\<^sub>D \<mu>') \<cdot>\<^sub>D (e (src\<^sub>D \<mu>') \<star>\<^sub>D \<l>\<^sub>D[d (src\<^sub>D \<mu>')]) :
                      e (src\<^sub>D \<mu>') \<star>\<^sub>D src\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>') \<Rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 (src\<^sub>D \<mu>'))\<guillemotright>"
              using \<mu>' e_src.counit_in_hom by fastforce
            moreover have "D.iso (\<epsilon> (src\<^sub>D \<mu>') \<cdot>\<^sub>D (e (src\<^sub>D \<mu>') \<star>\<^sub>D \<l>\<^sub>D[d (src\<^sub>D \<mu>')]))"
              using \<mu>' D.isos_compose D.arrI calculation by auto
            ultimately show ?thesis
              using D.isomorphic_def by blast
          qed
          also have "... \<cong>\<^sub>D F (src\<^sub>C (G \<mu>'))"
            using \<mu>' F.weakly_preserves_objects G\<^sub>0_preserves_obj(1) by auto
          finally show ?thesis by blast
        qed
        obtain \<phi>' where \<phi>': "\<guillemotleft>\<phi>' : F (G (src\<^sub>D \<mu>')) \<Rightarrow>\<^sub>D F (src\<^sub>C (G \<mu>'))\<guillemotright> \<and> D.iso \<phi>'"
          using 1 D.isomorphic_def by auto
        have 2: "\<exists>\<mu>. \<guillemotleft>\<mu> : G (src\<^sub>D \<mu>') \<Rightarrow>\<^sub>C src\<^sub>C (G \<mu>')\<guillemotright> \<and> F \<mu> = \<phi>'"
         proof -
          have "C.ide (G (src\<^sub>D \<mu>'))"
            using \<mu>' by simp
          moreover have "src\<^sub>C (G (src\<^sub>D \<mu>')) = src\<^sub>C (src\<^sub>C (G \<mu>'))"
            using \<mu>' C.src_src by fastforce
          moreover have "trg\<^sub>C (G (src\<^sub>D \<mu>')) = trg\<^sub>C (src\<^sub>C (G \<mu>'))"
            using \<mu>' C.trg_src by fastforce
          ultimately show ?thesis
            using \<mu>' \<phi>' F.locally_full [of "G (src\<^sub>D \<mu>')" "src\<^sub>C (G \<mu>')" \<phi>'] C.ide_src
            by blast
        qed
        obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : G (src\<^sub>D \<mu>') \<Rightarrow>\<^sub>C src\<^sub>C (G \<mu>')\<guillemotright> \<and> F \<phi> = \<phi>'"
          using 2 by auto
        have "C.iso \<phi>"
          using \<phi> \<phi>' F.reflects_iso by auto
        thus ?thesis
          using \<phi> C.isomorphic_def by auto
      qed
      show "G (trg\<^sub>D \<mu>') \<cong>\<^sub>C trg\<^sub>C (G \<mu>')"
      proof -
        interpret e_trg: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                           \<open>e (trg\<^sub>D \<mu>')\<close> \<open>d (trg\<^sub>D \<mu>')\<close> \<open>\<eta> (trg\<^sub>D \<mu>')\<close> \<open>\<epsilon> (trg\<^sub>D \<mu>')\<close>
          using \<mu>' equivalence_ed\<eta>\<epsilon> by simp
        have 1: "F (G (trg\<^sub>D \<mu>')) \<cong>\<^sub>D F (trg\<^sub>C (G \<mu>'))"
        proof -
          have "F (G (trg\<^sub>D \<mu>')) \<cong>\<^sub>D F (G\<^sub>1 (trg\<^sub>D \<mu>'))"
            using \<mu>' FG\<^sub>1_iso
            by (simp add: D.isomorphic_reflexive G_ide)
          also have "F (G\<^sub>1 (trg\<^sub>D \<mu>')) \<cong>\<^sub>D e (trg\<^sub>D \<mu>') \<star>\<^sub>D trg\<^sub>D \<mu>' \<star>\<^sub>D d (trg\<^sub>D \<mu>')"
            using \<mu>' FG\<^sub>1_iso [of "trg\<^sub>D \<mu>'"] by simp
          also have "... \<cong>\<^sub>D F.map\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<mu>'))"
          proof -
            have "\<guillemotleft>\<epsilon> (trg\<^sub>D \<mu>') \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<l>\<^sub>D[d (trg\<^sub>D \<mu>')]) :
                     e (trg\<^sub>D \<mu>') \<star>\<^sub>D trg\<^sub>D \<mu>' \<star>\<^sub>D d (trg\<^sub>D \<mu>') \<Rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<mu>'))\<guillemotright>"
              using \<mu>' e_trg.counit_in_hom by fastforce
            moreover have "D.iso (\<epsilon> (trg\<^sub>D \<mu>') \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<l>\<^sub>D[d (trg\<^sub>D \<mu>')]))"
              using \<mu>' D.isos_compose D.arrI calculation by simp
            ultimately show ?thesis
              using D.isomorphic_def by blast
          qed
          also have "... \<cong>\<^sub>D F (trg\<^sub>C (G \<mu>'))"
            using \<mu>' F.weakly_preserves_objects G\<^sub>0_preserves_obj(1) by auto
          finally show ?thesis by blast
        qed
        obtain \<phi>' where \<phi>': "\<guillemotleft>\<phi>' : F (G (trg\<^sub>D \<mu>')) \<Rightarrow>\<^sub>D F (trg\<^sub>C (G \<mu>'))\<guillemotright> \<and> D.iso \<phi>'"
          using 1 D.isomorphic_def by auto
        have 2: "\<exists>\<mu>. \<guillemotleft>\<mu> : G (trg\<^sub>D \<mu>') \<Rightarrow>\<^sub>C trg\<^sub>C (G \<mu>')\<guillemotright> \<and> F \<mu> = \<phi>'"
        proof -
          have "C.ide (G (trg\<^sub>D \<mu>'))"
            using \<mu>' by simp
          moreover have "src\<^sub>C (G (trg\<^sub>D \<mu>')) = src\<^sub>C (trg\<^sub>C (G \<mu>'))"
            using \<mu>' C.src_trg by fastforce
          moreover have "trg\<^sub>C (G (trg\<^sub>D \<mu>')) = trg\<^sub>C (trg\<^sub>C (G \<mu>'))"
            using \<mu>' C.trg_trg by fastforce
          ultimately show ?thesis
            using \<mu>' \<phi>' F.locally_full [of "G (trg\<^sub>D \<mu>')" "trg\<^sub>C (G \<mu>')" \<phi>'] C.ide_trg
            by blast
        qed
        obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : G (trg\<^sub>D \<mu>') \<Rightarrow>\<^sub>C trg\<^sub>C (G \<mu>')\<guillemotright> \<and> F \<phi> = \<phi>'"
          using 2 \<phi>' by auto
        have "C.iso \<phi>"
          using \<phi> \<phi>' F.reflects_iso by auto
        thus ?thesis
          using \<phi> C.isomorphic_def by auto
      qed
    qed

    lemma G_map\<^sub>0_eq_G\<^sub>0 [simp]:
    assumes "D.obj a'"
    shows "G.map\<^sub>0 a' = G\<^sub>0 a'"
      using assms G.map\<^sub>0_def D.obj_def by simp

    interpretation GG: "functor" D.VV.comp C.VV.comp G.FF
      using G.functor_FF by simp
    interpretation GoH\<^sub>D: composite_functor D.VV.comp V\<^sub>D V\<^sub>C
                           \<open>\<lambda>\<mu>\<nu>. H\<^sub>D (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> G
      ..
    interpretation H\<^sub>DoGG: composite_functor D.VV.comp C.VV.comp V\<^sub>C G.FF
                            \<open>\<lambda>\<mu>\<nu>. H\<^sub>C (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close>
      ..

    text \<open>
      We will need a naturality property of \<open>\<phi>\<close>, which amounts to the fact that the \<open>\<phi> f'\<close>
      are the components of a natural transformation from the functor \<open>F \<circ> G\<close> to the
      functor that transports \<open>\<mu>'\<close> to \<open>e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')\<close>.
    \<close>

    interpretation FoG: composite_functor V\<^sub>D V\<^sub>C V\<^sub>D G F ..

    abbreviation (input) XLT
    where "XLT \<mu>' \<equiv> e (trg\<^sub>D \<mu>') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>')"

    interpretation XLT: "functor" V\<^sub>D V\<^sub>D XLT
    proof
      show "\<And>\<mu>'. \<not> D.arr \<mu>' \<Longrightarrow> XLT \<mu>' = D.null"
        using D.hseq_char' by auto
      show 1: "\<And>\<mu>'. D.arr \<mu>' \<Longrightarrow> D.arr (XLT \<mu>')"
        by simp
      show "\<And>\<mu>'. D.arr \<mu>' \<Longrightarrow> D.dom (XLT \<mu>') = XLT (D.dom \<mu>')"
        using 1 by force
      show "\<And>\<mu>'. D.arr \<mu>' \<Longrightarrow> D.cod (XLT \<mu>') = XLT (D.cod \<mu>')"
        using 1 by force
      show "\<And>\<mu>' \<nu>'. D.seq \<mu>' \<nu>' \<Longrightarrow> XLT (\<mu>' \<cdot>\<^sub>D \<nu>') = XLT \<mu>' \<cdot>\<^sub>D XLT \<nu>'"
      proof -
        fix \<mu>' \<nu>'
        assume \<mu>'\<nu>': "D.seq \<mu>' \<nu>'"
        have \<mu>': "\<guillemotleft>\<mu>' : src\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>') \<rightarrow>\<^sub>D trg\<^sub>D \<mu>'\<guillemotright>"
          using \<mu>'\<nu>' D.vseq_implies_hpar by (intro D.in_hhomI, auto)
        have \<nu>': "\<guillemotleft>\<nu>' : src\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>') \<rightarrow>\<^sub>D trg\<^sub>D \<nu>'\<guillemotright>"
          using \<mu>'\<nu>' D.vseq_implies_hpar by (intro D.in_hhomI, auto)
        show "XLT (\<mu>' \<cdot>\<^sub>D \<nu>') = XLT \<mu>' \<cdot>\<^sub>D XLT \<nu>'"
        proof -
          have "XLT (\<mu>' \<cdot>\<^sub>D \<nu>') =
                e (trg\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>')) \<star>\<^sub>D (\<mu>' \<star>\<^sub>D d (src\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>'))) \<cdot>\<^sub>D (\<nu>' \<star>\<^sub>D d (src\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>')))"
            using \<mu>'\<nu>' D.whisker_right D.obj_src d_simps(1) by presburger
          also have "... = (e (trg\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>')) \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>'))) \<cdot>\<^sub>D
                             (e (trg\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>')) \<star>\<^sub>D \<nu>' \<star>\<^sub>D d (src\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>')))"
          proof -
            have "D.seq (\<mu>' \<star>\<^sub>D d (src\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>'))) (\<nu>' \<star>\<^sub>D d (src\<^sub>D (\<mu>' \<cdot>\<^sub>D \<nu>')))"
              using \<mu>' \<nu>' \<mu>'\<nu>' D.obj_src d_simps(1) by fastforce
            thus ?thesis
              using \<mu>'\<nu>' D.obj_src D.obj_trg e_simps(1) D.whisker_left by metis
          qed
          also have "... = XLT \<mu>' \<cdot>\<^sub>D XLT \<nu>'"
            using \<mu>'\<nu>' D.src_vcomp D.trg_vcomp D.vseq_implies_hpar by simp
          finally show ?thesis by simp
        qed
      qed
    qed

    interpretation \<phi>: transformation_by_components V\<^sub>D V\<^sub>D FoG.map XLT \<phi>
    proof
      show "\<And>f'. D.ide f' \<Longrightarrow> \<guillemotleft>\<phi> f' : FoG.map f' \<Rightarrow>\<^sub>D XLT f'\<guillemotright>"
        using \<phi>_props G_ide by simp
      show "\<And>\<mu>'. D.arr \<mu>' \<Longrightarrow> \<phi> (D.cod \<mu>') \<cdot>\<^sub>D FoG.map \<mu>' = XLT \<mu>' \<cdot>\<^sub>D \<phi> (D.dom \<mu>')"
      proof -
        fix \<mu>'
        assume \<mu>': "D.arr \<mu>'"
        show "\<phi> (D.cod \<mu>') \<cdot>\<^sub>D FoG.map \<mu>' = XLT \<mu>' \<cdot>\<^sub>D \<phi> (D.dom \<mu>')"
        proof -
          have "D.inv (\<phi> (D.cod \<mu>')) \<cdot>\<^sub>D XLT \<mu>' \<cdot>\<^sub>D \<phi> (D.dom \<mu>') = F (G \<mu>')"
            using \<mu>' FG_eq by simp
          thus ?thesis
            using \<mu>' \<phi>_props D.iso_inv_iso D.inv_inv
                  D.invert_side_of_triangle(1)
                    [of "F (G \<mu>')" "D.inv (\<phi> (D.cod \<mu>'))" "XLT \<mu>' \<cdot>\<^sub>D \<phi> (D.dom \<mu>')"]
            by auto
        qed
      qed
    qed

    lemma natural_transformation_\<phi>:
    shows "natural_transformation V\<^sub>D V\<^sub>D FoG.map XLT
             (\<lambda>f. if D.arr f then \<phi> (D.cod f) \<cdot>\<^sub>D FoG.map f else D.null)"
      using \<phi>.map_def \<phi>.natural_transformation_axioms by presburger

    text \<open>
      Now we need to define the composition isomorphisms \<open>\<Phi> (f', g')\<close> for each composable pair
      of 1-cells \<open>(f', g')\<close>.  These should be 2-cells \<open>\<guillemotleft>\<Phi> (f', g') : G f' \<star>\<^sub>D G g' \<Rightarrow>\<^sub>D G (f' \<star>\<^sub>D g')\<guillemotright>\<close>.
      The way we obtain these is to define what the \<open>F\<close>-images \<open>F (\<Phi> (f', g'))\<close> have to be,
      then use local fullness and faithfulness to obtain the \<open>\<Phi> (f', g')\<close>.
      To prove naturality and coherence we first show that corresponding results hold for
      \<open>F\<close>-images and then apply faithfulness.

      The \<open>F\<close>-images \<open>F (\<Phi> (f', g'))\<close> are 2-cells
      \<open>\<guillemotleft>F (\<Phi> (f', g')) : F (G f' \<star>\<^sub>D G g') \<Rightarrow>\<^sub>D F (G (f' \<star>\<^sub>D g'))\<guillemotright>\<close>.
      These are defined as the composition of a chain of 2-cells:
      \[\begin{array}{l}
          \<open>F (G f' \<star>\<^sub>C G g')\<close>\\
          \qquad \<open>\<Rightarrow>\<close> \<open>F (G f') \<star>\<^sub>D F (G g')\<close>\\
          \qquad \<open>\<Rightarrow>\<close> \<open>(e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f')) \<star>\<^sub>D e (trg\<^sub>D g') \<star>\<^sub>D g' \<star>\<^sub>D d (src\<^sub>D g')\<close>\\
          \qquad \<open>\<Rightarrow>\<close> \<open>e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D (d (src\<^sub>D f') \<star>\<^sub>D e (trg\<^sub>D g')) \<star>\<^sub>D g' \<star>\<^sub>D d (src\<^sub>D g')\<close>\\
          \qquad \<open>\<Rightarrow>\<close>  \<open>e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D g' \<star>\<^sub>D d (src\<^sub>D g')\<close>\\
          \qquad \<open>\<Rightarrow>\<close> \<open>e (trg\<^sub>D f') \<star>\<^sub>D (f' \<star>\<^sub>D g') \<star>\<^sub>D d (src\<^sub>D g')\<close>\\
          \qquad \<open>\<Rightarrow>\<close> \<open>F (G (f' \<star>\<^sub>D g'))\<close>.
      \end{array}\]
      This results in a rather large expression, which is very nasty to work with if we try
      to expand everything out.
      Instead, we express it in terms of simpler chunks obtained by translating arrows,
      composition, and unitors along the mapping that takes \<open>\<mu>\<close> to \<open>e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)\<close>.
      Since this mapping is an endo-biequivalence of \<open>D\<close> (though we don't establish this,
      \emph{per se}), it preserves equations that hold in \<open>D\<close> and we can work with the \<open>F\<close>-images
      of these equations to help establish the naturality and coherence results we need.
    \<close>

    abbreviation (input) SRC
    where "SRC \<mu> \<equiv> d (src\<^sub>D \<mu>) \<star>\<^sub>D e (src\<^sub>D \<mu>)"

    abbreviation (input) TRG
    where "TRG \<mu> \<equiv> d (trg\<^sub>D \<mu>) \<star>\<^sub>D e (trg\<^sub>D \<mu>)"

    definition LUNIT
    where "LUNIT f \<equiv> \<l>\<^sub>D[f] \<cdot>\<^sub>D (D.inv (\<eta> (trg\<^sub>D f)) \<star>\<^sub>D f)"

    definition RUNIT
    where "RUNIT f \<equiv> \<r>\<^sub>D[f] \<cdot>\<^sub>D (f \<star>\<^sub>D D.inv (\<eta> (src\<^sub>D f)))"

    text \<open>
      Here we prove a series of results that would be automatic if we had some notion of
      ``bicategory \<open>D\<close> with \<open>SRC\<close> and \<open>TRG\<close> as alternative source and target''.
      Perhaps this idea can be developed in future work and used to simplify the overall
      development.  For the current project, it is the end result (obtaining the converse
      equivalence pseudofunctor) that I am primarily interested in.
    \<close>

    lemma LUNIT_in_hom [intro]:
    assumes "D.ide f"
    shows "\<guillemotleft>LUNIT f : src\<^sub>D f \<rightarrow>\<^sub>D trg\<^sub>D f\<guillemotright>"
    and "\<guillemotleft>LUNIT f : TRG f \<star>\<^sub>D f \<Rightarrow>\<^sub>D f\<guillemotright>"
    proof -
      interpret e_trg_f: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            \<open>e (trg\<^sub>D f)\<close> \<open>d (trg\<^sub>D f)\<close> \<open>\<eta> (trg\<^sub>D f)\<close> \<open>\<epsilon> (trg\<^sub>D f)\<close>
        using assms equivalence_ed\<eta>\<epsilon> [of "trg\<^sub>D f"] by simp
      show "\<guillemotleft>LUNIT f : src\<^sub>D f \<rightarrow>\<^sub>D trg\<^sub>D f\<guillemotright>"
        unfolding LUNIT_def
        using assms e_trg_f.unit_is_iso by auto
      show "\<guillemotleft>LUNIT f : TRG f \<star>\<^sub>D f \<Rightarrow>\<^sub>D f\<guillemotright>"
        unfolding LUNIT_def
        using assms e_trg_f.unit_is_iso by auto
    qed

    lemma LUNIT_simps [simp]:
    assumes "D.ide f"
    shows "D.arr (LUNIT f)"
    and "src\<^sub>D (LUNIT f) = src\<^sub>D f" and "trg\<^sub>D (LUNIT f) = trg\<^sub>D f"
    and "D.dom (LUNIT f) = TRG f \<star>\<^sub>D f"
    and "D.cod (LUNIT f) = f"
      using assms LUNIT_in_hom by auto

    lemma RUNIT_in_hom [intro]:
    assumes "D.ide f"
    shows "\<guillemotleft>RUNIT f : src\<^sub>D f \<rightarrow>\<^sub>D trg\<^sub>D f\<guillemotright>"
    and "\<guillemotleft>RUNIT f : f \<star>\<^sub>D SRC f \<Rightarrow>\<^sub>D f\<guillemotright>"
    proof -
      interpret e_src_f: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            \<open>e (src\<^sub>D f)\<close> \<open>d (src\<^sub>D f)\<close> \<open>\<eta> (src\<^sub>D f)\<close> \<open>\<epsilon> (src\<^sub>D f)\<close>
        using assms equivalence_ed\<eta>\<epsilon> [of "src\<^sub>D f"] by simp
      show "\<guillemotleft>RUNIT f : src\<^sub>D f \<rightarrow>\<^sub>D trg\<^sub>D f\<guillemotright>"
        unfolding RUNIT_def
        using assms e_src_f.unit_is_iso by auto
      show "\<guillemotleft>RUNIT f : f \<star>\<^sub>D SRC f \<Rightarrow>\<^sub>D f\<guillemotright>"
        unfolding RUNIT_def
        using assms e_src_f.unit_is_iso by auto
    qed

    lemma RUNIT_simps [simp]:
    assumes "D.ide f"
    shows "D.arr (RUNIT f)"
    and "src\<^sub>D (RUNIT f) = src\<^sub>D f" and "trg\<^sub>D (RUNIT f) = trg\<^sub>D f"
    and "D.dom (RUNIT f) = f \<star>\<^sub>D SRC f"
    and "D.cod (RUNIT f) = f"
      using assms RUNIT_in_hom by auto

    lemma iso_LUNIT:
    assumes "D.ide f"
    shows "D.iso (LUNIT f)"
    proof -
      interpret e_trg_f: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            \<open>e (trg\<^sub>D f)\<close> \<open>d (trg\<^sub>D f)\<close> \<open>\<eta> (trg\<^sub>D f)\<close> \<open>\<epsilon> (trg\<^sub>D f)\<close>
        using assms equivalence_ed\<eta>\<epsilon> [of "trg\<^sub>D f"] by simp
      show ?thesis
        using assms e_trg_f.unit_is_iso D.iso_inv_iso D.iso_lunit LUNIT_def LUNIT_simps(1)
        by auto
    qed

    lemma iso_RUNIT:
    assumes "D.ide f"
    shows "D.iso (RUNIT f)"
    proof -
      interpret e_src_f: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            \<open>e (src\<^sub>D f)\<close> \<open>d (src\<^sub>D f)\<close> \<open>\<eta> (src\<^sub>D f)\<close> \<open>\<epsilon> (src\<^sub>D f)\<close>
        using assms equivalence_ed\<eta>\<epsilon> [of "src\<^sub>D f"] by simp
      show ?thesis
        using assms e_src_f.unit_is_iso D.iso_inv_iso D.iso_runit RUNIT_def RUNIT_simps(1)
        by auto
    qed

    lemma LUNIT_naturality:
    assumes "D.arr \<mu>"
    shows "\<mu> \<cdot>\<^sub>D LUNIT (D.dom \<mu>) = LUNIT (D.cod \<mu>) \<cdot>\<^sub>D (TRG \<mu> \<star>\<^sub>D \<mu>)"
    proof -
      interpret e_trg_\<mu>: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            \<open>e (trg\<^sub>D \<mu>)\<close> \<open>d (trg\<^sub>D \<mu>)\<close> \<open>\<eta> (trg\<^sub>D \<mu>)\<close> \<open>\<epsilon> (trg\<^sub>D \<mu>)\<close>
        using assms equivalence_ed\<eta>\<epsilon> [of "trg\<^sub>D \<mu>"] by simp
      show ?thesis
      proof -
        have "\<mu> \<cdot>\<^sub>D LUNIT (D.dom \<mu>) =
              (\<mu> \<cdot>\<^sub>D \<l>\<^sub>D[D.dom \<mu>]) \<cdot>\<^sub>D (D.inv (\<eta> (trg\<^sub>D \<mu>)) \<star>\<^sub>D D.dom \<mu>)"
          unfolding LUNIT_def
          using assms D.comp_assoc by simp
        also have "... = \<l>\<^sub>D[D.cod \<mu>] \<cdot>\<^sub>D (trg\<^sub>D \<mu> \<star>\<^sub>D \<mu>) \<cdot>\<^sub>D (D.inv (\<eta> (trg\<^sub>D \<mu>)) \<star>\<^sub>D D.dom \<mu>)"
          using assms D.lunit_naturality [of \<mu>] D.comp_assoc by simp
        also have "... = \<l>\<^sub>D[D.cod \<mu>] \<cdot>\<^sub>D (D.inv (\<eta> (trg\<^sub>D \<mu>)) \<star>\<^sub>D \<mu>)"
          using assms D.interchange [of "trg\<^sub>D \<mu>" "D.inv (\<eta> (trg\<^sub>D \<mu>))" \<mu> "D.dom \<mu>"]
                e_trg_\<mu>.unit_is_iso D.comp_arr_dom D.comp_cod_arr by simp
        also have "... = \<l>\<^sub>D[D.cod \<mu>] \<cdot>\<^sub>D (D.inv (\<eta> (trg\<^sub>D \<mu>)) \<star>\<^sub>D D.cod \<mu>) \<cdot>\<^sub>D (TRG \<mu> \<star>\<^sub>D \<mu>)"
          using assms D.interchange [of "D.inv (\<eta> (trg\<^sub>D \<mu>))" "TRG \<mu>" "D.cod \<mu>" \<mu>]
                e_trg_\<mu>.unit_is_iso D.comp_arr_dom D.comp_cod_arr by simp
        also have "... = LUNIT (D.cod \<mu>) \<cdot>\<^sub>D (TRG \<mu> \<star>\<^sub>D \<mu>)"
          unfolding LUNIT_def
          using assms D.comp_assoc by simp
        finally show ?thesis by simp
      qed
    qed

    lemma RUNIT_naturality:
    assumes "D.arr \<mu>"
    shows "\<mu> \<cdot>\<^sub>D RUNIT (D.dom \<mu>) = RUNIT (D.cod \<mu>) \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D SRC \<mu>)"
    proof -
      interpret e_src_\<mu>: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            \<open>e (src\<^sub>D \<mu>)\<close> \<open>d (src\<^sub>D \<mu>)\<close> \<open>\<eta> (src\<^sub>D \<mu>)\<close> \<open>\<epsilon> (src\<^sub>D \<mu>)\<close>
        using assms equivalence_ed\<eta>\<epsilon> [of "src\<^sub>D \<mu>"] by simp
      show ?thesis
      proof -
        have "\<mu> \<cdot>\<^sub>D RUNIT (D.dom \<mu>) =
              (\<mu> \<cdot>\<^sub>D \<r>\<^sub>D[D.dom \<mu>]) \<cdot>\<^sub>D (D.dom \<mu> \<star>\<^sub>D D.inv (\<eta> (src\<^sub>D \<mu>)))"
          unfolding RUNIT_def
          using assms D.comp_assoc by simp
        also have "... = \<r>\<^sub>D[D.cod \<mu>] \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D src\<^sub>D \<mu>) \<cdot>\<^sub>D (D.dom \<mu> \<star>\<^sub>D D.inv (\<eta> (src\<^sub>D \<mu>)))"
          using assms D.runit_naturality [of \<mu>] D.comp_assoc by simp
        also have "... = \<r>\<^sub>D[D.cod \<mu>] \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D D.inv (\<eta> (src\<^sub>D \<mu>)))"
          using assms D.interchange [of \<mu> "D.dom \<mu>" "src\<^sub>D \<mu>" "D.inv (\<eta> (src\<^sub>D \<mu>))"]
                e_src_\<mu>.unit_is_iso D.comp_arr_dom D.comp_cod_arr by simp
        also have "... = \<r>\<^sub>D[D.cod \<mu>] \<cdot>\<^sub>D (D.cod \<mu> \<star>\<^sub>D D.inv (\<eta> (src\<^sub>D \<mu>))) \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D SRC \<mu>)"
          using assms D.interchange [of "D.cod \<mu>" \<mu> "D.inv (\<eta> (src\<^sub>D \<mu>))" "SRC \<mu>"]
                e_src_\<mu>.unit_is_iso D.comp_arr_dom D.comp_cod_arr
          by simp
        also have "... = RUNIT (D.cod \<mu>) \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D SRC \<mu>)"
          unfolding RUNIT_def
          using assms D.comp_assoc by simp
        finally show ?thesis by simp
      qed
    qed

    lemma LUNIT_hcomp:
    assumes "D.ide f" and "D.ide g" and "src\<^sub>D f = trg\<^sub>D g"
    shows "LUNIT (f \<star>\<^sub>D g) \<cdot>\<^sub>D \<a>\<^sub>D[d (trg\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D f), f, g] = LUNIT f \<star>\<^sub>D g"
    proof -
      interpret e_trg_f: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            \<open>e (trg\<^sub>D f)\<close> \<open>d (trg\<^sub>D f)\<close> \<open>\<eta> (trg\<^sub>D f)\<close> \<open>\<epsilon> (trg\<^sub>D f)\<close>
        using assms equivalence_ed\<eta>\<epsilon> [of "trg\<^sub>D f"] by simp
      have "LUNIT (f \<star>\<^sub>D g) \<cdot>\<^sub>D \<a>\<^sub>D[TRG f, f, g] =
            \<l>\<^sub>D[f \<star>\<^sub>D g] \<cdot>\<^sub>D (D.inv (\<eta> (trg\<^sub>D f)) \<star>\<^sub>D f \<star>\<^sub>D g) \<cdot>\<^sub>D \<a>\<^sub>D[TRG f, f, g]"
        unfolding LUNIT_def
        using assms D.comp_assoc by simp
      also have "... = (\<l>\<^sub>D[f \<star>\<^sub>D g] \<cdot>\<^sub>D \<a>\<^sub>D[trg\<^sub>D f, f, g]) \<cdot>\<^sub>D ((D.inv (\<eta> (trg\<^sub>D f)) \<star>\<^sub>D f) \<star>\<^sub>D g)"
        using assms D.assoc_naturality [of "D.inv (\<eta> (trg\<^sub>D f))" f g] e_trg_f.unit_is_iso
              D.comp_assoc
        by simp
      also have "... = (\<l>\<^sub>D[f] \<star>\<^sub>D g) \<cdot>\<^sub>D ((D.inv (\<eta> (trg\<^sub>D f)) \<star>\<^sub>D f) \<star>\<^sub>D g)"
        using assms D.lunit_hcomp [of f g] by simp
      also have "... = LUNIT f \<star>\<^sub>D g"
        using assms LUNIT_def LUNIT_simps(1) D.whisker_right [of g] by auto
      finally show ?thesis by simp
    qed

    lemma RUNIT_hcomp:
    assumes "D.ide f" and "D.ide g" and "src\<^sub>D f = trg\<^sub>D g"
    shows "RUNIT (f \<star>\<^sub>D g) = (f \<star>\<^sub>D RUNIT g) \<cdot>\<^sub>D \<a>\<^sub>D[f, g, SRC g]"
    proof -
      interpret e_src_g: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            \<open>e (src\<^sub>D g)\<close> \<open>d (src\<^sub>D g)\<close> \<open>\<eta> (src\<^sub>D g)\<close> \<open>\<epsilon> (src\<^sub>D g)\<close>
        using assms equivalence_ed\<eta>\<epsilon> [of "src\<^sub>D g"] by simp
      have "(f \<star>\<^sub>D RUNIT g) \<cdot>\<^sub>D \<a>\<^sub>D[f, g, SRC g] =
            (f \<star>\<^sub>D \<r>\<^sub>D[g]) \<cdot>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D D.inv (\<eta> (src\<^sub>D g))) \<cdot>\<^sub>D \<a>\<^sub>D[f, g, SRC g]"
        unfolding RUNIT_def
        using assms D.whisker_left e_src_g.unit_is_iso D.comp_assoc by simp
      also have "... = ((f \<star>\<^sub>D \<r>\<^sub>D[g]) \<cdot>\<^sub>D \<a>\<^sub>D[f, g, src\<^sub>D g]) \<cdot>\<^sub>D ((f \<star>\<^sub>D g) \<star>\<^sub>D D.inv (\<eta> (src\<^sub>D g)))"
        using assms D.assoc_naturality [of f g "D.inv (\<eta> (src\<^sub>D g))"] e_src_g.unit_is_iso
              D.comp_assoc
        by simp
      also have "... = \<r>\<^sub>D[f \<star>\<^sub>D g] \<cdot>\<^sub>D ((f \<star>\<^sub>D g) \<star>\<^sub>D D.inv (\<eta> (src\<^sub>D g)))"
        using assms D.runit_hcomp [of f g] by simp
      also have "... = RUNIT (f \<star>\<^sub>D g)"
        using assms RUNIT_def by simp
      finally show ?thesis by simp
    qed

    lemma TRIANGLE:
    assumes "D.ide f" and "D.ide g" and "src\<^sub>D f = trg\<^sub>D g"
    shows "(f \<star>\<^sub>D LUNIT g) \<cdot>\<^sub>D \<a>\<^sub>D[f, SRC f, g] = RUNIT f \<star>\<^sub>D g"
    proof -
      interpret e_trg_g: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            \<open>e (trg\<^sub>D g)\<close> \<open>d (trg\<^sub>D g)\<close> \<open>\<eta> (trg\<^sub>D g)\<close> \<open>\<epsilon> (trg\<^sub>D g)\<close>
        using assms equivalence_ed\<eta>\<epsilon> [of "trg\<^sub>D g"] by simp
      show ?thesis
      proof -
        have "(f \<star>\<^sub>D LUNIT g) \<cdot>\<^sub>D \<a>\<^sub>D[f, SRC f, g] =
              (f \<star>\<^sub>D \<l>\<^sub>D[g]) \<cdot>\<^sub>D (f \<star>\<^sub>D D.inv (\<eta> (trg\<^sub>D g)) \<star>\<^sub>D g) \<cdot>\<^sub>D \<a>\<^sub>D[f, SRC f, g]"
          using assms D.whisker_left [of f "\<l>\<^sub>D[g]" "D.inv (\<eta> (trg\<^sub>D g)) \<star>\<^sub>D g"] e_trg_g.unit_is_iso
                LUNIT_def LUNIT_simps(1) D.comp_assoc
          by auto
        also have "... = ((f \<star>\<^sub>D \<l>\<^sub>D[g]) \<cdot>\<^sub>D \<a>\<^sub>D[f, src\<^sub>D f, g]) \<cdot>\<^sub>D ((f \<star>\<^sub>D D.inv (\<eta> (trg\<^sub>D g))) \<star>\<^sub>D g)"
          using assms D.assoc_naturality [of f "D.inv (\<eta> (trg\<^sub>D g))" g] e_trg_g.unit_is_iso
                D.comp_assoc
          by auto
        also have "... = (\<r>\<^sub>D[f] \<star>\<^sub>D g) \<cdot>\<^sub>D ((f \<star>\<^sub>D D.inv (\<eta> (trg\<^sub>D g))) \<star>\<^sub>D g)"
          using assms D.triangle by simp
        also have "... = RUNIT f \<star>\<^sub>D g"
          using assms D.whisker_right [of g "\<r>\<^sub>D[f]" "D.inv (\<eta> (trg\<^sub>D g))"] e_trg_g.unit_is_iso
                RUNIT_def RUNIT_simps D.whisker_right
          by metis
        finally show ?thesis by simp
      qed
    qed

    definition CMP
    where "CMP f g \<equiv> (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<cdot>\<^sub>D
                         (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<cdot>\<^sub>D
                         (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<cdot>\<^sub>D
                         \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g)"

    text \<open>
      The 2-cell \<open>CMP f g\<close> has the right type to be a component of the compositor of a pseudofunctor
      whose underlying mapping is \<open>XLT\<close>.  This pseudofunctor ought to be an endo-biequivalence
      of \<open>D\<close>, though we don't go so far as to show that.
    \<close>

    lemma CMP_in_hom [intro]:
    assumes "D.ide f" and "D.ide g" and "src\<^sub>D f = trg\<^sub>D g"
    shows "\<guillemotleft>CMP f g : F.map\<^sub>0 (G\<^sub>0 (src\<^sub>D g)) \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 (trg\<^sub>D f))\<guillemotright>"
    and "\<guillemotleft>CMP f g : XLT f \<star>\<^sub>D XLT g \<Rightarrow>\<^sub>D XLT (f \<star>\<^sub>D g)\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>CMP f g : XLT f \<star>\<^sub>D XLT g \<Rightarrow>\<^sub>D XLT (f \<star>\<^sub>D g)\<guillemotright>"
        apply (unfold CMP_def, intro D.comp_in_homI)
        using assms by fastforce+
      thus "\<guillemotleft>CMP f g : F.map\<^sub>0 (G\<^sub>0 (src\<^sub>D g)) \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 (trg\<^sub>D f))\<guillemotright>"
        using assms D.src_cod D.trg_cod by fastforce
    qed

    lemma CMP_simps [simp]:
    assumes "D.ide f" and "D.ide g" and "src\<^sub>D f = trg\<^sub>D g"
    shows "D.arr (CMP f g)"
    and "src\<^sub>D (CMP f g) = F.map\<^sub>0 (G\<^sub>0 (src\<^sub>D g))"
    and "trg\<^sub>D (CMP f g) = F.map\<^sub>0 (G\<^sub>0 (trg\<^sub>D f))"
    and "D.dom (CMP f g) = XLT f \<star>\<^sub>D XLT g"
    and "D.cod (CMP f g) = XLT (f \<star>\<^sub>D g)"
      using assms CMP_in_hom [of f g] by auto

    lemma iso_CMP:
    assumes "D.ide f" and "D.ide g" and "src\<^sub>D f = trg\<^sub>D g"
    shows "D.iso (CMP f g)"
      unfolding CMP_def
      using assms D.VV.arr_char D.iso_inv_iso \<phi>_props iso_LUNIT
      by (intro D.isos_compose) simp_all

    text \<open>
      The \<open>CMP f g\<close> also satisfy the naturality conditions required of compositors.
    \<close>

    lemma CMP_naturality:
    assumes "D.arr \<mu>" and "D.arr \<nu>" and "src\<^sub>D \<mu> = trg\<^sub>D \<nu>"
    shows "CMP (D.cod \<mu>) (D.cod \<nu>) \<cdot>\<^sub>D (XLT \<mu> \<star>\<^sub>D XLT \<nu>) =
           XLT (\<mu> \<star>\<^sub>D \<nu>) \<cdot>\<^sub>D CMP (D.dom \<mu>) (D.dom \<nu>)"
    proof -
      have "CMP (D.cod \<mu>) (D.cod \<nu>) \<cdot>\<^sub>D (XLT \<mu> \<star>\<^sub>D XLT \<nu>) =
            (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.cod \<mu>, D.cod \<nu>, d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D (D.cod \<mu>)) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D LUNIT (D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D (D.cod \<nu>)))) \<cdot>\<^sub>D
              (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D \<mu>), D.cod \<mu>, d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT (D.cod \<nu>)] \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.cod \<mu>, d (src\<^sub>D \<mu>), XLT (D.cod \<nu>)] \<cdot>\<^sub>D
             (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.cod \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.cod \<nu>)) \<cdot>\<^sub>D
             (XLT \<mu> \<star>\<^sub>D XLT \<nu>)"
        unfolding CMP_def using assms D.comp_assoc by simp
      also have
        "... = (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.cod \<mu>, D.cod \<nu>, d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D (D.cod \<mu>)) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D LUNIT (D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D (D.cod \<nu>)))) \<cdot>\<^sub>D
                 (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D \<mu>), D.cod \<mu>, d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT (D.cod \<nu>)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D[e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.cod \<mu>, d (src\<^sub>D \<mu>), XLT (D.cod \<nu>)] \<cdot>\<^sub>D
                 (((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<star>\<^sub>D XLT \<nu>)) \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.dom \<nu>))"
      proof -
        have "(\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.cod \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.cod \<nu>)) \<cdot>\<^sub>D
                (XLT \<mu> \<star>\<^sub>D XLT \<nu>) =
              \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.cod \<mu>, d (src\<^sub>D \<mu>)] \<cdot>\<^sub>D XLT \<mu> \<star>\<^sub>D XLT (D.cod \<nu>) \<cdot>\<^sub>D XLT \<nu>"
          using assms
                D.interchange
                  [of "\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.cod \<mu>, d (src\<^sub>D \<mu>)]" "XLT \<mu>" "XLT (D.cod \<nu>)" "XLT \<nu>"]
          by fastforce
        also have
          "... = ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D
                   XLT (D.cod \<nu>) \<cdot>\<^sub>D XLT \<nu>"
          using assms D.assoc'_naturality [of "e (trg\<^sub>D \<mu>)" \<mu> "d (src\<^sub>D \<mu>)"] by simp
        also have
          "... = ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D
                   XLT \<nu> \<cdot>\<^sub>D XLT (D.dom \<nu>)"
          using assms D.comp_arr_dom D.comp_cod_arr D.src_cod D.src_dom
                D.trg_cod D.trg_dom XLT.naturality
          by presburger
        also have "... = (((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<star>\<^sub>D XLT \<nu>) \<cdot>\<^sub>D
                           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.dom \<nu>))"
        proof -
          have "D.seq ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)]"
            using assms by auto
          moreover have "D.seq (XLT \<nu>) (XLT (D.dom \<nu>))"
            using assms by auto
          moreover have "src\<^sub>D ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>)) = trg\<^sub>D (XLT \<nu>)"
            using assms by simp
          ultimately show ?thesis
             using assms D.interchange by simp
        qed
        finally have "(\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.cod \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.cod \<nu>)) \<cdot>\<^sub>D
                        (XLT \<mu> \<star>\<^sub>D XLT \<nu>) =
                      (((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<star>\<^sub>D XLT \<nu>) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.dom \<nu>))"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.cod \<mu>, D.cod \<nu>, d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D (D.cod \<mu>)) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D LUNIT (D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D (D.cod \<nu>)))) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D \<mu>), D.cod \<mu>, d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT (D.cod \<nu>)] \<cdot>\<^sub>D
           ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>)) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu>, d (src\<^sub>D \<mu>), XLT (D.dom \<nu>)] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.dom \<nu>))"
      proof -
        have "\<a>\<^sub>D[e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.cod \<mu>, d (src\<^sub>D \<mu>), XLT (D.cod \<nu>)] \<cdot>\<^sub>D
                (((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<star>\<^sub>D XLT \<nu>) =
              ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>) \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu>, d (src\<^sub>D \<mu>), XLT (D.dom \<nu>)]"
          using assms D.assoc_naturality [of "e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>" "d (src\<^sub>D \<mu>)" "XLT \<nu>"]
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.cod \<mu>, D.cod \<nu>, d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D (D.cod \<mu>)) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D LUNIT (D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D (D.cod \<nu>)))) \<cdot>\<^sub>D
           ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>)) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT (D.dom \<nu>)] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu>, d (src\<^sub>D \<mu>), XLT (D.dom \<nu>)] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.dom \<nu>))"
      proof -
        have "\<a>\<^sub>D[e (trg\<^sub>D \<mu>), D.cod \<mu>, d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT (D.cod \<nu>)] \<cdot>\<^sub>D
                ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>) \<star>\<^sub>D d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>) =
              (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>) \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT (D.dom \<nu>)]"
          using assms D.assoc_naturality [of "e (trg\<^sub>D \<mu>)" \<mu> "d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>"]
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.cod \<mu>, D.cod \<nu>, d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           ((e (trg\<^sub>D (D.cod \<mu>)) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D LUNIT (D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D (D.cod \<nu>)))) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D SRC \<mu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT (D.dom \<nu>)] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu>, d (src\<^sub>D \<mu>), XLT (D.dom \<nu>)] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.dom \<nu>))"
      proof -
        have
          "(e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>) =
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D TRG \<nu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D
             (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)])"
        proof -
          have
            "(e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
               (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>) =
             e (trg\<^sub>D \<mu>) \<star>\<^sub>D
               (D.cod \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
               (\<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>)"
            using assms D.whisker_left by simp
          also have "... = e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)] \<cdot>\<^sub>D
                             (d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>)"
            using assms D.comp_cod_arr
                  D.interchange
                    [of "D.cod \<mu>" \<mu> "\<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]"
                        "d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT \<nu>"]
            by simp
          also have "... = e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D (TRG \<nu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]"
            using assms
                  D.assoc'_naturality [of "d (src\<^sub>D \<mu>)" "e (trg\<^sub>D \<nu>)" "\<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)"]
            by simp
          also have "... = e (trg\<^sub>D \<mu>) \<star>\<^sub>D (\<mu> \<star>\<^sub>D TRG \<nu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D
                             (D.dom \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)])"
            using assms D.comp_arr_dom
                  D.interchange
                    [of \<mu> "D.dom \<mu>" "TRG \<nu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)"
                        "\<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]"]
            by fastforce
          also have
            "... = (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D TRG \<nu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D
                     (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu> \<star>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)])"
            using assms D.whisker_left by simp
          finally show ?thesis by simp
        qed
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.cod \<mu>, D.cod \<nu>, d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu> \<star>\<^sub>D LUNIT (D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT (D.dom \<nu>)] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu>, d (src\<^sub>D \<mu>), XLT (D.dom \<nu>)] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.dom \<nu>))"
      proof -
        have "((e (trg\<^sub>D (D.cod \<mu>)) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D LUNIT (D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D (D.cod \<nu>)))) \<cdot>\<^sub>D
                (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D TRG \<nu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))) =
              e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D
                LUNIT (D.cod (\<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))) \<cdot>\<^sub>D
                ((d (src\<^sub>D \<mu>) \<star>\<^sub>D e (trg\<^sub>D \<nu>)) \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))"
          using assms D.comp_arr_dom D.comp_cod_arr D.whisker_left
                D.interchange [of "D.cod \<mu>" \<mu> "LUNIT (D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D (D.cod \<nu>)))"
                                  "(d (src\<^sub>D \<mu>) \<star>\<^sub>D e (trg\<^sub>D \<nu>)) \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)"]
          by fastforce
        also have "... =
                   e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D (\<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D LUNIT (D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))"
          using assms LUNIT_naturality [of "\<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)"] by simp
        also have "... = (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D 
                           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu> \<star>\<^sub>D LUNIT (D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)))"
          using assms D.comp_arr_dom D.comp_cod_arr D.whisker_left
                D.interchange [of \<mu> "D.dom \<mu>" "\<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)" "LUNIT (D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))"]
          by simp
        finally have
          "((e (trg\<^sub>D (D.cod \<mu>)) \<star>\<^sub>D D.cod \<mu> \<star>\<^sub>D LUNIT (D.cod \<nu> \<star>\<^sub>D d (src\<^sub>D (D.cod \<nu>)))) \<cdot>\<^sub>D
             (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D TRG \<nu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))) =
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D 
             (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu> \<star>\<^sub>D LUNIT (D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)))"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         XLT (\<mu> \<star>\<^sub>D \<nu>) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.dom \<mu>, D.dom \<nu>, d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu> \<star>\<^sub>D LUNIT (D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))) \<cdot>\<^sub>D
           (e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu> \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D \<mu>), e (trg\<^sub>D \<nu>), D.dom \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>) \<star>\<^sub>D XLT (D.dom \<nu>)] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D \<mu>) \<star>\<^sub>D D.dom \<mu>, d (src\<^sub>D \<mu>), XLT (D.dom \<nu>)] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D \<mu>), D.dom \<mu>, d (src\<^sub>D \<mu>)] \<star>\<^sub>D XLT (D.dom \<nu>))"
      proof -
        have "(e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.cod \<mu>, D.cod \<nu>, d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) =
              XLT (\<mu> \<star>\<^sub>D \<nu>) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.dom \<mu>, D.dom \<nu>, d (src\<^sub>D \<nu>)])"
        proof -
          have "(e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.cod \<mu>, D.cod \<nu>, d (src\<^sub>D \<nu>)]) \<cdot>\<^sub>D
                  (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>)) =
                e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.cod \<mu>, D.cod \<nu>, d (src\<^sub>D \<nu>)] \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D \<nu> \<star>\<^sub>D d (src\<^sub>D \<nu>))"
            using assms D.whisker_left by simp
          also have "... = e (trg\<^sub>D \<mu>) \<star>\<^sub>D ((\<mu> \<star>\<^sub>D \<nu>) \<star>\<^sub>D d (src\<^sub>D \<nu>)) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[D.dom \<mu>, D.dom \<nu>, d (src\<^sub>D \<nu>)]"
            using assms D.assoc'_naturality [of \<mu> \<nu> "d (src\<^sub>D \<nu>)"] by simp
          also have "... = XLT (\<mu> \<star>\<^sub>D \<nu>) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[D.dom \<mu>, D.dom \<nu>, d (src\<^sub>D \<nu>)])"
            using assms D.whisker_left by simp
          finally show ?thesis by simp
        qed
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = XLT (\<mu> \<star>\<^sub>D \<nu>) \<cdot>\<^sub>D CMP (D.dom \<mu>) (D.dom \<nu>)"
        unfolding CMP_def using assms D.comp_assoc by simp
      finally show ?thesis by simp
    qed

    interpretation E: self_evaluation_map V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D ..
    notation E.eval ("\<lbrace>_\<rbrace>")

    abbreviation (input) SRCt  ("\<^bold>S\<^bold>R\<^bold>C")
    where "\<^bold>S\<^bold>R\<^bold>C \<mu> \<equiv> \<^bold>\<langle>d (src\<^sub>D \<mu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e (src\<^sub>D \<mu>)\<^bold>\<rangle>"

    abbreviation (input) TRGt  ("\<^bold>T\<^bold>R\<^bold>G")
    where "\<^bold>T\<^bold>R\<^bold>G \<mu> \<equiv> \<^bold>\<langle>d (trg\<^sub>D \<mu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e (trg\<^sub>D \<mu>)\<^bold>\<rangle>"
 
    abbreviation (input) XLTt  ("\<^bold>X\<^bold>L\<^bold>T")
    where "\<^bold>X\<^bold>L\<^bold>T \<mu> \<equiv> \<^bold>\<langle>e (trg\<^sub>D \<mu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<mu>\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D \<mu>)\<^bold>\<rangle>"

    text \<open>
      The \<open>CMP f g\<close> satisfy the coherence conditions with respect to associativity that are
      required of compositors.
    \<close>

    (* TODO: This is a nasty proof that I would like to shorten somehow. *)

    lemma CMP_coherence:
    assumes "D.ide f" and "D.ide g" and "D.ide h" and "src\<^sub>D f = trg\<^sub>D g" and "src\<^sub>D g = trg\<^sub>D h"
    shows "XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D CMP (f \<star>\<^sub>D g) h \<cdot>\<^sub>D (CMP f g \<star>\<^sub>D XLT h) =
           CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D (XLT f \<star>\<^sub>D CMP g h) \<cdot>\<^sub>D \<a>\<^sub>D[XLT f, XLT g, XLT h]"
    proof -
      text \<open>
        The overall strategy of the proof is to expand the definition of \<open>CMP\<close> on the
        left and right-hand sides, then permute the occurrences of \<open>LUNIT\<close> and
        \<open>RUNIT\<close> to the left ends of both the left-hand side and right-hand side of the
        equation to be proved, so that the initial portions of these expressions become
        identical and the remaining parts to the right consist only of canonical isomorphisms.
        Then the Coherence Theorem is applied to prove syntactically (and automatically) that the
        canonical parts are equal, which implies equality of the complete expressions.
        The rest is just grinding through the calculations.
      \<close>
      have "XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D CMP (f \<star>\<^sub>D g) h \<cdot>\<^sub>D (CMP f g \<star>\<^sub>D XLT h) =
            XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
              (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
              ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g)
                  \<star>\<^sub>D XLT h)"
        unfolding CMP_def using assms D.comp_assoc by simp
      also have
        "... =
         XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
          (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
          (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
          (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
          \<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
          \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
          (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
          ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
          ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
          ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
          (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
          (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
          ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g)
                  \<star>\<^sub>D XLT h) =
              ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
          using assms D.whisker_right by simp (* 6 sec *)
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D (LUNIT h \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]"
          using assms LUNIT_hcomp [of h "d (src\<^sub>D h)"] D.invert_side_of_triangle
          by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, h, d (src\<^sub>D h)] \<cdot>\<^sub>D ((f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D
                           (((f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]"
          using assms D.assoc'_naturality [of "f \<star>\<^sub>D g" "LUNIT h" "d (src\<^sub>D h)"] by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D ((f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)"
          using assms D.whisker_left D.whisker_right by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<cdot>\<^sub>D
                           \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)"
          using assms D.assoc_naturality [of f g "LUNIT h"] by simp
        also have
          "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                   (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left D.whisker_right by simp
        finally have
          "XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) =
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h))"
          by simp
        thus ?thesis using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h)) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<star>\<^sub>D XLT h) =
              (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g \<star>\<^sub>D d (src\<^sub>D g)) \<cdot>\<^sub>D
                              \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h"
          using assms TRIANGLE [of f "g \<star>\<^sub>D d (src\<^sub>D g)"] D.invert_side_of_triangle
          by simp
        also have "... = ((e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                         ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h)"
          using assms D.whisker_left D.whisker_right by simp
        finally have "((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D d (src\<^sub>D g))) \<star>\<^sub>D XLT h) =
                      ((e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                        ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>D d (src\<^sub>D g)])
                            \<star>\<^sub>D XLT h)"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h)) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D TRG g, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                ((e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) =
              (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)] \<cdot>\<^sub>D (RUNIT f \<star>\<^sub>D g \<star>\<^sub>D d (src\<^sub>D g))) \<star>\<^sub>D XLT h"
          using assms D.whisker_left D.whisker_right by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D ((RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g)) \<cdot>\<^sub>D
                                        \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D TRG g, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h"
          using assms D.assoc'_naturality [of "RUNIT f" g "d (src\<^sub>D g)"] by simp
        also have "... = ((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D TRG g, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h)"
          using assms D.whisker_left D.whisker_right by simp
        finally have "((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                        ((e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) =
                      ((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                        ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D TRG g, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h)"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g)) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h)) \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "(\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                ((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) =
              \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h"
          using assms D.whisker_left D.whisker_right by simp
        also have "... = ((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g)) \<star>\<^sub>D d (src\<^sub>D g)) \<cdot>\<^sub>D
                            \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h"
          using assms D.assoc'_naturality [of "e (trg\<^sub>D f)" "RUNIT f \<star>\<^sub>D g" "d (src\<^sub>D g)"]
          by simp
        also have "... = (((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g)) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h)"
          using assms D.whisker_left D.whisker_right by simp
        finally have "(\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                        ((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) =
                      (((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g)) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h)"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g)) \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D XLT h)) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g)) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g)) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
                (((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g)) \<star>\<^sub>D d (src\<^sub>D g)) \<star>\<^sub>D XLT h) =
              ((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g)) \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]"
          using assms  
                D.assoc_naturality [of "e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g)" "d (src\<^sub>D g)" "XLT h"]
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D XLT h)) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "\<a>\<^sub>D[e (trg\<^sub>D f), f \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
                ((e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g)) \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D XLT h) =
              (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]"
          using assms
                D.assoc_naturality [of "e (trg\<^sub>D f)" "RUNIT f \<star>\<^sub>D g" "d (src\<^sub>D g) \<star>\<^sub>D XLT h"]
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)])) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "((e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D XLT h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)] \<cdot>\<^sub>D (d (src\<^sub>D g) \<star>\<^sub>D XLT h)"
          using assms D.comp_cod_arr D.whisker_left
                D.interchange [of "f \<star>\<^sub>D g" "RUNIT f \<star>\<^sub>D g"]
          by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]"
          using assms D.comp_arr_dom by simp
        finally have "((e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D
                          \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D XLT h)) =
                      e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)])) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
              \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D
                   \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) =
              e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)] \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]"
          using assms D.comp_arr_dom D.comp_cod_arr D.whisker_left
                D.interchange [of "f \<star>\<^sub>D g" "RUNIT f \<star>\<^sub>D g"
                                  "\<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]"
                                  "\<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]"]
          by simp (* 4 sec *)
        also have
          "... = (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                   (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
                      \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)])"
          using assms D.comp_arr_dom D.whisker_left
                D.interchange [of "RUNIT f \<star>\<^sub>D g" "(f \<star>\<^sub>D SRC f) \<star>\<^sub>D g"
                                  "\<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]"
                                  "\<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]"]
          by simp
        finally have
          "(e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) =
           (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)])) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) =
              e (trg\<^sub>D f) \<star>\<^sub>D
                (\<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]"
          using assms D.whisker_left by simp
        also have
          "... = e (trg\<^sub>D f) \<star>\<^sub>D
                   \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h, d (src\<^sub>D h)] \<cdot>\<^sub>D
                   (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                   \<a>\<^sub>D[f, g, ((d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]"
        proof -
          have "(\<a>\<^sub>D\<^sup>-\<^sup>1[f, g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h, d (src\<^sub>D h)] \<cdot>\<^sub>D
                  (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h, d (src\<^sub>D h)]) =
                  \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h, d (src\<^sub>D h)] \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[f, g, ((d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]"
            using assms D.pentagon' D.comp_assoc by simp
          moreover have "D.inv (\<a>\<^sub>D\<^sup>-\<^sup>1[f, g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) =
                         \<a>\<^sub>D[f, g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)"
            using assms D.iso_inv_iso by simp
          ultimately show ?thesis
            using assms D.iso_inv_iso D.comp_assoc
                  D.invert_opposite_sides_of_square
                    [of "\<a>\<^sub>D\<^sup>-\<^sup>1[f, g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)"
                        "\<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h, d (src\<^sub>D h)] \<cdot>\<^sub>D
                           (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h, d (src\<^sub>D h)])"
                        "\<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h, d (src\<^sub>D h)]"
                        "\<a>\<^sub>D\<^sup>-\<^sup>1[f, g, ((d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]"]
            by simp (* 10 sec *)
        qed
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, TRG h \<star>\<^sub>D h] \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, (d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) =
              e (trg\<^sub>D f) \<star>\<^sub>D
                \<a>\<^sub>D[f, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)] \<cdot>\<^sub>D
                ((RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D
                           (RUNIT f \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                           \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)]"
          using assms D.hseqI'
                D.assoc_naturality [of "RUNIT f" g "\<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]"]
          by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D (RUNIT f \<star>\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)))) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D
             \<a>\<^sub>D\<^sup>-\<^sup>1[d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h), h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h), h, d (src\<^sub>D h)] =
              (e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)])"
          using assms D.whisker_left D.comp_arr_dom D.comp_cod_arr
                D.interchange [of "RUNIT f" "f \<star>\<^sub>D SRC f"
                                  "g \<star>\<^sub>D ((TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))"
                                  "g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]"]
          by simp (* 8 sec *)
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D
                           (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                           \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)])"
          using assms TRIANGLE [of f "g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)"] by simp
        also have
          "... =
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D
               \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)])"
          using assms D.whisker_left D.comp_assoc by simp
        finally have
          "e (trg\<^sub>D f) \<star>\<^sub>D RUNIT f \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)] =
             (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D
               \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (LUNIT g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                                  \<a>\<^sub>D\<^sup>-\<^sup>1[d (trg\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D g), g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]"
          using assms LUNIT_hcomp [of g "(TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)"]
                D.invert_side_of_triangle
          by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                         (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)] \<cdot>\<^sub>D
                (LUNIT g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                           ((LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]"
          using assms D.assoc'_naturality [of "LUNIT g" "TRG h \<star>\<^sub>D h" "d (src\<^sub>D h)"]
          by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "(e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                         (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         ((e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D SRC g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>D g) \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)] \<cdot>\<^sub>D
                (f \<star>\<^sub>D (LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D
                           ((f \<star>\<^sub>D LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>D g) \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]"
          using assms D.assoc'_naturality [of f "LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h" "d (src\<^sub>D h)"]
          by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>D g) \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>D g) \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>D g) \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)"
          using assms D.whisker_left D.whisker_right D.comp_arr_dom D.comp_cod_arr
                D.interchange [of g "LUNIT g" "LUNIT h" "(d (trg\<^sub>D h) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h"]
          by simp (* 5 sec *)
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      finally have
        L: "XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D CMP (f \<star>\<^sub>D g) h \<cdot>\<^sub>D (CMP f g \<star>\<^sub>D XLT h) =
              (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>D g) \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D
                 \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
                 \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
              (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
              ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
              ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
              ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
              (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
              (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
              ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"
        by simp

      have "CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D (XLT f \<star>\<^sub>D CMP g h) \<cdot>\<^sub>D \<a>\<^sub>D[XLT f, XLT g, XLT h] =
            (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT ((g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
              (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
              (XLT f \<star>\<^sub>D
                (e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                (e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h)) \<cdot>\<^sub>D
              \<a>\<^sub>D[XLT f, XLT g, XLT h]"
        unfolding CMP_def using assms D.comp_assoc by simp
      also have
        "... = (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT ((g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "XLT f \<star>\<^sub>D
                (e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                (e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
                \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) =
              (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h)"
          using assms D.whisker_left by auto (* 6 sec *)
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... = ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (trg\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT ((g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D 
                (LUNIT (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)]"
          using assms LUNIT_hcomp [of "g \<star>\<^sub>D h" "d (src\<^sub>D h)"]
                D.invert_side_of_triangle
          by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT ((g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D h, d (src\<^sub>D h)] \<cdot>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D
                           ((f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]"
          using assms D.assoc'_naturality [of f "LUNIT (g \<star>\<^sub>D h)" "d (src\<^sub>D h)"]
                LUNIT_in_hom [of "g \<star>\<^sub>D h"]
          by auto
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                 ((XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D RUNIT g \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h)) =
              XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D
                (RUNIT g \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h, h \<star>\<^sub>D d (src\<^sub>D h)]"
          using assms TRIANGLE [of g "h \<star>\<^sub>D d (src\<^sub>D h)"] D.invert_side_of_triangle
          by simp
        also have "... = (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D RUNIT g \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h, h \<star>\<^sub>D d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D LUNIT (h \<star>\<^sub>D d (src\<^sub>D h)) =
                      (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D RUNIT g \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, TRG h, h \<star>\<^sub>D d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "(XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D RUNIT g \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)) =
              XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)] \<cdot>\<^sub>D (RUNIT g \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left by simp
        also have "... = XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D
                           ((RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]"
          using assms D.assoc'_naturality [of "RUNIT g" h "d (src\<^sub>D h)"] by auto
        also have "... = (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "(XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D RUNIT g \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)) =
                      (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
           (((e (trg\<^sub>D f) \<star>\<^sub>D f) \<star>\<^sub>D d (src\<^sub>D f)) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D
               (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
             (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
                e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
             \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "(\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
               (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
              \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)"
          using assms D.comp_arr_dom D.comp_cod_arr
                D.interchange
                  [of "\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)]" "XLT f"
                      "XLT (g \<star>\<^sub>D h)" "e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)"]
          by simp
        also have "... = (((e (trg\<^sub>D f) \<star>\<^sub>D f) \<star>\<^sub>D d (src\<^sub>D f)) \<star>\<^sub>D
                            e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
                            e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.comp_arr_dom D.comp_cod_arr
                D.interchange
                  [of "(e (trg\<^sub>D f) \<star>\<^sub>D f) \<star>\<^sub>D d (src\<^sub>D f)" "\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)]"
                      "e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)"
                      "e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)"]
          by simp (* 6 sec *)
        finally have "(\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                        (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
                      (((e (trg\<^sub>D f) \<star>\<^sub>D f) \<star>\<^sub>D d (src\<^sub>D f)) \<star>\<^sub>D
                        e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                      (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
                        e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (trg\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f) \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D
             (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
              e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
             (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
             \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have
          "\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
             (((e (trg\<^sub>D f) \<star>\<^sub>D f) \<star>\<^sub>D d (src\<^sub>D f)) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D
                d (src\<^sub>D h)) =
           ((e (trg\<^sub>D f) \<star>\<^sub>D f) \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
             \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)]"
          using assms
                D.assoc_naturality
                  [of "e (trg\<^sub>D f) \<star>\<^sub>D f" "d (src\<^sub>D f)" "e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)"]
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
        (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
          (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, (d (trg\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D g)) \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
          (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (trg\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
          ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
          (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
          \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h)] \<cdot>\<^sub>D
          \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h)] \<cdot>\<^sub>D
          (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
            e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
          (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h), h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
          (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
          (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
          (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
          (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
          (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
          \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have
          "\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT (g \<star>\<^sub>D h)] \<cdot>\<^sub>D
             ((e (trg\<^sub>D f) \<star>\<^sub>D f) \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D
                d (src\<^sub>D h)) =
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
             \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)]"
          using assms
                D.assoc_naturality
                  [of "e (trg\<^sub>D f)" f "d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)"]
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g),
                                   ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h)] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h)] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
             e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have
          "(e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D
                d (src\<^sub>D h)) =
           e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
             \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)] \<cdot>\<^sub>D
             (d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                           (TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]"
          using assms
                D.assoc'_naturality [of "d (src\<^sub>D f)" "e (trg\<^sub>D g)" "(RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)"]
          by auto
        also have
          "... = (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D SRC f \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                   (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                      \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have
          "(e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), (g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D SRC f \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g),
                                        ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
                   e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)] \<cdot>\<^sub>D
                (TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                           ((TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]"
          using assms D.assoc'_naturality [of "TRG g" "RUNIT g \<star>\<^sub>D h" "d (src\<^sub>D h)"]
          by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                              \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "(e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)])"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g),
                                        ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
                   e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)] \<cdot>\<^sub>D
                (f \<star>\<^sub>D (TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left by simp
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D
                           ((f \<star>\<^sub>D SRC f \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]"
          using assms
                D.assoc'_naturality
                  [of f "(d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g)) \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)" "d (src\<^sub>D h)"]
          by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)])"
          using assms D.whisker_left by simp
        finally have "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D g \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D (TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D TRG g \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)])"
          using assms by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D \<a>\<^sub>D[g, d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h), h]) \<star>\<^sub>D
                    d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
                   e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h) =
              e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D(g \<star>\<^sub>D LUNIT h) \<cdot>\<^sub>D \<a>\<^sub>D[g, SRC g, h]) \<star>\<^sub>D d (src\<^sub>D h)"
          using assms TRIANGLE [of g h] by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D \<a>\<^sub>D[g, TRG h, h]) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left D.whisker_right by simp
        finally have "e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D (RUNIT g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D \<a>\<^sub>D[g, TRG h, h]) \<star>\<^sub>D d (src\<^sub>D h))"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 ((e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D TRG g \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D TRG g \<star>\<^sub>D \<a>\<^sub>D[g, SRC g, h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g),
                                        ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
                   e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h) =
              e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D (LUNIT g \<star>\<^sub>D h) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>D d (src\<^sub>D h)"
          using assms LUNIT_hcomp [of g h] D.invert_side_of_triangle by simp
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left D.whisker_right by simp
        finally have "e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT (g \<star>\<^sub>D h)) \<star>\<^sub>D d (src\<^sub>D h) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>D d (src\<^sub>D h))"
          by simp
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have
        "... = ((e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D (TRG g \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h))) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>D h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D TRG g \<star>\<^sub>D \<a>\<^sub>D[g, SRC g, h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g),
                                        ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
                   e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D
                   \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
                 (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
                 \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have
          "(e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D TRG g \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) =
           e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, h] \<cdot>\<^sub>D (TRG g \<star>\<^sub>D g \<star>\<^sub>D LUNIT h)) \<star>\<^sub>D d (src\<^sub>D h)"
          using assms D.whisker_left D.whisker_right by auto
        also have "... = e (trg\<^sub>D f) \<star>\<^sub>D
                           (f \<star>\<^sub>D ((TRG g \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<cdot>\<^sub>D
                                   \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, SRC g \<star>\<^sub>D h]) \<star>\<^sub>D d (src\<^sub>D h)"
          using assms D.assoc'_naturality [of "TRG g" g "LUNIT h"] by auto
        also have "... = (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D (TRG g \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>D h]) \<star>\<^sub>D d (src\<^sub>D h))"
          using assms D.whisker_left D.whisker_right by auto
        finally have "(e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D TRG g \<star>\<^sub>D g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) =
                      (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D (TRG g \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                        (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>D h]) \<star>\<^sub>D d (src\<^sub>D h))"
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have
        "... =
         (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>D h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D TRG g \<star>\<^sub>D \<a>\<^sub>D[g, d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h), h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D
              \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
              \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
             e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D d (src\<^sub>D g) \<star>\<^sub>D e (trg\<^sub>D h)) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           \<a>\<^sub>D[XLT f, XLT g, XLT h]"
      proof -
        have "(e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
                (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D (TRG g \<star>\<^sub>D g) \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) =
              e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)"
          using assms D.whisker_left D.whisker_right D.comp_arr_dom D.comp_cod_arr
                D.interchange [of "LUNIT g" "TRG g \<star>\<^sub>D g" h "LUNIT h"]
          by simp (* 6 sec *)
        thus ?thesis
          using assms by simp
      qed
      finally have
        R: "CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D (XLT f \<star>\<^sub>D CMP g h) \<cdot>\<^sub>D \<a>\<^sub>D[XLT f, XLT g, XLT h] =
            (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D LUNIT g \<star>\<^sub>D LUNIT h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>D h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D \<a>\<^sub>D[g, TRG h, h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g),
                                      ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
              \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
              (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
                e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
              (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
              (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
              (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
              (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
              \<a>\<^sub>D[XLT f, XLT g, XLT h]"
         using assms by simp

      text \<open>
        The portions of the expressions on the right-hand sides of assertions \<open>L\<close> and \<open>R\<close>
        that are not identical only involve canonical isomorphisms, and thus they can be proved
        equal automatically by the simplifier, once we have expressed them in the formal
        language of \<open>D\<close>.
      \<close>

      let ?LHS =
          "(e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>D g) \<star>\<^sub>D TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g \<star>\<^sub>D g, TRG h \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D
                \<a>\<^sub>D[f, d (src\<^sub>D f) \<star>\<^sub>D e (trg\<^sub>D g), g \<star>\<^sub>D (TRG h \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG h, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D[f \<star>\<^sub>D SRC f, g, TRG h \<star>\<^sub>D h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             (e (trg\<^sub>D f) \<star>\<^sub>D ((f \<star>\<^sub>D SRC f) \<star>\<^sub>D g) \<star>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
             \<a>\<^sub>D[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g) \<star>\<^sub>D XLT h] \<cdot>\<^sub>D
             \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h] \<cdot>\<^sub>D
             (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), (f \<star>\<^sub>D SRC f) \<star>\<^sub>D g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
             ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f \<star>\<^sub>D SRC f, g, d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
             ((e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
             ((e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), g \<star>\<^sub>D d (src\<^sub>D g)]) \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
             (\<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
             (\<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT g] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
             ((\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D XLT g) \<star>\<^sub>D XLT h)"

      let ?LHSt =
        "(\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, (\<^bold>T\<^bold>R\<^bold>G g \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G g \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G g, \<^bold>\<langle>g\<^bold>\<rangle>, (\<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star>
              \<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> (\<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G h, \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star>
              \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle>, \<^bold>\<langle>e (trg\<^sub>D h)\<^bold>\<rangle>, \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           \<^bold>\<a>\<^bold>[\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle>, (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle> \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h\<^bold>] \<^bold>\<cdot>
           \<^bold>\<a>\<^bold>[\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle>, \<^bold>X\<^bold>L\<^bold>T h\<^bold>] \<^bold>\<cdot>
           (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle>, (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h) \<^bold>\<cdot>
           ((\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h) \<^bold>\<cdot>
           ((\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>S\<^bold>R\<^bold>C f, \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h) \<^bold>\<cdot>
           ((\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d (src\<^sub>D f)\<^bold>\<rangle>, \<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h) \<^bold>\<cdot>
           (\<^bold>\<a>\<^bold>[\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T g\<^bold>] \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h) \<^bold>\<cdot>
           (\<^bold>\<a>\<^bold>[\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D f)\<^bold>\<rangle>, \<^bold>X\<^bold>L\<^bold>T g\<^bold>] \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h) \<^bold>\<cdot>
           ((\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D f)\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T g) \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h)"

      let ?RHS =
        "(e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>D h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D (f \<star>\<^sub>D SRC f \<star>\<^sub>D \<a>\<^sub>D[g, TRG h, h]) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>D (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>D SRC g) \<star>\<^sub>D h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (e (trg\<^sub>D f) \<star>\<^sub>D f \<star>\<^sub>D
              \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D f), e (trg\<^sub>D g), ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f), f, d (src\<^sub>D f) \<star>\<^sub>D XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
           \<a>\<^sub>D[e (trg\<^sub>D f) \<star>\<^sub>D f, d (src\<^sub>D f), XLT ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h)] \<cdot>\<^sub>D
           (\<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D f), f, d (src\<^sub>D f)] \<star>\<^sub>D
             e (trg\<^sub>D g) \<star>\<^sub>D ((g \<star>\<^sub>D SRC g) \<star>\<^sub>D h) \<star>\<^sub>D d (src\<^sub>D h)) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g \<star>\<^sub>D SRC g, h, d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D e (trg\<^sub>D g) \<star>\<^sub>D g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[d (src\<^sub>D g), e (trg\<^sub>D h), h \<star>\<^sub>D d (src\<^sub>D h)]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g), g, d (src\<^sub>D g) \<star>\<^sub>D XLT h]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D \<a>\<^sub>D[e (trg\<^sub>D g) \<star>\<^sub>D g, d (src\<^sub>D g), XLT h]) \<cdot>\<^sub>D
           (XLT f \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[e (trg\<^sub>D g), g, d (src\<^sub>D g)] \<star>\<^sub>D XLT h) \<cdot>\<^sub>D
           \<a>\<^sub>D[XLT f, XLT g, XLT h]"

      let ?RHSt =
        "(\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G g, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G h, \<^bold>\<langle>h\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G g \<^bold>\<star> (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G g, (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star>
              \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d (src\<^sub>D f)\<^bold>\<rangle>, \<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle>, ((\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           \<^bold>\<a>\<^bold>[\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>,
             \<^bold>\<langle>d (src\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle> \<^bold>\<star> ((\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>)\<^bold>] \<^bold>\<cdot>
           \<^bold>\<a>\<^bold>[\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D f)\<^bold>\<rangle>,
             (\<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle> \<^bold>\<star> ((\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>)\<^bold>] \<^bold>\<cdot>
           (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e (trg\<^sub>D f)\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D f)\<^bold>\<rangle>\<^bold>] \<^bold>\<star>
             \<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle> \<^bold>\<star> ((\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>) \<^bold>\<cdot>
           (\<^bold>X\<^bold>L\<^bold>T f \<^bold>\<star> \<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g, \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>X\<^bold>L\<^bold>T f \<^bold>\<star> \<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>S\<^bold>R\<^bold>C g, \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>X\<^bold>L\<^bold>T f \<^bold>\<star> \<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle>, \<^bold>\<langle>e (trg\<^sub>D h)\<^bold>\<rangle>, \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>D h)\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
           (\<^bold>X\<^bold>L\<^bold>T f \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle> \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h\<^bold>]) \<^bold>\<cdot>
           (\<^bold>X\<^bold>L\<^bold>T f \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle>, \<^bold>X\<^bold>L\<^bold>T h\<^bold>]) \<^bold>\<cdot>
           (\<^bold>X\<^bold>L\<^bold>T f \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e (trg\<^sub>D g)\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d (src\<^sub>D g)\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>X\<^bold>L\<^bold>T h) \<^bold>\<cdot>
           \<^bold>\<a>\<^bold>[\<^bold>X\<^bold>L\<^bold>T f, \<^bold>X\<^bold>L\<^bold>T g, \<^bold>X\<^bold>L\<^bold>T h\<^bold>]"

      have E: "?LHS = ?RHS"
      proof -
        have "?LHS = \<lbrace>?LHSt\<rbrace>"
          using assms D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                D.VV.ide_char D.VV.arr_char
          by simp
        also have "... = \<lbrace>?RHSt\<rbrace>"
          using assms by (intro E.eval_eqI, auto)
        also have "... = ?RHS"
          using assms D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                D.VV.ide_char D.VV.arr_char
          by simp
        finally show ?thesis by blast
      qed
      show ?thesis
        using L R E by argo
    qed

    interpretation XLT: weak_arrow_of_homs V\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D src\<^sub>D trg\<^sub>D XLT
    proof
      have *: "\<And>a. D.obj a \<Longrightarrow> e a \<star>\<^sub>D a \<star>\<^sub>D d a \<cong>\<^sub>D F.map\<^sub>0 (G\<^sub>0 a)"
      proof -
        fix a
        assume a: "D.obj a"
        interpret e: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                       \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
          using a equivalence_ed\<eta>\<epsilon> by simp
        have "F.map\<^sub>0 (G\<^sub>0 a) \<cong>\<^sub>D e a \<star>\<^sub>D a \<star>\<^sub>D d a"
        proof -
            have "F.map\<^sub>0 (G\<^sub>0 a) \<cong>\<^sub>D e a \<star>\<^sub>D d a"
              using a D.isomorphic_def e.counit_in_vhom
              by (metis D.isomorphic_symmetric e.antipar(2) e.counit_is_iso e_simps(4))
            also have "... \<cong>\<^sub>D e a \<star>\<^sub>D a \<star>\<^sub>D d a"
            proof -
              have "d a \<cong>\<^sub>D a \<star>\<^sub>D d a"
                using a D.isomorphic_def
                by (metis D.iso_lunit' D.lunit'_in_vhom d_simps(3) e.ide_right)
              thus ?thesis
                using a by (simp add: D.hcomp_ide_isomorphic)
            qed
            finally show ?thesis by simp
        qed
        thus "e a \<star>\<^sub>D a \<star>\<^sub>D d a \<cong>\<^sub>D F.map\<^sub>0 (G\<^sub>0 a)"
          by (simp add: D.isomorphic_symmetric)
      qed
      show "\<And>\<mu>. D.arr \<mu> \<Longrightarrow> e (trg\<^sub>D (src\<^sub>D \<mu>)) \<star>\<^sub>D src\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D (src\<^sub>D \<mu>)) \<cong>\<^sub>D
                             src\<^sub>D (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>))"
        using * by simp
      show "\<And>\<mu>. D.arr \<mu> \<Longrightarrow> e (trg\<^sub>D (trg\<^sub>D \<mu>)) \<star>\<^sub>D trg\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D (trg\<^sub>D \<mu>)) \<cong>\<^sub>D
                             trg\<^sub>D (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>))"
        using * by simp
    qed

    interpretation HoXLT_XLT: composite_functor D.VV.comp  D.VV.comp V\<^sub>D XLT.FF
                                 \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>D snd \<mu>\<nu>\<close>
      ..
    interpretation XLToH: composite_functor D.VV.comp V\<^sub>D V\<^sub>D \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>D snd \<mu>\<nu>\<close> XLT
      ..

    interpretation CMP: transformation_by_components D.VV.comp V\<^sub>D HoXLT_XLT.map XLToH.map
                          \<open>\<lambda>\<mu>\<nu>. CMP (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close>
    proof
      show "\<And>fg. D.VV.ide fg \<Longrightarrow> \<guillemotleft>CMP (fst fg) (snd fg) : HoXLT_XLT.map fg \<Rightarrow>\<^sub>D XLToH.map fg\<guillemotright>"
        using CMP_in_hom D.VV.ide_char D.VV.arr_char XLT.FF_def by simp
      show "\<And>fg. D.VV.arr fg \<Longrightarrow>
                   CMP (fst (D.VV.cod fg)) (snd (D.VV.cod fg)) \<cdot>\<^sub>D HoXLT_XLT.map fg =
                   XLToH.map fg \<cdot>\<^sub>D CMP (fst (D.VV.dom fg)) (snd (D.VV.dom fg))"
        using CMP_naturality D.VV.ide_char D.VV.arr_char XLT.FF_def by simp
    qed

    interpretation CMP: natural_isomorphism D.VV.comp V\<^sub>D HoXLT_XLT.map XLToH.map CMP.map
    proof
      show "\<And>fg. D.VV.ide fg \<Longrightarrow> D.iso (CMP.map fg)"
        using iso_CMP D.VV.ide_char D.VV.arr_char CMP.map_simp_ide by simp
    qed

    interpretation XLT: pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D XLT CMP.map
      using CMP_coherence D.VV.ide_char D.VV.arr_char CMP.map_simp_ide
      by unfold_locales simp

    lemma pseudofunctor_XLT:
    shows "pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D XLT CMP.map"
      ..

    text \<open>
      For \<open>G\<close>, the component of the compositor at \<open>(f', g')\<close> is a 2-cell
      \[
         \<open>\<guillemotleft>\<Phi>\<^sub>0 (f', g') : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright>\<close>
      \]
      having the property \<open>F (\<Phi>\<^sub>0 (f', g')) = F\<Phi>\<^sub>0 f' g'\<close>, where
      \[
        \<open>F\<Phi>\<^sub>0 f' g' =
         D.inv (\<phi> (f' \<star>\<^sub>D g')) \<cdot>\<^sub>D CMP f' g' \<cdot>\<^sub>D (\<phi> f' \<star>\<^sub>D \<phi> g') \<cdot>\<^sub>D D.inv (\<Phi> (G f', G g'))\<close>.
      \]
      It is unique due to the faithfulness of \<open>F\<close>.
    \<close>

    abbreviation (input) F\<Phi>\<^sub>0
    where "F\<Phi>\<^sub>0 f' g' \<equiv>
           D.inv (\<phi> (f' \<star>\<^sub>D g')) \<cdot>\<^sub>D CMP f' g' \<cdot>\<^sub>D (\<phi> f' \<star>\<^sub>D \<phi> g') \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>F (G f', G g'))"

    definition \<Phi>\<^sub>0
    where "\<Phi>\<^sub>0 \<equiv> \<lambda>(f', g'). THE \<mu>. \<guillemotleft>\<mu> : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright> \<and> F \<mu> = F\<Phi>\<^sub>0 f' g'"

    lemma \<Phi>\<^sub>0_props:
    assumes "D.ide f'" and "D.ide g'" and "src\<^sub>D f' = trg\<^sub>D g'"
    shows "\<guillemotleft>\<Phi>\<^sub>0 (f', g') : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright>"
    and "F (\<Phi>\<^sub>0 (f', g')) = F\<Phi>\<^sub>0 f' g'"
    proof -
      have "\<exists>!\<mu>. \<guillemotleft>\<mu> : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright> \<and> F \<mu> = F\<Phi>\<^sub>0 f' g'"
      proof -
        have "\<guillemotleft>F\<Phi>\<^sub>0 f' g' : F (G f' \<star>\<^sub>C G g') \<Rightarrow>\<^sub>D F (G (f' \<star>\<^sub>D g'))\<guillemotright>"
          using assms FG\<^sub>1_iso \<phi>_props C.in_hhom_def by auto
        hence "\<exists>\<mu>. \<guillemotleft>\<mu> : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright> \<and> F \<mu> = F\<Phi>\<^sub>0 f' g'"
          using assms F.locally_full C.ide_hcomp C.ideD(1) C.hcomp_simps(1-2) D.ide_hcomp
                D.ideD(1) D.hcomp_simps(1-2) G.preserves_ide G.preserves_src G.preserves_trg
          by presburger
        moreover have "\<And>\<mu> \<nu>. \<guillemotleft>\<mu> : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright> \<and> F \<mu> = F\<Phi>\<^sub>0 f' g' \<and>
                              \<guillemotleft>\<nu> : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright> \<and> F \<nu> = F\<Phi>\<^sub>0 f' g'
                                \<Longrightarrow> \<mu> = \<nu>"
          using assms F.is_faithful C.in_homE by metis
        ultimately show ?thesis by auto
      qed
      hence 1: "\<guillemotleft>\<Phi>\<^sub>0 (f', g') : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright> \<and> F (\<Phi>\<^sub>0 (f', g')) = F\<Phi>\<^sub>0 f' g'"
        using \<Phi>\<^sub>0_def
              the1_equality [of "\<lambda>\<mu>. \<guillemotleft>\<mu> : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright> \<and> F \<mu> = F\<Phi>\<^sub>0 f' g'"]
        by auto
      show "\<guillemotleft>\<Phi>\<^sub>0 (f', g') : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright>"
        using 1 by simp
      show "F (\<Phi>\<^sub>0 (f', g')) = F\<Phi>\<^sub>0 f' g'"
        using 1 by simp
    qed

    lemma \<Phi>\<^sub>0_in_hom [intro]:
    assumes "D.ide f'" and "D.ide g'" and "src\<^sub>D f' = trg\<^sub>D g'"
    shows "\<guillemotleft>\<Phi>\<^sub>0 (f', g') : src\<^sub>C (G g') \<rightarrow>\<^sub>C trg\<^sub>C (G f')\<guillemotright>"
    and "\<guillemotleft>\<Phi>\<^sub>0 (f', g') : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright>"
    proof -
      show "\<guillemotleft>\<Phi>\<^sub>0 (f', g') : G f' \<star>\<^sub>C G g' \<Rightarrow>\<^sub>C G (f' \<star>\<^sub>D g')\<guillemotright>"
        using assms \<Phi>\<^sub>0_props by simp
      thus "\<guillemotleft>\<Phi>\<^sub>0 (f', g') : src\<^sub>C (G g') \<rightarrow>\<^sub>C trg\<^sub>C (G f')\<guillemotright>"
        using assms C.src_dom C.trg_dom by fastforce
    qed

    lemma \<Phi>\<^sub>0_simps [simp]:
    assumes "D.ide f'" and "D.ide g'" and "src\<^sub>D f' = trg\<^sub>D g'"
    shows "C.arr (\<Phi>\<^sub>0 (f', g'))"
    and "src\<^sub>C (\<Phi>\<^sub>0 (f', g')) = src\<^sub>C (G g')" and "trg\<^sub>C (\<Phi>\<^sub>0 (f', g')) = trg\<^sub>C (G f')"
    and "C.dom (\<Phi>\<^sub>0 (f', g')) = G f' \<star>\<^sub>C G g'" and "C.cod (\<Phi>\<^sub>0 (f', g')) = G (f' \<star>\<^sub>D g')"
      using assms \<Phi>\<^sub>0_in_hom
          apply auto
      by blast+

    lemma F\<Phi>\<^sub>0_naturality:
    assumes "D.arr \<mu>" and "D.arr \<nu>" and "src\<^sub>D \<mu> = trg\<^sub>D \<nu>"
    shows "F\<Phi>\<^sub>0 (D.cod \<mu>) (D.cod \<nu>) \<cdot>\<^sub>D F (G \<mu> \<star>\<^sub>C G \<nu>) =
           F (GoH\<^sub>D.map (\<mu>, \<nu>)) \<cdot>\<^sub>D F\<Phi>\<^sub>0 (D.dom \<mu>) (D.dom \<nu>)"
    proof -
      have "F\<Phi>\<^sub>0 (D.cod \<mu>) (D.cod \<nu>) \<cdot>\<^sub>D F (G \<mu> \<star>\<^sub>C G \<nu>) =
            D.inv (\<phi> (D.cod \<mu> \<star>\<^sub>D D.cod \<nu>)) \<cdot>\<^sub>D CMP (D.cod \<mu>) (D.cod \<nu>) \<cdot>\<^sub>D
                         ((\<phi> (D.cod \<mu>) \<star>\<^sub>D \<phi> (D.cod \<nu>)) \<cdot>\<^sub>D (F (G \<mu>) \<star>\<^sub>D F (G \<nu>))) \<cdot>\<^sub>D
                         D.inv (\<Phi>\<^sub>F (G (D.dom \<mu>), G (D.dom \<nu>)))"
      proof -
        have "D.inv (\<Phi>\<^sub>F (G (D.cod \<mu>), G (D.cod \<nu>))) \<cdot>\<^sub>D F (G \<mu> \<star>\<^sub>C G \<nu>) =
              (F (G \<mu>) \<star>\<^sub>D F (G \<nu>)) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>F (G (D.dom \<mu>), G (D.dom \<nu>)))"
        proof -
          have "\<Phi>\<^sub>F (G (D.cod \<mu>), G (D.cod \<nu>)) \<cdot>\<^sub>D (F (G \<mu>) \<star>\<^sub>D F (G \<nu>)) =
                F (G \<mu> \<star>\<^sub>C G \<nu>) \<cdot>\<^sub>D \<Phi>\<^sub>F (G (D.dom \<mu>), G (D.dom \<nu>))"
            using assms C.VV.arr_char F.\<Phi>.naturality [of "(G \<mu>, G \<nu>)"] F.FF_def by simp
          moreover have "D.seq (\<Phi>\<^sub>F (G (D.cod \<mu>), G (D.cod \<nu>))) (F (G \<mu>) \<star>\<^sub>D F (G \<nu>))"
            using assms F.preserves_hcomp C.VV.arr_char F.FF_def by auto
          ultimately show ?thesis
            using assms D.invert_opposite_sides_of_square by simp
        qed
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = D.inv (\<phi> (D.cod \<mu> \<star>\<^sub>D D.cod \<nu>)) \<cdot>\<^sub>D
                         (CMP (D.cod \<mu>) (D.cod \<nu>) \<cdot>\<^sub>D
                         (XLT \<mu> \<star>\<^sub>D XLT \<nu>)) \<cdot>\<^sub>D
                         (\<phi> (D.dom \<mu>) \<star>\<^sub>D \<phi> (D.dom \<nu>)) \<cdot>\<^sub>D
                         D.inv (\<Phi>\<^sub>F (G (D.dom \<mu>), G (D.dom \<nu>)))"
      proof -
        have "(\<phi> (D.cod \<mu>) \<star>\<^sub>D \<phi> (D.cod \<nu>)) \<cdot>\<^sub>D (F (G \<mu>) \<star>\<^sub>D F (G \<nu>)) =
              (XLT \<mu> \<star>\<^sub>D XLT \<nu>) \<cdot>\<^sub>D (\<phi> (D.dom \<mu>) \<star>\<^sub>D \<phi> (D.dom \<nu>))"
        proof -
          have "(\<phi> (D.cod \<mu>) \<star>\<^sub>D \<phi> (D.cod \<nu>)) \<cdot>\<^sub>D (F (G \<mu>) \<star>\<^sub>D F (G \<nu>)) =
                \<phi> (D.cod \<mu>) \<cdot>\<^sub>D F (G \<mu>) \<star>\<^sub>D \<phi> (D.cod \<nu>) \<cdot>\<^sub>D F (G \<nu>)"
            using assms D.interchange by simp
          also have "... = (XLT \<mu> \<cdot>\<^sub>D \<phi> (D.dom \<mu>)) \<star>\<^sub>D (XLT \<nu> \<cdot>\<^sub>D \<phi> (D.dom \<nu>))"
            using assms \<phi>.map_def \<phi>.naturality [of \<mu>] \<phi>.naturality [of \<nu>] by fastforce
          also have "... = (XLT \<mu> \<star>\<^sub>D XLT \<nu>) \<cdot>\<^sub>D (\<phi> (D.dom \<mu>) \<star>\<^sub>D \<phi> (D.dom \<nu>))"
            using assms D.interchange by simp
          finally show ?thesis by simp
        qed
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = (D.inv (\<phi> (D.cod \<mu> \<star>\<^sub>D D.cod \<nu>)) \<cdot>\<^sub>D
                         XLT (\<mu> \<star>\<^sub>D \<nu>)) \<cdot>\<^sub>D
                         CMP (D.dom \<mu>) (D.dom \<nu>) \<cdot>\<^sub>D
                         (\<phi> (D.dom \<mu>) \<star>\<^sub>D \<phi> (D.dom \<nu>)) \<cdot>\<^sub>D
                         D.inv (\<Phi>\<^sub>F (G (D.dom \<mu>), G (D.dom \<nu>)))"
        using assms CMP_naturality D.comp_assoc by simp
      also have "... = F (G (\<mu> \<star>\<^sub>D \<nu>)) \<cdot>\<^sub>D D.inv (\<phi> (D.dom \<mu> \<star>\<^sub>D D.dom \<nu>)) \<cdot>\<^sub>D
                         CMP (D.dom \<mu>) (D.dom \<nu>) \<cdot>\<^sub>D
                         (\<phi> (D.dom \<mu>) \<star>\<^sub>D \<phi> (D.dom \<nu>)) \<cdot>\<^sub>D
                         D.inv (\<Phi>\<^sub>F (G (D.dom \<mu>), G (D.dom \<nu>)))"
      proof -
        have "D.inv (\<phi> (D.cod \<mu> \<star>\<^sub>D D.cod \<nu>)) \<cdot>\<^sub>D XLT (\<mu> \<star>\<^sub>D \<nu>) =
              F (G (\<mu> \<star>\<^sub>D \<nu>)) \<cdot>\<^sub>D D.inv (\<phi> (D.dom \<mu> \<star>\<^sub>D D.dom \<nu>))"
          using assms \<phi>.naturality [of "\<mu> \<star>\<^sub>D \<nu>"] \<phi>_props(2)
                D.invert_opposite_sides_of_square
                  [of "\<phi> (D.cod \<mu> \<star>\<^sub>D D.cod \<nu>)" "F (G (\<mu> \<star>\<^sub>D \<nu>))" "XLT (\<mu> \<star>\<^sub>D \<nu>)"
                      "\<phi> (D.dom \<mu> \<star>\<^sub>D D.dom \<nu>)"]
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = F (GoH\<^sub>D.map (\<mu>, \<nu>)) \<cdot>\<^sub>D F\<Phi>\<^sub>0 (D.dom \<mu>) (D.dom \<nu>)"
        using assms D.comp_assoc by simp
      finally show ?thesis by simp
    qed

    interpretation \<Phi>: transformation_by_components D.VV.comp V\<^sub>C H\<^sub>DoGG.map GoH\<^sub>D.map \<Phi>\<^sub>0
    proof
      show 1: "\<And>a. D.VV.ide a \<Longrightarrow> \<guillemotleft>\<Phi>\<^sub>0 a : H\<^sub>DoGG.map a \<Rightarrow>\<^sub>C GoH\<^sub>D.map a\<guillemotright>"
        using D.VV.ide_char D.VV.arr_char \<Phi>\<^sub>0_props G.FF_def by auto
      show "\<And>\<mu>\<nu>. D.VV.arr \<mu>\<nu> \<Longrightarrow>
                 \<Phi>\<^sub>0 (D.VV.cod \<mu>\<nu>) \<cdot>\<^sub>C H\<^sub>DoGG.map \<mu>\<nu> = GoH\<^sub>D.map \<mu>\<nu> \<cdot>\<^sub>C \<Phi>\<^sub>0 (D.VV.dom \<mu>\<nu>)"
      proof -
        fix \<mu>\<nu>
        assume \<mu>\<nu>: "D.VV.arr \<mu>\<nu>"
        define \<mu> where "\<mu> = fst \<mu>\<nu>"
        define \<nu> where "\<nu> = snd \<mu>\<nu>"
        have \<mu>: "D.arr \<mu>"
          using \<mu>_def \<mu>\<nu> D.VV.arr_char by simp
        have \<nu>: "D.arr \<nu>"
          using \<nu>_def \<mu>\<nu> D.VV.arr_char by simp
        have \<mu>\<nu>: "src\<^sub>D \<mu> = trg\<^sub>D \<nu>"
          using \<mu>_def \<nu>_def \<mu>\<nu> D.VV.arr_char by simp
        have "F (\<Phi>\<^sub>0 (D.VV.cod \<mu>\<nu>) \<cdot>\<^sub>C H\<^sub>DoGG.map \<mu>\<nu>) = F (\<Phi>\<^sub>0 (D.VV.cod \<mu>\<nu>)) \<cdot>\<^sub>D F (H\<^sub>DoGG.map \<mu>\<nu>)"
          using 1 \<mu>_def \<nu>_def \<mu> \<nu> \<mu>\<nu> \<Phi>\<^sub>0_props D.VV.arr_char G.FF_def by simp
        also have "... = F\<Phi>\<^sub>0 (D.cod \<mu>) (D.cod \<nu>) \<cdot>\<^sub>D F (G \<mu> \<star>\<^sub>C G \<nu>)"
          using \<mu>_def \<nu>_def \<mu> \<nu> \<mu>\<nu> \<Phi>\<^sub>0_props D.VV.cod_char G.FF_def by auto
        also have "... = F (GoH\<^sub>D.map \<mu>\<nu>) \<cdot>\<^sub>D F\<Phi>\<^sub>0 (D.dom \<mu>) (D.dom \<nu>)"
          using \<mu>_def \<nu>_def \<mu> \<nu> \<mu>\<nu> F\<Phi>\<^sub>0_naturality by simp
        also have "... = F (GoH\<^sub>D.map \<mu>\<nu> \<cdot>\<^sub>C \<Phi>\<^sub>0 (D.VV.dom \<mu>\<nu>))"
          using \<mu>_def \<nu>_def \<mu> \<nu> \<mu>\<nu> \<Phi>\<^sub>0_props D.VV.dom_char by auto
        finally have "F (\<Phi>\<^sub>0 (D.VV.cod \<mu>\<nu>) \<cdot>\<^sub>C H\<^sub>DoGG.map \<mu>\<nu>) = F (GoH\<^sub>D.map \<mu>\<nu> \<cdot>\<^sub>C \<Phi>\<^sub>0 (D.VV.dom \<mu>\<nu>))"
          by simp
        moreover have "C.par (\<Phi>\<^sub>0 (D.VV.cod \<mu>\<nu>) \<cdot>\<^sub>C H\<^sub>DoGG.map \<mu>\<nu>)
                             (GoH\<^sub>D.map \<mu>\<nu> \<cdot>\<^sub>C \<Phi>\<^sub>0 (D.VV.dom \<mu>\<nu>))"
          using \<mu>_def \<nu>_def \<mu> \<nu> \<mu>\<nu> \<Phi>\<^sub>0_props D.VV.arr_char D.VV.dom_char D.VV.cod_char
                D.VV.ide_char G.FF_def
          by auto
        ultimately show "\<Phi>\<^sub>0 (D.VV.cod \<mu>\<nu>) \<cdot>\<^sub>C H\<^sub>DoGG.map \<mu>\<nu> = GoH\<^sub>D.map \<mu>\<nu> \<cdot>\<^sub>C \<Phi>\<^sub>0 (D.VV.dom \<mu>\<nu>)"
          using F.is_faithful by blast
      qed
    qed

    abbreviation \<Phi>
    where "\<Phi> \<equiv> \<Phi>.map"

    lemma \<Phi>_in_hom [intro]:
    assumes "D.arr \<mu>'" and "D.arr \<nu>'" and "src\<^sub>D \<mu>' = trg\<^sub>D \<nu>'"
    shows "\<guillemotleft>\<Phi> (\<mu>', \<nu>') : src\<^sub>C (G (D.dom \<nu>')) \<rightarrow>\<^sub>C trg\<^sub>C (G (D.cod \<mu>'))\<guillemotright>"
    and "\<guillemotleft>\<Phi> (\<mu>', \<nu>') : G (D.dom \<mu>') \<star>\<^sub>C G (D.dom \<nu>') \<Rightarrow>\<^sub>C G (D.cod \<mu>' \<star>\<^sub>D D.cod \<nu>')\<guillemotright>"
    proof -
      show "\<guillemotleft>\<Phi> (\<mu>', \<nu>') : G (D.dom \<mu>') \<star>\<^sub>C G (D.dom \<nu>') \<Rightarrow>\<^sub>C G (D.cod \<mu>' \<star>\<^sub>D D.cod \<nu>')\<guillemotright>"
        using assms D.VV.arr_char D.VV.dom_char D.VV.cod_char \<Phi>.map_def G.FF_def by simp
      thus "\<guillemotleft>\<Phi> (\<mu>', \<nu>') : src\<^sub>C (G (D.dom \<nu>')) \<rightarrow>\<^sub>C trg\<^sub>C (G (D.cod \<mu>'))\<guillemotright>"
        using assms C.src_dom [of "\<Phi> (\<mu>', \<nu>')"] C.trg_dom [of "\<Phi> (\<mu>', \<nu>')"] by auto
    qed

    lemma \<Phi>_simps [simp]:
    assumes "D.arr \<mu>'" and "D.arr \<nu>'" and "src\<^sub>D \<mu>' = trg\<^sub>D \<nu>'"
    shows "C.arr (\<Phi> (\<mu>', \<nu>'))"
    and "src\<^sub>C (\<Phi> (\<mu>', \<nu>')) = src\<^sub>C (G (D.dom \<nu>'))" and "trg\<^sub>C (\<Phi> (\<mu>', \<nu>')) = trg\<^sub>C (G (D.cod \<mu>'))"
    and "C.dom (\<Phi> (\<mu>', \<nu>')) = G (D.dom \<mu>') \<star>\<^sub>C G (D.dom \<nu>')"
    and "C.cod (\<Phi> (\<mu>', \<nu>')) = G (D.cod \<mu>' \<star>\<^sub>D D.cod \<nu>')"
      using assms \<Phi>_in_hom
          apply auto
      by blast+

    interpretation \<Phi>: natural_isomorphism D.VV.comp V\<^sub>C H\<^sub>DoGG.map GoH\<^sub>D.map \<Phi>
    proof
      fix fg
      assume fg: "D.VV.ide fg"
      let ?f = "fst fg"
      let ?g = "snd fg"
      have f: "D.ide ?f"
        using fg D.VV.ide_char by simp
      have g: "D.ide ?g"
        using fg D.VV.ide_char by simp
      have fg: "src\<^sub>D ?f = trg\<^sub>D ?g"
        using fg D.VV.ide_char D.VV.arr_char by simp
      have "D.iso (F (\<Phi> fg))"
      proof -
        have "F (\<Phi> fg) =
              D.inv (\<phi> (?f \<star>\<^sub>D ?g)) \<cdot>\<^sub>D CMP ?f ?g \<cdot>\<^sub>D (\<phi> ?f \<star>\<^sub>D \<phi> ?g) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>F (G ?f, G ?g))"
          using f g fg \<Phi>\<^sub>0_props [of ?f ?g] D.VV.ide_char D.VV.arr_char D.comp_assoc CMP_def
          by simp
        moreover have "D.iso ..."
          using f g fg D.VV.arr_char D.iso_inv_iso \<phi>_props iso_CMP
          by (intro D.isos_compose) simp_all
        ultimately show ?thesis by simp
      qed
      thus "C.iso (\<Phi> fg)"
        using F.reflects_iso by blast
    qed

    interpretation G: pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>
    proof
      fix f g h
      assume f: "D.ide f"
      assume g: "D.ide g"
      assume h: "D.ide h"
      assume fg: "src\<^sub>D f = trg\<^sub>D g"
      assume gh: "src\<^sub>D g = trg\<^sub>D h"
      show "G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi> (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi> (f, g) \<star>\<^sub>C G h) =
            \<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h]"
      proof -
        have LHS: "\<guillemotleft>G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi> (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi> (f, g) \<star>\<^sub>C G h) :
                     (G f \<star>\<^sub>C G g) \<star>\<^sub>C G h \<Rightarrow>\<^sub>C G (f \<star>\<^sub>D g \<star>\<^sub>D h)\<guillemotright>"
        proof
          show "\<guillemotleft>\<Phi> (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi> (f, g) \<star>\<^sub>C G h) :
                  (G f \<star>\<^sub>C G g) \<star>\<^sub>C G h \<Rightarrow>\<^sub>C G ((f \<star>\<^sub>D g) \<star>\<^sub>D h)\<guillemotright>"
            using f g h fg gh D.VV.arr_char D.VV.ide_char by simp
          show "\<guillemotleft>G \<a>\<^sub>D[f, g, h] : G ((f \<star>\<^sub>D g) \<star>\<^sub>D h) \<Rightarrow>\<^sub>C G (f \<star>\<^sub>D g \<star>\<^sub>D h)\<guillemotright>"
            using f g h fg gh by auto
        qed
        have RHS: "\<guillemotleft>\<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h] :
                     (G f \<star>\<^sub>C G g) \<star>\<^sub>C G h \<Rightarrow>\<^sub>C G (f \<star>\<^sub>D g \<star>\<^sub>D h)\<guillemotright>"
        proof -
          have "\<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h] =
                (\<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h))) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h]"
            using C.comp_assoc by simp
          moreover
          have "\<guillemotleft>(\<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h))) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h] :
                     (G f \<star>\<^sub>C G g) \<star>\<^sub>C G h \<Rightarrow>\<^sub>C G (f \<star>\<^sub>D g \<star>\<^sub>D h)\<guillemotright>"
            using f g h fg gh D.VV.arr_char D.VV.ide_char by auto
         ultimately show ?thesis by simp
        qed
        have "F (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi> (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi> (f, g) \<star>\<^sub>C G h)) =
              F (\<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h])"
        proof -
          have "F (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi> (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi> (f, g) \<star>\<^sub>C G h)) =
                F (G \<a>\<^sub>D[f, g, h]) \<cdot>\<^sub>D F (\<Phi> (f \<star>\<^sub>D g, h)) \<cdot>\<^sub>D F (\<Phi> (f, g) \<star>\<^sub>C G h)"
            using f g h fg gh D.VV.arr_char D.VV.ide_char by simp
          also have "... = (D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                             \<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h)) \<cdot>\<^sub>D F (\<Phi> (f \<star>\<^sub>D g, h)) \<cdot>\<^sub>D F (\<Phi> (f, g) \<star>\<^sub>C G h)"
            using f g h fg gh FG_eq by fastforce
          also have "... = (D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                             \<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h)) \<cdot>\<^sub>D F\<Phi>\<^sub>0 (f \<star>\<^sub>D g) h \<cdot>\<^sub>D F (\<Phi> (f, g) \<star>\<^sub>C G h)"
            using f g h fg gh \<Phi>.map_simp_ide \<Phi>\<^sub>0_props D.VV.arr_char
                  D.VV.ide_char G.FF_def
            by auto
          also have "... = (D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                             \<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h)) \<cdot>\<^sub>D F\<Phi>\<^sub>0 (f \<star>\<^sub>D g) h \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (C.cod (\<Phi>.map (f, g)), G h) \<cdot>\<^sub>D
                             (F (\<Phi>.map (f, g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (C.dom (\<Phi>.map (f, g)), G h))"
          proof -
            have "C.hseq (\<Phi> (f, g)) (G h)"
              using f g h fg gh \<Phi>_in_hom [of f g]
              by (intro C.hseqI) auto
            thus ?thesis
              using f g h fg gh F.preserves_hcomp by auto
          qed
          also have "... = (D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                             \<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h)) \<cdot>\<^sub>D F\<Phi>\<^sub>0 (f \<star>\<^sub>D g) h \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G (f \<star>\<^sub>D g), G h) \<cdot>\<^sub>D
                             (F (\<Phi>.map (f, g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using f g h fg gh \<Phi>\<^sub>0_in_hom [of f g] \<Phi>.map_def D.VV.arr_char G.FF_def by simp
          also have "... = (D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                             \<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h)) \<cdot>\<^sub>D F\<Phi>\<^sub>0 (f \<star>\<^sub>D g) h \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G (f \<star>\<^sub>D g), G h) \<cdot>\<^sub>D
                             (F\<Phi>\<^sub>0 f g \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using f g h fg gh \<Phi>.map_simp_ide \<Phi>\<^sub>0_props [of f g] D.VV.arr_char D.VV.ide_char
                  G.FF_def
            by auto
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                             \<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h) \<cdot>\<^sub>D
                             D.inv (\<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             CMP (f \<star>\<^sub>D g) h \<cdot>\<^sub>D
                             (\<phi> (f \<star>\<^sub>D g) \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G (f \<star>\<^sub>D g), G h) \<cdot>\<^sub>D
                             (D.inv (\<phi> (f \<star>\<^sub>D g)) \<cdot>\<^sub>D
                                CMP f g \<cdot>\<^sub>D (\<phi> f \<star>\<^sub>D \<phi> g) \<cdot>\<^sub>D
                                D.inv (\<Phi>\<^sub>F (G f, G g))
                               \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using D.comp_assoc by simp
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                             ((\<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h) \<cdot>\<^sub>D
                             D.inv (\<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h))) \<cdot>\<^sub>D
                             CMP (f \<star>\<^sub>D g) h) \<cdot>\<^sub>D
                             (((\<phi> (f \<star>\<^sub>D g) \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D
                             ((D.inv (\<Phi>\<^sub>F (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                             (D.inv (\<phi> (f \<star>\<^sub>D g)) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                             (CMP f g \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D 
                             ((\<phi> f \<star>\<^sub>D \<phi> g) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using f g h fg gh \<phi>_props(2) D.whisker_right D.comp_assoc by simp
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                               XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                               CMP (f \<star>\<^sub>D g) h \<cdot>\<^sub>D
                               ((XLT (f \<star>\<^sub>D g) \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D
                               (CMP f g \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D 
                               ((\<phi> f \<star>\<^sub>D \<phi> g) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                               (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                               D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
          proof -
            have "(\<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h) \<cdot>\<^sub>D D.inv (\<phi> ((f \<star>\<^sub>D g) \<star>\<^sub>D h))) \<cdot>\<^sub>D CMP (f \<star>\<^sub>D g) h =
                  CMP (f \<star>\<^sub>D g) h"
              using f g h fg gh \<phi>_props(2) D.comp_arr_inv' D.comp_cod_arr by simp
            moreover have "(\<phi> (f \<star>\<^sub>D g) \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D
                             ((D.inv (\<Phi>\<^sub>F (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D \<Phi>\<^sub>F (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                             (D.inv (\<phi> (f \<star>\<^sub>D g)) \<star>\<^sub>D F (G h))) =
                           XLT (f \<star>\<^sub>D g) \<star>\<^sub>D \<phi> h"
              using f g h fg gh \<phi>_props(2) D.comp_arr_inv' D.comp_inv_arr'
                    D.comp_arr_dom D.comp_cod_arr
                    D.interchange [of "\<phi> (f \<star>\<^sub>D g)" "D.inv (\<phi> (f \<star>\<^sub>D g))" "\<phi> h" "F (G h)"]
              by simp
            ultimately show ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                               XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                               CMP (f \<star>\<^sub>D g) h \<cdot>\<^sub>D
                               ((CMP f g \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D ((\<phi> f \<star>\<^sub>D \<phi> g) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                               (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                               D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
          proof -
            have "(XLT (f \<star>\<^sub>D g) \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D (CMP f g \<star>\<^sub>D F (G h)) = CMP f g \<star>\<^sub>D \<phi> h"
              using f g h fg gh D.comp_arr_dom D.comp_cod_arr
                    D.interchange [of "XLT (f \<star>\<^sub>D g)" "CMP f g" "\<phi> h" "F (G h)"]
              by simp
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                               (XLT \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                               CMP (f \<star>\<^sub>D g) h \<cdot>\<^sub>D (CMP f g \<star>\<^sub>D XLT h)) \<cdot>\<^sub>D
                               ((\<phi> f \<star>\<^sub>D \<phi> g) \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D
                               (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                               D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
          proof -
            have "(CMP f g \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D ((\<phi> f \<star>\<^sub>D \<phi> g) \<star>\<^sub>D F (G h)) =
                  (CMP f g \<star>\<^sub>D XLT h) \<cdot>\<^sub>D ((\<phi> f \<star>\<^sub>D \<phi> g) \<star>\<^sub>D \<phi> h)"
              using f g h fg gh D.comp_arr_dom D.comp_cod_arr
                    D.interchange [of "CMP f g" "\<phi> f \<star>\<^sub>D \<phi> g" "\<phi> h" "F (G h)"]
                    D.interchange [of "CMP f g" "\<phi> f \<star>\<^sub>D \<phi> g" "XLT h" "\<phi> h"]
              by simp
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                               CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D (XLT f \<star>\<^sub>D CMP g h) \<cdot>\<^sub>D
                               (\<a>\<^sub>D[XLT f, XLT g, XLT h] \<cdot>\<^sub>D
                               ((\<phi> f \<star>\<^sub>D \<phi> g) \<star>\<^sub>D \<phi> h)) \<cdot>\<^sub>D
                               (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                               D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using f g h fg gh CMP_coherence [of f g h] D.comp_assoc by simp
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                               CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D (XLT f \<star>\<^sub>D CMP g h) \<cdot>\<^sub>D
                               (\<phi> f \<star>\<^sub>D \<phi> g \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D
                               (\<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                               (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                               D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h)))"
            using f g h fg gh D.assoc_naturality [of "\<phi> f" "\<phi> g" "\<phi> h"] D.comp_assoc
            by simp
          finally have
            A: "F (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi> (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi> (f, g) \<star>\<^sub>C G h)) =
                D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                  CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D (XLT f \<star>\<^sub>D CMP g h) \<cdot>\<^sub>D
                  (\<phi> f \<star>\<^sub>D \<phi> g \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D
                  (\<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                  (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                  D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h)))"
            by simp

          have "F (\<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h]) =
                F (\<Phi> (f, g \<star>\<^sub>D h)) \<cdot>\<^sub>D F (G f \<star>\<^sub>C \<Phi> (g, h)) \<cdot>\<^sub>D F \<a>\<^sub>C[G f, G g, G h]"
            using f g h fg gh
            by (metis (no_types, lifting) C.arrI C.seqE F.preserves_comp RHS)
          also have "... = F\<Phi>\<^sub>0 f (g \<star>\<^sub>D h) \<cdot>\<^sub>D
                             F (G f \<star>\<^sub>C \<Phi>\<^sub>0 (g, h)) \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using f g h fg gh \<Phi>\<^sub>0_props D.VV.arr_char D.VV.cod_char D.VV.ide_char
                  F.preserves_assoc(1)
            by simp
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D
                             (\<phi> f \<star>\<^sub>D \<phi> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                             F (G f \<star>\<^sub>C \<Phi>\<^sub>0 (g, h)) \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using D.comp_assoc by simp
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D
                             (\<phi> f \<star>\<^sub>D \<phi> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                             (\<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D F (\<Phi>\<^sub>0 (g, h))) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using f g h fg gh F.preserves_hcomp by simp
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D
                             (\<phi> f \<star>\<^sub>D \<phi> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                             (\<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D
                               D.inv (\<phi> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                               CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D
                               D.inv (\<Phi>\<^sub>F (G g, G h))) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using f g h fg gh \<Phi>\<^sub>0_props by simp
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D
                             ((\<phi> f \<star>\<^sub>D \<phi> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D D.inv (\<phi> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h))) \<cdot>\<^sub>D
                             ((F (G f) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (G g, G h))) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h)) \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F (G f), F (G g), F (G h)]) \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            using f g h fg gh \<phi>_props(2) D.whisker_left D.comp_assoc by simp
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D
                             (\<phi> f \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
          proof -
            have "(\<phi> f \<star>\<^sub>D \<phi> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                    D.inv (\<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                    \<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                    (F (G f) \<star>\<^sub>D D.inv (\<phi> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                    (F (G f) \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h)) =
                  \<phi> f \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h)"
            proof -
              have "(\<phi> f \<star>\<^sub>D \<phi> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                      D.inv (\<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                      \<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                      (F (G f) \<star>\<^sub>D D.inv (\<phi> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                      (F (G f) \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h)) =
                    ((\<phi> f \<star>\<^sub>D \<phi> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                      ((D.inv (\<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                      \<Phi>\<^sub>F (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                      (F (G f) \<star>\<^sub>D D.inv (\<phi> (g \<star>\<^sub>D h))))) \<cdot>\<^sub>D
                      (F (G f) \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h))"
                using D.comp_assoc by simp
              also have "... = ((\<phi> f \<star>\<^sub>D \<phi> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                                 (F (G f) \<star>\<^sub>D D.inv (\<phi> (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                                 (F (G f) \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h))"
                using f g h fg gh \<phi>_props(2) D.comp_arr_inv' D.comp_inv_arr' D.comp_cod_arr
                by simp
              also have "... = (\<phi> f \<star>\<^sub>D XLT (g \<star>\<^sub>D h)) \<cdot>\<^sub>D (F (G f) \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h))"
                using f g h fg gh \<phi>_props(2) D.comp_arr_inv' D.comp_inv_arr'
                      D.comp_arr_dom D.comp_cod_arr
                      D.interchange [of "\<phi> f" "F (G f)" "\<phi> (g \<star>\<^sub>D h)" "D.inv (\<phi> (g \<star>\<^sub>D h))"]
                by simp
              also have "... = \<phi> f \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h)"
                using f g h fg gh \<phi>_props(2) D.comp_arr_dom D.comp_cod_arr
                      D.interchange [of "\<phi> f" "F (G f)" "XLT (g \<star>\<^sub>D h)" "CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h)"]
                by simp
              finally show ?thesis by simp
            qed
            moreover have "(F (G f) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (G g, G h))) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h)) \<cdot>\<^sub>D
                             \<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h) \<cdot>\<^sub>D
                             (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F (G f), F (G g), F (G h)] =
                           \<a>\<^sub>D[F (G f), F (G g), F (G h)]"
            proof -
              have "(F (G f) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (G g, G h))) \<cdot>\<^sub>D
                      D.inv (\<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h)) \<cdot>\<^sub>D
                      \<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h) \<cdot>\<^sub>D
                      (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h)) \<cdot>\<^sub>D
                      \<a>\<^sub>D[F (G f), F (G g), F (G h)] =
                    ((F (G f) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (G g, G h))) \<cdot>\<^sub>D
                      ((D.inv (\<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h)) \<cdot>\<^sub>D
                      \<Phi>\<^sub>F (G f, G g \<star>\<^sub>C G h)) \<cdot>\<^sub>D
                      (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h)))) \<cdot>\<^sub>D
                      \<a>\<^sub>D[F (G f), F (G g), F (G h)]"
                using D.comp_assoc by simp
              also have "... = ((F (G f) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (G g, G h))) \<cdot>\<^sub>D
                                 ((F (G f) \<star>\<^sub>D F (G g \<star>\<^sub>C G h)) \<cdot>\<^sub>D
                                 (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h)))) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F (G f), F (G g), F (G h)]"
                using f g h fg gh \<phi>_props(2) D.comp_arr_inv' D.comp_inv_arr'
                      D.comp_arr_dom D.comp_cod_arr
                by fastforce
              also have "... = ((F (G f) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (G g, G h))) \<cdot>\<^sub>D
                                 (F (G f) \<star>\<^sub>D \<Phi>\<^sub>F (G g, G h))) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[F (G f), F (G g), F (G h)]"
               proof -
                have "D.seq (F (G g \<star>\<^sub>C G h)) (\<Phi>\<^sub>F (G g, G h))"
                  using f g h fg gh by force
                thus ?thesis
                  using f g h fg gh \<phi>_props(2) D.comp_cod_arr by auto
              qed
              also have "... = \<a>\<^sub>D[F (G f), F (G g), F (G h)]"
                using f g h fg gh \<phi>_props(2) D.comp_arr_inv' D.comp_inv_arr'
                      D.comp_arr_dom D.comp_cod_arr
                      D.whisker_left [of "F (G f)" "D.inv (\<Phi>\<^sub>F (G g, G h))" "\<Phi>\<^sub>F (G g, G h)"]
                by auto
              finally show ?thesis by simp
            qed
            ultimately show ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                             CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D
                             (XLT f \<star>\<^sub>D CMP g h) \<cdot>\<^sub>D
                             (\<phi> f \<star>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
          proof -
            have "\<phi> f \<star>\<^sub>D CMP g h \<cdot>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h) =
                  (XLT f \<star>\<^sub>D CMP g h) \<cdot>\<^sub>D (\<phi> f \<star>\<^sub>D (\<phi> g \<star>\<^sub>D \<phi> h))"
              using f g h fg gh D.comp_cod_arr
                    D.interchange [of "XLT f" "\<phi> f" "CMP g h" "\<phi> g \<star>\<^sub>D \<phi> h"]
              by auto
            thus ?thesis
              using D.comp_assoc by simp
          qed
          finally have
            B: "F (\<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h]) =
                D.inv (\<phi> (f \<star>\<^sub>D g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                  CMP f (g \<star>\<^sub>D h) \<cdot>\<^sub>D (XLT f \<star>\<^sub>D CMP g h) \<cdot>\<^sub>D
                  (\<phi> f \<star>\<^sub>D \<phi> g \<star>\<^sub>D \<phi> h) \<cdot>\<^sub>D
                  \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                  (D.inv (\<Phi>\<^sub>F (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                  D.inv (\<Phi>\<^sub>F (G f \<star>\<^sub>C G g, G h))"
            by simp
          show ?thesis using A B by argo
        qed
        moreover have "C.par (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi> (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi> (f, g) \<star>\<^sub>C G h))
                             (\<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h])"
          using LHS RHS by (metis (no_types, lifting) C.in_homE)
        ultimately show ?thesis
          using F.is_faithful [of "G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi> (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi> (f, g) \<star>\<^sub>C G h)"
                                  "\<Phi> (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi> (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h]"]
          by simp
      qed
    qed

    interpretation faithful_functor V\<^sub>D V\<^sub>C G
    proof
      fix \<mu> \<mu>'
      assume par: "D.par \<mu> \<mu>'"
      assume eq: "G \<mu> = G \<mu>'"
      have \<mu>: "\<guillemotleft>\<mu> : src\<^sub>D \<mu> \<rightarrow>\<^sub>D src\<^sub>D (e (trg\<^sub>D \<mu>))\<guillemotright>"
        using par by simp
      hence \<mu>': "\<guillemotleft>\<mu>' : src\<^sub>D \<mu> \<rightarrow>\<^sub>D src\<^sub>D (e (trg\<^sub>D \<mu>))\<guillemotright>"
        using par by (metis D.in_hhom_def D.src_dom D.trg_dom)
      interpret e_src: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         \<open>e (src\<^sub>D \<mu>)\<close> \<open>d (src\<^sub>D \<mu>)\<close> \<open>\<eta> (src\<^sub>D \<mu>)\<close> \<open>\<epsilon> (src\<^sub>D \<mu>)\<close>
        using \<mu> equivalence_ed\<eta>\<epsilon> by auto
      interpret e_trg: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         \<open>e (trg\<^sub>D \<mu>)\<close> \<open>d (trg\<^sub>D \<mu>)\<close> \<open>\<eta> (trg\<^sub>D \<mu>)\<close> \<open>\<epsilon> (trg\<^sub>D \<mu>)\<close>
        using \<mu> equivalence_ed\<eta>\<epsilon> by auto
      have d_src: "D.equivalence_map (d (src\<^sub>D \<mu>))"
        using e_src.equivalence_in_bicategory_axioms D.equivalence_map_def
              D.equivalence_pair_symmetric D.equivalence_pair_def
        by blast
      have e_trg: "D.equivalence_map (e (trg\<^sub>D \<mu>))"
        using e_trg.equivalence_in_bicategory_axioms D.equivalence_map_def by blast
      show "\<mu> = \<mu>'"
      proof -
        have "F (G \<mu>) = F (G \<mu>')"
          using eq by simp
        hence 1: "D.inv (\<phi> (D.cod \<mu>)) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<phi> (D.dom \<mu>) =
                  D.inv (\<phi> (D.cod \<mu>)) \<cdot>\<^sub>D (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<phi> (D.dom \<mu>)"
          using par FG_eq [of \<mu>] FG_eq [of \<mu>']
          by (metis D.src_cod D.trg_cod)
        have 2: "(e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<phi> (D.dom \<mu>) =
                 (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<phi> (D.dom \<mu>)"
        proof -
          have "D.iso (D.inv (\<phi> (D.cod \<mu>)))"
            using par \<phi>_props D.iso_inv_iso by simp
          moreover have "D.seq (D.inv (\<phi> (D.cod \<mu>)))
                               ((e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<phi> (D.dom \<mu>))"
          proof -
            have "D.arr (F (G \<mu>))"
              using par by simp
            thus ?thesis
              using 1 par FG_eq by simp
          qed
          ultimately show ?thesis
            using 1 par \<phi>_props D.comp_arr_dom D.comp_arr_inv' D.comp_assoc D.comp_cod_arr
                  D.ide_char D.iso_is_section D.section_is_mono D.iso_inv_iso
                  D.monoE
                    [of "D.inv (\<phi> (D.cod \<mu>))" "(e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<phi> (D.dom \<mu>)"
                         "(e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>)) \<cdot>\<^sub>D \<phi> (D.dom \<mu>)"]
            by metis
        qed
        have "e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>) = e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>)"
        proof -
          have "D.seq (e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)) (\<phi> (D.dom \<mu>))"
            using par by fastforce
          thus ?thesis
            using 2 par \<phi>_props D.iso_is_retraction D.retraction_is_epi D.ide_dom
                  D.epiE [of "\<phi> (D.dom \<mu>)" "e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)"
                             "e (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>)"]
            by metis
        qed
        hence "\<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>) = \<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>)"
          using \<mu> \<mu>' e_trg par
                D.equivalence_cancel_left [of "e (trg\<^sub>D \<mu>)" "\<mu> \<star>\<^sub>D d (src\<^sub>D \<mu>)" "\<mu>' \<star>\<^sub>D d (src\<^sub>D \<mu>)"]
          by (metis D.hcomp_simps(3-4) D.hseqE XLT.preserves_arr)
        thus ?thesis
          using \<mu> \<mu>' D.equivalence_cancel_right d_src
          by (metis D.obj_src d_simps(3) par)
      qed
    qed

    interpretation G: equivalence_pseudofunctor
                        V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>
    proof
      show "\<And>a. C.obj a \<Longrightarrow> \<exists>a'. D.obj a' \<and> C.equivalent_objects (G.map\<^sub>0 a') a"
      proof
        fix a
        assume a: "C.obj a"
        have "D.obj (F.map\<^sub>0 a)"
          using a by simp
        moreover have "C.equivalent_objects (G.map\<^sub>0 (F.map\<^sub>0 a)) a"
          using a C.equivalent_objects_symmetric
                F.reflects_equivalent_objects G\<^sub>0_preserves_obj(2) G.map\<^sub>0_simps(1)
          by auto
        ultimately show "D.obj (F.map\<^sub>0 a) \<and> C.equivalent_objects (G.map\<^sub>0 (F.map\<^sub>0 a)) a"
          by blast
      qed
      show "\<And>a b g. \<lbrakk> D.obj a; D.obj b; \<guillemotleft>g : G.map\<^sub>0 a \<rightarrow>\<^sub>C G.map\<^sub>0 b\<guillemotright>; C.ide g \<rbrakk>
                         \<Longrightarrow> \<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>D b\<guillemotright> \<and> D.ide f \<and> C.isomorphic (G f) g"
      proof -
        fix a b g
        assume a: "D.obj a"
        assume b: "D.obj b"
        assume g_in_hhom: "\<guillemotleft>g : G.map\<^sub>0 a \<rightarrow>\<^sub>C G.map\<^sub>0 b\<guillemotright>"
        assume ide_g: "C.ide g"
        interpret e\<^sub>a: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
          using a equivalence_ed\<eta>\<epsilon> by auto
        interpret e\<^sub>b: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         \<open>e b\<close> \<open>d b\<close> \<open>\<eta> b\<close> \<open>\<epsilon> b\<close>
          using b equivalence_ed\<eta>\<epsilon> by auto
        interpret e\<^sub>ae\<^sub>b: two_equivalences_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close> \<open>e b\<close> \<open>d b\<close> \<open>\<eta> b\<close> \<open>\<epsilon> b\<close>
          ..
        have Fg: "\<guillemotleft>F g : F.map\<^sub>0 (G.map\<^sub>0 a) \<rightarrow>\<^sub>D F.map\<^sub>0 (G.map\<^sub>0 b)\<guillemotright>"
          using a b g_in_hhom by auto
        let ?f = "d b \<star>\<^sub>D F g \<star>\<^sub>D e a"
        have f: "\<guillemotleft>?f: a \<rightarrow>\<^sub>D b\<guillemotright>"
          using a b g_in_hhom ide_g by auto
        have 2: "D.isomorphic (F (G ?f)) (F g)"
        proof -
          have "D.isomorphic (F (G ?f)) (e b \<star>\<^sub>D ?f \<star>\<^sub>D d a)"
            using a b ide_g g_in_hhom f FG\<^sub>1_iso
            by (metis D.hseqE D.ide_hcomp D.in_hhomE F.preserves_ide G_ide
                e\<^sub>a.ide_left e\<^sub>b.ide_right)
          also have "D.isomorphic ... (F g)"
            using ide_g e\<^sub>ae\<^sub>b.\<psi>_in_hom e\<^sub>ae\<^sub>b.\<psi>_components_are_iso
                  D.isomorphic_symmetric D.isomorphic_def
            by (metis D.hseqE D.ide_char D.ide_in_hom(1) D.in_hhomE D.hcomp_simps(2)
                F.preserves_ide e\<^sub>b.antipar(2) f)
          finally show ?thesis by simp
        qed
        obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : F (G ?f) \<Rightarrow>\<^sub>D F g\<guillemotright> \<and> D.iso \<phi>"
          using 2 by auto
        have "C.isomorphic (G ?f) g"
          using f ide_g \<phi> F.reflects_iso F.locally_full
          by (metis C.arrI C.isomorphic_def D.ide_hcomp D.hseqE
              F.preserves_ide d_simps(1) e_simps(1) g_in_hhom horizontal_homs.in_hhomE
              G.preserves_ide G.preserves_src G.preserves_trg G.weak_arrow_of_homs_axioms
              weak_arrow_of_homs_def)
        thus "\<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>D b\<guillemotright> \<and> D.ide f \<and> C.isomorphic (G f) g"
          using f
          by (meson D.ide_hcomp D.hseqE D.in_hhomE F.preserves_ide d_simps(1) e_simps(1)
              ide_g)
      qed
      show "\<And>f' g' \<mu>. \<lbrakk> D.ide f'; D.ide g'; src\<^sub>D f' = src\<^sub>D g'; trg\<^sub>D f' = trg\<^sub>D g';
                         \<guillemotleft>\<mu> : G f' \<Rightarrow>\<^sub>C G g'\<guillemotright> \<rbrakk> \<Longrightarrow> \<exists>\<mu>'. \<guillemotleft>\<mu>' : f' \<Rightarrow>\<^sub>D g'\<guillemotright> \<and> G \<mu>' = \<mu>"
      proof -
        fix f' g' \<mu>
        assume f': "D.ide f'"
        assume g': "D.ide g'"
        assume \<mu>: "\<guillemotleft>\<mu> : G f' \<Rightarrow>\<^sub>C G g'\<guillemotright>"
        assume src_eq: "src\<^sub>D f' = src\<^sub>D g'"
        assume trg_eq: "trg\<^sub>D f' = trg\<^sub>D g'"
        let ?a' = "src\<^sub>D f'"
        let ?b' = "trg\<^sub>D f'"
        text \<open>
          Given \<open>\<guillemotleft>\<mu> : G f' \<Rightarrow>\<^sub>C G g'\<guillemotright>\<close>, the 2-cell \<open>F \<mu>\<close> is in \<open>hom\<^sub>D (F (G f')) (F (G g'))\<close>.
          We have equivalence maps \<open>\<guillemotleft>e\<^sub>a : a' \<rightarrow>\<^sub>D F\<^sub>0 (G\<^sub>0 a')\<guillemotright>\<close>
          and \<open>\<guillemotleft>e\<^sub>b :  b' \<rightarrow>\<^sub>D F\<^sub>0 (G\<^sub>0 b')\<guillemotright>\<close> and \<open>d\<^sub>a\<close> and \<open>d\<^sub>b\<close> in the opposite directions.
          We have shown that the functor from \<open>hom\<^sub>D f' g'\<close> to \<open>hom\<^sub>D (F (G f')) (F (G g'))\<close>
          that takes \<open>\<mu>'\<close> to \<open>e b' \<star>\<^sub>D \<mu>' \<star>\<^sub>D d a'\<close> is an equivalence functor, as is also
          the functor from \<open>hom\<^sub>D (F (G f')) (F (G g'))\<close> to \<open>hom f' g'\<close> that takes
          \<open>\<nu>'\<close> to \<open>d b' \<star>\<^sub>D \<nu>' \<star>\<^sub>D e a'\<close>.

          Now, \<open>G\<close> is defined on a 2-cell \<open>\<guillemotleft>\<mu>' : f' \<Rightarrow> g'\<guillemotright>\<close> by the condition:
          \[
              \<open>\<guillemotleft>G \<mu>' : G f' \<Rightarrow>\<^sub>C G g'\<guillemotright> \<and>  F (G \<mu>') = D.inv (\<phi> g') \<cdot>\<^sub>D (e b' \<star>\<^sub>D \<mu>' \<star>\<^sub>D d a') \<cdot>\<^sub>D \<phi> f'\<close>.
          \]
          To show that \<open>G\<close> is locally full, what we need is, given \<open>\<guillemotleft>\<mu> : G f' \<Rightarrow>\<^sub>C G g'\<guillemotright>\<close>,
          to obtain a 2-cell \<open>\<mu>'\<close> in \<open>hom\<^sub>D f' g'\<close> that satisfies: \<open>F (G \<mu>') = F \<mu>\<close>;
          that is:  \<open>D.inv (\<phi> g') \<cdot>\<^sub>D (e b' \<star>\<^sub>D \<mu>' \<star>\<^sub>D d a') \<cdot>\<^sub>D \<phi> f' = F \<mu>\<close>.
          This then implies \<open>G \<mu>' = \<mu>\<close> by the faithfulness of F.
        \<close>
        interpret e\<^sub>a: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         \<open>e ?a'\<close> \<open>d ?a'\<close> \<open>\<eta> ?a'\<close> \<open>\<epsilon> ?a'\<close>
          using f' equivalence_ed\<eta>\<epsilon> by auto
        interpret d\<^sub>a: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          \<open>d ?a'\<close> \<open>e ?a'\<close> \<open>D.inv (\<epsilon> ?a')\<close> \<open>D.inv (\<eta> ?a')\<close>
          using e\<^sub>a.dual_equivalence by simp
        interpret e\<^sub>b: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         \<open>e ?b'\<close> \<open>d ?b'\<close> \<open>\<eta> ?b'\<close> \<open>\<epsilon> ?b'\<close>
          using f' equivalence_ed\<eta>\<epsilon> by auto
        interpret d\<^sub>b: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          \<open>d ?b'\<close> \<open>e ?b'\<close> \<open>D.inv (\<epsilon> ?b')\<close> \<open>D.inv (\<eta> ?b')\<close>
          using e\<^sub>b.dual_equivalence by simp
        interpret d\<^sub>ad\<^sub>b: two_equivalences_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         \<open>d ?a'\<close> \<open>e ?a'\<close> \<open>D.inv (\<epsilon> ?a')\<close> \<open>D.inv (\<eta> ?a')\<close>
                         \<open>d ?b'\<close> \<open>e ?b'\<close> \<open>D.inv (\<epsilon> ?b')\<close> \<open>D.inv (\<eta> ?b')\<close>
          ..
        interpret hom_a_b: subcategory V\<^sub>D \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : ?a' \<rightarrow>\<^sub>D ?b'\<guillemotright>\<close>
          using D.hhom_is_subcategory by simp
        interpret hom_FGa_FGb: subcategory V\<^sub>D
                                 \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : F.map\<^sub>0 (G\<^sub>0 ?a') \<rightarrow>\<^sub>D F.map\<^sub>0 (G\<^sub>0 ?b')\<guillemotright>\<close>
          using D.hhom_is_subcategory by simp
        interpret d: equivalence_of_categories hom_a_b.comp hom_FGa_FGb.comp
                       d\<^sub>ad\<^sub>b.F d\<^sub>ad\<^sub>b.G d\<^sub>ad\<^sub>b.\<phi> d\<^sub>ad\<^sub>b.\<psi>
          using f' d\<^sub>ad\<^sub>b.induces_equivalence_of_hom_categories by simp

        have F\<mu>_in_hom: "\<guillemotleft>F \<mu> : F (G f') \<Rightarrow>\<^sub>D F (G g')\<guillemotright>"
          using \<mu> by auto
        have F\<mu>_in_hhom: "D.in_hhom (F \<mu>) (F.map\<^sub>0 (G\<^sub>0 (src\<^sub>D f'))) (F.map\<^sub>0 (G\<^sub>0 (trg\<^sub>D f')))"
          using f' F\<mu>_in_hom D.src_dom [of "F \<mu>"] D.trg_dom [of "F \<mu>"] by fastforce
        have "hom_FGa_FGb.in_hom (F \<mu>) (F (G f')) (F (G g'))"
          using F\<mu>_in_hom F\<mu>_in_hhom hom_FGa_FGb.in_hom_char hom_FGa_FGb.arr_char
                hom_FGa_FGb.cod_closed hom_FGa_FGb.dom_closed
          by (metis D.in_homE)
        have \<phi>g': "\<guillemotleft>\<phi> g' : F (G g') \<Rightarrow>\<^sub>D e (trg\<^sub>D g') \<star>\<^sub>D g' \<star>\<^sub>D d (src\<^sub>D g')\<guillemotright>"
          using g' \<phi>_props [of g'] by blast
        have inv_\<phi>f': "\<guillemotleft>D.inv (\<phi> f') : e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f') \<Rightarrow>\<^sub>D F (G f')\<guillemotright>"
          using f' \<phi>_props [of f'] by auto

        have 1: "\<guillemotleft>\<phi> g' \<cdot>\<^sub>D F \<mu> \<cdot>\<^sub>D D.inv (\<phi> f') :
                e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f') \<Rightarrow>\<^sub>D e (trg\<^sub>D g') \<star>\<^sub>D g' \<star>\<^sub>D d (src\<^sub>D g')\<guillemotright>"
          using F\<mu>_in_hom \<phi>g' inv_\<phi>f' G_ide f' g' by auto
        have 2: "hom_FGa_FGb.in_hom (\<phi> g' \<cdot>\<^sub>D F \<mu> \<cdot>\<^sub>D D.inv (\<phi> f'))
                                    (e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f'))
                                    (e (trg\<^sub>D g') \<star>\<^sub>D g' \<star>\<^sub>D d (src\<^sub>D g'))"
        proof -
          have "hom_FGa_FGb.arr (\<phi> g' \<cdot>\<^sub>D F \<mu> \<cdot>\<^sub>D D.inv (\<phi> f'))"
            using 1 D.vseq_implies_hpar hom_FGa_FGb.arr_char
            by (simp add: D.arrI g' src_eq trg_eq)
          thus ?thesis
            using 1 hom_FGa_FGb.dom_char hom_FGa_FGb.cod_char
            by (metis D.in_homE hom_FGa_FGb.in_homI)
        qed
        obtain \<mu>' where \<mu>': "hom_a_b.in_hom \<mu>' f' g' \<and> d\<^sub>ad\<^sub>b.G \<mu>' = \<phi> g' \<cdot>\<^sub>D F \<mu> \<cdot>\<^sub>D D.inv (\<phi> f')"
          using 1 2 f' g' src_eq trg_eq d.is_full [of g' f' "\<phi> g' \<cdot>\<^sub>D F \<mu> \<cdot>\<^sub>D D.inv (\<phi> f')"]
                hom_a_b.ide_char hom_a_b.arr_char
          by auto
        have 3: "\<guillemotleft>\<mu>' : f' \<Rightarrow>\<^sub>D g'\<guillemotright> \<and> F (G \<mu>') = F \<mu>"
        proof -
          have 4: "\<guillemotleft>\<mu>' : f' \<Rightarrow>\<^sub>D g'\<guillemotright> \<and>
                   e (trg\<^sub>D f') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D f') = \<phi> g' \<cdot>\<^sub>D F \<mu> \<cdot>\<^sub>D D.inv (\<phi> f')"
            using \<mu>' f' g' hom_a_b.arr_char hom_a_b.in_hom_char by auto
          have "\<guillemotleft>\<mu>' : f' \<Rightarrow>\<^sub>D g'\<guillemotright> \<and>
                  D.inv (\<phi> g') \<cdot>\<^sub>D (e (trg\<^sub>D f') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D f')) = F \<mu> \<cdot>\<^sub>D D.inv (\<phi> f')"
          proof -
            have "D.hseq (e (trg\<^sub>D f')) (\<mu>' \<star>\<^sub>D d (src\<^sub>D f'))"
              using f' g' \<mu>'
              apply (intro D.hseqI, auto)
              by force
            thus ?thesis
              using 4 g' \<phi>_props(2) D.invert_side_of_triangle(1) by metis
          qed
          moreover have "D.seq (D.inv (\<phi> g')) (e (trg\<^sub>D f') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D f'))"
          proof
            show "D.in_hom (e (trg\<^sub>D f') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D f'))
                           (e (trg\<^sub>D f') \<star>\<^sub>D f' \<star>\<^sub>D d (src\<^sub>D f'))
                           (e (trg\<^sub>D f') \<star>\<^sub>D g' \<star>\<^sub>D d (src\<^sub>D f'))"
              using 4 f' g' \<mu>' d_simps e_simps
              by (intro D.hcomp_in_vhom) auto
            show "D.in_hom (D.inv (\<phi> g')) (e (trg\<^sub>D f') \<star>\<^sub>D g' \<star>\<^sub>D d (src\<^sub>D f')) (F (G\<^sub>1 g'))"
                using 4 g' \<mu>' \<phi>_props [of g'] D.vconn_implies_hpar by simp
          qed
          ultimately have "\<guillemotleft>\<mu>' : f' \<Rightarrow>\<^sub>D g'\<guillemotright> \<and>
                           D.inv (\<phi> g') \<cdot>\<^sub>D (e (trg\<^sub>D f') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D f')) \<cdot>\<^sub>D \<phi> f' = F \<mu>"
            using f' \<phi>_props(2) D.iso_inv_iso D.inv_inv D.invert_side_of_triangle(2)
                  D.comp_assoc
            by metis
          moreover have "D.inv (\<phi> g') \<cdot>\<^sub>D (e (trg\<^sub>D f') \<star>\<^sub>D \<mu>' \<star>\<^sub>D d (src\<^sub>D f')) \<cdot>\<^sub>D \<phi> f' = F (G \<mu>')"
            using 4 FG_eq by auto
          ultimately show ?thesis by simp
        qed
        hence "G \<mu>' = \<mu>"
          using \<mu> \<mu>' F.is_faithful [of "G \<mu>'" \<mu>] by force
        thus "\<exists>\<mu>'. \<guillemotleft>\<mu>' : f' \<Rightarrow>\<^sub>D g'\<guillemotright> \<and> G \<mu>' = \<mu>"
          using 3 by auto
      qed
    qed

    proposition is_equivalence_pseudofunctor:
    shows "equivalence_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>"
      ..

  end

  sublocale converse_equivalence_pseudofunctor \<subseteq>
            equivalence_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>
    using is_equivalence_pseudofunctor by simp

  definition equivalent_bicategories
  where "equivalent_bicategories V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C \<equiv>
         \<exists>F \<Phi>. equivalence_pseudofunctor
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>"

  lemma equivalent_bicategories_reflexive:
  assumes "bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
  shows "equivalent_bicategories V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
  proof -
    interpret bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
      using assms by simp
    interpret I: identity_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C ..
    show ?thesis
      using I.equivalence_pseudofunctor_axioms equivalent_bicategories_def by blast
  qed

  lemma equivalent_bicategories_symmetric:
  assumes "equivalent_bicategories V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
  shows "equivalent_bicategories V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
  proof -
    obtain F \<Phi>\<^sub>F where F: "equivalence_pseudofunctor
                            V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F"
      using assms equivalent_bicategories_def by blast
    interpret F: equivalence_pseudofunctor
                   V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F
      using F by simp
    interpret G: converse_equivalence_pseudofunctor
                   V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F
      ..
    show ?thesis
      using G.is_equivalence_pseudofunctor equivalent_bicategories_def by blast
  qed

  lemma equivalent_bicategories_transitive [trans]:
  assumes "equivalent_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
  and "equivalent_bicategories V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
  shows "equivalent_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
  proof -
    obtain F \<Phi>\<^sub>F where F: "equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F"
      using assms(1) equivalent_bicategories_def by blast
    obtain G \<Phi>\<^sub>G where G: "equivalence_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G"
      using assms(2) equivalent_bicategories_def by blast
    interpret F: equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F
      using F by simp
    interpret G: equivalence_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G
      using G by simp
    interpret GoF: composite_equivalence_pseudofunctor
                     V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G ..
    show "equivalent_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
      using equivalent_bicategories_def GoF.equivalence_pseudofunctor_axioms by blast
  qed

end
