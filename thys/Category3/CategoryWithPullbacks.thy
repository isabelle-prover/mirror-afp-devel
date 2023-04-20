(*  Title:       CategoryWithPullbacks
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Category with Pullbacks"

theory CategoryWithPullbacks
imports Limit
begin

text \<open>
  \sloppypar
  In this chapter, we give a traditional definition of pullbacks in a category as
  limits of cospan diagrams and we define a locale \<open>category_with_pullbacks\<close> that
  is satisfied by categories in which every cospan diagram has a limit.
  These definitions build on the general definition of limit that we gave in
  @{theory Category3.Limit}.  We then define a locale \<open>elementary_category_with_pullbacks\<close>
  that axiomatizes categories equipped with chosen functions that assign to each cospan
  a corresponding span of ``projections'', which enjoy the familiar universal property
  of a pullback.  After developing consequences of the axioms, we prove that the two
  locales are in agreement, in the sense that every interpretation of
  \<open>category_with_pullbacks\<close> extends to an interpretation of
  \<open>elementary_category_with_pullbacks\<close>, and conversely, the underlying category of
  an interpretation of \<open>elementary_category_with_pullbacks\<close> always yields an interpretation
  of \<open>category_with_pullbacks\<close>.
\<close>

  section "Commutative Squares"

  context category
  begin

    text \<open>
      The following provides some useful technology for working with commutative squares.
    \<close>

    definition commutative_square
    where "commutative_square f g h k \<equiv> cospan f g \<and> span h k \<and> dom f = cod h \<and> f \<cdot> h = g \<cdot> k"

    lemma commutative_squareI [intro, simp]:
    assumes "cospan f g" and "span h k" and "dom f = cod h" and "f \<cdot> h = g \<cdot> k"
    shows "commutative_square f g h k"
      using assms commutative_square_def by auto

    lemma commutative_squareE [elim]:
    assumes "commutative_square f g h k"
    and "\<lbrakk> arr f; arr g; arr h; arr k; cod f = cod g; dom h = dom k; dom f = cod h;
           dom g = cod k; f \<cdot> h = g \<cdot> k \<rbrakk> \<Longrightarrow> T"
    shows T
      using assms commutative_square_def
      by (metis (mono_tags, lifting) seqE seqI)

    lemma commutative_square_comp_arr:
    assumes "commutative_square f g h k" and "seq h l"
    shows "commutative_square f g (h \<cdot> l) (k \<cdot> l)"
      using assms
      apply (elim commutative_squareE, intro commutative_squareI, auto)
      using comp_assoc by metis

    lemma arr_comp_commutative_square:
    assumes "commutative_square f g h k" and "seq l f"
    shows "commutative_square (l \<cdot> f) (l \<cdot> g) h k"
      using assms comp_assoc
      by (elim commutative_squareE, intro commutative_squareI, auto)

  end

  section "Cospan Diagrams"

  (* TODO: Rework the ugly development of equalizers into this form. *)

  text \<open>
    The ``shape'' of a cospan diagram is a category having two non-identity arrows
    with distinct domains and a common codomain.
  \<close>

  locale cospan_shape
  begin

    datatype Arr = Null | AA | BB | TT | AT | BT

    fun comp
    where "comp AA AA = AA"
        | "comp AT AA = AT"
        | "comp TT AT = AT"
        | "comp BB BB = BB"
        | "comp BT BB = BT"
        | "comp TT BT = BT"
        | "comp TT TT = TT"
        | "comp _ _ = Null"

    interpretation partial_composition comp
    proof
      show "\<exists>!n. \<forall>f. comp n f = n \<and> comp f n = n"
      proof
        show "\<forall>f. comp Null f = Null \<and> comp f Null = Null" by simp
        show "\<And>n. \<forall>f. comp n f = n \<and> comp f n = n \<Longrightarrow> n = Null"
          by (metis comp.simps(8))
      qed
    qed

    lemma null_char:
    shows "null = Null"
    proof -
      have "\<forall>f. comp Null f = Null \<and> comp f Null = Null" by simp
      thus ?thesis
        using null_def ex_un_null theI [of "\<lambda>n. \<forall>f. comp n f = n \<and> comp f n = n"]
        by (metis partial_magma.null_is_zero(2) partial_magma_axioms)
    qed

    lemma ide_char:
    shows "ide f \<longleftrightarrow> f = AA \<or> f = BB \<or> f = TT"
    proof
      show "ide f \<Longrightarrow> f = AA \<or> f = BB \<or> f = TT"
        using ide_def null_char by (cases f, simp_all)
      show "f = AA \<or> f = BB \<or> f = TT \<Longrightarrow> ide f"
      proof -
        have 1: "\<And>f g. f = AA \<or> f = BB \<or> f = TT \<Longrightarrow>
                       comp f f \<noteq> Null \<and>
                       (comp g f \<noteq> Null \<longrightarrow> comp g f = g) \<and>
                       (comp f g \<noteq> Null \<longrightarrow> comp f g = g)"
        proof -
          fix f g
          show "f = AA \<or> f = BB \<or> f = TT \<Longrightarrow>
                  comp f f \<noteq> Null \<and>
                  (comp g f \<noteq> Null \<longrightarrow> comp g f = g) \<and>
                  (comp f g \<noteq> Null \<longrightarrow> comp f g = g)"
            by (cases f; cases g, auto)
        qed
        assume f: "f = AA \<or> f = BB \<or> f = TT"
        show "ide f"
          using f 1 ide_def null_char by simp
      qed
    qed

    fun Dom
    where "Dom AA = AA"
        | "Dom BB = BB"
        | "Dom TT = TT"
        | "Dom AT = AA"
        | "Dom BT = BB"
        | "Dom _ = Null"

    fun Cod
    where "Cod AA = AA"
        | "Cod BB = BB"
        | "Cod TT = TT"
        | "Cod AT = TT"
        | "Cod BT = TT"
        | "Cod _ = Null"

    lemma domains_char':
    shows "domains f = (if f = Null then {} else {Dom f})"
      using domains_def ide_char null_char
      by (cases f, auto)

    lemma codomains_char':
    shows "codomains f = (if f = Null then {} else {Cod f})"
      using codomains_def ide_char null_char
      by (cases f, auto)

    lemma arr_char:
    shows "arr f \<longleftrightarrow> f \<noteq> Null"
      using arr_def domains_char' codomains_char' by simp

    lemma seq_char:
    shows "seq g f \<longleftrightarrow> (f = AA \<and> (g = AA \<or> g = AT)) \<or>
                       (f = BB \<and> (g = BB \<or> g = BT)) \<or>
                       (f = AT \<and> g = TT) \<or>
                       (f = BT \<and> g = TT) \<or>
                       (f = TT \<and> g = TT)"
      using arr_char null_char
      by (cases f; cases g, simp_all)

    interpretation category comp
    proof
      fix f g h
      show "comp g f \<noteq> null \<Longrightarrow> seq g f"
        using null_char arr_char seq_char by simp
      show "domains f \<noteq> {} \<longleftrightarrow> codomains f \<noteq> {}"
        using domains_char' codomains_char' by auto
      show "seq h g \<Longrightarrow> seq (comp h g) f \<Longrightarrow> seq g f"
        using seq_char arr_char
        by (cases g; cases h; simp_all)
      show "seq h (comp g f) \<Longrightarrow> seq g f \<Longrightarrow> seq h g"
        using seq_char arr_char
        by (cases f; cases g; simp_all)
      show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> seq (comp h g) f"
        using seq_char arr_char
        by (cases f; simp_all; cases g; simp_all; cases h; auto)
      show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> comp (comp h g) f = comp h (comp g f)"
       using seq_char
       by (cases f; simp_all; cases g; simp_all; cases h; auto)
    qed

    lemma is_category:
    shows "category comp"
      ..

    lemma dom_char:
    shows "dom = Dom"
      using dom_def domains_char domains_char' null_char by fastforce

    lemma cod_char:
    shows "cod = Cod"
      using cod_def codomains_char codomains_char' null_char by fastforce

  end

  sublocale cospan_shape \<subseteq> category comp
    using is_category by auto

  locale cospan_diagram =
    J: cospan_shape +
    C: category C
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and f0 :: 'c
  and f1 :: 'c +
  assumes is_cospan: "C.cospan f0 f1"
  begin

    no_notation J.comp   (infixr "\<cdot>" 55)
    notation J.comp      (infixr "\<cdot>\<^sub>J" 55)

    fun map
    where "map J.AA = C.dom f0"
        | "map J.BB = C.dom f1"
        | "map J.TT = C.cod f0"
        | "map J.AT = f0"
        | "map J.BT = f1"
        | "map _ = C.null"

  end

  sublocale cospan_diagram \<subseteq> diagram J.comp C map
  proof
    show "\<And>f. \<not> J.arr f \<Longrightarrow> map f = C.null"
      using J.arr_char by simp
    fix f
    assume f: "J.arr f"
    show "C.arr (map f)"
      using f J.arr_char is_cospan by (cases f, simp_all)
    show "C.dom (map f) = map (J.dom f)"
      using f J.arr_char J.dom_char is_cospan by (cases f, simp_all)
    show "C.cod (map f) = map (J.cod f)"
      using f J.arr_char J.cod_char is_cospan by (cases f, simp_all)
    next
    fix f g
    assume fg: "J.seq g f"
    show "map (g \<cdot>\<^sub>J f) = map g \<cdot> map f"
      using fg J.seq_char J.null_char J.not_arr_null is_cospan
      apply (cases f; cases g, simp_all)
      using C.comp_arr_dom C.comp_cod_arr by auto
  qed

  section "Category with Pullbacks"

  text \<open>
    A \emph{pullback} in a category @{term C} is a limit of a cospan diagram in @{term C}.
  \<close>

  context cospan_diagram
  begin

    definition mkCone
    where "mkCone p0 p1 \<equiv> \<lambda>j. if j = J.AA then p0
                               else if j = J.BB then p1
                               else if j = J.AT then f0 \<cdot> p0
                               else if j = J.BT then f1 \<cdot> p1
                               else if j = J.TT then f0 \<cdot> p0
                               else C.null"

    abbreviation is_rendered_commutative_by
    where "is_rendered_commutative_by p0 p1 \<equiv> C.seq f0 p0 \<and> f0 \<cdot> p0 = f1 \<cdot> p1"

    abbreviation has_as_pullback
    where "has_as_pullback p0 p1 \<equiv> limit_cone (C.dom p0) (mkCone p0 p1)"

    lemma cone_mkCone:
    assumes "is_rendered_commutative_by p0 p1"
    shows "cone (C.dom p0) (mkCone p0 p1)"
    proof -
      interpret E: constant_functor J.comp C \<open>C.dom p0\<close>
        apply unfold_locales using assms by auto
      show "cone (C.dom p0) (mkCone p0 p1)"
      proof
        fix f
        show "\<not> J.arr f \<Longrightarrow> mkCone p0 p1 f = C.null"
          using mkCone_def J.arr_char by simp
        assume f: "J.arr f"
        show "C.dom (mkCone p0 p1 f) = E.map (J.dom f)"
          using assms f mkCone_def J.arr_char J.dom_char
          apply (cases f, simp_all)
          by (metis C.dom_comp)+
        show "C.cod (mkCone p0 p1 f) = map (J.cod f)"
          using assms f mkCone_def J.arr_char J.cod_char is_cospan
          by (cases f, auto)
        show "map f \<cdot> mkCone p0 p1 (J.dom f) = mkCone p0 p1 f"
          using assms f mkCone_def J.arr_char J.dom_char C.comp_ide_arr is_cospan
          by (cases f, auto)
        show "mkCone p0 p1 (J.cod f) \<cdot> E.map f = mkCone p0 p1 f"
          using assms f mkCone_def J.arr_char J.cod_char C.comp_arr_dom
          apply (cases f, auto)
             apply (metis C.dom_comp C.seqE)
          by (metis C.dom_comp)+
      qed
    qed

    lemma is_rendered_commutative_by_cone:
    assumes "cone a \<chi>"
    shows "is_rendered_commutative_by (\<chi> J.AA) (\<chi> J.BB)"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      show ?thesis
      proof
        show "C.seq f0 (\<chi> J.AA)"
          by (metis C.seqI J.cod_char J.seq_char \<chi>.preserves_cod \<chi>.preserves_reflects_arr
              J.seqE is_cospan J.Cod.simps(1) map.simps(1))
        show "f0 \<cdot> \<chi> J.AA = f1 \<cdot> \<chi> J.BB"
          by (metis J.cod_char J.dom_char \<chi>.A.map_simp \<chi>.naturality
              J.Cod.simps(4-5) J.Dom.simps(4-5) J.comp.simps(2,5) J.seq_char map.simps(4-5))
      qed
    qed

    lemma mkCone_cone:
    assumes "cone a \<chi>"
    shows "mkCone (\<chi> J.AA) (\<chi> J.BB) = \<chi>"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      have 1: "is_rendered_commutative_by (\<chi> J.AA) (\<chi> J.BB)"
        using assms is_rendered_commutative_by_cone by blast
      interpret mkCone_\<chi>: cone J.comp C map \<open>C.dom (\<chi> J.AA)\<close> \<open>mkCone (\<chi> J.AA) (\<chi> J.BB)\<close>
        using assms cone_mkCone 1 by auto
      show ?thesis
      proof -
        have "\<And>j. j = J.AA \<Longrightarrow> mkCone (\<chi> J.AA) (\<chi> J.BB) j = \<chi> j"
          using mkCone_def \<chi>.is_extensional by simp
        moreover have "\<And>j. j = J.BB \<Longrightarrow> mkCone (\<chi> J.AA) (\<chi> J.BB) j = \<chi> j"
          using mkCone_def \<chi>.is_extensional by simp
        moreover have "\<And>j. j = J.TT \<Longrightarrow> mkCone (\<chi> J.AA) (\<chi> J.BB) j = \<chi> j"
          using 1 mkCone_def \<chi>.is_extensional \<chi>.A.map_simp \<chi>.preserves_comp_1
                cospan_shape.seq_char \<chi>.is_natural_2
          apply simp
          by (metis J.seqE J.comp.simps(5) map.simps(5))
        ultimately have "\<And>j. J.ide j \<Longrightarrow> mkCone (\<chi> J.AA) (\<chi> J.BB) j = \<chi> j"
          using J.ide_char by auto
        thus "mkCone (\<chi> J.AA) (\<chi> J.BB) = \<chi>"
          using mkCone_def NaturalTransformation.eqI [of J.comp C]
                \<chi>.natural_transformation_axioms mkCone_\<chi>.natural_transformation_axioms
                J.ide_char
          by simp
      qed
    qed

    lemma cone_iff_commutative_square:
    shows "cone (C.dom h) (mkCone h k) \<longleftrightarrow> C.commutative_square f0 f1 h k"
      using cone_mkCone mkCone_def J.arr_char J.ide_char is_rendered_commutative_by_cone
            is_cospan C.commutative_square_def cospan_shape.Arr.simps(11)
            C.dom_comp C.seqE C.seqI
      apply (intro iffI)
      by (intro C.commutative_squareI) metis+

    lemma cones_map_mkCone_eq_iff:
    assumes "is_rendered_commutative_by p0 p1" and "is_rendered_commutative_by p0' p1'"
    and "\<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright>"
    shows "cones_map h (mkCone p0 p1) = mkCone p0' p1' \<longleftrightarrow> p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
    proof -
      interpret \<chi>: cone J.comp C map \<open>C.dom p0\<close> \<open>mkCone p0 p1\<close>
        using assms(1) cone_mkCone [of p0 p1] by blast
      interpret \<chi>': cone J.comp C map \<open>C.dom p0'\<close> \<open>mkCone p0' p1'\<close>
        using assms(2) cone_mkCone [of p0' p1'] by blast
      show ?thesis
      proof
        assume 3: "cones_map h (mkCone p0 p1) = mkCone p0' p1'"
        show "p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
        proof
          show "p0 \<cdot> h = p0'"
          proof -
            have "p0' = mkCone p0' p1' J.AA"
              using mkCone_def J.arr_char by simp
            also have "... = cones_map h (mkCone p0 p1) J.AA"
              using 3 by simp
            also have "... = p0 \<cdot> h"
              using assms mkCone_def J.arr_char \<chi>.cone_axioms by auto
            finally show ?thesis by auto
          qed
          show "p1 \<cdot> h = p1'"
          proof -
            have "p1' = mkCone p0' p1' J.BB"
              using mkCone_def J.arr_char by simp
            also have "... = cones_map h (mkCone p0 p1) J.BB"
              using 3 by simp
            also have "... = p1 \<cdot> h"
              using assms mkCone_def J.arr_char \<chi>.cone_axioms by auto
            finally show ?thesis by auto
          qed
        qed
        next
        assume 4: "p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
        show "cones_map h (mkCone p0 p1) = mkCone p0' p1'"
        proof
          fix j
          have "\<not> J.arr j \<Longrightarrow> cones_map h (mkCone p0 p1) j = mkCone p0' p1' j"
            using assms \<chi>.cone_axioms mkCone_def J.arr_char by auto
          moreover have "J.arr j \<Longrightarrow> cones_map h (mkCone p0 p1) j = mkCone p0' p1' j"
            using assms 4 \<chi>.cone_axioms mkCone_def J.arr_char C.comp_assoc
            by fastforce
          ultimately show "cones_map h (mkCone p0 p1) j = mkCone p0' p1' j"
            using J.arr_char J.Dom.cases by blast
        qed
      qed
    qed

  end

  locale pullback_cone =
    J: cospan_shape +
    C: category C +
    D: cospan_diagram C f0 f1 +
    limit_cone J.comp C D.map \<open>C.dom p0\<close> \<open>D.mkCone p0 p1\<close>
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and f0 :: 'c
  and f1 :: 'c
  and p0 :: 'c
  and p1 :: 'c
  begin

    (* TODO: Equalizer should be simplifiable in the same way. *)
    lemma renders_commutative:
    shows "D.is_rendered_commutative_by p0 p1"
      using D.mkCone_def D.cospan_diagram_axioms cone_axioms
            cospan_diagram.is_rendered_commutative_by_cone
      by fastforce

    lemma is_universal':
    assumes "D.is_rendered_commutative_by p0' p1'"
    shows "\<exists>!h. \<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright> \<and> p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
    proof -
      have "D.cone (C.dom p0') (D.mkCone p0' p1')"
        using assms D.cone_mkCone by blast
      hence 1: "\<exists>!h. \<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright> \<and>
                     D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1'"
        using is_universal by simp
      have 2: "\<And>h. \<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright> \<Longrightarrow>
                    D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1' \<longleftrightarrow>
                    p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
        using assms D.cones_map_mkCone_eq_iff [of p0 p1 p0' p1'] renders_commutative
        by fastforce
      thus ?thesis using 1 by blast
    qed

    lemma induced_arrowI':
    assumes "D.is_rendered_commutative_by p0' p1'"
    shows "\<guillemotleft>induced_arrow (C.dom p0') (D.mkCone p0' p1') : C.dom p0' \<rightarrow> C.dom p0\<guillemotright>"
    and "p0 \<cdot> induced_arrow (C.dom p0') (D.mkCone p0' p1') = p0'"
    and "p1 \<cdot> induced_arrow (C.dom p1') (D.mkCone p0' p1') = p1'"
    proof -
      interpret A': constant_functor J.comp C \<open>C.dom p0'\<close>
        using assms by (unfold_locales, auto)
      have cone: "D.cone (C.dom p0') (D.mkCone p0' p1')"
        using assms D.cone_mkCone [of p0' p1'] by blast
      show 1: "p0 \<cdot> induced_arrow (C.dom p0') (D.mkCone p0' p1') = p0'"
      proof -
        have "p0 \<cdot> induced_arrow (C.dom p0') (D.mkCone p0' p1') =
                D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) J.AA"
          using cone induced_arrowI(1) D.mkCone_def J.arr_char is_cone by force
        also have "... = p0'"
        proof -
          have "D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) =
                D.mkCone p0' p1'"
            using cone induced_arrowI by blast
          thus ?thesis
            using J.arr_char D.mkCone_def by simp
        qed
        finally show ?thesis by auto
      qed
      show 2: "p1 \<cdot> induced_arrow (C.dom p1') (D.mkCone p0' p1') = p1'"
      proof -
        have "p1 \<cdot> induced_arrow (C.dom p1') (D.mkCone p0' p1') =
              D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                          (D.mkCone p0 p1) J.BB"
        proof -
          have "C.dom p0' = C.dom p1'"
            using assms by (metis C.dom_comp)
          thus ?thesis
            using cone induced_arrowI(1) D.mkCone_def J.arr_char is_cone by force
        qed
        also have "... = p1'"
        proof -
          have "D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) =
                D.mkCone p0' p1'"
            using cone induced_arrowI by blast
          thus ?thesis
            using J.arr_char D.mkCone_def by simp
        qed
        finally show ?thesis by auto
      qed
      show "\<guillemotleft>induced_arrow (C.dom p0') (D.mkCone p0' p1') : C.dom p0' \<rightarrow> C.dom p0\<guillemotright>"
        using 1 cone induced_arrowI by simp
    qed

  end

  context category
  begin

    definition has_as_pullback
    where "has_as_pullback f0 f1 p0 p1 \<equiv>
           cospan f0 f1 \<and> cospan_diagram.has_as_pullback C f0 f1 p0 p1"

    definition has_pullbacks
    where "has_pullbacks = (\<forall>f0 f1. cospan f0 f1 \<longrightarrow> (\<exists>p0 p1. has_as_pullback f0 f1 p0 p1))"

    lemma has_as_pullbackI [intro]:
    assumes "cospan f g" and "commutative_square f g p q"
    and "\<And>h k. commutative_square f g h k \<Longrightarrow> \<exists>!l. p \<cdot> l = h \<and> q \<cdot> l = k"
    shows "has_as_pullback f g p q"
    proof (unfold has_as_pullback_def, intro conjI)
      show "arr f" and "arr g" and "cod f = cod g"
        using assms(1) by auto
      interpret J: cospan_shape .
      interpret D: cospan_diagram C f g
        using assms(1-2) by unfold_locales auto
      show "D.has_as_pullback p q"
      proof -
        have 1: "D.is_rendered_commutative_by p q"
          using assms ide_in_hom by blast
        let ?\<chi> = "D.mkCone p q"
        let ?a = "dom p"
        interpret \<chi>: cone J.comp C D.map ?a ?\<chi>
           using assms(2) D.cone_mkCone 1 by auto
        interpret \<chi>: limit_cone J.comp C D.map ?a ?\<chi>
        proof
          fix x \<chi>'
          assume \<chi>': "D.cone x \<chi>'"
          interpret \<chi>': cone J.comp C D.map x \<chi>'
            using \<chi>' by simp
          have 2: "D.is_rendered_commutative_by (\<chi>' J.AA) (\<chi>' J.BB)"
            using \<chi>' D.is_rendered_commutative_by_cone [of x \<chi>'] by blast
          have 3: "\<exists>!l. p \<cdot> l = \<chi>' J.AA \<and> q \<cdot> l = \<chi>' J.BB"
            using assms(1,3) 2 \<chi>'.preserves_hom J.arr_char J.ide_char by simp
          obtain l where l: "p \<cdot> l = \<chi>' J.AA \<and> q \<cdot> l = \<chi>' J.BB"
            using 3 by blast
          have "\<guillemotleft>l : x \<rightarrow> ?a\<guillemotright>"
            using l 2 \<chi>'.preserves_hom J.arr_char J.ide_char \<chi>'.component_in_hom
                  \<chi>'.is_extensional \<chi>'.preserves_reflects_arr comp_in_homE null_is_zero(2) in_homE
            by metis
          moreover have "D.cones_map l (D.mkCone p q) = \<chi>'"
            using l D.cones_map_mkCone_eq_iff [of p q "\<chi>' J.AA" "\<chi>' J.BB" l]
            by (metis (no_types, lifting) 1 2 D.mkCone_cone \<chi>' calculation dom_comp in_homE seqE)
          ultimately have "\<exists>l. \<guillemotleft>l : x \<rightarrow> ?a\<guillemotright> \<and> D.cones_map l (D.mkCone p q) = \<chi>'"
            by blast
          moreover have "\<And>l'. \<lbrakk>\<guillemotleft>l' : x \<rightarrow> ?a\<guillemotright>; D.cones_map l' (D.mkCone p q) = \<chi>'\<rbrakk> \<Longrightarrow> l' = l"
          proof -
            fix l'
            assume l': "\<guillemotleft>l' : x \<rightarrow> ?a\<guillemotright>"
            assume eq: "D.cones_map l' (D.mkCone p q) = \<chi>'"
            have "p \<cdot> l' = \<chi>' J.AA \<and> q \<cdot> l' = \<chi>' J.BB"
              using l' eq J.arr_char \<chi>.cone_axioms D.mkCone_def by auto
            thus "l' = l"
              using 3 l by blast
          qed
          ultimately show "\<exists>!l. \<guillemotleft>l : x \<rightarrow> ?a\<guillemotright> \<and> D.cones_map l (D.mkCone p q) = \<chi>'"
            by blast
        qed
        show "D.has_as_pullback p q"
          using assms \<chi>.limit_cone_axioms by blast
      qed
    qed

    lemma has_as_pullbackE [elim]:
    assumes "has_as_pullback f g p q"
    and "\<lbrakk>cospan f g; commutative_square f g p q;
          \<And>h k. commutative_square f g h k \<Longrightarrow> \<exists>!l. p \<cdot> l = h \<and> q \<cdot> l = k\<rbrakk> \<Longrightarrow> T"
    shows T
    proof -
      interpret J: cospan_shape .
      interpret D: cospan_diagram C f g
        using assms(1) has_as_pullback_def
        by (meson category_axioms cospan_diagram.intro cospan_diagram_axioms.intro)
      have 1: "\<And>h k. commutative_square f g h k \<longleftrightarrow> D.cone (dom h) (D.mkCone h k)"
        using D.cone_iff_commutative_square by presburger
      let ?\<chi> = "D.mkCone p q"
      interpret \<chi>: limit_cone J.comp C D.map \<open>dom p\<close> ?\<chi>
        using assms(1) has_as_pullback_def D.cone_mkCone by blast
      have "cospan f g"
        using D.is_cospan by blast
      moreover have csq: "commutative_square f g p q"
        using 1 \<chi>.cone_axioms by blast
      moreover have "\<And>h k. commutative_square f g h k \<Longrightarrow> \<exists>!l. p \<cdot> l = h \<and> q \<cdot> l = k"
      proof -
        fix h k
        assume 2: "commutative_square f g h k"
        let ?\<chi>' = "D.mkCone h k"
        interpret \<chi>': cone J.comp C D.map \<open>dom h\<close> ?\<chi>'
          using 1 2 by blast
        have 3: "\<exists>!l. \<guillemotleft>l : dom h \<rightarrow> dom p\<guillemotright> \<and> D.cones_map l ?\<chi> = ?\<chi>'"
          using 1 2 \<chi>.is_universal [of "dom h" "D.mkCone h k"] by blast
        obtain l where l: "\<guillemotleft>l : dom h \<rightarrow> dom p\<guillemotright> \<and> D.cones_map l ?\<chi> = ?\<chi>'"
          using 3 by blast
        have "p \<cdot> l = h \<and> q \<cdot> l = k"
        proof
          have "p \<cdot> l = D.cones_map l ?\<chi> J.AA"
            using \<chi>.cone_axioms D.mkCone_def J.seq_char in_homE
            apply simp
            by (metis J.seqE l)
          also have "... = h"
            using l \<chi>'.cone_axioms D.mkCone_def J.seq_char in_homE by simp
          finally show "p \<cdot> l = h" by blast
          have "q \<cdot> l = D.cones_map l ?\<chi> J.BB"
            using \<chi>.cone_axioms D.mkCone_def J.seq_char in_homE
            apply simp
            by (metis J.seqE l)
          also have "... = k"
            using l \<chi>'.cone_axioms D.mkCone_def J.seq_char in_homE by simp
          finally show "q \<cdot> l = k" by blast
        qed
        moreover have "\<And>l'. p \<cdot> l' = h \<and> q \<cdot> l' = k \<Longrightarrow> l' = l"
        proof -
          fix l'
          assume 1: "p \<cdot> l' = h \<and> q \<cdot> l' = k"
          have 2: "\<guillemotleft>l' : dom h \<rightarrow> dom p\<guillemotright>"
            using 1
            by (metis \<chi>'.ide_apex arr_dom_iff_arr arr_iff_in_hom ideD(1) seqE dom_comp)
          moreover have "D.cones_map l' ?\<chi> = ?\<chi>'"
            using D.cones_map_mkCone_eq_iff
            by (meson 1 2 csq D.cone_iff_commutative_square \<chi>'.cone_axioms
                      commutative_squareE seqI)
          ultimately show "l' = l"
            using l \<chi>.is_universal \<chi>'.cone_axioms by blast
        qed
        ultimately show "\<exists>!l. p \<cdot> l = h \<and> q \<cdot> l = k" by blast
      qed
      ultimately show T
        using assms(2) by blast
    qed

  end

  locale category_with_pullbacks =
    category +
  assumes has_pullbacks: has_pullbacks

  section "Elementary Category with Pullbacks"

  text \<open>
    An \emph{elementary category with pullbacks} is a category equipped with a specific
    way of mapping each cospan to a span such that the resulting square commutes and
    such that the span is universal for that property.  It is useful to assume that the
    functions, mapping a cospan to the two projections of the pullback, are extensional;
    that is, they yield @{term null} when applied to arguments that do not form a cospan.
  \<close>

  locale elementary_category_with_pullbacks =
    category C
  for C :: "'a comp"                              (infixr "\<cdot>" 55)
  and prj0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"                    ("\<p>\<^sub>0[_, _]")
  and prj1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"                    ("\<p>\<^sub>1[_, _]") +
  assumes prj0_ext: "\<not> cospan f g \<Longrightarrow> \<p>\<^sub>0[f, g] = null"
  and prj1_ext: "\<not> cospan f g \<Longrightarrow> \<p>\<^sub>1[f, g] = null"
  and pullback_commutes [intro]: "cospan f g \<Longrightarrow> commutative_square f g \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]"
  and universal: "commutative_square f g h k \<Longrightarrow> \<exists>!l. \<p>\<^sub>1[f, g] \<cdot> l = h \<and> \<p>\<^sub>0[f, g] \<cdot> l = k"
  begin

    lemma pullback_commutes':
    assumes "cospan f g"
    shows "f \<cdot> \<p>\<^sub>1[f, g] = g \<cdot> \<p>\<^sub>0[f, g]"
      using assms commutative_square_def by blast

    lemma prj0_in_hom':
    assumes "cospan f g"
    shows "\<guillemotleft>\<p>\<^sub>0[f, g] : dom \<p>\<^sub>0[f, g] \<rightarrow> dom g\<guillemotright>"
      using assms pullback_commutes
      by (metis category.commutative_squareE category_axioms in_homI)

    lemma prj1_in_hom':
    assumes "cospan f g"
    shows "\<guillemotleft>\<p>\<^sub>1[f, g] : dom \<p>\<^sub>0[f, g] \<rightarrow> dom f\<guillemotright>"
      using assms pullback_commutes
      by (metis category.commutative_squareE category_axioms in_homI)

    text \<open>
      The following gives us a notation for the common domain of the two projections
      of a pullback.
    \<close>

    definition pbdom        (infix "\<down>\<down>" 51)
    where "f \<down>\<down> g \<equiv> dom \<p>\<^sub>0[f, g]"

    lemma pbdom_in_hom [intro]:
    assumes "cospan f g"
    shows "\<guillemotleft>f \<down>\<down> g : f \<down>\<down> g \<rightarrow> f \<down>\<down> g\<guillemotright>"
      unfolding pbdom_def
      using assms prj0_in_hom'
      by (metis arr_dom_iff_arr arr_iff_in_hom cod_dom dom_dom in_homE)

    lemma ide_pbdom [simp]:
    assumes "cospan f g"
    shows "ide (f \<down>\<down> g)"
      using assms ide_in_hom by auto[1]

    lemma prj0_in_hom [intro, simp]:
    assumes "cospan f g" and "a = f \<down>\<down> g" and "b = dom g"
    shows "\<guillemotleft>\<p>\<^sub>0[f, g] : a \<rightarrow> b\<guillemotright>"
      unfolding pbdom_def
      using assms prj0_in_hom' by (simp add: pbdom_def)

    lemma prj1_in_hom [intro, simp]:
    assumes "cospan f g" and "a = f \<down>\<down> g" and "b = dom f"
    shows "\<guillemotleft>\<p>\<^sub>1[f, g] : a \<rightarrow> b\<guillemotright>"
      unfolding pbdom_def
      using assms prj1_in_hom' by (simp add: pbdom_def)

    lemma prj0_simps [simp]:
    assumes "cospan f g"
    shows "arr \<p>\<^sub>0[f, g]" and "dom \<p>\<^sub>0[f, g] = f \<down>\<down> g" and "cod \<p>\<^sub>0[f, g] = dom g"
      using assms prj0_in_hom by (blast, blast, blast)

    lemma prj0_simps_arr [iff]:
    shows "arr \<p>\<^sub>0[f, g] \<longleftrightarrow> cospan f g"
    proof
      show "cospan f g \<Longrightarrow> arr \<p>\<^sub>0[f, g]"
        using prj0_in_hom by auto
      show "arr \<p>\<^sub>0[f, g] \<Longrightarrow> cospan f g"
        using prj0_ext not_arr_null by metis
    qed

    lemma prj1_simps [simp]:
    assumes "cospan f g"
    shows "arr \<p>\<^sub>1[f, g]" and "dom \<p>\<^sub>1[f, g] = f \<down>\<down> g" and "cod \<p>\<^sub>1[f, g] = dom f"
      using assms prj1_in_hom by (blast, blast, blast)

    lemma prj1_simps_arr [iff]:
    shows "arr \<p>\<^sub>1[f, g] \<longleftrightarrow> cospan f g"
    proof
      show "cospan f g \<Longrightarrow> arr \<p>\<^sub>1[f, g]"
        using prj1_in_hom by auto
      show "arr \<p>\<^sub>1[f, g] \<Longrightarrow> cospan f g"
        using prj1_ext not_arr_null by metis
    qed

    lemma span_prj:
    assumes "cospan f g"
    shows "span \<p>\<^sub>0[f, g] \<p>\<^sub>1[f, g]"
      using assms by simp

    text \<open>
      We introduce a notation for tupling, which produces the induced arrow into a pullback.
      In our notation, the ``$0$-side'', which we regard as the input, occurs on the right,
      and the ``$1$-side'', which we regard as the output, occurs on the left.
    \<close>

    definition tuple         ("\<langle>_ \<lbrakk>_, _\<rbrakk> _\<rangle>")
    where "\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<equiv> if commutative_square f g h k then
                           THE l. \<p>\<^sub>0[f, g] \<cdot> l = k \<and> \<p>\<^sub>1[f, g] \<cdot> l = h
                         else null"

    lemma tuple_in_hom [intro]:
    assumes "commutative_square f g h k"
    shows "\<guillemotleft>\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> : dom h \<rightarrow> f \<down>\<down> g\<guillemotright>"
    proof
      have 1: "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = k \<and> \<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = h"
        unfolding tuple_def
        using assms universal theI [of "\<lambda>l. \<p>\<^sub>0[f, g] \<cdot> l = k \<and> \<p>\<^sub>1[f, g] \<cdot> l = h"]
        apply simp
        by meson
      show "arr \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle>"
        using assms 1
        apply (elim commutative_squareE)
        by (metis (no_types, lifting) seqE)
      show "dom \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = dom h"
        using assms 1
        apply (elim commutative_squareE)
        by (metis (no_types, lifting) dom_comp)
      show "cod \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = f \<down>\<down> g"
        unfolding pbdom_def
        using assms 1
        apply (elim commutative_squareE)
        by (metis seqE)
    qed

    lemma tuple_is_extensional:
    assumes "\<not> commutative_square f g h k"
    shows "\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = null"
      unfolding tuple_def
      using assms by simp

    lemma tuple_simps [simp]:
    assumes "commutative_square f g h k"
    shows "arr \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle>" and "dom \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = dom h" and "cod \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = f \<down>\<down> g"
      using assms tuple_in_hom apply blast
      using assms tuple_in_hom apply blast
      using assms tuple_in_hom by blast

    lemma prj_tuple [simp]:
    assumes "commutative_square f g h k"
    shows "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = k" and "\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = h"
    proof -
      have 1: "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = k \<and> \<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = h"
        unfolding tuple_def
        using assms universal theI [of "\<lambda>l. \<p>\<^sub>0[f, g] \<cdot> l = k \<and> \<p>\<^sub>1[f, g] \<cdot> l = h"]
        apply simp
        by meson
      show "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = k" using 1 by simp
      show "\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = h" using 1 by simp
    qed

    lemma tuple_prj:
    assumes "cospan f g" and "seq \<p>\<^sub>1[f, g] h"
    shows "\<langle>\<p>\<^sub>1[f, g] \<cdot> h \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h\<rangle> = h"
    proof -
      have 1: "commutative_square f g (\<p>\<^sub>1[f, g] \<cdot> h) (\<p>\<^sub>0[f, g] \<cdot> h)"
        using assms pullback_commutes
        by (simp add: commutative_square_comp_arr)
      have "\<p>\<^sub>0[f, g] \<cdot> \<langle>\<p>\<^sub>1[f, g] \<cdot> h \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h\<rangle> = \<p>\<^sub>0[f, g] \<cdot> h"
        using assms 1 by simp
      moreover have "\<p>\<^sub>1[f, g] \<cdot> \<langle>\<p>\<^sub>1[f, g] \<cdot> h \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h\<rangle> = \<p>\<^sub>1[f, g] \<cdot> h"
        using assms 1 by simp
      ultimately show ?thesis
        unfolding tuple_def
        using assms 1 universal [of f g "\<p>\<^sub>1[f, g] \<cdot> h" "\<p>\<^sub>0[f, g] \<cdot> h"]
              theI_unique [of "\<lambda>l. \<p>\<^sub>0[f, g] \<cdot> l = \<p>\<^sub>0[f, g] \<cdot> h \<and> \<p>\<^sub>1[f, g] \<cdot> l = \<p>\<^sub>1[f, g] \<cdot> h" h]
        by auto
    qed

    lemma tuple_prj_spc [simp]:
    assumes "cospan f g"
    shows "\<langle>\<p>\<^sub>1[f, g] \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g]\<rangle> = f \<down>\<down> g"
    proof -
      have "\<langle>\<p>\<^sub>1[f, g] \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g]\<rangle> = \<langle>\<p>\<^sub>1[f, g] \<cdot> (f \<down>\<down> g) \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> (f \<down>\<down> g)\<rangle>"
        using assms comp_arr_dom by simp
      thus ?thesis
        using assms tuple_prj by simp
    qed

    lemma prj_joint_monic:
    assumes "cospan f g" and "seq \<p>\<^sub>1[f, g] h" and "seq \<p>\<^sub>1[f, g] h'"
    and "\<p>\<^sub>0[f, g] \<cdot> h = \<p>\<^sub>0[f, g] \<cdot> h'" and "\<p>\<^sub>1[f, g] \<cdot> h = \<p>\<^sub>1[f, g] \<cdot> h'"
    shows "h = h'"
    proof -
      have "h = \<langle>\<p>\<^sub>1[f, g] \<cdot> h \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h\<rangle>"
        using assms tuple_prj [of f g h] by simp
      also have "... = \<langle>\<p>\<^sub>1[f, g] \<cdot> h' \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h'\<rangle>"
        using assms by simp
      also have "... = h'"
        using assms tuple_prj [of f g h'] by simp
      finally show ?thesis by blast
    qed

    text \<open>
      The pullback of an identity along an arbitrary arrow is an isomorphism.
    \<close>

    lemma iso_pullback_ide:
    assumes "cospan \<mu> \<nu>" and "ide \<mu>"
    shows "iso \<p>\<^sub>0[\<mu>, \<nu>]"
    proof -
      have "inverse_arrows \<p>\<^sub>0[\<mu>, \<nu>] \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle>"
      proof
        show 1: "ide (\<p>\<^sub>0[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle>)"
          using assms comp_arr_dom comp_cod_arr prj_tuple(1) by simp
        show "ide (\<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>])"
        proof -
          have "\<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = (\<mu> \<down>\<down> \<nu>)"
          proof -
            have "\<p>\<^sub>0[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = \<p>\<^sub>0[\<mu>, \<nu>] \<cdot> (\<mu> \<down>\<down> \<nu>)"
            proof -
              have "\<p>\<^sub>0[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = (\<p>\<^sub>0[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle>) \<cdot> \<p>\<^sub>0[\<mu>, \<nu>]"
                using assms 1 comp_reduce by blast
              also have "... = \<p>\<^sub>0[\<mu>, \<nu>] \<cdot> (\<mu> \<down>\<down> \<nu>)"
                using assms prj_tuple(1) pullback_commutes comp_arr_dom comp_cod_arr by simp
              finally show ?thesis by blast
            qed
            moreover have "\<p>\<^sub>1[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = \<p>\<^sub>1[\<mu>, \<nu>] \<cdot> (\<mu> \<down>\<down> \<nu>)"
            proof -
              have "\<p>\<^sub>1[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = (\<p>\<^sub>1[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle>) \<cdot> \<p>\<^sub>0[\<mu>, \<nu>]"
                using assms(2) comp_assoc by simp
              also have "... = \<nu> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>]"
                using assms comp_arr_dom comp_cod_arr prj_tuple(2) by fastforce
              also have "... = \<mu> \<cdot> \<p>\<^sub>1[\<mu>, \<nu>]"
                using assms pullback_commutes commutative_square_def by simp
              also have "... = \<p>\<^sub>1[\<mu>, \<nu>] \<cdot> (\<mu> \<down>\<down> \<nu>)"
                using assms comp_arr_dom comp_cod_arr pullback_commutes commutative_square_def
                by simp
              finally show ?thesis by simp
            qed
            ultimately show ?thesis
              using assms prj0_in_hom prj1_in_hom comp_arr_dom prj1_simps(1-2) prj_joint_monic
              by metis
          qed
          thus ?thesis
            using assms by auto
        qed
      qed
      thus ?thesis by auto
    qed

    lemma comp_tuple_arr:
    assumes "commutative_square f g h k" and "seq h l"
    shows "\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
    proof -
      have "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = \<p>\<^sub>0[f, g] \<cdot> \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
      proof -
        have "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = (\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle>) \<cdot> l"
          using comp_assoc by simp
        also have "... = \<p>\<^sub>0[f, g] \<cdot> \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
          using assms commutative_square_comp_arr by auto
        finally show ?thesis by blast
      qed
      moreover have "\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = \<p>\<^sub>1[f, g] \<cdot> \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
      proof -
        have "\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = (\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle>) \<cdot> l"
          using comp_assoc by simp
        also have "... = \<p>\<^sub>1[f, g] \<cdot> \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
          using assms commutative_square_comp_arr by auto
        finally show ?thesis by blast
      qed
      moreover have "seq \<p>\<^sub>1[f, g] (\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l)"
        using assms tuple_in_hom prj1_in_hom by fastforce
      ultimately show ?thesis
        using assms prj_joint_monic [of f g "\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l" "\<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"]
        by auto
    qed

    lemma pullback_arr_cod:
    assumes "arr f"
    shows "inverse_arrows \<p>\<^sub>1[f, cod f] \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>"
    and "inverse_arrows \<p>\<^sub>0[cod f, f] \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>"
    proof -
      show "inverse_arrows \<p>\<^sub>1[f, cod f] \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>"
      proof
        show "ide (\<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f])"
        proof -
          have "\<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] = f \<down>\<down> cod f"
          proof -
            have "\<p>\<^sub>0[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] = \<p>\<^sub>0[f, cod f] \<cdot> (f \<down>\<down> cod f)"
            proof -
              have "\<p>\<^sub>0[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] =
                    (\<p>\<^sub>0[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>) \<cdot> \<p>\<^sub>1[f, cod f]"
                using comp_assoc by simp
              also have "... = \<p>\<^sub>0[f, cod f] \<cdot> (f \<down>\<down> cod f)"
                using assms pullback_commutes [of f "cod f"] comp_arr_dom comp_cod_arr
                by auto
              finally show ?thesis by blast
            qed
            moreover
            have "\<p>\<^sub>1[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] = \<p>\<^sub>1[f, cod f] \<cdot> (f \<down>\<down> cod f)"
            proof -
              have "\<p>\<^sub>1[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] =
                    (\<p>\<^sub>1[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>) \<cdot> \<p>\<^sub>1[f, cod f]"
                using assms comp_assoc by presburger
              also have "... = \<p>\<^sub>1[f, cod f] \<cdot> (f \<down>\<down> cod f)"
                using assms comp_arr_dom comp_cod_arr by simp
              finally show ?thesis by blast
            qed
            ultimately show ?thesis
              using assms
                    prj_joint_monic
                      [of f "cod f" "\<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f]" "f \<down>\<down> cod f"]
              by simp
          qed
          thus ?thesis
            using assms arr_cod cod_cod prj1_simps_arr by simp
        qed
        show "ide (\<p>\<^sub>1[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>)"
          using assms comp_arr_dom comp_cod_arr by fastforce
      qed
      show "inverse_arrows \<p>\<^sub>0[cod f, f] \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>"
      proof
        show "ide (\<p>\<^sub>0[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>)"
          using assms comp_arr_dom comp_cod_arr by simp
        show "ide (\<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f])"
        proof -
          have "\<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] = cod f \<down>\<down> f"
          proof -
            have "\<p>\<^sub>0[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] = \<p>\<^sub>0[cod f, f] \<cdot> (cod f \<down>\<down> f)"
            proof -
              have "\<p>\<^sub>0[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] =
                    (\<p>\<^sub>0[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>) \<cdot> \<p>\<^sub>0[cod f, f]"
                using comp_assoc by simp
              also have "... = dom f \<cdot> \<p>\<^sub>0[cod f, f]"
                using assms comp_arr_dom comp_cod_arr by simp
              also have "... = \<p>\<^sub>0[cod f, f] \<cdot> (cod f \<down>\<down> f)"
                using assms comp_arr_dom comp_cod_arr by simp
              finally show ?thesis
                using prj0_in_hom by blast
            qed
            moreover
            have "\<p>\<^sub>1[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] = \<p>\<^sub>1[cod f, f] \<cdot> (cod f \<down>\<down> f)"
            proof -
              have "\<p>\<^sub>1[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] =
                    (\<p>\<^sub>1[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>) \<cdot> \<p>\<^sub>0[cod f, f]"
                using comp_assoc by simp
              also have "... = \<p>\<^sub>1[cod f, f] \<cdot> (cod f \<down>\<down> f)"
                using assms pullback_commutes [of "cod f" f] comp_arr_dom comp_cod_arr
                by auto
              finally show ?thesis by blast
            qed
            ultimately show ?thesis
              using assms prj_joint_monic [of "cod f" f "\<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f]"]
              by simp
          qed
          thus ?thesis using assms by simp
        qed
      qed
    qed

    text \<open>
      The pullback of a monomorphism along itself is automatically symmetric: the left
      and right projections are equal.
    \<close>

    lemma pullback_mono_self:
    assumes "mono f"
    shows "\<p>\<^sub>0[f, f] = \<p>\<^sub>1[f, f]"
    proof -
      have "f \<cdot> \<p>\<^sub>0[f, f] = f \<cdot> \<p>\<^sub>1[f, f]"
        using assms pullback_commutes [of f f]
        by (metis commutative_squareE mono_implies_arr)
      thus ?thesis
        using assms monoE [of f "\<p>\<^sub>1[f, f]" "\<p>\<^sub>0[f, f]"]
        by (metis mono_implies_arr prj0_simps(1,3) seqI)
    qed

    lemma pullback_iso_self:
    assumes "iso f"
    shows "\<p>\<^sub>0[f, f] = \<p>\<^sub>1[f, f]"
      using assms pullback_mono_self iso_is_section section_is_mono by simp

    lemma pullback_ide_self [simp]:
    assumes "ide a"
    shows "\<p>\<^sub>0[a, a] = \<p>\<^sub>1[a, a]"
      using assms pullback_iso_self ide_is_iso by blast

  end

  section "Agreement between the Definitions"

  text \<open>
    It is very easy to write locale assumptions that have unintended consequences
    or that are even inconsistent.  So, to keep ourselves honest, we don't just accept the
    definition of ``elementary category with pullbacks'', but in fact we formally establish
    the sense in which it agrees with our standard definition of ``category with pullbacks'',
    which is given in terms of limit cones.
    This is extra work, but it ensures that we didn't make a mistake.
  \<close>

  context category_with_pullbacks
  begin

    definition some_prj1  ("\<p>\<^sub>1\<^sup>?[_, _]")
    where "\<p>\<^sub>1\<^sup>?[f, g] \<equiv> if cospan f g then
                         fst (SOME x. cospan_diagram.has_as_pullback C f g (fst x) (snd x))
                       else null"

    definition some_prj0  ("\<p>\<^sub>0\<^sup>?[_, _]")
    where "\<p>\<^sub>0\<^sup>?[f, g] \<equiv> if cospan f g then
                         snd (SOME x. cospan_diagram.has_as_pullback C f g (fst x) (snd x))
                       else null"

    lemma prj_yields_pullback:
    assumes "cospan f g"
    shows "cospan_diagram.has_as_pullback C f g \<p>\<^sub>1\<^sup>?[f, g] \<p>\<^sub>0\<^sup>?[f, g]"
    proof -
      have "\<exists>x. cospan_diagram.has_as_pullback C f g (fst x) (snd x)"
        using assms has_pullbacks has_pullbacks_def has_as_pullback_def by simp
      thus ?thesis
        using assms has_pullbacks has_pullbacks_def some_prj0_def some_prj1_def
              someI_ex [of "\<lambda>x. cospan_diagram.has_as_pullback C f g (fst x) (snd x)"]
        by simp
    qed

    interpretation elementary_category_with_pullbacks C some_prj0 some_prj1
    proof
      show "\<And>f g. \<not> cospan f g \<Longrightarrow> \<p>\<^sub>0\<^sup>?[f, g] = null"
        using some_prj0_def by auto
      show "\<And>f g. \<not> cospan f g \<Longrightarrow> \<p>\<^sub>1\<^sup>?[f, g] = null"
        using some_prj1_def by auto
      show "\<And>f g. cospan f g \<Longrightarrow> commutative_square f g \<p>\<^sub>1\<^sup>?[f, g] \<p>\<^sub>0\<^sup>?[f, g]"
      proof
        fix f g
        assume fg: "cospan f g"
        show "cospan f g" by fact
        interpret J: cospan_shape .
        interpret D: cospan_diagram C f g
          using fg by (unfold_locales, auto)
        let ?\<chi> = "D.mkCone \<p>\<^sub>1\<^sup>?[f, g] \<p>\<^sub>0\<^sup>?[f, g]"
        interpret \<chi>: limit_cone J.comp C D.map \<open>dom \<p>\<^sub>1\<^sup>?[f, g]\<close> ?\<chi>
          using fg prj_yields_pullback by auto
        have 1: "\<p>\<^sub>1\<^sup>?[f, g] = ?\<chi> J.AA \<and> \<p>\<^sub>0\<^sup>?[f, g] = ?\<chi> J.BB"
          using D.mkCone_def by simp
        show "span \<p>\<^sub>1\<^sup>?[f, g] \<p>\<^sub>0\<^sup>?[f, g]"
        proof -
          have "arr \<p>\<^sub>1\<^sup>?[f, g] \<and> arr \<p>\<^sub>0\<^sup>?[f, g]"
            using 1 J.arr_char J.seq_char
            by (metis J.seqE \<chi>.preserves_reflects_arr)
          moreover have "dom \<p>\<^sub>1\<^sup>?[f, g] = dom \<p>\<^sub>0\<^sup>?[f, g]"
            using 1 D.is_rendered_commutative_by_cone \<chi>.cone_axioms J.seq_char
            by (metis J.cod_eqI J.seqE \<chi>.A.map_simp \<chi>.preserves_dom J.ide_char)
          ultimately show ?thesis by simp
        qed
        show "dom f = cod \<p>\<^sub>1\<^sup>?[f, g]"
          using 1 fg \<chi>.preserves_cod [of J.BB] J.cod_char D.mkCone_def
          by (metis D.map.simps(1) D.preserves_cod J.seqE \<chi>.preserves_cod cod_dom J.seq_char)
        show "f \<cdot> \<p>\<^sub>1\<^sup>?[f, g] = g \<cdot> \<p>\<^sub>0\<^sup>?[f, g]"
          using 1 fg D.is_rendered_commutative_by_cone \<chi>.cone_axioms by force
      qed
      show "\<And>f g h k. commutative_square f g h k \<Longrightarrow> \<exists>!l. \<p>\<^sub>1\<^sup>?[f, g] \<cdot> l = h \<and> \<p>\<^sub>0\<^sup>?[f, g] \<cdot> l = k"
      proof -
        fix f g h k
        assume fghk: "commutative_square f g h k"
        interpret J: cospan_shape .
        interpret D: cospan_diagram C f g
          using fghk by (unfold_locales, auto)
        let ?\<chi> = "D.mkCone \<p>\<^sub>1\<^sup>?[f, g] \<p>\<^sub>0\<^sup>?[f, g]"
        interpret \<chi>: limit_cone J.comp C D.map \<open>dom \<p>\<^sub>1\<^sup>?[f, g]\<close> ?\<chi>
          using fghk prj_yields_pullback by auto
        interpret \<chi>: pullback_cone C f g \<open>\<p>\<^sub>1\<^sup>?[f, g]\<close> \<open>\<p>\<^sub>0\<^sup>?[f, g]\<close> ..
        have 1: "\<p>\<^sub>1\<^sup>?[f, g] = ?\<chi> J.AA \<and> \<p>\<^sub>0\<^sup>?[f, g] = ?\<chi> J.BB"
          using D.mkCone_def by simp
        show "\<exists>!l. \<p>\<^sub>1\<^sup>?[f, g] \<cdot> l = h \<and> \<p>\<^sub>0\<^sup>?[f, g] \<cdot> l = k"
        proof
          let ?l = "SOME l. \<p>\<^sub>1\<^sup>?[f, g] \<cdot> l = h \<and> \<p>\<^sub>0\<^sup>?[f, g] \<cdot> l = k"
          show "\<p>\<^sub>1\<^sup>?[f, g] \<cdot> ?l = h \<and> \<p>\<^sub>0\<^sup>?[f, g] \<cdot> ?l = k"
             using fghk \<chi>.is_universal' \<chi>.renders_commutative
                   someI_ex [of "\<lambda>l. \<p>\<^sub>1\<^sup>?[f, g] \<cdot> l = h \<and> \<p>\<^sub>0\<^sup>?[f, g] \<cdot> l = k"]
             by blast
          thus "\<And>l. \<p>\<^sub>1\<^sup>?[f, g] \<cdot> l = h \<and> \<p>\<^sub>0\<^sup>?[f, g] \<cdot> l = k \<Longrightarrow> l = ?l"
            using fghk \<chi>.is_universal' \<chi>.renders_commutative limit_cone_def
            by (metis (no_types, lifting) in_homI seqE commutative_squareE dom_comp seqI)
        qed
      qed
    qed

    proposition extends_to_elementary_category_with_pullbacks:
    shows "elementary_category_with_pullbacks C some_prj0 some_prj1"
      ..

  end

  context elementary_category_with_pullbacks
  begin

    interpretation category_with_pullbacks C
    proof
      show "has_pullbacks"
      proof (unfold has_pullbacks_def)
        have "\<And>f g. cospan f g \<Longrightarrow> \<exists>p0 p1. has_as_pullback f g p0 p1"
        proof -
          fix f g
          assume fg: "cospan f g"
          have "has_as_pullback f g \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]"
            using fg has_as_pullbackI pullback_commutes universal by presburger
          thus "\<exists>p0 p1. has_as_pullback f g p0 p1" by blast
        qed
        thus "\<forall>f g. cospan f g \<longrightarrow> (\<exists>p0 p1. has_as_pullback f g p0 p1)"
          by simp
      qed
    qed

    proposition is_category_with_pullbacks:
    shows "category_with_pullbacks C"
      ..

  end

  sublocale elementary_category_with_pullbacks \<subseteq> category_with_pullbacks
    using is_category_with_pullbacks by auto

end

