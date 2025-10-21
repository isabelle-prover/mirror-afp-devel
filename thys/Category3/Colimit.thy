(*  Title:       Colimit
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2025
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Colimit

theory Colimit
imports Category3.Limit
begin

  text\<open>
    After mulling it over for a long time, I do not have any strong sense that it would be
    simpler or more useful to try to come up with some clever way of dualizing the material
    in @{theory Category3.Limit}, than just to do the dualization directly.  This theory
    therefore contains (a portion of) such a direct dualization, including at least the general
    definitions of cocone and colimit, and including particular special cases of colimits
    that I have wanted to work with.  I have omitted theorems about preservation of colimits
    for now.
\<close>

section "Diagrams and Cocones"

  text\<open>
    A \emph{cocone} over a diagram \<open>D: J \<rightarrow> C\<close> is a natural transformation
    from @{term D} to a constant functor.  The value of the constant functor is
    the \emph{apex} of the cocone.
\<close>

  locale cocone =
    C: category C +
    J: category J +
    D: diagram J C D +
    A: constant_functor J C a +
    natural_transformation J C D A.map \<chi>
  for J :: "'j comp"      (infixr \<open>\<cdot>\<^sub>J\<close> 55)
  and C :: "'c comp"      (infixr \<open>\<cdot>\<close> 55)
  and D :: "'j \<Rightarrow> 'c"
  and a :: 'c
  and \<chi> :: "'j \<Rightarrow> 'c"
  begin

    lemma ide_apex:
    shows "C.ide a"
      using A.value_is_ide by auto

    lemma component_in_hom:
    assumes "J.arr j"
    shows "\<guillemotleft>\<chi> j : D (J.dom j) \<rightarrow> a\<guillemotright>"
      using assms by auto

    lemma dom_determines_component:
    assumes "J.arr j"
    shows "\<chi> j = \<chi> (J.dom j)"
      by (metis A.map_simp J.arr_dom_iff_arr J.dom_dom assms naturality1)

  end

  text\<open>
    A cocone over diagram @{term D} is transformed into a cocone over diagram @{term "D o F"}
    by pre-composing with @{term F}.
\<close>

  lemma comp_cocone_functor:
  assumes "cocone J C D a \<chi>" and "functor J' J F"
  shows "cocone J' C (D o F) a (\<chi> o F)"
  proof -
    interpret \<chi>: cocone J C D a \<chi> using assms(1) by auto
    interpret F: "functor" J' J F using assms(2) by auto
    interpret A': constant_functor J' C a
      using \<chi>.A.value_is_ide by unfold_locales auto
    have 1: "\<chi>.A.map o F = A'.map"
      using \<chi>.A.map_def A'.map_def \<chi>.J.not_arr_null by auto
    interpret \<chi>': natural_transformation J' C \<open>D o F\<close> A'.map \<open>\<chi> o F\<close>
      using 1 horizontal_composite F.as_nat_trans.natural_transformation_axioms
            \<chi>.natural_transformation_axioms
      by fastforce
    show "cocone J' C (D o F) a (\<chi> o F)" ..
  qed

  text\<open>
    A cocone over diagram @{term D} can be transformed into a cocone over a diagram @{term D'}
    by pre-composing with a natural transformation from @{term D'} to @{term D}.
\<close>

  lemma vcomp_transformation_cocone:
  assumes "cocone J C D a \<chi>"
  and "natural_transformation J C D' D \<tau>"
  shows "cocone J C D' a (vertical_composite.map J C \<tau> \<chi>)"
    by (meson assms(1,2) cocone.axioms(4,5) cocone.intro diagram.intro natural_transformation_def
        vertical_composite.intro vertical_composite.is_natural_transformation)

  context "functor"
  begin

    lemma preserves_cocones:
    fixes J :: "'j comp"
    assumes "cocone J A D a \<chi>"
    shows "cocone J B (F o D) (F a) (F o \<chi>)"
    proof -
      interpret \<chi>: cocone J A D a \<chi> using assms by auto
      interpret Fa: constant_functor J B \<open>F a\<close>
        using \<chi>.ide_apex by unfold_locales auto
      have 1: "F o \<chi>.A.map = Fa.map"
      proof
        fix f
        show "(F \<circ> \<chi>.A.map) f = Fa.map f"
          using extensionality Fa.extensionality \<chi>.A.extensionality
          by (cases "\<chi>.J.arr f", simp_all)
      qed
      interpret \<chi>': natural_transformation J B \<open>F o D\<close> Fa.map \<open>F o \<chi>\<close>
        using 1 horizontal_composite \<chi>.natural_transformation_axioms
              as_nat_trans.natural_transformation_axioms
        by fastforce
      show "cocone J B (F o D) (F a) (F o \<chi>)" ..
    qed

  end

  context diagram
  begin

    abbreviation cocone
    where "cocone a \<chi> \<equiv> Colimit.cocone J C D a \<chi>"

    abbreviation cocones :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) set"
    where "cocones a \<equiv> { \<chi>. cocone a \<chi> }"

    text\<open>
      An arrow @{term "f \<in> C.hom a a'"} induces by composition a transformation from
      cocones with apex @{term a} to cocones with apex @{term a'}.  This transformation
      is functorial in @{term f}.
\<close>

    abbreviation cocones_map :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) \<Rightarrow> ('j \<Rightarrow> 'c)"
    where "cocones_map f \<equiv> (\<lambda>\<chi> \<in> cocones (C.dom f). \<lambda>j. if J.arr j then f \<cdot> \<chi> j else C.null)"

    lemma cocones_map_mapsto:
    assumes "C.arr f"
    shows "cocones_map f \<in>
             extensional (cocones (C.dom f)) \<inter> (cocones (C.dom f) \<rightarrow> cocones (C.cod f))"
    proof
      show "cocones_map f \<in> extensional (cocones (C.dom f))" by blast
      show "cocones_map f \<in> cocones (C.dom f) \<rightarrow> cocones (C.cod f)"
      proof
        fix \<chi>
        assume "\<chi> \<in> cocones (C.dom f)"
        hence \<chi>: "cocone (C.dom f) \<chi>" by auto
        interpret \<chi>: cocone J C D \<open>C.dom f\<close> \<chi> using \<chi> by auto
        interpret B: constant_functor J C \<open>C.cod f\<close>
          using assms by unfold_locales auto
        have "cocone (C.cod f) (\<lambda>j. if J.arr j then f \<cdot> \<chi> j else C.null)"
          using assms B.value_is_ide
          apply (unfold_locales, simp_all)
           apply (metis C.comp_assoc C.comp_cod_arr \<chi>.dom_determines_component)
          by (simp add: C.comp_assoc)
        thus "(\<lambda>j. if J.arr j then f \<cdot> \<chi> j else C.null) \<in> cocones (C.cod f)" by auto
      qed
    qed

    lemma cocones_map_ide:
    assumes "\<chi> \<in> cocones a"
    shows "cocones_map a \<chi> = \<chi>"
    proof -
      interpret \<chi>: cocone J C D a \<chi> using assms by auto
      show ?thesis
        using assms \<chi>.A.value_is_ide \<chi>.preserves_hom C.comp_cod_arr \<chi>.extensionality
        by auto
    qed

    lemma cocones_map_comp:
    assumes "C.seq g f"
    shows "cocones_map (g \<cdot> f) = restrict (cocones_map g o cocones_map f) (cocones (C.dom f))"
    proof (intro restr_eqI)
      show "cocones (C.dom (g \<cdot> f)) = cocones (C.dom f)" using assms by simp
      show "\<And>\<chi>. \<chi> \<in> cocones (C.dom (g \<cdot> f)) \<Longrightarrow>
                  (\<lambda>j. if J.arr j then (g \<cdot> f) \<cdot> \<chi> j else C.null) =
                  (cocones_map g o cocones_map f) \<chi>"
      proof -
        fix \<chi>
        assume \<chi>: "\<chi> \<in> cocones (C.dom (g \<cdot> f))"
        show "(\<lambda>j. if J.arr j then (g \<cdot> f) \<cdot> \<chi> j else C.null) = (cocones_map g o cocones_map f) \<chi>"
        proof -
          have "((cocones_map g) o (cocones_map f)) \<chi> = cocones_map g (cocones_map f \<chi>)"
            by force
          also have "... = (\<lambda>j. if J.arr j
                                then g \<cdot> (\<lambda>j. if J.arr j then f \<cdot> \<chi> j else C.null) j
                                else C.null)"
          proof
            fix j
            have "cocone (C.cod f) (cocones_map f \<chi>)"
              using assms \<chi> cocones_map_mapsto by (elim C.seqE, force)
            thus "cocones_map g (cocones_map f \<chi>) j =
                  (if J.arr j then g \<cdot> (\<lambda>j. if J.arr j then f \<cdot> \<chi> j else C.null) j else C.null)"
              using \<chi> assms by auto
          qed
          also have "... = (\<lambda>j. if J.arr j then (g \<cdot> f) \<cdot> \<chi> j else C.null)"
            using C.comp_assoc by fastforce
          finally show ?thesis by auto
        qed
      qed
    qed

  end

  text\<open>
    Changing the apex of a cocone by post-composing with an arrow @{term f} commutes
    with changing the diagram of a cocone by pre-composing with a natural transformation.
\<close>

  lemma cones_map_vcomp:
  assumes "diagram J C D" and "diagram J C D'"
  and "natural_transformation J C D D' \<tau>"
  and "cone J C D a \<chi>"
  and f: "partial_composition.in_hom C f a' a"
  shows "diagram.cones_map J C D' f (vertical_composite.map J C \<chi> \<tau>)
           = vertical_composite.map J C (diagram.cones_map J C D f \<chi>) \<tau>"
  proof -
    interpret D: diagram J C D using assms(1) by auto
    interpret D': diagram J C D' using assms(2) by auto
    interpret \<tau>: natural_transformation J C D D' \<tau> using assms(3) by auto
    interpret \<chi>: cone J C D a \<chi> using assms(4) by auto
    interpret \<tau>o\<chi>: vertical_composite J C \<chi>.A.map D D' \<chi> \<tau> ..
    interpret \<tau>o\<chi>: cone J C D' a \<tau>o\<chi>.map ..
    interpret \<chi>f: cone J C D a' \<open>D.cones_map f \<chi>\<close>
      using f \<chi>.cone_axioms D.cones_map_mapsto by blast
    interpret \<tau>o\<chi>f: vertical_composite J C \<chi>f.A.map D D' \<open>D.cones_map f \<chi>\<close> \<tau> ..
    interpret \<tau>o\<chi>_f: cone J C D' a' \<open>D'.cones_map f \<tau>o\<chi>.map\<close>
      using f \<tau>o\<chi>.cone_axioms D'.cones_map_mapsto [of f] by blast
    write C (infixr \<open>\<cdot>\<close> 55)
    show "D'.cones_map f \<tau>o\<chi>.map = \<tau>o\<chi>f.map"
    proof (intro natural_transformation_eqI)
      show "natural_transformation J C \<chi>f.A.map D' (D'.cones_map f \<tau>o\<chi>.map)" ..
      show "natural_transformation J C \<chi>f.A.map D' \<tau>o\<chi>f.map" ..
      show "\<And>j. D.J.ide j \<Longrightarrow> D'.cones_map f \<tau>o\<chi>.map j = \<tau>o\<chi>f.map j"
      proof -
        fix j
        assume j: "D.J.ide j"
        have "D'.cones_map f \<tau>o\<chi>.map j = \<tau>o\<chi>.map j \<cdot> f"
          using f \<tau>o\<chi>.cone_axioms \<tau>o\<chi>.map_simp_2 \<tau>o\<chi>.extensionality by auto
        also have "... = (\<tau> j \<cdot> \<chi> (D.J.dom j)) \<cdot> f"
          using j \<tau>o\<chi>.map_simp_2 by simp
        also have "... = \<tau> j \<cdot> \<chi> (D.J.dom j) \<cdot> f"
          using D.C.comp_assoc by simp
        also have "... = \<tau>o\<chi>f.map j"
          using j f \<chi>.cone_axioms \<tau>o\<chi>f.map_simp_2 by auto
        finally show "D'.cones_map f \<tau>o\<chi>.map j = \<tau>o\<chi>f.map j" by auto
      qed
    qed
  qed

  section "Colimits"

  subsection "Colimit Cocones"

  text\<open>
    A \emph{colimit cocone} for a diagram @{term D} is a cocone @{term \<chi>} over @{term D}
    with the couniversal property that any other cocone @{term \<chi>'} over the diagram @{term D}
    factors uniquely through @{term \<chi>}.
\<close>

  locale colimit_cocone =
    C: category C +
    J: category J +
    D: diagram J C D +
    cocone J C D a \<chi>
  for J :: "'j comp"      (infixr \<open>\<cdot>\<^sub>J\<close> 55)
  and C :: "'c comp"      (infixr \<open>\<cdot>\<close> 55)
  and D :: "'j \<Rightarrow> 'c"
  and a :: 'c
  and \<chi> :: "'j \<Rightarrow> 'c" +
  assumes is_couniversal: "cocone J C D a' \<chi>' \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> a'\<guillemotright> \<and> D.cocones_map f \<chi> = \<chi>'"
  begin

    lemma is_cocone [simp]:
    shows "\<chi> \<in> D.cocones a"
      using cocone_axioms by simp
    
    definition induced_arrow :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) \<Rightarrow> 'c"
    where "induced_arrow a' \<chi>' = (THE f. \<guillemotleft>f : a \<rightarrow> a'\<guillemotright> \<and> D.cocones_map f \<chi> = \<chi>')"

    lemma induced_arrowI:
    assumes \<chi>': "\<chi>' \<in> D.cocones a'"
    shows "\<guillemotleft>induced_arrow a' \<chi>' : a \<rightarrow> a'\<guillemotright>"
    and "D.cocones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
    proof -
      have "\<exists>!f. \<guillemotleft>f : a \<rightarrow> a'\<guillemotright> \<and> D.cocones_map f \<chi> = \<chi>'"
        using assms \<chi>' is_couniversal by simp
      hence 1: "\<guillemotleft>induced_arrow a' \<chi>' : a \<rightarrow> a'\<guillemotright> \<and> D.cocones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
        using theI' [of "\<lambda>f. \<guillemotleft>f : a \<rightarrow> a'\<guillemotright> \<and> D.cocones_map f \<chi> = \<chi>'"] induced_arrow_def
        by presburger
      show "\<guillemotleft>induced_arrow a' \<chi>' : a \<rightarrow> a'\<guillemotright>" using 1 by simp
      show "D.cocones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'" using 1 by simp
    qed

    lemma cocones_map_induced_arrow:
    shows "induced_arrow a' \<in> D.cocones a' \<rightarrow> C.hom a a'"
    and "\<And>\<chi>'. \<chi>' \<in> D.cocones a' \<Longrightarrow> D.cocones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
      using induced_arrowI by auto

    lemma induced_arrow_cocones_map:
    assumes "C.ide a'"
    shows "(\<lambda>f. D.cocones_map f \<chi>) \<in> C.hom a a' \<rightarrow> D.cocones a'"
    and "\<And>f. \<guillemotleft>f : a \<rightarrow> a'\<guillemotright> \<Longrightarrow> induced_arrow a' (D.cocones_map f \<chi>) = f"
    proof -
      have a': "C.ide a'" using assms by (simp add: cone.ide_apex)
      have cocone_\<chi>: "cocone J C D a \<chi>" ..
      show "(\<lambda>f. D.cocones_map f \<chi>) \<in> C.hom a a' \<rightarrow> D.cocones a'"
        using cocone_\<chi> D.cocones_map_mapsto by blast
      fix f
      assume f: "\<guillemotleft>f : a \<rightarrow> a'\<guillemotright>"
      show "induced_arrow a' (D.cocones_map f \<chi>) = f"
      proof -
        have "D.cocones_map f \<chi> \<in> D.cocones a'"
          using f cocone_\<chi> D.cocones_map_mapsto by blast
        hence "\<exists>!f'. \<guillemotleft>f' : a \<rightarrow> a'\<guillemotright> \<and> D.cocones_map f' \<chi> = D.cocones_map f \<chi>"
          using assms is_couniversal by auto
        thus ?thesis
          using f induced_arrow_def
                the1_equality
                  [of "\<lambda>f'. \<guillemotleft>f' : a \<rightarrow> a'\<guillemotright> \<and> D.cocones_map f' \<chi> = D.cocones_map f \<chi>"]
          by presburger
      qed
    qed

    text\<open>
      For a colimit cocone @{term \<chi>} with apex @{term a}, for each object @{term a'} the
      hom-set @{term "C.hom a a'"} is in bijective correspondence with the set of cocones
      with apex @{term a'}.
\<close>

    lemma bij_betw_hom_and_cocones:
    assumes "C.ide a'"
    shows "bij_betw (\<lambda>f. D.cocones_map f \<chi>) (C.hom a a') (D.cocones a')"
    proof (intro bij_betwI)
      show "(\<lambda>f. D.cocones_map f \<chi>) \<in> C.hom a a' \<rightarrow> D.cocones a'"
        using assms induced_arrow_cocones_map by blast
      show "induced_arrow a' \<in> D.cocones a' \<rightarrow> C.hom a a'"
        using assms cocones_map_induced_arrow by blast
      show "\<And>f. f \<in> C.hom a a' \<Longrightarrow> induced_arrow a' (D.cocones_map f \<chi>) = f"
        using assms induced_arrow_cocones_map by blast
      show "\<And>\<chi>'. \<chi>' \<in> D.cocones a' \<Longrightarrow> D.cocones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
        using assms cocones_map_induced_arrow by blast
    qed

    lemma induced_arrow_eqI:
    assumes "D.cocone a' \<chi>'" and "\<guillemotleft>f : a \<rightarrow> a'\<guillemotright>" and "D.cocones_map f \<chi> = \<chi>'"
    shows "induced_arrow a' \<chi>' = f"
      using assms is_couniversal induced_arrow_def
            the1_equality [of "\<lambda>f. f \<in> C.hom a a' \<and> D.cocones_map f \<chi> = \<chi>'" f]
      by simp

    lemma induced_arrow_self:
    shows "induced_arrow a \<chi> = a"
    proof -
      have "\<guillemotleft>a : a \<rightarrow> a\<guillemotright> \<and> D.cocones_map a \<chi> = \<chi>"
        using ide_apex cocone_axioms D.cocones_map_ide by force
      thus ?thesis using induced_arrow_eqI cocone_axioms by auto
    qed

  end

  context diagram
  begin

    abbreviation colimit_cocone
    where "colimit_cocone a \<chi> \<equiv> Colimit.colimit_cocone J C D a \<chi>"

    text\<open>
      A diagram @{term D} has object @{term a} as a colimit if @{term a} is the apex
      of some colimit cocone over @{term D}.
\<close>

    abbreviation has_as_colimit :: "'c \<Rightarrow> bool"
    where "has_as_colimit a \<equiv> (\<exists>\<chi>. colimit_cocone a \<chi>)"

    abbreviation has_colimit
    where "has_colimit \<equiv> (\<exists>a. has_as_colimit a)"

    definition some_colimit :: 'c
    where "some_colimit = (SOME a. has_as_colimit a)"

    definition some_colimit_cocone :: "'j \<Rightarrow> 'c"
    where "some_colimit_cocone = (SOME \<chi>. colimit_cocone some_colimit \<chi>)"

    lemma colimit_cocone_some_colimit_cocone:
    assumes has_colimit
    shows "colimit_cocone some_colimit some_colimit_cocone"
    proof -
      have "\<exists>a. has_as_colimit a" using assms by simp
      hence "has_as_colimit some_colimit"
        using some_colimit_def someI_ex [of "\<lambda>a. \<exists>\<chi>. colimit_cocone a \<chi>"] by simp
      thus "colimit_cocone some_colimit some_colimit_cocone"
        using assms some_colimit_cocone_def someI_ex [of "\<lambda>\<chi>. colimit_cocone some_colimit \<chi>"]
        by simp
    qed

    lemma has_colimitE:
    assumes has_colimit
    obtains a \<chi> where "colimit_cocone a \<chi>"
      using assms someI_ex by blast

  end

  section "Special Kinds of Coimits"

  subsection "Coproducts"

  text\<open>
    A \emph{coproduct} in a category @{term C} is a colimit of a discrete diagram in @{term C}.
\<close>

  context discrete_diagram
  begin

    abbreviation mkCocone
    where "mkCocone F \<equiv> (\<lambda>j. if J.arr j then F j else C.null)"

    lemma cocone_mkCocone:
    assumes "C.ide a" and "\<And>j. J.arr j \<Longrightarrow> \<guillemotleft>F j : D j \<rightarrow> a\<guillemotright>"
    shows "cocone a (mkCocone F)"
    proof -
      interpret A: constant_functor J C a
         using assms(1) by unfold_locales auto
      show "cocone a (mkCocone F)"
        using assms(2) is_discrete
        apply unfold_locales
            apply auto
         apply (metis C.in_homE C.comp_cod_arr)
        using C.comp_arr_ide by fastforce
    qed

    lemma mkCocone_cocone:
    assumes "cocone a \<pi>"
    shows "mkCocone \<pi> = \<pi>"
    proof -
      interpret \<pi>: cocone J C D a \<pi>
        using assms by auto
      show "mkCocone \<pi> = \<pi>" using \<pi>.extensionality by auto
    qed

  end

  locale coproduct_cocone =
    J: category J +
    C: category C +
    D: discrete_diagram J C D +
    colimit_cocone J C D a \<pi>
  for J :: "'j comp"      (infixr \<open>\<cdot>\<^sub>J\<close> 55)
  and C :: "'c comp"      (infixr \<open>\<cdot>\<close> 55)
  and D :: "'j \<Rightarrow> 'c"
  and a :: 'c
  and \<pi> :: "'j \<Rightarrow> 'c"
  begin

    lemma is_cocone:
    shows "D.cocone a \<pi>" ..

    lemma is_couniversal':
    assumes "C.ide b" and "\<And>j. J.arr j \<Longrightarrow> \<guillemotleft>F j: D j \<rightarrow> b\<guillemotright>"
    shows "\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>j. J.arr j \<longrightarrow> f \<cdot> \<pi> j = F j)"
    proof -
      let ?\<chi> = "D.mkCocone F"
      interpret B: constant_functor J C b
        using assms(1) by unfold_locales auto
      have cocone_\<chi>: "D.cocone b ?\<chi>"
        using assms D.is_discrete D.cocone_mkCocone by blast
      interpret \<chi>: cocone J C D b ?\<chi> using cocone_\<chi> by auto
      have "\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> D.cocones_map f \<pi> = ?\<chi>"
        using cocone_\<chi> is_couniversal by force
      moreover have
           "\<And>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<Longrightarrow> D.cocones_map f \<pi> = ?\<chi> \<longleftrightarrow> (\<forall>j. J.arr j \<longrightarrow> f \<cdot> \<pi> j = F j)"
      proof -
        fix f
        assume f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
        show "D.cocones_map f \<pi> = ?\<chi> \<longleftrightarrow> (\<forall>j. J.arr j \<longrightarrow> f \<cdot> \<pi> j = F j)"
        proof
          assume 1: "D.cocones_map f \<pi> = ?\<chi>"
          show "\<forall>j. J.arr j \<longrightarrow> f \<cdot> \<pi> j = F j"
          proof -
            have "\<And>j. J.arr j \<Longrightarrow> f \<cdot> \<pi> j = F j"
            proof -
              fix j
              assume j: "J.arr j"
              have "f \<cdot> \<pi> j = D.cocones_map f \<pi> j"
                using j f cocone_axioms by force
              also have "... = F j" using j 1 by simp
              finally show "f \<cdot> \<pi> j = F j" by auto
            qed
            thus ?thesis by auto
          qed
          next
          assume 1: "\<forall>j. J.arr j \<longrightarrow> f \<cdot> \<pi> j = F j"
          show "D.cocones_map f \<pi> = ?\<chi>"
            using 1 f is_cocone \<chi>.extensionality D.is_discrete is_cocone cocone_\<chi> by auto
        qed
      qed
      ultimately show ?thesis by blast
    qed

    abbreviation induced_arrow' :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) \<Rightarrow> 'c"
    where "induced_arrow' b F \<equiv> induced_arrow b (D.mkCocone F)"

    lemma induced_arrowI':
    assumes "C.ide b" and "\<And>j. J.arr j \<Longrightarrow> \<guillemotleft>F j : D j \<rightarrow> b\<guillemotright>"
    shows "\<And>j. J.arr j \<Longrightarrow> induced_arrow' b F \<cdot> \<pi> j = F j"
    proof -
      interpret B: constant_functor J C b
        using assms(1) by unfold_locales auto
      interpret \<chi>: cocone J C D b \<open>D.mkCocone F\<close>
        using assms D.cocone_mkCocone by blast
      have cocone_\<chi>: "D.cocone b (D.mkCocone F)" ..
      hence 1: "D.cocones_map (induced_arrow' b F) \<pi> = D.mkCocone F"
        using induced_arrowI by blast
      fix j
      assume j: "J.arr j"
      have "induced_arrow' b F \<cdot> \<pi> j = D.cocones_map (induced_arrow' b F) \<pi> j"
        using induced_arrowI(1) cocone_\<chi> is_cocone extensionality by force
      also have "... = F j"
        using j 1 by auto
      finally show "induced_arrow' b F \<cdot> \<pi> j = F j"
        by auto
    qed

  end

  context discrete_diagram
  begin

    lemma coproduct_coconeI:
    assumes "colimit_cocone a \<pi>"
    shows "coproduct_cocone J C D a \<pi>"
      by (meson assms discrete_diagram_axioms functor_axioms functor_def
          coproduct_cocone.intro)

  end

  context category
  begin

    definition has_as_coproduct
    where "has_as_coproduct J D a \<equiv> (\<exists>\<pi>. coproduct_cocone J C D a \<pi>)"

    abbreviation has_coproduct
    where "has_coproduct J D \<equiv> \<exists>a. has_as_coproduct J D a"

    lemma coproduct_is_ide:
    assumes "has_as_coproduct J D a"
    shows "ide a"
    proof -
      obtain \<pi> where \<pi>: "coproduct_cocone J C D a \<pi>"
        using assms has_as_coproduct_def by blast
      interpret \<pi>: coproduct_cocone J C D a \<pi>
        using \<pi> by auto
      show ?thesis using \<pi>.ide_apex by auto
    qed

    text\<open>
      The reason why we assume @{term "I \<noteq> UNIV"} in the following is the same as
      for products.
\<close>

    definition has_coproducts
    where "has_coproducts (I :: 'i set) \<equiv>
             I \<noteq> UNIV \<and>
             (\<forall>J D. discrete_diagram J C D \<and> Collect (partial_composition.arr J) = I
                      \<longrightarrow> (\<exists>a. has_as_coproduct J D a))"

    lemma has_coproductE:
    assumes "has_coproduct J D"
    obtains a \<pi> where "coproduct_cocone J C D a \<pi>"
      using assms has_as_coproduct_def by metis

  end

  subsection "Coequalizers"

  text\<open>
    An \emph{coequalizer} in a category @{term C} is a colimit of a parallel pair
    of arrows in @{term C}.
\<close>

  context parallel_pair_diagram
  begin

    definition mkCocone
    where " mkCocone e \<equiv> \<lambda>j. if J.arr j then if j = J.One then e else e \<cdot> f0 else C.null"

    abbreviation is_coequalized_by
    where "is_coequalized_by e \<equiv> C.seq e f0 \<and> e \<cdot> f0 = e \<cdot> f1"

    abbreviation has_as_coequalizer
    where "has_as_coequalizer e \<equiv> colimit_cocone (C.cod e) (mkCocone e)"

    lemma cocone_mkCocone:
    assumes "is_coequalized_by e"
    shows "cocone (C.cod e) (mkCocone e)"
    proof -
      interpret E: constant_functor J.comp C \<open>C.cod e\<close>
        using assms by unfold_locales auto
      show "cocone (C.cod e) (mkCocone e)"
      proof (unfold_locales)
        show "\<And>j. \<not> J.arr j \<Longrightarrow> mkCocone e j = C.null"
          using assms mkCocone_def by auto
        show "\<And>j. J.arr j \<Longrightarrow> C.arr (mkCocone e j)"
          using assms mkCocone_def by auto
        show "\<And>j. J.arr j \<Longrightarrow> mkCocone e (J.cod j) \<cdot> map j = mkCocone e j"
          using assms mkCocone_def C.comp_arr_dom extensionality map_def is_parallel
          apply auto
          using parallel_pair.arr_char by auto
        show "\<And>j. J.arr j \<Longrightarrow> E.map j \<cdot> mkCocone e (J.dom j) = mkCocone e j"
          using assms mkCocone_def C.comp_cod_arr
          apply auto[1]
          using parallel_pair.arr_char by fastforce
      qed
    qed

    lemma is_coequalized_by_cocone:
    assumes "cocone a \<chi>"
    shows "is_coequalized_by (\<chi> (J.One))"
    proof -
      interpret \<chi>: cocone J.comp C map a \<chi>
        using assms by auto
      show ?thesis
        by (metis (no_types, lifting) J.arr_char J.cod_char J.dom_char \<chi>.cocone_axioms
            \<chi>.naturality2 \<chi>.preserves_arr cocone.dom_determines_component map_simp(3-4))
    qed

    lemma mkCocone_cocone:
    assumes "cocone a \<chi>"
    shows "mkCocone (\<chi> J.One) = \<chi>"
    proof -
      interpret \<chi>: cocone J.comp C map a \<chi>
        using assms by auto
      have 1: "is_coequalized_by (\<chi> J.One)"
        using assms is_coequalized_by_cocone by blast
      show ?thesis
      proof
        fix j
        have "j = J.One \<Longrightarrow> mkCocone (\<chi> J.One) j = \<chi> j"
          using mkCocone_def \<chi>.extensionality by simp 
        moreover have "j = J.Zero \<or> j = J.j0 \<or> j = J.j1 \<Longrightarrow> mkCocone (\<chi> J.One) j = \<chi> j"
          using J.arr_char J.cod_char J.dom_char J.seq_char mkCocone_def
                \<chi>.naturality1 \<chi>.naturality2 \<chi>.A.map_simp map_def
          by (metis (lifting) map_simp(3))
        ultimately have "J.arr j \<Longrightarrow> mkCocone (\<chi> J.One) j = \<chi> j"
          using J.arr_char by auto
        thus "mkCocone (\<chi> J.One) j = \<chi> j"
          using mkCocone_def \<chi>.extensionality by fastforce
      qed
    qed

  end

  locale coequalizer_cocone =
    J: parallel_pair +
    C: category C +
    D: parallel_pair_diagram C f0 f1 +
    colimit_cocone J.comp C D.map "C.cod e" "D.mkCocone e"
  for C :: "'c comp"      (infixr \<open>\<cdot>\<close> 55)
  and f0 :: 'c
  and f1 :: 'c
  and e :: 'c
  begin

    lemma coequalizes:
    shows "D.is_coequalized_by e"
    proof
      show "C.seq e f0"
      proof (intro C.seqI)
        show "C.arr e" using ide_apex C.arr_cod_iff_arr by fastforce
        show "C.arr f0"
          using D.map_simp D.preserves_arr J.arr_char by metis
        show "C.dom e = C.cod f0"
          using J.arr_char J.ide_char D.mkCocone_def D.map_simp preserves_dom by force
      qed
      show "e \<cdot> f0 = e \<cdot> f1"
        using D.map_simp D.mkCocone_def J.arr_char naturality by force
    qed

    lemma is_couniversal':
    assumes "D.is_coequalized_by e'"
    shows "\<exists>!h. \<guillemotleft>h : C.cod e \<rightarrow> C.cod e'\<guillemotright> \<and> h \<cdot> e = e'"
    proof -
      have "D.cocone (C.cod e') (D.mkCocone e')"
        using assms D.cocone_mkCocone by blast
      moreover have 0: "D.cocone (C.cod e) (D.mkCocone e)" ..
      ultimately have 1: "\<exists>!h. \<guillemotleft>h : C.cod e \<rightarrow> C.cod e'\<guillemotright> \<and>
                               D.cocones_map h (D.mkCocone e) = D.mkCocone e'"
        using is_couniversal [of "C.cod e'" "D.mkCocone e'"] by auto
      have 2: "\<And>h. \<guillemotleft>h : C.cod e \<rightarrow> C.cod e'\<guillemotright> \<Longrightarrow>
                    D.cocones_map h (D.mkCocone e) = D.mkCocone e' \<longleftrightarrow> h \<cdot> e = e'"
      proof -
        fix h
        assume h: "\<guillemotleft>h : C.cod e \<rightarrow> C.cod e'\<guillemotright>"
        show "D.cocones_map h (D.mkCocone e) = D.mkCocone e' \<longleftrightarrow> h \<cdot> e = e'"
        proof
          assume 3: "D.cocones_map h (D.mkCocone e) = D.mkCocone e'"
          show "h \<cdot> e = e'"
          proof -
            have "e' = D.mkCocone e' J.One"
              using D.mkCocone_def J.arr_char by simp
            also have "... = D.cocones_map h (D.mkCocone e) J.One"
              using 3 by simp
            also have "... = h \<cdot> e"
              using 0 h D.mkCocone_def J.arr_char by auto
            finally show ?thesis by auto
          qed
          next
          assume e': "h \<cdot> e = e'"
          show "D.cocones_map h (D.mkCocone e) = D.mkCocone e'"
          proof
            fix j
            have "\<not>J.arr j \<Longrightarrow> D.cocones_map h (D.mkCocone e) j = D.mkCocone e' j"
              using h cocone_axioms D.mkCocone_def by auto
            moreover have "j = J.One \<Longrightarrow> D.cocones_map h (D.mkCocone e) j = D.mkCocone e' j"
              using h e' is_cocone D.mkCocone_def J.arr_char [of J.One] by force
            moreover have
                "J.arr j \<and> j \<noteq> J.One \<Longrightarrow> D.cocones_map h (D.mkCocone e) j = D.mkCocone e' j"
              using C.comp_assoc D.mkCocone_def is_cocone e' h by auto
            ultimately show "D.cocones_map h (D.mkCocone e) j = D.mkCocone e' j" by blast
          qed
        qed
      qed
      thus ?thesis using 1 by blast
    qed

    lemma induced_arrowI':
    assumes "D.is_coequalized_by e'"
    shows "\<guillemotleft>induced_arrow (C.cod e') (D.mkCocone e') : C.cod e \<rightarrow> C.cod e'\<guillemotright>"
    and "induced_arrow (C.cod e') (D.mkCocone e') \<cdot> e = e'"
    proof -
      interpret A': constant_functor J.comp C \<open>C.cod e'\<close>
        using assms by (unfold_locales, auto)
      have cocone: "D.cocone (C.cod e') (D.mkCocone e')"
        using assms D.cocone_mkCocone [of e'] by blast
      have "induced_arrow (C.cod e') (D.mkCocone e') \<cdot> e =
              D.cocones_map (induced_arrow (C.cod e') (D.mkCocone e')) (D.mkCocone e) J.One"
        using cocone induced_arrowI(1) D.mkCocone_def J.arr_char is_cocone by force
      also have "... = e'"
      proof -
        have "D.cocones_map (induced_arrow (C.cod e') (D.mkCocone e')) (D.mkCocone e) =
              D.mkCocone e'"
          using cocone induced_arrowI by blast
        thus ?thesis
          using J.arr_char D.mkCocone_def by simp
      qed
      finally have 1: "induced_arrow (C.cod e') (D.mkCocone e') \<cdot> e = e'"
        by auto
      show "\<guillemotleft>induced_arrow (C.cod e') (D.mkCocone e') : C.cod e \<rightarrow> C.cod e'\<guillemotright>"
        using 1 cocone induced_arrowI by simp
      show "induced_arrow (C.cod e') (D.mkCocone e') \<cdot> e = e'"
        using 1 cocone induced_arrowI by simp
    qed

  end

  context category
  begin

    definition has_as_coequalizer
    where "has_as_coequalizer f0 f1 e \<equiv>
           par f0 f1 \<and> parallel_pair_diagram.has_as_coequalizer C f0 f1 e"

    definition has_coequalizers
    where "has_coequalizers = (\<forall>f0 f1. par f0 f1 \<longrightarrow> (\<exists>e. has_as_coequalizer f0 f1 e))"

    lemma has_as_coequalizerI [intro]:
    assumes "par f g" and "seq e f" and "e \<cdot> f = e \<cdot> g"
    and "\<And>e'. \<lbrakk>seq e' f; e' \<cdot> f = e' \<cdot> g\<rbrakk> \<Longrightarrow> \<exists>!h. h \<cdot> e = e'"
    shows "has_as_coequalizer f g e"
    proof (unfold has_as_coequalizer_def, intro conjI)
      show "arr f" and "arr g" and "dom f = dom g" and "cod f = cod g"
        using assms(1) by auto
      interpret J: parallel_pair .
      interpret D: parallel_pair_diagram C f g
        using assms(1) by unfold_locales
      show "D.has_as_coequalizer e"
      proof -
        let ?\<chi> = "D.mkCocone e"
        let ?a = "cod e"
        interpret \<chi>: cocone J.comp C D.map ?a ?\<chi>
           using assms(2-3) D.cocone_mkCocone [of e] by simp
        interpret \<chi>: colimit_cocone J.comp C D.map ?a ?\<chi>
        proof
          fix a' \<chi>'
          assume \<chi>': "D.cocone a' \<chi>'"
          interpret \<chi>': cocone J.comp C D.map a' \<chi>'
            using \<chi>' by blast
          have 0: "seq (\<chi>' J.One) f"
            using J.ide_char J.arr_char \<chi>'.preserves_hom
            by (meson D.is_coequalized_by_cocone \<chi>')
          have 1: "\<exists>!h. h \<cdot> e = \<chi>' J.One"
            using assms 0 \<chi>' D.is_coequalized_by_cocone by blast
          obtain h where h: "h \<cdot> e = \<chi>' J.One"
            using 1 by blast
          have 2: "D.is_coequalized_by e"
            using assms(2-3) by blast
          have "\<exists>h. \<guillemotleft>h : cod e \<rightarrow> a'\<guillemotright> \<and> D.cocones_map h (D.mkCocone e) = \<chi>'"
          proof 
            show "\<guillemotleft>h : cod e \<rightarrow> a'\<guillemotright> \<and> D.cocones_map h (D.mkCocone e) = \<chi>'"
            proof
              show 3: "\<guillemotleft>h : cod e \<rightarrow> a'\<guillemotright>"
                using h \<chi>'.preserves_cod
                by (metis (no_types, lifting) \<chi>'.A.map_simp \<chi>'.preserves_reflects_arr
                    0 cod_comp seqE in_homI J.cod_simp(2))
              show "D.cocones_map h (D.mkCocone e) = \<chi>'"
              proof
                fix j
                have "D.cocone (dom h) (D.mkCocone e)"
                  using 2 3 D.cocone_mkCocone by auto
                thus "D.cocones_map h (D.mkCocone e) j = \<chi>' j"
                  using h 2 3 D.cocone_mkCocone [of e] J.arr_char D.mkCocone_def comp_assoc
                  apply (cases "J.arr j")
                   apply simp_all
                   apply (metis (no_types, lifting) D.mkCocone_cocone \<chi>')
                  using \<chi>'.extensionality
                  by presburger
              qed
            qed
          qed
          moreover have "\<And>h'. \<guillemotleft>h' : cod e \<rightarrow> a'\<guillemotright> \<and>
                              D.cocones_map h' (D.mkCocone e) = \<chi>' \<Longrightarrow> h' = h"
          proof (elim conjE)
            fix h'
            assume h': "\<guillemotleft>h' : cod e \<rightarrow> a'\<guillemotright>"
            assume eq: "D.cocones_map h' (D.mkCocone e) = \<chi>'"
            have "h' \<cdot> e = \<chi>' J.One"
              using 0 D.mkCocone_def \<chi>.cocone_axioms eq h' by fastforce
            moreover have "\<exists>!h. h \<cdot> e = \<chi>' J.One"
              using assms(2,4) 1 seqI by blast
            ultimately show "h' = h"
              using h by auto
          qed
          ultimately show "\<exists>!h. \<guillemotleft>h : cod e \<rightarrow> a'\<guillemotright> \<and> D.cocones_map h (D.mkCocone e) = \<chi>'"
            by blast
        qed
        show "D.has_as_coequalizer e"
          using assms \<chi>.colimit_cocone_axioms by blast
      qed
    qed

    lemma has_as_coequalizerE [elim]:
    assumes "has_as_coequalizer f g e"
    and "\<lbrakk>seq e f; e \<cdot> f = e \<cdot> g; \<And>e'. \<lbrakk>seq e' f; e' \<cdot> f = e' \<cdot> g\<rbrakk> \<Longrightarrow> \<exists>!h. h \<cdot> e = e'\<rbrakk> \<Longrightarrow> T"
    shows T
    proof -
      interpret D: parallel_pair_diagram C f g
        using assms has_as_coequalizer_def parallel_pair_diagram_axioms_def
        by (metis category_axioms parallel_pair_diagram_def)
      have "D.has_as_coequalizer e"
        using assms has_as_coequalizer_def by blast
      interpret coequalizer_cocone C f g e
        by (simp add: \<open>D.has_as_coequalizer e\<close> category_axioms coequalizer_cocone_def
            D.parallel_pair_diagram_axioms)
      show T
        by (metis (lifting) HOL.ext assms(2) cod_comp coequalizes in_homI is_couniversal' seqE)
    qed

  end

end

