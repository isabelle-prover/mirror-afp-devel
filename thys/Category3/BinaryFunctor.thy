(*  Title:       BinaryFunctor
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter BinaryFunctor

theory BinaryFunctor
imports ProductCategory NaturalTransformation
begin

  text\<open>
    This theory develops various properties of binary functors, which are functors
    defined on product categories.
\<close>

  locale binary_functor =
    A1: category A1 +
    A2: category A2 +
    B: category B +
    A1xA2: product_category A1 A2 +
    "functor" A1xA2.comp B F
  for A1 :: "'a1 comp"     (infixr \<open>\<cdot>\<^sub>A\<^sub>1\<close> 55)
  and A2 :: "'a2 comp"     (infixr \<open>\<cdot>\<^sub>A\<^sub>2\<close> 55)
  and B :: "'b comp"       (infixr \<open>\<cdot>\<^sub>B\<close> 55)
  and F :: "'a1 * 'a2 \<Rightarrow> 'b"
  begin

    notation A1.in_hom     (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>1 _\<guillemotright>\<close>)
    notation A2.in_hom     (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>2 _\<guillemotright>\<close>)

  end

  text\<open>
    A product functor is a binary functor obtained by placing two functors in parallel.
\<close>

  locale product_functor =
    A1: category A1 +
    A2: category A2 +
    B1: category B1 +
    B2: category B2 +
    F1: "functor" A1 B1 F1 +
    F2: "functor" A2 B2 F2 +
    A1xA2: product_category A1 A2 +
    B1xB2: product_category B1 B2
  for A1 :: "'a1 comp"     (infixr \<open>\<cdot>\<^sub>A\<^sub>1\<close> 55)
  and A2 :: "'a2 comp"     (infixr \<open>\<cdot>\<^sub>A\<^sub>2\<close> 55)
  and B1 :: "'b1 comp"     (infixr \<open>\<cdot>\<^sub>B\<^sub>1\<close> 55)
  and B2 :: "'b2 comp"     (infixr \<open>\<cdot>\<^sub>B\<^sub>2\<close> 55)
  and F1 :: "'a1 \<Rightarrow> 'b1"
  and F2 :: "'a2 \<Rightarrow> 'b2"
  begin

    notation A1xA2.comp    (infixr \<open>\<cdot>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2\<close> 55)
    notation B1xB2.comp    (infixr \<open>\<cdot>\<^sub>B\<^sub>1\<^sub>x\<^sub>B\<^sub>2\<close> 55)
    notation A1.in_hom     (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>1 _\<guillemotright>\<close>)
    notation A2.in_hom     (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>2 _\<guillemotright>\<close>)
    notation B1.in_hom     (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>B\<^sub>1 _\<guillemotright>\<close>)
    notation B2.in_hom     (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>B\<^sub>2 _\<guillemotright>\<close>)
    notation A1xA2.in_hom  (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2 _\<guillemotright>\<close>)
    notation B1xB2.in_hom  (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>B\<^sub>1\<^sub>x\<^sub>B\<^sub>2 _\<guillemotright>\<close>)

    definition map
    where "map f = (if A1.arr (fst f) \<and> A2.arr (snd f)
                    then (F1 (fst f), F2 (snd f)) else (F1 A1.null, F2 A2.null))"

    lemma map_simp [simp]:
    assumes "A1xA2.arr f"
    shows "map f = (F1 (fst f), F2 (snd f))"
      using assms map_def by simp

    lemma is_functor:
    shows "functor A1xA2.comp B1xB2.comp map"
      using B1xB2.dom_char B1xB2.cod_char F1.extensionality F2.extensionality
      apply (unfold_locales)
      using map_def A1.arr_dom_iff_arr A1.arr_cod_iff_arr A2.arr_dom_iff_arr A2.arr_cod_iff_arr
          apply auto[4]
      using A1xA2.seqE map_simp by fastforce

  end

  sublocale product_functor \<subseteq> "functor" A1xA2.comp B1xB2.comp map
    using is_functor by auto
  sublocale product_functor \<subseteq> binary_functor A1 A2 B1xB2.comp map ..

  text\<open>
    The following locale is concerned with a binary functor from a category to itself.
    It defines related functors that are useful when considering monoidal structure on a
    category.
\<close>

  locale binary_endofunctor =
    C: category C +
    CC: product_category C C +
    CCC: product_category C CC.comp +
    binary_functor C C C T
  for C :: "'a comp"      (infixr \<open>\<cdot>\<close> 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  begin

    definition ToTC
    where "ToTC f \<equiv> if CCC.arr f then T (T (fst f, fst (snd f)), snd (snd f)) else C.null"

    lemma functor_ToTC:
    shows "functor CCC.comp C ToTC"
      using ToTC_def apply unfold_locales
          apply auto[4]
    proof -
      fix f g
      assume gf: "CCC.seq g f"
      show "ToTC (CCC.comp g f) = ToTC g \<cdot> ToTC f"
        using gf unfolding CCC.seq_char CC.seq_char ToTC_def
        apply auto
        by (metis CC.comp_simp CC.seqI\<^sub>P\<^sub>C fst_conv preserves_comp preserves_seq snd_conv)
    qed

    lemma ToTC_simp [simp]:
    assumes "C.arr f" and "C.arr g" and "C.arr h"
    shows "ToTC (f, g, h) = T (T (f, g), h)"
      using assms ToTC_def CCC.arr_char by simp

    definition ToCT
    where "ToCT f \<equiv> if CCC.arr f then T (fst f, T (fst (snd f), snd (snd f))) else C.null"

    lemma functor_ToCT:
    shows "functor CCC.comp C ToCT"
      using ToCT_def apply unfold_locales
        apply auto[4]
    proof -
      fix f g
      assume gf: "CCC.seq g f"
      show "ToCT (CCC.comp g f) = ToCT g \<cdot> ToCT f"
        using gf unfolding CCC.seq_char CC.seq_char ToCT_def
        apply auto
        by (metis CC.comp_simp CC.seq_char as_nat_trans.preserves_comp_2 fst_conv
                  preserves_reflects_arr snd_conv)
    qed

    lemma ToCT_simp [simp]:
    assumes "C.arr f" and "C.arr g" and "C.arr h"
    shows "ToCT (f, g, h) = T (f, T (g, h))"
      using assms ToCT_def CCC.arr_char by simp

  end

  text\<open>
    A symmetry functor is a binary functor that exchanges its two arguments.
\<close>

  locale symmetry_functor =
  A1: category A1 +
  A2: category A2 +
  A1xA2: product_category A1 A2 +
  A2xA1: product_category A2 A1
  for A1 :: "'a1 comp"     (infixr \<open>\<cdot>\<^sub>A\<^sub>1\<close> 55)
  and A2 :: "'a2 comp"     (infixr \<open>\<cdot>\<^sub>A\<^sub>2\<close> 55)
  begin

    notation A1xA2.comp    (infixr \<open>\<cdot>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2\<close> 55)
    notation A2xA1.comp    (infixr \<open>\<cdot>\<^sub>A\<^sub>2\<^sub>x\<^sub>A\<^sub>1\<close> 55)
    notation A1xA2.in_hom  (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2 _\<guillemotright>\<close>)
    notation A2xA1.in_hom  (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>2\<^sub>x\<^sub>A\<^sub>1 _\<guillemotright>\<close>)

    definition map :: "'a1 * 'a2 \<Rightarrow> 'a2 * 'a1"
    where "map f = (if A1xA2.arr f then (snd f, fst f) else A2xA1.null)"

    lemma map_simp [simp]:
    assumes "A1xA2.arr f"
    shows "map f = (snd f, fst f)"
      using assms map_def by meson

    lemma is_functor:
    shows "functor A1xA2.comp A2xA1.comp map"
      using map_def A1.arr_dom_iff_arr A1.arr_cod_iff_arr A2.arr_dom_iff_arr A2.arr_cod_iff_arr
      apply (unfold_locales)
          apply auto[4]
      by force

  end

  sublocale symmetry_functor \<subseteq> "functor" A1xA2.comp A2xA1.comp map
    using is_functor by auto
  sublocale symmetry_functor \<subseteq> binary_functor A1 A2 A2xA1.comp map ..

  context binary_functor
  begin

    abbreviation sym
    where "sym \<equiv> (\<lambda>f. F (snd f, fst f))"

    lemma sym_is_binary_functor:
    shows "binary_functor A2 A1 B sym"
    proof -
      interpret A2xA1: product_category A2 A1 ..
      interpret S: symmetry_functor A2 A1 ..
      interpret SF: composite_functor A2xA1.comp A1xA2.comp B S.map F ..
      have "binary_functor A2 A1 B (F o S.map)" ..
      moreover have "F o S.map = (\<lambda>f. F (snd f, fst f))"
        using extensionality SF.extensionality S.map_def by fastforce
      ultimately show ?thesis using sym_def by auto
    qed

    text\<open>
      Fixing one or the other argument of a binary functor to be an identity
      yields a functor of the other argument.
\<close>

    lemma fixing_ide_gives_functor_1:
    assumes "A1.ide a1"
    shows "functor A2 B (\<lambda>f2. F (a1, f2))"
      using assms
      apply unfold_locales
      using extensionality
          apply auto[4]
      by (metis A1.ideD(1) A1.comp_ide_self A1xA2.comp_simp A1xA2.seq_char fst_conv
          as_nat_trans.preserves_comp_2 snd_conv)

    lemma fixing_ide_gives_functor_2:
    assumes "A2.ide a2"
    shows "functor A1 B (\<lambda>f1. F (f1, a2))"
      using assms
      apply (unfold_locales)
      using extensionality
          apply auto[4]
      by (metis A1xA2.comp_simp A1xA2.seq_char A2.ideD(1) A2.comp_ide_self fst_conv
          as_nat_trans.preserves_comp_2 snd_conv)

    text\<open>
      Fixing one or the other argument of a binary functor to be an arrow
      yields a natural transformation.
\<close>

    lemma fixing_arr_gives_natural_transformation_1:
    assumes "A1.arr f1"
    shows "natural_transformation A2 B (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. F (A1.cod f1, f2))
                                       (\<lambda>f2. F (f1, f2))"
    proof -
      let ?Fdom = "\<lambda>f2. F (A1.dom f1, f2)"
      interpret Fdom: "functor" A2 B ?Fdom using assms fixing_ide_gives_functor_1 by auto
      let ?Fcod = "\<lambda>f2. F (A1.cod f1, f2)"
      interpret Fcod: "functor" A2 B ?Fcod using assms fixing_ide_gives_functor_1 by auto
      let ?\<tau> = "\<lambda>f2. F (f1, f2)"
      show "natural_transformation A2 B ?Fdom ?Fcod ?\<tau>"
        using assms
        apply unfold_locales
        using extensionality
            apply auto[3]
        using A1xA2.arr_char preserves_comp A1.comp_cod_arr A1xA2.comp_char A2.comp_arr_dom
         apply (metis fst_conv snd_conv)
        using A1xA2.arr_char preserves_comp A2.comp_cod_arr A1xA2.comp_char A1.comp_arr_dom
        by (metis fst_conv snd_conv)
    qed

    lemma fixing_arr_gives_natural_transformation_2:
    assumes "A2.arr f2"
    shows "natural_transformation A1 B (\<lambda>f1. F (f1, A2.dom f2)) (\<lambda>f1. F (f1, A2.cod f2))
                                       (\<lambda>f1. F (f1, f2))"
    proof -
      interpret F': binary_functor A2 A1 B sym
        using assms(1) sym_is_binary_functor by auto
      have "natural_transformation A1 B (\<lambda>f1. sym (A2.dom f2, f1)) (\<lambda>f1. sym (A2.cod f2, f1))
                                        (\<lambda>f1. sym (f2, f1))"
        using assms F'.fixing_arr_gives_natural_transformation_1 by fast
      thus ?thesis by simp
    qed

    text\<open>
      Fixing one or the other argument of a binary functor to be a composite arrow
      yields a natural transformation that is a vertical composite.
\<close>

    lemma preserves_comp_1:
    assumes "A1.seq f1' f1"
    shows "(\<lambda>f2. F (f1' \<cdot>\<^sub>A\<^sub>1 f1, f2)) =
                 vertical_composite.map A2 B (\<lambda>f2. F (f1, f2)) (\<lambda>f2. F (f1', f2))"
    proof -
      interpret \<tau>: natural_transformation A2 B
                     \<open>\<lambda>f2. F (A1.dom f1, f2)\<close> \<open>\<lambda>f2. F (A1.cod f1, f2)\<close> \<open>\<lambda>f2. F (f1, f2)\<close>
        using assms fixing_arr_gives_natural_transformation_1 by blast
      interpret \<tau>': natural_transformation A2 B
                     \<open>\<lambda>f2. F (A1.cod f1, f2)\<close> \<open>\<lambda>f2. F (A1.cod f1', f2)\<close> \<open>\<lambda>f2. F (f1', f2)\<close>
        using assms fixing_arr_gives_natural_transformation_1 A1.seqE by metis
      interpret \<tau>'o\<tau>: vertical_composite A2 B
                        \<open>\<lambda>f2. F (A1.dom f1, f2)\<close> \<open>\<lambda>f2. F (A1.cod f1, f2)\<close> \<open>\<lambda>f2. F (A1.cod f1', f2)\<close>
                        \<open>\<lambda>f2. F (f1, f2)\<close> \<open>\<lambda>f2. F (f1', f2)\<close> ..
      show "(\<lambda>f2. F (f1' \<cdot>\<^sub>A\<^sub>1 f1, f2)) = \<tau>'o\<tau>.map"
      proof
        fix f2
        have "\<not>A2.arr f2 \<Longrightarrow> F (f1' \<cdot>\<^sub>A\<^sub>1 f1, f2) = \<tau>'o\<tau>.map f2"
          using \<tau>'o\<tau>.extensionality extensionality by simp
        moreover have "A2.arr f2 \<Longrightarrow> F (f1' \<cdot>\<^sub>A\<^sub>1 f1, f2) = \<tau>'o\<tau>.map f2"
          using \<tau>'o\<tau>.map_simp_1 assms fixing_arr_gives_natural_transformation_2
                natural_transformation.preserves_comp_1
          by fastforce
        ultimately show "F (f1' \<cdot>\<^sub>A\<^sub>1 f1, f2) = \<tau>'o\<tau>.map f2" by blast
      qed
    qed

    lemma preserves_comp_2:
    assumes "A2.seq f2' f2"
    shows "(\<lambda>f1. F (f1, f2' \<cdot>\<^sub>A\<^sub>2 f2)) =
                 vertical_composite.map A1 B (\<lambda>f1. F (f1, f2)) (\<lambda>f1. F (f1, f2'))"
    proof -
      interpret F': binary_functor A2 A1 B sym
        using assms(1) sym_is_binary_functor by auto
      have "(\<lambda>f1. sym (f2' \<cdot>\<^sub>A\<^sub>2 f2, f1)) =
                 vertical_composite.map A1 B (\<lambda>f1. sym (f2, f1)) (\<lambda>f1. sym (f2', f1))"
        using assms F'.preserves_comp_1 by fastforce
      thus ?thesis by simp
    qed

  end

  text\<open>
    A binary functor transformation is a natural transformation between binary functors.
    We need a certain property of such transformations; namely, that if one or the
    other argument is fixed to be an identity, the result is a natural transformation.
\<close>

  locale binary_functor_transformation =
    A1: category A1 +
    A2: category A2 +
    B: category B +
    A1xA2: product_category A1 A2 +
    F: binary_functor A1 A2 B F +
    G: binary_functor A1 A2 B G +
    natural_transformation A1xA2.comp B F G \<tau>
  for A1 :: "'a1 comp"     (infixr \<open>\<cdot>\<^sub>A\<^sub>1\<close> 55)
  and A2 :: "'a2 comp"     (infixr \<open>\<cdot>\<^sub>A\<^sub>2\<close> 55)
  and B :: "'b comp"       (infixr \<open>\<cdot>\<^sub>B\<close> 55)
  and F :: "'a1 * 'a2 \<Rightarrow> 'b"
  and G :: "'a1 * 'a2 \<Rightarrow> 'b"
  and \<tau> :: "'a1 * 'a2 \<Rightarrow> 'b"
  begin

    notation A1xA2.comp    (infixr \<open>\<cdot>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2\<close> 55)
    notation A1xA2.in_hom  (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2 _\<guillemotright>\<close>)

    lemma fixing_ide_gives_natural_transformation_1:
    assumes "A1.ide a1"
    shows "natural_transformation A2 B (\<lambda>f2. F (a1, f2)) (\<lambda>f2. G (a1, f2)) (\<lambda>f2. \<tau> (a1, f2))"
    proof -
      interpret Fa1: "functor" A2 B \<open>\<lambda>f2. F (a1, f2)\<close>
        using assms F.fixing_ide_gives_functor_1 by simp
      interpret Ga1: "functor" A2 B \<open>\<lambda>f2. G (a1, f2)\<close>
        using assms "G.fixing_ide_gives_functor_1" by simp
      show ?thesis
        using assms extensionality naturality1 naturality2
        apply (unfold_locales, auto)
         apply (metis A1.ide_char)
        by (metis A1.ide_char)
    qed

    lemma fixing_ide_gives_natural_transformation_2:
    assumes "A2.ide a2"
    shows "natural_transformation A1 B (\<lambda>f1. F (f1, a2)) (\<lambda>f1. G (f1, a2)) (\<lambda>f1. \<tau> (f1, a2))"
    proof -
      interpret Fa2: "functor" A1 B \<open>\<lambda>f1. F (f1, a2)\<close>
        using assms F.fixing_ide_gives_functor_2 by simp
      interpret Ga2: "functor" A1 B \<open>\<lambda>f1. G (f1, a2)\<close>
        using assms "G.fixing_ide_gives_functor_2" by simp
      show ?thesis
        using assms extensionality naturality1 naturality2
        apply (unfold_locales, auto)
         apply (metis A2.ide_char)
        by (metis A2.ide_char)
    qed

  end

end
