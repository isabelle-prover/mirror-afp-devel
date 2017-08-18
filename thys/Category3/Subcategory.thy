(*  Title:       Subcategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Subcategory"

  text{*
    In this chapter we give a construction of the subcategory of a category
    defined by a predicate on arrows subject to closure conditions.  The arrows of
    the subcategory are directly identified with the arrows of the ambient category.
    We also define the related notions of full subcategory and inclusion functor.
  *}

theory Subcategory
imports Functor
begin

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
       using has_dom_char has_cod_char by presburger
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

  section "Full Subcategory"

  locale full_subcategory =
    C: category C
    for C :: "'a comp"
    and Ide :: "'a \<Rightarrow> bool" +
    assumes Ide_implies_Ide: "Ide f \<Longrightarrow> C.ide f"

  sublocale full_subcategory \<subseteq> subcategory C "\<lambda>f. C.arr f \<and> Ide (C.dom f) \<and> Ide (C.cod f)"
      by (unfold_locales; simp)

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
        have "antipar f g" using f g by auto
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

end
