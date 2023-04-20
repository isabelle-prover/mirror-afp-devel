(*  Title:       Subcategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Subcategory"

  text\<open>
    In this chapter we give a construction of the subcategory of a category
    defined by a predicate on arrows subject to closure conditions.  The arrows of
    the subcategory are directly identified with the arrows of the ambient category.
    We also define the related notions of full subcategory and inclusion functor.
\<close>

theory Subcategory
imports Functor
begin

  locale subcategory =
    C: category C
    for C :: "'a comp"      (infixr "\<cdot>\<^sub>C" 55)
    and Arr :: "'a \<Rightarrow> bool" +
    assumes inclusion: "Arr f \<Longrightarrow> C.arr f"
    and dom_closed: "Arr f \<Longrightarrow> Arr (C.dom f)"
    and cod_closed: "Arr f \<Longrightarrow> Arr (C.cod f)"
    and comp_closed: "\<lbrakk> Arr f; Arr g; C.cod f = C.dom g \<rbrakk> \<Longrightarrow> Arr (g \<cdot>\<^sub>C f)"
  begin

    no_notation C.in_hom    ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation C.in_hom       ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")

    definition comp         (infixr "\<cdot>" 55)
    where "g \<cdot> f = (if Arr f \<and> Arr g \<and> C.cod f = C.dom g then g \<cdot>\<^sub>C f else C.null)"

    interpretation partial_composition comp
    proof
      show "\<exists>!n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"
      proof
        show 1: "\<forall>f. C.null \<cdot> f = C.null \<and> f \<cdot> C.null = C.null"
          by (metis C.null_is_zero(1) C.ex_un_null comp_def)
        show "\<And>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n \<Longrightarrow> n = C.null"
          using 1 C.ex_un_null by metis
      qed
    qed

    lemma null_char [simp]:
    shows "null = C.null"
    proof -
      have "\<forall>f. C.null \<cdot> f = C.null \<and> f \<cdot> C.null = C.null"
        by (metis C.null_is_zero(1) C.ex_un_null comp_def)
      thus ?thesis using ex_un_null by (metis null_is_zero(2))
    qed

    lemma ideI\<^sub>S\<^sub>b\<^sub>C:
    assumes "Arr a" and "C.ide a"
    shows "ide a"
      unfolding ide_def
      using assms null_char C.ide_def comp_def by auto

    lemma Arr_iff_dom_in_domain:
    shows "Arr f \<longleftrightarrow> C.dom f \<in> domains f"
    proof
      show "C.dom f \<in> domains f \<Longrightarrow> Arr f"
        using domains_def comp_def ide_def by fastforce
      show "Arr f \<Longrightarrow> C.dom f \<in> domains f"
      proof -
        assume f: "Arr f"
        have "ide (C.dom f)"
          using f inclusion C.dom_in_domains C.has_domain_iff_arr C.domains_def
                dom_closed ideI\<^sub>S\<^sub>b\<^sub>C
          by auto
        moreover have "f \<cdot> C.dom f \<noteq> null"
          using f comp_def dom_closed null_char inclusion C.comp_arr_dom by force
        ultimately show ?thesis
          using domains_def by simp
      qed
    qed

    lemma Arr_iff_cod_in_codomain:
    shows "Arr f \<longleftrightarrow> C.cod f \<in> codomains f"
    proof
      show "C.cod f \<in> codomains f \<Longrightarrow> Arr f"
        using codomains_def comp_def ide_def by fastforce
      show "Arr f \<Longrightarrow> C.cod f \<in> codomains f"
      proof -
        assume f: "Arr f"
        have "ide (C.cod f)"
          using f inclusion C.cod_in_codomains C.has_codomain_iff_arr C.codomains_def
                cod_closed ideI\<^sub>S\<^sub>b\<^sub>C
          by auto
        moreover have "C.cod f \<cdot> f \<noteq> null"
          using f comp_def cod_closed null_char inclusion C.comp_cod_arr by force
        ultimately show ?thesis
          using codomains_def by simp
      qed
    qed

    lemma arr_char\<^sub>S\<^sub>b\<^sub>C:
    shows "arr f \<longleftrightarrow> Arr f"
    proof
      show "Arr f \<Longrightarrow> arr f"
        using arr_def comp_def Arr_iff_dom_in_domain Arr_iff_cod_in_codomain by auto
      show "arr f \<Longrightarrow> Arr f"
      proof -
        assume f: "arr f"
        obtain a where a: "a \<in> domains f \<or> a \<in> codomains f"
          using f arr_def by auto
        have "f \<cdot> a \<noteq> C.null \<or> a \<cdot> f \<noteq> C.null"
          using a domains_def codomains_def null_char by auto
        thus "Arr f"
          using comp_def by metis
      qed
    qed

    lemma arrI\<^sub>S\<^sub>b\<^sub>C [intro]:
    assumes "Arr f"
    shows "arr f"
      using assms arr_char\<^sub>S\<^sub>b\<^sub>C by simp

    lemma arrE [elim]:
    assumes "arr f"
    shows "Arr f"
      using assms arr_char\<^sub>S\<^sub>b\<^sub>C by simp

    interpretation category comp
    proof
      show 1: "\<And>g f. g \<cdot> f \<noteq> null \<Longrightarrow> seq g f"
        using comp_closed comp_def by fastforce
      show "\<And>f. (domains f \<noteq> {}) = (codomains f \<noteq> {})"
        using Arr_iff_cod_in_codomain Arr_iff_dom_in_domain arrE arr_def codomains_def by blast
      show "\<And>h g f. \<lbrakk>seq h g; seq (h \<cdot> g) f\<rbrakk> \<Longrightarrow> seq g f"
        by (metis (full_types) 1 C.dom_comp C.match_1 C.not_arr_null arrE inclusion comp_def)
      show "\<And>h g f. \<lbrakk>seq h (g \<cdot> f); seq g f\<rbrakk> \<Longrightarrow> seq h g"
        by (metis (full_types) 1 C.cod_comp C.match_2 C.not_arr_null arrE inclusion comp_def)
      show 2: "\<And>g f h. \<lbrakk>seq g f; seq h g\<rbrakk> \<Longrightarrow> seq (h \<cdot> g) f"
        by (metis (full_types) 1 C.dom_comp C.not_arr_null C.seqI arrE inclusion comp_def)
      show "\<And>g f h. \<lbrakk>seq g f; seq h g\<rbrakk> \<Longrightarrow> (h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
        by (metis 2 C.comp_assoc C.not_arr_null arrE C.cod_comp inclusion comp_def)
    qed

    theorem is_category:
    shows "category comp" ..

    notation in_hom     ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma dom_simp:
    assumes "arr f"
    shows "dom f = C.dom f"
      by (metis Arr_iff_dom_in_domain arrE assms dom_eqI')

    lemma dom_char\<^sub>S\<^sub>b\<^sub>C:
    shows "dom f = (if arr f then C.dom f else C.null)"
      using dom_simp dom_def arr_def arr_char\<^sub>S\<^sub>b\<^sub>C by auto

    lemma cod_simp:
    assumes "arr f"
    shows "cod f = C.cod f"
      by (metis Arr_iff_cod_in_codomain arrE assms cod_eqI')

    lemma cod_char\<^sub>S\<^sub>b\<^sub>C:
    shows "cod f = (if arr f then C.cod f else C.null)"
      using cod_simp cod_def arr_def by auto

    lemma in_hom_char\<^sub>S\<^sub>b\<^sub>C:
    shows "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<longleftrightarrow> arr a \<and> arr b \<and> arr f \<and> \<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright>"
      using inclusion arr_char\<^sub>S\<^sub>b\<^sub>C cod_closed dom_closed
      by (metis C.arr_iff_in_hom C.in_homE arr_iff_in_hom cod_simp dom_simp in_homE)

    lemma ide_char\<^sub>S\<^sub>b\<^sub>C:
    shows "ide a \<longleftrightarrow> arr a \<and> C.ide a"
      using ide_in_hom C.ide_in_hom in_hom_char\<^sub>S\<^sub>b\<^sub>C by simp

    lemma seq_char\<^sub>S\<^sub>b\<^sub>C:
    shows "seq g f \<longleftrightarrow> arr f \<and> arr g \<and> C.seq g f"
    proof
      show "arr f \<and> arr g \<and> C.seq g f \<Longrightarrow> seq g f"
        using arr_char\<^sub>S\<^sub>b\<^sub>C dom_char\<^sub>S\<^sub>b\<^sub>C cod_char\<^sub>S\<^sub>b\<^sub>C by (intro seqI, auto)
      show "seq g f \<Longrightarrow> arr f \<and> arr g \<and> C.seq g f"
        apply (elim seqE, auto)
        using inclusion arr_char\<^sub>S\<^sub>b\<^sub>C dom_simp cod_simp by auto
    qed

    lemma hom_char:
    shows "hom a b = C.hom a b \<inter> Collect Arr"
    proof
      show "hom a b \<subseteq> C.hom a b \<inter> Collect Arr"
        using in_hom_char\<^sub>S\<^sub>b\<^sub>C by auto
      show "C.hom a b \<inter> Collect Arr \<subseteq> hom a b"
        using arr_char\<^sub>S\<^sub>b\<^sub>C dom_char\<^sub>S\<^sub>b\<^sub>C cod_char\<^sub>S\<^sub>b\<^sub>C by force
    qed

    lemma comp_char:
    shows "g \<cdot> f = (if arr f \<and> arr g \<and> C.seq g f then g \<cdot>\<^sub>C f else C.null)"
      using arr_char\<^sub>S\<^sub>b\<^sub>C comp_def comp_closed C.ext by force

    lemma comp_simp:
    assumes "seq g f"
    shows "g \<cdot> f = g \<cdot>\<^sub>C f"
      using assms comp_char seq_char\<^sub>S\<^sub>b\<^sub>C by metis

    lemma inclusion_preserves_inverse:
    assumes "inverse_arrows f g"
    shows "C.inverse_arrows f g"
      using assms ide_char\<^sub>S\<^sub>b\<^sub>C comp_simp arr_char\<^sub>S\<^sub>b\<^sub>C
      by (intro C.inverse_arrowsI, auto)

    lemma iso_char\<^sub>S\<^sub>b\<^sub>C:
    shows "iso f \<longleftrightarrow> C.iso f \<and> arr f \<and> arr (C.inv f)"
      by (metis C.category_axioms C.cod_inv C.comp_arr_inv' C.comp_inv_arr' C.dom_inv arr_inv
          category.inverse_unique category.isoI category.seqI cod_simp comp_simp dom_simp
          ide_cod inverse_arrowsI is_category iso_is_arr iso_def inclusion_preserves_inverse)

    lemma inv_char\<^sub>S\<^sub>b\<^sub>C:
    assumes "iso f"
    shows "inv f = C.inv f"
      by (metis assms C.inverse_unique inclusion_preserves_inverse isoE inverse_unique)

    lemma inverse_arrows_char\<^sub>S\<^sub>b\<^sub>C:
    shows "inverse_arrows f g \<longleftrightarrow> seq f g \<and> C.inverse_arrows f g"
      by (metis C.inverse_arrows_def comp_simp ide_char\<^sub>S\<^sub>b\<^sub>C ide_compE inverse_arrows_def)

  end

  sublocale subcategory \<subseteq> category comp
    using is_category by auto

  section "Full Subcategory"

  locale full_subcategory =
    C: category C
    for C :: "'a comp"
    and Ide :: "'a \<Rightarrow> bool" +
    assumes inclusion\<^sub>F\<^sub>S\<^sub>b\<^sub>C: "Ide f \<Longrightarrow> C.ide f"
  begin

    sublocale subcategory C "\<lambda>f. C.arr f \<and> Ide (C.dom f) \<and> Ide (C.cod f)"
      by (unfold_locales; simp)

    lemma is_subcategory:
    shows "subcategory C (\<lambda>f. C.arr f \<and> Ide (C.dom f) \<and> Ide (C.cod f))"
      ..

    lemma in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C:
    shows "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<longleftrightarrow> arr a \<and> arr b \<and> \<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright>"
      using arr_char\<^sub>S\<^sub>b\<^sub>C in_hom_char\<^sub>S\<^sub>b\<^sub>C by auto

    text \<open>
      Isomorphisms in a full subcategory are inherited from the ambient category.
\<close>

    lemma iso_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C:
    shows "iso f \<longleftrightarrow> arr f \<and> C.iso f"
      using arr_char\<^sub>S\<^sub>b\<^sub>C iso_char\<^sub>S\<^sub>b\<^sub>C by force

  end

  section "Inclusion Functor"

  text \<open>
    If \<open>S\<close> is a subcategory of \<open>C\<close>, then there is an inclusion functor
    from \<open>S\<close> to \<open>C\<close>.  Inclusion functors are faithful embeddings.
\<close>

  locale inclusion_functor =
    C: category C +
    S: subcategory C Arr
  for C :: "'a comp"
  and Arr :: "'a \<Rightarrow> bool"
  begin

    interpretation "functor" S.comp C S.map
      using S.map_def S.arr_char\<^sub>S\<^sub>b\<^sub>C S.inclusion S.dom_char\<^sub>S\<^sub>b\<^sub>C S.cod_char\<^sub>S\<^sub>b\<^sub>C
            S.dom_closed S.cod_closed S.comp_closed S.arr_char\<^sub>S\<^sub>b\<^sub>C S.comp_char
      apply unfold_locales
          apply auto[4]
      by (elim S.seqE, auto)

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

  text \<open>
    The inclusion of a full subcategory is a special case.
    Such functors are fully faithful.
\<close>

  locale full_inclusion_functor =
    C: category C +
    S: full_subcategory C Ide
  for C :: "'a comp"
  and Ide :: "'a \<Rightarrow> bool"
  begin

    sublocale inclusion_functor C \<open>\<lambda>f. C.arr f \<and> Ide (C.dom f) \<and> Ide (C.cod f)\<close> ..

    lemma is_inclusion_functor:
    shows "inclusion_functor C (\<lambda>f. C.arr f \<and> Ide (C.dom f) \<and> Ide (C.cod f))"
      ..

    interpretation full_functor S.comp C S.map
      apply unfold_locales
      using S.ide_in_hom
      by (metis (no_types, lifting) C.in_homE S.arr_char\<^sub>S\<^sub>b\<^sub>C S.in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C S.map_simp)

    lemma is_full_functor:
    shows "full_functor S.comp C S.map" ..

    sublocale full_functor S.comp C S.map
      using is_full_functor by auto
    sublocale fully_faithful_functor S.comp C S.map ..

  end

end
