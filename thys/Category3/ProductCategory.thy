(*  Title:       ProductCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter ProductCategory

theory ProductCategory
imports Category
begin

  text{*
    This theory defines the product of two categories @{term C1} and @{term C2},
    which is the category @{term C} whose arrows are ordered pairs consisting of an
    arrow of @{term C1} and an arrow of @{term C2}, with composition defined
    componentwise.  As the ordered pair @{text "(C1.null, C2.null)"} is available
    to serve as @{text "C.null"}, we may directly identify the arrows of the product
    category @{term C} with ordered pairs, leaving the type of arrows of @{term C}
    transparent.
  *}

  type_synonym ('a1, 'a2) arr = "'a1 * 'a2"

  locale product_category =
    C1: category C1 +
    C2: category C2
  for C1 :: "'a1 comp"
  and C2 :: "'a2 comp"
  begin

    abbreviation Null :: "('a1, 'a2) arr"
    where "Null \<equiv> (C1.null, C2.null)"

    abbreviation Arr :: "('a1, 'a2) arr \<Rightarrow> bool"
    where "Arr f \<equiv> C1.arr (fst f) \<and> C2.arr (snd f)"

    abbreviation Ide :: "('a1, 'a2) arr \<Rightarrow> bool"
    where "Ide f \<equiv> C1.ide (fst f) \<and> C2.ide (snd f)"

    abbreviation Dom :: "('a1, 'a2) arr \<Rightarrow> ('a1, 'a2) arr"
    where "Dom f \<equiv> (if Arr f then (C1.dom (fst f), C2.dom (snd f)) else Null)"

    abbreviation Cod :: "('a1, 'a2) arr \<Rightarrow> ('a1, 'a2) arr"
    where "Cod f \<equiv> (if Arr f then (C1.cod (fst f), C2.cod (snd f)) else Null)"

    definition comp :: "('a1, 'a2) arr \<Rightarrow> ('a1, 'a2) arr \<Rightarrow> ('a1, 'a2) arr"
    where "comp g f = (if Arr f \<and> Arr g \<and> Cod f = Dom g then
                         (C1 (fst g) (fst f), C2 (snd g) (snd f))
                       else Null)"

    lemma not_Arr_Null:
    shows "\<not>Arr Null"
      by (simp add: C2.not_arr_null)

    interpretation partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. comp n f = n \<and> comp f n = n"
      proof
        let ?P = "\<lambda>n. \<forall>f. comp n f = n \<and> comp f n = n"
        show 1: "?P Null" using comp_def not_Arr_Null by metis
        thus "\<And>n. \<forall>f. comp n f = n \<and> comp f n = n \<Longrightarrow> n = Null" by metis
      qed
    qed

    lemma null_char [simp]:
    shows "null = Null"
    proof -
      let ?P = "\<lambda>n. \<forall>f. comp n f = n \<and> comp f n = n"
      have "?P Null" using comp_def not_Arr_Null by metis
      thus ?thesis
        unfolding null_def using the1_equality [of ?P Null] ex_un_null by blast
    qed

    lemma unit_Ide:
    assumes "Ide a"
    shows "unit a"
    proof (unfold unit_def)
      have "\<And>f. comp f a \<noteq> null \<Longrightarrow> comp f a = f"
        using assms comp_def null_char
        by (metis (no_types, lifting) C1.comp_arr_dom C1.ide_def C2.comp_arr_dom C2.ide_def
            fst_conv snd_conv surjective_pairing)
      moreover have "\<And>f. comp a f \<noteq> null \<Longrightarrow> comp a f = f"
        using assms comp_def null_char by auto
      ultimately show "\<forall>f. (comp a f \<noteq> null \<longrightarrow> comp a f = f)
                             \<and> (comp f a \<noteq> null \<longrightarrow> comp f a = f)"
        by auto
    qed

    lemma has_dom_char:
    shows "has_dom f \<longleftrightarrow> Arr f"
    proof
      assume f: "has_dom f"
      show "Arr f"
      proof -
        from f obtain a where A: "unit a \<and> comp f a \<noteq> null" using has_dom_def by blast
        thus ?thesis using comp_def null_char by metis
      qed
      next
      assume f: "Arr f"
      show "has_dom f"
      proof -
        have "unit (Dom f) \<and> comp f (Dom f) \<noteq> null"
          using f C1.not_arr_null comp_def null_char unit_Ide by auto
        thus ?thesis using has_dom_def by blast
      qed
    qed

    lemma has_cod_char:
    shows "has_cod f \<longleftrightarrow> Arr f"
    proof
      assume f: "has_cod f"
      show "Arr f"
      proof -
        from f obtain a where A: "unit a \<and> comp a f \<noteq> null" using has_cod_def by blast
        thus ?thesis using comp_def null_char by metis
      qed
      next
      assume f: "Arr f"
      show "has_cod f"
      proof -
        have "unit (Cod f) \<and> comp (Cod f) f \<noteq> null"
          using f C1.not_arr_null comp_def null_char unit_Ide by auto
        thus ?thesis using has_cod_def by blast
      qed
    qed

    theorem is_category:
    shows "category comp"
      using comp_def
      apply unfold_locales
      (* 6 *) apply (metis (no_types, lifting) C1.arr_comp C1.dom_comp C1.not_arr_null
                     C2.dom_comp fst_conv null_char snd_conv)
      (* 5 *) apply (metis (no_types, lifting) C1.arr_comp C1.cod_comp C1.not_arr_null
                     C2.cod_comp fst_conv null_char snd_conv)
      proof -
        fix f g h
        assume gf: "comp g f \<noteq> null" and hg: "comp h g \<noteq> null"
        have f: "Arr f" using gf null_char comp_def by metis
        have g: "Arr g" using gf null_char comp_def by metis
        have h: "Arr h" using hg null_char comp_def by metis
        have 1: "Cod f = Dom g" using gf null_char comp_def by metis
        have 2: "Cod g = Dom h" using hg null_char comp_def by metis
        show "comp (comp h g) f \<noteq> null"
        proof -
          have "Arr (comp h g)" using h g 2 comp_def null_char by simp
          moreover have "Dom (comp h g) = Dom g" using h g 2 comp_def null_char by simp
          ultimately show ?thesis using f 1 2 comp_def [of "comp h g" f] null_char
            by (metis C1.arr_comp C1.not_arr_null fst_conv)
        qed
        show "comp h (comp g f) \<noteq> null"
        proof -
          have "Arr (comp g f)" using g f 1 comp_def null_char by simp
          moreover have "Cod (comp g f) = Cod g" using g f 1 comp_def null_char by simp
          ultimately show ?thesis using h 1 2 comp_def [of h "comp g f"] null_char
            using C1.arr_comp C1.not_arr_null fst_conv by fastforce
        qed
        show "comp h (comp g f) = comp (comp h g) f"
          using f g h 1 2 comp_def by simp
        next
        fix f
        show "has_dom f = has_cod f"
          using has_dom_char has_cod_char by blast
      qed

  end

  sublocale product_category \<subseteq> category comp
    using is_category comp_def by auto

  context product_category
  begin

    lemma arr_char [iff]:
    shows "arr f \<longleftrightarrow> Arr f"
      using has_dom_char has_cod_char arr_def by simp

    lemma dom_char:
    shows "dom f = Dom f"
    proof (cases "Arr f")
      show "\<not>Arr f \<Longrightarrow> dom f = Dom f"
        unfolding dom_def using has_dom_char by auto
      show "Arr f \<Longrightarrow> dom f = Dom f"
      proof -
        assume f: "Arr f"
        have "unit (C1.dom (fst f), C2.dom (snd f))"
          by (simp add: f unit_Ide)
        moreover have "comp f (C1.dom (fst f), C2.dom (snd f)) \<noteq> null"
          using f comp_def has_codD(1) has_cod_char not_arr_null by auto
        ultimately show "dom f = Dom f"
          by (simp add: f dom_simp)
      qed
    qed

    lemma dom_simp [simp]:
    assumes "arr f"
    shows "dom f = (C1.dom (fst f), C2.dom (snd f))"
      using assms dom_char by auto

    lemma cod_char:
    shows "cod f = Cod f"
    proof (cases "Arr f")
      show "\<not>Arr f \<Longrightarrow> cod f = Cod f"
        unfolding cod_def using has_cod_char by auto
      show "Arr f \<Longrightarrow> cod f = Cod f"
      proof -
        assume f: "Arr f"
        have "unit (C1.cod (fst f), C2.cod (snd f))"
          by (simp add: f unit_Ide)
        moreover have "comp (C1.cod (fst f), C2.cod (snd f)) f \<noteq> null"
          using f comp_def has_codD(1) has_cod_char not_arr_null by auto
        ultimately show "cod f = Cod f"
          by (simp add: f cod_simp)
      qed
    qed

    lemma cod_simp [simp]:
    assumes "arr f"
    shows "cod f = (C1.cod (fst f), C2.cod (snd f))"
      using assms cod_char by auto

    lemma hom_char [iff]:
    shows "f \<in> hom b a \<longleftrightarrow> fst f \<in> C1.hom (fst b) (fst a) \<and> snd f \<in> C2.hom (snd b) (snd a)"
      using arr_char dom_char cod_char by auto

    lemma ide_char [iff]:
    shows "ide f \<longleftrightarrow> Ide f"
      by (metis (no_types, lifting) C1.ideD(1) C1.ideD(3) C2.ide_dom
          C2.ideD(1) C2.ideD(3) arr_char C1.ide_cod cod_simp dom_simp fst_conv
          ideI_cod ideD(1) ideD(2) ideD(3) prod.collapse snd_conv)

    lemma seq_char [iff]:
    shows "seq g f \<longleftrightarrow> C1.seq (fst g) (fst f) \<and> C2.seq (snd g) (snd f)"
      using arr_char cod_char dom_char by auto

    lemma comp_char:
    shows "comp g f = (if C1.seq (fst g) (fst f) \<and> C2.seq (snd g) (snd f) then
                          (C1 (fst g) (fst f), C2 (snd g) (snd f))
                       else Null)"
      using comp_def arr_char by auto

    lemma comp_simp [simp]:
    assumes "seq g f"
    shows "comp g f = (C1 (fst g) (fst f), C2 (snd g) (snd f))"
      using assms comp_char by auto

  end

end

