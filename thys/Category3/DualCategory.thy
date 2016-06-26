(*  Title:       DualCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter DualCategory

theory DualCategory
imports Category
begin

  text{*
    The locale defined here constructs the dual (opposite) of a category.
    The arrows of the dual category are directly identified with the arrows of
    the given category and simplification rules are introduced that automatically
    eliminate notions defined for the dual category in favor of the corresponding
    notions on the original category.  This makes it easy to use the dual of
    a category in the same context as the category itself, without having to
    worry about whether an arrow belows to the category or its dual.
  *}
    
  locale dual_category = C: category C
  for C :: "'a comp"
  begin

    definition comp
    where "comp g f \<equiv> C f g"

    lemma comp_char [simp]:
    shows "comp g f = C f g"
      using comp_def by auto

    interpretation partial_magma comp
      apply unfold_locales using comp_def C.ex_un_null by metis

    lemma null_char [simp]:
    shows "null = C.null"
      using C.comp_null comp_def C.nullI null_def by auto

    lemma unit_char:
    shows "unit a \<longleftrightarrow> C.unit a"
      unfolding unit_def C.unit_def by auto

    lemma has_dom_char:
    shows "has_dom f \<longleftrightarrow> C.has_cod f"
      using unit_char has_dom_def C.has_cod_def by simp

    lemma has_cod_char:
    shows "has_cod f \<longleftrightarrow> C.has_dom f"
      using unit_char has_cod_def C.has_dom_def by simp

    interpretation category comp
      apply unfold_locales
      (* 6 *) using comp_def C.match_2 null_char apply metis
      (* 5 *) using comp_def C.match_1 null_char apply metis
      (* 4 *) apply (auto simp add: C.match_3 C.match_4)
      (* 3 *) by (auto simp add: C.has_dom_iff_has_cod has_cod_char has_dom_char C.comp_assoc')

    lemma is_category:
    shows "category comp" ..

  end

  sublocale dual_category \<subseteq> category comp
    using is_category by auto

  context dual_category
  begin

    lemma dom_char [simp]:
    shows "dom f = C.cod f"
      using unit_char has_dom_char dom_def C.cod_def by auto

    lemma cod_char [simp]:
    shows "cod f = C.dom f"
      using unit_char has_cod_char cod_def C.dom_def by auto

    lemma arr_char [iff]:
    shows "arr f \<longleftrightarrow> C.arr f"
      using arr_def C.arr_def has_cod_char has_dom_char by auto

    lemma hom_char [iff]:
    shows "f \<in> hom b a \<longleftrightarrow> f \<in> C.hom a b"
      by fastforce

    lemma ide_char [iff]:
    shows "ide a \<longleftrightarrow> C.ide a"
      using ideD(1) ideD(3) by auto

    lemma seq_char [iff]:
    shows "seq g f \<longleftrightarrow> C.seq f g"
      by auto

  end

end

