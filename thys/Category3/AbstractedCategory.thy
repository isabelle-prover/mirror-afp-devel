(*  Title:       AbstractedCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter AbstractedCategory

theory AbstractedCategory
imports Category
begin

  text{*
    The locale defined here allows us to lift a category to a different arrow
    type via an abstraction map.  It is used to obtain categories with opaque
    arrow types, by first defining the category on the concrete representation type,
    then lifting the composition to the abstract type.  I apply this technique
    in several places to avoid the possibility of ``contaminating'' theories
    with specific details about a particular construction on categories.
    The construction of functor categories is a good example of this.
  *}

  locale abstracted_category = C: category C
  for C :: "'c comp"
  and A :: "'c \<Rightarrow> 'a"
  and R :: "'a \<Rightarrow> 'c"
  and S :: "'c set" +
  assumes abs_rep: "A (R f) = f"
  and rep_abs: "x \<in> S \<Longrightarrow> R (A x) = x"
  and rep_in_domain: "R f \<in> S"
  and domain_closed: "C.arr x \<or> x = C.null \<Longrightarrow> x \<in> S"
  begin

    definition comp
    where "comp g f \<equiv> if C.seq (R g) (R f) then A (C (R g) (R f)) else A C.null"

    interpretation partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. comp n f = n \<and> comp f n = n"
      proof
        show "\<forall>f. comp (A C.null) f = A C.null \<and> comp f (A C.null) = A C.null"
          using comp_def rep_abs domain_closed by auto
        show "\<And>n. \<forall>f. comp n f = n \<and> comp f n = n \<Longrightarrow> n = A C.null"
          by (metis comp_def C.not_arr_null rep_abs domain_closed)
      qed
    qed

    lemma null_char:
    shows "null = A C.null"
      by (metis C.not_arr_null abstracted_category.comp_def abstracted_category_axioms comp_null(2)
                domain_closed rep_abs)

    lemma ide_implies_unit_abs:
    shows "C.ide f \<Longrightarrow> unit (A f)"
      by (simp add: abs_rep domain_closed local.comp_def null_char rep_abs unit_def)

    lemma has_dom_char':
    shows "has_dom f \<longleftrightarrow> C.has_dom (R f)"
    proof -
      fix f
      show "has_dom f \<longleftrightarrow> C.has_dom (R f)"
      proof
        assume f: "has_dom f"
        show "C.has_dom (R f)"
          using ide_implies_unit_abs f comp_def has_dom_def C.has_dom_def
          by (metis C.dom_def C.ideD(1) C.not_arr_null C.ide_dom comp_null(2))
        next
        assume f: "C.has_dom (R f)"
        show "has_dom f"
          using ide_implies_unit_abs f comp_def has_dom_def C.has_dom_def
          by (metis C.arr_dom_iff_arr C.has_domD(1) C.has_domD(3) C.not_arr_null
                    abstracted_category.domain_closed abstracted_category_axioms
                    C.cod_dom C.ide_dom comp_null(2) rep_abs)
      qed
    qed

    lemma has_cod_char':
    shows "has_cod f \<longleftrightarrow> C.has_cod (R f)"
    proof -
      fix f
      show "has_cod f \<longleftrightarrow> C.has_cod (R f)"
      proof
        assume f: "has_cod f"
        show "C.has_cod (R f)"
          using ide_implies_unit_abs has_dom_char' f comp_def has_cod_def C.has_cod_def
          by (metis C.category_axioms C.cod_def C.ideD(1) C.not_arr_null category.ide_cod null_char)
        next
        assume f: "C.has_cod (R f)"
        show "has_cod f"
        proof (intro has_codI)
          have "unit (A (C.cod (R f)))"
            using ide_implies_unit_abs f C.arrI C.ide_cod by blast
          moreover have "comp (A (C.cod (R f))) f \<noteq> null"
          proof -
            have "C.seq (R (A (C.cod (R f)))) (R f)"
              using ide_implies_unit_abs f rep_abs
              by (simp add: C.arrI C.arr_cod_iff_arr C.dom_cod domain_closed)
            thus ?thesis
              using ide_implies_unit_abs f comp_def
              by (metis C.arr_cod_iff_arr C.has_codD(3) C.not_arr_null domain_closed
                        null_char rep_abs)
          qed
          ultimately show "unit (A (C.cod (R f))) \<and> comp (A (C.cod (R f))) f \<noteq> null"
            by auto
        qed
      qed
    qed

    lemma is_category:
    shows "category comp"
    proof -
      interpret category comp
        using comp_def C.not_arr_null C.arr_comp C.dom_comp C.cod_comp comp_null(2) rep_abs
        apply unfold_locales
        (* 6 *) apply (metis abstracted_category.domain_closed abstracted_category_axioms)
        (* 5 *) apply (metis abstracted_category.domain_closed abstracted_category_axioms)
        (* 4 *) apply (metis abstracted_category.domain_closed abstracted_category_axioms)
        (* 3 *) apply (metis abstracted_category.domain_closed abstracted_category_axioms)
        using C.comp_assoc abstracted_category.domain_closed abstracted_category_axioms
        (* 2 *) apply metis (* 20 sec *)
        (* 1 *) using has_dom_char' has_cod_char' by (simp add: C.has_dom_iff_has_cod)
      show "category comp" ..
    qed

  end

  sublocale abstracted_category \<subseteq> category comp
    using is_category by auto

  context abstracted_category
  begin

    lemma has_dom_char:
    shows "has_dom f \<longleftrightarrow> C.arr (R f)"
      using has_dom_char' by (simp add: C.arr_def C.has_dom_iff_has_cod)
     
    lemma has_cod_char:
    shows "has_cod f \<longleftrightarrow> C.arr (R f)"
      using has_cod_char' by (simp add: C.arr_def C.has_dom_iff_has_cod)

    lemma arr_char:
    shows "arr f \<longleftrightarrow> C.arr (R f)"
      using has_dom_char has_cod_char arr_def by simp

    lemma dom_char:
    shows "dom f = (if arr f then A (C.dom (R f)) else null)"
    proof -
      have "arr f \<Longrightarrow> dom f = A (C.dom (R f))"
      proof -
        assume f: "arr f"
        have "unit (A (C.dom (R f)))"
          using f arr_char ide_implies_unit_abs by simp
        moreover have "comp f (A (C.dom (R f))) \<noteq> null"
          using f arr_char comp_def null_char rep_abs
          by (metis C.arr_dom_iff_arr C.comp_arr_dom C.cod_dom not_arr_null
                    abstracted_category.domain_closed abstracted_category_axioms)
        ultimately show "dom f = A (C.dom (R f))"
          using f dom_simp by simp
      qed
      moreover have "\<not>arr f \<Longrightarrow> dom f = null"
        by (simp add: arr_def dom_def)
      ultimately show ?thesis by auto
    qed
     
    lemma cod_char:
    shows "cod f = (if arr f then A (C.cod (R f)) else null)"
    proof -
      have "arr f \<Longrightarrow> cod f = A (C.cod (R f))"
      proof -
        assume f: "arr f"
        have "unit (A (C.cod (R f)))"
          using f arr_char ide_implies_unit_abs by simp
        moreover have "comp (A (C.cod (R f))) f \<noteq> null"
          using f arr_char comp_def null_char rep_abs
          by (metis C.arr_cod_iff_arr C.comp_cod_arr C.dom_cod not_arr_null
                    abstracted_category.domain_closed abstracted_category_axioms)
        ultimately show "cod f = A (C.cod (R f))"
          using f cod_simp by simp
      qed
      moreover have "\<not>arr f \<Longrightarrow> cod f = null"
        by (simp add: arr_def cod_def)
      ultimately show ?thesis by auto
    qed

    lemma ide_char:
    shows "ide a \<longleftrightarrow> C.ide (R a)"
     using arr_char dom_char
     by (metis C.arr_dom_iff_arr C.ideD(1) C.ideD(2) C.ideI_dom abs_rep domain_closed
               ideD(1) ideD(2) ideI_dom rep_abs)

    lemma comp_char:
    shows "comp g f = (if seq g f then A (C (R g) (R f)) else null)"
      using arr_char dom_char cod_char comp_def null_char arr_comp not_arr_null by metis

  end

end
