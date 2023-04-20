(*  Title:       ConcreteBicategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2021
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Concrete Bicategories"

text \<open>
  The locale \<open>concrete_bicategory\<close> defined in this section provides a uniform way to construct
  a bicategory from extrinsically specified data comprising: a set of \<open>Obj\<close> of ``objects'',
  a ``hom-category'' \<open>Hom A B\<close> for each pair of objects \<open>A\<close> and \<open>B\<close>, an ``identity arrow''
  \<open>Id A \<in> Hom A A\<close> for each object \<open>A\<close>, ``horizontal composition'' functors
  \<open>Comp C B A : Hom B C \<times> Hom A B \<rightarrow> Hom A C\<close> indexed by triples of objects,
  together with unit and associativity isomorphisms; the latter subject to naturality and
  coherence conditions.
  We show that the bicategory produced by the construction relates to the given data in the
  expected fashion: the objects of the bicategory are in bijective correspondence with the
  given set \<open>Obj\<close>, the hom-categories of the bicategory are isomorphic to the given
  categories \<open>Hom A B\<close>, the horizontal composition of the bicategory agrees with the given
  compositions \<open>Comp C B A\<close>, and the unit and associativity 2-cells of the bicategory are
  directly defined in terms of the given unit and associativity isomorphisms.
\<close>

theory ConcreteBicategory
imports Bicategory.Bicategory
begin

  locale concrete_bicategory =
  fixes Obj :: "'o set"
  and Hom :: "'o \<Rightarrow> 'o \<Rightarrow> 'a comp"
  and Id :: "'o \<Rightarrow> 'a"
  and Comp :: "'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>'a"
  and Unit :: "'o \<Rightarrow> 'a"
  and Assoc :: "'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes category_Hom: "\<lbrakk> A \<in> Obj; B \<in> Obj \<rbrakk> \<Longrightarrow> category (Hom A B)"
  and binary_functor_Comp:
        "\<lbrakk> A \<in> Obj; B \<in> Obj; C \<in> Obj \<rbrakk>
            \<Longrightarrow> binary_functor (Hom B C) (Hom A B) (Hom A C) (\<lambda>(f, g). Comp C B A f g)"
  and ide_Id: "A \<in> Obj \<Longrightarrow> partial_composition.ide (Hom A A) (Id A)"
  and Unit_in_hom:
        "A \<in> Obj \<Longrightarrow>
           partial_composition.in_hom (Hom A A) (Unit A) (Comp A A A (Id A) (Id A)) (Id A)"
  and iso_Unit: "A \<in> Obj \<Longrightarrow> category.iso (Hom A A) (Unit A)"
  and natural_isomorphism_Assoc:
        "\<lbrakk> A \<in> Obj; B \<in> Obj; C \<in> Obj; D \<in> Obj \<rbrakk>
            \<Longrightarrow> natural_isomorphism
                  (product_category.comp
                    (Hom C D) (product_category.comp (Hom B C) (Hom A B))) (Hom A D)
                  (\<lambda>(f, g, h). Comp D B A (Comp D C B f g) h)
                  (\<lambda>(f, g, h). Comp D C A f (Comp C B A g h))
                  (\<lambda>(f, g, h). Assoc D C B A f g h)"
  and left_unit_Id:
        "\<And>A B. \<lbrakk> A \<in> Obj; B \<in> Obj \<rbrakk>
                   \<Longrightarrow> fully_faithful_functor (Hom A B) (Hom A B)
                         (\<lambda>f. if partial_composition.arr (Hom A B) f
                              then Comp B B A (Id B) f
                              else partial_magma.null (Hom A B))"
  and right_unit_Id:
        "\<And>A B. \<lbrakk> A \<in> Obj; B \<in> Obj \<rbrakk>
                   \<Longrightarrow> fully_faithful_functor (Hom A B) (Hom A B)
                         (\<lambda>f. if partial_composition.arr (Hom A B) f
                              then Comp B A A f (Id A)
                              else partial_magma.null (Hom A B))"
  and pentagon:
        "\<And>A B C D E f g h k.
            \<lbrakk> A \<in> Obj; B \<in> Obj; C \<in> Obj; D \<in> Obj; E \<in> Obj;
              partial_composition.ide (Hom D E) f; partial_composition.ide (Hom C D) g;
              partial_composition.ide (Hom B C) h; partial_composition.ide (Hom A B) k \<rbrakk> \<Longrightarrow>
              Hom A E (Comp E D A f (Assoc D C B A g h k))
                      (Hom A E (Assoc E D B A f (Comp D C B g h) k)
                               (Comp E B A (Assoc E D C B f g h) k)) =
              Hom A E (Assoc E D C A f g (Comp C B A h k))
                      (Assoc E C B A (Comp E D C f g) h k)"
  begin

    text \<open>
      We first construct the vertical category.
      Arrows are terms of the form \<open>MkCell A B \<mu>\<close>, where \<open>A \<in> Obj\<close>, \<open>B \<in> Obj\<close>, and where \<open>\<mu>\<close>
      is an arrow of \<open>Hom A B\<close>.
      Composition requires agreement of the ``source'' \<open>A\<close> and ``target'' \<open>B\<close> components,
      and is then defined in terms of composition within \<open>Hom A B\<close>.
    \<close>

    datatype ('oo, 'aa) cell =
      Null
    | MkCell 'oo 'oo 'aa

    abbreviation MkObj :: "'o \<Rightarrow> ('o, 'a) cell"
    where "MkObj A \<equiv> MkCell A A (Id A)"

    fun Src :: "('o, 'a) cell \<Rightarrow> 'o"
    where "Src (MkCell A _ _) = A"
        | "Src _ = undefined"

    fun Trg
    where "Trg (MkCell _ B _) = B"
        | "Trg _ = undefined"

    fun Map
    where "Map (MkCell _ _ F) = F"
        | "Map _ = undefined"

    abbreviation Cell
    where "Cell \<mu> \<equiv> \<mu> \<noteq> Null \<and> Src \<mu> \<in> Obj \<and> Trg \<mu> \<in> Obj \<and>
                    partial_composition.arr (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"

    definition vcomp
    where "vcomp \<mu> \<nu> \<equiv> if Cell \<mu> \<and> Cell \<nu> \<and> Src \<mu> = Src \<nu> \<and> Trg \<mu> = Trg \<nu> \<and>
                           partial_composition.seq (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>) (Map \<nu>)
                        then MkCell (Src \<mu>) (Trg \<mu>) (Hom (Src \<mu>) (Trg \<mu>) (Map \<mu>) (Map \<nu>))
                        else Null"

    interpretation partial_composition vcomp
      by (metis partial_composition_def partial_magma_def vcomp_def)

    lemma null_char:
    shows "null = Null"
      using null_is_zero(1) vcomp_def by metis

    lemma MkCell_Map:
    assumes "\<mu> \<noteq> null"
    shows "\<mu> = MkCell (Src \<mu>) (Trg \<mu>) (Map \<mu>)"
      using assms null_char
      by (metis Map.simps(1) Src.elims Trg.simps(1))

    (*
     * We need to name the following fact so that it does not get
     * hidden when we interpret the category locale, because it is still
     * used in some subsequent proofs.
     *)
    lemma ide_char'':
    shows "ide \<mu> \<longleftrightarrow> Cell \<mu> \<and> partial_composition.ide (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"
    proof
      show "ide \<mu> \<Longrightarrow> Cell \<mu> \<and> partial_composition.ide (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"
      proof
        assume \<mu>: "ide \<mu>"
        show 1: "Cell \<mu>"
          by (metis \<mu> ide_def vcomp_def)
        interpret Hom: category "Hom (Src \<mu>) (Trg \<mu>)"
          using 1 category_Hom by simp
        let ?\<nu> = "MkCell (Src \<mu>) (Trg \<mu>) (Hom.dom (Map \<mu>))"
        have "vcomp \<mu> ?\<nu> = MkCell (Src \<mu>) (Trg \<mu>) (Map \<mu>)"
          using 1 vcomp_def Hom.comp_arr_dom by simp
        moreover have "vcomp \<mu> ?\<nu> = ?\<nu>"
          using \<mu> ide_def null_char
          by (metis MkCell_Map calculation)
        ultimately show "Hom.ide (Map \<mu>)"
          using 1 Hom.ide_dom by fastforce
      qed
      show "Cell \<mu> \<and> partial_composition.ide (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>) \<Longrightarrow> ide \<mu>"
      proof -
        assume \<mu>: "Cell \<mu> \<and> partial_composition.ide (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"
        interpret Hom: category "Hom (Src \<mu>) (Trg \<mu>)"
          using \<mu> category_Hom by simp
        show "ide \<mu>"
        proof -
          have "vcomp \<mu> \<mu> \<noteq> null"
            using \<mu> vcomp_def null_char by simp
          moreover have "\<And>\<nu>. vcomp \<nu> \<mu> \<noteq> null \<Longrightarrow> vcomp \<nu> \<mu> = \<nu>"
            by (metis (full_types) Hom.comp_arr_ide \<mu> MkCell_Map vcomp_def null_char)
          moreover have "\<And>\<nu>. vcomp \<mu> \<nu> \<noteq> null \<Longrightarrow> vcomp \<mu> \<nu> = \<nu>"
            by (metis Hom.comp_ide_arr MkCell_Map \<mu> null_char vcomp_def)
          ultimately show ?thesis
            unfolding ide_def by simp
        qed
      qed
    qed

    lemma MkCell_in_domains:
    assumes "Cell \<mu>"
    shows "MkCell (Src \<mu>) (Trg \<mu>) (partial_composition.dom (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>))
             \<in> domains \<mu>"
    proof -
      interpret Hom: category "Hom (Src \<mu>) (Trg \<mu>)"
        using assms category_Hom by simp
      let ?\<nu> = "MkCell (Src \<mu>) (Trg \<mu>) (Hom.dom (Map \<mu>))"
      have "ide ?\<nu>"
        using assms ide_char'' Hom.arr_dom Hom.ide_dom by simp
      moreover have "vcomp \<mu> ?\<nu> = \<mu>"
        unfolding vcomp_def
        using assms Hom.comp_arr_dom MkCell_Map null_char by auto
      ultimately show ?thesis
          using domains_def by (simp add: assms null_char)
    qed
    
    lemma MkCell_in_codomains:
    assumes "Cell \<mu>"
    shows "MkCell (Src \<mu>) (Trg \<mu>) (partial_composition.cod (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>))
             \<in> codomains \<mu>"
    proof -
      interpret Hom: category "Hom (Src \<mu>) (Trg \<mu>)"
        using assms category_Hom by simp
      let ?\<nu> = "MkCell (Src \<mu>) (Trg \<mu>) (Hom.cod (Map \<mu>))"
      have "ide ?\<nu>"
        using assms ide_char'' Hom.arr_dom Hom.ide_dom by simp
      moreover have "vcomp ?\<nu> \<mu> = \<mu>"
        unfolding vcomp_def
        using assms Hom.comp_cod_arr MkCell_Map null_char by auto
      ultimately show ?thesis
          using codomains_def by (simp add: assms null_char)
    qed
  
    lemma has_domain_char:
    shows "domains \<mu> \<noteq> {} \<longleftrightarrow> Cell \<mu>"
    proof -
      have "\<not> Cell \<mu> \<Longrightarrow> domains \<mu> = {}"
        using vcomp_def domains_def null_char by auto
      moreover have
        "Cell \<mu> \<Longrightarrow> MkCell (Src \<mu>) (Trg \<mu>) (partial_composition.dom (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>))
                       \<in> domains \<mu>"
        using MkCell_in_domains by simp
      ultimately show ?thesis by auto
    qed

    lemma has_codomain_char:
    shows "codomains \<mu> \<noteq> {} \<longleftrightarrow> Cell \<mu>"
    proof -
      have "\<not> Cell \<mu> \<Longrightarrow> codomains \<mu> = {}"
        using vcomp_def codomains_def null_char by auto
      moreover have
        "Cell \<mu> \<Longrightarrow> MkCell (Src \<mu>) (Trg \<mu>) (partial_composition.cod (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>))
                       \<in> codomains \<mu>"
        using MkCell_in_codomains by simp
      ultimately show ?thesis by auto
    qed

    lemma arr_char:
    shows "arr \<mu> \<longleftrightarrow> Cell \<mu>"
      using arr_def has_domain_char has_codomain_char by simp

    lemma ide_char''':
    shows "ide \<mu> \<longleftrightarrow> arr \<mu> \<and> partial_composition.ide (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"
      using ide_char'' arr_char by simp

    lemma seq_char:
    shows "seq \<mu> \<nu> \<longleftrightarrow> Cell \<mu> \<and> Cell \<nu> \<and> Src \<mu> = Src \<nu> \<and> Trg \<mu> = Trg \<nu> \<and>
                       partial_composition.seq (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>) (Map \<nu>)"
      using arr_char vcomp_def by auto

    lemma vcomp_char:
    shows "vcomp \<mu> \<nu> = (if seq \<mu> \<nu> then
                          MkCell (Src \<mu>) (Trg \<mu>) (Hom (Src \<mu>) (Trg \<mu>) (Map \<mu>) (Map \<nu>))
                        else null)"
      by (metis null_char seq_char vcomp_def)

    interpretation category vcomp
    proof
      show "\<And>g f. vcomp g f \<noteq> null \<Longrightarrow> seq g f"
        using seq_char null_char vcomp_def by metis
      show "\<And>f. (domains f \<noteq> {}) = (codomains f \<noteq> {})"
        using has_domain_char has_codomain_char by simp
      show "\<And>h g f. \<lbrakk>seq h g; seq (vcomp h g) f\<rbrakk> \<Longrightarrow> seq g f"
        using vcomp_def
        apply (unfold seq_char, intro conjI)
                  apply auto
        by (meson category.match_1 category_Hom)
      show "\<And>h g f. \<lbrakk>seq h (vcomp g f); seq g f\<rbrakk> \<Longrightarrow> seq h g"
        using vcomp_def
        apply (unfold seq_char, intro conjI)
                  apply auto
        by (meson category.match_2 category_Hom)
      show "\<And>g f h. \<lbrakk>seq g f; seq h g\<rbrakk> \<Longrightarrow> seq (vcomp h g) f"
        using vcomp_def
        apply (unfold seq_char, intro conjI)
                  apply auto
        by (meson category.match_3 category_Hom)
      show "\<And>g f h. \<lbrakk>seq g f; seq h g\<rbrakk> \<Longrightarrow> vcomp (vcomp h g) f = vcomp h (vcomp g f)"
      proof -
        fix f g h
        assume fg: "seq g f" and gh: "seq h g"
        interpret Hom: category \<open>Hom (Src f) (Trg f)\<close>
          using fg seq_char category_Hom by simp
        have "vcomp (vcomp h g) f =
              MkCell (Src f) (Trg f)
                                (Hom (Src f) (Trg f)
                                     (Hom (Src f) (Trg f) (Map h) (Map g)) (Map f))"
          using fg gh vcomp_char seq_char null_char Hom.match_3 by auto
        also have "... =
              MkCell (Src f) (Trg f)
                     (Hom (Src f) (Trg f) (Map h)
                          (Hom (Src f) (Trg f) (Map g) (Map f)))"
          using fg gh seq_char Hom.comp_assoc by simp
        also have "... = vcomp h (vcomp g f)"
          using fg gh vcomp_char seq_char null_char Hom.match_4 by auto
        finally show "vcomp (vcomp h g) f = vcomp h (vcomp g f)"
          by blast
      qed
    qed

    lemma arr_eqI:
    assumes "arr f" and "arr f'"
    and "Src f = Src f'" and "Trg f = Trg f'" and "Map f = Map f'"
    shows "f = f'"
      using arr_char MkCell_Map assms null_char by metis

    lemma dom_char:
    shows "dom \<mu> = (if arr \<mu> then
                      MkCell (Src \<mu>) (Trg \<mu>) (partial_composition.dom (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>))
                    else Null)"
      by (metis MkCell_in_domains arr_char dom_in_domains domain_unique has_domain_iff_arr
          dom_def null_char)
        
    lemma cod_char:
    shows "cod \<mu> = (if arr \<mu> then
                      MkCell (Src \<mu>) (Trg \<mu>) (partial_composition.cod (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>))
                    else Null)"
      by (metis MkCell_in_codomains arr_char cod_def cod_in_codomains codomain_unique
          has_codomain_iff_arr null_char)

    lemma Src_vcomp [simp]:
    assumes "seq \<mu> \<nu>"
    shows "Src (vcomp \<mu> \<nu>) = Src \<mu>"
      using assms seq_char vcomp_def by auto

    lemma Trg_vcomp [simp]:
    assumes "seq \<mu> \<nu>"
    shows "Trg (vcomp \<mu> \<nu>) = Trg \<mu>"
      using assms seq_char vcomp_def by auto

    lemma Map_vcomp [simp]:
    assumes "seq \<mu> \<nu>"
    shows "Map (vcomp \<mu> \<nu>) = Hom (Src \<mu>) (Trg \<mu>) (Map \<mu>) (Map \<nu>)"
      using assms seq_char vcomp_def by auto

    lemma arr_MkCell [simp]:
    assumes "A \<in> Obj" and "B \<in> Obj" and "partial_composition.arr (Hom A B) f"
    shows "arr (MkCell A B f)"
      using assms arr_char by simp

    lemma dom_MkCell [simp]:
    assumes "arr (MkCell A B f)"
    shows "dom (MkCell A B f) = MkCell A B (partial_composition.dom (Hom A B) f)"
      using assms arr_char dom_char by simp

    lemma cod_MkCell [simp]:
    assumes "arr (MkCell A B f)"
    shows "cod (MkCell A B f) = MkCell A B (partial_composition.cod (Hom A B) f)"
      using assms arr_char cod_char by simp

    lemma iso_char:
    shows "iso \<mu> \<longleftrightarrow> arr \<mu> \<and> category.iso (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"
    proof
      assume \<mu>: "iso \<mu>"
      have 1: "arr \<mu>" using \<mu> by blast
      interpret Hom: category \<open>Hom (Src \<mu>) (Trg \<mu>)\<close>
        using 1 arr_char category_Hom by simp
      have 2: "Hom.iso (Map \<mu>)"
      proof -
        obtain \<nu> where \<nu>: "inverse_arrows \<mu> \<nu>"
          using \<mu> by blast
        have "Hom.inverse_arrows (Map \<mu>) (Map \<nu>)"
        proof
          show "Hom.ide (Hom (Src \<mu>) (Trg \<mu>) (Map \<mu>) (Map \<nu>))"
            using \<nu> ide_char'' Src_vcomp Trg_vcomp ideD(1) vcomp_char Map_vcomp
            by (metis inverse_arrowsE)
          show "Hom.ide (Hom (Src \<mu>) (Trg \<mu>) (Map \<nu>) (Map \<mu>))"
          proof -
            have 1: "ide (vcomp \<nu> \<mu>)"
              using \<nu> by auto
            hence "Hom.ide (Map (vcomp \<nu> \<mu>))"
              using ide_char'' Src_vcomp Trg_vcomp ideD(1) seq_char by metis
            thus "Hom.ide (Hom (Src \<mu>) (Trg \<mu>) (Map \<nu>) (Map \<mu>))"
              using \<nu> 1 vcomp_char Map.simps(1) seq_char ideD(1)
              by (metis (no_types, lifting))
          qed
        qed
        thus ?thesis by auto
      qed
      show "arr \<mu> \<and> Hom.iso (Map \<mu>)"
        using 1 2 by simp
      next
      assume \<mu>: "arr \<mu> \<and> category.iso (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"
      interpret Hom: category \<open>Hom (Src \<mu>) (Trg \<mu>)\<close>
        using \<mu> arr_char category_Hom by simp
      obtain f where f: "Hom.inverse_arrows (Map \<mu>) f"
        using \<mu> by auto
      let ?\<nu> = "MkCell (Src \<mu>) (Trg \<mu>) f"
      have 1: "arr ?\<nu>"
        using \<mu> f arr_char by auto
      have "inverse_arrows \<mu> (MkCell (Src \<mu>) (Trg \<mu>) f)"
        using \<mu> f 1 arr_char ide_char'' vcomp_def
        apply (intro inverse_arrowsI) by auto
      thus "iso \<mu>" by auto        
    qed

    text \<open>
      Next, we equip each arrow with a source and a target, and show that these assignments
      are functorial.
    \<close>

    definition src
    where "src \<mu> \<equiv> if arr \<mu> then MkObj (Src \<mu>) else null"

    definition trg
    where "trg \<mu> \<equiv> if arr \<mu> then MkObj (Trg \<mu>) else null"

    lemma src_MkCell [simp]:
    assumes "arr (MkCell A B f)"
    shows "src (MkCell A B f) = MkObj A"
      using assms src_def by simp

    lemma trg_MkCell [simp]:
    assumes "arr (MkCell A B f)"
    shows "trg (MkCell A B f) = MkObj B"
      using assms trg_def by simp

    lemma src_dom:
    assumes "arr \<mu>"
    shows "src (dom \<mu>) = src \<mu>"
      using assms dom_char src_def arr_char arr_dom by auto

    lemma src_cod:
    assumes "arr \<mu>"
    shows "src (cod \<mu>) = src \<mu>"
      using assms cod_char src_def arr_char arr_cod by auto

    lemma trg_dom:
    assumes "arr \<mu>"
    shows "trg (dom \<mu>) = trg \<mu>"
      using assms dom_char trg_def arr_char arr_dom by auto

    lemma trg_cod:
    assumes "arr \<mu>"
    shows "trg (cod \<mu>) = trg \<mu>"
      using assms cod_char trg_def arr_char arr_cod by auto

    lemma Src_src [simp]:
    assumes "arr \<mu>"
    shows "Src (src \<mu>) = Src \<mu>"
      using assms src_def by simp

    lemma Trg_src [simp]:
    assumes "arr \<mu>"
    shows "Trg (src \<mu>) = Src \<mu>"
      using assms src_def by simp

    lemma Map_src [simp]:
    assumes "arr \<mu>"
    shows "Map (src \<mu>) = Id (Src \<mu>)"
      using assms src_def by simp

    lemma Src_trg [simp]:
    assumes "arr \<mu>"
    shows "Src (trg \<mu>) = Trg \<mu>"
      using assms trg_def by simp

    lemma Trg_trg [simp]:
    assumes "arr \<mu>"
    shows "Trg (trg \<mu>) = Trg \<mu>"
      using assms trg_def by simp

    lemma Map_trg [simp]:
    assumes "arr \<mu>"
    shows "Map (trg \<mu>) = Id (Trg \<mu>)"
      using assms trg_def by simp

    lemma Src_dom [simp]:
    assumes "arr \<mu>"
    shows "Src (dom \<mu>) = Src \<mu>"
      using assms dom_char src_def arr_char arr_dom by auto

    lemma Src_cod [simp]:
    assumes "arr \<mu>"
    shows "Src (cod \<mu>) = Src \<mu>"
      using assms src_cod src_def arr_char arr_cod by auto

    lemma Trg_dom [simp]:
    assumes "arr \<mu>"
    shows "Trg (dom \<mu>) = Trg \<mu>"
      using assms dom_char trg_def arr_char arr_dom by auto

    lemma Trg_cod [simp]:
    assumes "arr \<mu>"
    shows "Trg (cod \<mu>) = Trg \<mu>"
      using assms cod_char trg_def arr_char arr_cod by auto

    lemma Map_dom [simp]:
    assumes "arr \<mu>"
    shows "Map (dom \<mu>) = partial_composition.dom (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"
      using assms by (simp add: dom_char)

    lemma Map_cod [simp]:
    assumes "arr \<mu>"
    shows "Map (cod \<mu>) = partial_composition.cod (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"
      using assms by (simp add: cod_char)

    lemma ide_MkObj:
    assumes "A \<in> Obj"
    shows "ide (MkObj A)"
      using assms ide_char'
      by (metis Map.simps(1) Src.simps(1) Trg.simps(1) category.ideD(1) cell.simps(2)
          category_Hom ide_char'' ide_Id) 

    interpretation src: "functor" vcomp vcomp src
      using src_def arr_char Map.simps(1) Src.simps(1) Trg.simps(1) arr_dom category.ideD(1)
            ide_MkObj src_dom src_cod ide_Id
      apply unfold_locales
          apply auto[1]
         apply (simp add: category.ideD(1) category_Hom)
        apply auto[2]
    proof -
      fix g :: "('o, 'a) cell" and f :: "('o, 'a) cell"
      assume fg: "seq g f"
      thus "src (vcomp g f) = vcomp (src g) (src f)"
        using arr_char ide_MkObj src_dom src_cod src_def
        by (metis Src_vcomp comp_ide_self seqE)
    qed

    interpretation trg: "functor" vcomp vcomp trg
      using trg_def arr_char Map.simps(1) Src.simps(1) Trg.simps(1) arr_dom category.ideD(1)
            ide_MkObj trg_dom trg_cod ide_Id
      apply unfold_locales
          apply auto[1]
         apply (simp add: category.ideD(1) category_Hom)
        apply auto[2]
    proof -
      fix g :: "('o, 'a) cell" and f :: "('o, 'a) cell"
      assume fg: "seq g f"
      thus "trg (vcomp g f) = vcomp (trg g) (trg f)"
        using arr_char ide_MkObj trg_dom trg_cod trg_def
        by (metis Trg_vcomp comp_ide_self seqE)
    qed

    interpretation H: horizontal_homs vcomp src trg
      using ide_MkObj arr_char src_def trg_def src.preserves_arr trg.preserves_arr
      by unfold_locales auto

    lemma obj_MkObj:
    assumes "A \<in> Obj"
    shows "H.obj (MkObj A)"
      using assms src_def H.obj_def ide_MkObj by simp

    lemma MkCell_in_hom [intro]:
    assumes "A \<in> Obj" and "B \<in> Obj" and "partial_composition.arr (Hom A B) f"
    shows "H.in_hhom (MkCell A B f) (MkObj A) (MkObj B)"
    and "\<guillemotleft>MkCell A B f : MkCell A B (partial_composition.dom (Hom A B) f)
                            \<Rightarrow> MkCell A B (partial_composition.cod (Hom A B) f)\<guillemotright>"
      using assms by auto

    text \<open>
      Horizontal composition of horizontally composable arrows is now defined by applying
      the given function \<open>Comp\<close> to the ``Map'' components.
    \<close>

    definition hcomp
    where "hcomp \<mu> \<nu> \<equiv> if arr \<mu> \<and> arr \<nu> \<and> src \<mu> = trg \<nu> then
                         MkCell (Src \<nu>) (Trg \<mu>) (Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) (Map \<mu>) (Map \<nu>))
                       else
                         null"

    lemma arr_hcomp:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "arr (hcomp \<mu> \<nu>)"
    and "dom (hcomp \<mu> \<nu>) = hcomp (dom \<mu>) (dom \<nu>)"
    and "cod (hcomp \<mu> \<nu>) = hcomp (cod \<mu>) (cod \<nu>)"
    proof -
      have 1: "hcomp \<mu> \<nu> =
               MkCell (Src \<nu>) (Trg \<mu>) (Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) (Map \<mu>) (Map \<nu>))"
        using assms hcomp_def by simp
      have 2: "Src \<mu> = Trg \<nu>"
        using assms src_def trg_def by simp
      interpret Hom_\<mu>: category \<open>Hom (Src \<mu>) (Trg \<mu>)\<close>
        using assms arr_char category_Hom by simp
      interpret Hom_\<nu>: category \<open>Hom (Src \<nu>) (Trg \<nu>)\<close>
        using assms arr_char category_Hom by simp
      interpret Hom_\<mu>\<nu>: category \<open>Hom (Src \<nu>) (Trg \<mu>)\<close>
        using assms arr_char category_Hom by simp
      interpret Comp: binary_functor
                        \<open>Hom (Trg \<nu>) (Trg \<mu>)\<close> \<open>Hom (Src \<nu>) (Trg \<nu>)\<close> \<open>Hom (Src \<nu>) (Trg \<mu>)\<close>
                        \<open>\<lambda>(f, g). Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) f g\<close>
        using assms arr_char 2 binary_functor_Comp [of "Src \<nu>" "Trg \<nu>" "Trg \<mu>"]
        by simp
      have 4: "Comp.A1xA2.arr (Map \<mu>, Map \<nu>)"
        using assms 2 arr_char Comp.A1xA2.arr_char by simp
      show 3: "arr (hcomp \<mu> \<nu>)"
        using assms 1 2 4 arr_char Comp.preserves_arr [of "(Map \<mu>, Map \<nu>)"]
        by simp
      show "dom (hcomp \<mu> \<nu>) = hcomp (dom \<mu>) (dom \<nu>)"
      proof -
        have "dom (hcomp \<mu> \<nu>) =
              MkCell (Src \<nu>) (Trg \<mu>)
                     (Hom_\<mu>\<nu>.dom (Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) (Map \<mu>) (Map \<nu>)))"
          using 1 3 dom_char by simp
        moreover have "Hom_\<mu>\<nu>.dom (Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) (Map \<mu>) (Map \<nu>)) =
                       Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) (Hom_\<mu>.dom (Map \<mu>)) (Hom_\<nu>.dom (Map \<nu>))"
          using 2 Comp.preserves_dom \<open>Comp.A1xA2.arr (Map \<mu>, Map \<nu>)\<close> by force
        ultimately show ?thesis
          using assms 2 dom_char hcomp_def arr_dom
          by auto metis
      qed
      show "cod (hcomp \<mu> \<nu>) = hcomp (cod \<mu>) (cod \<nu>)"
      proof -
        have "cod (hcomp \<mu> \<nu>) =
              MkCell (Src \<nu>) (Trg \<mu>)
                     (Hom_\<mu>\<nu>.cod (Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) (Map \<mu>) (Map \<nu>)))"
          using 1 3 cod_char by simp
        moreover have "Hom_\<mu>\<nu>.cod (Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) (Map \<mu>) (Map \<nu>)) =
                       Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) (Hom_\<mu>.cod (Map \<mu>)) (Hom_\<nu>.cod (Map \<nu>))"
          using 2 Comp.preserves_cod \<open>Comp.A1xA2.arr (Map \<mu>, Map \<nu>)\<close> by force
        ultimately show "cod (hcomp \<mu> \<nu>) = hcomp (cod \<mu>) (cod \<nu>)"
          using assms 2 cod_char hcomp_def arr_cod
          by auto metis
      qed
    qed

    lemma src_hcomp:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "src (hcomp \<mu> \<nu>) = src \<nu>"
      using assms hcomp_def src_def arr_hcomp(1) by auto

    lemma trg_hcomp:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "trg (hcomp \<mu> \<nu>) = trg \<mu>"
      using assms hcomp_def trg_def arr_hcomp(1) by auto

    lemma Src_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "Src (hcomp \<mu> \<nu>) = Src \<nu>"
      using assms hcomp_def by simp

    lemma Trg_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "Trg (hcomp \<mu> \<nu>) = Trg \<mu>"
      using assms hcomp_def by simp

    lemma Map_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "Map (hcomp \<mu> \<nu>) = Comp (Trg \<mu>) (Trg \<nu>) (Src \<nu>) (Map \<mu>) (Map \<nu>)"
      using assms hcomp_def by simp

    lemma hcomp_vcomp:
    assumes "H.VV.seq g f"
    shows "hcomp (fst (H.VV.comp g f)) (snd (H.VV.comp g f)) =
           vcomp (hcomp (fst g) (snd g)) (hcomp (fst f) (snd f))"
    proof -
      let ?f1 = "fst f" and ?f2 = "snd f" and ?g1 = "fst g" and ?g2 = "snd g"
      have 1: "Src ?f1 \<in> Obj \<and> Trg ?f1 \<in> Obj \<and> Src ?f2 \<in> Obj \<and> Trg ?f2 \<in> Obj \<and>
               Src ?g1 \<in> Obj \<and> Trg ?g1 \<in> Obj \<and> Src ?g2 \<in> Obj \<and> Trg ?g2 \<in> Obj"
        using assms arr_char H.VV.arrE by blast
      interpret Hom_f1: category \<open>Hom (Src ?f1) (Trg ?f1)\<close>
        using assms 1 category_Hom by simp
      interpret Hom_f2: category \<open>Hom (Src ?f2) (Trg ?f2)\<close>
        using assms 1 category_Hom by simp
      interpret Hom_g1: category \<open>Hom (Src ?g1) (Trg ?g1)\<close>
        using assms 1 category_Hom by simp
      interpret Hom_g2: category \<open>Hom (Src ?g2) (Trg ?g2)\<close>
        using assms 1 category_Hom by simp
      interpret Hom_f: category \<open>Hom (Src ?f2) (Trg ?f1)\<close>
        using assms 1 category_Hom by simp
      interpret Hom_g: category \<open>Hom (Src ?g2) (Trg ?g1)\<close>
        using assms 1 category_Hom by simp
      interpret Comp_f: binary_functor \<open>Hom (Trg ?f2) (Trg ?f1)\<close> \<open>Hom (Src ?f2) (Trg ?f2)\<close>
                          \<open>Hom (Src ?f2) (Trg ?f1)\<close>
                          \<open>\<lambda>(fa, g). Comp (Trg ?f1) (Trg ?f2) (Src ?f2) fa g\<close>
        using assms 1 arr_char binary_functor_Comp by simp

      have "hcomp (fst (H.VV.comp g f)) (snd (H.VV.comp g f)) =
            MkCell (Src (snd (H.VV.comp g f))) (Trg (fst (H.VV.comp g f)))
                   (Comp (Trg (fst (H.VV.comp g f))) (Trg (snd (H.VV.comp g f)))
                         (Src (snd (H.VV.comp g f)))
                         (Map (fst (H.VV.comp g f))) (Map (snd (H.VV.comp g f))))"
        using assms hcomp_def H.VV.arrE
        by (metis (no_types, lifting))
      also have "... = MkCell (Src ?f2) (Trg ?f1)
                              (Hom (Src ?f2) (Trg ?f1)
                                   (Comp (Trg ?f1) (Trg ?g2) (Src ?f2) (Map ?g1) (Map ?g2))
                                   (Comp (Trg ?f1) (Trg ?f2) (Src ?f2) (Map ?f1) (Map ?f2)))"
      proof -
        have "Src (snd (H.VV.comp g f)) = Src ?f2"
          using assms arr_char src_def H.VV.comp_char H.VV.seq_char\<^sub>S\<^sub>b\<^sub>C
          by (metis (no_types, lifting) H.vseq_implies_hpar(1) Src.simps(1) H.VV.arrE
              H.VV.inclusion H.VxV.comp_arr_dom H.VxV.dom_comp H.VxV.seqE\<^sub>P\<^sub>C)
        moreover have "Trg (fst (H.VV.comp g f)) = Trg ?f1"
          by (metis (no_types, lifting) H.VV.comp_arr_dom H.VV.comp_simp H.VV.seq_char\<^sub>S\<^sub>b\<^sub>C
              H.VxV.arr_char H.VxV.cod_comp H.VxV.comp_cod_arr H.VxV.seqE\<^sub>P\<^sub>C
              H.vseq_implies_hpar(2) Src_trg assms)
        moreover have
            "Comp (Trg (fst (H.VV.comp g f))) (Trg (snd (H.VV.comp g f)))
                  (Src (snd (H.VV.comp g f)))
                  (Map (fst (H.VV.comp g f))) (Map (snd (H.VV.comp g f))) =
             Hom (Src ?f2) (Trg ?f1)
                 (Comp (Trg ?f1) (Trg ?g2) (Src ?f2) (Map ?g1) (Map ?g2))
                 (Comp (Trg ?f1) (Trg ?f2) (Src ?f2) (Map ?f1) (Map ?f2))"
        proof -
          have "Comp (Trg (fst (H.VV.comp g f))) (Trg (snd (H.VV.comp g f)))
                     (Src (snd (H.VV.comp g f)))
                     (Map (fst (H.VV.comp g f))) (Map (snd (H.VV.comp g f))) =
                Comp (Trg ?g1) (Trg ?g2) (Src ?g2)
                     (Map (vcomp ?g1 ?f1)) (Map (vcomp ?g2 ?f2))"
            using assms H.VV.comp_char H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VxV.comp_char by auto  (* 10 sec *)
          also have "... = Comp (Trg ?g1) (Trg ?g2) (Src ?g2)
                                (Hom (Src ?g1) (Trg ?g1) (Map ?g1) (Map ?f1))
                                (Hom (Src ?g2) (Trg ?g2) (Map ?g2) (Map ?f2))"
            using assms H.VV.seq_char\<^sub>S\<^sub>b\<^sub>C Map_vcomp H.VxV.seq_char by auto
          also have "... = Hom (Src ?f2) (Trg ?f1)
                               (Comp (Trg ?f1) (Trg ?g2) (Src ?f2)
                                     (Map ?g1) (Map ?g2))
                               (Comp (Trg ?f1) (Trg ?f2) (Src ?f2)
                                     (Map ?f1) (Map ?f2))"
          proof -
            have 2: "Src ?g1 = Trg ?g2"
              using assms H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C [of g] src_def [of "?g1"] trg_def [of "?g2"] by auto
            have "Comp (Trg ?f1) (Trg ?f2) (Src ?f2)
                       (Hom (Trg ?g2) (Trg ?g1) (Map ?g1) (Map ?f1))
                       (Hom (Src ?g2) (Trg ?g2) (Map ?g2) (Map ?f2)) =
                  Hom (Src ?f2) (Trg ?f1)
                      (Comp (Trg ?f1) (Trg ?f2) (Src ?f2)
                            (Map ?g1) (Map ?g2))
                      (Comp (Trg ?f1) (Trg ?f2) (Src ?f2)
                            (Map ?f1) (Map ?f2))"
            proof -
              have "Comp_f.A1xA2.seq (Map ?g1, Map ?g2) (Map ?f1, Map ?f2)"
                using assms 2 H.VV.seq_char\<^sub>S\<^sub>b\<^sub>C
                by (metis (no_types, lifting) Comp_f.A1xA2.seq_char H.VxV.seqE\<^sub>P\<^sub>C
                    fst_conv seq_char snd_conv)
              moreover have
                "Comp_f.A1xA2.comp (Map ?g1, Map ?g2) (Map ?f1, Map ?f2) =
                 (Hom (Src ?g1) (Trg ?g1) (Map ?g1) (Map ?f1),
                  Hom (Src ?g2) (Trg ?g2) (Map ?g2) (Map ?f2))"
                using assms 2 H.VV.seq_char\<^sub>S\<^sub>b\<^sub>C H.VxV.seqE\<^sub>P\<^sub>C seq_char
                by (metis (no_types, lifting) Comp_f.A1xA2.comp_char fst_conv snd_conv)
              ultimately show ?thesis
                by (metis 2 Comp_f.as_nat_trans.preserves_comp_2 old.prod.case)
            qed
            thus ?thesis using assms 2 H.VV.seq_char\<^sub>S\<^sub>b\<^sub>C H.VxV.seqE\<^sub>P\<^sub>C seq_char
              by (metis (no_types, lifting))
          qed
          finally show ?thesis by blast
        qed
        ultimately show ?thesis by blast
      qed
      also have "... = vcomp (hcomp ?g1 ?g2) (hcomp ?f1 ?f2)"
      proof -
        have 2: "Trg ?g1 = Trg ?f1 \<and> Src ?g2 = Src ?f2 \<and> Src ?f1 = Trg ?f2"
          using assms seq_char H.VV.seq_char\<^sub>S\<^sub>b\<^sub>C H.VxV.seqE\<^sub>P\<^sub>C
          by (metis (no_types, lifting) H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C Src_src Src_trg)
        have "Hom_f.seq (Comp (Trg ?f1) (Trg ?g2) (Src ?f2)
                              (Map ?g1) (Map ?g2))
                        (Comp (Trg ?f1) (Trg ?f2) (Src ?f2)
                              (Map ?f1) (Map ?f2))"
          by (metis (no_types, lifting) 2 Comp_f.A1xA2.seqI\<^sub>P\<^sub>C Comp_f.preserves_seq H.VV.seq_char\<^sub>S\<^sub>b\<^sub>C
              H.VxV.seqE\<^sub>P\<^sub>C arr_char assms case_prod_conv vcomp_def)
        moreover have "?f1 \<noteq> Null \<and> ?f2 \<noteq> Null \<and> src ?f1 = trg ?f2 \<and>
                       ?g1 \<noteq> Null \<and> ?g2 \<noteq> Null \<and> src ?g1 = trg ?g2"
          using assms H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C arr_char assms by blast
        moreover have "Hom_f1.arr (Map ?f1) \<and> Hom_f2.arr (Map ?f2)"
          using assms seq_char H.VV.arrE H.VV.seqE arr_char by fast
        moreover have "Hom_g1.arr (Map ?g1) \<and> Hom_g2.arr (Map ?g2)"
          using assms seq_char H.VV.arrE H.VV.seqE arr_char by meson
        ultimately show ?thesis
          using 1 2 arr_char hcomp_def vcomp_def by auto
      qed
      finally show ?thesis by simp
    qed

    interpretation H: "functor" H.VV.comp vcomp \<open>\<lambda>\<mu>\<nu>. hcomp (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close>
      using hcomp_def arr_hcomp hcomp_vcomp H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VV.dom_char\<^sub>S\<^sub>b\<^sub>C H.VV.cod_char\<^sub>S\<^sub>b\<^sub>C
      by unfold_locales auto

    interpretation H: horizontal_composition vcomp hcomp src trg
      using src_hcomp trg_hcomp arr_char hcomp_def null_char
      by unfold_locales auto

    lemma Map_obj:
    assumes "H.obj a"
    shows "Map a = Id (Src a)" and "Map a = Id (Trg a)"
      using assms H.obj_def Map_src Map_trg H.obj_simps(3) by metis+

    lemma MkCell_simps:
    assumes "A \<in> Obj" and "B \<in> Obj" and "partial_composition.arr (Hom A B) f"
    shows "arr (MkCell A B f)"
    and "src (MkCell A B f) = MkObj A" and "trg (MkCell A B f) = MkObj B"
    and "dom (MkCell A B f) = MkCell A B (partial_composition.dom (Hom A B) f)"
    and "cod (MkCell A B f) = MkCell A B (partial_composition.cod (Hom A B) f)"
      using assms MkCell_in_hom by auto

    text \<open>
      Next, define the associativities and show that they are the components of a
      natural isomorphism.
    \<close>

    definition assoc
    where "assoc f g h \<equiv>
           if H.VVV.ide (f, g, h) then
             MkCell (Src h) (Trg f)
                    (Assoc (Trg f) (Trg g) (Trg h) (Src h) (Map f) (Map g) (Map h))
           else null"

    lemma assoc_in_hom [intro]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "\<guillemotleft>assoc f g h : hcomp (hcomp f g) h \<Rightarrow> hcomp f (hcomp g h)\<guillemotright>"
    proof -
      let ?A = "Src h" and ?B = "Trg h" and ?C = "Trg g" and ?D = "Trg f"
      interpret Hom_f: category \<open>Hom ?C ?D\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Hom_g: category \<open>Hom ?B ?C\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Hom_h: category \<open>Hom ?A ?B\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Hom_gh: product_category \<open>Hom ?B ?C\<close> \<open>Hom ?A ?B\<close> ..
      interpret Hom_f_gh: product_category \<open>Hom ?C ?D\<close> Hom_gh.comp ..
      interpret Comp_fg: binary_functor \<open>Hom ?C ?D\<close> \<open>Hom ?B ?C\<close> \<open>Hom ?B ?D\<close>
                           \<open>\<lambda>(fa, g). Comp ?D ?C ?B fa g\<close>
        using assms arr_char ide_char'' binary_functor_Comp [of ?B ?C ?D] by simp
      interpret \<alpha>: natural_isomorphism Hom_f_gh.comp \<open>Hom (Src h) (Trg f)\<close>
                     \<open>\<lambda>(fa, ga, ha). Comp ?D ?B ?A (Comp ?D ?C ?B fa ga) ha\<close>
                     \<open>\<lambda>(fa, ga, ha). Comp ?D ?C ?A fa (Comp ?C ?B ?A ga ha)\<close>
                     \<open>\<lambda>(fa, ga, ha). Assoc ?D ?C ?B ?A fa ga ha\<close>
        using assms ide_char arr_char natural_isomorphism_Assoc [of ?A ?B ?C ?D]
        by blast
      show ?thesis
      proof
        have 1: "Src f = Trg g \<and> Src g = Trg h"
          using assms src_def trg_def by simp
        have 2: "Hom_f.ide (Map f) \<and> Hom_g.ide (Map g) \<and> Hom_h.ide (Map h)"
          using assms 1 ide_char' [of f] arr_char [of f]
          by (simp add: ide_char'')
        show 3: "arr (assoc f g h)"
          unfolding assoc_def
          using assms arr_char ide_char'' H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C
                src_def trg_def \<alpha>.preserves_reflects_arr [of "(Map f, Map g, Map h)"]
                Hom_f_gh.arr_char Hom_gh.arr_char
          by simp
        show "dom (assoc f g h) = hcomp (hcomp f g) h"
        proof -
          have  "arr (MkCell ?B ?D (Comp ?D ?C ?B (Map f) (Map g)))"
            by (metis assms(1-2,4) 1 Map_hcomp Src_hcomp Trg_hcomp arr_MkCell arr_char
                arr_hcomp(1) ideD(1))
          moreover have "MkObj ?B = trg h"
            using assms ide_char'' arr_char MkCell_Map null_char trg_MkCell by metis
          ultimately show ?thesis
            unfolding hcomp_def
            using assms 1 2 3 arr_char ide_char'' assoc_def dom_MkCell H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C
                  H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C src_MkCell trg_MkCell \<alpha>.preserves_dom
            by force
        qed
        show "cod (assoc f g h) = hcomp f (hcomp g h)"
        proof -
          have "trg g = MkObj ?C"
            using assms ide_char'' arr_char MkCell_Map null_char trg_MkCell by metis
          thus ?thesis
            unfolding hcomp_def
            using assms 2 3 \<alpha>.preserves_cod src_MkCell trg_MkCell H.hseqI' hcomp_def
                  assms arr_char ide_char'' assoc_def cod_MkCell H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C
                  H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C
            by force
        qed
      qed
    qed

    lemma assoc_simps [simp]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "arr (assoc f g h)"
    and "dom (assoc f g h) = hcomp (hcomp f g) h"
    and "cod (assoc f g h) = hcomp f (hcomp g h)"
      using assms assoc_in_hom by auto

    lemma assoc_simps' [simp]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "src (assoc f g h) = src h"
    and "trg (assoc f g h) = trg f"
    and "Src (assoc f g h) = Src h"
    and "Trg (assoc f g h) = Trg f"
    and "Map (assoc f g h) = Assoc (Trg f) (Trg g) (Trg h) (Src h) (Map f) (Map g) (Map h)"
    proof -
      show "src (assoc f g h) = src h"
        using assms src_hcomp src_dom src_def src_MkCell assoc_simps(1) assoc_def
        by (metis (no_types, lifting) ideD(1) not_arr_null)
      show "trg (assoc f g h) = trg f"
        using assms trg_hcomp trg_hcomp trg_cod H.hseqI'
        by (metis assoc_simps(1,3) ideD(1))
      show "Src (assoc f g h) = Src h"
        using assms Src_hcomp Src_dom
        by (metis (no_types, lifting) Src.simps(1) arr_char assoc_def assoc_simps(1) null_char)
      show "Trg (assoc f g h) = Trg f"
        using assms Trg_hcomp Trg_dom
        by (metis (no_types, lifting) Trg.simps(1) arr_char assoc_def assoc_simps(1) null_char)
      show "Map (assoc f g h) = Assoc (Trg f) (Trg g) (Trg h) (Src h) (Map f) (Map g) (Map h)"
        using assms Map_hcomp Map_dom
        by (metis (no_types, lifting) Map.simps(1) arr_char assoc_def assoc_simps(1) null_char)
    qed

    lemma iso_assoc:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "iso (assoc f g h)"
    proof -
      let ?A = "Src h" and ?B = "Trg h" and ?C = "Trg g" and ?D = "Trg f"
      interpret Hom_f: category \<open>Hom ?C ?D\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Hom_g: category \<open>Hom ?B ?C\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Hom_h: category \<open>Hom ?A ?B\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Hom_fg: product_category \<open>Hom ?C ?D\<close> \<open>Hom ?B ?C\<close> ..
      interpret Hom_gh: product_category \<open>Hom ?B ?C\<close> \<open>Hom ?A ?B\<close> ..
      interpret Hom_f_gh: product_category \<open>Hom ?C ?D\<close> Hom_gh.comp ..
      interpret \<alpha>: natural_isomorphism Hom_f_gh.comp \<open>Hom (Src h) (Trg f)\<close>
                     \<open>\<lambda>(fa, ga, ha). Comp ?D ?B ?A (Comp ?D ?C ?B fa ga) ha\<close>
                     \<open>\<lambda>(fa, ga, ha). Comp ?D ?C ?A fa (Comp ?C ?B ?A ga ha)\<close>
                     \<open>\<lambda>(fa, ga, ha). Assoc ?D ?C ?B ?A fa ga ha\<close>
        using assms ide_char arr_char natural_isomorphism_Assoc [of ?A ?B ?C ?D]
        by blast
      show ?thesis
        using assms \<alpha>.components_are_iso [of "(Map f, Map g, Map h)"]
              iso_char H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.ide_char ide_char''
        by (simp add: src_def trg_def)
    qed

    lemma assoc_naturality:
    assumes "arr f" and "arr g" and "arr h" and "src f = trg g" and "src g = trg h"
    shows "vcomp (H.HoVH (f, g, h)) (assoc (dom f) (dom g) (dom h)) =
           vcomp (assoc (cod f) (cod g) (cod h)) (H.HoHV (f, g, h))"
    proof -
      let ?A = "Src h" and ?B = "Trg h" and ?C = "Trg g" and ?D = "Trg f"
      have 1: "Src f = Trg g \<and> Src g = Trg h"
        using assms src_def trg_def by simp
      interpret Hom_f: category \<open>Hom ?C ?D\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Hom_g: category \<open>Hom ?B ?C\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Hom_h: category \<open>Hom ?A ?B\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Hom_fg: product_category \<open>Hom ?C ?D\<close> \<open>Hom ?B ?C\<close> ..
      interpret Hom_gh: product_category \<open>Hom ?B ?C\<close> \<open>Hom ?A ?B\<close> ..
      interpret Hom_fg_h: product_category Hom_fg.comp \<open>Hom ?A ?B\<close> ..
      interpret Hom_f_gh: product_category \<open>Hom ?C ?D\<close> Hom_gh.comp ..
      interpret Hom: category \<open>Hom ?A ?D\<close>
        using assms ide_char arr_char dom_char cod_char category_Hom by simp
      interpret Comp_fg: binary_functor \<open>Hom ?C ?D\<close> \<open>Hom ?B ?C\<close> \<open>Hom ?B ?D\<close>
                           \<open>\<lambda>(f', g). Comp ?D ?C ?B f' g\<close>
        using assms arr_char ide_char'' binary_functor_Comp [of ?B ?C ?D] by simp
      interpret Comp_gh: binary_functor \<open>Hom ?B ?C\<close> \<open>Hom ?A ?B\<close> \<open>Hom ?A ?C\<close>
                           \<open>\<lambda>(f', g). Comp ?C ?B ?A f' g\<close>
        using assms arr_char ide_char'' binary_functor_Comp [of ?A ?B ?C] by simp
      interpret Comp_fg_h: binary_functor \<open>Hom ?B ?D\<close> \<open>Hom ?A ?B\<close> \<open>Hom ?A ?D\<close>
                           \<open>\<lambda>(f', g). Comp ?D ?B ?A f' g\<close>
        using assms arr_char ide_char'' binary_functor_Comp [of ?A ?B ?D] by simp
      interpret Comp_f_gh: binary_functor \<open>Hom ?C ?D\<close> \<open>Hom ?A ?C\<close> \<open>Hom ?A ?D\<close>
                           \<open>\<lambda>(f', g). Comp ?D ?C ?A f' g\<close>
        using assms arr_char ide_char'' binary_functor_Comp [of ?A ?C ?D] by simp
      interpret \<alpha>: natural_isomorphism Hom_f_gh.comp \<open>Hom ?A ?D\<close>
                     \<open>\<lambda>(f', g', h'). Comp ?D ?B ?A (Comp ?D ?C ?B f' g') h'\<close>
                     \<open>\<lambda>(f', g', h'). Comp ?D ?C ?A f' (Comp ?C ?B ?A g' h')\<close>
                     \<open>\<lambda>(f', g', h'). Assoc ?D ?C ?B ?A f' g' h'\<close>
        using assms ide_char arr_char natural_isomorphism_Assoc [of ?A ?B ?C ?D]
        by blast

      have ide_Map_dom:
             "Hom_f.ide (Map (dom f)) \<and> Hom_g.ide (Map (dom g)) \<and> Hom_h.ide (Map (dom h))"
        using assms 1 ide_char'' arr_char by simp
      have ide_Map_cod:
             "Hom_f.ide (Map (cod f)) \<and> Hom_g.ide (Map (cod g)) \<and> Hom_h.ide (Map (cod h))"
        using assms 1 ide_char'' arr_char by simp

      have "vcomp (H.HoVH (f, g, h)) (assoc (dom f) (dom g) (dom h)) =
            vcomp (hcomp f (hcomp g h))
                  (MkCell (Src (dom h)) (Trg (dom f))
                          (Assoc (Trg (dom f)) (Trg (dom g)) (Trg (dom h)) (Src (dom h))
                                 (Map (dom f)) (Map (dom g)) (Map (dom h))))"
        using assms 1 H.HoVH_def H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C
              assoc_def assoc_in_hom
         by simp
      also have "... = MkCell (Src (dom h)) (Trg (dom f))
                              (Hom (Src (dom h)) (Trg (dom f))
                                   (Comp (Trg (dom f)) (Trg g) (Src (dom h)) (Map f)
                                         (Comp (Trg g) (Trg h) (Src (dom h)) (Map g) (Map h)))
                                   (Assoc (Trg (dom f)) (Trg (dom g)) (Trg (dom h)) (Src (dom h))
                                          (Map (dom f)) (Map (dom g)) (Map (dom h))))"
      proof -
        have "Hom.seq (Comp ?D ?C ?A (Map f) (Comp ?C ?B ?A (Map g) (Map h)))
                      (Assoc ?D (Trg (dom g)) (Trg (dom h)) ?A
                             (Map (dom f)) (Map (dom g)) (Map (dom h)))"
        proof (intro Hom.seqI)
          show "Hom.arr (Assoc ?D (Trg (dom g)) (Trg (dom h)) ?A
                               (Map (dom f)) (Map (dom g)) (Map (dom h)))"
          proof -
            have "Hom.arr (Assoc ?D (Trg (dom g)) (Trg (dom h)) ?A
                                 (Map (dom f)) (Map (dom g)) (Map (dom h)))"
              using assms 1 arr_char Trg_dom Src_dom ide_Map_dom
                    \<alpha>.preserves_reflects_arr [of "(Map (dom f), Map (dom g), Map (dom h))"]
              by simp
            thus ?thesis
              using assms 1 arr_char Src_dom Trg_dom assoc_simps(1-2) assoc_def
                    H.VV.ide_char H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C ide_Map_dom
              by simp
          qed
          show "Hom.arr (Comp ?D ?C ?A (Map f) (Comp ?C ?B ?A (Map g) (Map h)))"
          proof -
            have "Hom.arr (Comp ?D ?C ?A (Map f) (Comp ?C ?B ?A (Map g) (Map h)))"
              using assms 1 arr_char
                    Comp_f_gh.preserves_reflects_arr [of "(Map f, Comp ?C ?B ?A (Map g) (Map h))"]
                    Comp_gh.preserves_reflects_arr [of "(Map g, Map h)"] Src_dom Trg_dom
              by simp
            thus ?thesis
              using assms 1 arr_char Src_dom Trg_dom by simp
          qed
          show "Hom.dom (Comp ?D ?C ?A (Map f) (Comp ?C ?B ?A (Map g) (Map h))) =
                Hom.cod (Assoc ?D (Trg (dom g)) (Trg (dom h)) ?A
                        (Map (dom f)) (Map (dom g)) (Map (dom h)))"
          proof -
            have "Hom.cod (Assoc ?D (Trg (dom g)) (Trg (dom h)) ?A
                          (Map (dom f)) (Map (dom g)) (Map (dom h))) =
                  Hom.cod (Map (assoc (dom f) (dom g) (dom h)))"
              using Src_dom Trg_dom assms(1-5) assoc_simps'(5) ide_dom src_dom trg_dom
              by presburger
            also have "... = Comp ?D ?C ?A
                                  (Map (dom f))
                                  (Comp ?C ?B ?A (Map (dom g)) (Map (dom h)))"
            proof -
              have "dom f \<noteq> Null \<and> dom g \<noteq> Null \<and> dom h \<noteq> Null"
                using arr_dom assms not_arr_null null_char by fastforce
              moreover have "Hom.cod (Map (assoc (dom f) (dom g) (dom h))) =
                             Comp ?D ?C ?A
                                  (Map (dom f))
                                  (Comp ?C ?B ?A (Map (dom g)) (Map (dom h)))"
                using assms assoc_simps'(5) ide_Map_dom
                      \<alpha>.preserves_cod [of "(Map (dom f), Map (dom g), Map (dom h))"]
                by simp
              ultimately show ?thesis
                using assms 1 arr_char assoc_def H.VV.ide_char H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C
                      Src_dom Trg_dom ide_Map_dom null_char assoc_simps'(5)
                by simp
            qed
            also have "... =
                       Hom.dom (Comp ?D ?C ?A (Map f) (Comp ?C ?B ?A (Map g) (Map h)))"
            proof -
              have "arr (MkCell ?A ?C (Comp ?C ?B ?A (Map g) (Map h)))"
                using assms 1 arr_char arr_MkCell
                      Comp_gh.preserves_reflects_arr [of "(Map g, Map h)"]
                by simp
              thus ?thesis
                using assms arr_char 1 Map_dom
                      Comp_f_gh.preserves_dom [of "(Map f, Comp ?C ?B ?A (Map g) (Map h))"]
                      Comp_gh.preserves_dom [of "(Map g, Map h)"]
                by simp
            qed
            finally show ?thesis by argo
          qed
        qed
        thus ?thesis
          using assms(1-5) H.hseqI' arr_char vcomp_def by auto
      qed
      also have "... = MkCell (Src h) (Trg f)
                              (Hom (Src h) (Trg f)
                                   (Assoc (Trg f) (Trg (cod g)) (Trg (cod h)) (Src h)
                                          (Map (cod f)) (Map (cod g)) (Map (cod h)))
                                   (Comp (Trg f) (Trg h) (Src h)
                                         (Comp (Trg f) (Trg g) (Src g) (Map f) (Map g)) (Map h)))"
        using assms 1 arr_char \<alpha>.naturality [of "(Map f, Map g, Map h)"] by simp
      also have "... = vcomp (MkCell (Src (cod h)) (Trg (cod f))
                                     (Assoc (Trg (cod f)) (Trg (cod g)) (Trg (cod h)) (Src (cod h))
                                            (Map (cod f)) (Map (cod g)) (Map (cod h))))
                             (hcomp (hcomp f g) h)"
      proof -
        have "arr (MkCell ?B ?D (Comp ?D ?C ?B (Map f) (Map g)))"
          using assms 1 arr_char arr_MkCell
                Comp_fg.preserves_reflects_arr [of "(Map f, Map g)"]
          by simp
        moreover have
                   "Hom.arr (Comp ?D ?B ?A (Comp ?D ?C ?B (Map f) (Map g)) (Map h))"
          using assms 1 arr_char Comp_fg.preserves_reflects_arr [of "(Map f, Map g)"]
                Comp_fg_h.preserves_reflects_arr [of "(Comp ?D ?C ?B (Map f) (Map g), Map h)"]
          by simp
        moreover have "Hom.arr (Assoc ?D (Trg (cod g)) (Trg (cod h)) ?A
                                         (Map (cod f)) (Map (cod g)) (Map (cod h)))"
          using assms 1 arr_char Trg_cod ide_Map_cod
                \<alpha>.preserves_reflects_arr [of "(Map (cod f), Map (cod g), Map (cod h))"]
          by simp
        moreover have "Hom.seq (Assoc ?D (Trg (cod g)) (Trg (cod h)) ?A
                                      (Map (cod f)) (Map (cod g)) (Map (cod h)))
                               (Comp ?D ?B ?A (Comp ?D ?C ?B (Map f) (Map g)) (Map h))"
        proof (intro Hom.seqI)
          show "Hom.arr (Comp ?D ?B ?A (Comp ?D ?C ?B (Map f) (Map g)) (Map h))"
            using assms 1 arr_char Comp_fg.preserves_reflects_arr [of "(Map f, Map g)"]
                  Comp_fg_h.preserves_reflects_arr [of "(Comp ?D ?C ?B (Map f) (Map g), Map h)"]
            by simp
          show "Hom.arr (Assoc ?D (Trg (cod g)) (Trg (cod h)) ?A
                            (Map (cod f)) (Map (cod g)) (Map (cod h)))"
            using assms 1 arr_char Trg_cod ide_Map_cod
                  \<alpha>.preserves_reflects_arr [of "(Map (cod f), Map (cod g), Map (cod h))"]
            by simp
          show "Hom.dom (Assoc ?D (Trg (cod g)) (Trg (cod h)) ?A
                        (Map (cod f)) (Map (cod g)) (Map (cod h))) =
                Hom.cod (Comp ?D ?B ?A (Comp ?D ?C ?B (Map f) (Map g)) (Map h))"
          proof -
            have "Hom.dom (Assoc ?D (Trg (cod g)) (Trg (cod h)) ?A
                          (Map (cod f)) (Map (cod g)) (Map (cod h))) =
                  Hom.dom (Map (assoc (cod f) (cod g) (cod h)))"
              using H.cod_trg Src_cod Trg_cod assms(1-5) assoc_simps'(5) ide_cod src_cod
                    trg.preserves_cod
              by presburger
            also have "... = Comp ?D ?B ?A
                                  (Comp ?D ?C ?B (Map (cod f)) (Map (cod g))) (Map (cod h))"
            proof -
              have "cod f \<noteq> Null \<and> cod g \<noteq> Null \<and> cod h \<noteq> Null"
                using arr_cod assms not_arr_null null_char by fastforce
              moreover have "Hom.dom (Map (assoc (cod f) (cod g) (cod h))) =
                             Comp ?D ?B ?A
                                  (Comp ?D ?C ?B (Map (cod f)) (Map (cod g))) (Map (cod h))"
                using assms assoc_simps'(5) ide_Map_cod
                      \<alpha>.preserves_dom [of "(Map (cod f), Map (cod g), Map (cod h))"]
                by simp
              ultimately show ?thesis
                using assms 1 arr_char assoc_def H.VV.ide_char H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C
                      Src_cod Trg_cod ide_Map_cod null_char assoc_simps'(5)
                by simp
            qed
            also have "... =
                       Hom.cod (Comp ?D ?B ?A (Comp ?D ?C ?B (Map f) (Map g)) (Map h))"
              using assms arr_char 1 Map_cod arr_MkCell
                    Comp_fg_h.preserves_cod [of "(Comp ?D ?C ?B (Map f) (Map g), Map h)"]
                    Comp_fg.preserves_cod [of "(Map f, Map g)"]
                    Comp_fg.preserves_reflects_arr [of "(Map f, Map g)"]
              by simp
            finally show ?thesis by blast
          qed
        qed
        ultimately show ?thesis
          using assms arr_char vcomp_def hcomp_def Src_cod Trg_cod
                H.VV.ide_char H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C src_def trg_def
          by simp
      qed
      also have "... = vcomp (assoc (cod f) (cod g) (cod h)) (H.HoHV (f, g, h))"
        using assms 1 H.HoHV_def H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C
              assoc_def assoc_in_hom
         by simp
      finally show "vcomp (H.HoVH (f, g, h)) (assoc (dom f) (dom g) (dom h)) =
                    vcomp (assoc (cod f) (cod g) (cod h)) (H.HoHV (f, g, h))"
        by blast
    qed

    interpretation \<alpha>\<^sub>0: transformation_by_components H.VVV.comp vcomp H.HoHV H.HoVH
                         \<open>\<lambda>(f, g, h). assoc f g h\<close>
    proof
      fix fgh
      show "H.VVV.ide fgh \<Longrightarrow>
              \<guillemotleft>case fgh of (f, g, h) \<Rightarrow> assoc f g h : H.HoHV fgh \<Rightarrow> H.HoVH fgh\<guillemotright>"
        using assoc_in_hom H.HoHV_def H.HoVH_def H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C
        by (cases fgh) simp
      assume fgh: "H.VVV.arr fgh"
      show "vcomp (case H.VVV.cod fgh of (f, g, h) \<Rightarrow> assoc f g h) (H.HoHV fgh) =
            vcomp (H.HoVH fgh) (case H.VVV.dom fgh of (f, g, h) \<Rightarrow> assoc f g h)"
        using fgh assoc_simps H.HoHV_def assoc_naturality
              H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.dom_char\<^sub>S\<^sub>b\<^sub>C H.VVV.cod_char\<^sub>S\<^sub>b\<^sub>C
        by (cases fgh) simp
    qed

    definition \<a>  ("\<a>[_,_,_]")
    where "\<a> f g h == \<alpha>\<^sub>0.map (f, g, h)"

    lemma \<a>_simp_ide:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "\<a>[f, g, h] =
           MkCell (Src h) (Trg f)
                  (Assoc (Trg f) (Trg g) (Trg h) (Src h) (Map f) (Map g) (Map h))"
      using assms \<a>_def assoc_def assoc_simps' MkCell_Map not_arr_null
            \<alpha>\<^sub>0.map_simp_ide H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C
      by simp

    interpretation \<alpha>: natural_isomorphism H.VVV.comp vcomp H.HoHV H.HoVH
                        \<open>\<lambda>fgh. \<a> (fst fgh) (fst (snd fgh)) (snd (snd fgh))\<close>
    proof -
      interpret \<alpha>: natural_isomorphism H.VVV.comp vcomp H.HoHV H.HoVH \<alpha>\<^sub>0.map
        using \<alpha>\<^sub>0.map_simp_ide iso_assoc H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C
        by unfold_locales auto
      show "natural_isomorphism H.VVV.comp vcomp H.HoHV H.HoVH
              (\<lambda>fgh. \<a> (fst fgh) (fst (snd fgh)) (snd (snd fgh)))"
        using \<alpha>.natural_isomorphism_axioms \<a>_def by simp
    qed

    text \<open>
      What remains is to show that horizontal composition with source or target defines
      fully faithful functors.
    \<close>

    interpretation endofunctor vcomp H.L
        using H.endofunctor_L by auto
    interpretation endofunctor vcomp H.R
      using H.endofunctor_R by auto

    interpretation R: fully_faithful_functor vcomp vcomp H.R
    proof
      show "\<And>f f'. \<lbrakk>par f f'; H.R f = H.R f'\<rbrakk> \<Longrightarrow> f = f'"
      proof -
        fix \<mu> \<mu>'
        assume par: "par \<mu> \<mu>'"
        and eq: "H.R \<mu> = H.R \<mu>'"
        have 1: "Src \<mu>' = Src \<mu> \<and> Trg \<mu>' = Trg \<mu>"
          using par by (metis Src_dom Trg_dom)
        interpret Hom: category \<open>Hom (Src \<mu>) (Trg \<mu>)\<close>
          using par arr_char category_Hom by simp
        let ?R = "\<lambda>f. if Hom.arr f
                      then Comp (Trg \<mu>) (Src \<mu>) (Src \<mu>) f (Id (Src \<mu>))
                      else Hom.null"
        interpret R: fully_faithful_functor \<open>Hom (Src \<mu>) (Trg \<mu>)\<close> \<open>Hom (Src \<mu>) (Trg \<mu>)\<close> ?R
          using par arr_char right_unit_Id by simp
        have R\<mu>: "H.R \<mu> = MkCell (Src \<mu>) (Trg \<mu>)
                                 (Comp (Trg \<mu>) (Src \<mu>) (Src \<mu>) (Map \<mu>) (Id (Src \<mu>)))"
          unfolding hcomp_def
          using par src_def null_char H.trg_src src.preserves_arr by simp
        have R\<mu>': "H.R \<mu>' = MkCell (Src \<mu>) (Trg \<mu>)
                                   (Comp (Trg \<mu>) (Src \<mu>) (Src \<mu>) (Map \<mu>') (Id (Src \<mu>)))"
          unfolding hcomp_def
          using par 1 src_def null_char H.trg_src src.preserves_arr by simp
        have "Map \<mu> = Map \<mu>'"
          using R\<mu> R\<mu>' eq par arr_char eq R.is_faithful
          by (metis "1" Map_cod Map_dom cell.inject)
        thus "\<mu> = \<mu>'"
          using 1 par MkCell_Map by (metis arr_char null_char)
      qed
      show "\<And>f g \<nu>. \<lbrakk>ide f; ide g; \<guillemotleft>\<nu> : H.R f \<Rightarrow> H.R g\<guillemotright>\<rbrakk> \<Longrightarrow> \<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow> g\<guillemotright> \<and> H.R \<mu> = \<nu>"
      proof -
        fix f g \<nu>
        assume f: "ide f" and g: "ide g" and \<nu>: "\<guillemotleft>\<nu> : H.R f \<Rightarrow> H.R g\<guillemotright>"
        interpret Hom: category \<open>Hom (Src \<nu>) (Trg \<nu>)\<close>
          using \<nu> arr_char category_Hom by auto
        let ?R = "\<lambda>f. if Hom.arr f
                      then Comp (Trg \<nu>) (Src \<nu>) (Src \<nu>) f (Id (Src \<nu>))
                      else Hom.null"
        interpret R: fully_faithful_functor \<open>Hom (Src \<nu>) (Trg \<nu>)\<close> \<open>Hom (Src \<nu>) (Trg \<nu>)\<close> ?R
          using \<nu> arr_char right_unit_Id by auto
        have 0: "Src f = Src \<nu> \<and> Trg f = Trg \<nu> \<and> Src g = Src \<nu> \<and> Trg g = Trg \<nu>"
        proof (intro conjI)
          show "Trg f = Trg \<nu>"
            using f \<nu> Trg_dom Trg_hcomp by fastforce
          show "Trg g = Trg \<nu>"
            using g \<nu> Trg_cod Trg_hcomp by fastforce
          show "Src f = Src \<nu>"
          proof -
            have 1: "arr f \<and> dom f = f \<and> cod f = f"
              by (meson f ide_char)
            hence "hcomp f (src f) = dom \<nu>"
              using \<nu> by fastforce
            thus ?thesis
              using 1
              by (metis (no_types) H.trg_src Src.simps(1) Src_hcomp \<nu> dom_char in_homE
                  src.preserves_arr src_def)
          qed
          show "Src g = Src \<nu>"
          proof -
            have 1: "arr g \<and> dom g = g \<and> cod g = g"
              by (meson g ide_char)
            hence "hcomp g (src g) = cod \<nu>"
              using \<nu> by fastforce
            thus ?thesis
              using 1
              by (metis (no_types) H.trg_src Src.simps(1) Src_hcomp \<nu> cod_char in_homE
                  src.preserves_arr src_def)
          qed
        qed
        have 1: "Hom.in_hom (Map \<nu>) (?R (Map f)) (?R (Map g))"
        proof
          show "Hom.arr (Map \<nu>)"
            using \<nu> arr_char by auto
          show "Hom.dom (Map \<nu>) = ?R (Map f)"
          proof -
            have 1: "arr f \<and> dom f = f \<and> cod f = f"
              using f ide_char by blast
            have "dom \<nu> = MkCell (Src \<nu>) (Trg \<nu>) (Hom.dom (Map \<nu>))"
              by (meson \<nu> dom_char in_homE)
            thus ?thesis
              using 1 H.trg_src \<nu> arr_char hcomp_def src.preserves_arr src_def by fastforce
          qed
          show "Hom.cod (Map \<nu>) = ?R (Map g)"
          proof -
            have 1: "arr g \<and> dom g = g \<and> cod g = g"
              using g ide_char by blast
            have "cod \<nu> = MkCell (Src \<nu>) (Trg \<nu>) (Hom.cod (Map \<nu>))"
              by (meson \<nu> cod_char in_homE)
            thus ?thesis
              using 1 H.trg_src \<nu> arr_char hcomp_def src.preserves_arr src_def by fastforce
          qed
        qed
        have 2: "Hom.ide (Map f) \<and> Hom.ide (Map g)"
          using 0 f g arr_char ide_char'' by simp
        obtain x where x: "Hom.in_hom x (Map f) (Map g) \<and> ?R x = Map \<nu>"
          using \<nu> 1 2 R.is_full by blast
        have "\<guillemotleft>MkCell (Src \<nu>) (Trg \<nu>) x : f \<Rightarrow> g\<guillemotright>"
        proof -
          have "arr (MkCell (Src \<nu>) (Trg \<nu>) x)"
            using \<nu> arr_char x by auto
          thus ?thesis
            by (metis 0 Hom.in_homE Map.simps(1) Src.simps(1) Trg.simps(1)
                      cod_char dom_char f g ide_char in_homI x)
        qed
        moreover have "H.R (MkCell (Src \<nu>) (Trg \<nu>) x) = \<nu>"
          using MkCell_Map \<nu> arrI arr_char hcomp_def null_char src.preserves_arr x by auto
        ultimately show "\<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow> g\<guillemotright> \<and> H.R \<mu> = \<nu>" by auto
      qed
    qed

    interpretation L: fully_faithful_functor vcomp vcomp H.L
    proof
      show "\<And>f f'. \<lbrakk>par f f'; H.L f = H.L f'\<rbrakk> \<Longrightarrow> f = f'"
      proof -
        fix \<mu> \<mu>'
        assume par: "par \<mu> \<mu>'"
        and eq: "H.L \<mu> = H.L \<mu>'"
        have 1: "Src \<mu>' = Src \<mu> \<and> Trg \<mu>' = Trg \<mu>"
          using par by (metis Src_dom Trg_dom)
        interpret Hom: category \<open>Hom (Src \<mu>) (Trg \<mu>)\<close>
          using par arr_char category_Hom by simp
        let ?L = "\<lambda>f. if Hom.arr f
                      then Comp (Trg \<mu>) (Trg \<mu>) (Src \<mu>) (Id (Trg \<mu>)) f
                      else Hom.null"
        interpret L: fully_faithful_functor \<open>Hom (Src \<mu>) (Trg \<mu>)\<close> \<open>Hom (Src \<mu>) (Trg \<mu>)\<close> ?L
          using par arr_char left_unit_Id [of "Src \<mu>" "Trg \<mu>"] by simp
        have L\<mu>: "H.L \<mu> = MkCell (Src \<mu>) (Trg \<mu>)
                                 (Comp (Trg \<mu>) (Trg \<mu>) (Src \<mu>) (Id (Trg \<mu>)) (Map \<mu>))"
          unfolding hcomp_def
          using par trg_def null_char H.src_trg trg.preserves_arr by simp
        have L\<mu>': "H.L \<mu>' = MkCell (Src \<mu>) (Trg \<mu>)
                                   (Comp (Trg \<mu>) (Trg \<mu>) (Src \<mu>) (Id (Trg \<mu>)) (Map \<mu>'))"
          unfolding hcomp_def
          using par 1 trg_def null_char H.src_trg trg.preserves_arr by simp
        have "Map \<mu> = Map \<mu>'"
          using L\<mu> L\<mu>' eq par arr_char eq L.is_faithful
          by (metis "1" Map.simps(1) Map_cod Map_dom)
        thus "\<mu> = \<mu>'"
          using 1 par MkCell_Map
          by (metis arr_char null_char)
      qed
      show "\<And>f g \<nu>. \<lbrakk>ide f; ide g; \<guillemotleft>\<nu> : H.L f \<Rightarrow> H.L g\<guillemotright>\<rbrakk> \<Longrightarrow> \<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow> g\<guillemotright> \<and> H.L \<mu> = \<nu>"
      proof -
        fix f g \<nu>
        assume f: "ide f" and g: "ide g" and \<nu>: "\<guillemotleft>\<nu> : H.L f \<Rightarrow> H.L g\<guillemotright>"
        interpret Hom: category \<open>Hom (Src \<nu>) (Trg \<nu>)\<close>
          using \<nu> arr_char category_Hom by auto
        let ?L = "\<lambda>f. if Hom.arr f
                      then Comp (Trg \<nu>) (Trg \<nu>) (Src \<nu>) (Id (Trg \<nu>)) f
                      else Hom.null"
        interpret L: fully_faithful_functor \<open>Hom (Src \<nu>) (Trg \<nu>)\<close> \<open>Hom (Src \<nu>) (Trg \<nu>)\<close> ?L
          using \<nu> arr_char left_unit_Id by auto
        have 0: "Src f = Src \<nu> \<and> Trg f = Trg \<nu> \<and> Src g = Src \<nu> \<and> Trg g = Trg \<nu>"
        proof (intro conjI)
          show "Src f = Src \<nu>"
            using Src_dom Src_hcomp \<nu> f by fastforce
          show "Src g = Src \<nu>"
            using \<nu> g Src_cod Src_hcomp by fastforce
          show "Trg f = Trg \<nu>"
          proof -
            have 1: "arr f \<and> dom f = f \<and> cod f = f"
              by (meson f ide_char)
            hence "hcomp (trg f) f = dom \<nu>"
              using \<nu> by fastforce
            thus ?thesis
              using 1
              by (metis (no_types) H.src_trg Trg.simps(1) Trg_hcomp \<nu> dom_char in_homE
                  trg.preserves_arr trg_def)
          qed
          show "Trg g = Trg \<nu>"
          proof -
            have 1: "arr g \<and> dom g = g \<and> cod g = g"
              by (meson g ide_char)
            hence "hcomp (trg g) g = cod \<nu>"
              using \<nu> by fastforce
            thus ?thesis
              using 1
              by (metis (no_types) H.src_trg Trg.simps(1) Trg_hcomp \<nu> cod_char in_homE
                  trg.preserves_arr trg_def)
          qed
        qed
        have 1: "Hom.in_hom (Map \<nu>) (?L (Map f)) (?L (Map g))"
        proof
          show "Hom.arr (Map \<nu>)"
            using \<nu> arr_char by auto
          show "Hom.dom (Map \<nu>) = ?L (Map f)"
          proof -
            have "dom \<nu> = MkCell (Src \<nu>) (Trg \<nu>) (Hom.dom (Map \<nu>))"
              using \<nu> dom_char [of \<nu>] by auto
            hence "Hom.dom (Map \<nu>) = Map (dom \<nu>)"
              by simp
            also have "... = ?L (Map f)"
              using 0 f \<nu> left_unit_Id [of "Src f" "Trg f"]
              apply (simp add: ide_char'')
              by (metis (no_types, lifting) H.src_trg Map.simps(1) Map_hcomp Trg.simps(1)
                  f ide_char in_homE trg.preserves_arr trg_def)
            finally show ?thesis by blast
          qed
          show "Hom.cod (Map \<nu>) = ?L (Map g)"
          proof -
            have "cod \<nu> = MkCell (Src \<nu>) (Trg \<nu>) (Hom.cod (Map \<nu>))"
              using \<nu> cod_char [of \<nu>] by auto
            hence "Hom.cod (Map \<nu>) = Map (cod \<nu>)"
              by simp
            also have "... = ?L (Map g)"
              using 0 g \<nu> left_unit_Id [of "Src g" "Trg g"]
              apply (simp add: ide_char'')
              by (metis (no_types, lifting) H.src_trg Map.simps(1) Map_hcomp Trg.simps(1)
                  g ide_char in_homE trg.preserves_arr trg_def)
            finally show ?thesis by blast
          qed
        qed
        have 2: "Hom.ide (Map f) \<and> Hom.ide (Map g)"
          using 0 f g arr_char ide_char'' by simp
        obtain x where x: "Hom.in_hom x (Map f) (Map g) \<and> ?L x = Map \<nu>"
          using \<nu> 1 2 L.is_full by blast
        have "\<guillemotleft>MkCell (Src \<nu>) (Trg \<nu>) x : f \<Rightarrow> g\<guillemotright>"
        proof -
          have "arr (MkCell (Src \<nu>) (Trg \<nu>) x)"
            using \<nu> arr_char x by auto
          thus ?thesis
            by (metis 0 Hom.in_homE Map.simps(1) Src.simps(1) Trg.simps(1)
                      cod_char dom_char f g ide_char in_homI x)
        qed
        moreover have "H.L (MkCell (Src \<nu>) (Trg \<nu>) x) = \<nu>"
          using MkCell_Map \<nu> arrI arr_char hcomp_def null_char trg.preserves_arr x by auto
        ultimately show "\<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow> g\<guillemotright> \<and> H.L \<mu> = \<nu>" by auto
      qed
    qed

    text \<open>
      The unit isomorphisms are defined in terms of the specified function \<open>Unit\<close>.
    \<close>

    definition \<i>  ("\<i>[_]")
    where "\<i>[a] \<equiv> MkCell (Src a) (Src a) (Unit (Src a))"

    lemma \<i>_simps [simp]:
    assumes "H.obj a"
    shows "Src \<i>[a] = Src a" and "Trg \<i>[a] = Trg a" and "Map \<i>[a] = Unit (Src a)"
      using assms \<i>_def H.obj_def src_def trg_def
       apply auto
      by (metis Trg.simps(1))

    text \<open>
      The main result: the construction produces a bicategory.
    \<close>

    proposition induces_bicategory:
    shows "bicategory vcomp hcomp \<a> \<i> src trg"
    proof
      fix a
      assume a: "H.obj a"
      have Src_a: "Src a \<in> Obj"
        using a ide_char'' by auto
      interpret Hom: category \<open>Hom (Src a) (Src a)\<close>
        using Src_a category_Hom by auto
      show "\<guillemotleft>\<i> a : hcomp a a \<Rightarrow> a\<guillemotright>"
      proof -
        have "\<guillemotleft>\<i> a : MkCell (Src a) (Src a) (Hom.dom (Unit (Src a)))
                       \<Rightarrow> MkCell (Src a) (Src a) (Hom.cod (Unit (Src a)))\<guillemotright>"
          using a Src_a MkCell_in_hom Unit_in_hom [of "Src a"] \<i>_def
          by simp (metis Hom.in_homE)
        moreover have "MkCell (Src a) (Src a) (Hom.cod (Unit (Src a))) = a"
          using a MkCell_Map H.obj_def Map_obj src_def Src_a Unit_in_hom by force
        moreover have "MkCell (Src a) (Src a) (Hom.dom (Unit (Src a))) = hcomp a a"
          using a H.obj_def Map_hcomp [of a a] Map_obj Src_a Unit_in_hom Src_hcomp Trg_hcomp
          by (metis H.objE Hom.in_homE Trg.simps(1) calculation(2) hcomp_def)
        ultimately show ?thesis by simp
      qed
      show "iso (\<i> a)"
        using a Src_a iso_Unit [of "Src a"] \<open>\<guillemotleft>\<i> a : hcomp a a \<Rightarrow> a\<guillemotright>\<close> iso_char \<i>_def by auto
      next
      show "\<And>f g h k. \<lbrakk>ide f; ide g; ide h; ide k; src f = trg g; src g = trg h; src h = trg k\<rbrakk>
              \<Longrightarrow> vcomp (hcomp f (\<a> g h k)) (vcomp (\<a> f (hcomp g h) k) (hcomp (\<a> f g h) k)) =
                  vcomp (\<a> f g (hcomp h k)) (\<a> (hcomp f g) h k)"
      proof (intro arr_eqI)
        fix f g h k
        assume f: "ide f" and g: "ide g" and h: "ide h" and k: "ide k"
        and fg: "src f = trg g" and gh: "src g = trg h" and hk: "src h = trg k"
        have 1: "\<guillemotleft>hcomp f (\<a> g h k) :
                    hcomp f (hcomp (hcomp g h) k) \<Rightarrow> hcomp f (hcomp g (hcomp h k))\<guillemotright>"
          using f g h k fg gh hk H.VV.in_hom_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C
                assoc_simps \<alpha>\<^sub>0.map_simp_ide H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C
                H.preserves_hom \<a>_def
            by auto
        have 2: "\<guillemotleft>hcomp (\<a> f g h) k :
                    hcomp (hcomp (hcomp f g) h) k \<Rightarrow> hcomp (hcomp f (hcomp g h)) k\<guillemotright>"
          using f g h k fg gh hk H.VV.in_hom_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C
                assoc_simps \<alpha>\<^sub>0.map_simp_ide H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C
                H.preserves_hom \<a>_def
          by auto
        have 3: "\<guillemotleft>\<a> f (hcomp g h) k :
                    hcomp (hcomp f (hcomp g h)) k \<Rightarrow> hcomp f (hcomp (hcomp g h) k)\<guillemotright>"
          using f g h k fg gh hk H.VV.in_hom_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C
                assoc_simps \<alpha>\<^sub>0.map_simp_ide H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C
                H.preserves_hom \<a>_def
          by auto
        have 4: "seq (hcomp f (\<a> g h k)) (vcomp (\<a> f (hcomp g h) k) (hcomp (\<a> f g h) k))"
          using 1 2 3 by auto
        have 5: "seq (\<a> f (hcomp g h) k) (hcomp (\<a> f g h) k)"
          using 2 3 by auto
        have 6: "seq (\<a> f g (hcomp h k)) (\<a> (hcomp f g) h k)"
          using f g h k fg gh hk H.VV.in_hom_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C
                assoc_simps \<alpha>\<^sub>0.map_simp_ide H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C
                H.preserves_hom \<a>_def
          by simp

        let ?LHS = "vcomp (hcomp f (\<a> g h k)) (vcomp (\<a> f (hcomp g h) k) (hcomp (\<a> f g h) k))"
        let ?RHS = "vcomp (\<a> f g (hcomp h k)) (\<a> (hcomp f g) h k)"
        show "arr ?LHS"
          using 4 by simp
        show "arr ?RHS"
          using 6 by simp
        show "Src ?LHS = Src ?RHS"
          using 4 6 f g h k fg gh hk Src_vcomp Src_hcomp
                \<alpha>\<^sub>0.map_simp_ide H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C
                assoc_simps assoc_simps' assoc_def \<a>_def
          by simp
        show "Trg ?LHS = Trg ?RHS"
          using 4 6 f g h k fg gh hk Trg_vcomp Trg_hcomp
                \<alpha>\<^sub>0.map_simp_ide H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C
                assoc_simps assoc_simps' assoc_def \<a>_def
          by simp
        show "Map ?LHS = Map ?RHS"
          using 4 5 6 f g h k fg gh hk \<alpha>\<^sub>0.map_simp_ide H.VVV.ide_char\<^sub>S\<^sub>b\<^sub>C
                H.VV.arr_char\<^sub>S\<^sub>b\<^sub>C H.VVV.arr_char\<^sub>S\<^sub>b\<^sub>C \<a>_def
          apply simp
          using Trg_src Trg_trg pentagon ideD(1) ide_char''
          by (metis (no_types, lifting))
      qed
    qed

    sublocale bicategory vcomp hcomp \<a> \<i> src trg
      using induces_bicategory by simp

  end

  text \<open>
    We now establish some correspondences between the constructed bicategory and the
    originally given data, to provide some assurance that the construction really is doing
    what we think it is.
  \<close>

  context concrete_bicategory
  begin

    lemma Src_in_Obj:
    assumes "arr \<mu>"
    shows "Src \<mu> \<in> Obj"
      using assms arr_char by simp

    lemma Trg_in_Obj:
    assumes "arr \<mu>"
    shows "Trg \<mu> \<in> Obj"
      using assms arr_char by simp

    lemma arr_Map:
    assumes "arr \<mu>"
    shows "partial_composition.arr (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>)"
      using assms arr_char by simp

    lemma obj_MkObj_Src:
    assumes "arr \<mu>"
    shows "obj (MkObj (Src \<mu>))"
      using assms by (simp add: Src_in_Obj obj_MkObj)

    lemma obj_MkObj_Trg:
    assumes "arr \<mu>"
    shows "obj (MkObj (Trg \<mu>))"
      using assms by (simp add: Trg_in_Obj obj_MkObj)

    lemma vcomp_MkCell [simp]:
    assumes "arr (MkCell A B f)" and "arr (MkCell A B g)"
    and "partial_composition.seq (Hom A B) f g"
    shows "vcomp (MkCell A B f) (MkCell A B g) = MkCell A B (Hom A B f g)"
      using assms(1-3) arr_char vcomp_def by fastforce

    lemma hcomp_MkCell [simp]:
    assumes "arr (MkCell B C f)" and "arr (MkCell A B g)"
    shows "hcomp (MkCell B C f) (MkCell A B g) = MkCell A C (Comp C B A f g)"
      by (simp add: assms(1-2) hcomp_def)

    text \<open>
      The objects of the constructed bicategory are in bijective correspondence with
      the originally given set \<open>Obj\<close>, via the inverse mappings \<open>MkObj\<close> and \<open>Src\<close>.
    \<close>

    proposition bij_betw_obj_Obj:
    shows "MkObj \<in> Obj \<rightarrow> Collect obj"
    and "Src \<in> Collect obj \<rightarrow> Obj"
    and "A \<in> Obj \<Longrightarrow> Src (MkObj A) = A"
    and "a \<in> Collect obj \<Longrightarrow> MkObj (Src a) = a"
    and "bij_betw MkObj Obj (Collect obj)"
      using obj_MkObj obj_def Src_in_Obj src_def
          apply auto
      by (intro bij_betwI) auto

    lemma obj_char:
    shows "obj a \<longleftrightarrow> Src a \<in> Obj \<and> a = MkCell (Src a) (Src a) (Id (Src a))"
      using Src_in_Obj bij_betw_obj_Obj(4) obj_MkObj by force

    lemma Map_in_Hom:
    assumes "arr \<mu>"
    shows "partial_composition.in_hom (Hom (Src \<mu>) (Trg \<mu>)) (Map \<mu>) (Map (dom \<mu>)) (Map (cod \<mu>))"
      by (simp add: Src_in_Obj Trg_in_Obj arr_Map assms category.in_homI category_Hom)

    text \<open>
      For each pair of objects \<open>a\<close> and \<open>b\<close>, the hom-category \<open>hhom a b\<close> of the constructed
      bicategory is isomorphic to the originally given category \<open>Hom (Src a) (Src b)\<close>.
    \<close>

    proposition isomorphic_hhom_Hom:
    assumes "obj a" and "obj b"
    shows "isomorphic_categories
             (subcategory.comp vcomp (\<lambda>f. f \<in> hhom a b)) (Hom (Src a) (Src b))"
    proof -
      interpret hom: subcategory vcomp \<open>\<lambda>f. f \<in> hhom a b\<close>
        using assms by unfold_locales auto
      interpret Hom: category \<open>Hom (Src a) (Src b)\<close>
        using assms category_Hom Src_in_Obj obj_def by simp
      let ?Map = "\<lambda>\<mu>. if \<mu> \<in> hhom a b then Map \<mu> else Hom.null"
      let ?MkCell = "\<lambda>\<mu>. if Hom.arr \<mu> then MkCell (Src a) (Src b) \<mu> else hom.null"
      interpret Map: "functor" hom.comp \<open>Hom (Src a) (Src b)\<close> ?Map
      proof
        fix \<mu>
        show "\<not> hom.arr \<mu> \<Longrightarrow> ?Map \<mu> = Hom.null"
          using hom.inclusion [of \<mu>] hom.arr_char\<^sub>S\<^sub>b\<^sub>C by auto
        assume \<mu>: "hom.arr \<mu>"
        have 0: "src \<mu> = a \<and> trg \<mu> = b"
          using \<mu> hom.arrE src_def trg_def
          by (metis in_hhomE mem_Collect_eq)
        have 1: "arr \<mu>"
          using \<mu> hom.inclusion hom.arrE by blast
        have 2: "Src \<mu> = Src a \<and> Trg \<mu> = Trg b"
          using \<mu> 0
          by (metis Src_src Trg_trg hom.arr_char\<^sub>S\<^sub>b\<^sub>C hom.inclusion)
        show "Hom.arr (?Map \<mu>)"
          using 0 1 arr_Map [of \<mu>] \<mu> by auto
        show "Hom.dom (?Map \<mu>) = ?Map (hom.dom \<mu>)"
        proof -
          have "Hom.dom (?Map \<mu>) = Map (dom \<mu>)"
            using \<mu> hom.arrE by fastforce
          thus ?thesis
            by (metis \<mu> hom.arrE hom.arr_dom hom.dom_simp)
        qed
        show "Hom.cod (?Map \<mu>) = ?Map (hom.cod \<mu>)"
        proof -
          have "Hom.cod (?Map \<mu>) = Map (cod \<mu>)"
            using \<mu> hom.arrE by fastforce
          thus ?thesis
            by (metis \<mu> hom.arrE hom.arr_cod hom.cod_simp)
        qed
        next
        fix \<mu> \<nu>
        assume \<mu>\<nu>: "hom.seq \<mu> \<nu>"
        show "?Map (hom.comp \<mu> \<nu>) = Hom (Src a) (Src b) (?Map \<mu>) (?Map \<nu>)"
        proof -
          have 1: "hom.arr \<nu> \<and> hom.arr \<mu> \<and> seq \<mu> \<nu>"
            using \<mu>\<nu> hom.seq_char\<^sub>S\<^sub>b\<^sub>C by blast
          hence 2: "hom.comp \<mu> \<nu> = vcomp \<mu> \<nu>"
            using hom.comp_char by auto
          have 3: "\<mu> \<in> hhom a b"
            using 1 hom.arrE by blast
          have "Src a = Src \<mu>"
            using 3 by (metis Trg_src in_hhomE mem_Collect_eq obj_def)
          moreover have "Src b = Trg \<mu>"
            using 3 by (metis Trg_src Trg_trg in_hhomE mem_Collect_eq obj_def)
          ultimately show ?thesis
            using 1 2 Map_vcomp \<mu>\<nu> hom.arrE by presburger
        qed
      qed
      interpret MkCell: "functor" \<open>Hom (Src a) (Src b)\<close> hom.comp ?MkCell
      proof
        fix \<mu>
        show "\<not> Hom.arr \<mu> \<Longrightarrow> ?MkCell \<mu> = hom.null"
          by simp
        assume \<mu>: "Hom.arr \<mu>"
        show 1: "hom.arr (?MkCell \<mu>)"
          using assms obj_def \<mu> hom.arr_char\<^sub>S\<^sub>b\<^sub>C arr_MkCell src_def arr_char by auto
        show "hom.dom (?MkCell \<mu>) = ?MkCell (Hom.dom \<mu>)"
              using assms 1 \<mu> hom.dom_char\<^sub>S\<^sub>b\<^sub>C src_def arr_char obj_def Src_in_Obj by simp
        show "hom.cod (?MkCell \<mu>) = ?MkCell (Hom.cod \<mu>)"
              using assms 1 \<mu> hom.cod_char\<^sub>S\<^sub>b\<^sub>C src_def arr_char obj_def Src_in_Obj by simp
        next
        fix \<mu> \<nu>
        assume \<mu>\<nu>: "Hom.seq \<mu> \<nu>"
        have 1: "hom.arr (?MkCell \<mu>)"
          using assms obj_def \<mu>\<nu> hom.arr_char\<^sub>S\<^sub>b\<^sub>C src_def arr_char by auto
        have 2: "hom.arr (?MkCell \<nu>)"
          using assms obj_def \<mu>\<nu> hom.arr_char\<^sub>S\<^sub>b\<^sub>C src_def arr_char by auto
        have 3: "hom.dom (?MkCell \<mu>) = hom.cod (?MkCell \<nu>)"
          using \<mu>\<nu> 1 2 hom.dom_char\<^sub>S\<^sub>b\<^sub>C dom_char hom.cod_char\<^sub>S\<^sub>b\<^sub>C cod_char arr_char by auto
        have 4: "seq (?MkCell \<mu>) (?MkCell \<nu>)"
          by (metis 1 2 3 hom.arrE hom.cod_simp hom.comp_closed hom.dom_simp hom.inclusion)
        have "hom.comp (?MkCell \<mu>) (?MkCell \<nu>) =
               vcomp (MkCell (Src a) (Src b) \<mu>) (MkCell (Src a) (Src b) \<nu>)"
          using \<mu>\<nu> 1 2 4 hom.comp_char by auto
        also have "... = MkCell (Src a) (Src b) (Hom (Src a) (Src b) \<mu> \<nu>)"
          using \<mu>\<nu> 4 vcomp_char [of "MkCell (Src a) (Src b) \<mu>" "MkCell (Src a) (Src b) \<nu>"]
          by auto
        also have "... = ?MkCell (Hom (Src a) (Src b) \<mu> \<nu>)"
          using \<mu>\<nu> by simp
        finally show "?MkCell (Hom (Src a) (Src b) \<mu> \<nu>) = hom.comp (?MkCell \<mu>) (?MkCell \<nu>)"
          by simp
      qed
      interpret inverse_functors hom.comp \<open>Hom (Src a) (Src b)\<close> ?MkCell ?Map
      proof
        show "?MkCell o ?Map = hom.map"
        proof
          fix \<mu>
          have "\<mu> \<notin> hhom a b \<Longrightarrow> (?MkCell o ?Map) \<mu> = hom.map \<mu>"
            using o_apply hom.is_extensional hom.arr_char\<^sub>S\<^sub>b\<^sub>C by simp
          moreover have "\<mu> \<in> hhom a b \<Longrightarrow> (?MkCell o ?Map) \<mu> = hom.map \<mu>"
          proof -
            assume \<mu>: "\<mu> \<in> hhom a b"
            have "(?MkCell o ?Map) \<mu> = MkCell (Src a) (Src b) (Map \<mu>)"
              using \<mu> arr_char src_def trg_def by auto
            also have "... = \<mu>"
              using \<mu> MkCell_Map arr_char null_char by auto
            also have "... = hom.map \<mu>"
              using \<mu> hom.arrI\<^sub>S\<^sub>b\<^sub>C hom.map_def by presburger
            finally show "(?MkCell o ?Map) \<mu> = hom.map \<mu>"
              by simp
          qed
          ultimately show "(?MkCell o ?Map) \<mu> = hom.map \<mu>"
            by blast
        qed
        show "?Map o ?MkCell = Hom.map"
        proof
          fix \<mu>
          have "\<not> Hom.arr \<mu> \<Longrightarrow> (?Map o ?MkCell) \<mu> = Hom.map \<mu>"
            using Hom.is_extensional hom.null_char by auto
          moreover have "Hom.arr \<mu> \<Longrightarrow> (?Map o ?MkCell) \<mu> = Hom.map \<mu>"
          proof -
            assume \<mu>: "Hom.arr \<mu>"
            have "in_hhom (MkCell (Src a) (Src b) \<mu>) a b"
              using \<mu> MkCell.preserves_reflects_arr [of \<mu>] hom.arr_char\<^sub>S\<^sub>b\<^sub>C by simp
            thus "(?Map o ?MkCell) \<mu> = Hom.map \<mu>"
              using \<mu> by simp
          qed
          ultimately show "(?Map o ?MkCell) \<mu> = Hom.map \<mu>"
            by blast
        qed
      qed
      show ?thesis ..
    qed

  end

end
