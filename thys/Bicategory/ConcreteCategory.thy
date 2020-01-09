(*  Title:       ConcreteCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Concrete Categories"

text \<open>
  This theory developed in this section provides a uniform way to construct a category from
  specified sets of objects and arrows, and proves that the identities and arrows of the
  constructed category are appropriately in bijective correspondence with the given sets.
  This is a general tool that would more properly appear in @{session \<open>Category3\<close>}
  (see \cite{Category3-AFP}) and it will likely eventually be moved there.
\<close>

theory ConcreteCategory
imports Category3.Category
begin

  datatype ('o, 'a) arr =
    Null
  | MkArr 'o 'o 'a

  locale concrete_category =
    fixes Obj :: "'o set"
    and Hom :: "'o \<Rightarrow> 'o \<Rightarrow> 'a set"
    and Id :: "'o \<Rightarrow> 'a"
    and Comp :: "'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>'a"
    assumes Id_in_Hom: "A \<in> Obj \<Longrightarrow> Id A \<in> Hom A A"
    and Comp_in_Hom: "\<lbrakk> A \<in> Obj; B \<in> Obj; C \<in> Obj; f \<in> Hom A B; g \<in> Hom B C \<rbrakk>
                         \<Longrightarrow> Comp C B A g f \<in> Hom A C"
    and Comp_Hom_Id: "\<lbrakk> A \<in> Obj; f \<in> Hom A B \<rbrakk> \<Longrightarrow> Comp B A A f (Id A) = f"
    and Comp_Id_Hom: "\<lbrakk> B \<in> Obj; f \<in> Hom A B \<rbrakk> \<Longrightarrow> Comp B B A (Id B) f = f"
    and Comp_assoc: "\<lbrakk> A \<in> Obj; B \<in> Obj; C \<in> Obj; D \<in> Obj;
                       f \<in> Hom A B; g \<in> Hom B C; h \<in> Hom C D \<rbrakk> \<Longrightarrow>
                        Comp D C A h (Comp C B A g f) = Comp D B A (Comp D C B h g) f"
  begin

    abbreviation MkIde :: "'o \<Rightarrow> ('o, 'a) arr"
    where "MkIde A \<equiv> MkArr A A (Id A)"

    fun Dom :: "('o, 'a) arr \<Rightarrow> 'o"
    where "Dom (MkArr A _ _) = A"
        | "Dom _ = undefined"

    fun Cod
    where "Cod (MkArr _ B _) = B"
        | "Cod _ = undefined"

    fun Map
    where "Map (MkArr _ _ F) = F"
        | "Map _ = undefined"

    abbreviation Arr
    where "Arr f \<equiv> f \<noteq> Null \<and> Dom f \<in> Obj \<and> Cod f \<in> Obj \<and> Map f \<in> Hom (Dom f) (Cod f)"

    abbreviation Ide
    where "Ide a \<equiv> a \<noteq> Null \<and> Dom a \<in> Obj \<and> Cod a = Dom a \<and> Map a = Id (Dom a)"

    definition comp :: "('o, 'a) arr comp"
    where "comp g f \<equiv> if Arr f \<and> Arr g \<and> Dom g = Cod f then
                         MkArr (Dom f) (Cod g) (Comp (Cod g) (Dom g) (Dom f) (Map g) (Map f))
                      else
                         Null"

    interpretation partial_magma comp
      using comp_def by (unfold_locales, metis)

    lemma null_char:
    shows "null = Null"
    proof -
      let ?P = "\<lambda>n. \<forall>f. comp n f = n \<and> comp f n = n"
      have "Null = null"
        using comp_def null_def the1_equality [of ?P] by metis
      thus ?thesis by simp
    qed

    lemma ide_char:
    shows "ide f \<longleftrightarrow> Ide f"
    proof
      assume f: "Ide f"
      show "ide f"
      proof (unfold ide_def)
        have "comp f f \<noteq> null"
          using f comp_def null_char Id_in_Hom by auto
        moreover have "\<forall>g. (comp g f \<noteq> null \<longrightarrow> comp g f = g) \<and>
                           (comp f g \<noteq> null \<longrightarrow> comp f g = g)"
        proof
          fix g
          have "comp g f \<noteq> null \<longrightarrow> comp g f = g"
            using f comp_def null_char Comp_Hom_Id Id_in_Hom
            by (cases g, auto)
          moreover have "comp f g \<noteq> null \<longrightarrow> comp f g = g"
            using f comp_def null_char Comp_Id_Hom Id_in_Hom
            by (cases g, auto)
          ultimately show "(comp g f \<noteq> null \<longrightarrow> comp g f = g) \<and>
                           (comp f g \<noteq> null \<longrightarrow> comp f g = g)"
            by blast
        qed
        ultimately show "comp f f \<noteq> null \<and>
                         (\<forall>g. (comp g f \<noteq> null \<longrightarrow> comp g f = g) \<and>
                         (comp f g \<noteq> null \<longrightarrow> comp f g = g))"
          by blast
      qed
      next
      assume f: "ide f"
      have 1: "Arr f \<and> Dom f = Cod f"
        using f ide_def comp_def null_char by metis
      moreover have "Map f = Id (Dom f)"
      proof -
        let ?g = "MkIde (Dom f)"
        have g: "Arr f \<and> Arr ?g \<and> Dom ?g = Cod f"
          using 1 Id_in_Hom
          by (intro conjI, simp_all)
        hence 2: "comp ?g f \<noteq> null"
          using 1 comp_def null_char by simp
        have "comp ?g f = MkArr (Dom f) (Dom f) (Map f)"
          using g comp_def Comp_Id_Hom by auto
        moreover have "comp ?g f = ?g"
          using f 2 ide_def by blast
        ultimately show ?thesis by simp
      qed
      ultimately show "Ide f" by auto
    qed

    lemma ide_MkIde [simp]:
    assumes "A \<in> Obj"
    shows "ide (MkIde A)"
      using assms ide_char Id_in_Hom by simp

    lemma in_domains_char:
    shows "a \<in> domains f \<longleftrightarrow> Arr f \<and> a = MkIde (Dom f)"
    proof
      assume a: "a \<in> domains f"
      have "Ide a"
        using a domains_def ide_char comp_def null_char by auto
      moreover have "Arr f \<and> Dom f = Cod a"
      proof -
        have "comp f a \<noteq> null"
          using a domains_def by simp
        thus ?thesis
          using a domains_def comp_def [of f a] null_char by metis
      qed
      ultimately show "Arr f \<and> a = MkIde (Dom f)"
        by (cases a, auto)
      next
      assume a: "Arr f \<and> a = MkIde (Dom f)"
      show "a \<in> domains f"
        using a Id_in_Hom comp_def null_char domains_def by auto
    qed

    lemma in_codomains_char:
    shows "b \<in> codomains f \<longleftrightarrow> Arr f \<and> b = MkIde (Cod f)"
    proof
      assume b: "b \<in> codomains f"
      have "Ide b"
        using b codomains_def ide_char comp_def null_char by auto
      moreover have "Arr f \<and> Dom b = Cod f"
      proof -
        have "comp b f \<noteq> null"
          using b codomains_def by simp
        thus ?thesis
          using b codomains_def comp_def [of b f] null_char by metis
      qed
      ultimately show "Arr f \<and> b = MkIde (Cod f)"
        by (cases b, auto)
      next
      assume b: "Arr f \<and> b = MkIde (Cod f)"
      show "b \<in> codomains f"
        using b Id_in_Hom comp_def null_char codomains_def by auto
    qed

    lemma arr_char:
    shows "arr f \<longleftrightarrow> Arr f"
      using arr_def in_domains_char in_codomains_char by auto

    lemma arrI:
    assumes "f \<noteq> Null" and "Dom f \<in> Obj" "Cod f \<in> Obj" "Map f \<in> Hom (Dom f) (Cod f)"
    shows "arr f"
      using assms arr_char by blast

    lemma arrE:
    assumes "arr f"
    and "\<lbrakk> f \<noteq> Null; Dom f \<in> Obj; Cod f \<in> Obj; Map f \<in> Hom (Dom f) (Cod f) \<rbrakk> \<Longrightarrow> T"
    shows T
      using assms arr_char by simp

    lemma arr_MkArr [simp]:
    assumes "A \<in> Obj" and "B \<in> Obj" and "f \<in> Hom A B"
    shows "arr (MkArr A B f)"
      using assms arr_char by simp

    lemma MkArr_Map:
    assumes "arr f"
    shows "MkArr (Dom f) (Cod f) (Map f) = f"
      using assms arr_char by (cases f, auto)

    lemma Arr_comp:
    assumes "arr f" and "arr g" and "Dom g = Cod f"
    shows "Arr (comp g f)"
      unfolding comp_def
      using assms arr_char Comp_in_Hom by simp

    lemma Dom_comp [simp]:
    assumes "arr f" and "arr g" and "Dom g = Cod f"
    shows "Dom (comp g f) = Dom f"
      unfolding comp_def
      using assms arr_char by simp

    lemma Cod_comp [simp]:
    assumes "arr f" and "arr g" and "Dom g = Cod f"
    shows "Cod (comp g f) = Cod g"
      unfolding comp_def
      using assms arr_char by simp

    lemma Map_comp [simp]:
    assumes "arr f" and "arr g" and "Dom g = Cod f"
    shows "Map (comp g f) = Comp (Cod g) (Dom g) (Dom f) (Map g) (Map f)"
      unfolding comp_def
      using assms arr_char by simp

    lemma seq_char:
    shows "seq g f \<longleftrightarrow> arr f \<and> arr g \<and> Dom g = Cod f"
      using arr_char not_arr_null null_char comp_def Arr_comp by metis

    interpretation category comp
    proof
      show "\<And>g f. comp g f \<noteq> null \<Longrightarrow> seq g f"
        using arr_char comp_def null_char Comp_in_Hom by auto
      show 1: "\<And>f. (domains f \<noteq> {}) = (codomains f \<noteq> {})"
        using in_domains_char in_codomains_char by auto
      show "\<And>f g h. seq h g \<Longrightarrow> seq (comp h g) f \<Longrightarrow> seq g f"
        by (auto simp add: seq_char)
      show "\<And>f g h. seq h (comp g f) \<Longrightarrow> seq g f \<Longrightarrow> seq h g"
        using seq_char comp_def Comp_in_Hom by (metis Cod_comp)
      show "\<And>f g h. seq g f \<Longrightarrow> seq h g \<Longrightarrow> seq (comp h g) f"
        using Comp_in_Hom
        by (auto simp add: comp_def seq_char)
      show "\<And>g f h. seq g f \<Longrightarrow> seq h g \<Longrightarrow> comp (comp h g) f = comp h (comp g f)"
        using seq_char comp_def Comp_assoc Comp_in_Hom Dom_comp Cod_comp Map_comp
        by auto
    qed

    proposition is_category:
    shows "category comp"
      ..

    lemma dom_char:
    shows "dom f = (if arr f then MkIde (Dom f) else null)"
      using dom_def in_domains_char dom_in_domains has_domain_iff_arr by auto

    lemma cod_char:
    shows "cod f = (if arr f then MkIde (Cod f) else null)"
      using cod_def in_codomains_char cod_in_codomains has_codomain_iff_arr by auto

    lemma comp_char:
    shows "comp g f = (if seq g f then
                         MkArr (Dom f) (Cod g) (Comp (Cod g) (Dom g) (Dom f) (Map g) (Map f))
                       else
                         null)"
      using comp_def seq_char arr_char null_char by auto

    lemma in_hom_char:
    shows "in_hom f a b \<longleftrightarrow> arr f \<and> ide a \<and> ide b \<and> Dom f = Dom a \<and> Cod f = Dom b"
    proof
      show "in_hom f a b \<Longrightarrow> arr f \<and> ide a \<and> ide b \<and> Dom f = Dom a \<and> Cod f = Dom b"
        using arr_char dom_char cod_char by auto
      show "arr f \<and> ide a \<and> ide b \<and> Dom f = Dom a \<and> Cod f = Dom b \<Longrightarrow> in_hom f a b"
        using arr_char dom_char cod_char ide_char Id_in_Hom MkArr_Map in_homI by metis
    qed

    lemma Dom_in_Obj:
    assumes "arr f"
    shows "Dom f \<in> Obj"
      using assms arr_char by simp

    lemma Cod_in_Obj:
    assumes "arr f"
    shows "Cod f \<in> Obj"
      using assms arr_char by simp

    lemma Map_in_Hom:
    assumes "arr f"
    shows "Map f \<in> Hom (Dom f) (Cod f)"
      using assms arr_char by simp

    lemma MkArr_in_hom:
    assumes "A \<in> Obj" and "B \<in> Obj" and "f \<in> Hom A B"
    shows "in_hom (MkArr A B f) (MkIde A) (MkIde B)"
      using assms arr_char dom_char cod_char ide_MkIde by auto

    lemma Dom_dom [simp]:
    assumes "arr f"
    shows "Dom (dom f) = Dom f"
      using assms MkArr_Map dom_char by simp

    lemma Cod_dom [simp]:
    assumes "arr f"
    shows "Cod (dom f) = Dom f"
      using assms MkArr_Map dom_char by simp

    lemma Dom_cod [simp]:
    assumes "arr f"
    shows "Dom (cod f) = Cod f"
      using assms MkArr_Map cod_char by simp

    lemma Cod_cod [simp]:
    assumes "arr f"
    shows "Cod (cod f) = Cod f"
      using assms MkArr_Map cod_char by simp

    lemma Map_dom [simp]:
    assumes "arr f"
    shows "Map (dom f) = Id (Dom f)"
      using assms MkArr_Map dom_char by simp

    lemma Map_cod [simp]:
    assumes "arr f"
    shows "Map (cod f) = Id (Cod f)"
      using assms MkArr_Map cod_char by simp

    lemma Map_ide:
    assumes "ide a"
    shows "Map a = Id (Dom a)" and "Map a = Id (Cod a)"
    proof -
      show "Map a = Id (Dom a)"
        using assms ide_char dom_char [of a] Map_dom ideD(1) by metis
      show "Map a = Id (Cod a)"
        using assms ide_char dom_char [of a] Map_cod ideD(1) by metis
    qed

    (*
     * TODO: The next two ought to be simps, but they cause looping when they find themselves
     * in combination with dom_char and cod_char.
     *)
    lemma MkIde_Dom:
    assumes "arr a"
    shows "MkIde (Dom a) = dom a"
      using assms arr_char dom_char by (cases a, auto)

    lemma MkIde_Cod:
    assumes "arr a"
    shows "MkIde (Cod a) = cod a"
      using assms arr_char cod_char by (cases a, auto)

    lemma MkIde_Dom' [simp]:
    assumes "ide a"
    shows "MkIde (Dom a) = a"
      using assms MkIde_Dom by simp

    lemma MkIde_Cod' [simp]:
    assumes "ide a"
    shows "MkIde (Cod a) = a"
      using assms MkIde_Cod by simp

    lemma dom_MkArr [simp]:
    assumes "arr (MkArr A B F)"
    shows "dom (MkArr A B F) = MkIde A"
      using assms dom_char by simp

    lemma cod_MkArr [simp]:
    assumes "arr (MkArr A B F)"
    shows "cod (MkArr A B F) = MkIde B"
      using assms cod_char by simp

    lemma comp_MkArr [simp]:
    assumes "arr (MkArr A B F)" and "arr (MkArr B C G)"
    shows "comp (MkArr B C G) (MkArr A B F) = MkArr A C (Comp C B A G F)"
      using assms comp_char [of "MkArr B C G" "MkArr A B F"] by simp

    proposition bij_betw_ide_Obj:
    shows "MkIde \<in> Obj \<rightarrow> Collect ide"
    and "Dom \<in> Collect ide \<rightarrow> Obj"
    and "A \<in> Obj \<Longrightarrow> Dom (MkIde A) = A"
    and "a \<in> Collect ide \<Longrightarrow> MkIde (Dom a) = a"
    and "bij_betw Dom (Collect ide) Obj"
    proof -
      show 1: "MkIde \<in> Obj \<rightarrow> Collect ide"
        using ide_MkIde by simp
      show 2: "Dom \<in> Collect ide \<rightarrow> Obj"
        using arr_char ideD(1) by simp
      show 3: "\<And>A. A \<in> Obj \<Longrightarrow> Dom (MkIde A) = A"
        by simp
      show 4: "\<And>a. a \<in> Collect ide \<Longrightarrow> MkIde (Dom a) = a"
        using MkIde_Dom by simp
      show "bij_betw Dom (Collect ide) Obj"
        using 1 2 3 4 bij_betwI by blast
    qed

    proposition bij_betw_hom_Hom:
    assumes "ide a" and "ide b"
    shows "Map \<in> hom a b \<rightarrow> Hom (Dom a) (Dom b)"
    and "MkArr (Dom a) (Dom b) \<in> Hom (Dom a) (Dom b) \<rightarrow> hom a b"
    and "\<And>f. f \<in> hom a b \<Longrightarrow> MkArr (Dom a) (Dom b) (Map f) = f"
    and "\<And>F. F \<in> Hom (Dom a) (Dom b) \<Longrightarrow> Map (MkArr (Dom a) (Dom b) F) = F"
    and "bij_betw Map (hom a b) (Hom (Dom a) (Dom b))"
    proof -
      show 1: "Map \<in> hom a b \<rightarrow> Hom (Dom a) (Dom b)"
        using Map_in_Hom cod_char dom_char in_hom_char by fastforce
      show 2: "MkArr (Dom a) (Dom b) \<in> Hom (Dom a) (Dom b) \<rightarrow> hom a b"
        using assms Dom_in_Obj MkArr_in_hom [of "Dom a" "Dom b"] by simp
      show 3: "\<And>f. f \<in> hom a b \<Longrightarrow> MkArr (Dom a) (Dom b) (Map f) = f"
        using MkArr_Map by auto
      show 4: "\<And>F. F \<in> Hom (Dom a) (Dom b) \<Longrightarrow> Map (MkArr (Dom a) (Dom b) F) = F"
        by simp
      show "bij_betw Map (hom a b) (Hom (Dom a) (Dom b))"
        using 1 2 3 4 bij_betwI by blast
    qed

    lemma arr_eqI:
    assumes "arr t" and "arr t'" and "Dom t = Dom t'" and "Cod t = Cod t'" and "Map t = Map t'"
    shows "t = t'"
      using assms MkArr_Map by metis

  end

  sublocale concrete_category \<subseteq> category comp
    using is_category by auto

end
