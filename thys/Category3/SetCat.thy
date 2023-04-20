(*  Title:       SetCat
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter SetCat

theory SetCat
imports SetCategory ConcreteCategory
begin

  text\<open>
    This theory proves the consistency of the \<open>set_category\<close> locale by giving
    a particular concrete construction of an interpretation for it.
    Applying the general construction given by @{locale concrete_category},
    we define arrows to be terms \<open>MkArr A B F\<close>, where \<open>A\<close> and \<open>B\<close> are sets
    and \<open>F\<close> is an extensional function that maps \<open>A\<close> to \<open>B\<close>.
\<close>

  text\<open>
    This locale uses an extra dummy parameter just to fix the element type for sets.
    Without this, a type is used for each interpretation, which makes it impossible to
    construct set categories whose element types are related to the context.
    An additional parameter, @{term Setp}, allows some control over which subsets of
    the element type are assumed to correspond to objects of the category.
  \<close>

  locale setcat =
  fixes elem_type :: "'e itself"
  and Setp :: "'e set \<Rightarrow> bool"
  assumes Setp_singleton: "Setp {x}"
  and Setp_respects_subset: "A' \<subseteq> A \<Longrightarrow> Setp A \<Longrightarrow> Setp A'"
  and union_preserves_Setp: "\<lbrakk> Setp A; Setp B \<rbrakk> \<Longrightarrow> Setp (A \<union> B)"
  begin

    lemma finite_imp_Setp: "finite A \<Longrightarrow> Setp A"
      using Setp_singleton
      by (metis finite_induct insert_is_Un Setp_respects_subset singleton_insert_inj_eq
          union_preserves_Setp)

    type_synonym 'b arr = "('b set, 'b \<Rightarrow> 'b) concrete_category.arr"

    interpretation S: concrete_category \<open>Collect Setp\<close> \<open>\<lambda>A B. extensional A \<inter> (A \<rightarrow> B)\<close>
                        \<open>\<lambda>A. \<lambda>x \<in> A. x\<close> \<open>\<lambda>C B A g f. compose A g f\<close>
      using compose_Id Id_compose
      apply unfold_locales
          apply auto[3]
       apply blast
      by (metis IntD2 compose_assoc)

    abbreviation comp :: "'e setcat.arr comp"     (infixr "\<cdot>" 55)
    where "comp \<equiv> S.COMP"
    notation S.in_hom                               ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma is_category:
    shows "category comp"
      using S.category_axioms by simp

    lemma MkArr_expansion:
    assumes "S.arr f"
    shows "f = S.MkArr (S.Dom f) (S.Cod f) (\<lambda>x \<in> S.Dom f. S.Map f x)"
    proof (intro S.arr_eqI)
      show "S.arr f" by fact
      show "S.arr (S.MkArr (S.Dom f) (S.Cod f) (\<lambda>x \<in> S.Dom f. S.Map f x))"
        using assms S.arr_char
        by (metis (mono_tags, lifting) Int_iff S.MkArr_Map extensional_restrict)
      show "S.Dom f = S.Dom (S.MkArr (S.Dom f) (S.Cod f) (\<lambda>x \<in> S.Dom f. S.Map f x))"
        by simp
      show "S.Cod f = S.Cod (S.MkArr (S.Dom f) (S.Cod f) (\<lambda>x \<in> S.Dom f. S.Map f x))"
        by simp
      show "S.Map f = S.Map (S.MkArr (S.Dom f) (S.Cod f) (\<lambda>x \<in> S.Dom f. S.Map f x))"
        using assms S.arr_char
        by (metis (mono_tags, lifting) Int_iff S.MkArr_Map extensional_restrict)
    qed

    lemma arr_char:
    shows "S.arr f \<longleftrightarrow> f \<noteq> S.Null \<and> Setp (S.Dom f) \<and> Setp (S.Cod f) \<and>
                       S.Map f \<in> extensional (S.Dom f) \<inter> (S.Dom f \<rightarrow> S.Cod f)"
      using S.arr_char by auto

    lemma terminal_char:
    shows "S.terminal a \<longleftrightarrow> (\<exists>x. a = S.MkIde {x})"
    proof
      show "\<exists>x. a = S.MkIde {x} \<Longrightarrow> S.terminal a"
      proof -
        assume a: "\<exists>x. a = S.MkIde {x}"
        from this obtain x where x: "a = S.MkIde {x}" by blast
        have "S.terminal (S.MkIde {x})"
        proof
          show 1: "S.ide (S.MkIde {x})"
            using finite_imp_Setp S.ide_MkIde by auto
          show "\<And>a. S.ide a \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> S.MkIde {x}\<guillemotright>"
          proof
            fix a :: "'e setcat.arr"
            assume a: "S.ide a"
            show "\<guillemotleft>S.MkArr (S.Dom a) {x} (\<lambda>_\<in>S.Dom a. x) : a \<rightarrow> S.MkIde {x}\<guillemotright>"
            proof
              show 2: "S.arr (S.MkArr (S.Dom a) {x} (\<lambda>_ \<in> S.Dom a. x))"
                using a 1 S.arr_MkArr [of "S.Dom a" "{x}"] S.ide_char\<^sub>C\<^sub>C by force
              show "S.dom (S.MkArr (S.Dom a) {x} (\<lambda>_ \<in> S.Dom a. x)) = a"
                using a 2 S.dom_MkArr by force
              show "S.cod (S.MkArr (S.Dom a) {x} (\<lambda>_\<in>S.Dom a. x)) = S.MkIde {x}"
                using 2 S.cod_MkArr by blast
            qed
            fix f :: "'e setcat.arr"
            assume f: "\<guillemotleft>f : a \<rightarrow> S.MkIde {x}\<guillemotright>"
            show "f = S.MkArr (S.Dom a) {x} (\<lambda>_ \<in> S.Dom a. x)"
            proof -
              have 1: "S.Dom f = S.Dom a \<and> S.Cod f = {x}"
                using a f by (metis (mono_tags, lifting) S.Dom.simps(1) S.in_hom_char)
              moreover have "S.Map f = (\<lambda>_ \<in> S.Dom a. x)"
              proof
                fix z
                have "z \<notin> S.Dom a \<Longrightarrow> S.Map f z = (\<lambda>_ \<in> S.Dom a. x) z"
                  using f 1 MkArr_expansion
                  by (metis (mono_tags, lifting) S.Map.simps(1) S.in_homE restrict_apply)
                moreover have "z \<in> S.Dom a \<Longrightarrow> S.Map f z = (\<lambda>_ \<in> S.Dom a. x) z"
                  using f 1 arr_char [of f] by fastforce
                ultimately show "S.Map f z = (\<lambda>_ \<in> S.Dom a. x) z" by auto
              qed
              ultimately show ?thesis
               using f MkArr_expansion [of f] by fastforce
            qed
          qed
        qed
        thus "S.terminal a" using x by simp
      qed
      show "S.terminal a \<Longrightarrow> \<exists>x. a = S.MkIde {x}"
      proof -
        assume a: "S.terminal a"
        hence ide_a: "S.ide a" using S.terminal_def by auto
        have 1: "\<exists>!x. x \<in> S.Dom a"
        proof -
          have "S.Dom a = {} \<Longrightarrow> \<not>S.terminal a"
          proof -
            assume "S.Dom a = {}"
            hence 1: "a = S.MkIde {}"
              using S.MkIde_Dom' \<open>S.ide a\<close> by fastforce
            have "\<And>f. f \<in> S.hom (S.MkIde {undefined}) (S.MkIde ({} :: 'e set))
                         \<Longrightarrow> S.Map f \<in> {undefined} \<rightarrow> {}"
            proof -
              fix f
              assume f: "f \<in> S.hom (S.MkIde {undefined}) (S.MkIde ({} :: 'e set))"
              show "S.Map f \<in> {undefined} \<rightarrow> {}"
                using f MkArr_expansion arr_char [of f] S.in_hom_char by auto
            qed
            hence "S.hom (S.MkIde {undefined}) a = {}" using 1 by auto
            moreover have "S.ide (S.MkIde {undefined})"
              using finite_imp_Setp
              by (metis (mono_tags, lifting) finite.intros(1-2) S.ide_MkIde mem_Collect_eq)
            ultimately show "\<not>S.terminal a" by blast
          qed
          moreover have "\<And>x x'. x \<in> S.Dom a \<and> x' \<in> S.Dom a \<and> x \<noteq> x' \<Longrightarrow> \<not>S.terminal a"
          proof -
            fix x x'
            assume 1: "x \<in> S.Dom a \<and> x' \<in> S.Dom a \<and> x \<noteq> x'"
            let ?f = "S.MkArr {undefined} (S.Dom a) (\<lambda>_ \<in> {undefined}. x)"
            let ?f' = "S.MkArr {undefined} (S.Dom a) (\<lambda>_ \<in> {undefined}. x')"
            have "S.par ?f ?f'"
            proof -
              have "\<guillemotleft>?f : S.MkIde {undefined} \<rightarrow> a\<guillemotright>"
              proof
                show 2: "S.arr ?f"
                proof (intro S.arr_MkArr)
                  show "{undefined} \<in> {A. Setp A}"
                    by (simp add: finite_imp_Setp)
                  show "S.Dom a \<in> {A. Setp A}"
                    using ide_a S.ide_char\<^sub>C\<^sub>C by blast
                  show "(\<lambda>_ \<in> {undefined}. x) \<in> extensional {undefined} \<inter> ({undefined} \<rightarrow> S.Dom a)"
                    using 1 by blast
                qed
                show "S.dom ?f = S.MkIde {undefined}"
                  using 2 S.dom_MkArr by auto
                show "S.cod ?f = a"
                  using 2 S.cod_MkArr ide_a by force
              qed
              moreover have "\<guillemotleft>?f' : S.MkIde {undefined} \<rightarrow> a\<guillemotright>"
              proof
                show 2: "S.arr ?f'"
                proof (intro S.arr_MkArr)
                  show "{undefined} \<in> {A. Setp A}"
                    by (simp add: finite_imp_Setp)
                  show "S.Dom a \<in> {A. Setp A}"
                    using ide_a S.ide_char\<^sub>C\<^sub>C by blast
                  show "(\<lambda>_ \<in> {undefined}. x') \<in> extensional {undefined} \<inter> ({undefined} \<rightarrow> S.Dom a)"
                    using 1 by blast
                qed
                show "S.dom ?f' = S.MkIde {undefined}"
                  using 2 S.dom_MkArr by auto
                show "S.cod ?f' = a"
                  using 2 S.cod_MkArr ide_a by force
              qed
              ultimately show ?thesis
                by (metis (no_types, lifting) S.in_homE)
            qed
            moreover have "?f \<noteq> ?f'"
              using 1 by (metis S.arr.inject restrict_apply' singletonI)
            ultimately show "\<not>S.terminal a"
              using S.cod_MkArr ide_a S.terminal_arr_unique [of ?f ?f'] by auto
          qed
          ultimately show ?thesis
            using a by auto
        qed
        hence "S.Dom a = {THE x. x \<in> S.Dom a}"
          using theI [of "\<lambda>x. x \<in> S.Dom a"] by auto
        hence "a = S.MkIde {THE x. x \<in> S.Dom a}"
          using a S.terminal_def by (metis (mono_tags, lifting) S.MkIde_Dom')
        thus "\<exists>x. a = S.MkIde {x}"
          by auto
      qed
    qed

    definition IMG :: "'e setcat.arr \<Rightarrow> 'e setcat.arr"
    where "IMG f = S.MkIde (S.Map f ` S.Dom f)"
  
    interpretation S: set_category_data comp IMG
      ..

    lemma terminal_unity:
    shows "S.terminal S.unity"
      using terminal_char S.unity_def someI_ex [of S.terminal]
      by (metis (mono_tags, lifting))
  
    text\<open>
      The inverse maps @{term arr_of} and @{term elem_of} are used to pass back and forth between
      the inhabitants of type @{typ 'a} and the corresponding terminal objects.
      These are exported so that a client of the theory can relate the concrete
      element type @{typ 'a} to the otherwise abstract arrow type.
\<close>

    definition arr_of :: "'e \<Rightarrow> 'e setcat.arr"
    where "arr_of x \<equiv> S.MkIde {x}"
  
    definition elem_of :: "'e setcat.arr \<Rightarrow> 'e"
    where "elem_of t \<equiv> the_elem (S.Dom t)"

    abbreviation U
    where "U \<equiv> elem_of S.unity"
  
    lemma arr_of_mapsto:
    shows "arr_of \<in> UNIV \<rightarrow> S.Univ"
      using terminal_char arr_of_def by fast
    
    lemma elem_of_mapsto:
    shows "elem_of \<in> Univ \<rightarrow> UNIV"
      by auto
    
    lemma elem_of_arr_of [simp]:
    shows "elem_of (arr_of x) = x"
      by (simp add: elem_of_def arr_of_def)
    
    lemma arr_of_elem_of [simp]:
    assumes "t \<in> S.Univ"
    shows "arr_of (elem_of t) = t"
      using assms terminal_char arr_of_def elem_of_def
      by (metis (mono_tags, lifting) mem_Collect_eq elem_of_arr_of)
  
    lemma inj_arr_of:
    shows "inj arr_of"
      by (metis elem_of_arr_of injI)
  
    lemma bij_arr_of:
    shows "bij_betw arr_of UNIV S.Univ"
    proof (intro bij_betwI)
      show "\<And>x :: 'e. elem_of (arr_of x) = x" by simp
      show "\<And>t. t \<in> S.Univ \<Longrightarrow> arr_of (elem_of t) = t" by simp
      show "arr_of \<in> UNIV \<rightarrow> S.Univ" using arr_of_mapsto by auto
      show "elem_of \<in> Collect S.terminal \<rightarrow> UNIV" by auto
    qed
  
    lemma bij_elem_of:
    shows "bij_betw elem_of S.Univ UNIV"
    proof (intro bij_betwI)
      show "\<And>t. t \<in> S.Univ \<Longrightarrow> arr_of (elem_of t) = t" by simp
      show "\<And>x. x \<in> UNIV \<Longrightarrow> elem_of (arr_of x) = x" by simp
      show "elem_of \<in> S.Univ \<rightarrow> UNIV" using elem_of_mapsto by auto
      show "arr_of \<in> UNIV \<rightarrow> S.Univ" using arr_of_mapsto by auto
    qed

    lemma elem_of_img_arr_of_img [simp]:
    shows "elem_of ` arr_of ` A = A"
      by force

    lemma arr_of_img_elem_of_img [simp]:
    assumes "A \<subseteq> S.Univ"
    shows "arr_of ` elem_of ` A = A"
      using assms by force

    lemma Dom_terminal:
    assumes "S.terminal t"
    shows "S.Dom t = {elem_of t}"
      using assms arr_of_def
      by (metis (mono_tags, lifting) S.Dom.simps(1) elem_of_def terminal_char the_elem_eq)

    text\<open>
      The image of a point @{term "p \<in> hom unity a"} is a terminal object, which is given
      by the formula @{term "(arr_of o Fun p o elem_of) unity"}.
\<close>

    lemma IMG_point:
    assumes "\<guillemotleft>p : S.unity \<rightarrow> a\<guillemotright>"
    shows "IMG \<in> S.hom S.unity a \<rightarrow> S.Univ"
    and "IMG p = (arr_of o S.Map p o elem_of) S.unity"
    proof -
      show "IMG \<in> S.hom S.unity a \<rightarrow> S.Univ"
      proof
        fix f
        assume f: "f \<in> S.hom S.unity a"
        have "S.terminal (S.MkIde (S.Map f ` S.Dom S.unity))"
        proof -
          obtain u :: 'e where u: "S.unity = S.MkIde {u}"
            using terminal_unity terminal_char
            by (metis (mono_tags, lifting))
          have "S.Map f ` S.Dom S.unity = {S.Map f u}"
            using u by simp
          thus ?thesis
            using terminal_char by auto
        qed
        hence "S.MkIde (S.Map f ` S.Dom S.unity) \<in> S.Univ" by simp
        moreover have "S.MkIde (S.Map f ` S.Dom S.unity) = IMG f"
          using f IMG_def S.in_hom_char
          by (metis (mono_tags, lifting) mem_Collect_eq)
        ultimately show "IMG f \<in> S.Univ" by auto
      qed
      have "IMG p = S.MkIde (S.Map p ` S.Dom p)" using IMG_def by blast
      also have "... = S.MkIde (S.Map p ` {U})"
        using assms S.in_hom_char terminal_unity Dom_terminal
        by (metis (mono_tags, lifting))
      also have "... = (arr_of o S.Map p o elem_of) S.unity" by (simp add: arr_of_def)
      finally show "IMG p = (arr_of o S.Map p o elem_of) S.unity" using assms by auto
    qed
  
    text\<open>
      The function @{term IMG} is injective on @{term "hom unity a"} and its inverse takes
      a terminal object @{term t} to the arrow in @{term "hom unity a"} corresponding to the
      constant-@{term t} function.
\<close>

    abbreviation MkElem :: "'e setcat.arr => 'e setcat.arr => 'e setcat.arr"
    where "MkElem t a \<equiv> S.MkArr {U} (S.Dom a) (\<lambda>_ \<in> {U}. elem_of t)"

    lemma MkElem_in_hom:
    assumes "S.arr f" and "x \<in> S.Dom f"
    shows "\<guillemotleft>MkElem (arr_of x) (S.dom f) : S.unity \<rightarrow> S.dom f\<guillemotright>"
    proof -
      have "(\<lambda>_ \<in> {U}. elem_of (arr_of x)) \<in> {U} \<rightarrow> S.Dom (S.dom f)"
        using assms S.dom_char [of f] by simp
      moreover have "S.MkIde {U} = S.unity"
        using terminal_char terminal_unity
        by (metis (mono_tags, lifting) elem_of_arr_of arr_of_def)
      moreover have "S.MkIde (S.Dom (S.dom f)) = S.dom f"
        using assms S.dom_char S.MkIde_Dom' S.ide_dom by blast
      ultimately show ?thesis
        using assms S.MkArr_in_hom [of "{U}" "S.Dom (S.dom f)" "\<lambda>_ \<in> {U}. elem_of (arr_of x)"]
        by (metis (no_types, lifting) S.Dom.simps(1) S.Dom_in_Obj IntI S.arr_dom S.ideD(1)
            restrict_extensional S.terminal_def terminal_unity)
    qed

    lemma MkElem_IMG:
    assumes "p \<in> S.hom S.unity a"
    shows "MkElem (IMG p) a = p"
    proof -
      have 0: "IMG p = arr_of (S.Map p U)"
        using assms IMG_point(2) by auto
      have 1: "S.Dom p = {U}"
        using assms terminal_unity Dom_terminal
        by (metis (mono_tags, lifting) S.in_hom_char mem_Collect_eq)
      moreover have "S.Cod p = S.Dom a"
        using assms
        by (metis (mono_tags, lifting) S.in_hom_char mem_Collect_eq)
      moreover have "S.Map p = (\<lambda>_ \<in> {U}. elem_of (IMG p))"
      proof
        fix e
        show "S.Map p e = (\<lambda>_ \<in> {U}. elem_of (IMG p)) e"
        proof -
          have "S.Map p e = (\<lambda>x \<in> S.Dom p. S.Map p x) e"
            using assms MkArr_expansion [of p]
            by (metis (mono_tags, lifting) CollectD S.Map.simps(1) S.in_homE)
          also have "... = (\<lambda>_ \<in> {U}. elem_of (IMG p)) e"
            using assms 0 1 by simp
          finally show ?thesis by blast
        qed
      qed
      ultimately show "MkElem (IMG p) a = p"
        using assms S.MkArr_Map CollectD
        by (metis (mono_tags, lifting) S.in_homE mem_Collect_eq)
    qed

    lemma inj_IMG:
    assumes "S.ide a"
    shows "inj_on IMG (S.hom S.unity a)"
    proof (intro inj_onI)
      fix x y
      assume x: "x \<in> S.hom S.unity a"
      assume y: "y \<in> S.hom S.unity a"
      assume eq: "IMG x = IMG y"
      show "x = y"
      proof (intro S.arr_eqI)
        show "S.arr x" using x by blast
        show "S.arr y" using y by blast
        show "S.Dom x = S.Dom y"
          using x y S.in_hom_char by (metis (mono_tags, lifting) CollectD)
        show "S.Cod x = S.Cod y"
          using x y S.in_hom_char by (metis (mono_tags, lifting) CollectD)
        show "S.Map x = S.Map y"
        proof -
          have "\<And>a. y \<in> S.hom S.unity a \<Longrightarrow> S.MkArr {U} (S.Dom a) (\<lambda>e\<in>{U}. elem_of (IMG x)) = y"
            using MkElem_IMG eq by presburger
          hence "y = x"
            using MkElem_IMG x y by blast
          thus ?thesis by meson
        qed
      qed
    qed

    lemma set_char:
    assumes "S.ide a"
    shows "S.set a = arr_of ` S.Dom a"
    proof
      show "S.set a \<subseteq> arr_of ` S.Dom a"
      proof
        fix t
        assume "t \<in> S.set a"
        from this obtain p where p: "\<guillemotleft>p : S.unity \<rightarrow> a\<guillemotright> \<and> t = IMG p"
          using S.set_def by blast
        have "t = (arr_of o S.Map p o elem_of) S.unity"
          using p IMG_point(2) by blast
        moreover have "(S.Map p o elem_of) S.unity \<in> S.Dom a"
          using p arr_char S.in_hom_char Dom_terminal terminal_unity
          by (metis (mono_tags, lifting) IntD2 Pi_split_insert_domain o_apply)
        ultimately show "t \<in> arr_of ` S.Dom a" by simp
      qed
      show "arr_of ` S.Dom a \<subseteq> S.set a"
      proof
        fix t
        assume "t \<in> arr_of ` S.Dom a"
        from this obtain x where x: "x \<in> S.Dom a \<and> t = arr_of x" by blast
        let ?p = "MkElem (arr_of x) a"
        have p: "?p \<in> S.hom S.unity a"
          using assms x MkElem_in_hom [of "S.dom a"] S.ideD(1-2) by force
        moreover have "IMG ?p = t"
          using p x elem_of_arr_of IMG_def arr_of_def
          by (metis (no_types, lifting) S.Dom.simps(1) S.Map.simps(1) image_empty
              image_insert image_restrict_eq)
        ultimately show "t \<in> S.set a" using S.set_def by blast
      qed
    qed
  
    lemma Map_via_comp:
    assumes "S.arr f"
    shows "S.Map f = (\<lambda>x \<in> S.Dom f. S.Map (f \<cdot> MkElem (arr_of x) (S.dom f)) U)"
    proof
      fix x
      have "x \<notin> S.Dom f \<Longrightarrow> S.Map f x = (\<lambda>x \<in> S.Dom f. S.Map (f \<cdot> MkElem (arr_of x) (S.dom f)) U) x"
        using assms arr_char [of f] IntD1 extensional_arb restrict_apply by fastforce
      moreover have
           "x \<in> S.Dom f \<Longrightarrow> S.Map f x = (\<lambda>x \<in> S.Dom f. S.Map (f \<cdot> MkElem (arr_of x) (S.dom f)) U) x"
      proof -
        assume x: "x \<in> S.Dom f"
        let ?X = "MkElem (arr_of x) (S.dom f)"
        have "\<guillemotleft>?X : S.unity \<rightarrow> S.dom f\<guillemotright>"
          using assms x MkElem_in_hom by auto
        moreover have "S.Dom ?X = {U} \<and> S.Map ?X = (\<lambda>_ \<in> {U}. x)"
          using x by simp
        ultimately have
          "S.Map (f \<cdot> MkElem (arr_of x) (S.dom f)) = compose {U} (S.Map f) (\<lambda>_ \<in> {U}. x)"
          using assms x S.Map_comp [of "MkElem (arr_of x) (S.dom f)" f]
          by (metis (mono_tags, lifting) S.Cod.simps(1) S.Dom_dom S.arr_iff_in_hom S.seqE S.seqI')
        thus ?thesis
          using x by (simp add: compose_eq restrict_apply' singletonI)
      qed
      ultimately show "S.Map f x = (\<lambda>x \<in> S.Dom f. S.Map (f \<cdot> MkElem (arr_of x) (S.dom f)) U) x"
        by auto
    qed

    lemma arr_eqI':
    assumes "S.par f f'" and "\<And>t. \<guillemotleft>t : S.unity \<rightarrow> S.dom f\<guillemotright> \<Longrightarrow> f \<cdot> t = f' \<cdot> t"
    shows "f = f'"
    proof (intro S.arr_eqI)
      show "S.arr f" using assms by simp
      show "S.arr f'" using assms by simp
      show "S.Dom f = S.Dom f'"
        using assms by (metis (mono_tags, lifting) S.Dom_dom)
      show "S.Cod f = S.Cod f'"
        using assms by (metis (mono_tags, lifting) S.Cod_cod)
      show "S.Map f = S.Map f'"
      proof
        have 1: "\<And>x. x \<in> S.Dom f \<Longrightarrow> \<guillemotleft>MkElem (arr_of x) (S.dom f) : S.unity \<rightarrow> S.dom f\<guillemotright>"
          using MkElem_in_hom by (metis (mono_tags, lifting) assms(1))
        fix x
        show "S.Map f x = S.Map f' x"
          using assms 1 \<open>S.Dom f = S.Dom f'\<close> by (simp add: Map_via_comp)
      qed
    qed

    lemma Setp_elem_of_img:
    assumes "A \<in> S.set ` Collect S.ide"
    shows "Setp (elem_of ` A)"
    proof -
      obtain a where a: "S.ide a \<and> S.set a = A"
        using assms by blast
      have "elem_of ` S.set a = S.Dom a"
      proof -
        have "S.set a = arr_of ` S.Dom a"
        using a set_char by blast
        moreover have "elem_of ` arr_of ` S.Dom a = S.Dom a"
          using elem_of_arr_of by force
        ultimately show ?thesis by presburger
      qed
      thus ?thesis
        using a S.ide_char\<^sub>C\<^sub>C by auto
    qed

    lemma set_MkIde_elem_of_img:
    assumes "A \<subseteq> S.Univ" and "S.ide (S.MkIde (elem_of ` A))"
    shows "S.set (S.MkIde (elem_of ` A)) = A"
    proof -
      have "S.Dom (S.MkIde (elem_of ` A)) = elem_of ` A"
        by simp
      moreover have "arr_of ` elem_of ` A = A"
        using assms arr_of_elem_of by force
      ultimately show ?thesis
        using assms Setp_elem_of_img set_char S.ide_MkIde by auto
    qed

    (*
     * We need this result, which characterizes what sets of terminals correspond
     * to sets.
     *)
    lemma set_img_Collect_ide_iff:
    shows "A \<in> S.set ` Collect S.ide \<longleftrightarrow> A \<subseteq> S.Univ \<and> Setp (elem_of ` A)"
    proof
      show "A \<in> S.set ` Collect S.ide \<Longrightarrow> A \<subseteq> S.Univ \<and> Setp (elem_of ` A)"
        using set_char arr_of_mapsto Setp_elem_of_img by auto
      assume A: "A \<subseteq> S.Univ \<and> Setp (elem_of ` A)"
      have "S.ide (S.MkIde (elem_of ` A))"
        using A S.ide_MkIde by blast
      moreover have "S.set (S.MkIde (elem_of ` A)) = A"
        using A calculation set_MkIde_elem_of_img by presburger
      ultimately show "A \<in> S.set ` Collect S.ide" by blast
    qed

    text\<open>
      The main result, which establishes the consistency of the \<open>set_category\<close> locale
      and provides us with a way of obtaining ``set categories'' at arbitrary types.
\<close>

    theorem is_set_category:
    shows "set_category comp (\<lambda>A. A \<subseteq> S.Univ \<and> Setp (elem_of ` A))"
    proof
      show "\<exists>img :: 'e setcat.arr \<Rightarrow> 'e setcat.arr.
                       set_category_given_img comp img (\<lambda>A. A \<subseteq> S.Univ \<and> Setp (elem_of ` A))"
      proof
        show "set_category_given_img comp IMG (\<lambda>A. A \<subseteq> S.Univ \<and> Setp (elem_of ` A))"
        proof
          show "S.Univ \<noteq> {}" using terminal_char by blast
          fix a :: "'e setcat.arr"
          assume a: "S.ide a"
          show "S.set a \<subseteq> S.Univ \<and> Setp (elem_of ` S.set a)"
            using a set_img_Collect_ide_iff by auto
          show "inj_on IMG (S.hom S.unity a)" using a inj_IMG terminal_unity by blast
          next
          fix t :: "'e setcat.arr"
          assume t: "S.terminal t"
          show "t \<in> IMG ` S.hom S.unity t"
          proof -
            have "t \<in> S.set t"
              using t set_char [of t]
              by (metis (mono_tags, lifting) S.Dom.simps(1) image_insert insertI1 arr_of_def
                  terminal_char S.terminal_def)
            thus ?thesis
              using t S.set_def [of t] by simp
          qed
          next
          show "\<And>A. A \<subseteq> S.Univ \<and> Setp (elem_of ` A) \<Longrightarrow> \<exists>a. S.ide a \<and> S.set a = A"
            using set_img_Collect_ide_iff by fast
          next
          fix a b :: "'e setcat.arr"
          assume a: "S.ide a" and b: "S.ide b" and ab: "S.set a = S.set b"
          show "a = b"
            using a b ab set_char inj_arr_of inj_image_eq_iff S.dom_char S.in_homE S.ide_in_hom
            by (metis (mono_tags, lifting))
          next
          fix f f' :: "'e setcat.arr"
          assume par: "S.par f f'" and ff': "\<And>x. \<guillemotleft>x : S.unity \<rightarrow> S.dom f\<guillemotright> \<Longrightarrow> f \<cdot> x = f' \<cdot> x"
          show "f = f'" using par ff' arr_eqI' by blast
          next
          fix a b :: "'e setcat.arr" and F :: "'e setcat.arr \<Rightarrow> 'e setcat.arr"
          assume a: "S.ide a" and b: "S.ide b" and F: "F \<in> S.hom S.unity a \<rightarrow> S.hom S.unity b"
          show "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : S.unity \<rightarrow> S.dom f\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
          proof
            let ?f = "S.MkArr (S.Dom a) (S.Dom b) (\<lambda>x \<in> S.Dom a. S.Map (F (MkElem (arr_of x) a)) U)"
            have 1: "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright>"
            proof -
              have "(\<lambda>x \<in> S.Dom a. S.Map (F (MkElem (arr_of x) a)) U)
                      \<in> extensional (S.Dom a) \<inter> (S.Dom a \<rightarrow> S.Dom b)"
              proof
                show "(\<lambda>x \<in> S.Dom a. S.Map (F (MkElem (arr_of x) a)) U) \<in> extensional (S.Dom a)"
                  using a F by simp
                show "(\<lambda>x \<in> S.Dom a. S.Map (F (MkElem (arr_of x) a)) U) \<in> S.Dom a \<rightarrow> S.Dom b"
                proof
                  fix x
                  assume x: "x \<in> S.Dom a"
                  have "MkElem (arr_of x) a \<in> S.hom S.unity a"
                    using x a MkElem_in_hom [of a x] S.ide_char S.ideD(1-2) by force
                  hence 1: "F (MkElem (arr_of x) a) \<in> S.hom S.unity b"
                    using F by auto
                  moreover have "S.Dom (F (MkElem (arr_of x) a)) = {U}"
                    using 1 MkElem_IMG
                    by (metis (mono_tags, lifting) S.Dom.simps(1))
                  moreover have "S.Cod (F (MkElem (arr_of x) a)) = S.Dom b"
                    using 1 by (metis (mono_tags, lifting) CollectD S.in_hom_char)
                  ultimately have "S.Map (F (MkElem (arr_of x) a)) \<in> {U} \<rightarrow> S.Dom b"
                    using arr_char [of "F (MkElem (arr_of x) a)"] by blast
                  thus "S.Map (F (MkElem (arr_of x) a)) U \<in> S.Dom b" by blast
                qed
              qed
              hence "\<guillemotleft>?f : S.MkIde (S.Dom a) \<rightarrow> S.MkIde (S.Dom b)\<guillemotright>"
                using a b S.MkArr_in_hom S.ide_char\<^sub>C\<^sub>C by blast
              thus ?thesis
                using a b by simp
            qed
            moreover have "\<And>x. \<guillemotleft>x : S.unity \<rightarrow> S.dom ?f\<guillemotright> \<Longrightarrow> ?f \<cdot> x = F x"
            proof -
              fix x
              assume x: "\<guillemotleft>x : S.unity \<rightarrow> S.dom ?f\<guillemotright>"
              have 2: "x = MkElem (IMG x) a"
                using a x 1 MkElem_IMG [of x a]
                by (metis (mono_tags, lifting) S.in_homE mem_Collect_eq)
              moreover have 5: "S.Dom x = {U} \<and> S.Cod x = S.Dom a \<and>
                                S.Map x = (\<lambda>_ \<in> {U}. elem_of (IMG x))"
                using x 2
                by (metis (no_types, lifting) S.Cod.simps(1) S.Dom.simps(1) S.Map.simps(1))
              moreover have "S.Cod ?f = S.Dom b" using 1 by simp
              ultimately have
                   3: "?f \<cdot> x =
                       S.MkArr {U} (S.Dom b) (compose {U} (S.Map ?f) (\<lambda>_ \<in> {U}. elem_of (IMG x)))"
                by (metis (no_types, lifting) "1" S.Map.simps(1) S.comp_MkArr S.in_homE x)
              have 4: "compose {U} (S.Map ?f) (\<lambda>_ \<in> {U}. elem_of (IMG x)) = S.Map (F x)"
              proof
                fix y
                have "y \<notin> {U} \<Longrightarrow>
                        compose {U} (S.Map ?f) (\<lambda>_ \<in> {U}. elem_of (IMG x)) y = S.Map (F x) y"
                proof -
                  assume y: "y \<notin> {U}"
                  have "compose {U} (S.Map ?f) (\<lambda>_ \<in> {U}. elem_of (IMG x)) y = undefined"
                    using y compose_def extensional_arb by simp
                  also have "... = S.Map (F x) y"
                  proof -
                    have 5: "F x \<in> S.hom S.unity b" using x F 1 by fastforce
                    hence "S.Dom (F x) = {U}"
                      by (metis (mono_tags, lifting) "2" CollectD S.Dom.simps(1) S.in_hom_char x)
                    thus ?thesis
                      using x y F 5 arr_char [of "F x"] extensional_arb [of "S.Map (F x)" "{U}" y]
                      by (metis (mono_tags, lifting) CollectD Int_iff S.in_hom_char)
                  qed
                  ultimately show ?thesis by auto
                qed
                moreover have
                    "y \<in> {U} \<Longrightarrow>
                       compose {U} (S.Map ?f) (\<lambda>_ \<in> {U}. elem_of (IMG x)) y = S.Map (F x) y"
                proof -
                  assume y: "y \<in> {U}"
                  have "compose {U} (S.Map ?f) (\<lambda>_ \<in> {U}. elem_of (IMG x)) y =
                        S.Map ?f (elem_of (IMG x))"
                    using y by (simp add: compose_eq restrict_apply')
                  also have "... = (\<lambda>x. S.Map (F (MkElem (arr_of x) a)) U) (elem_of (IMG x))"
                  proof -
                    have "elem_of (IMG x) \<in> S.Dom a"
                      using x y a 5 arr_char S.in_homE restrict_apply by force
                    thus ?thesis
                      using restrict_apply by simp
                  qed
                  also have "... = S.Map (F x) y"
                    using x y 1 2 MkElem_IMG [of x a] by simp
                  finally show
                      "compose {U} (S.Map ?f) (\<lambda>_ \<in> {U}. elem_of (IMG x)) y = S.Map (F x) y"
                    by auto
                qed
                ultimately show
                    "compose {U} (S.Map ?f) (\<lambda>_ \<in> {U}. elem_of (IMG x)) y = S.Map (F x) y"
                  by auto
              qed
              show "?f \<cdot> x = F x"
              proof (intro S.arr_eqI)
                have 5: "?f \<cdot> x \<in> S.hom S.unity b" using 1 x by blast
                have 6: "F x \<in> S.hom S.unity b"
                  using x F 1
                  by (metis (mono_tags, lifting) PiE S.in_homE mem_Collect_eq)
                show "S.arr (comp ?f x)" using 5 by blast
                show "S.arr (F x)" using 6 by blast
                show "S.Dom (comp ?f x) = S.Dom (F x)"
                  using 5 6 by (metis (mono_tags, lifting) CollectD S.in_hom_char)
                show "S.Cod (comp ?f x) = S.Cod (F x)"
                  using 5 6 by (metis (mono_tags, lifting) CollectD S.in_hom_char)
                show "S.Map (comp ?f x) = S.Map (F x)"
                  using 3 4 by simp
              qed
            qed
            thus "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : S.unity \<rightarrow> S.dom ?f\<guillemotright> \<longrightarrow> comp ?f x = F x)"
              using 1 by blast
          qed
          next
          show "\<And>A. A \<subseteq> S.Univ \<and> Setp (elem_of ` A) \<Longrightarrow> A \<subseteq> S.Univ"
            by simp
          show "\<And>A' A. \<lbrakk>A' \<subseteq> A; A \<subseteq> S.Univ \<and> Setp (elem_of ` A)\<rbrakk> \<Longrightarrow> A' \<subseteq> S.Univ \<and> Setp (elem_of ` A')"
            by (meson image_mono setcat.Setp_respects_subset setcat_axioms subset_trans)
          show "\<And>A B. \<lbrakk>A \<subseteq> S.Univ \<and> Setp (elem_of ` A); B \<subseteq> S.Univ \<and> Setp (elem_of ` B)\<rbrakk>
                         \<Longrightarrow> A \<union> B \<subseteq> S.Univ \<and> Setp (elem_of ` (A \<union> B))"
            by (simp add: image_Un union_preserves_Setp)
        qed
      qed
    qed

    text\<open>
      \<open>SetCat\<close> can be viewed as a concrete set category over its own element type
      @{typ 'a}, using @{term arr_of} as the required injection from @{typ 'a} to the universe
      of \<open>SetCat\<close>.
\<close>

    corollary is_concrete_set_category:
    shows "concrete_set_category comp (\<lambda>A. A \<subseteq> S.Univ \<and> Setp (elem_of ` A)) UNIV arr_of"
    proof -
      interpret S': set_category comp \<open>\<lambda>A. A \<subseteq> S.Univ \<and> Setp (elem_of ` A)\<close>
        using is_set_category by auto
      show ?thesis
      proof
        show 1: "arr_of \<in> UNIV \<rightarrow> S'.Univ"
          using arr_of_def terminal_char by force
        show "inj_on arr_of UNIV"
          using inj_arr_of by blast
      qed
    qed

    text\<open>
      As a consequence of the categoricity of the \<open>set_category\<close> axioms,
      if @{term S} interprets \<open>set_category\<close>, and if @{term \<phi>} is a bijection between
      the universe of @{term S} and the elements of type @{typ 'a}, then @{term S} is isomorphic
      to the category \<open>setcat\<close> of @{typ 'a} sets and functions between them constructed here.
\<close>

    corollary set_category_iso_SetCat:
    fixes S :: "'s comp" and \<phi> :: "'s \<Rightarrow> 'e"
    assumes "set_category S \<S>"
    and "bij_betw \<phi> (set_category_data.Univ S) UNIV"
    and "\<And>A. \<S> A \<longleftrightarrow> A \<subseteq> set_category_data.Univ S \<and> (arr_of \<circ> \<phi>) ` A \<in> S.set ` Collect S.ide"
    shows "\<exists>\<Phi>. invertible_functor S comp \<Phi>
                 \<and> (\<forall>m. set_category.incl S \<S> m
                           \<longrightarrow> set_category.incl comp (\<lambda>A. A \<in> S.set ` Collect S.ide) (\<Phi> m))"
    proof -
      interpret S': set_category S \<S> using assms by auto
      let ?\<psi> = "inv_into S'.Univ \<phi>"
      have "bij_betw (arr_of o \<phi>) S'.Univ S.Univ"
      proof (intro bij_betwI)
        show "arr_of o \<phi> \<in> S'.Univ \<rightarrow> Collect S.terminal"
          using assms(2) arr_of_mapsto by auto
        show "?\<psi> o elem_of \<in> S.Univ \<rightarrow> S'.Univ"
        proof
          fix x :: "'e setcat.arr"
          assume x: "x \<in> S.Univ"
          show "(inv_into S'.Univ \<phi> \<circ> elem_of) x \<in> S'.Univ"
            using x assms(2) bij_betw_def comp_apply inv_into_into
            by (metis UNIV_I)
        qed
        fix t
        assume "t \<in> S'.Univ"
        thus "(?\<psi> o elem_of) ((arr_of o \<phi>) t) = t"
          using assms(2) bij_betw_inv_into_left
          by (metis comp_apply elem_of_arr_of)
        next
        fix t' :: "'e setcat.arr"
        assume "t' \<in> S.Univ"
        thus "(arr_of o \<phi>) ((?\<psi> o elem_of) t') = t'"
          using assms(2) by (simp add: bij_betw_def f_inv_into_f)
      qed
      thus ?thesis
        using assms is_set_category set_img_Collect_ide_iff
              set_category_is_categorical
                [of S \<S> comp "\<lambda>A. A \<in> S.set ` Collect S.ide" "arr_of o \<phi>"]
        by simp
    qed

    sublocale category comp
      using is_category by blast
    sublocale set_category comp \<open>\<lambda>A. A \<subseteq> Collect S.terminal \<and> Setp (elem_of ` A)\<close>
      using is_set_category set_img_Collect_ide_iff by simp
    interpretation concrete_set_category comp \<open>\<lambda>A. A \<subseteq> Collect S.terminal \<and> Setp (elem_of ` A)\<close>
                       UNIV arr_of
      using is_concrete_set_category by simp
 
  end
(*
  interpretation SetCat: setcat undefined \<open>\<lambda>S. True\<close>
    by unfold_locales auto
 *)
  text\<open>
    Here we discard the temporary interpretations \<open>S\<close>, leaving only the exported
    definitions and facts.
\<close>

  context setcat
  begin

    text\<open>
      We establish mappings to pass back and forth between objects and arrows of the category
      and sets and functions on the underlying elements.
\<close>

    interpretation set_category comp \<open>\<lambda>A. A \<subseteq> Collect terminal \<and> Setp (elem_of ` A)\<close>
      using is_set_category by blast
    interpretation concrete_set_category comp \<open>\<lambda>A. A \<subseteq> Univ \<and> Setp (elem_of ` A)\<close> UNIV arr_of
      using is_concrete_set_category by blast

    definition set_of_ide :: "'e setcat.arr \<Rightarrow> 'e set"
    where "set_of_ide a \<equiv> elem_of ` set a"

    definition ide_of_set :: "'e set \<Rightarrow> 'e setcat.arr"
    where "ide_of_set A \<equiv> mkIde (arr_of ` A)"

    lemma bij_betw_ide_set:
    shows "set_of_ide \<in> Collect ide \<rightarrow> Collect Setp"
    and "ide_of_set \<in> Collect Setp \<rightarrow> Collect ide"
    and [simp]: "ide a \<Longrightarrow> ide_of_set (set_of_ide a) = a"
    and [simp]: "Setp A \<Longrightarrow> set_of_ide (ide_of_set A) = A"
    and "bij_betw set_of_ide (Collect ide) (Collect Setp)"
    and "bij_betw ide_of_set (Collect Setp) (Collect ide)"
    proof -
      show 1: "set_of_ide \<in> Collect ide \<rightarrow> Collect Setp"
        using setp_set_ide set_of_ide_def by auto
      show 2: "ide_of_set \<in> Collect Setp \<rightarrow> Collect ide"
      proof
        fix A :: "'e set"
        assume A: "A \<in> Collect Setp"
        have "arr_of ` A \<subseteq> Univ"
          using A arr_of_mapsto by auto
        moreover have "Setp (elem_of ` arr_of ` A)"
          using A elem_of_arr_of Setp_respects_subset by simp
        ultimately have "ide (mkIde (arr_of ` A))"
          using ide_mkIde by blast
        thus "ide_of_set A \<in> Collect ide"
          using ide_of_set_def by simp
      qed
      show 3: "\<And>a. ide a \<Longrightarrow> ide_of_set (set_of_ide a) = a"
        using arr_of_img_elem_of_img ide_of_set_def mkIde_set set_of_ide_def setp_set_ide
        by presburger
      show 4: "\<And>A. Setp A \<Longrightarrow> set_of_ide (ide_of_set A) = A"
      proof -
        fix A :: "'e set"
        assume A: "Setp A"
        have "elem_of ` set (mkIde (arr_of ` A)) = elem_of ` arr_of ` A"
        proof -
          have "arr_of ` A \<subseteq> Univ"
            using A arr_of_mapsto by blast
          moreover have "Setp (elem_of ` arr_of ` A)"
            using A by simp
          ultimately have "set (mkIde (arr_of ` A)) = arr_of ` A"
            using A set_mkIde by blast
          thus ?thesis by auto
        qed
        also have "... = A"
          using A elem_of_arr_of by force
        finally show "set_of_ide (ide_of_set A) = A"
          using ide_of_set_def set_of_ide_def by simp
      qed
      show "bij_betw set_of_ide (Collect ide) (Collect Setp)"
        using 1 2 3 4
        by (intro bij_betwI) blast+
      show "bij_betw ide_of_set (Collect Setp) (Collect ide)"
        using 1 2 3 4
        by (intro bij_betwI) blast+
    qed

    definition fun_of_arr :: "'e setcat.arr \<Rightarrow> 'e \<Rightarrow> 'e"
    where "fun_of_arr f \<equiv> restrict (elem_of o Fun f o arr_of) (elem_of `Dom f)"

    definition arr_of_fun :: "'e set \<Rightarrow> 'e set \<Rightarrow> ('e \<Rightarrow> 'e) \<Rightarrow> 'e setcat.arr"
    where "arr_of_fun A B F \<equiv> mkArr (arr_of ` A) (arr_of ` B) (arr_of o F o elem_of)"

    lemma bij_betw_hom_fun:
    shows "fun_of_arr \<in> hom a b \<rightarrow> extensional (set_of_ide a) \<inter> (set_of_ide a \<rightarrow> set_of_ide b)"
    and "\<lbrakk>Setp A; Setp B\<rbrakk> \<Longrightarrow> arr_of_fun A B \<in> (A \<rightarrow> B) \<rightarrow> hom (ide_of_set A) (ide_of_set B)"
    and "f \<in> hom a b \<Longrightarrow> arr_of_fun (set_of_ide a) (set_of_ide b) (fun_of_arr f) = f"
    and "\<lbrakk>Setp A; Setp B; F \<in> A \<rightarrow> B; F \<in> extensional A\<rbrakk> \<Longrightarrow> fun_of_arr (arr_of_fun A B F) = F"
    and "\<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> bij_betw fun_of_arr (hom a b)
                             (extensional (set_of_ide a) \<inter> (set_of_ide a \<rightarrow> set_of_ide b))"
    and "\<lbrakk>Setp A; Setp B\<rbrakk> \<Longrightarrow>
            bij_betw (arr_of_fun A B)
                     (extensional A \<inter> (A \<rightarrow> B)) (hom (ide_of_set A) (ide_of_set B))"
    proof -
      show 1: "\<And>a b. fun_of_arr \<in>
                        hom a b \<rightarrow> extensional (set_of_ide a) \<inter> (set_of_ide a \<rightarrow> set_of_ide b)"
      proof
        fix a b f
        assume f: "f \<in> hom a b"
        have Dom: "Dom f = arr_of ` set_of_ide a"
          using f set_of_ide_def
          by (metis (mono_tags, lifting) arr_dom arr_mkIde bij_betw_ide_set(3)
              ide_dom ide_of_set_def in_homE mem_Collect_eq set_mkIde)
        have Cod: "Cod f = arr_of ` set_of_ide b"
          using f set_of_ide_def
          by (metis (mono_tags, lifting) arr_cod arr_mkIde bij_betw_ide_set(3)
              ide_cod ide_of_set_def in_homE mem_Collect_eq set_mkIde)
        have "fun_of_arr f \<in> set_of_ide a \<rightarrow> set_of_ide b"
        proof
          fix x
          assume x: "x \<in> set_of_ide a"
          have 1: "arr_of x \<in> Dom f"
            using x Dom by blast
          hence "Fun f (arr_of x) \<in> Cod f"
            using f Fun_mapsto Cod by blast
          hence "elem_of (Fun f (arr_of x)) \<in> set_of_ide b"
            using Cod by auto
          hence "restrict (elem_of o Fun f o arr_of) (elem_of ` Dom f) x \<in> set_of_ide b"
            using 1 by force
          thus "fun_of_arr f x \<in> set_of_ide b"
            unfolding fun_of_arr_def by auto
        qed
        moreover have "fun_of_arr f \<in> extensional (set_of_ide a)"
          unfolding fun_of_arr_def
          using set_of_ide_def f by blast
        ultimately show "fun_of_arr f \<in> extensional (set_of_ide a) \<inter> (set_of_ide a \<rightarrow> set_of_ide b)"
          by blast
      qed
      show 2: "\<And>A B. \<lbrakk>Setp A; Setp B\<rbrakk> \<Longrightarrow>
                        arr_of_fun A B \<in> (A \<rightarrow> B) \<rightarrow> hom (ide_of_set A) (ide_of_set B)"
      proof
        fix x and A B :: "'e set"
        assume A: "Setp A" and B: "Setp B"
        assume x: "x \<in> A \<rightarrow> B"
        show "arr_of_fun A B x \<in> hom (ide_of_set A) (ide_of_set B)"
        proof
          show "\<guillemotleft>arr_of_fun A B x : ide_of_set A \<rightarrow> ide_of_set B\<guillemotright>"
          proof
            show 1: "arr (arr_of_fun A B x)"
            proof -
              have "arr_of ` A \<subseteq> Univ \<and> Setp (elem_of ` arr_of ` A)"
                using A arr_of_mapsto elem_of_arr_of
                by (metis (no_types, lifting) PiE arr_mkIde bij_betw_ide_set(2)
                    ide_implies_incl ide_of_set_def incl_def mem_Collect_eq)
              moreover have "arr_of ` B \<subseteq> Univ \<and> Setp (elem_of ` arr_of ` B)"
                using B arr_of_mapsto elem_of_arr_of
                by (metis (no_types, lifting) PiE arr_mkIde bij_betw_ide_set(2)
                    ide_implies_incl ide_of_set_def incl_def mem_Collect_eq)
              moreover have "arr_of \<circ> x \<circ> elem_of \<in> arr_of ` A \<rightarrow> arr_of ` B"
                using x by auto
              ultimately show ?thesis
                unfolding arr_of_fun_def by blast
            qed
            show "dom (arr_of_fun A B x) = ide_of_set A"
              using 1 dom_mkArr ide_of_set_def arr_of_fun_def by simp
            show "cod (arr_of_fun A B x) = ide_of_set B"
              using 1 cod_mkArr ide_of_set_def arr_of_fun_def by simp
          qed
        qed
      qed
      show 3: "\<And>a b f. f \<in> hom a b \<Longrightarrow> arr_of_fun (set_of_ide a) (set_of_ide b) (fun_of_arr f) = f"
      proof -
        fix a b f
        assume f: "f \<in> hom a b"
        have 1: "Dom f = set a \<and> Cod f = set b"
          using f by blast
        have Dom: "Dom f \<subseteq> Univ \<and> Setp (elem_of ` Dom f)"
          using setp_set_ide f ide_dom by blast
        have Cod: "Cod f \<subseteq> Univ \<and> Setp (elem_of ` Cod f)"
          using setp_set_ide f ide_cod by blast
        have "mkArr (set a) (set b)
                    (arr_of \<circ> restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ> elem_of) =
              mkArr (Dom f) (Cod f)
                    (arr_of \<circ> restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ> elem_of)"
          using 1 by simp
        also have "... = mkArr (Dom f) (Cod f) (Fun f)"
        proof (intro mkArr_eqI')
          show 2: "\<And>x. x \<in> Dom f \<Longrightarrow>
                         (arr_of \<circ>
                            restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ>
                              elem_of) x =
                         Fun f x"
          proof -
            fix x
            assume x: "x \<in> Dom f"
            hence 1: "elem_of x \<in> elem_of ` Dom f"
              by blast
            have "(arr_of \<circ> restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ> elem_of) x =
                  arr_of (restrict (elem_of o Fun f o arr_of) (elem_of ` Dom f) (elem_of x))"
              by auto
            also have "... = arr_of ((elem_of o Fun f o arr_of) (elem_of x))"
              using 1 by auto
            also have "... = arr_of (elem_of (Fun f (arr_of (elem_of x))))"
              by auto
            also have "... = arr_of (elem_of (Fun f x))"
              using x arr_of_elem_of \<open>Dom f \<subseteq> Univ \<and> Setp (elem_of ` Dom f)\<close> by auto
            also have "... = Fun f x"
              using x f Dom Cod Fun_mapsto arr_of_elem_of [of "Fun f x"] by blast
            finally show "(arr_of \<circ>
                             restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ>
                               elem_of) x =
                          Fun f x"
              by blast
          qed
          have "arr_of \<circ> restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ> elem_of
                  \<in> Dom f \<rightarrow> Cod f"
          proof
            fix x
            assume x: "x \<in> Dom f"
            have "(arr_of \<circ> restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ> elem_of) x =
                  Fun f x"
              using 2 x by blast
            moreover have "... \<in> Cod f"
              using f x Fun_mapsto by blast
            ultimately show "(arr_of \<circ>
                                restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ>
                                  elem_of) x
                               \<in> Cod f"
              by argo
          qed
          thus "arr (mkArr (Dom f) (Cod f)
                           (arr_of \<circ>
                              restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ>
                                elem_of))"
            using Dom Cod by blast
        qed
        finally have "mkArr (set a) (set b)
                            (arr_of \<circ>
                               restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) \<circ>
                                 elem_of) = f"
          using f mkArr_Fun
          by (metis (no_types, lifting) in_homE mem_Collect_eq)
        thus "arr_of_fun (set_of_ide a) (set_of_ide b) (fun_of_arr f) = f"
          using 1 f
          by (metis (no_types, lifting) Cod Dom arr_of_img_elem_of_img arr_of_fun_def
              fun_of_arr_def set_of_ide_def)
      qed
      show 4: "\<And>A B F. \<lbrakk>Setp A; Setp B; F \<in> A \<rightarrow> B; F \<in> extensional A\<rbrakk>
                          \<Longrightarrow> fun_of_arr (arr_of_fun A B F) = F"
      proof
        fix F and A B :: "'e set"
        assume A: "Setp A" and B: "Setp B"
        assume F: "F \<in> A \<rightarrow> B" and ext: "F \<in> extensional A"
        have 4: "arr (mkArr (arr_of ` A) (arr_of ` B) (arr_of \<circ> F \<circ> elem_of))"
        proof -
          have "arr_of ` A \<subseteq> Univ \<and> Setp (elem_of ` arr_of ` A)"
            using A
            by (metis (no_types, lifting) PiE arr_mkIde bij_betw_ide_set(2) ide_implies_incl
                ide_of_set_def incl_def mem_Collect_eq)
          moreover have "arr_of ` B \<subseteq> Univ \<and> Setp (elem_of ` arr_of ` B)"
            using B
            by (metis (no_types, lifting) PiE arr_mkIde bij_betw_ide_set(2) ide_implies_incl
                ide_of_set_def incl_def mem_Collect_eq)
          moreover have "arr_of \<circ> F \<circ> elem_of \<in> arr_of ` A \<rightarrow> arr_of ` B"
            using F by auto
          ultimately show ?thesis by blast
        qed
        show "\<And>x. fun_of_arr (arr_of_fun A B F) x = F x"
        proof -
          fix x
          have "fun_of_arr (arr_of_fun A B F) x =
                restrict (elem_of \<circ>
                            Fun (mkArr (arr_of ` A) (arr_of ` B) (arr_of \<circ> F \<circ> elem_of)) \<circ>
                              arr_of) A x"
          proof -
            have "elem_of ` Dom (mkArr (arr_of ` A) (arr_of ` B) (arr_of \<circ> F \<circ> elem_of)) = A"
              using A 4 elem_of_arr_of dom_mkArr set_of_ide_def bij_betw_ide_set(4) ide_of_set_def
              by auto
            thus ?thesis
              using arr_of_fun_def fun_of_arr_def by auto
          qed
          also have "... = F x"
          proof (cases "x \<in> A")
            show "x \<notin> A \<Longrightarrow> ?thesis"
              using ext extensional_arb by fastforce
            assume x: "x \<in> A"
            show "restrict
                    (elem_of \<circ>
                       Fun (mkArr (arr_of ` A) (arr_of ` B) (arr_of \<circ> F \<circ> elem_of)) \<circ>
                         arr_of) A x =
                  F x"
              using x 4 Fun_mkArr by simp
          qed
          finally show "fun_of_arr (arr_of_fun A B F) x = F x"
            by blast
        qed
      qed
      show "\<lbrakk>Setp A; Setp B\<rbrakk> \<Longrightarrow>
               bij_betw (arr_of_fun A B) (extensional A \<inter> (A \<rightarrow> B))
                        (hom (ide_of_set A) (ide_of_set B))"
      proof -
        assume A: "Setp A" and B: "Setp B"
        have "ide (ide_of_set A) \<and> ide (ide_of_set B)"
          using A B bij_betw_ide_set(2) by auto
        have "set_of_ide (ide_of_set A) = A \<and> set_of_ide (ide_of_set B) = B"
          using A B by simp
        show ?thesis
          using A B 1 [of "ide_of_set A" "ide_of_set B"] 2 3 4
          apply (intro bij_betwI)
             apply auto
           apply blast
          by fastforce
      qed
      show "\<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> bij_betw fun_of_arr (hom a b)
                                (extensional (set_of_ide a) \<inter> (set_of_ide a \<rightarrow> set_of_ide b))"
      proof (intro bij_betwI)
        assume a: "ide a" and b: "ide b"
        show "fun_of_arr \<in> hom a b \<rightarrow> extensional (set_of_ide a) \<inter> (set_of_ide a \<rightarrow> set_of_ide b)"
          using 1 by blast
        show "arr_of_fun (set_of_ide a) (set_of_ide b) \<in>
               extensional (set_of_ide a) \<inter> (set_of_ide a \<rightarrow> set_of_ide b) \<rightarrow> hom a b"
          using a b 2 [of "set_of_ide a" "set_of_ide b"] setp_set_ide set_of_ide_def
                bij_betw_ide_set(3)
          by auto
        show "\<And>f. f \<in> hom a b \<Longrightarrow> arr_of_fun (set_of_ide a) (set_of_ide b) (fun_of_arr f) = f"
          using a b 3 by blast
        show "\<And>F. F \<in> extensional (set_of_ide a) \<inter> (set_of_ide a \<rightarrow> set_of_ide b) \<Longrightarrow>
                    fun_of_arr (arr_of_fun (set_of_ide a) (set_of_ide b) F) = F"
          using a b 4 [of "set_of_ide a" "set_of_ide b"]
          by (metis (no_types, lifting) IntE set_of_ide_def setp_set_ide)
      qed
    qed

    lemma fun_of_arr_ide:
    assumes "ide a"
    shows "fun_of_arr a = restrict id (elem_of ` Dom a)"
    proof
      fix x
      show "fun_of_arr a x = restrict id (elem_of ` Dom a) x"
      proof (cases "x \<in> elem_of ` Dom a")
        show "x \<notin> elem_of ` Dom a \<Longrightarrow> ?thesis"
          using fun_of_arr_def extensional_arb by auto
        assume x: "x \<in> elem_of ` Dom a"
        have "fun_of_arr a x = restrict (elem_of \<circ> Fun a \<circ> arr_of) (elem_of ` Dom a) x"
          using x fun_of_arr_def by simp
        also have "... = elem_of (Fun a (arr_of x))"
          using x by auto
        also have "... = elem_of ((\<lambda>x\<in>set a. x) (arr_of x))"
          using assms x Fun_ide by auto
        also have "... = elem_of (arr_of x)"
        proof -
          have "x \<in> elem_of ` set a"
            using assms x ideD(2) by force
          hence "arr_of x \<in> set a"
            by (metis (mono_tags, lifting) arr_of_img_elem_of_img assms image_eqI setp_set_ide)
          thus ?thesis by simp
        qed
        also have "... = x"
          by simp
        also have "... = restrict id (elem_of ` Dom a) x"
          using x by auto
        finally show ?thesis by blast
      qed
    qed

    lemma arr_of_fun_id:
    assumes "Setp A"
    shows "arr_of_fun A A (restrict id A) = ide_of_set A"
    proof -
      have A: "arr_of ` A \<subseteq> Univ \<and> Setp (elem_of ` arr_of ` A)"
        using assms elem_of_arr_of
        by (metis (no_types, lifting) PiE arr_mkIde bij_betw_ide_set(2) ide_implies_incl
            ide_of_set_def incl_def mem_Collect_eq)
      have "arr_of_fun A A (restrict id A) =
            mkArr (arr_of ` A) (arr_of ` A) (arr_of \<circ> restrict id A \<circ> elem_of)"
        unfolding arr_of_fun_def by simp
      also have "... = mkArr (arr_of ` A) (arr_of ` A) (\<lambda>x. x)"
        using A arr_mkArr
        by (intro mkArr_eqI') auto
      also have "... = ide_of_set A"
        using A ide_of_set_def mkIde_as_mkArr by simp
      finally show ?thesis by blast
    qed

    lemma fun_of_arr_comp:
    assumes "f \<in> hom a b" and "g \<in> hom b c"
    shows "fun_of_arr (comp g f) = restrict (fun_of_arr g \<circ> fun_of_arr f) (set_of_ide a)"
    proof -
      have 1: "seq g f"
        using assms by blast
      have "fun_of_arr (comp g f) =
            restrict (elem_of \<circ> Fun (comp g f) \<circ> arr_of) (elem_of ` Dom (comp g f))"
        unfolding fun_of_arr_def by blast
      also have "... = restrict (elem_of \<circ> Fun (comp g f) \<circ> arr_of) (elem_of ` Dom f)"
        using assms dom_comp seqI' by auto
      also have "... = restrict (elem_of \<circ> restrict (Fun g \<circ> Fun f) (Dom f) \<circ> arr_of)
                                (elem_of ` Dom f)"
        using 1 Fun_comp by auto
      also have "... = restrict (restrict (elem_of o Fun g o arr_of) (elem_of ` Dom g) \<circ>
                                   restrict (elem_of o Fun f o arr_of) (elem_of ` Dom f))
                                (elem_of ` Dom f)"
      proof
        fix x
        show "restrict (elem_of \<circ> restrict (Fun g \<circ> Fun f) (Dom f) \<circ> arr_of) (elem_of ` Dom f) x =
              restrict (restrict (elem_of \<circ> Fun g \<circ> arr_of) (elem_of ` Dom g) \<circ>
                          restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f))
                       (elem_of ` Dom f) x"
        proof (cases "x \<in> elem_of ` Dom f")
          show "x \<notin> elem_of ` Dom f \<Longrightarrow> ?thesis"
            by auto
          assume x: "x \<in> elem_of ` Dom f"
          have 2: "arr_of x \<in> Dom f"
          proof -
            have "arr_of x \<in> arr_of ` elem_of ` Dom f"
              using x by simp
            thus ?thesis
              by (metis (no_types, lifting) 1 arr_of_img_elem_of_img ide_dom seqE setp_set_ide)
          qed
          have 3: "Dom g = Cod f"
            using assms by fastforce
          have "restrict (elem_of \<circ> restrict (Fun g \<circ> Fun f) (Dom f) \<circ> arr_of) (elem_of ` Dom f) x =
                elem_of (Fun g (Fun f (arr_of x)))"
            using x 2 by simp
          also have "... = restrict
                             (restrict (elem_of \<circ> Fun g \<circ> arr_of) (elem_of ` Dom g) \<circ>
                                restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f))
                             (elem_of ` Dom f) x"
          proof -
            have "restrict (restrict (elem_of \<circ> Fun g \<circ> arr_of) (elem_of ` Dom g) \<circ>
                              restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f))
                           (elem_of ` Dom f) x =
                  elem_of (Fun g (Fun f (arr_of x)))"
            proof -
              have "restrict (restrict (elem_of \<circ> Fun g \<circ> arr_of) (elem_of ` Dom g) \<circ>
                                restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f))
                             (elem_of ` Dom f) x =
                    (restrict (elem_of \<circ> Fun g \<circ> arr_of) (elem_of ` Dom g) o
                       restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f)) x"
                using 2 by force
              also have "... = restrict (elem_of \<circ> Fun g \<circ> arr_of) (elem_of ` Dom g)
                                 (restrict (elem_of \<circ> Fun f \<circ> arr_of) (elem_of ` Dom f) x)"
                by simp
              also have "... = restrict (elem_of \<circ> Fun g \<circ> arr_of) (elem_of ` Dom g)
                                 (elem_of (Fun f (arr_of x)))"
                using 2 by force
              also have "... = (elem_of o Fun g o arr_of) (elem_of (Fun f (arr_of x)))"
              proof -
                have "elem_of (Fun f (arr_of x)) \<in> elem_of ` Dom g"
                  using assms 2 3 Fun_mapsto [of f] by blast
                thus ?thesis by simp
              qed
              also have "... = elem_of (Fun g (arr_of (elem_of (Fun f (arr_of x)))))"
                by simp
              also have "... = elem_of (Fun g (Fun f (arr_of x)))"
              proof -
                have "Fun f (arr_of x) \<in> Univ"
                  using assms 2 setp_set_ide ide_cod Fun_mapsto by blast
                thus ?thesis
                  using 2 by simp
              qed
              finally show ?thesis by blast
            qed
            thus ?thesis by simp
          qed
          finally show ?thesis by blast
        qed
      qed
      also have "... = restrict (fun_of_arr g o fun_of_arr f) (elem_of ` Dom f)"
        unfolding fun_of_arr_def by blast
      finally show ?thesis
        unfolding set_of_ide_def
        using assms by blast
    qed

    lemma arr_of_fun_comp:
    assumes "Setp A" and "Setp B" and "Setp C"
    and "F \<in> extensional A \<inter> (A \<rightarrow> B)" and "G \<in> extensional B \<inter> (B \<rightarrow> C)"
    shows "arr_of_fun A C (G o F) = comp (arr_of_fun B C G) (arr_of_fun A B F)"
    proof -
      have A: "arr_of ` A \<subseteq> Univ \<and> Setp (elem_of ` arr_of ` A)"
        using assms elem_of_arr_of
        by (metis (no_types, lifting) Pi_iff arr_mkIde bij_betw_ide_set(2)
            ide_implies_incl ide_of_set_def incl_def mem_Collect_eq)
      have B: "arr_of ` B \<subseteq> Univ \<and> Setp (elem_of ` arr_of ` B)"
        using assms elem_of_arr_of
        by (metis (no_types, lifting) Pi_iff arr_mkIde bij_betw_ide_set(2)
            ide_implies_incl ide_of_set_def incl_def mem_Collect_eq)
      have C: "arr_of ` C \<subseteq> Univ \<and> Setp (elem_of ` arr_of ` C)"
        using assms elem_of_arr_of
        by (metis (no_types, lifting) Pi_iff arr_mkIde bij_betw_ide_set(2)
            ide_implies_incl ide_of_set_def incl_def mem_Collect_eq)
      have "arr_of_fun A C (G o F) = mkArr (arr_of ` A) (arr_of ` C) (arr_of \<circ> (G \<circ> F) \<circ> elem_of)"
        unfolding arr_of_fun_def by simp
      also have "... = mkArr (arr_of ` A) (arr_of ` C)
                             ((arr_of \<circ> G \<circ> elem_of) o (arr_of o F \<circ> elem_of))"
      proof (intro mkArr_eqI')
        show "arr (mkArr (arr_of ` A) (arr_of ` C) (arr_of \<circ> (G \<circ> F) \<circ> elem_of))"
        proof -
          have "arr_of \<circ> (G \<circ> F) \<circ> elem_of \<in> arr_of ` A \<rightarrow> arr_of ` C"
            using assms by force
          thus ?thesis
            using A B C by blast
        qed
        show "\<And>x. x \<in> arr_of ` A \<Longrightarrow>
                    (arr_of \<circ> (G \<circ> F) \<circ> elem_of) x =
                    ((arr_of \<circ> G \<circ> elem_of) o (arr_of o F \<circ> elem_of)) x"
          by simp
      qed
      also have "... = comp (mkArr (arr_of ` B) (arr_of ` C) (arr_of \<circ> G \<circ> elem_of))
                            (mkArr (arr_of ` A) (arr_of ` B) (arr_of o F o elem_of))"
      proof -
        have "arr (mkArr (arr_of ` B) (arr_of ` C) (arr_of \<circ> G \<circ> elem_of))"
          using assms B C elem_of_arr_of by fastforce
        moreover have "arr (mkArr (arr_of ` A) (arr_of ` B) (arr_of o F o elem_of))"
          using assms A B elem_of_arr_of by fastforce
        ultimately show ?thesis
          using comp_mkArr by auto
      qed
      also have "... = comp (arr_of_fun B C G) (arr_of_fun A B F)"
        using arr_of_fun_def by presburger
      finally show ?thesis by blast
    qed

  end

  text\<open>
    When there is no restriction on the sets that determine objects, the resulting set category
    is replete.  This is the normal use case, which we want to streamline as much as possible,
    so it is useful to introduce a special locale for this purpose.
  \<close>

  locale replete_setcat =
  fixes elem_type :: "'e itself"
  begin

    interpretation SC: setcat elem_type \<open>\<lambda>_. True\<close>
      by unfold_locales blast

    definition comp
    where "comp \<equiv> SC.comp"

    definition arr_of
    where "arr_of \<equiv> SC.arr_of"

    definition elem_of
    where "elem_of \<equiv> SC.elem_of"

    sublocale replete_set_category comp
      unfolding comp_def
      using SC.is_set_category replete_set_category_def set_category_def by auto

    lemma is_replete_set_category:
    shows "replete_set_category comp"
      ..

    lemma is_set_category\<^sub>R\<^sub>S\<^sub>C:
    shows "set_category comp (\<lambda>A. A \<subseteq> Univ)"
      using is_set_category by blast

    sublocale concrete_set_category comp setp UNIV arr_of
      using SC.is_concrete_set_category comp_def SC.set_img_Collect_ide_iff arr_of_def
      by auto

    lemma is_concrete_set_category:
    shows "concrete_set_category comp setp UNIV arr_of"
      ..

    lemma bij_arr_of:
    shows "bij_betw arr_of UNIV Univ"
      using SC.bij_arr_of comp_def arr_of_def by presburger

    lemma bij_elem_of:
    shows "bij_betw elem_of Univ UNIV"
      using SC.bij_elem_of comp_def elem_of_def by auto

  end
(*
  interpretation RepleteSetCat: replete_setcat undefined .
 *)
end

