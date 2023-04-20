(*  Title:       HF_SetCat
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2020
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "The Category of Hereditarily Finite Sets"

theory HF_SetCat
imports CategoryWithFiniteLimits CartesianClosedCategory HereditarilyFinite.HF
begin

  text\<open>
    This theory constructs a category whose objects are in bijective correspondence with
    the hereditarily finite sets and whose arrows correspond to the functions between such
    sets.  We show that this category is cartesian closed and has finite limits.
    Note that up to this point we have not constructed any other interpretation for the
    @{locale cartesian_closed_category} locale, but it is important to have one to ensure
    that the locale assumptions are consistent.
  \<close>

  section "Preliminaries"

  text\<open>
    We begin with some preliminary definitions and facts about hereditarily finite sets,
    which are better targeted toward what we are trying to do here than what already exists
    in @{theory HereditarilyFinite.HF}.
  \<close>

  text\<open>
    The following defines when a hereditarily finite set \<open>F\<close> represents a function from
    a hereditarily finite set \<open>B\<close> to a hereditarily finite set \<open>C\<close>.  Specifically, \<open>F\<close>
    must be a relation from \<open>B\<close> to \<open>C\<close>, whose domain is \<open>B\<close>, whose range is contained in \<open>C\<close>,
    and which is single-valued on its domain.
  \<close>

  definition hfun
  where "hfun B C F \<equiv> F \<le> B * C \<and> hfunction F \<and> hdomain F = B \<and> hrange F \<le> C"

  lemma hfunI [intro]:
  assumes "F \<le> A * B"
  and "\<And>X. X \<^bold>\<in> A \<Longrightarrow> \<exists>!Y. \<langle>X, Y\<rangle> \<^bold>\<in> F"
  and "\<And>X Y. \<langle>X, Y\<rangle> \<^bold>\<in> F \<Longrightarrow> Y \<^bold>\<in> B"
  shows "hfun A B F"
    unfolding hfun_def
    using assms hfunction_def hrelation_def is_hpair_def hrange_def hconverse_def hdomain_def
    apply (intro conjI)
    apply auto
    by fast

  lemma hfunE [elim]:
  assumes "hfun B C F"
  and "(\<And>Y. Y \<^bold>\<in> B \<Longrightarrow> (\<exists>!Z. \<langle>Y, Z\<rangle> \<^bold>\<in> F) \<and> (\<forall>Z. \<langle>Y, Z\<rangle> \<^bold>\<in> F \<longrightarrow> Z \<^bold>\<in> C)) \<Longrightarrow> T"
  shows T
  proof -
    have "\<And>Y. Y \<^bold>\<in> B \<Longrightarrow> (\<exists>!Z. \<langle>Y, Z\<rangle> \<^bold>\<in> F) \<and> (\<forall>Z. \<langle>Y, Z\<rangle> \<^bold>\<in> F \<longrightarrow> Z \<^bold>\<in> C)"
    proof (intro allI impI conjI)
      fix Y
      assume Y: "Y \<^bold>\<in> B"
      show "\<exists>!Z. \<langle>Y, Z\<rangle> \<^bold>\<in> F"
      proof -
        have "\<exists>Z. \<langle>Y, Z\<rangle> \<^bold>\<in> F"
          using assms Y hfun_def hdomain_def by auto
        moreover have "\<And>Z Z'. \<lbrakk> \<langle>Y, Z\<rangle> \<^bold>\<in> F; \<langle>Y, Z'\<rangle> \<^bold>\<in> F \<rbrakk> \<Longrightarrow> Z = Z'"
          using assms hfun_def hfunction_def by simp
        ultimately show ?thesis by blast
      qed
      show "\<And>Z. \<langle>Y, Z\<rangle> \<^bold>\<in> F \<Longrightarrow> Z \<^bold>\<in> C"
        using assms Y hfun_def by auto
    qed
    thus ?thesis
      using assms(2) by simp
  qed

  text\<open>
    The hereditarily finite set \<open>hexp B C\<close> represents the collection of all functions
    from \<open>B\<close> to \<open>C\<close>.
  \<close>

  definition hexp
  where "hexp B C = \<lbrace>F \<^bold>\<in> HPow (B * C). hfun B C F\<rbrace>"

  lemma hfun_in_hexp:
  assumes "hfun B C F"
  shows "F \<^bold>\<in> hexp B C"
    using assms by (simp add: hexp_def hfun_def)

  text\<open>
    The function \<open>happ\<close> applies a function \<open>F\<close> from \<open>B\<close> to \<open>C\<close> to an element of \<open>B\<close>,
    yielding an element of \<open>C\<close>.
  \<close>

  abbreviation happ
  where "happ \<equiv> app"

  lemma happ_mapsto:
  assumes "F \<^bold>\<in> hexp B C" and "Y \<^bold>\<in> B"
  shows "happ F Y \<^bold>\<in> C" and "happ F Y \<^bold>\<in> hrange F"
  proof -
    show "happ F Y \<^bold>\<in> C"
      using assms app_def hexp_def app_equality hdomain_def hfun_def by auto
    show "happ F Y \<^bold>\<in> hrange F"
    proof -
      have "\<langle>Y, happ F Y\<rangle> \<^bold>\<in> F"
        using assms app_def hexp_def app_equality hdomain_def hfun_def by auto
      thus ?thesis
        using hdomain_def hrange_def hconverse_def by auto
    qed
  qed

  lemma happ_expansion:
  assumes "hfun B C F"
  shows "F = \<lbrace>XY \<^bold>\<in> B * C. hsnd XY = happ F (hfst XY)\<rbrace>"
  proof
    fix XY
    show "XY \<^bold>\<in> F \<longleftrightarrow> XY \<^bold>\<in> \<lbrace>XY \<^bold>\<in> B * C. hsnd XY = happ F (hfst XY)\<rbrace>"
    proof
      show "XY \<^bold>\<in> F \<Longrightarrow> XY \<^bold>\<in> \<lbrace>XY \<^bold>\<in> B * C. hsnd XY = happ F (hfst XY)\<rbrace>"
      proof -
        assume XY: "XY \<^bold>\<in> F"
        have "XY \<^bold>\<in> B * C"
          using assms XY hfun_def by auto
        moreover have "hsnd XY = happ F (hfst XY)"
          using assms XY hfunE app_def [of F "hfst XY"] the1_equality [of "\<lambda>y. \<langle>hfst XY, y\<rangle> \<^bold>\<in> F"]
                calculation
          by auto
        ultimately show "XY \<^bold>\<in> \<lbrace>XY \<^bold>\<in> B * C. hsnd XY = happ F (hfst XY)\<rbrace>" by simp
      qed
      show "XY \<^bold>\<in> \<lbrace>XY \<^bold>\<in> B * C. hsnd XY = happ F (hfst XY)\<rbrace> \<Longrightarrow> XY \<^bold>\<in> F"
      proof -
        assume XY: "XY \<^bold>\<in> \<lbrace>XY \<^bold>\<in> B * C. hsnd XY = happ F (hfst XY)\<rbrace>"
        show "XY \<^bold>\<in> F"
          using assms XY app_def [of F "hfst XY"] the1_equality [of "\<lambda>y. \<langle>hfst XY, y\<rangle> \<^bold>\<in> F"]
          by fastforce
      qed
    qed
  qed

  text\<open>
    Function \<open>hlam\<close> takes a function \<open>F\<close> from \<open>A * B\<close> to \<open>C\<close> to a function \<open>hlam F\<close>
    from \<open>A\<close> to \<open>hexp B C\<close>.
  \<close>

  definition hlam
  where "hlam A B C F =
         \<lbrace>XG \<^bold>\<in> A * hexp B C.
            \<forall>YZ. YZ \<^bold>\<in> hsnd XG \<longleftrightarrow> is_hpair YZ \<and> \<langle>\<langle>hfst XG, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace>"

  lemma hfun_hlam:
  assumes "hfun (A * B) C F"
  shows "hfun A (hexp B C) (hlam A B C F)"
  proof
    show "hlam A B C F \<le> A * hexp B C"
      using assms hlam_def by auto
    show "\<And>X. X \<^bold>\<in> A \<Longrightarrow> \<exists>!Y. \<langle>X, Y\<rangle> \<^bold>\<in> hlam A B C F"
    proof
      fix X
      assume X: "X \<^bold>\<in> A"
      let ?G = "\<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace>"
      have 1: "?G \<^bold>\<in> hexp B C"
        using assms X hexp_def by fastforce
      show "\<langle>X, ?G\<rangle> \<^bold>\<in> hlam A B C F"
        using assms X 1 is_hpair_def hfun_def hlam_def by auto
      fix Y
      assume XY: "\<langle>X, Y\<rangle> \<^bold>\<in> hlam A B C F"
      show "Y = ?G"
        using assms X XY hlam_def hexp_def by fastforce
    qed
    show "\<And>X Y. \<langle>X, Y\<rangle> \<^bold>\<in> hlam A B C F \<Longrightarrow> Y \<^bold>\<in> hexp B C"
      using assms hlam_def hexp_def by simp
  qed

  lemma happ_hlam:
  assumes "X \<^bold>\<in> A" and "hfun (A * B) C F"
  shows "\<exists>!G. \<langle>X, G\<rangle> \<^bold>\<in> hlam A B C F"
  and "happ (hlam A B C F) X = (THE G. \<langle>X, G\<rangle> \<^bold>\<in> hlam A B C F)"
  and "happ (hlam A B C F) X = \<lbrace>yz \<^bold>\<in> B * C. \<langle>\<langle>X, hfst yz\<rangle>, hsnd yz\<rangle> \<^bold>\<in> F\<rbrace>"
  and "Y \<^bold>\<in> B \<Longrightarrow> happ (happ (hlam A B C F) X) Y = happ F \<langle>X, Y\<rangle>"
  proof -
    show 1: "\<exists>!G. \<langle>X, G\<rangle> \<^bold>\<in> hlam A B C F"
      using assms(1,2) hfun_hlam hfunE
      by (metis (full_types))
    show 2: "happ (hlam A B C F) X = (THE G. \<langle>X, G\<rangle> \<^bold>\<in> hlam A B C F)"
      using assms app_def by simp
    show "happ (happ (hlam A B C F) X) Y = happ F \<langle>X, Y\<rangle>"
    proof -
      have 3: "\<langle>X, happ (hlam A B C F) X\<rangle> \<^bold>\<in> hlam A B C F"
        using assms(1) 1 2 theI' [of "\<lambda>G. \<langle>X, G\<rangle> \<^bold>\<in> hlam A B C F"] by simp
      hence "\<exists>!Z. happ (happ (hlam A B C F) X) = Z"
        by simp
      moreover have "happ (happ (hlam A B C F) X) Y = happ F \<langle>X, Y\<rangle>"
        using assms(1-2) 3 hlam_def is_hpair_def app_def by simp
      ultimately show ?thesis by simp
    qed
    show "happ (hlam A B C F) X = \<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace>"
    proof -
      let ?G = "\<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace>"
      have 4: "hfun B C ?G"
      proof
        show "\<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace> \<le> B * C"
          using assms by auto
        show "\<And>Y. Y \<^bold>\<in> B \<Longrightarrow> \<exists>!Z. \<langle>Y, Z\<rangle> \<^bold>\<in> \<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace>"
        proof -
          fix Y
          assume Y: "Y \<^bold>\<in> B"
          have XY: "\<langle>X, Y\<rangle> \<^bold>\<in> A * B"
            using assms Y by simp
          hence 1: "\<exists>!Z. \<langle>\<langle>X, Y\<rangle>, Z\<rangle> \<^bold>\<in> F"
            using assms XY hfunE [of "A * B" C F] by metis
          obtain Z where Z: "\<langle>\<langle>X, Y\<rangle>, Z\<rangle> \<^bold>\<in> F"
            using 1 by auto
          have "\<exists>Z. \<langle>Y, Z\<rangle> \<^bold>\<in> \<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace>"
          proof -
            have "\<langle>Y, Z\<rangle> \<^bold>\<in> B * C"
              using assms Y Z by blast
            moreover have "\<langle>\<langle>X, hfst \<langle>Y, Z\<rangle>\<rangle>, hsnd \<langle>Y, Z\<rangle>\<rangle> \<^bold>\<in> F"
              using assms Y Z by simp
            ultimately show ?thesis by auto
          qed
          moreover have "\<And>Z Z'. \<lbrakk>\<langle>Y, Z\<rangle> \<^bold>\<in> \<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace>;
                                 \<langle>Y, Z'\<rangle> \<^bold>\<in> \<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace>\<rbrakk> \<Longrightarrow> Z = Z'"
            using assms Y by auto
          ultimately show "\<exists>!Z. \<langle>Y, Z\<rangle> \<^bold>\<in> \<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace>"
            by auto
        qed
        show "\<And>Y Z. \<langle>Y, Z\<rangle> \<^bold>\<in> \<lbrace>YZ \<^bold>\<in> B * C. \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F\<rbrace> \<Longrightarrow> Z \<^bold>\<in> C"
          using assms by simp
      qed
      have "\<langle>X, ?G\<rangle> \<^bold>\<in> hlam A B C F"
      proof -
        have "\<langle>X, ?G\<rangle> \<^bold>\<in> A * hexp B C"
          using assms 4
          by (simp add: hfun_in_hexp)
        moreover have "\<forall>YZ. YZ \<^bold>\<in> ?G \<longleftrightarrow> is_hpair YZ \<and> \<langle>\<langle>X, hfst YZ\<rangle>, hsnd YZ\<rangle> \<^bold>\<in> F"
          using assms 1 is_hpair_def hfun_def by auto
        ultimately show ?thesis
          using assms 1 hlam_def by simp
      qed
      thus "happ (hlam A B C F) X = ?G"
        using assms 2 4 app_equality hfun_def hfun_hlam by auto
    qed
  qed

  section "Construction of the Category"

  locale hfsetcat
  begin

    text\<open>
      We construct the category of hereditarily finite sets and functions simply by applying
      the generic ``set category'' construction, using the hereditarily finite sets as the
      universe, and constraining the collections of such sets that determine objects of the
      category to those that are finite.
    \<close>

    interpretation setcat \<open>TYPE(hf)\<close> finite
      using finite_subset
      by unfold_locales blast+
    interpretation set_category comp \<open>\<lambda>A. A \<subseteq> Collect terminal \<and> finite (elem_of ` A)\<close>
      using is_set_category by blast

    lemma set_ide_char:
    shows "A \<in> set ` Collect ide \<longleftrightarrow> A \<subseteq> Univ \<and> finite A"
    proof
      assume A: "A \<in> set ` Collect ide"
      show "A \<subseteq> Univ \<and> finite A"
      proof
        show "A \<subseteq> Univ"
          using A setp_set' by auto
        obtain a where a: "ide a \<and> A = set a"
          using A by blast
        have "finite (elem_of ` set a)"
          using a setp_set_ide by blast
        moreover have "inj_on elem_of (set a)"
        proof -
          have "inj_on elem_of Univ"
            using bij_elem_of bij_betw_imp_inj_on by auto
          moreover have "set a \<subseteq> Univ"
            using a setp_set' [of a] by blast
          ultimately show ?thesis
            using inj_on_subset by auto
        qed
        ultimately show "finite A"
          using a A finite_imageD [of elem_of "set a"] by blast
      qed
      next
      assume A: "A \<subseteq> Univ \<and> finite A"
      have "ide (mkIde A)"
        using A ide_mkIde by simp
      moreover have "set (mkIde A) = A"
        using A finite_imp_setp set_mkIde by presburger
      ultimately show "A \<in> set ` Collect ide" by blast
    qed

    lemma set_ideD:
    assumes "ide a"
    shows "set a \<subseteq> Univ" and "finite (set a)"
      using assms set_ide_char by auto

    lemma ide_mkIdeI [intro]:
    assumes "A \<subseteq> Univ" and "finite A"
    shows "ide (mkIde A)" and "set (mkIde A) = A"
      using assms ide_mkIde set_mkIde by auto

    interpretation category_with_terminal_object comp
      using terminal_unity by unfold_locales auto

    text\<open>
      We verify that the objects of HF are indeed in bijective correspondence with the
      hereditarily finite sets.
    \<close>

    definition ide_to_hf
    where "ide_to_hf a = HF (elem_of ` set a)"

    definition hf_to_ide
    where "hf_to_ide x = mkIde (arr_of ` hfset x)"

    lemma ide_to_hf_mapsto:
    shows "ide_to_hf \<in> Collect ide \<rightarrow> UNIV"
      by simp

    lemma hf_to_ide_mapsto:
    shows "hf_to_ide \<in> UNIV \<rightarrow> Collect ide"
    proof
      fix x :: hf
      have "finite (arr_of ` hfset x)"
        by simp
      moreover have "arr_of ` hfset x \<subseteq> Univ"
        by (metis (mono_tags, lifting) UNIV_I bij_arr_of bij_betw_def imageE image_eqI subsetI)
      ultimately have "ide (mkIde (arr_of ` hfset x))"
        using finite_imp_setp ide_mkIde by presburger
      thus "hf_to_ide x \<in> Collect ide"
        using hf_to_ide_def by simp
    qed

    lemma hf_to_ide_ide_to_hf:
    assumes "a \<in> Collect ide"
    shows "hf_to_ide (ide_to_hf a) = a"
    proof -
      have "hf_to_ide (ide_to_hf a) = mkIde (arr_of ` hfset (HF (elem_of ` set a)))"
        using hf_to_ide_def ide_to_hf_def by simp
      also have "... = a"
      proof -
        have "mkIde (arr_of ` hfset (HF (elem_of ` set a))) = mkIde (arr_of ` elem_of ` set a)"
        proof -
          have "finite (set a)"
            using assms set_ide_char by blast
          hence "finite (elem_of ` set a)"
            by simp
          hence "hfset (HF (elem_of ` set a)) = elem_of ` set a"
            using hfset_HF [of "elem_of ` set a"] by simp
          thus ?thesis by simp
        qed
        also have "... = a"
        proof -
          have "set a \<subseteq> Univ"
            using assms set_ide_char by blast
          hence "\<And>x. x \<in> set a \<Longrightarrow> arr_of (elem_of x) = x"
            using assms by auto
          hence "arr_of ` elem_of ` set a = set a"
            by force
          thus ?thesis
            using assms ide_char mkIde_set by simp
        qed
        finally show ?thesis by blast
      qed
      finally show "hf_to_ide (ide_to_hf a) = a" by blast
    qed

    lemma ide_to_hf_hf_to_ide:
    assumes "x \<in> UNIV"
    shows "ide_to_hf (hf_to_ide x) = x"
    proof -
      have "HF (elem_of ` set (mkIde (arr_of ` hfset x))) = x"
      proof -
        have "HF (elem_of ` set (mkIde (arr_of ` hfset x))) = HF (elem_of ` arr_of ` hfset x)"
          using assms set_mkIde [of "arr_of ` hfset x"] arr_of_mapsto mkIde_def by auto
        also have "... = HF (hfset x)"
        proof -
          have "\<And>A. elem_of ` arr_of ` A = A"
            using elem_of_arr_of by force
          thus ?thesis by metis
        qed
        also have "... = x" by simp
        finally show ?thesis by blast
      qed
      thus ?thesis
        using assms ide_to_hf_def hf_to_ide_def by simp
    qed

    lemma bij_betw_ide_hf_set:
    shows "bij_betw ide_to_hf (Collect ide) (UNIV :: hf set)"
      using ide_to_hf_mapsto hf_to_ide_mapsto ide_to_hf_hf_to_ide hf_to_ide_ide_to_hf
      by (intro bij_betwI) auto

    lemma ide_implies_finite_set:
    assumes "ide a"
    shows "finite (set a)" and "finite (hom unity a)"
    proof -
      show 1: "finite (set a)"
        using assms set_ide_char by blast
      show "finite (hom unity a)"
        using assms 1 bij_betw_points_and_set finite_imageD inj_img set_def by auto
    qed

    text\<open>
      We establish the connection between the membership relation defined for hereditarily
      finite sets and the corresponding membership relation associated with the set category.
    \<close>

    lemma arr_of_membI [intro]:
    assumes "x \<^bold>\<in> ide_to_hf a"
    shows "arr_of x \<in> set a"
    proof -
      let ?X = "inv_into (set a) elem_of x"
      have "x = elem_of ?X \<and> ?X \<in> set a"
        using assms
        by (simp add: f_inv_into_f ide_to_hf_def inv_into_into)
      thus ?thesis
        by (metis (no_types, lifting) arr_of_elem_of elem_set_implies_incl_in
            elem_set_implies_set_eq_singleton incl_in_def mem_Collect_eq terminal_char2)
    qed

    lemma elem_of_membI [intro]:
    assumes "ide a" and "x \<in> set a"
    shows "elem_of x \<^bold>\<in> ide_to_hf a"
    proof -
      have "finite (elem_of ` set a)"
        using assms ide_implies_finite_set [of a] by simp
      hence "elem_of x \<in> hfset (ide_to_hf a)"
        using assms ide_to_hf_def hfset_HF [of "elem_of ` set a"] by simp
      thus ?thesis
        using hmem_def by blast
    qed

    text\<open>
      We show that each hom-set \<open>hom a b\<close> is in bijective correspondence with
      the elements of the hereditarily finite set \<open>hfun (ide_to_hf a) (ide_to_hf b)\<close>.
    \<close>

    definition arr_to_hfun
    where "arr_to_hfun f = \<lbrace>XY \<^bold>\<in> ide_to_hf (dom f) * ide_to_hf (cod f).
                              hsnd XY = elem_of (Fun f (arr_of (hfst XY)))\<rbrace>"

    definition hfun_to_arr
    where "hfun_to_arr B C F =
           mkArr (arr_of ` hfset B) (arr_of ` hfset C) (\<lambda>x. arr_of (happ F (elem_of x)))"

    lemma hfun_arr_to_hfun:
    assumes "arr f"
    shows "hfun (ide_to_hf (dom f)) (ide_to_hf (cod f)) (arr_to_hfun f)"
    proof
      show "arr_to_hfun f \<le> ide_to_hf (dom f) * ide_to_hf (cod f)"
        using assms arr_to_hfun_def by auto
      show "\<And>X. X \<^bold>\<in> ide_to_hf (dom f) \<Longrightarrow> \<exists>!Y. \<langle>X, Y\<rangle> \<^bold>\<in> arr_to_hfun f"
      proof
        fix X
        assume X: "X \<^bold>\<in> ide_to_hf (dom f)"
        show "\<langle>X, elem_of (Fun f (arr_of X))\<rangle> \<^bold>\<in> arr_to_hfun f"
        proof -
          have "\<langle>X, elem_of (Fun f (arr_of X))\<rangle> \<^bold>\<in> \<lbrace>XY \<^bold>\<in> ide_to_hf (dom f) * ide_to_hf (cod f).
                     hsnd XY = elem_of (Fun f (arr_of (hfst XY)))\<rbrace>"
          proof -
            have "hsnd \<langle>X, elem_of (Fun f (arr_of X))\<rangle> =
                  elem_of (Fun f (arr_of (hfst \<langle>X, elem_of (Fun f (arr_of X))\<rangle>)))"
              using assms X by simp
            moreover have "\<langle>X, elem_of (Fun f (arr_of X))\<rangle> \<^bold>\<in> ide_to_hf (dom f) * ide_to_hf (cod f)"
            proof -
              have "elem_of (Fun f (arr_of X)) \<^bold>\<in> ide_to_hf (cod f)"
              proof (intro elem_of_membI)
                show "ide (cod f)"
                  using assms ide_cod by simp
                show "Fun f (arr_of X) \<in> Cod f"
                  using assms X Fun_mapsto arr_of_membI by auto
              qed
              thus ?thesis
                using X by simp
            qed
            ultimately show ?thesis by simp
          qed
          thus ?thesis
            using arr_to_hfun_def by simp
        qed
        fix Y
        assume XY: "\<langle>X, Y\<rangle> \<^bold>\<in> arr_to_hfun f"
        show "Y = elem_of (Fun f (arr_of X))"
          using assms X XY arr_to_hfun_def by auto
      qed
      show "\<And>X Y. \<langle>X, Y\<rangle> \<^bold>\<in> arr_to_hfun f \<Longrightarrow> Y \<^bold>\<in> ide_to_hf (cod f)"
        using assms arr_to_hfun_def ide_to_hf_def
              \<open>arr_to_hfun f \<le> ide_to_hf (dom f) * ide_to_hf (cod f)\<close>
        by blast
    qed

    lemma arr_to_hfun_in_hexp:
    assumes "arr f"
    shows "arr_to_hfun f \<^bold>\<in> hexp (ide_to_hf (dom f)) (ide_to_hf (cod f))"
      using assms arr_to_hfun_def hfun_arr_to_hfun hexp_def by auto

    lemma hfun_to_arr_in_hom:
    assumes "hfun B C F"
    shows "\<guillemotleft>hfun_to_arr B C F : hf_to_ide B \<rightarrow> hf_to_ide C\<guillemotright>"
    proof
      let ?f = "mkArr (arr_of ` hfset B) (arr_of ` hfset C) (\<lambda>x. arr_of (happ F (elem_of x)))"
      have 0: "arr ?f"
      proof -
        have "arr_of ` hfset B \<subseteq> Univ \<and> arr_of ` hfset C \<subseteq> Univ"
          using arr_of_mapsto by auto
        moreover have "(\<lambda>x. arr_of (happ F (elem_of x))) \<in> arr_of ` hfset B \<rightarrow> arr_of ` hfset C"
        proof
          fix x
          assume x: "x \<in> arr_of ` hfset B"
          have "happ F (elem_of x) \<in> hfset C"
            using assms x happ_mapsto hfun_in_hexp
            by (metis elem_of_arr_of HF_hfset finite_hfset hmem_HF_iff imageE)
          thus "arr_of (happ F (elem_of x)) \<in> arr_of ` hfset C"
            by simp
        qed
        ultimately show ?thesis
          using arr_mkArr
          by (meson finite_hfset finite_iff_ordLess_natLeq finite_imageI)
      qed
      show 1: "arr (hfun_to_arr B C F)"
        using 0 hfun_to_arr_def by simp
      show "dom (hfun_to_arr B C F) = hf_to_ide B"
        using 1 hfun_to_arr_def hf_to_ide_def dom_mkArr by auto
      show "cod (hfun_to_arr B C F) = hf_to_ide C"
        using 1 hfun_to_arr_def hf_to_ide_def cod_mkArr by auto
    qed

    text\<open>
      The comprehension notation from @{theory HereditarilyFinite.HF} interferes in an
      unfortunate way with the restriction notation from @{theory "HOL-Library.FuncSet"},
      making it impossible to use both in the present context.
    \<close>

    lemma Fun_char:
    assumes "arr f"
    shows "Fun f = restrict (\<lambda>x. arr_of (happ (arr_to_hfun f) (elem_of x))) (Dom f)"
    proof
      fix x
      show "Fun f x = restrict (\<lambda>x. arr_of (happ (arr_to_hfun f) (elem_of x))) (Dom f) x"
      proof (cases "x \<in> Dom f")
        show "x \<notin> Dom f \<Longrightarrow> ?thesis"
          using assms Fun_mapsto Fun_def restrict_apply by simp
        show "x \<in> Dom f \<Longrightarrow> ?thesis"
        proof -
          assume x: "x \<in> Dom f"
          have 1: "hfun (ide_to_hf (dom f)) (ide_to_hf (cod f)) (arr_to_hfun f)"
            using assms app_def arr_to_hfun_def hfun_arr_to_hfun
                  the1_equality [of "\<lambda>y. \<langle>elem_of x, y\<rangle> \<^bold>\<in> arr_to_hfun f" "elem_of (Fun f x)"]
            by simp
          have 2: "\<exists>!Y. \<langle>elem_of x, Y\<rangle> \<^bold>\<in> arr_to_hfun f"
            using assms x 1 hfunE elem_of_membI ide_dom
            by (metis (no_types, lifting))
          have "Fun f x = arr_of (elem_of (Fun f x))"
          proof -
            have "Fun f x \<in> Univ"
              using assms x ide_cod Fun_mapsto [of f] set_ide_char by blast
            thus ?thesis
              using arr_of_elem_of by simp
          qed
          also have "... = arr_of (happ (arr_to_hfun f) (elem_of x))"
          proof -
            have "\<langle>elem_of x, elem_of (Fun f x)\<rangle> \<^bold>\<in> arr_to_hfun f"
            proof -
              have "\<langle>elem_of x, elem_of (Fun f x)\<rangle> \<^bold>\<in> ide_to_hf (dom f) * ide_to_hf (cod f)"
                using assms x ide_dom ide_cod Fun_mapsto by fast
              moreover have "elem_of (Fun f x) = elem_of (Fun f (arr_of (elem_of x)))"
                by (metis (no_types, lifting) arr_of_elem_of setp_set_ide assms ide_dom subsetD x)
              ultimately show ?thesis
                using arr_to_hfun_def by auto
            qed
            moreover have "\<langle>elem_of x, happ (arr_to_hfun f) (elem_of x)\<rangle> \<^bold>\<in> arr_to_hfun f"
              using assms x 1 2 app_equality hfun_def by blast
            ultimately show ?thesis
              using 2 by fastforce
          qed
          also have "... = restrict (\<lambda>x. arr_of (happ (arr_to_hfun f) (elem_of x))) (Dom f) x"
            using assms x ide_dom by auto
          finally show ?thesis by simp
        qed
      qed
    qed

    lemma Fun_hfun_to_arr:
    assumes "hfun B C F"
    shows "Fun (hfun_to_arr B C F) = restrict (\<lambda>x. arr_of (happ F (elem_of x))) (arr_of ` hfset B)"
    proof -
      have "arr (hfun_to_arr B C F)"
        using assms hfun_to_arr_in_hom by blast
      hence "arr (mkArr (arr_of ` hfset B) (arr_of ` hfset C) (\<lambda>x. arr_of (happ F (elem_of x))))"
        using hfun_to_arr_def by simp
      thus ?thesis
        using assms hfun_to_arr_def Fun_mkArr by simp
    qed

    lemma arr_of_img_hfset_ide_to_hf:
    assumes "ide a"
    shows "arr_of ` hfset (ide_to_hf a) = set a"
    proof -
      have "arr_of ` hfset (ide_to_hf a) = arr_of ` hfset (HF (elem_of ` set a))"
        using ide_to_hf_def by simp
      also have "... = arr_of ` elem_of ` set a"
        using assms ide_implies_finite_set(1) ide_char by auto
      also have "... = set a"
      proof -
        have "\<And>x. x \<in> set a \<Longrightarrow> arr_of (elem_of x) = x"
          using assms ide_char arr_of_elem_of setp_set_ide by blast
        thus ?thesis by force
      qed
      finally show ?thesis by blast
    qed

    lemma hfun_to_arr_arr_to_hfun:
    assumes "arr f"
    shows "hfun_to_arr (ide_to_hf (dom f)) (ide_to_hf (cod f)) (arr_to_hfun f) = f"
    proof -
      have 0: "hfun_to_arr (ide_to_hf (dom f)) (ide_to_hf (cod f)) (arr_to_hfun f) =
               mkArr (arr_of ` hfset (ide_to_hf (dom f))) (arr_of ` hfset (ide_to_hf (cod f)))
                     (\<lambda>x. arr_of (happ (arr_to_hfun f) (elem_of x)))"
        unfolding hfun_to_arr_def by blast
      also have "... = mkArr (Dom f) (Cod f)
                             (restrict (\<lambda>x. arr_of (happ (arr_to_hfun f) (elem_of x))) (Dom f))"
      proof (intro mkArr_eqI)
        show 1: "arr_of ` hfset (ide_to_hf (dom f)) = Dom f"
          using assms arr_of_img_hfset_ide_to_hf ide_dom by simp
        show 2: "arr_of ` hfset (ide_to_hf (cod f)) = Cod f"
          using assms arr_of_img_hfset_ide_to_hf ide_cod by simp
        show "arr (mkArr (arr_of ` hfset (ide_to_hf (dom f))) (arr_of ` hfset (ide_to_hf (cod f)))
                         (\<lambda>x. arr_of (happ (arr_to_hfun f) (elem_of x))))"
          using 0 1 2
          by (metis (no_types, lifting) arrI assms hfun_arr_to_hfun hfun_to_arr_in_hom)
        show "\<And>x. x \<in> arr_of ` hfset (ide_to_hf (dom f)) \<Longrightarrow>
                     arr_of (happ (arr_to_hfun f) (elem_of x)) =
                     restrict (\<lambda>x. arr_of (happ (arr_to_hfun f) (elem_of x))) (Dom f) x"
          using assms 1 by simp
      qed
      also have "... = mkArr (Dom f) (Cod f) (Fun f)"
        using assms Fun_char mkArr_eqI by simp
      also have "... = f"
        using assms mkArr_Fun by blast
      finally show ?thesis by simp
    qed

    lemma arr_to_hfun_hfun_to_arr:
    assumes "hfun B C F"
    shows "arr_to_hfun (hfun_to_arr B C F) = F"
    proof -
      have "arr_to_hfun (hfun_to_arr B C F) =
            \<lbrace>XY \<^bold>\<in> ide_to_hf (dom (hfun_to_arr B C F)) * ide_to_hf (cod (hfun_to_arr B C F)).
               hsnd XY = elem_of (Fun (hfun_to_arr B C F) (arr_of (hfst XY)))\<rbrace>"
        unfolding arr_to_hfun_def by blast
      also have
          "... = \<lbrace>XY \<^bold>\<in> ide_to_hf (mkIde (arr_of ` hfset B)) * ide_to_hf (mkIde (arr_of ` hfset C)).
                    hsnd XY = elem_of (Fun (hfun_to_arr B C F) (arr_of (hfst XY)))\<rbrace>"
        using assms hfun_to_arr_in_hom [of B C F] hf_to_ide_def
        by (metis (no_types, lifting) in_homE)
      also have
          "... = \<lbrace>XY \<^bold>\<in> ide_to_hf (mkIde (arr_of ` hfset B)) * ide_to_hf (mkIde (arr_of ` hfset C)).
                    hsnd XY = elem_of (restrict (\<lambda>x. arr_of (happ F (elem_of x))) (arr_of ` hfset B)
                                   (arr_of (hfst XY)))\<rbrace>"
        using assms Fun_hfun_to_arr by simp
      also have
          "... = \<lbrace>XY \<^bold>\<in> ide_to_hf (mkIde (arr_of ` hfset B)) * ide_to_hf (mkIde (arr_of ` hfset C)).
                    hsnd XY = elem_of (arr_of (happ F (elem_of (arr_of (hfst XY)))))\<rbrace>"
      proof -
        have
          1: "\<And>XY. XY \<^bold>\<in> ide_to_hf (mkIde (arr_of ` hfset B)) * ide_to_hf (mkIde (arr_of ` hfset C))
                     \<Longrightarrow> arr_of (hfst XY) \<in> arr_of ` hfset B"
        proof -
          fix XY
          assume
            XY: "XY \<^bold>\<in> ide_to_hf (mkIde (arr_of ` hfset B)) * ide_to_hf (mkIde (arr_of ` hfset C))"
          have "hfst XY \<^bold>\<in> ide_to_hf (mkIde (arr_of ` hfset B))"
            using XY by auto
          thus "arr_of (hfst XY) \<in> arr_of ` hfset B"
            using assms arr_of_membI [of "hfst XY" "mkIde (arr_of ` hfset B)"] set_mkIde
            by (metis (mono_tags, lifting) arrI arr_mkArr hfun_to_arr_def hfun_to_arr_in_hom)
        qed
        show ?thesis
        proof -
          have
            "\<And>XY. (XY \<^bold>\<in> ide_to_hf (mkIde (arr_of ` hfset B)) * ide_to_hf (mkIde (arr_of ` hfset C)) \<and>
                     hsnd XY = elem_of (restrict (\<lambda>x. arr_of (happ F (elem_of x))) (arr_of ` hfset B)
                                       (arr_of (hfst XY))))
                   \<longleftrightarrow>
                   (XY \<^bold>\<in> ide_to_hf (mkIde (arr_of ` hfset B)) * ide_to_hf (mkIde (arr_of ` hfset C)) \<and>
                     hsnd XY = elem_of (arr_of (happ F (elem_of (arr_of (hfst XY))))))"
            using 1 by auto
          thus ?thesis by blast
        qed
      qed
      also have
        "... = \<lbrace>XY \<^bold>\<in> ide_to_hf (mkIde (arr_of ` hfset B)) * ide_to_hf (mkIde (arr_of ` hfset C)).
                  hsnd XY = happ F (hfst XY)\<rbrace>"
        by simp
      also have "... = \<lbrace>XY \<^bold>\<in> B * C. hsnd XY = happ F (hfst XY)\<rbrace>"
        using assms hf_to_ide_def ide_to_hf_hf_to_ide by force
      also have "... = F"
        using assms happ_expansion by simp
      finally show ?thesis by simp
    qed

    lemma bij_betw_hom_hfun:
    assumes "ide a" and "ide b"
    shows "bij_betw arr_to_hfun (hom a b) {F. hfun (ide_to_hf a) (ide_to_hf b) F}"
    proof (intro bij_betwI)
      show "arr_to_hfun \<in> hom a b \<rightarrow> {F. hfun (ide_to_hf a) (ide_to_hf b) F}"
        using assms arr_to_hfun_in_hexp hexp_def hfun_arr_to_hfun by blast
      show "hfun_to_arr (ide_to_hf a) (ide_to_hf b)
              \<in> {F. hfun (ide_to_hf a) (ide_to_hf b) F} \<rightarrow> hom a b"
        using assms hfun_to_arr_in_hom
        by (metis (no_types, lifting) Pi_I hf_to_ide_ide_to_hf mem_Collect_eq)
      show "\<And>x. x \<in> hom a b \<Longrightarrow> hfun_to_arr (ide_to_hf a) (ide_to_hf b) (arr_to_hfun x) = x"
        using assms hfun_to_arr_arr_to_hfun by blast
      show "\<And>y. y \<in> {F. hfun (ide_to_hf a) (ide_to_hf b) F} \<Longrightarrow>
                  arr_to_hfun (hfun_to_arr (ide_to_hf a) (ide_to_hf b) y) = y"
        using assms arr_to_hfun_hfun_to_arr by simp
    qed

    text\<open>
      We next relate composition of arrows in the category to the corresponding operation
      on hereditarily finite sets.
    \<close>

    definition hcomp
    where "hcomp G F =
           \<lbrace>XZ \<^bold>\<in> hdomain F * hrange G. hsnd XZ = happ G (happ F (hfst XZ))\<rbrace>"

    lemma hfun_hcomp:
    assumes "hfun A B F" and "hfun B C G"
    shows "hfun A C (hcomp G F)"
    proof
      show "hcomp G F \<le> A * C"
        using assms hcomp_def hfun_def by auto
      show "\<And>X. X \<^bold>\<in> A \<Longrightarrow> \<exists>!Y. \<langle>X, Y\<rangle> \<^bold>\<in> hcomp G F"
      proof
        fix X
        assume X: "X \<^bold>\<in> A"
        show "\<langle>X, happ G (happ F X)\<rangle> \<^bold>\<in> hcomp G F"
          unfolding hcomp_def
          using assms X hfunE happ_mapsto hfun_in_hexp
          by (metis (mono_tags, lifting) HCollect_iff hfst_conv hfun_def hsnd_conv timesI)
        show "\<And>X Y. \<lbrakk>X \<^bold>\<in> A; \<langle>X, Y\<rangle> \<^bold>\<in> hcomp G F\<rbrakk> \<Longrightarrow> Y = happ G (happ F X)"
          unfolding hcomp_def by simp
      qed
      show "\<And>X Y. \<langle>X, Y\<rangle> \<^bold>\<in> hcomp G F \<Longrightarrow> Y \<^bold>\<in> C"
        unfolding hcomp_def
        using assms hfunE happ_mapsto hfun_in_hexp
        by (metis HCollectE hfun_def hsubsetCE timesD2)
    qed

    lemma arr_to_hfun_comp:
    assumes "seq g f"
    shows "arr_to_hfun (comp g f) = hcomp (arr_to_hfun g) (arr_to_hfun f)"
    proof -
      have 1: "hdomain (arr_to_hfun f) = ide_to_hf (dom f)"
        using assms hfun_arr_to_hfun hfun_def by blast
      have "arr_to_hfun (comp g f) =
            \<lbrace>XZ \<^bold>\<in> ide_to_hf (dom f) * ide_to_hf (cod g).
               hsnd XZ = elem_of (Fun (comp g f) (arr_of (hfst XZ)))\<rbrace>"
        unfolding arr_to_hfun_def comp_def
        using assms by fastforce
      also have "... = \<lbrace>XZ \<^bold>\<in> hdomain (arr_to_hfun f) * hrange (arr_to_hfun g).
                          hsnd XZ = happ (arr_to_hfun g) (happ (arr_to_hfun f) (hfst XZ))\<rbrace>"
      proof
        fix XZ
        have "hfst XZ \<^bold>\<in> hdomain (arr_to_hfun f)
                 \<Longrightarrow> hsnd XZ \<^bold>\<in> ide_to_hf (cod g) \<and>
                       hsnd XZ = elem_of (Fun (comp g f) (arr_of (hfst XZ)))
                      \<longleftrightarrow>
                     hsnd XZ \<^bold>\<in> hrange (arr_to_hfun g) \<and>
                       hsnd XZ = happ (arr_to_hfun g) (happ (arr_to_hfun f) (hfst XZ))"
        proof
          assume XZ: "hfst XZ \<^bold>\<in> hdomain (arr_to_hfun f)"
          have 2: "arr_of (hfst XZ) \<in> Dom f"
            using XZ 1 hfsetcat.arr_of_membI by auto
          have 3: "arr_of (happ (arr_to_hfun f) (hfst XZ)) \<in> Dom g"
            using assms XZ 2
            by (metis (no_types, lifting) "1" happ_mapsto(1) hfsetcat.arr_of_membI
                arr_to_hfun_in_hexp seqE)
          have 4: "elem_of (Fun (comp g f) (arr_of (hfst XZ))) =
                   happ (arr_to_hfun g) (happ (arr_to_hfun f) (hfst XZ))"
          proof -
            have "elem_of (Fun (comp g f) (arr_of (hfst XZ))) =
                  elem_of (restrict (Fun g o Fun f) (Dom f) (arr_of (hfst XZ)))"
              using assms Fun_comp Fun_char by simp
            also have "... = elem_of ((Fun g o Fun f) (arr_of (hfst XZ)))"
              using XZ 2 by auto
            also have "... = elem_of (Fun g (Fun f (arr_of (hfst XZ))))"
              by simp
            also have
              "... = elem_of (Fun g (restrict (\<lambda>x. arr_of (happ (arr_to_hfun f) (elem_of x))) (Dom f)
                                           (arr_of (hfst XZ))))"
            proof -
              have "Fun f = restrict (\<lambda>x. arr_of (happ (arr_to_hfun f) (elem_of x))) (Dom f)"
                using assms Fun_char [of f] by blast
              thus ?thesis by simp
            qed
            also have "... = elem_of (Fun g (arr_of (happ (arr_to_hfun f) (hfst XZ))))"
              using 2 by simp
            also have "... = elem_of (restrict (\<lambda>x. arr_of (happ (arr_to_hfun g) (elem_of x))) (Dom g)
                                            (arr_of (happ (arr_to_hfun f) (hfst XZ))))"
            proof -
              have "Fun g = restrict (\<lambda>x. arr_of (happ (arr_to_hfun g) (elem_of x))) (Dom g)"
                using assms Fun_char [of g] by blast
              thus ?thesis by simp
            qed
            also have "... = happ (arr_to_hfun g) (happ (arr_to_hfun f) (hfst XZ))"
              using 3 by simp
            finally show ?thesis by blast
          qed
          have 5: "elem_of (Fun (comp g f) (arr_of (hfst XZ))) \<^bold>\<in> hrange (arr_to_hfun g)"
          proof -
            have "happ (arr_to_hfun g) (happ (arr_to_hfun f) (hfst XZ)) \<^bold>\<in> hrange (arr_to_hfun g)"
              using assms 1 3 XZ hfun_arr_to_hfun happ_mapsto arr_to_hfun_in_hexp arr_to_hfun_def
              by (metis (no_types, lifting) seqE)
            thus ?thesis
              using XZ 4 by simp
          qed
          show "hsnd XZ \<^bold>\<in> ide_to_hf (cod g) \<and>
                  hsnd XZ = elem_of (Fun (comp g f) (arr_of (hfst XZ)))
                          \<Longrightarrow>
                hsnd XZ \<^bold>\<in> hrange (arr_to_hfun g) \<and>
                  hsnd XZ = happ (arr_to_hfun g) (happ (arr_to_hfun f) (hfst XZ))"
            using XZ 4 5 by simp
          show "hsnd XZ \<^bold>\<in> hrange (arr_to_hfun g) \<and>
                  hsnd XZ = happ (arr_to_hfun g) (happ (arr_to_hfun f) (hfst XZ))
                          \<Longrightarrow>
                hsnd XZ \<^bold>\<in> ide_to_hf (cod g) \<and>
                  hsnd XZ = elem_of (Fun (comp g f) (arr_of (hfst XZ)))"
            using assms XZ 1 4
            by (metis (no_types, lifting) arr_to_hfun_in_hexp happ_mapsto(1) seqE)
        qed
        thus "XZ \<^bold>\<in> \<lbrace>XZ \<^bold>\<in> ide_to_hf (dom f) * ide_to_hf (cod g).
                      hsnd XZ = elem_of (Fun (comp g f) (arr_of (hfst XZ)))\<rbrace>
                \<longleftrightarrow>
              XZ \<^bold>\<in> \<lbrace>XZ \<^bold>\<in> hdomain (arr_to_hfun f) * hrange (arr_to_hfun g).
                      hsnd XZ = happ (arr_to_hfun g) (happ (arr_to_hfun f) (hfst XZ))\<rbrace>"
          using 1 is_hpair_def by auto
      qed
      also have "... = hcomp (arr_to_hfun g) (arr_to_hfun f)"
        using assms arr_to_hfun_def hcomp_def by simp
      finally show ?thesis by simp
    qed

    lemma hfun_to_arr_hcomp:
    assumes "hfun A B F" and "hfun B C G"
    shows "hfun_to_arr A C (hcomp G F) = comp (hfun_to_arr B C G) (hfun_to_arr A B F)"
    proof -
      have 1: "arr_to_hfun (hfun_to_arr A C (hcomp G F)) =
               arr_to_hfun (comp (hfun_to_arr B C G) (hfun_to_arr A B F))"
      proof -
        have "arr_to_hfun (comp (hfun_to_arr B C G) (hfun_to_arr A B F)) =
              hcomp (arr_to_hfun (hfun_to_arr B C G)) (arr_to_hfun (hfun_to_arr A B F))"
          using assms arr_to_hfun_comp hfun_to_arr_in_hom by blast
        also have "... = hcomp G F"
          using assms by (simp add: arr_to_hfun_hfun_to_arr)
        also have "... = arr_to_hfun (hfun_to_arr A C (hcomp G F))"
        proof -
          have "hfun A C (hcomp G F)"
            using assms hfun_hcomp by simp
          thus ?thesis
            by (simp add: arr_to_hfun_hfun_to_arr)
        qed
        finally show ?thesis by simp
      qed
      show ?thesis
      proof -
        have "hfun_to_arr A C (hcomp G F) \<in> hom (hf_to_ide A) (hf_to_ide C)"
          using assms hfun_hcomp hf_to_ide_def hfun_to_arr_in_hom by auto
        moreover have "comp (hfun_to_arr B C G) (hfun_to_arr A B F)
                          \<in> hom (hf_to_ide A) (hf_to_ide C)"
          using assms hfun_to_arr_in_hom hf_to_ide_def
          by (metis (no_types, lifting) comp_in_homI mem_Collect_eq)
        moreover have "inj_on arr_to_hfun (hom (hf_to_ide A) (hf_to_ide C))"
        proof -
          have "ide (hf_to_ide A) \<and> ide (hf_to_ide C)"
            using assms hf_to_ide_mapsto by auto
          thus ?thesis
            using bij_betw_hom_hfun [of "hf_to_ide A" "hf_to_ide C"] bij_betw_imp_inj_on
            by auto
        qed
        ultimately show ?thesis
          using 1 inj_on_def [of arr_to_hfun "hom (hf_to_ide A) (hf_to_ide C)"] by simp
      qed
    qed

    section "Binary Products"

    text\<open>
      The category of hereditarily finite sets has binary products,
      given by cartesian product of sets in the usual way.
    \<close>

    definition prod
    where "prod a b = hf_to_ide (ide_to_hf a * ide_to_hf b)"

    definition pr0
    where "pr0 a b = (if ide a \<and> ide b then
                         mkArr (set (prod a b)) (set b) (\<lambda>x. arr_of (hsnd (elem_of x)))
                      else null)"

    definition pr1
    where "pr1 a b = (if ide a \<and> ide b then
                         mkArr (set (prod a b)) (set a) (\<lambda>x. arr_of (hfst (elem_of x)))
                      else null)"

    definition tuple
    where "tuple f g = mkArr (set (dom f)) (set (prod (cod f) (cod g)))
                             (\<lambda>x. arr_of (hpair (elem_of (Fun f x)) (elem_of (Fun g x))))"

    lemma ide_prod:
    assumes "ide a" and "ide b"
    shows "ide (prod a b)"
      using assms prod_def hf_to_ide_mapsto ide_to_hf_mapsto by auto

    lemma pr1_in_hom [intro]:
    assumes "ide a" and "ide b"
    shows "\<guillemotleft>pr1 a b : prod a b \<rightarrow> a\<guillemotright>"
    proof
      show 0: "arr (pr1 a b)"
      proof -
        have "set (prod a b) \<subseteq> Univ \<and> finite (set (prod a b))"
          using assms ide_implies_finite_set(1) set_ideD(1) ide_prod by presburger
        moreover have "set a \<subseteq> Univ \<and> finite (set a)"
          using assms ide_char set_ide_char by blast
        moreover have "(\<lambda>x. arr_of (hfst (elem_of x))) \<in> set (prod a b) \<rightarrow> set a"
        proof (unfold prod_def)
          show "(\<lambda>x. arr_of (hfst (elem_of x))) \<in> set (hf_to_ide (ide_to_hf a * ide_to_hf b)) \<rightarrow> set a"
          proof
            fix x
              assume x: "x \<in> set (hf_to_ide (ide_to_hf a * ide_to_hf b))"
              have "elem_of x \<in> hfset (ide_to_hf a * ide_to_hf b)"
                using assms ide_char x
                by (metis (no_types, lifting) prod_def elem_of_membI HF_hfset UNIV_I hmem_HF_iff
                    ide_prod ide_to_hf_hf_to_ide)
              hence "hfst (elem_of x) \<^bold>\<in> ide_to_hf a"
                by (metis HF_hfset finite_hfset hfst_conv hmem_HF_iff timesE)
              thus "arr_of (hfst (elem_of x)) \<in> set a"
                using arr_of_membI by simp
          qed
        qed
        ultimately show ?thesis
          unfolding pr1_def
          using assms arr_mkArr finite_imp_setp by presburger
      qed
      show "dom (pr1 a b) = prod a b"
        using assms 0 ide_char ide_prod dom_mkArr
        by (metis (no_types, lifting) mkIde_set pr1_def)
      show "cod (pr1 a b) = a"
        using assms 0 ide_char ide_prod cod_mkArr
        by (metis (no_types, lifting) mkIde_set pr1_def)
    qed

    lemma pr1_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr (pr1 a b)" and "dom (pr1 a b) = prod a b" and "cod (pr1 a b) = a"
      using assms pr1_in_hom by blast+

    lemma pr0_in_hom [intro]:
    assumes "ide a" and "ide b"
    shows "\<guillemotleft>pr0 a b : prod a b \<rightarrow> b\<guillemotright>"
    proof
      show 0: "arr (pr0 a b)"
      proof -
        have "set (prod a b) \<subseteq> Univ \<and> finite (set (prod a b))"
          using setp_set_ide assms ide_implies_finite_set(1) ide_prod by presburger
        moreover have "set b \<subseteq> Univ \<and> finite (set b)"
          using assms ide_char set_ide_char by blast
        moreover have "(\<lambda>x. arr_of (hsnd (elem_of x))) \<in> set (prod a b) \<rightarrow> set b"
        proof (unfold prod_def)
          show "(\<lambda>x. arr_of (hsnd (elem_of x))) \<in> set (hf_to_ide (ide_to_hf a * ide_to_hf b)) \<rightarrow> set b"
          proof
            fix x
              assume x: "x \<in> set (hf_to_ide (ide_to_hf a * ide_to_hf b))"
              have "elem_of x \<in> hfset (ide_to_hf a * ide_to_hf b)"
                using assms ide_char x
                by (metis (no_types, lifting) prod_def elem_of_membI HF_hfset UNIV_I hmem_HF_iff
                    ide_prod ide_to_hf_hf_to_ide)
              hence "hsnd (elem_of x) \<^bold>\<in> ide_to_hf b"
                by (metis HF_hfset finite_hfset hsnd_conv hmem_HF_iff timesE)
              thus "arr_of (hsnd (elem_of x)) \<in> set b"
                using arr_of_membI by simp
          qed
        qed
        ultimately show ?thesis
          unfolding pr0_def
          using assms arr_mkArr finite_imp_setp by presburger
      qed
      show "dom (pr0 a b) = prod a b"
        using assms 0 ide_char ide_prod dom_mkArr
        by (metis (no_types, lifting) mkIde_set pr0_def)
      show "cod (pr0 a b) = b"
        using assms 0 ide_char ide_prod cod_mkArr
        by (metis (no_types, lifting) mkIde_set pr0_def)
    qed

    lemma pr0_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr (pr0 a b)" and "dom (pr0 a b) = prod a b" and "cod (pr0 a b) = b"
      using assms pr0_in_hom by blast+

    lemma arr_of_tuple_elem_of_membI:
    assumes "span f g" and "x \<in> Dom f"
    shows "arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle> \<in> set (prod (cod f) (cod g))"
    proof -
      have "Fun f x \<in> set (cod f)"
        using assms Fun_mapsto by blast
      moreover have "Fun g x \<in> set (cod g)"
        using assms Fun_mapsto by auto
      ultimately have "\<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>
                          \<^bold>\<in> ide_to_hf (cod f) * ide_to_hf (cod g)"
        using assms ide_cod by auto
      moreover have "set (prod (cod f) (cod g)) \<subseteq> Univ"
        using setp_set_ide assms(1) ide_cod ide_prod by presburger
      ultimately show ?thesis
        using prod_def arr_of_membI ide_to_hf_hf_to_ide by auto
    qed

    lemma tuple_in_hom [intro]:
    assumes "span f g"
    shows "\<guillemotleft>tuple f g : dom f \<rightarrow> prod (cod f) (cod g)\<guillemotright>"
    proof
      show 1: "arr (tuple f g)"
      proof -
        have "Dom f \<subseteq> Univ \<and> finite (Dom f)"
          using assms set_ideD(1) ide_dom ide_implies_finite_set(1) by presburger
        moreover have "set (prod (cod f) (cod g)) \<subseteq> Univ \<and> finite (set (prod (cod f) (cod g)))"
          using assms set_ideD(1) ide_cod ide_prod ide_implies_finite_set(1) by presburger
        moreover have "(\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>)
                          \<in> Dom f \<rightarrow> set (prod (cod f) (cod g))"
          using assms arr_of_tuple_elem_of_membI by simp
        ultimately show ?thesis
          using assms ide_prod tuple_def arr_mkArr ide_dom ide_cod by simp
      qed
      show "dom (tuple f g) = dom f"
        using assms 1 dom_mkArr ide_dom mkIde_set tuple_def by auto
      show "cod (tuple f g) = prod (cod f) (cod g)"
        using assms 1 cod_mkArr ide_cod mkIde_set tuple_def ide_prod by auto
    qed

    lemma tuple_simps [simp]:
    assumes "span f g"
    shows "arr (tuple f g)" and "dom (tuple f g) = dom f"
    and "cod (tuple f g) = prod (cod f) (cod g)"
      using assms tuple_in_hom by blast+

    lemma Fun_pr1:
    assumes "ide a" and "ide b"
    shows "Fun (pr1 a b) = restrict (\<lambda>x. arr_of (hfst (elem_of x))) (set (prod a b))"
      using assms pr1_def Fun_mkArr arr_char pr1_simps(1) by presburger

    lemma Fun_pr0:
    assumes "ide a" and "ide b"
    shows "Fun (pr0 a b) = restrict (\<lambda>x. arr_of (hsnd (elem_of x))) (set (prod a b))"
      using assms pr0_def Fun_mkArr arr_char pr0_simps(1) by presburger

    lemma Fun_tuple:
    assumes "span f g"
    shows "Fun (tuple f g) = restrict (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>) (Dom f)"
    proof -
      have "arr (tuple f g)"
        using assms tuple_in_hom by blast
      thus ?thesis
        using assms tuple_def Fun_mkArr by simp
    qed

    lemma pr1_tuple:
    assumes "span f g"
    shows "comp (pr1 (cod f) (cod g)) (tuple f g) = f"
    proof (intro arr_eqI\<^sub>S\<^sub>C)
      have pr1: "\<guillemotleft>pr1 (cod f) (cod g) : prod (cod f) (cod g) \<rightarrow> cod f\<guillemotright>"
        using assms ide_cod by blast
      have tuple: "\<guillemotleft>tuple f g : dom f \<rightarrow> prod (cod f) (cod g)\<guillemotright>"
        using assms by blast
      show par: "par (comp (pr1 (cod f) (cod g)) (tuple f g)) f"
        using assms pr1_in_hom tuple_in_hom
        by (metis (no_types, lifting) comp_in_homI' ide_cod in_homE)
      show "Fun (comp (pr1 (cod f) (cod g)) (tuple f g)) = Fun f"
      proof -
        have seq: "seq (pr1 (cod f) (cod g)) (tuple f g)"
          using par by blast
        have "Fun (comp (pr1 (cod f) (cod g)) (tuple f g)) =
              restrict (Fun (pr1 (cod f) (cod g)) \<circ> Fun (tuple f g)) (Dom (tuple f g))"
          using pr1 tuple seq Fun_comp by simp
        also have "... = restrict
                           (Fun (mkArr (set (prod (cod f) (cod g))) (Cod f)
                                       (\<lambda>x. arr_of (hfst (elem_of x)))) \<circ>
                            Fun (mkArr (Dom f) (set (prod (cod f) (cod g)))
                                       (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>)))
                           (Dom (tuple f g))"
          unfolding pr1_def tuple_def
          using assms ide_cod by presburger
        also have
          "... = restrict
                   (restrict (\<lambda>x. arr_of (hfst (elem_of x))) (set (prod (cod f) (cod g))) o
                      restrict (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>) (Dom f))
                   (Dom f)"
        proof -
          have "Fun (mkArr (set (prod (cod f) (cod g))) (Cod f) (\<lambda>x. arr_of (hfst (elem_of x)))) =
                restrict (\<lambda>x. arr_of (hfst (elem_of x))) (set (prod (cod f) (cod g)))"
            using assms Fun_mkArr ide_prod pr1
            by (metis (no_types, lifting) arrI ide_cod pr1_def)
          moreover have "Fun (mkArr (Dom f) (set (prod (cod f) (cod g)))
                                    (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>)) =
                         restrict (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>) (Dom f)"
            using assms Fun_mkArr ide_prod ide_cod tuple_def tuple arrI by simp
          ultimately show ?thesis
            using assms tuple_simps(2) by simp
        qed
        also have
          "... = restrict
                   ((\<lambda>x. arr_of (hfst (elem_of x))) o (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>))
                   (Dom f)"
          using assms tuple tuple_def arr_of_tuple_elem_of_membI by auto
        also have "... = restrict (Fun f) (Dom f)"
        proof
          fix x
          have "restrict ((\<lambda>x. arr_of (hfst (elem_of x))) o (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>))
                         (Dom f) x =
                restrict (\<lambda>x. arr_of (elem_of (Fun f x))) (Dom f) x"
            by simp
          also have "... = restrict (Fun f) (Dom f) x"
          proof (cases "x \<in> Dom f")
            show "x \<notin> Dom f \<Longrightarrow> ?thesis" by simp
            assume x: "x \<in> Dom f"
            have "Fun f x \<in> Cod f"
              using assms x Fun_mapsto arr_char by blast
            moreover have "Cod f \<subseteq> Univ"
              using setp_set_ide assms ide_cod by blast
            ultimately show ?thesis
              using assms arr_of_elem_of Fun_mapsto by auto
          qed
          finally show "restrict ((\<lambda>x. arr_of (hfst (elem_of x))) \<circ>
                                    (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>))
                                 (Dom f) x =
                        restrict (Fun f) (Dom f) x"
            by blast
        qed
        also have "... = Fun f"
          using assms par Fun_mapsto Fun_mkArr mkArr_Fun
          by (metis (no_types, lifting))
        finally show ?thesis by blast
      qed
    qed

    lemma pr0_tuple:
    assumes "span f g"
    shows "comp (pr0 (cod f) (cod g)) (tuple f g) = g"
    proof (intro arr_eqI\<^sub>S\<^sub>C)
      have pr0: "\<guillemotleft>pr0 (cod f) (cod g) : prod (cod f) (cod g) \<rightarrow> cod g\<guillemotright>"
        using assms ide_cod by blast
      have tuple: "\<guillemotleft>tuple f g : dom f \<rightarrow> prod (cod f) (cod g)\<guillemotright>"
        using assms by blast
      show par: "par (comp (pr0 (cod f) (cod g)) (tuple f g)) g"
        using assms pr0_in_hom tuple_in_hom
        by (metis (no_types, lifting) comp_in_homI' ide_cod in_homE)
      show "Fun (comp (pr0 (cod f) (cod g)) (tuple f g)) = Fun g"
      proof -
        have seq: "seq (pr0 (cod f) (cod g)) (tuple f g)"
          using par by blast
        have "Fun (comp (pr0 (cod f) (cod g)) (tuple f g)) =
              restrict (Fun (pr0 (cod f) (cod g)) \<circ> Fun (tuple f g)) (Dom (tuple f g))"
          using pr0 tuple seq Fun_comp by simp
        also have
          "... = restrict
                   (Fun (mkArr (set (prod (cod f) (cod g))) (Cod g)
                               (\<lambda>x. arr_of (hsnd (elem_of x)))) \<circ>
                    Fun (mkArr (Dom f) (set (prod (cod f) (cod g)))
                               (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>)))
                   (Dom (tuple f g))"
          unfolding pr0_def tuple_def
          using assms ide_cod by presburger
        also have "... = restrict
                           (restrict (\<lambda>x. arr_of (hsnd (elem_of x))) (set (prod (cod f) (cod g))) o
                            restrict (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>) (Dom g))
                           (Dom g)"
        proof -
          have "Fun (mkArr (set (prod (cod f) (cod g))) (Cod g) (\<lambda>x. arr_of (hsnd (elem_of x)))) =
                restrict (\<lambda>x. arr_of (hsnd (elem_of x))) (set (prod (cod f) (cod g)))"
            using assms Fun_mkArr ide_prod arrI
            by (metis (no_types, lifting) ide_cod pr0 pr0_def)
          moreover have "Fun (mkArr (Dom f) (set (prod (cod f) (cod g)))
                                    (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>)) =
                         restrict (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>) (Dom f)"
            using assms Fun_mkArr ide_prod ide_cod tuple_def tuple arrI by simp
          ultimately show ?thesis
            using assms tuple_simps(2) by simp
        qed
        also have "... = restrict
                           ((\<lambda>x. arr_of (hsnd (elem_of x))) o (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>))
                           (Dom g)"
          using assms tuple tuple_def arr_of_tuple_elem_of_membI by auto
        also have "... = restrict (Fun g) (Dom g)"
        proof
          fix x
          have "restrict ((\<lambda>x. arr_of (hsnd (elem_of x)))
                            o (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>))
                         (Dom g) x =
                restrict (\<lambda>x. arr_of (elem_of (Fun g x))) (Dom g) x"
            by simp
          also have "... = restrict (Fun g) (Dom g) x"
          proof (cases "x \<in> Dom g")
            show "x \<notin> Dom g \<Longrightarrow> ?thesis" by simp
            assume x: "x \<in> Dom g"
            have "Fun g x \<in> Cod g"
              using assms x Fun_mapsto arr_char by blast
            moreover have "Cod g \<subseteq> Univ"
              using assms set_ideD(1) ide_cod by blast
            ultimately show ?thesis
              using assms arr_of_elem_of Fun_mapsto by auto
          qed
          finally show "restrict ((\<lambda>x. arr_of (hsnd (elem_of x))) \<circ>
                                    (\<lambda>x. arr_of \<langle>elem_of (Fun f x), elem_of (Fun g x)\<rangle>))
                                 (Dom g) x =
                        restrict (Fun g) (Dom g) x"
            by blast
        qed
        also have "... = Fun g"
          using assms par Fun_mapsto Fun_mkArr mkArr_Fun
          by (metis (no_types, lifting))
        finally show ?thesis by blast
      qed
    qed

    lemma tuple_pr:
    assumes "ide a" and "ide b" and "\<guillemotleft>h : dom h \<rightarrow> prod a b\<guillemotright>"
    shows "tuple (comp (pr1 a b) h) (comp (pr0 a b) h) = h"
    proof (intro arr_eqI\<^sub>S\<^sub>C)
      have pr0: "\<guillemotleft>pr0 a b : prod a b \<rightarrow> b\<guillemotright>"
        using assms pr0_in_hom ide_cod by blast
      have pr1: "\<guillemotleft>pr1 a b : prod a b \<rightarrow> a\<guillemotright>"
        using assms pr1_in_hom ide_cod by blast
      have tuple: "\<guillemotleft>tuple (comp (pr1 a b) h) (comp (pr0 a b) h) : dom h \<rightarrow> prod a b\<guillemotright>"
        using assms pr0 pr1
        by (metis (no_types, lifting) cod_comp dom_comp pr0_simps(3) pr1_simps(3)
            seqI' tuple_in_hom)
      show par: "par (tuple (comp (pr1 a b) h) (comp (pr0 a b) h)) h"
        using assms tuple by (metis (no_types, lifting) in_homE)
      show "Fun (tuple (comp (pr1 a b) h) (comp (pr0 a b) h)) = Fun h"
      proof -
        have 1: "Fun (comp (pr1 a b) h) =
                 restrict (restrict (\<lambda>x. arr_of (hfst (elem_of x))) (set (prod a b)) \<circ> Fun h) (Dom h)"
          using assms pr1 Fun_comp Fun_pr1 seqI' by auto
        have 2: "Fun (comp (pr0 a b) h) =
                 restrict (restrict (\<lambda>x. arr_of (hsnd (elem_of x))) (set (prod a b)) \<circ> Fun h) (Dom h)"
          using assms pr0 Fun_comp Fun_pr0 seqI' by auto
        have "Fun (tuple (comp (pr1 a b) h) (comp (pr0 a b) h)) =
              restrict (\<lambda>x. arr_of \<langle>elem_of (restrict
                                       (restrict (\<lambda>x. arr_of (hfst (elem_of x))) (set (prod a b)) \<circ> Fun h)
                                                 (Dom h) x),
                                elem_of (restrict
                                       (restrict (\<lambda>x. arr_of (hsnd (elem_of x))) (set (prod a b)) \<circ> Fun h)
                                                 (Dom h) x)\<rangle>)
                       (Dom h)"
        proof -
          have "Dom (comp (pr1 a b) h) = Dom h"
            using assms pr1_in_hom
            by (metis (no_types, lifting) in_homE dom_comp seqI)
          moreover have "arr (mkArr (Dom (comp (pr1 a b) h))
                             (set (prod (cod (comp (pr1 a b) h)) (cod (comp (pr0 a b) h))))
                             (\<lambda>x. arr_of \<langle>elem_of (Fun (comp (pr1 a b) h) x),
                                      elem_of (Fun (comp (pr0 a b) h) x)\<rangle>))"
            using tuple unfolding tuple_def by blast
          ultimately show ?thesis
            using 1 2 tuple tuple_def
                  Fun_mkArr [of "Dom (comp (pr1 a b) h)"
                                 "set (prod (cod (comp (pr1 a b) h))
                                            (cod (comp (pr0 a b) h)))"
                                 "\<lambda>x. arr_of \<langle>elem_of (Fun (comp (pr1 a b) h) x),
                                          elem_of (Fun (comp (pr0 a b) h) x)\<rangle>"]
            by simp
        qed
        also have "... = Fun h"
        proof
          let ?f = "..."
          fix x
          show "?f x = Fun h x"
          proof -
            have "x \<notin> Dom h \<Longrightarrow> ?f x = Fun h x"
            proof -
              assume x: "x \<notin> Dom h"
              have "restrict ?f (Dom h) x = undefined"
                using assms x restrict_apply by auto
              also have "... = Fun h x"
              proof -
                have "arr h"
                  using assms by blast
                thus ?thesis
                  using assms x Fun_mapsto [of h] extensional_arb [of "Fun h" "Dom h" x]
                  by simp
              qed
              finally show ?thesis by auto
            qed
            moreover have "x \<in> Dom h \<Longrightarrow> ?f x = Fun h x"
            proof -
              assume x: "x \<in> Dom h"
              have 1: "Fun h x \<in> set (prod a b)"
              proof -
                have "Fun h x \<in> Cod h"
                  using assms x Fun_mapsto [of h] by blast
                moreover have "Cod h = set (prod a b)"
                  using assms ide_prod
                  by (metis (no_types, lifting) in_homE)
                ultimately show ?thesis by fast
              qed
              have "?f x = arr_of \<langle>hfst (elem_of (Fun h x)), hsnd (elem_of (Fun h x))\<rangle>"
                using x 1 by simp
              also have "... = arr_of (elem_of (Fun h x))"
              proof -
                have "elem_of (Fun h x) \<^bold>\<in> ide_to_hf a * ide_to_hf b"
                  using assms x 1 par
                  by (metis (no_types, lifting) prod_def elem_of_membI UNIV_I ide_prod
                      ide_to_hf_hf_to_ide)
                thus ?thesis
                  using x is_hpair_def by auto
              qed
              also have "... = Fun h x"
                using 1 arr_of_elem_of assms set_ideD(1) ide_prod by blast
              finally show ?thesis by blast
            qed
            ultimately show ?thesis by blast
          qed
        qed
        finally show ?thesis by blast
      qed
    qed

    interpretation HF': elementary_category_with_binary_products comp pr0 pr1
    proof
      show "\<And>a b. \<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> span (pr1 a b) (pr0 a b)"
        using pr0_simps(1) pr0_simps(2) pr1_simps(1) pr1_simps(2) by auto
      show "\<And>a b. \<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> cod (pr0 a b) = b"
        using pr0_simps(1-3) by blast
      show "\<And>a b. \<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> cod (pr1 a b) = a"
        using pr1_simps(1-3) by blast
      show "\<And>f g. span f g \<Longrightarrow>
                    \<exists>!l. comp (pr1 (cod f) (cod g)) l = f \<and> comp (pr0 (cod f) (cod g)) l = g"
      proof
        fix f g
        assume fg: "span f g"
        show "comp (pr1 (cod f) (cod g)) (tuple f g) = f \<and>
              comp (pr0 (cod f) (cod g)) (tuple f g) = g"
          using fg pr0_simps pr1_simps tuple_simps pr0_tuple pr1_tuple by presburger
        show "\<And>l. \<lbrakk>comp (pr1 (cod f) (cod g)) l = f \<and> comp (pr0 (cod f) (cod g)) l = g\<rbrakk>
                      \<Longrightarrow> l = tuple f g "
        proof -
          fix l
          assume l: "comp (pr1 (cod f) (cod g)) l = f \<and> comp (pr0 (cod f) (cod g)) l = g"
          show "l = tuple f g"
            using fg l tuple_pr
            by (metis (no_types, lifting) arr_iff_in_hom ide_cod seqE pr0_simps(2))
        qed
      qed
    qed

    text\<open>
      For reasons of economy of locale parameters, the notion \<open>prod\<close> is a defined notion
      of the @{locale elementary_category_with_binary_products} locale.
      However, we need to be able to relate this notion to that of cartesian product of
      hereditarily finite sets, which we have already used to give a definition of \<open>prod\<close>.
      The locale assumptions for @{locale elementary_cartesian_closed_category} refer
      specifically to \<open>HF'.prod\<close>, even though in the end the notion itself does not depend
      on that choice.  To be able to show that the locale assumptions of
      @{locale elementary_cartesian_closed_category} are satisfied, we need to use a choice
      of products that we can relate to the cartesian product of hereditarily
      finite sets.  We therefore need to show that our previously defined \<open>prod\<close> coincides
      (on objects) with the one defined in the @{locale elementary_category_with_binary_products} locale;
      \emph{i.e.}~\<open>HF'.prod\<close>.  Note that the latter is defined for all arrows,
      not just identity arrows, so we need to use that for the subsequent definitions and proofs.
    \<close>

    lemma prod_ide_eq:
    assumes "ide a" and "ide b"
    shows "prod a b = HF'.prod a b"
      using assms prod_def HF'.pr_simps(2) HF'.prod_def pr0_simps(2) by presburger

    lemma tuple_span_eq:
    assumes "span f g"
    shows "tuple f g = HF'.tuple f g"
      using assms tuple_def HF'.tuple_def
      by (metis (no_types, lifting) HF'.tuple_eqI ide_cod pr0_tuple pr1_tuple)

    section "Exponentials"

    text\<open>
      We now turn our attention to exponentials.
    \<close>

    definition exp
    where "exp b c = hf_to_ide (hexp (ide_to_hf b) (ide_to_hf c))"

    definition eval
    where "eval b c = mkArr (set (HF'.prod (exp b c) b)) (set c)
                            (\<lambda>x. arr_of (happ (hfst (elem_of x)) (hsnd (elem_of x))))"

    definition \<Lambda>
    where "\<Lambda> a b c f = mkArr (set a) (set (exp b c))
                             (\<lambda>x. arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c)
                                                 (arr_to_hfun f))
                                           (elem_of x)))"

    lemma ide_exp:
    assumes "ide b" and "ide c"
    shows "ide (exp b c)"
      using assms exp_def hf_to_ide_mapsto ide_to_hf_mapsto by auto

    lemma hfset_ide_to_hf:
    assumes "ide a"
    shows "hfset (ide_to_hf a) = elem_of ` set a"
      using assms ide_to_hf_def ide_implies_finite_set(1) by auto

    lemma eval_in_hom [intro]:
    assumes "ide b" and "ide c"
    shows "in_hom (eval b c) (HF'.prod (exp b c) b) c"
    proof
      show 1: "arr (eval b c)"
      proof (unfold eval_def arr_mkArr, intro conjI)
        show "set (HF'.prod (exp b c) b) \<subseteq> Univ"
          using HF'.ide_prod assms set_ideD(1) ide_exp by presburger
        show "set c \<subseteq> Univ"
          using assms set_ideD(1) by blast
        show "(\<lambda>x. arr_of (happ (hfst (elem_of x)) (hsnd (elem_of x))))
                 \<in> set (HF'.prod (exp b c) b) \<rightarrow> set c"
        proof
          fix x
          assume "x \<in> set (HF'.prod (exp b c) b)"
          hence x: "x \<in> set (prod (exp b c) b)"
            using assms prod_ide_eq ide_exp by auto
          show "arr_of (happ (hfst (elem_of x)) (hsnd (elem_of x))) \<in> set c"
          proof (intro arr_of_membI)
            show "happ (hfst (elem_of x)) (hsnd (elem_of x)) \<^bold>\<in> ide_to_hf c"
            proof -
              have 1: "elem_of x \<^bold>\<in> ide_to_hf (exp b c) * ide_to_hf b"
              proof -
                have "elem_of x \<^bold>\<in> ide_to_hf (prod (exp b c) b)"
                  using assms x elem_of_membI ide_prod ide_exp by simp
                thus ?thesis
                  using assms x prod_def ide_to_hf_hf_to_ide by auto
              qed
              have "hfst (elem_of x) \<^bold>\<in> hexp (ide_to_hf b) (ide_to_hf c)"
                using assms 1 x exp_def ide_to_hf_hf_to_ide by auto
              moreover have "hsnd (elem_of x) \<^bold>\<in> ide_to_hf b"
                using assms 1 by auto
              ultimately show ?thesis
                using happ_mapsto [of "hfst (elem_of x)" "ide_to_hf b" "ide_to_hf c"
                                      "hsnd (elem_of x)"]
                by simp
            qed
          qed
        qed
        show "finite (elem_of ` set (HF'.prod (exp b c) b))"
          using HF'.ide_prod setp_set_ide assms ide_exp by presburger
        show "finite (elem_of ` set c)"
          using setp_set_ide assms(2) by blast
      qed
      show "dom (eval b c) = HF'.prod (exp b c) b"
        using assms 1 ide_char HF'.ide_prod ide_exp dom_mkArr eval_def
        by (metis (no_types, lifting) mkIde_set)
      show "cod (eval b c) = c"
        using assms 1 ide_char cod_mkArr eval_def
        by (metis (no_types, lifting) mkIde_set)
    qed

    lemma eval_simps [simp]:
    assumes "ide b" and "ide c"
    shows "arr (eval b c)"
    and "dom (eval b c) = HF'.prod (exp b c) b"
    and "cod (eval b c) = c"
      using assms eval_in_hom by blast+

    lemma hlam_arr_to_hfun_in_hexp:
    assumes "ide a" and "ide b" and "ide c"
    and "in_hom f (prod a b) c"
    shows "hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c) (arr_to_hfun f)
             \<^bold>\<in> hexp (ide_to_hf a) (ide_to_hf (exp b c))"
      using assms hfun_in_hexp hfun_hlam
      by (metis (no_types, lifting) prod_def HCollect_iff in_homE UNIV_I
          arr_to_hfun_in_hexp exp_def hexp_def ide_to_hf_hf_to_ide)

    lemma lam_in_hom [intro]:
    assumes "ide a" and "ide b" and "ide c"
    and "in_hom f (prod a b) c"
    shows "in_hom (\<Lambda> a b c f) a (exp b c)"
    proof
      show 1: "arr (\<Lambda> a b c f)"
      proof (unfold \<Lambda>_def arr_mkArr, intro conjI)
        show "set a \<subseteq> Univ"
          using assms(1) set_ideD(1) by blast
        show "set (exp b c) \<subseteq> Univ"
          using assms(2-3) set_ideD(1) ide_exp ide_char by blast
        show "finite (elem_of ` set a)"
          using assms(1) set_ideD(1) setp_set_ide by presburger
        show "finite (elem_of ` set (exp b c))"
          using assms(2-3) set_ideD(1) setp_set_ide ide_exp by presburger
        show "(\<lambda>x. arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c) (arr_to_hfun f))
                            (elem_of x)))
                 \<in> set a \<rightarrow> set (exp b c)"
        proof
          fix x
          assume x: "x \<in> set a"
          show "arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c) (arr_to_hfun f))
                         (elem_of x))
                     \<in> set (exp b c)"
            using assms x hlam_arr_to_hfun_in_hexp ide_to_hf_def elem_of_membI happ_mapsto
                  arr_of_membI
            by meson
        qed
      qed
      show "dom (\<Lambda> a b c f) = a"
        using assms(1) 1 \<Lambda>_def ide_char dom_mkArr mkIde_set by auto
      show "cod (\<Lambda> a b c f) = exp b c"
        using assms(2-3) 1 \<Lambda>_def cod_mkArr ide_exp mkIde_set by auto
    qed

    lemma lam_simps [simp]:
    assumes "ide a" and "ide b" and "ide c"
    and "in_hom f (prod a b) c"
    shows "arr (\<Lambda> a b c f)"
    and "dom (\<Lambda> a b c f) = a"
    and "cod (\<Lambda> a b c f) = exp b c"
      using assms lam_in_hom by blast+

    lemma Fun_lam:
    assumes "ide a" and "ide b" and "ide c"
    and "in_hom f (prod a b) c"
    shows "Fun (\<Lambda> a b c f) =
           restrict (\<lambda>x. arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c) (arr_to_hfun f))
                                  (elem_of x)))
                    (set a)"
      using assms arr_char lam_simps(1) \<Lambda>_def Fun_mkArr by simp

    lemma Fun_eval:
    assumes "ide b" and "ide c"
    shows "Fun (eval b c) = restrict (\<lambda>x. arr_of (happ (hfst (elem_of x)) (hsnd (elem_of x))))
                                     (set (HF'.prod (exp b c) b))"
      using assms arr_char eval_simps(1) eval_def Fun_mkArr by force

    lemma Fun_prod:
    assumes "arr f" and "arr g" and "x \<in> set (prod (dom f) (dom g))"
    shows "Fun (HF'.prod f g) x = arr_of \<langle>elem_of (Fun f (arr_of (hfst (elem_of x)))),
                                     elem_of (Fun g (arr_of (hsnd (elem_of x))))\<rangle>"
    proof -
      have 1: "span (comp f (pr1 (dom f) (dom g))) (comp g (pr0 (dom f) (dom g)))"
        using assms
        by (metis (no_types, lifting) HF'.prod_def HF'.prod_simps(1) HF'.tuple_ext not_arr_null)
      have 2: "Dom (comp f (pr1 (dom f) (dom g))) = set (prod (dom f) (dom g))"
        using assms
        by (metis (mono_tags, lifting) 1 dom_comp ide_dom pr0_simps(2))
      have 3: "Dom (comp g (pr0 (dom f) (dom g))) = set (prod (dom f) (dom g))"
        using assms 1 2 by force
      have "Fun (HF'.prod f g) x =
            Fun (HF'.tuple (comp f (pr1 (dom f) (dom g))) (comp g (pr0 (dom f) (dom g)))) x"
        using assms(3) HF'.prod_def by simp
      also have "... = restrict (\<lambda>x. arr_of \<langle>elem_of (Fun (comp f (pr1 (dom f) (dom g))) x),
                                         elem_of (Fun (comp g (pr0 (dom f) (dom g))) x)\<rangle>)
                                (Dom (comp f (pr1 (dom f) (dom g))))
                                x"
        using assms 1 tuple_span_eq Fun_tuple by simp
      also have "... = arr_of \<langle>elem_of (Fun (comp f (pr1 (dom f) (dom g))) x),
                           elem_of (Fun (comp g (pr0 (dom f) (dom g))) x)\<rangle>"
        using assms(3) 2 by simp
      also have "... = arr_of \<langle>elem_of (Fun f (arr_of (hfst (elem_of x)))),
                           elem_of (Fun g (arr_of (hsnd (elem_of x))))\<rangle>"
      proof -
        have "Fun (comp f (pr1 (dom f) (dom g))) x = Fun f (arr_of (hfst (elem_of x)))"
        proof -
          (* TODO: Figure out what is making this proof so "stiff". *)
          have 4: "seq f (pr1 (dom f) (dom g))"
            using assms 1 by blast
          have "Fun (comp f (pr1 (dom f) (dom g))) x =
                restrict (Fun f \<circ> Fun (pr1 (dom f) (dom g))) (Dom (pr1 (dom f) (dom g))) x"
            using assms 1 Fun_comp [of f "pr1 (dom f) (dom g)"]
            by (metis (no_types, lifting))
          also have "... = (Fun f \<circ> Fun (pr1 (dom f) (dom g))) x"
          proof -
            have "x \<in> Dom (pr1 (dom f) (dom g))"
              using assms 1 2 4
              by (metis (no_types, lifting) dom_comp)
            thus ?thesis by simp
          qed
          also have "... = Fun f (Fun (pr1 (dom f) (dom g)) x)"
            by simp
          also have "... = Fun f (arr_of (hfst (elem_of x)))"
            using assms 1 Fun_pr1 [of "dom f" "dom g"] ide_dom by simp
          finally show ?thesis by blast
        qed
        moreover
        have "Fun (comp g (pr0 (dom f) (dom g))) x = Fun g (arr_of (hsnd (elem_of x)))"
        proof -
          have 4: "seq g (pr0 (dom f) (dom g))"
            using assms 1 by blast
          have "Fun (comp g (pr0 (dom f) (dom g))) x =
                restrict (Fun g \<circ> Fun (pr0 (dom f) (dom g))) (Dom (pr0 (dom f) (dom g))) x"
            using assms 1 Fun_comp [of g "pr0 (dom f) (dom g)"]
            by (metis (no_types, lifting))
          also have "... = (Fun g \<circ> Fun (pr0 (dom f) (dom g))) x"
          proof -
            have "x \<in> Dom (pr0 (dom f) (dom g))"
              using assms 1 2 4
              by (metis (no_types, lifting) dom_comp)
            thus ?thesis by simp
          qed
          also have "... = Fun g (Fun (pr0 (dom f) (dom g)) x)"
            by simp
          also have "... = Fun g (arr_of (hsnd (elem_of x)))"
            using assms 1 Fun_pr0 [of "dom f" "dom g"] ide_dom by simp
          finally show ?thesis by blast
        qed
        ultimately show ?thesis by simp
      qed
      finally show ?thesis by simp
    qed

    lemma prod_in_terms_of_tuple:
    assumes "arr f" and "arr g"
    shows "HF'.prod f g =
           tuple (comp f (pr1 (dom f) (dom g))) (comp g (pr0 (dom f) (dom g)))"
      using assms HF'.prod_def tuple_span_eq
      by (metis (no_types, lifting) HF'.prod_simps(1) HF'.tuple_ext not_arr_null)

    lemma eval_prod_lam:
    assumes "ide a" and "ide b" and "ide c"
    and "in_hom g (prod a b) c"
    shows "comp (eval b c) (HF'.prod (\<Lambda> a b c g) b) = g"
    proof -
      have ide_dom_lam: "ide (dom (\<Lambda> a b c g))"
        using assms lam_in_hom [of a b c g] ide_dom by blast
      have ide_dom_b: "ide (dom b)"
        using assms ide_dom ideD(1) by blast
      define \<Lambda>_pr1 where "\<Lambda>_pr1 = comp (\<Lambda> a b c g) (pr1 (dom (\<Lambda> a b c g)) (dom b))"
      define b_pr0 where "b_pr0 = comp b (pr0 (dom (\<Lambda> a b c g)) (dom b))"
      have lam_pr1: "in_hom \<Lambda>_pr1 (prod a b) (exp b c)"
      proof (unfold \<Lambda>_pr1_def, intro comp_in_homI)
        show "in_hom (pr1 (dom (\<Lambda> a b c g)) (dom b)) (prod a b) a"
          using assms ide_dom_lam ide_dom_b ideD(2) lam_simps(2) pr1_in_hom by auto
        show "in_hom (\<Lambda> a b c g) a (exp b c)"
          using assms lam_in_hom by simp
      qed
      have b_pr0: "in_hom b_pr0 (prod a b) b"
        using assms b_pr0_def
        by (metis (no_types, lifting) comp_in_homI hfsetcat.lam_simps(2) ideD(2)
            ide_in_hom pr0_in_hom)
      have 1: "span \<Lambda>_pr1 b_pr0"
        using lam_pr1 b_pr0
        by (metis (no_types, lifting) in_homE)
      have tuple: "in_hom (tuple \<Lambda>_pr1 b_pr0) (prod a b) (prod (exp b c) b)"
        using 1 lam_pr1 b_pr0 tuple_in_hom [of \<Lambda>_pr1 b_pr0]
        by (metis (mono_tags, lifting) in_homE)
      define \<Lambda>_pr1' where "\<Lambda>_pr1' = comp (\<Lambda> a b c g) (pr1 a b)"
      define b_pr0' where "b_pr0' = pr0 a b"
      have lam_pr1_eq: "\<Lambda>_pr1 = \<Lambda>_pr1'"
        using assms \<Lambda>_pr1_def \<Lambda>_pr1'_def ideD(2) lam_simps(2) by auto
      have b_pr0_eq: "b_pr0 = b_pr0'"
        using assms b_pr0_def b_pr0'_def b_pr0 comp_ide_arr
        by (metis (no_types, lifting) ideD(2) in_homE lam_simps(2))
      have Fun_pr0: "Fun (pr0 a b) = restrict (\<lambda>x. arr_of (hsnd (elem_of x))) (set (prod a b))"
        using assms Fun_pr0 by simp
      have Fun_lam_pr1: "Fun \<Lambda>_pr1 =
                         restrict (Fun (\<Lambda> a b c g) o
                                   restrict (\<lambda>x. arr_of (hfst (elem_of x))) (set (prod a b)))
                                  (set (prod a b))"
        using assms 1 Fun_comp Fun_pr1 lam_pr1_eq \<Lambda>_pr1'_def
        by (metis (no_types, lifting) pr1_simps(2))
      have "comp (eval b c) (HF'.prod (\<Lambda> a b c g) b) = comp (eval b c) (tuple \<Lambda>_pr1 b_pr0)"
        using assms \<Lambda>_pr1_def b_pr0_def 1 prod_in_terms_of_tuple ideD(1) lam_simps(1)
        by presburger
      also have 5: "... = comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')"
        using lam_pr1_eq b_pr0_eq by simp
      also have "... = g"
      proof (intro arr_eqI\<^sub>S\<^sub>C)
        have 2: "arr (comp (eval b c) (tuple \<Lambda>_pr1 b_pr0))"
          using assms tuple arr_char
          by (metis (no_types, lifting) in_homE seqI eval_simps(1-2) ide_exp prod_ide_eq)
        have 3: "arr g"
          using assms by blast
        have tuple': "in_hom (tuple \<Lambda>_pr1' b_pr0') (prod a b) (prod (exp b c) b)"
          using tuple lam_pr1_eq b_pr0_eq by blast
        have 4: "Dom g = set (prod a b)"
          using assms
          by (metis (no_types, lifting) in_homE)
        show par: "par (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')) g"
          using assms tuple' 2 3 5
          by (metis (no_types, lifting) cod_comp dom_comp in_homE eval_simps(3))
        show "Fun (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')) = Fun g"
        proof
          fix x
          have "x \<notin> set (prod a b) \<Longrightarrow> Fun (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')) x = Fun g x"
          proof -
            have 5: "Fun g \<in> extensional (Dom g)"
              using assms 3 Fun_mapsto by simp
            moreover have "Fun (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')) \<in> extensional (Dom g)"
              using 5 par Fun_mapsto by (metis (no_types, lifting) Int_iff)
            ultimately show "x \<notin> set (prod a b) \<Longrightarrow>
                             Fun (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')) x = Fun g x"
              using 4 extensional_arb [of "Fun g" "Dom g" x]
                    extensional_arb [of "Fun (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0'))" "Dom g" x]
              by force
          qed
          moreover have "x \<in> set (prod a b) \<Longrightarrow>
                           Fun (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')) x = Fun g x"
          proof -
            assume x: "x \<in> set (prod a b)"
            have 6: "Dom (tuple \<Lambda>_pr1' b_pr0') = set (prod a b)"
              using assms 4 tuple' par
              by (metis (no_types, lifting) in_homE)
            have "Fun (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')) x =
                  Fun (eval b c) (Fun (tuple \<Lambda>_pr1' b_pr0') x)"
            proof -
              have "Fun (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')) x =
                    (Fun (eval b c) \<circ> Fun (tuple \<Lambda>_pr1' b_pr0')) x"
                using assms par x 6 Fun_comp [of "eval b c" "tuple \<Lambda>_pr1' b_pr0'"] by auto
              also have "... = Fun (eval b c) (Fun (tuple \<Lambda>_pr1' b_pr0') x)"
                by simp
              finally show ?thesis by blast
            qed
            also have "... = restrict (\<lambda>x. arr_of (happ (hfst (elem_of x)) (hsnd (elem_of x))))
                                      (set (HF'.prod (exp b c) b))
                                      (Fun (tuple \<Lambda>_pr1' b_pr0') x)"
              using assms Fun_eval by simp
            also have "... = (\<lambda>x. arr_of (happ (hfst (elem_of x)) (hsnd (elem_of x))))
                               (Fun (tuple \<Lambda>_pr1' b_pr0') x)"
            proof -
              have "Fun (tuple \<Lambda>_pr1' b_pr0') x \<in> set (HF'.prod (exp b c) b)"
              proof -
                have "x \<in> Dom (tuple \<Lambda>_pr1' b_pr0')"
                  using x 6 by blast
                moreover have "Cod (tuple \<Lambda>_pr1' b_pr0') = set (HF'.prod (exp b c) b)"
                  by (metis (no_types, lifting) in_homE assms(2-3) ide_exp
                      prod_ide_eq tuple')
                moreover have "arr (tuple \<Lambda>_pr1' b_pr0')"
                  using tuple' by blast
                ultimately show ?thesis
                  using tuple' Fun_mapsto [of "tuple \<Lambda>_pr1' b_pr0'"] by auto
              qed
              thus ?thesis
                using restrict_apply by simp
            qed
            also have "... = (\<lambda>x. arr_of (happ (hfst (elem_of x)) (hsnd (elem_of x))))
                               (arr_of \<langle>elem_of (Fun \<Lambda>_pr1' x), elem_of (Fun b_pr0' x)\<rangle>)"
            proof -
              have 7: "Dom \<Lambda>_pr1' = set (prod a b)"
                using assms
                by (metis (no_types, lifting) 1 comp_ide_arr ideD(2)
                    b_pr0_def lam_pr1_eq lam_simps(2) pr0_simps(2))
              moreover have "span \<Lambda>_pr1' b_pr0'"
                using assms 1 b_pr0_eq lam_pr1_eq by auto
              moreover have "x \<in> Dom \<Lambda>_pr1'"
                using x 7 by simp
              ultimately have "Fun (tuple \<Lambda>_pr1' b_pr0') x =
                               arr_of \<langle>elem_of (Fun \<Lambda>_pr1' x), elem_of (Fun b_pr0' x)\<rangle>"
                using assms x restrict_apply Fun_tuple by simp
              thus ?thesis by simp
            qed
            also have "... = arr_of (happ (elem_of (Fun \<Lambda>_pr1' x)) (elem_of (Fun b_pr0' x)))"
              using assms by simp
            also have "... = arr_of (happ (elem_of (arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b)
                                                            (ide_to_hf c) (arr_to_hfun g))
                                      (hfst (elem_of x)))))
                                      (elem_of (arr_of (hsnd (elem_of x)))))"
            proof -
              have "Fun b_pr0' x = arr_of (hsnd (elem_of x))"
                using assms x Fun_pr0 b_pr0'_def by simp
              moreover have "Fun \<Lambda>_pr1' x =
                             arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c)
                                            (arr_to_hfun g))
                                      (hfst (elem_of x)))"
              proof -
                have "Fun \<Lambda>_pr1' x =
                      restrict (Fun (\<Lambda> a b c g) o Fun (pr1 a b)) (Dom (pr1 a b)) x"
                  using assms x Fun_pr1 Fun_comp lam_pr1_eq Fun_lam_pr1 pr1_simps(1-2)
                  by presburger
                also have "... = Fun (\<Lambda> a b c g) (Fun (pr1 a b) x)"
                  using assms x restrict_apply Fun_lam_pr1 Fun_pr1 calculation lam_pr1_eq
                  by auto
                also have "... = restrict (\<lambda>x. arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b)
                                                              (ide_to_hf c) (arr_to_hfun g))
                                          (elem_of x)))
                                          (set a)
                                          (Fun (pr1 a b) x)"
                  using assms x Fun_lam by simp
                also have "... = arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c)
                                                (arr_to_hfun g))
                                          (elem_of (Fun (pr1 a b) x)))"
                proof -
                  have "Fun (pr1 a b) x \<in> set a"
                  proof -
                    have "x \<in> Dom (pr1 a b)"
                      using assms x pr1_simps(1-2) by auto
                    moreover have "Cod (pr1 a b) = set a"
                      using assms HF'.cod_pr1 pr1_simps(1) by auto
                    moreover have "arr (pr1 a b)"
                      using assms arr_char by blast
                    ultimately show ?thesis
                      using Fun_mapsto [of "pr1 a b"] by auto
                  qed
                  thus ?thesis
                    using restrict_apply by simp
                qed
                also have "... = arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c)
                                                (arr_to_hfun g))
                                          (hfst (elem_of x)))"
                  using assms x Fun_pr1 Fun_lam [of a b c g] by simp
                finally show ?thesis by simp
              qed
              ultimately show ?thesis by simp
            qed
            also have "... = arr_of (happ (happ (hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c)
                                                  (arr_to_hfun g))
                                            (hfst (elem_of x)))
                                      (hsnd (elem_of x)))"
              by simp
            also have "... = arr_of (happ (arr_to_hfun g) (elem_of x))"
              using assms x happ_hlam
              by (metis (no_types, lifting) prod_def elem_of_membI HCollect_iff ide_dom
                  in_homE UNIV_I arr_to_hfun_in_hexp hexp_def hfst_conv hsnd_conv
                  ide_to_hf_hf_to_ide timesE)
            also have "... = Fun g x"
              using assms x 3 4 Fun_char [of g] restrict_apply [of "Fun g" "Dom g" x]
              by simp
            finally show ?thesis by simp
          qed
          ultimately show "Fun (comp (eval b c) (tuple \<Lambda>_pr1' b_pr0')) x = Fun g x"
            by auto
        qed
      qed
      finally show ?thesis by simp
    qed

    lemma lam_eval_prod:
    assumes "ide a" and "ide b" and "ide c"
    and "in_hom h a (exp b c)"
    shows "\<Lambda> a b c (comp (eval b c) (HF'.prod h b)) = h"
    proof (intro arr_eqI\<^sub>S\<^sub>C)
      have 0: "in_hom (comp (eval b c) (HF'.prod h b)) (prod a b) c"
      proof
        show "in_hom (HF'.prod h b) (prod a b) (HF'.prod (exp b c) b)"
        proof
          show 1: "arr (HF'.prod h b)"
            using assms HF'.prod_in_hom'
            by (metis (no_types, lifting) ideD(1) in_homE)
          show "dom (HF'.prod h b) = prod a b"
            using assms 1
            by (metis (no_types, lifting) HF'.prod_simps(2) ideD(1-2) in_homE prod_ide_eq)
          show "cod (HF'.prod h b) = HF'.prod (exp b c) b"
            using assms 1
            by (metis (no_types, lifting) HF'.prod_simps(3) ideD(1,3) in_homE)
        qed
        show "in_hom (eval b c) (HF'.prod (exp b c) b) c"
          using assms by blast
      qed
      have 1: "in_hom (\<Lambda> a b c (comp (eval b c) (HF'.prod h b))) a (exp b c)"
        using assms 0 by blast
      have 2: "Fun (comp (eval b c) (HF'.prod h b)) =
               restrict (Fun (eval b c) \<circ> Fun (HF'.prod h b))
                        (set (HF'.prod a b))"
      proof -
        have "seq (eval b c) (HF'.prod h b)"
          using assms 1
          by (metis (no_types, lifting) 0 in_homE)
        moreover have "Dom (HF'.prod h b) = set (HF'.prod a b)"
          using assms
          by (metis (no_types, lifting) HF'.prod_simps(2) ideD(1-2) in_homE)
        ultimately show ?thesis
          using assms Fun_comp [of "eval b c" "HF'.prod h b"] by simp
      qed
      show par: "par (\<Lambda> a b c (comp (eval b c) (HF'.prod h b))) h"
        using assms 1
        by (metis (no_types, lifting) in_homE)
      show "Fun (\<Lambda> a b c (comp (eval b c) (HF'.prod h b))) = Fun h"
      proof
        fix x
        show "Fun (\<Lambda> a b c (comp (eval b c) (HF'.prod h b))) x = Fun h x"
        proof -
          have "x \<notin> set a \<Longrightarrow> ?thesis"
            using assms 1 Fun_mapsto
                  extensional_arb [of "Fun h" "set a" x]
                  extensional_arb [of "Fun (\<Lambda> a b c (comp (eval b c) (HF'.prod h b)))"
                                      "set a" x]
            by (metis (no_types, lifting) 0 Int_iff lam_simps(2) par)
          moreover have "x \<in> set a \<Longrightarrow> ?thesis"
          proof -
            assume x: "x \<in> set a"
            have 3: "dom (comp (eval b c) (HF'.prod h b)) = HF'.prod a b"
              using assms 0 in_homE prod_ide_eq by auto
            have 4: "cod (comp (eval b c) (HF'.prod h b)) = c"
              using assms 0 by blast
            have 5: "dom (comp (eval b c) (HF'.prod h b)) = HF'.prod a b"
              using assms 3
              by (metis (mono_tags, lifting))
            have 6: "cod (comp (eval b c) (HF'.prod h b)) = c"
              using assms 4 by (metis (no_types, lifting))
            have 7: "arr_to_hfun (comp (eval b c) (HF'.prod h b)) =
                     \<lbrace>xy \<^bold>\<in> ide_to_hf (HF'.prod a b) * ide_to_hf c.
                        hsnd xy = elem_of (Fun (comp (eval b c) (HF'.prod h b)) (arr_of (hfst xy)))\<rbrace>"
              unfolding arr_to_hfun_def
              using 2 5 6 by metis
            have "Fun (\<Lambda> a b c (comp (eval b c) (HF'.prod h b))) x =
                  arr_of (happ (hlam (ide_to_hf a) (ide_to_hf b) (ide_to_hf c)
                                 (arr_to_hfun (comp (eval b c) (HF'.prod h b))))
                           (elem_of x))"
              using assms 0 x Fun_lam by auto
            also have "... = arr_of \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c.
                                   \<langle>\<langle>elem_of x, hfst yz\<rangle>, hsnd yz\<rangle>
                                      \<^bold>\<in> arr_to_hfun (comp (eval b c) (HF'.prod h b))\<rbrace>"
            proof -
              have "seq (eval b c) (HF'.prod h b)"
                using assms 0 by blast
              moreover have "ide_to_hf (dom (comp (eval b c) (HF'.prod h b))) =
                             ide_to_hf a * ide_to_hf b"
                using assms 1 3
                by (metis (no_types, lifting) prod_def UNIV_I ide_to_hf_hf_to_ide prod_ide_eq)
              moreover have "ide_to_hf (cod (comp (eval b c) (HF'.prod h b))) = ide_to_hf c"
                using assms 2 4 by auto
              ultimately show ?thesis
                using assms 0 x happ_hlam(3) elem_of_membI
                      hfun_arr_to_hfun [of "comp (eval b c) (HF'.prod h b)"]
                by simp
            qed
            also have "... = arr_of \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c.
                                   hsnd yz = elem_of (Fun (comp (eval b c) (HF'.prod h b))
                                                       (arr_of \<langle>elem_of x, hfst yz\<rangle>))\<rbrace>"
            proof -
              have "\<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c.
                       \<langle>\<langle>elem_of x, hfst yz\<rangle>, hsnd yz\<rangle>
                          \<^bold>\<in> arr_to_hfun (comp (eval b c) (HF'.prod h b))\<rbrace> =
                    \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c.
                                   hsnd yz = elem_of (Fun (comp (eval b c) (HF'.prod h b))
                                                       (arr_of \<langle>elem_of x, hfst yz\<rangle>))\<rbrace>"
              proof
                fix yz
                show "yz \<^bold>\<in> \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c.
                                   \<langle>\<langle>elem_of x, hfst yz\<rangle>, hsnd yz\<rangle>
                                      \<^bold>\<in> arr_to_hfun (comp (eval b c) (HF'.prod h b))\<rbrace> \<longleftrightarrow>
                      yz \<^bold>\<in> \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c.
                                   hsnd yz = elem_of (Fun (comp (eval b c) (HF'.prod h b))
                                                     (arr_of \<langle>elem_of x, hfst yz\<rangle>))\<rbrace>"
                proof -
                  have "yz \<^bold>\<in> ide_to_hf b * ide_to_hf c \<Longrightarrow>
                        \<langle>\<langle>elem_of x, hfst yz\<rangle>, hsnd yz\<rangle> \<^bold>\<in> arr_to_hfun (comp (eval b c) (HF'.prod h b))
                          \<longleftrightarrow> hsnd yz = elem_of (Fun (comp (eval b c) (HF'.prod h b))
                                                     (arr_of \<langle>elem_of x, hfst yz\<rangle>))"
                  proof -
                    assume yz: "yz \<^bold>\<in> ide_to_hf b * ide_to_hf c"
                    have "\<langle>\<langle>elem_of x, hfst yz\<rangle>, hsnd yz\<rangle>
                             \<^bold>\<in> arr_to_hfun (comp (eval b c) (HF'.prod h b))
                            \<longleftrightarrow>
                          \<langle>\<langle>elem_of x, hfst yz\<rangle>, hsnd yz\<rangle> \<^bold>\<in> ide_to_hf (HF'.prod a b) * ide_to_hf c \<and>
                          hsnd yz = elem_of (Fun (comp (eval b c) (HF'.prod h b))
                                         (arr_of \<langle>elem_of x, hfst yz\<rangle>))"
                      using 7 by auto
                    moreover have "\<langle>\<langle>elem_of x, hfst yz\<rangle>, hsnd yz\<rangle>
                                      \<^bold>\<in> ide_to_hf (prod a b) * ide_to_hf c"
                    proof -
                      have "\<langle>elem_of x, hfst yz\<rangle> \<^bold>\<in> ide_to_hf (HF'.prod a b)"
                        using assms x yz
                        by (metis (no_types, lifting) prod_def elem_of_membI UNIV_I hfst_conv
                            ide_to_hf_hf_to_ide prod_ide_eq timesE times_iff)
                      thus ?thesis
                        using yz assms(1-2) prod_ide_eq by auto
                    qed
                    ultimately show ?thesis
                      using assms(1-2) prod_ide_eq by auto
                  qed
                  thus ?thesis by auto
                qed
              qed
              thus ?thesis by simp
            qed
            also have "... = arr_of \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c. yz \<^bold>\<in> elem_of (Fun h x)\<rbrace>"
            proof -
              have "\<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c.
                       hsnd yz = elem_of (Fun (comp (eval b c) (HF'.prod h b))
                                               (arr_of \<langle>elem_of x, hfst yz\<rangle>))\<rbrace> =
                    \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c. yz \<^bold>\<in> elem_of (Fun h x)\<rbrace>"
              proof -
                have "\<And>yz. yz \<^bold>\<in> ide_to_hf b * ide_to_hf c \<Longrightarrow>
                             hsnd yz = elem_of (Fun (comp (eval b c) (HF'.prod h b))
                                            (arr_of \<langle>elem_of x, hfst yz\<rangle>))
                               \<longleftrightarrow>
                             yz \<^bold>\<in> elem_of (Fun h x)"
                proof -
                  fix yz
                  assume yz: "yz \<^bold>\<in> ide_to_hf b * ide_to_hf c"
                  have 7: "arr_of \<langle>elem_of x, hfst yz\<rangle> \<in> set (HF'.prod a b)"
                    using assms x yz arr_of_membI
                    by (metis (no_types, lifting) prod_def elem_of_membI UNIV_I hfst_conv
                        ide_to_hf_hf_to_ide prod_ide_eq timesE times_iff)
                  have 8: "Fun h x \<in> set (exp b c)"
                  proof -
                    have "Fun h x \<in> Cod h"
                      using assms x Fun_mapsto by blast
                    moreover have "Cod h = set (exp b c)"
                      using assms 0 lam_simps(3) par by auto
                    ultimately show ?thesis by blast
                  qed
                  show "hsnd yz = elem_of (Fun (comp (eval b c) (HF'.prod h b))
                                            (arr_of \<langle>elem_of x, hfst yz\<rangle>))
                           \<longleftrightarrow>
                        yz \<^bold>\<in> elem_of (Fun h x)"
                  proof -
                    have "Fun (comp (eval b c) (HF'.prod h b)) (arr_of \<langle>elem_of x, hfst yz\<rangle>) =
                            arr_of (happ (elem_of (Fun h x)) (hfst yz))"
                    proof -
                      have "Fun (comp (eval b c) (HF'.prod h b)) (arr_of \<langle>elem_of x, hfst yz\<rangle>) =
                            restrict (Fun (eval b c) \<circ> Fun (HF'.prod h b))
                                     (set (HF'.prod a b))
                                     (arr_of \<langle>elem_of x, hfst yz\<rangle>)"
                        using assms x yz 2 by simp
                      also have "... = Fun (eval b c)
                                               (Fun (HF'.prod h b) (arr_of \<langle>elem_of x, hfst yz\<rangle>))"
                        using 7 by simp
                      also have "... = Fun (eval b c)
                                               (arr_of \<langle>elem_of (Fun h x),
                                                    elem_of (Fun b (arr_of (hfst yz)))\<rangle>)"
                      proof -
                        have "Fun (HF'.prod h b) (arr_of \<langle>elem_of x, hfst yz\<rangle>) =
                           arr_of \<langle>elem_of (Fun h x), elem_of (Fun b (arr_of (hfst yz)))\<rangle>"
                        proof -
                          have "Fun (HF'.prod h b) (arr_of \<langle>elem_of x, hfst yz\<rangle>) =
                                arr_of \<langle>elem_of (Fun h (arr_of (hfst (elem_of (arr_of \<langle>elem_of x, hfst yz\<rangle>))))),
                                    elem_of (Fun b (arr_of (hsnd (elem_of (arr_of \<langle>elem_of x, hfst yz\<rangle>)))))\<rangle>"
                          proof -
                            have "arr_of \<langle>elem_of x, hfst yz\<rangle> \<in> set (prod (dom h) (dom b))"
                              using assms x yz 7
                              by (metis (no_types, lifting) ideD(2) in_homE prod_ide_eq)
                            thus ?thesis
                              using assms x yz Fun_prod ideD(1) by blast
                          qed
                          also have "... = arr_of \<langle>elem_of (Fun h (arr_of (elem_of x))),
                                               elem_of (Fun b (arr_of (hfst yz)))\<rangle>"
                            using assms x yz by simp
                          also have "... = arr_of \<langle>elem_of (Fun h x), elem_of (Fun b (arr_of (hfst yz)))\<rangle>"
                            using assms(1) set_ideD(1) x by force
                          finally show ?thesis by simp
                        qed
                        thus ?thesis by simp
                      qed
                      also have "... = Fun (eval b c) (arr_of \<langle>elem_of (Fun h x), hfst yz\<rangle>)"
                        using assms x yz Fun_ide ide_char arr_of_membI by auto
                      also have "... = restrict (\<lambda>x. arr_of (happ (hfst (elem_of x)) (hsnd (elem_of x))))
                                                (set (HF'.prod (exp b c) b))
                                                (arr_of \<langle>elem_of (Fun h x), hfst yz\<rangle>)"
                        using assms Fun_eval [of b c] by simp
                      also have "... = (\<lambda>x. arr_of (happ (hfst (elem_of x)) (hsnd (elem_of x))))
                                         (arr_of \<langle>elem_of (Fun h x), hfst yz\<rangle>)"
                      proof -
                        have "arr_of \<langle>elem_of (Fun h x), hfst yz\<rangle>
                                 \<in> set (HF'.prod (exp b c) b)"
                        proof -
                          have 1: "ide_to_hf (HF'.prod (exp b c) b) =
                                   HF (elem_of ` set (HF'.prod (exp b c) b))"
                            unfolding ide_to_hf_def by blast
                          have "\<langle>elem_of (Fun h x), hfst yz\<rangle>
                                  \<^bold>\<in> HF (elem_of ` set (HF'.prod (exp b c) b))"
                            using assms x yz 1 8 Fun_mapsto [of h]
                            by (metis (no_types, lifting) prod_def elem_of_membI UNIV_I
                                hfst_conv ide_exp ide_to_hf_hf_to_ide prod_ide_eq timesE times_iff)
                          thus ?thesis
                            using assms x yz 1 arr_of_membI [of "\<langle>elem_of (Fun h x), hfst yz\<rangle>"]
                            by auto
                        qed
                        thus ?thesis by simp
                      qed
                      also have "... = arr_of (happ (elem_of (Fun h x)) (hfst yz))"
                        by simp
                      finally show ?thesis by simp
                    qed
                    hence 9: "elem_of (Fun (comp (eval b c) (HF'.prod h b))
                                        (arr_of \<langle>elem_of x, hfst yz\<rangle>)) =
                              happ (elem_of (Fun h x)) (hfst yz)"
                      by simp
                    show ?thesis
                    proof -
                      have "hsnd yz = happ (elem_of (Fun h x)) (hfst yz)
                              \<longleftrightarrow> yz \<^bold>\<in> elem_of (Fun h x)"
                      proof
                        have 10: "\<exists>!z. \<langle>hfst yz, z\<rangle> \<^bold>\<in> elem_of (Fun h x)"
                        proof -
                          have "hfun (ide_to_hf b) (ide_to_hf c) (elem_of (Fun h x))"
                            using assms x 8
                            by (metis (no_types, lifting) elem_of_membI HCollect_iff UNIV_I
                                exp_def hexp_def ide_exp ide_to_hf_hf_to_ide)
                          thus ?thesis
                            using assms yz
                                  hfunE [of "ide_to_hf b" "ide_to_hf c" "elem_of (Fun h x)"]
                            by (metis (no_types, lifting) hfst_conv timesE)
                        qed
                        show "yz \<^bold>\<in> elem_of (Fun h x)
                                \<Longrightarrow> hsnd yz = happ (elem_of (Fun h x)) (hfst yz)"
                        proof -
                          assume yz1: "yz \<^bold>\<in> elem_of (Fun h x)"
                          show "hsnd yz = happ (elem_of (Fun h x)) (hfst yz)"
                            unfolding app_def
                            using assms x yz yz1 10 hfun_arr_to_hfun arr_to_hfun_def
                                  the1_equality
                                    [of "\<lambda>y. \<langle>hfst yz, y\<rangle> \<^bold>\<in> elem_of (Fun h x)" "hsnd yz"]
                            by (metis (no_types, lifting) hfst_conv hsnd_conv timesE)
                        qed
                        show "hsnd yz = happ (elem_of (Fun h x)) (hfst yz)
                                \<Longrightarrow> yz \<^bold>\<in> elem_of (Fun h x)"
                          unfolding app_def
                          using assms x yz 10
                                theI' [of "\<lambda>y. \<langle>hfst yz, y\<rangle> \<^bold>\<in> elem_of (Fun h x)"]
                          by (metis (no_types, lifting) hfst_conv hsnd_conv timesE)
                      qed
                      thus ?thesis
                        using 9 by simp
                    qed
                  qed
                qed
                thus ?thesis by blast
              qed
              thus ?thesis by simp
            qed
            also have "... = Fun h x"
            proof -
              have H: "Fun h x = restrict (\<lambda>x. arr_of (happ (arr_to_hfun h) (elem_of x))) (Dom h) x"
              proof -
                have "arr h"
                  using assms by blast
                thus ?thesis
                  using assms x Fun_char by simp
              qed
              also have "... = arr_of (happ (arr_to_hfun h) (elem_of x))"
                using assms x par
                by (metis (no_types, lifting) 0 lam_simps(2) restrict_apply)
              also have "... = arr_of (THE g. \<langle>elem_of x, g\<rangle> \<^bold>\<in> arr_to_hfun h)"
                using app_def by simp
              also have "... = arr_of \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c. yz \<^bold>\<in> elem_of (Fun h x)\<rbrace>"
              proof -
                have ex_un_g: "\<exists>!g. \<langle>elem_of x, g\<rangle> \<^bold>\<in> arr_to_hfun h"
                  using assms x arr_to_hfun_def hfun_arr_to_hfun
                        hfunE [of "ide_to_hf a" "ide_to_hf (exp b c)" "arr_to_hfun h"]
                  by (metis (no_types, lifting) elem_of_membI in_homE)
                moreover have
                   "\<langle>elem_of x, \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c. yz \<^bold>\<in> elem_of (Fun h x)\<rbrace>\<rangle>
                       \<^bold>\<in> arr_to_hfun h"
                proof -
                  have "elem_of (Fun h x) =
                        \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c. yz \<^bold>\<in> elem_of (Fun h x)\<rbrace>"
                  proof
                    fix yz
                    show "yz \<^bold>\<in> elem_of (Fun h x) \<longleftrightarrow>
                          yz \<^bold>\<in> \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c. yz \<^bold>\<in> elem_of (Fun h x)\<rbrace>"
                    proof
                      show "yz \<^bold>\<in> elem_of (Fun h x)
                              \<Longrightarrow> yz \<^bold>\<in> \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c. yz \<^bold>\<in> elem_of (Fun h x)\<rbrace>"
                      proof -
                        assume yz: "yz \<^bold>\<in> elem_of (Fun h x)"
                        have "yz \<^bold>\<in> ide_to_hf b * ide_to_hf c"
                        proof -
                          have "elem_of (Fun h x) \<^bold>\<in> hexp (ide_to_hf b) (ide_to_hf c)"
                          proof -
                            have "ide (hf_to_ide (hexp (ide_to_hf b) (ide_to_hf c)))"
                              using assms exp_def ide_exp by auto
                            moreover have
                              "Fun h x \<in> set (hf_to_ide (hexp (ide_to_hf b) (ide_to_hf c)))"
                            proof -
                              have "Fun h x \<in> Cod h"
                                using assms x Fun_mapsto by blast
                              moreover have
                                "Cod h = set (hf_to_ide (hexp (ide_to_hf b) (ide_to_hf c)))"
                                using assms 0 exp_def lam_simps(3) par by auto
                              ultimately show ?thesis by blast
                            qed
                            ultimately show ?thesis
                              using elem_of_membI [of "hf_to_ide (hexp (ide_to_hf b) (ide_to_hf c))"
                                                   "Fun h x"]
                              by (simp add: ide_to_hf_hf_to_ide)
                          qed
                          thus ?thesis
                            using assms yz hexp_def by auto
                        qed
                        thus ?thesis
                          using assms x yz by blast
                      qed
                      show "yz \<^bold>\<in> \<lbrace>yz \<^bold>\<in> ide_to_hf b * ide_to_hf c. yz \<^bold>\<in> elem_of (Fun h x)\<rbrace>
                              \<Longrightarrow> yz \<^bold>\<in> elem_of (Fun h x)"
                        using assms by simp
                    qed
                  qed
                  moreover have "arr_of (elem_of x) = x"
                    using arr_of_elem_of assms(1) set_ideD(1) x by blast
                  ultimately show ?thesis
                    using assms x arr_to_hfun_def ex_un_g by auto
                qed
                ultimately show ?thesis
                  using assms x theI' [of "\<lambda>g. \<langle>elem_of x, g\<rangle> \<^bold>\<in> arr_to_hfun h"]
                  by fastforce
              qed
              finally show ?thesis
                using assms x by simp
            qed
            finally show ?thesis by simp
          qed
          ultimately show "Fun (\<Lambda> a b c (comp (eval b c) (HF'.prod h b))) x = Fun h x"
            by blast
        qed
      qed
    qed

    section "The Main Results"

    interpretation cartesian_closed_category comp
    proof -
      interpret elementary_category_with_terminal_object comp some_terminal some_terminator
        using extends_to_elementary_category_with_terminal_object by blast
      interpret elementary_cartesian_closed_category comp pr0 pr1
                       some_terminal some_terminator exp eval \<Lambda>
        using ide_exp eval_in_hom lam_in_hom prod_ide_eq eval_prod_lam lam_eval_prod
        by unfold_locales auto
      show "cartesian_closed_category comp"
        using is_cartesian_closed_category by simp
    qed

    theorem is_cartesian_closed_category:
    shows "cartesian_closed_category comp"
      ..

    theorem is_category_with_finite_limits:
    shows "category_with_finite_limits comp"
    proof
      fix J :: "'j comp"
      assume J: "category J"
      interpret J: category J
        using J by simp
      assume finite: "finite (Collect J.arr)"
      have "has_products (Collect J.ide)"
      proof -
        have "Collect J.ide \<noteq> UNIV"
          using J.not_arr_null by blast
        moreover have "finite (Collect J.ide)"
        proof -
          have "Collect J.ide \<subseteq> Collect J.arr"
            by auto
          thus ?thesis
            using finite J.ideD(1) finite_subset by blast
        qed
        ultimately show ?thesis
          using finite has_finite_products' by simp
      qed
      moreover have "has_products (Collect J.arr)"
      proof -
        have "Collect J.arr \<noteq> UNIV"
          using J.not_arr_null by blast
        thus ?thesis
          using finite has_finite_products' by simp
      qed
      ultimately show "has_limits_of_shape J"
        using J.category_axioms has_limits_if_has_products [of J] by simp
    qed

  end

end

