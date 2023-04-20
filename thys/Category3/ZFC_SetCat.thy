(*  Title:       ZFC_SetCat
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2022
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "ZFC SetCat"

text\<open>
  In the statement and proof of the Yoneda Lemma given in theory \<open>Yoneda\<close>,
  we sidestepped the issue, of not having a category of ``all'' sets, by axiomatizing
  the notion of a ``set category'', showing that for every category we could obtain
  a hom-functor into a set category at a higher type, and then proving the Yoneda
  lemma for that particular hom-functor.  This is perhaps the best we can do within HOL,
  because HOL does not provide any type that contains a universe of sets with the closure
  properties usually associated with a category \<open>Set\<close> of sets and functions between them.
  However, a significant aspect of category theory involves considering ``all''
  algebraic structures of a particular kind as the objects of a ``large'' category having
  nice closure or completeness properties.  Being able to consider a category of sets that
  is ``small-complete'', or a cartesian closed category of sets and functions that includes
  some infinite sets as objects, are basic examples of this kind of situation.

  The purpose of this section is to demonstrate that, although it cannot be done in
  pure HOL, if we are willing to accept the existence of a type \<open>V\<close> whose inhabitants
  correspond to sets satisfying the axioms of ZFC, then it is possible to construct,
  for example, the ``large'' category of sets and functions as it is usually understood
  in category theory.  Moreover, assuming the existence of such a type is essentially
  all we have to do; all the category theory we have developed so far still applies.
  Specifically, what we do in this section is to use theory \<open>ZFC_in_HOL\<close>, which provides
  an axiomatization of a set-theoretic universe \<open>V\<close>, to construct a ``set category''
  \<open>ZFC_SetCat\<close>, whose objects correspond to \<open>V\<close>-sets, whose arrows correspond to functions
  between \<open>V\<close>-sets, and which has the small-completeness property traditionally ascribed
  to the category of all small sets and functions between them.
\<close>

theory ZFC_SetCat
imports ZFC_in_HOL.ZFC_Cardinals Limit
begin

  text\<open>
    The following locale constructs the category of classes and functions between them
    and shows that it is small complete.  The category is obtained simply as the replete
    set category at type \<open>V\<close>.  This is not yet the category of sets we want, because it
    contains objects corresponding to ``large'' \<open>V\<close>-sets.
  \<close>

  locale ZFC_class_cat
  begin

    sublocale replete_setcat \<open>TYPE(V)\<close> .

    lemma admits_small_V_tupling:
    assumes "small (I :: V set)"
    shows "admits_tupling I"
    proof (unfold admits_tupling_def)
      let ?\<pi> = "\<lambda>f. UP (VLambda (ZFC_in_HOL.set I) (DN o f))"
      have "?\<pi> \<in> (I \<rightarrow> Univ) \<inter> extensional' I \<rightarrow> Univ"
        using UP_mapsto by force
      moreover have "inj_on ?\<pi> ((I \<rightarrow> Univ) \<inter> extensional' I)"
      proof
        fix f g
        assume f: "f \<in> (I \<rightarrow> Univ) \<inter> extensional' I"
        assume g: "g \<in> (I \<rightarrow> Univ) \<inter> extensional' I"
        assume eq: "UP (VLambda (ZFC_in_HOL.set I) (DN \<circ> f)) =
                    UP (VLambda (ZFC_in_HOL.set I) (DN \<circ> g))"
        have 1: "VLambda (ZFC_in_HOL.set I) (DN \<circ> f) = VLambda (ZFC_in_HOL.set I) (DN \<circ> g)"
          using f g eq
          by (meson injD inj_UP)
        show "f = g"
        proof
          fix x
          have "x \<notin> I \<Longrightarrow> f x = g x"
            using f g extensional'_def [of I] by auto
          moreover have "x \<in> I \<Longrightarrow> f x = g x"
          proof -
            assume x: "x \<in> I"
            hence "(DN o f) x = (DN o g) x"
              using assms 1 x elts_of_set VLambda_eq_D2 by fastforce
            thus "f x = g x"
              using f g x comp_apply UP_DN
              by (metis IntD1 PiE bij_arr_of bij_betw_imp_surj_on)
          qed
          ultimately show "f x = g x" by blast
        qed
      qed
      ultimately show "\<exists>\<pi>. \<pi> \<in> (I \<rightarrow> Univ) \<inter> extensional' I \<rightarrow> Univ \<and>
                           inj_on \<pi> ((I \<rightarrow> Univ) \<inter> extensional' I)"
        by blast
    qed

    corollary admits_small_tupling:
    assumes "small I"
    shows "admits_tupling I"
    proof -
      obtain \<phi> where \<phi>: "inj_on \<phi> I \<and> \<phi> ` I \<in> range elts"
        using assms small_def by metis
      have "admits_tupling (\<phi> ` I)"
        using \<phi> admits_small_V_tupling by fastforce
      moreover have inv: "bij_betw (inv_into I \<phi>) (\<phi> ` I) I"
        by (simp add: \<phi> bij_betw_inv_into inj_on_imp_bij_betw)
      ultimately show ?thesis
        using admits_tupling_respects_bij by blast
    qed

    lemma has_small_products:
    assumes "small (I :: 'i set)" and "I \<noteq> UNIV"
    shows "has_products I"
    proof -
      have 1: "\<And>I :: V set. small I \<Longrightarrow> has_products I"
        using big_UNIV
        by (metis admits_small_tupling has_products_iff_admits_tupling)
      obtain V_of where V_of: "inj_on V_of I \<and> V_of ` I \<in> range elts"
        using assms small_def by metis
      have "bij_betw (inv_into I V_of) (V_of ` I) I"
        using V_of bij_betw_inv_into bij_betw_imageI by metis
      moreover have "small (V_of ` I)"
        using assms by auto
      ultimately show ?thesis
        using assms 1 has_products_preserved_by_bijection by blast
    qed

    theorem has_small_limits:
    assumes "small (UNIV :: 'i set)"
    shows "has_limits (undefined :: 'i)"
    proof -
      have "\<forall>I :: 'i set. I \<noteq> UNIV \<longrightarrow> admits_tupling I"
        using assms smaller_than_small subset_UNIV admits_small_tupling by auto
      thus ?thesis
        using assms has_limits_iff_admits_tupling by blast
    qed

  end

  text\<open>
    We now construct the desired category of small sets and functions between them,
    as a full subcategory of the category of classes and functions.  To show that this
    subcategory is small complete, we show that the inclusion creates small products;
    that is, a small product of objects corresponding to small sets itself corresponds
    to a small set.
  \<close>

  locale ZFC_set_cat
  begin

    interpretation Cls: ZFC_class_cat .

    definition setp
    where "setp A \<equiv> A \<subseteq> Cls.Univ \<and> small A"

    sublocale sub_set_category Cls.comp \<open>\<lambda>A. A \<subseteq> Cls.Univ\<close> setp
      using small_Un smaller_than_small setp_def
      apply unfold_locales
         apply simp_all
       apply force
      by auto

    lemma is_sub_set_category:
    shows "sub_set_category Cls.comp (\<lambda>A. A \<subseteq> Cls.Univ) setp"
      using sub_set_category_axioms by blast

    interpretation incl: full_inclusion_functor Cls.comp \<open>\<lambda>a. Cls.ide a \<and> setp (Cls.set a)\<close>
      ..

    text\<open>
      The following functions establish a bijection between the identities of the category
      and the elements of type \<open>V\<close>; which in turn are in bijective correspondence with
      small \<open>V\<close>-sets.
    \<close>

    definition V_of_ide :: "V setcat.arr \<Rightarrow> V"
    where "V_of_ide a \<equiv> ZFC_in_HOL.set (Cls.DN ` Cls.set a)"

    definition ide_of_V :: "V \<Rightarrow> V setcat.arr"
    where "ide_of_V A \<equiv> Cls.mkIde (Cls.UP ` elts A)"

    lemma bij_betw_ide_V:
    shows "V_of_ide \<in> Collect ide \<rightarrow> UNIV"
    and "ide_of_V \<in> UNIV \<rightarrow> Collect ide"
    and [simp]: "ide a \<Longrightarrow> ide_of_V (V_of_ide a) = a"
    and [simp]: "V_of_ide (ide_of_V A) = A"
    and "bij_betw V_of_ide (Collect ide) UNIV"
    and "bij_betw ide_of_V UNIV (Collect ide)"
    proof -
      have "Univ = Cls.Univ"
        using terminal_char by presburger
      show 1: "V_of_ide \<in> Collect ide \<rightarrow> UNIV"
        by blast
      show 2: "ide_of_V \<in> UNIV \<rightarrow> Collect ide"
      proof
        fix A :: V
        have "small (elts A)"
          by blast
        have "Cls.UP ` elts A \<subseteq> Univ \<and> small (Cls.UP ` elts A)"
          using Cls.UP_mapsto terminal_char by blast
        hence "ide (mkIde (Cls.UP ` elts A))"
          using ide_mkIde \<open>Univ = Cls.Univ\<close> setp_def by auto
        thus "ide_of_V A \<in> Collect ide"
          using ide_of_V_def ide_char\<^sub>S\<^sub>S\<^sub>C setp_def
          by (metis (no_types, lifting) Cls.ide_mkIde Cls.set_mkIde arr_mkIde ide_char'
              mem_Collect_eq)
      qed
      show 3: "\<And>a. ide a \<Longrightarrow> ide_of_V (V_of_ide a) = a"
      proof -
        fix a
        assume a: "ide a"
        have "ide_of_V (V_of_ide a) =
              Cls.mkIde (Cls.UP ` elts (ZFC_in_HOL.set (Cls.DN ` Cls.set a)))"
          unfolding ide_of_V_def V_of_ide_def by simp
        also have "... = Cls.mkIde (Cls.UP ` Cls.DN ` Cls.set a)"
          using setp_set_ide a ide_char\<^sub>S\<^sub>S\<^sub>C setp_def by force
        also have "... = Cls.mkIde (Cls.set a)"
        proof -
          have "Cls.set a \<subseteq> Cls.Univ"
            using a ide_char\<^sub>S\<^sub>S\<^sub>C setp_def by blast
          hence "Cls.UP ` Cls.DN ` Cls.set a = Cls.set a"
          proof -
            have "\<And>x. x \<in> Cls.set a \<Longrightarrow> x \<in> Cls.UP ` Cls.DN ` Cls.set a"
              using Cls.UP_DN \<open>Cls.set a \<subseteq> Cls.Univ\<close>
              by (metis Cls.bij_arr_of bij_betw_def image_inv_into_cancel)
            moreover have "\<And>x. x \<in> Cls.UP ` Cls.DN ` Cls.set a \<Longrightarrow> x \<in> Cls.set a"
              using \<open>Cls.set a \<subseteq> Cls.Univ\<close>
              by (metis Cls.bij_arr_of bij_betw_def image_inv_into_cancel)
            ultimately show ?thesis by blast
          qed
          thus ?thesis by argo
        qed
        also have "... = a"
          using a Cls.mkIde_set ide_char\<^sub>S\<^sub>b\<^sub>C by blast
        finally show "ide_of_V (V_of_ide a) = a" by simp
      qed
      show 4: "\<And>A. V_of_ide (ide_of_V A) = A"
      proof -
        fix A
        have "V_of_ide (ide_of_V A) =
              ZFC_in_HOL.set (Cls.DN ` Cls.set (Cls.mkIde (Cls.UP ` elts A)))"
          unfolding V_of_ide_def ide_of_V_def by simp
        also have "... = ZFC_in_HOL.set (Cls.DN ` Cls.UP ` elts A)"
          using Cls.set_mkIde [of "Cls.UP ` elts A"] Cls.UP_mapsto by fastforce
        also have "... = ZFC_in_HOL.set (elts A)"
          using Cls.DN_UP by force
        also have "... = A" by simp
        finally show "V_of_ide (ide_of_V A) = A" by blast
      qed
      show "bij_betw V_of_ide (Collect ide) UNIV"
        using 1 2 3 4
        by (intro bij_betwI) auto
      show "bij_betw ide_of_V UNIV (Collect ide)"
        using 1 2 3 4
        by (intro bij_betwI) blast+
    qed

    text\<open>
      Next, we establish bijections between the hom-sets of the category and certain
      subsets of \<open>V\<close> whose elements represent functions.
    \<close>

    definition V_of_arr :: "V setcat.arr \<Rightarrow> V"
    where "V_of_arr f \<equiv> VLambda (V_of_ide (dom f)) (Cls.DN o Cls.Fun f o Cls.UP)"

    definition arr_of_V :: "V setcat.arr \<Rightarrow> V setcat.arr \<Rightarrow> V \<Rightarrow> V setcat.arr"
    where "arr_of_V a b F \<equiv> Cls.mkArr (Cls.set a) (Cls.set b) (Cls.UP o app F o Cls.DN)"

    definition vfun
    where "vfun A B f \<equiv> f \<in> elts (VPow (vtimes A B)) \<and> elts A = Domain (pairs f) \<and>
                        single_valued (pairs f)"

    lemma small_Collect_vfun:
    shows "small (Collect (vfun A B))"
      unfolding vfun_def
      by (metis (full_types) small_Collect small_elts)

    lemma vfunI:
    assumes "f \<in> elts A \<rightarrow> elts B"
    shows "vfun A B (VLambda A f)"
    proof (unfold vfun_def, intro conjI)
      show "VLambda A f \<in> elts (VPow (vtimes A B))"
        using assms VLambda_def by auto
      show "elts A = Domain (pairs (VLambda A f))"
        using assms VLambda_def [of A f]
        by (metis Domain_fst fst_pairs_VLambda)
      show "single_valued (pairs (VLambda A f))"
        using assms VLambda_def single_valued_def pairs_iff_elts by fastforce
    qed

    lemma app_vfun_mapsto:
    assumes "vfun A B F"
    shows "app F \<in> elts A \<rightarrow> elts B"
    proof
      have "F \<in> elts (VPow (vtimes A B)) \<and> elts A = Domain (pairs F) \<and> single_valued (pairs F)"
        using assms vfun_def by simp
      hence 1: "F \<in> elts (VPi A (\<lambda>_. B)) \<and> elts A = Domain (pairs F) \<and> single_valued (pairs F)"
        unfolding VPi_def
        by (metis (no_types, lifting) down elts_of_set mem_Collect_eq subsetI)
      fix x
      assume x: "x \<in> elts A"
      have "x \<in> Domain (pairs F)"
        using assms x vfun_def by blast
      thus "app F x \<in> elts B"
        using x 1 VPi_D [of F A "\<lambda>_. B" x] by blast
    qed

    lemma bij_betw_hom_vfun:
    shows "V_of_arr \<in> hom a b \<rightarrow> Collect (vfun (V_of_ide a) (V_of_ide b))"
    and "\<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> arr_of_V a b \<in> Collect (vfun (V_of_ide a) (V_of_ide b)) \<rightarrow> hom a b"
    and "f \<in> hom a b \<Longrightarrow> arr_of_V a b (V_of_arr f) = f"
    and "\<lbrakk>ide a; ide b; F \<in> Collect (vfun (V_of_ide a) (V_of_ide b))\<rbrakk>
            \<Longrightarrow> V_of_arr (arr_of_V a b F) = F"
    and "\<lbrakk>ide a; ide b\<rbrakk>
            \<Longrightarrow> bij_betw V_of_arr (hom a b) (Collect (vfun (V_of_ide a) (V_of_ide b)))"
    and "\<lbrakk>ide a; ide b\<rbrakk>
            \<Longrightarrow> bij_betw (arr_of_V a b) (Collect (vfun (V_of_ide a) (V_of_ide b))) (hom a b)"
    proof -
      show 1: "\<And>a b. V_of_arr \<in> hom a b \<rightarrow> Collect (vfun (V_of_ide a) (V_of_ide b))"
      proof
        fix a b f
        assume f: "f \<in> hom a b"
        have "V_of_arr f = VLambda (V_of_ide (dom f)) (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP)"
          unfolding V_of_arr_def by simp
        moreover have "vfun (V_of_ide a) (V_of_ide b) ..."
        proof -
          have "Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP \<in> elts (V_of_ide a) \<rightarrow> elts (V_of_ide b)"
          proof
            fix x
            assume x: "x \<in> elts (V_of_ide a)"
            have "(Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) x = Cls.DN (Cls.Fun f (Cls.UP x))"
              by simp
            moreover have "... \<in> elts (V_of_ide b)"
            proof -
              have "Cls.UP x \<in> Cls.Dom f"
                by (metis (no_types, lifting) Cls.arr_dom_iff_arr Cls.arr_mkIde Cls.set_mkIde
                    bij_betw_ide_V(3) arr_char\<^sub>S\<^sub>b\<^sub>C dom_simp f ide_char\<^sub>S\<^sub>S\<^sub>C ide_of_V_def image_eqI
                    in_homE mem_Collect_eq x)
              hence "Cls.DN (Cls.Fun f (Cls.UP x)) \<in> Cls.DN ` Cls.Cod f"
                using f in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C arr_char\<^sub>S\<^sub>b\<^sub>C Cls.Fun_mapsto [of f] by blast
              thus "Cls.DN (Cls.Fun f (Cls.UP x)) \<in> elts (V_of_ide b)"
                by (metis (no_types, lifting) V_of_ide_def arrE cod_char\<^sub>S\<^sub>b\<^sub>C elts_of_set f
                    in_homE mem_Collect_eq replacement setp_def)
            qed
            ultimately show "(Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) x \<in> elts (V_of_ide b)" by argo
          qed
          thus ?thesis
            using f vfunI by blast
        qed
        ultimately show "V_of_arr f \<in> Collect (vfun (V_of_ide a) (V_of_ide b))" by simp
      qed
      show 2: "\<And>a b. \<lbrakk>ide a; ide b\<rbrakk>
                        \<Longrightarrow> arr_of_V a b \<in> Collect (vfun (V_of_ide a) (V_of_ide b)) \<rightarrow> hom a b"
      proof -
        fix a b
        assume a: "ide a" and b: "ide b"
        show "arr_of_V a b \<in> Collect (vfun (V_of_ide a) (V_of_ide b)) \<rightarrow> hom a b"
        proof
          fix F
          assume F: "F \<in> Collect (vfun (V_of_ide a) (V_of_ide b))"
          have 3: "app F \<in> elts (V_of_ide a) \<rightarrow> elts (V_of_ide b)"
            using F app_vfun_mapsto [of "V_of_ide a" "V_of_ide b" F] by blast
          have 4: "app F \<in> Cls.DN ` (Cls.set a) \<rightarrow> Cls.DN ` (Cls.set b)"
            using 3 V_of_ide_def a b ide_char\<^sub>S\<^sub>S\<^sub>C setp_def by auto
          have "arr_of_V a b F = Cls.mkArr (Cls.set a) (Cls.set b) (Cls.UP \<circ> app F \<circ> Cls.DN)"
            unfolding arr_of_V_def by simp
          moreover have "... \<in> hom a b"
          proof
            show "\<guillemotleft>Cls.mkArr (Cls.set a) (Cls.set b) (Cls.UP \<circ> app F \<circ> Cls.DN) : a \<rightarrow> b\<guillemotright>"
            proof
              have 4: "Cls.arr (Cls.mkArr (Cls.set a) (Cls.set b) (Cls.UP \<circ> app F \<circ> Cls.DN))"
              proof -
                have "Cls.set a \<subseteq> Cls.Univ \<and> Cls.set b \<subseteq> Cls.Univ"
                  using a b ide_char\<^sub>S\<^sub>S\<^sub>C setp_def by blast
                moreover have "Cls.UP \<circ> app F \<circ> Cls.DN \<in> Cls.set a \<rightarrow> Cls.set b"
                proof
                  fix x
                  assume x: "x \<in> Cls.set a"
                  have "(Cls.UP \<circ> app F \<circ> Cls.DN) x = Cls.UP (app F (Cls.DN x))"
                    by simp
                  moreover have "... \<in> Cls.set b"
                    by (metis (no_types, lifting) 4 Cls.arr_mkIde Cls.ide_char' Cls.set_mkIde
                        PiE V_of_ide_def bij_betw_ide_V(3) b elts_of_set ide_char\<^sub>S\<^sub>S\<^sub>C
                        ide_of_V_def replacement rev_image_eqI x setp_def)
                  ultimately show "(Cls.UP \<circ> app F \<circ> Cls.DN) x \<in> Cls.set b"
                    by auto
                qed
                ultimately show ?thesis by blast
              qed
              show 5: "arr (Cls.mkArr (Cls.set a) (Cls.set b) (Cls.UP \<circ> app F \<circ> Cls.DN))"
                using a b 4 arr_char\<^sub>S\<^sub>b\<^sub>C ide_char\<^sub>S\<^sub>b\<^sub>C by auto
              show "dom (Cls.mkArr (Cls.set a) (Cls.set b) (Cls.UP \<circ> app F \<circ> Cls.DN)) = a"
                using a 4 5 dom_char\<^sub>S\<^sub>b\<^sub>C ide_char\<^sub>S\<^sub>b\<^sub>C by auto
              show "cod (Cls.mkArr (Cls.set a) (Cls.set b) (Cls.UP \<circ> app F \<circ> Cls.DN)) = b"
                using b 4 5 cod_char\<^sub>S\<^sub>b\<^sub>C ide_char\<^sub>S\<^sub>b\<^sub>C by auto
            qed
          qed
          ultimately show "arr_of_V a b F \<in> hom a b" by auto
        qed
      qed
      show 3: "\<And>a b f. f \<in> hom a b \<Longrightarrow> arr_of_V a b (V_of_arr f) = f"
      proof -
        fix a b f
        assume f: "f \<in> hom a b"
        have 4: "\<And>x. x \<in> Cls.set a
                        \<Longrightarrow> (Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN) x = Cls.Fun f x"
        proof - 
          fix x
          assume x: "x \<in> Cls.set a"
          have "(Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN) x =
                Cls.UP (Cls.DN (Cls.Fun f (Cls.UP (Cls.DN x))))"
            by simp
          also have "... = Cls.UP (Cls.DN (Cls.Fun f x))"
            using x Cls.UP_DN
            by (metis (no_types, lifting) Cls.elem_set_implies_incl_in Cls.incl_in_def
                Cls.setp_set_ide bij_betw_def replete_setcat.bij_arr_of subset_eq)
          also have "... = Cls.Fun f x"
          proof -
            have "x \<in> Cls.Dom f"
              using x f dom_char\<^sub>S\<^sub>b\<^sub>C by fastforce
            hence "Cls.Fun f x \<in> Cls.Cod f"
              using x f Cls.Fun_mapsto in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C by blast
            hence "Cls.Fun f x \<in> Cls.Univ"
              using f cod_char\<^sub>S\<^sub>b\<^sub>C in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C
              by (metis (no_types, lifting) Cls.elem_set_implies_incl_in Cls.incl_in_def
                  Cls.setp_set_ide subsetD)
            thus ?thesis
              by (meson bij_betw_inv_into_right replete_setcat.bij_arr_of)
          qed
          finally show "(Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN) x = Cls.Fun f x"
            by blast
        qed
        have 5: "Cls.arr (Cls.mkArr (Cls.set a) (Cls.set b)
                                    (Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN))"
        proof -
          have "Cls.set a \<subseteq> Cls.Univ \<and> Cls.set b \<subseteq> Cls.Univ"
            using f ide_char\<^sub>S\<^sub>b\<^sub>C codomains_def domains_def in_hom_def by force
          moreover have "Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN
                           \<in> Cls.set a \<rightarrow> Cls.set b"
          proof
            fix x
            assume x: "x \<in> Cls.set a"
            hence 6: "x \<in> Cls.Dom f"
              using f by (metis (no_types, lifting) dom_char\<^sub>S\<^sub>b\<^sub>C in_homE mem_Collect_eq)
            have "(Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN) x = Cls.Fun f x"
              using 4 f x by blast
            moreover have "... \<in> Cls.Cod f"
              using 4 6 f Cls.Fun_mapsto
              by (metis (no_types, lifting) Cls.arr_dom_iff_arr Cls.elem_set_implies_incl_in
                  Cls.ideD(1) Cls.incl_in_def IntE PiE)
            moreover have "... = Cls.set b"
              using f by (metis (no_types, lifting) cod_char\<^sub>S\<^sub>b\<^sub>C in_homE mem_Collect_eq)
            ultimately show "(Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN) x \<in> Cls.set b"
              by auto
          qed
          ultimately show ?thesis by blast
        qed
        have "arr_of_V a b (V_of_arr f) =
              Cls.mkArr (Cls.set a) (Cls.set b)
                        (Cls.UP \<circ> app (VLambda (V_of_ide (dom f)) (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP))
                                \<circ> Cls.DN)"
          unfolding arr_of_V_def V_of_arr_def by simp
        also have "... = Cls.mkArr (Cls.set a) (Cls.set b)
                                   (Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN)"
        proof (intro Cls.mkArr_eqI')
          show 6: "\<And>x. x \<in> Cls.set a \<Longrightarrow>
                         (Cls.UP \<circ> app (VLambda (V_of_ide (dom f)) (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP))
                                 \<circ> Cls.DN) x =
                         (Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN) x"
          proof -
            fix x
            assume x: "x \<in> Cls.set a"
            have "(Cls.UP \<circ> app (VLambda (V_of_ide (dom f)) (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP))
                          \<circ> Cls.DN) x =
                   Cls.UP (app (VLambda (V_of_ide (dom f)) (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP))
                               (Cls.DN x))"
              by simp
            also have "... = (Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN) x"
            proof -
              have "Cls.DN x \<in> elts (V_of_ide (dom f))"
                using f
                by (metis (no_types, lifting) V_of_ide_def elts_of_set ide_char\<^sub>S\<^sub>S\<^sub>C ide_dom image_eqI
                    in_homE mem_Collect_eq replacement x setp_def)
              thus ?thesis
                using beta by auto
            qed
            ultimately show "(Cls.UP \<circ> app (VLambda (V_of_ide (dom f))
                                                    (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP))
                                     \<circ> Cls.DN) x =
                             (Cls.UP \<circ> (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP) \<circ> Cls.DN) x"
              by argo
          qed
          show "Cls.arr (Cls.mkArr (Cls.set a) (Cls.set b)
                        (Cls.UP \<circ> app (VLambda (V_of_ide (local.dom f))
                                               (Cls.DN \<circ> Cls.Fun f \<circ> Cls.UP))
                                \<circ> Cls.DN))"
            using 5 6 Cls.mkArr_eqI by auto
        qed
        also have "... = Cls.mkArr (Cls.set a) (Cls.set b) (Cls.Fun f)"
          using 4 5 by force
        also have "... = f"
          using f Cls.mkArr_Fun
          by (metis (no_types, lifting) arr_char\<^sub>S\<^sub>b\<^sub>C cod_simp dom_char\<^sub>S\<^sub>b\<^sub>C in_homE mem_Collect_eq)
        finally show "arr_of_V a b (V_of_arr f) = f" by blast
      qed
      show 4: "\<And>a b F. \<lbrakk>ide a; ide b; F \<in> Collect (vfun (V_of_ide a) (V_of_ide b))\<rbrakk>
                          \<Longrightarrow> V_of_arr (arr_of_V a b F) = F"
      proof -
        fix a b F
        assume a: "ide a" and b: "ide b"
        assume F: "F \<in> Collect (vfun (V_of_ide a) (V_of_ide b))"
        have "F \<in> elts (VPow (vtimes (V_of_ide a) (V_of_ide b))) \<and>
              elts (V_of_ide a) = Domain (pairs F) \<and> single_valued (pairs F)"
          using F vfun_def by simp
        hence 5: "F \<in> elts (VPi (V_of_ide a) (\<lambda>_. V_of_ide b))"
          unfolding VPi_def
          by (metis (no_types, lifting) down elts_of_set mem_Collect_eq subsetI)
        let ?f = "Cls.mkArr (Cls.set a) (Cls.set b) (Cls.UP \<circ> app F \<circ> Cls.DN)"
        have 6: "Cls.arr ?f"
        proof -
          have "Cls.set a \<subseteq> Cls.Univ \<and> Cls.set b \<subseteq> Cls.Univ"
            using a b ide_char\<^sub>S\<^sub>S\<^sub>C setp_def by blast
          moreover have "Cls.UP \<circ> app F \<circ> Cls.DN \<in> Cls.set a \<rightarrow> Cls.set b"
          proof
            fix x
            assume x: "x \<in> Cls.set a"
            have "(Cls.UP \<circ> app F \<circ> Cls.DN) x = Cls.UP (app F (Cls.DN x))"
              by simp
            moreover have "... \<in> Cls.set b"
            proof -
              have "app F (Cls.DN x) \<in> Cls.DN ` Cls.set b"
                using a b ide_char\<^sub>S\<^sub>S\<^sub>C x F app_vfun_mapsto [of "V_of_ide a" "V_of_ide b" F]
                      V_of_ide_def setp_def
                by auto
              thus ?thesis
                using \<open>Cls.set a \<subseteq> Cls.Univ \<and> Cls.set b \<subseteq> Cls.Univ\<close>
                by (metis Cls.bij_arr_of bij_betw_def imageI image_inv_into_cancel)
            qed
            ultimately show "(Cls.UP \<circ> app F \<circ> Cls.DN) x \<in> Cls.set b" by auto
          qed
          ultimately show ?thesis by blast
        qed
        have "V_of_arr (arr_of_V a b F) = VLambda (V_of_ide (dom ?f)) (Cls.DN \<circ> Cls.Fun ?f \<circ> Cls.UP)"
          unfolding V_of_arr_def arr_of_V_def by simp
        also have "... = VLambda (V_of_ide a) (Cls.DN \<circ> Cls.Fun ?f \<circ> Cls.UP)"
          unfolding V_of_ide_def
          using a b 6 ide_char\<^sub>S\<^sub>S\<^sub>C V_of_ide_def dom_char\<^sub>S\<^sub>b\<^sub>C Cls.dom_mkArr arrI\<^sub>S\<^sub>b\<^sub>C by auto
        also have "... = VLambda (V_of_ide a)
                                 (Cls.DN \<circ>
                                    restrict (Cls.UP \<circ> app F \<circ> Cls.DN) (Cls.set a) \<circ> Cls.UP)"
          using 6 Cls.Fun_mkArr by simp
        also have "... = VLambda (V_of_ide a) (app F)"
        proof -
          have 7: "\<And>x. x \<in> elts (V_of_ide a) \<Longrightarrow>
                         (Cls.DN \<circ> restrict (Cls.UP \<circ> app F \<circ> Cls.DN) (Cls.set a) \<circ> Cls.UP) x =
                         app F x"
            unfolding V_of_ide_def
            using a
            apply simp
            by (metis (no_types, lifting) Cls.bij_arr_of a bij_betw_def empty_iff ide_char\<^sub>S\<^sub>S\<^sub>C
                image_eqI image_inv_into_cancel setp_def)
          have 8: "\<And>x. x \<in> elts (V_of_ide a) \<Longrightarrow>
                         (Cls.DN \<circ> restrict (Cls.UP \<circ> app F \<circ> Cls.DN) (Cls.set a) \<circ> Cls.UP) x
                            \<in> elts (V_of_ide b)"
            using 5 7 VPi_D by fastforce
          have "VLambda (V_of_ide a) (app F) \<in> elts (VPi (V_of_ide a) (\<lambda>_. V_of_ide b))"
            using 5 VPi_I VPi_D by auto
          moreover have "VLambda (V_of_ide a)
                                 (Cls.DN \<circ>
                                    restrict (Cls.UP \<circ> app F \<circ> Cls.DN) (Cls.set a) \<circ> Cls.UP)
                           \<in> elts (VPi (V_of_ide a) (\<lambda>_. V_of_ide b))"
            using 8 VPi_I by auto
          moreover have "\<And>x. x \<in> elts (V_of_ide a) \<Longrightarrow>
                               app (VLambda (V_of_ide a)
                                   (Cls.DN \<circ>
                                      restrict (Cls.UP \<circ> app F \<circ> Cls.DN) (Cls.set a) \<circ>
                                        Cls.UP)) x =
                               app F x"
            using 7 beta by auto
          ultimately show ?thesis
            using fun_ext by simp
        qed
        also have "... = F"
          using 5 eta [of F "V_of_ide a" "\<lambda>_. V_of_ide b"] by auto
        finally show "V_of_arr (arr_of_V a b F) = F" by blast
      qed
      show "\<lbrakk>ide a; ide b\<rbrakk>
               \<Longrightarrow> bij_betw V_of_arr (hom a b) (Collect (vfun (V_of_ide a) (V_of_ide b)))"
        using 1 2 3 4
        apply (intro bij_betwI)
           apply blast
          apply blast
        by auto
      show "\<lbrakk>ide a; ide b\<rbrakk>
               \<Longrightarrow> bij_betw (arr_of_V a b) (Collect (vfun (V_of_ide a) (V_of_ide b))) (hom a b)"
        using 1 2 3 4
        apply (intro bij_betwI)
           apply blast
          apply blast
        by auto
    qed

    lemma small_hom:
    shows "small (hom a b)"
    proof (cases "ide a \<and> ide b")
      assume 1: "\<not> (ide a \<and> ide b)"
      have "\<And>f. \<not> \<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
        using 1 in_hom_def ide_cod ide_dom by blast
      hence "hom a b = {}"
        by blast
      thus ?thesis by simp
      next
      assume 1: "ide a \<and> ide b"
      show ?thesis
        using 1 bij_betw_hom_vfun(5) small_Collect_vfun small_def
        by (metis (no_types, lifting) bij_betw_def small_iff_range)
    qed

    text\<open>
      We can now show that the inclusion of the subcategory into the ambient category \<open>Cls\<close>
      creates small products.  To do this, we consider a product in \<open>Cls\<close> of objects of the
      subcategory indexed by a small set \<open>I\<close>.  Since \<open>Cls\<close> is a replete set category,
      by a previous result we know that the elements of a product object \<open>p\<close> in \<open>Cls\<close>
      correspond to its points; that is, to the elements of \<open>hom unity p\<close>.
      The elements of \<open>hom unity p\<close> in turn correspond to \<open>I\<close>-tuples.  By carrying out
      the construction of the set of \<open>I\<close>-tuples in \<open>V\<close> and exploiting the bijections between
      homs of the subcatgory and \<open>V\<close>-sets, we can obtain an injection of \<open>hom unity p\<close>
      to the extension of a \<open>V\<close>-set, thus showing \<open>hom unity p\<close> is small.
      Since \<open>hom unity p\<close> is small, it determines an object of the subcategory,
      which must then be a product in the subcategory, in view of the fact that the
      subcategory is full.
    \<close>

    lemma has_small_V_products:
    assumes "small (I :: V set)"
    shows "has_products I"
    proof (unfold has_products_def, intro conjI impI allI)
      show "I \<noteq> UNIV"
        using assms big_UNIV by blast
      fix J D
      assume D: "discrete_diagram J comp D \<and> Collect (partial_composition.arr J) = I"
      interpret J: category J
        using D discrete_diagram_def by blast
      interpret D: discrete_diagram J comp D
        using D by blast
      interpret incloD: composite_functor J comp Cls.comp D map ..
      interpret incloD: discrete_diagram J Cls.comp incloD.map
        using D.is_discrete
        by unfold_locales auto
      interpret incloD: diagram_in_set_category J Cls.comp \<open>\<lambda>A. A \<subseteq> Cls.Univ\<close> incloD.map
        ..
      have 1: "small (Collect J.ide)"
        using assms D D.is_discrete by argo
      show "\<exists>a. has_as_product J D a"
      proof -
        have 2: "\<exists>a. Cls.has_as_product J incloD.map a"
        proof -
          have "Collect J.ide \<noteq> UNIV"
            using J.ide_def by blast
          thus ?thesis
            using 1 D.is_discrete Cls.has_small_products [of "Collect J.ide"]
                  Cls.has_products_def [of "Collect J.ide"] incloD.discrete_diagram_axioms
            by presburger
        qed
        obtain \<Pi>D where \<Pi>D: "Cls.has_as_product J incloD.map \<Pi>D"
          using 2 by blast
        interpret \<Pi>D: constant_functor J Cls.comp \<Pi>D
          using \<Pi>D Cls.product_is_ide
          by unfold_locales auto
        obtain \<pi> where \<pi>: "product_cone J Cls.comp incloD.map \<Pi>D \<pi>"
          using \<Pi>D Cls.has_as_product_def by blast
        interpret \<pi>: product_cone J Cls.comp incloD.map \<Pi>D \<pi>
          using \<pi> by blast
        have "small (Cls.hom Cls.unity \<Pi>D)"
        proof -
          obtain \<phi> where \<phi>: "bij_betw \<phi> (Cls.hom Cls.unity \<Pi>D) (incloD.cones Cls.unity)"
            using incloD.limits_are_sets_of_cones \<pi>.limit_cone_axioms by blast
          let ?J = "ZFC_in_HOL.set (Collect J.arr)"
          let ?V_of_point = "\<lambda>x. VLambda ?J (\<lambda>j. V_of_arr (\<phi> x j))"
          let ?Tuples = "VPi ?J (\<lambda>j. ZFC_in_HOL.set (V_of_arr ` hom Cls.unity (D j)))"
          have V_of_point: "?V_of_point \<in> Cls.hom Cls.unity \<Pi>D \<rightarrow> elts ?Tuples"
          proof
            fix x
            assume x: "x \<in> Cls.hom Cls.unity \<Pi>D"
            have \<phi>x: "\<phi> x \<in> incloD.cones Cls.unity"
              using \<phi> x
              unfolding bij_betw_def by blast
            interpret \<phi>x: cone J Cls.comp incloD.map Cls.unity \<open>\<phi> x\<close>
              using \<phi>x by blast
            have "\<And>j. J.arr j \<Longrightarrow> V_of_arr (\<phi> x j)
                                    \<in> elts (ZFC_in_HOL.set (V_of_arr ` hom Cls.unity (D j)))"
            proof -
              fix j
              assume j: "J.arr j"
              have "\<phi> x j \<in> hom Cls.unity (D j)"
                by (metis (mono_tags, lifting) D.preserves_ide \<phi>x.component_in_hom cod_simp
                    ideD(1,3) in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C incloD.is_discrete incloD.preserves_cod j map_simp
                    mem_Collect_eq o_apply terminal_char2 terminal_unity\<^sub>S\<^sub>S\<^sub>C)
              moreover have "V_of_arr ` hom Cls.unity (D j) =
                             elts (ZFC_in_HOL.set (V_of_arr ` hom Cls.unity (D j)))"
                using small_hom replacement by simp
              ultimately show "V_of_arr (\<phi> x j)
                                 \<in> elts (ZFC_in_HOL.set (V_of_arr ` hom Cls.unity (D j)))"
                using j \<phi>x bij_betw_hom_vfun(1) by blast
            qed
            thus "?V_of_point x \<in> elts ?Tuples"
              using VPi_I by fastforce
          qed
          have "?V_of_point ` Cls.hom Cls.unity \<Pi>D \<in> range elts"
          proof -
            have "?V_of_point ` Cls.hom Cls.unity \<Pi>D \<subseteq> elts ?Tuples"
              using V_of_point by blast
            thus ?thesis
              using smaller_than_small down_raw by auto
          qed
          moreover have "inj_on ?V_of_point (Cls.hom Cls.unity \<Pi>D)"
          proof
            fix x y
            assume x: "x \<in> Cls.hom Cls.unity \<Pi>D" and y: "y \<in> Cls.hom Cls.unity \<Pi>D"
            and eq: "?V_of_point x = ?V_of_point y"
            have \<phi>x: "\<phi> x \<in> incloD.cones Cls.unity"
              using \<phi> x
              unfolding bij_betw_def by blast
            have \<phi>y: "\<phi> y \<in> incloD.cones Cls.unity"
              using \<phi> y
              unfolding bij_betw_def by blast
            interpret \<phi>x: cone J Cls.comp incloD.map Cls.unity \<open>\<phi> x\<close>
              using \<phi>x by blast
            interpret \<phi>y: cone J Cls.comp incloD.map Cls.unity \<open>\<phi> y\<close>
              using \<phi>y by blast
            have "\<phi> x = \<phi> y"
            proof -
              have "\<And>j. j \<in> elts ?J \<Longrightarrow> \<phi> x j = \<phi> y j"
              proof -
                fix j
                assume j: "j \<in> elts ?J"
                hence 3: "J.arr j"
                  by (simp add: 1 incloD.is_discrete)
                have 4: "ide (D j)"
                  using 3 incloD.is_discrete D.preserves_ide by force
                have 5:"ide Cls.unity"
                  using Cls.terminal_unity\<^sub>S\<^sub>C terminal_char terminal_def by auto
                have \<phi>xj: "\<phi> x j \<in> hom Cls.unity (D j)"
                  using 3 4 5 incloD.is_discrete \<phi>x.preserves_hom \<phi>x.A.map_simp in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C
                  by (metis (no_types, lifting) J.ide_char \<phi>x.component_in_hom ideD(1) map_simp
                      mem_Collect_eq o_apply)
                have \<phi>yj: "\<phi> y j \<in> hom Cls.unity (D j)"
                  using 3 4 5 incloD.is_discrete \<phi>y.preserves_hom \<phi>x.A.map_simp in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C
                  by (metis (no_types, lifting) J.ide_char \<phi>y.component_in_hom ideD(1) map_simp
                      mem_Collect_eq o_apply)
                show "\<phi> x j = \<phi> y j"
                proof -
                  have "\<And>j. j \<in> elts ?J \<Longrightarrow> V_of_arr (\<phi> x j) = V_of_arr (\<phi> y j)"
                    using x eq VLambda_eq_D2 by blast
                  thus ?thesis
                    using V_of_arr_def
                    by (metis (mono_tags, lifting) j \<phi>xj \<phi>yj bij_betw_hom_vfun(3) mem_Collect_eq)
                qed
              qed
              moreover have "elts ?J = Collect J.arr"
                by (simp add: 1 incloD.is_discrete)
              ultimately show ?thesis
                using \<phi>x.is_extensional \<phi>y.is_extensional
                by (metis HOL.ext mem_Collect_eq)
            qed
            thus "x = y"
              using x y \<phi> bij_betw_imp_inj_on inj_on_def
              by (metis (no_types, lifting))
          qed
          ultimately show "small (Cls.hom Cls.unity \<Pi>D)"
            using small_def by blast
        qed
        hence "small (Cls.set \<Pi>D)"
          by (simp add: Cls.set_def)
        hence 2: "ide \<Pi>D"
          using ide_char\<^sub>S\<^sub>S\<^sub>C Cls.setp_set_ide Cls.product_is_ide \<Pi>D
          unfolding setp_def
          by blast
        interpret \<Pi>D': constant_functor J comp \<Pi>D
          using 2 by unfold_locales
        interpret \<pi>': cone J comp D \<Pi>D \<pi>
        proof -
          have "\<And>j. J.arr j \<Longrightarrow> \<guillemotleft>\<pi> j : \<Pi>D \<rightarrow> D j\<guillemotright>"
          proof
            fix j
            assume j: "J.arr j"
            show 3: "arr (\<pi> j)"
              by (metis (mono_tags, lifting) 2 D.as_nat_trans.preserves_cod D.is_discrete
                  D.preserves_ide \<pi>.component_in_hom ideD(1) ideD(3) in_homE in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C
                  j map_simp o_apply)
            show "dom (\<pi> j) = \<Pi>D"
              using 3 arr_char\<^sub>S\<^sub>b\<^sub>C dom_char\<^sub>S\<^sub>b\<^sub>C \<pi>.preserves_dom by auto
            show "cod (\<pi> j) = D j"
              using 3 arr_char\<^sub>S\<^sub>b\<^sub>C cod_char\<^sub>S\<^sub>b\<^sub>C \<pi>.preserves_cod
              by (metis (no_types, lifting) Cls.ideD(3) D.preserves_arr functor.preserves_ide
                  incloD.is_discrete incloD.is_functor incloD.preserves_cod j map_simp o_apply)
          qed
          moreover have "D.mkCone \<pi> = \<pi>"
            using \<pi>.is_extensional null_char by auto
          ultimately show "cone J comp D \<Pi>D \<pi>"
            using 2 D.cone_mkCone [of \<Pi>D \<pi>] by simp
        qed
        interpret \<pi>': product_cone J comp D \<Pi>D \<pi>
        proof
          fix a \<chi>'
          assume \<chi>': "D.cone a \<chi>'"
          interpret \<chi>': cone J comp D a \<chi>'
            using \<chi>' by blast
          have a: "Cls.ide a"
            using ide_char\<^sub>S\<^sub>b\<^sub>C \<chi>'.A.value_is_ide by blast
          moreover have "\<And>j. J.arr j \<Longrightarrow> Cls.in_hom (\<chi>' j) a (incloD.map j)"
          proof -
            fix j
            assume j: "J.arr j"
            have "\<guillemotleft>\<chi>' j : a \<rightarrow> D j\<guillemotright>"
              using j D.is_discrete \<chi>'.component_in_hom by force
            thus "Cls.in_hom (\<chi>' j) a (incloD.map j)"
              using a j D.is_discrete in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C map_simp by auto
          qed
          ultimately have 3: "incloD.cone a (incloD.mkCone \<chi>')"
            using incloD.cone_mkCone [of a \<chi>'] by blast
          interpret \<chi>: cone J Cls.comp incloD.map a \<open>incloD.mkCone \<chi>'\<close>
            using 3 by blast
          have univ: "\<exists>!f. Cls.in_hom f a \<Pi>D \<and> incloD.cones_map f \<pi> = incloD.mkCone \<chi>'"
            using \<chi>.cone_axioms \<pi>.is_universal [of a "incloD.mkCone \<chi>'"] by blast
          have 4: "incloD.mkCone \<chi>' = \<chi>'"
            using D.as_nat_trans.preserves_reflects_arr D.preserves_arr Limit.cone_def
                  \<chi>' \<chi>'.is_extensional identity_functor.intro identity_functor.map_def
                  incloD.as_nat_trans.is_extensional o_apply
            by fastforce
          have 5: "D.mkCone \<pi> = \<pi>"
            using \<pi>.is_extensional null_char by auto
          have 6: "\<And>f. Cls.in_hom f a \<Pi>D \<Longrightarrow> incloD.cones_map f \<pi> = D.cones_map f \<pi>"
          proof -
            fix f
            assume f: "Cls.in_hom f a \<Pi>D"
            have "incloD.cones_map f \<pi> = (\<lambda>j. if J.arr j then Cls.comp (\<pi> j) f else Cls.null)"
              using f \<pi>.cone_axioms by auto
            also have "... = (\<lambda>j. if J.arr j then comp (\<pi> j) f else null)"
            proof -
              have "\<And>j. J.arr j \<Longrightarrow> Cls.comp (\<pi> j) f = comp (\<pi> j) f"
                using f 2 comp_char in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C seq_char\<^sub>S\<^sub>b\<^sub>C
                by (metis (no_types, lifting) Cls.ext Cls.in_homE \<chi>'.ide_apex
                    \<pi>'.preserves_reflects_arr arr_char\<^sub>S\<^sub>b\<^sub>C ide_char\<^sub>S\<^sub>S\<^sub>C)
              thus ?thesis
                using null_char by auto
            qed
            also have "... = D.cones_map f \<pi>"
            proof -
              have "\<pi> \<in> D.cones (cod f)"
              proof -
                have "\<guillemotleft>f : a \<rightarrow> \<Pi>D\<guillemotright>"
                  using f 2 in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C \<chi>'.ide_apex ideD(1) by presburger
                thus ?thesis
                  using f \<pi>'.cone_axioms by blast
              qed
              thus ?thesis
                using \<open>\<pi> \<in> D.cones (cod f)\<close> by simp
            qed
            finally show "incloD.cones_map f \<pi> = D.cones_map f \<pi>" by blast
          qed
          moreover have "\<And>f. \<guillemotleft>f : a \<rightarrow> \<Pi>D\<guillemotright> \<Longrightarrow> Cls.in_hom f a \<Pi>D"
            using in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C by blast
          show "\<exists>!f. \<guillemotleft>f : a \<rightarrow> \<Pi>D\<guillemotright> \<and> D.cones_map f \<pi> = \<chi>'"
          proof -
            have "\<exists>f. \<guillemotleft>f : a \<rightarrow> \<Pi>D\<guillemotright> \<and> D.cones_map f \<pi> = \<chi>'"
              using 2 4 5 6 univ \<chi>'.ide_apex ideD(1) in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C
              by (metis (no_types, lifting))
            moreover have "\<And>f g. \<lbrakk>\<guillemotleft>f : a \<rightarrow> \<Pi>D\<guillemotright> \<and> D.cones_map f \<pi> = \<chi>';
                                   \<guillemotleft>g : a \<rightarrow> \<Pi>D\<guillemotright> \<and> D.cones_map g \<pi> = \<chi>'\<rbrakk>
                                     \<Longrightarrow> f = g"
              using 2 4 5 6 univ \<chi>'.ide_apex ideD(1) in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C by auto
            ultimately show ?thesis by blast
          qed
        qed
        show ?thesis
          using \<pi>'.product_cone_axioms has_as_product_def by blast
      qed
    qed

    corollary has_small_products:
    assumes "small I" and "I \<noteq> UNIV"
    shows "has_products I"
    proof -
      have 1: "\<And>I :: V set. small I \<Longrightarrow> has_products I"
        using has_small_V_products by blast
      obtain \<phi> where \<phi>: "inj_on \<phi> I \<and> \<phi> ` I \<in> range elts"
        using assms small_def by metis
      have "bij_betw (inv_into I \<phi>) (\<phi> ` I) I"
        using \<phi> bij_betw_inv_into bij_betw_imageI by metis
      moreover have "small (\<phi> ` I)"
        using assms by auto
      ultimately show ?thesis
        using assms 1 has_products_preserved_by_bijection by blast
    qed

    theorem has_small_limits:
    assumes "category (J :: 'j comp)" and "small (Collect (partial_composition.arr J))"
    shows "has_limits_of_shape J"
    proof -
      interpret J: category J
        using assms by blast
      have "small (Collect J.ide)"
        using assms smaller_than_small [of "Collect J.arr" "Collect J.ide"] by fastforce
      moreover have "Collect J.ide \<noteq> UNIV"
        using J.ide_def by blast
      moreover have "Collect J.arr \<noteq> UNIV"
        using J.not_arr_null by blast
      ultimately show "has_limits_of_shape J"
        using assms has_small_products has_limits_if_has_products [of J] by blast
    qed

    sublocale concrete_set_category comp setp UNIV Cls.UP
    proof
      show "Cls.UP \<in> UNIV \<rightarrow> Univ"
        using Cls.UP_mapsto terminal_char by presburger
      show "inj Cls.UP"
        using Cls.inj_UP by blast
    qed

    lemma is_concrete_set_category:
    shows "concrete_set_category comp setp UNIV Cls.UP"
      ..

  end

  text\<open>
    In pure HOL (without ZFC), we were able to show that every category \<open>C\<close> has a ``hom functor'',
    but there was necessarily a dependence of the target set category of the hom functor
    on the arrow type of \<open>C\<close>.  Using the construction of the present theory, we can now show
    that every ``locally small'' category \<open>C\<close> has a hom functor, whose target is the same set
    category for all such \<open>C\<close>.  To obtain such a hom functor requires a choice, for each hom-set
    \<open>hom a b\<close> of \<open>C\<close>, of an injection of \<open>hom a b\<close> to the extension of a \<open>V\<close>-set.
  \<close>

  locale locally_small_category =
    category +
    assumes locally_small: "\<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> small (hom b a)"
  begin

    interpretation Cop: dual_category C ..
    interpretation CopxC: product_category Cop.comp C ..
    interpretation S: ZFC_set_cat .

    definition Hom
    where "Hom \<equiv> \<lambda>(b, a). S.UP o (SOME \<phi>. \<phi> ` hom b a \<in> range elts \<and> inj_on \<phi> (hom b a))"

    interpretation Hom: hom_functor C S.comp S.setp Hom
    proof
      have 1: "\<And>a b. Hom (b, a) \<in> hom b a \<rightarrow> S.Univ \<and> inj_on (Hom (b, a)) (hom b a)"
      proof -
        fix a b
        show "Hom (b, a) \<in> hom b a \<rightarrow> S.Univ \<and> inj_on (Hom (b, a)) (hom b a)"
        proof (cases "ide a \<and> ide b")
          show "\<not> (ide a \<and> ide b) \<Longrightarrow> ?thesis"
            using inj_on_def by fastforce
          assume ab: "ide a \<and> ide b"
          show ?thesis
          proof
            have 1: "\<exists>\<phi>. \<phi> ` hom b a \<in> range elts \<and> inj_on \<phi> (hom b a)"
              using ab locally_small [of a b] small_def [of "hom b a"] by blast
            let ?\<phi> = "SOME \<phi>. \<phi> ` hom b a \<in> range elts \<and> inj_on \<phi> (hom b a)"
            have \<phi>: "?\<phi> ` hom b a \<in> range elts \<and> inj_on ?\<phi> (hom b a)"
              using 1 someI_ex [of "\<lambda>\<phi>. \<phi> ` hom b a \<in> range elts \<and> inj_on \<phi> (hom b a)"]
              by blast
            show "Hom (b, a) \<in> hom b a \<rightarrow> S.Univ"
              unfolding Hom_def
              using \<phi> S.UP_mapsto by auto
            show "inj_on (Hom (b, a)) (hom b a)"
              unfolding Hom_def
              apply simp
              using ab \<phi> S.inj_UP comp_inj_on injD inj_on_def
              by (metis (no_types, lifting))
          qed
        qed
      qed
      show "\<And>f. arr f \<Longrightarrow> Hom (dom f, cod f) f \<in> S.Univ"
        using 1 by blast
      show "\<And>b a. \<lbrakk>ide b; ide a\<rbrakk> \<Longrightarrow> inj_on (Hom (b, a)) (hom b a)"
        using 1 by blast
      show "\<And>b a. \<lbrakk>ide b; ide a\<rbrakk> \<Longrightarrow> S.setp (Hom (b, a) ` hom b a)"
        unfolding S.setp_def
        using 1 locally_small S.terminal_char by force
    qed

    lemma has_ZFC_hom_functor:
    shows "hom_functor C S.comp S.setp Hom"
      ..

    text\<open>
      Using this result, we can now state a more traditional version of the Yoneda Lemma
      in which the target category of the Yoneda functor is the same for all locally small
      categories.
    \<close>

    interpretation Y: yoneda_functor C S.comp S.setp Hom
      ..

    theorem ZFC_yoneda_lemma:
    assumes "ide a" and "functor Cop.comp S.comp F"
    shows "\<exists>\<phi>. bij_betw \<phi> (S.set (F a)) {\<tau>. natural_transformation Cop.comp S.comp (Y.Y a) F \<tau>}"
    proof -
      interpret F: "functor" Cop.comp S.comp F
        using assms(2) by blast
      interpret F: set_valued_functor Cop.comp S.comp S.setp F
        ..
      interpret Ya: yoneda_functor_fixed_object C S.comp S.setp Hom a
        using assms(1) by unfold_locales blast
      interpret Ya: yoneda_lemma C S.comp S.setp Hom F a
        ..
      show ?thesis
        using Ya.yoneda_lemma by blast
    qed

  end

end
