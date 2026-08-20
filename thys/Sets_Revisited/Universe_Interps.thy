(*  Title:       Universe_Interps
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2026
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Interpretations of \<open>universe\<close>"

theory Universe_Interps
imports Universe ZFC_in_HOL.ZFC_Cardinals
begin

  text\<open>
    In this section we give two interpretations of locales defined in
    theory \<open>Universe\<close>.  In one interpretation, ``finite'' is taken as
    the notion of smallness and the set of natural numbers is used to interpret the
    @{locale tupling} locale.
    In the second interpretation, the notion ``small'' is as defined in \<open>ZFC_in_HOL\<close>
    and the set of elements of the type \<open>V\<close> defined in that theory is used as the universe.
    This interpretation interprets the @{locale universe} locale, which augments
    @{locale universe} with the assumption @{locale small_nat} that the set of natural numbers
    is small.
    The purpose of constructing these interpretations is to show the consistency of the
    @{locale universe} locale assumptions (relative, of course to the consistency of
    HOL itself, and of HOL as extended in \<open>ZFC_in_HOL\<close>), as well as to provide a
    starting point for the construction of large categories, such as the category of small sets
    which is treated in this article.
  \<close>

  section "Interpretation using Natural Numbers"

  text\<open>
    We first give an interpretation for the @{locale tupling} locale, taking the set of natural
    numbers as the universe and taking ``finite'' as the meaning of ``small''.
  \<close>

  context
  begin

    text\<open>
      We first establish properties of \<open>finite :: nat set \<Rightarrow> bool\<close> as our notion of smallness.
    \<close>

    interpretation smallness \<open>finite :: nat set \<Rightarrow> bool\<close>
      by unfold_locales (meson finite_surj lepoll_iff)

    text\<open>
      The notion @{term small} defined by the @{locale smallness} locale agrees with the notion
      \<open>finite\<close> given as a locale parameter.
    \<close>

    lemma finset_small_iff_finite:
    shows "local.small X \<longleftrightarrow> finite X"
      by (metis eqpoll_finite_iff eqpoll_iff_finite_card local.small_def)

    interpretation small_finite \<open>finite :: nat set \<Rightarrow> bool\<close>
      by unfold_locales blast

    lemma small_finite_finset:
    shows "small_finite (finite :: nat set \<Rightarrow> bool)"
      ..

    interpretation small_product \<open>finite :: nat set \<Rightarrow> bool\<close>
      using eqpoll_iff_finite_card by unfold_locales auto

    lemma small_product_finset:
    shows "small_product (finite :: nat set \<Rightarrow> bool)"
      ..

    interpretation small_sum \<open>finite :: nat set \<Rightarrow> bool\<close>
      by unfold_locales (meson eqpoll_iff_finite_card finite_SigmaI finite_lessThan)

    lemma small_sum_finset:
    shows "small_sum (finite :: nat set \<Rightarrow> bool)"
      ..

    interpretation small_powerset \<open>finite :: nat set \<Rightarrow> bool\<close>
      using eqpoll_iff_finite_card by unfold_locales blast

    lemma small_powerset_finset:
    shows "small_powerset (finite :: nat set \<Rightarrow> bool)"
      ..

    interpretation small_funcset \<open>finite :: nat set \<Rightarrow> bool\<close> ..

    text\<open>
      As expected, the assumptions of locale @{locale small_nat} are inconsistent with
      the present context.
    \<close>

    lemma large_nat_finset:
    shows "\<not> local.small (UNIV :: nat set)"
      using finset_small_iff_finite large_UNIV by blast

    text\<open>
      Next, we develop embedding properties of \<open>UNIV :: nat set\<close>.
    \<close>

    interpretation embedding \<open>UNIV :: nat set\<close> .

    interpretation lifting \<open>UNIV :: nat set\<close>
      by unfold_locales blast

    lemma nat_admits_lifting:
    shows "lifting (UNIV :: nat set)"
      ..

    interpretation pairing \<open>UNIV :: nat set\<close>
      by unfold_locales blast

    lemma nat_admits_pairing:
    shows "pairing (UNIV :: nat set)"
      ..

    interpretation powering \<open>finite :: nat set \<Rightarrow> bool\<close> \<open>UNIV :: nat set\<close>
      using inj_on_set_encode small_iff_sml
      by unfold_locales auto

    lemma nat_admits_finite_powering:
    shows "powering (finite :: nat set \<Rightarrow> bool) (UNIV :: nat set)"
      ..

    interpretation tupling \<open>finite :: nat set \<Rightarrow> bool\<close> \<open>UNIV :: nat set\<close> ..

    lemma nat_admits_finite_tupling:
    shows "tupling (finite :: nat set \<Rightarrow> bool) (UNIV :: nat set)"
      ..

  end

  text\<open>
    Finally, we give the interpretation of the @{locale tupling} locale, stated in the top-level
    context in order to make it clear that it can be established directly in HOL, without
    depending somehow on any underlying locale assumptions.
  \<close>

  interpretation nat_tupling: tupling \<open>finite :: nat set \<Rightarrow> bool\<close> \<open>UNIV :: nat set\<close> undefined
    using nat_admits_finite_tupling by blast

  section "Interpretation using \<open>ZFC_in_HOL\<close>"

  text\<open>
    We now give an interpretation for the @{locale universe} locale, taking as the universe the
    set of elements of type \<open>V\<close> defined in \<open>ZFC_in_HOL\<close> as the universe and
    using the notion @{term ZFC_in_HOL.small} also defined in that theory.
  \<close>

  context
  begin

    text\<open>
      We first develop properties of @{term ZFC_in_HOL.small}, which we take
      as our notion of smallness.
    \<close>

    interpretation smallness \<open>ZFC_in_HOL.small :: V set \<Rightarrow> bool\<close>
      using lepoll_small by unfold_locales blast

    text\<open>
      The notion @{term local.small} defined by the @{locale smallness} locale agrees
      with the notion @{term ZFC_in_HOL.small} given as a locale parameter.
    \<close>

    lemma small_iff_ZFC_small:
    shows "local.small X \<longleftrightarrow> ZFC_in_HOL.small X"
      by (metis eqpoll_sym local.small_def small_eqpoll small_iff)

    interpretation small_finite \<open>ZFC_in_HOL.small :: V set \<Rightarrow> bool\<close>
      by unfold_locales
         (meson eqpoll_sym finite_atLeastAtMost finite_imp_small small_elts small_eqpoll)

    lemma small_finite_ZFC:
    shows "small_finite (ZFC_in_HOL.small :: V set \<Rightarrow> bool)"
      ..

    interpretation small_product \<open>ZFC_in_HOL.small :: V set \<Rightarrow> bool\<close>
      by unfold_locales (metis eqpoll_sym small_Times small_elts small_eqpoll)

    lemma small_product_ZFC:
    shows "small_product (ZFC_in_HOL.small :: V set \<Rightarrow> bool)"
      ..

    interpretation small_sum \<open>ZFC_in_HOL.small :: V set \<Rightarrow> bool\<close>
      by unfold_locales (meson eqpoll_sym small_Sigma small_elts small_eqpoll)

    lemma small_sum_ZFC:
    shows "small_sum (ZFC_in_HOL.small :: V set \<Rightarrow> bool)"
      ..

    text\<open>
      We need the following, which does not seem to be directly available in
      \<open>ZFC_in_HOL\<close>.
    \<close>

    lemma ZFC_small_implies_small_powerset:
    fixes X
    assumes "ZFC_in_HOL.small X"
    shows "ZFC_in_HOL.small (Pow X)"
    proof -
      obtain f v where f: "inj_on f X \<and> f ` X = elts v"
        using assms imageE ZFC_in_HOL.small_def by meson
      obtain f' where f': "inj_on f' (Pow X) \<and> f' ` (Pow X) = Pow (elts v)"
        using f image_Pow_surj inj_on_image_Pow by metis
      have "ZFC_in_HOL.small (f' ` (Pow X))"
        using assms f' ZFC_in_HOL.small_image_iff [of f' "Pow X"]
        by (metis Pow_iff down elts_VPow inj_onCI inj_on_image_eqpoll_self set_injective
            small_eqpoll)
      moreover have "eqpoll (f' ` (Pow X)) (Pow X)"
        using f' eqpoll_sym inj_on_image_eqpoll_self by meson
      ultimately show "ZFC_in_HOL.small (Pow X)"
        by (metis image_iff inj_on_image_eqpoll_1 ZFC_in_HOL.small_def small_eqpoll)
    qed

    interpretation small_powerset \<open>ZFC_in_HOL.small :: V set \<Rightarrow> bool\<close>
      by unfold_locales
         (meson eqpoll_sym gcard_eqpoll small_iff ZFC_small_implies_small_powerset)

    lemma small_powerset_ZFC:
    shows "small_powerset (ZFC_in_HOL.small :: V set \<Rightarrow> bool)"
      ..

    interpretation small_funcset \<open>ZFC_in_HOL.small :: V set \<Rightarrow> bool\<close> ..

    lemma small_funcset_ZFC:
    shows "small_funcset (ZFC_in_HOL.small :: V set \<Rightarrow> bool)"
      ..

    interpretation small_nat \<open>ZFC_in_HOL.small :: V set \<Rightarrow> bool\<close>
    proof -
      have "ZFC_in_HOL.small (UNIV :: nat set)"
        using small_image_nat by (metis surj_id)
      thus "small_nat (ZFC_in_HOL.small :: V set \<Rightarrow> bool)"
        using gcard_eqpoll by unfold_locales auto
    qed

    lemma small_nat_ZFC:
    shows "small_nat (ZFC_in_HOL.small :: V set \<Rightarrow> bool)"
      ..

    interpretation small_funcset_and_nat \<open>ZFC_in_HOL.small :: V set \<Rightarrow> bool\<close> ..

    lemma small_funcset_and_nat_ZFC:
    shows "small_funcset_and_nat (ZFC_in_HOL.small :: V set \<Rightarrow> bool)"
      ..

    text\<open>
      Next, we develop embedding properties of \<open>UNIV :: V set\<close>.
    \<close>

    interpretation embedding \<open>UNIV :: V set\<close> .

    interpretation lifting \<open>UNIV :: V set\<close>
    proof
      let ?\<iota> = "\<lambda> None \<Rightarrow> ZFC_in_HOL.set {}
                | Some x \<Rightarrow> ZFC_in_HOL.set {x}"
      have "is_embedding_of ?\<iota> ({None} \<union> Some ` UNIV)"
      proof
        show "?\<iota> ` ({None} \<union> Some ` UNIV) \<subseteq> UNIV" by blast
        show "inj_on ?\<iota> ({None} \<union> Some ` UNIV)"
        proof
          fix x y
          assume x: "x \<in> {None :: V option} \<union> Some ` UNIV"
          assume y: "y \<in> {None :: V option} \<union> Some ` UNIV"
          assume eq: "?\<iota> x = ?\<iota> y"
          show "x = y"
            by (metis (no_types, lifting) elts_of_set eq insert_not_empty option.case_eq_if
                option.collapse range_constant singleton_eq_iff small_image_nat)
        qed
      qed
      thus "\<exists>\<iota> :: V option \<Rightarrow> V. is_embedding_of \<iota> ({None} \<union> Some ` UNIV)"
        by blast
    qed

    lemma V_admits_lifting:
    shows "lifting (UNIV :: V set)"
      ..

    interpretation pairing \<open>UNIV :: V set\<close>
    proof
      show "\<exists>\<iota> :: V \<times> V \<Rightarrow> V. is_embedding_of \<iota> (UNIV \<times> UNIV)"
        using inj_on_vpair by blast
    qed

    lemma V_admits_pairing:
    shows "pairing (UNIV :: V set)"
      ..

    interpretation powering \<open>ZFC_in_HOL.small :: V set => bool\<close> \<open>UNIV :: V set\<close>
    proof
      show "\<exists>\<iota> :: V set \<Rightarrow> V. is_embedding_of \<iota> {X. X \<subseteq> UNIV \<and> local.small X}"
        using inj_on_set small_iff_sml by auto
    qed

    lemma V_admits_small_powering:
    shows "powering (ZFC_in_HOL.small :: V set => bool) (UNIV :: V set)"
      ..

    interpretation tupling \<open>ZFC_in_HOL.small :: V set => bool\<close> \<open>UNIV :: V set\<close> undefined ..

    lemma V_admits_small_tupling:
    shows "tupling (ZFC_in_HOL.small :: V set => bool) (UNIV :: V set)"
      ..

    interpretation universe \<open>ZFC_in_HOL.small :: V set => bool\<close> \<open>UNIV :: V set\<close> undefined ..

    theorem V_is_universe:
    shows "universe (ZFC_in_HOL.small :: V set => bool) (UNIV :: V set)"
      ..

  end

  text\<open>
    Finally, we give the interpretation of the @{locale universe} locale, stated in the top-level
    context.  Note however, that this is proved not in ``vanilla HOL'', but rather in HOL as
    extended by the axiomatization in \<open>ZFC_in_HOL\<close>.
  \<close>

  interpretation ZFC_universe: universe \<open>ZFC_in_HOL.small :: V set => bool\<close> \<open>UNIV :: V set\<close> undefined
    using V_is_universe by blast

end
