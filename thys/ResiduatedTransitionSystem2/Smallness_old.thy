(*  Title:       Smallness_old
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

theory Smallness_old
imports Main RTSConstructions RTSCategory ZFC_in_HOL.ZFC_Cardinals
begin

section "Smallness"

  text \<open>
    ({\em Note added in 2026}):
    This theory contains the original development of a notion of smallness that is used
    in the present article to construct a cartesian closed category of RTS's.
    This original development has been superseded by a more systematic one in a later
    (January 2026) AFP article, ``Sets Revisited''.  To avoid confusion, the original
    development has been extracted from the theory
    @{theory ResiduatedTransitionSystem2.RTSConstructions} where it originally appeared
    and placed here, so that future work can import that theory without also automatically
    importing an obsolete development of smallness and the associated dependence on
    @{theory ZFC_in_HOL.ZFC_Cardinals}.
  \<close>

subsection "Notation"

  text \<open>
    Some of the theories in the HOL library that we depend on define global notation involving
    generic symbols that we would like to use here.  It would be best if there were some way
    to import these theories without also having to import this notation, but for now the best
    we can do is to uninstall the notation involving the symbols at issue.
  \<close>

  (* I really don't like global notation -- it's rude. *)
  no_notation Equipollence.eqpoll (infixl \<open>\<approx>\<close> 50)
  no_notation Equipollence.lepoll (infixl \<open>\<lesssim>\<close> 50)
  no_notation Lattices.sup_class.sup (infixl \<open>\<squnion>\<close> 65)
  no_notation ZFC_Cardinals.cmult   (infixl \<open>\<otimes>\<close> 70)

  no_syntax "_Tuple"    :: "[V, Vs] \<Rightarrow> V"                 (\<open>\<langle>(_,/ _)\<rangle>\<close>)
  no_syntax "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   (\<open>\<langle>(_,/ _)\<rangle>\<close>)

subsection "Some Constraints on a Type"

subsubsection "Lifting"

  text \<open>
    A type \<open>'a\<close> ``admits lifting'' if there is an injection from the type \<open>'a option\<close> to \<open>'a\<close>.
  \<close>

  locale lifting =
  fixes type :: "'a itself"
  assumes admits_lifting: "\<exists>l :: 'a option \<Rightarrow> 'a. inj l"
  begin

    definition some_lift :: "'a option \<Rightarrow> 'a"
    where "some_lift \<equiv> SOME l :: 'a option \<Rightarrow> 'a. inj l"

    lemma inj_some_lift:
    shows "inj some_lift"
      using admits_lifting someI_ex [of "\<lambda>l. inj l"] some_lift_def by fastforce

    text \<open>
      A type that admits lifting is obviously nondegenerate.
    \<close>

    sublocale nondegenerate
    proof (unfold_locales, intro exI)
      show "some_lift None \<noteq> some_lift (Some (some_lift None))"
        using injD inj_some_lift by fastforce
    qed

  end

subsubsection "Pairing"

  text \<open>
    A type \<open>'a\<close> ``admits pairing'' if there exists an injective ``pairing function'' from
    \<open>'a * 'a\<close> to \<open>'a\<close>.  This allows us to encode pairs of elements of \<open>'a\<close> without
    having to pass to a higher type.
  \<close>

  locale pairing =
  fixes type :: "'a itself"
  assumes admits_pairing: "\<exists>p :: 'a * 'a \<Rightarrow> 'a. inj p"
  begin

    definition some_pair :: "'a * 'a \<Rightarrow> 'a"
    where "some_pair \<equiv> SOME p :: 'a * 'a \<Rightarrow> 'a. inj p"

    abbreviation is_pair
    where "is_pair x \<equiv> x \<in> range some_pair"

    definition first :: "'a \<Rightarrow> 'a"
    where "first x \<equiv> fst (inv some_pair x)"

    definition second :: "'a \<Rightarrow> 'a"
    where "second x = snd (inv some_pair x)"

    lemma inj_some_pair:
    shows "inj some_pair"
      using admits_pairing someI_ex [of "\<lambda>p. inj p"] some_pair_def by fastforce

    lemma first_conv:
    shows "first (some_pair (x, y)) = x"
      using first_def inj_some_pair by auto

    lemma second_conv:
    shows "second (some_pair (x, y)) = y"
      using second_def inj_some_pair by auto

    lemma pair_conv:
    assumes "is_pair x"
    shows "some_pair (first x, second x) = x"
      using assms first_def second_def inj_some_pair by force

  end

  text \<open>
    A type that is nondegenerate and admits pairing also admits lifting.
  \<close>

  locale nondegenerate_and_pairing =
    nondegenerate + pairing
  begin

    sublocale lifting type
    proof
      obtain c :: 'a where c: "\<forall>x. c \<noteq> some_pair (c, x)"
        using is_nondegenerate inj_some_pair
        by (metis (full_types) first_conv second_conv)
      let ?f = "\<lambda>None \<Rightarrow> c | Some x \<Rightarrow> some_pair (c, x)"
      have "inj ?f"
        unfolding inj_def
        by (metis (no_types, lifting) c option.case_eq_if option.collapse
            second_conv)
      thus "\<exists>l :: 'a option \<Rightarrow> 'a. inj l"
        by blast
    qed

  end

subsubsection "Exponentiation"

  text \<open>
    In order to define the exponential \<open>[A, B]\<close> of an RTS \<open>A\<close> and an RTS \<open>B\<close>
    at a type \<open>'a\<close> without having to pass to a higher type, we need the type \<open>'a\<close>
    to be large enough to embed the set of all extensional
    functions that have ``small'' sets as their domains.  Here we are using the
    notion of ``small'' provided by the @{session ZFC_in_HOL} extension to HOL.
    Now, the standard Isabelle/HOL definition of ``extensional'' uses the specific chosen
    value \<open>undefined\<close> as the default value for an extensional function outside of its domain,
    but here we need to apply this concept in cases where the value could be something else
    (the null value for an RTS, in particular).  So, we define a notion of a function
    that has at most one ``popular value'' in its range, where a popular value is one with a
    ``large'' preimage.  If such a function in addition has a small range, then it in some
    sense has a small encoding, which consists of its graph restricted to its domain
    (which must then necessarily be small), paired with the single default value that it
    takes outside its domain.
  \<close>

  abbreviation popular_value :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> bool"
  where "popular_value F y \<equiv> \<not> small {x. F x = y}"

  definition some_popular_value :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "some_popular_value F \<equiv> SOME y. popular_value F y"

  abbreviation at_most_one_popular_value
  where "at_most_one_popular_value F \<equiv> \<exists>\<^sub>\<le>\<^sub>1 y. popular_value F y"

  definition small_function
  where "small_function F \<equiv> small (range F) \<and> at_most_one_popular_value F"

  lemma small_preimage_unpopular:
  fixes F :: "'a \<Rightarrow> 'b"
  assumes "small_function F"
  shows "small {x. F x \<noteq> some_popular_value F}"
  proof (cases "\<exists>y. popular_value F y")
    assume 1: "\<not> (\<exists>y. popular_value F y)"
    have "\<And>y. small {x. F x = y}"
      using 1 by blast
    moreover have "UNIV = (\<Union>y\<in>range F. {x. F x = y})"
      by auto
    ultimately have "small (UNIV :: 'a set)"
      using assms(1) small_function_def by (metis small_UN)
    thus ?thesis
      using smaller_than_small by blast
    next
    assume 1: "\<exists>y. popular_value F y"
    have "popular_value F (some_popular_value F)"
      using 1 someI_ex [of "\<lambda>y. popular_value F y"] some_popular_value_def by metis
    hence 2: "\<And>y. y \<noteq> some_popular_value F \<Longrightarrow> small {x. F x = y}"
      using assms
      unfolding small_function_def
      by (meson Uniq_D)
    moreover have "{x. F x \<noteq> some_popular_value F} =
                   (\<Union>y\<in>{y. y \<in> range F \<and> y \<noteq> some_popular_value F}. {x. F x = y})"
      by auto
    ultimately show ?thesis
      using assms
      unfolding small_function_def
      by auto
  qed

  text \<open>
    A type \<open>'a\<close> ``admits exponentiation'' if there is an injective function that maps
    each small function from \<open>'a\<close> to \<open>'a\<close> back into \<open>'a\<close>.
  \<close>

  locale exponentiation =
  fixes type :: "'a itself"
  assumes admits_exponentiation:
            "\<exists>e :: ('a \<Rightarrow> 'a) \<Rightarrow> 'a. inj_on e (Collect small_function)"
  begin

    definition "some_inj" :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
    where "some_inj \<equiv> SOME e :: ('a \<Rightarrow> 'a) \<Rightarrow> 'a. inj_on e (Collect small_function)"

    lemma inj_some_inj:
    shows "inj_on some_inj (Collect small_function)"
      using some_inj_def admits_exponentiation
            someI_ex [of "\<lambda>e :: ('a \<Rightarrow> 'a) \<Rightarrow> 'a. inj_on e (Collect small_function)"]
      unfolding small_function_def
      by presburger

    definition app :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    where "app f \<equiv> inv_into
                     {F. small (range F) \<and>
                         at_most_one_popular_value F} some_inj f"

    lemma app_some_inj:
    assumes "small_function F"
    shows "app (some_inj F) = F"
      by (metis (mono_tags, lifting) Collect_cong assms inv_into_f_f app_def
          inj_some_inj mem_Collect_eq small_function_def)

    lemma some_inj_lam_app:
    assumes "f \<in> some_inj ` Collect small_function"
    shows "some_inj (\<lambda>x. app f x) = f"
      using assms f_inv_into_f
      unfolding small_function_def
      by (metis (no_types, lifting) app_def)

  end

  context
  begin

    text \<open>
      The type @{typ V} (axiomatized in @{theory "ZFC_in_HOL.ZFC_in_HOL"}) admits exponentiation.
      We show this by exhibiting a ``small encoding'' for small functions.  We provide this fact
      as evidence of the nontriviality of the subsequent development, in the sense that if the
      existence of the type @{typ V} is consistent with HOL, then the existence of infinite types
      satisfying the locale assumptions for @{locale exponentiation} is also consistent with HOL.
    \<close>

    interpretation exponentiation \<open>TYPE(V)\<close>
    proof
      show "\<exists>e :: (V \<Rightarrow> V) \<Rightarrow> V. inj_on e (Collect small_function)"
      proof
        let ?e = "\<lambda>F. vpair (some_popular_value F)
                            (set ((\<lambda>a. vpair a (F a)) ` {x. F x \<noteq> some_popular_value F}))"
        show "inj_on ?e (Collect small_function)"
        proof (intro inj_onI)
          fix F F' :: "V \<Rightarrow> V"
          assume F: "F \<in> Collect small_function"
          assume F': "F' \<in> Collect small_function"
          assume eq:
            "vpair (some_popular_value F)
                   (set ((\<lambda>a. vpair a (F a)) ` {x. F x \<noteq> some_popular_value F})) =
             vpair (some_popular_value F')
                   (set ((\<lambda>a. vpair a (F' a)) ` {x. F' x \<noteq> some_popular_value F'}))"
          have 1: "some_popular_value F = some_popular_value F' \<and>
                   set ((\<lambda>a. vpair a (F a)) ` {x. F x \<noteq> some_popular_value F}) =
                   set ((\<lambda>a. vpair a (F' a)) ` {x. F' x \<noteq> some_popular_value F'})"
            using eq by blast
          have 2: "(\<lambda>a. vpair a (F a)) ` {x. F x \<noteq> some_popular_value F} =
                   (\<lambda>a. vpair a (F' a)) ` {x. F' x \<noteq> some_popular_value F'}"
          proof -
            have "small {x. F x \<noteq> some_popular_value F}"
              using F small_preimage_unpopular by blast
            hence "small ((\<lambda>a. vpair a (F a)) ` {x. F x \<noteq> some_popular_value F})"
              by blast
            thus ?thesis
              by (metis (full_types) 1 F' mem_Collect_eq replacement set_injective
                  small_preimage_unpopular)
          qed
          show "F = F'"
          proof
            fix x
            show "F x = F' x"
              using 1 2
              by (cases "F x = some_popular_value F") force+
          qed
        qed
      qed
    qed

    lemma V_admits_exponentiation:
    shows "exponentiation TYPE(V)"
      ..

  end

subsubsection "Universe"

  locale universe = nondegenerate_and_pairing + exponentiation

  text\<open>
    The type @{typ V} axiomatized in @{theory "ZFC_in_HOL.ZFC_in_HOL"} is a universe.
  \<close>

  context
  begin

    interpretation nondegenerate \<open>TYPE(V)\<close>
    proof
      obtain f :: "bool \<Rightarrow> V" where f: "inj f"
        using inj_compose inj_ord_of_nat by blast
      show "\<exists>x y :: V. x \<noteq> y"
        by (metis Inl_Inr_iff)
    qed

    lemma V_is_nondegenerate:
    shows "nondegenerate TYPE(V)"
      ..

    interpretation pairing \<open>TYPE(V)\<close>
      apply unfold_locales
      using inj_on_vpair by blast

    lemma V_admits_pairing:
    shows "pairing TYPE(V)"
      ..

    interpretation exponentiation \<open>TYPE(V)\<close>
      using V_admits_exponentiation by blast

    interpretation universe \<open>TYPE(V)\<close>
      ..

    lemma V_is_universe:
    shows "universe TYPE(V)"
      ..

  end

subsection "Small RTS's"

  text\<open>
    We will call an RTS ``small'' if its set of arrows is a small set.
  \<close>

  locale small_rts =
    rts +
  assumes small: "small (Collect arr)"

  lemma isomorphic_to_small_rts_is_small_rts:
  assumes "small_rts A" and "isomorphic_rts A B"
  shows "small_rts B"
  proof -
    interpret A: small_rts A
      using assms by blast
    interpret B: rts B
      using assms isomorphic_rts_def inverse_simulations_def by blast
    obtain F G where FG: "inverse_simulations A B F G"
      using assms isomorphic_rts_def by blast
    interpret FG: inverse_simulations A B F G
      using FG by blast
    show "small_rts B"
      using A.small FG.G.is_bijection_betw_arr_sets
      apply unfold_locales
      by (metis bij_betw_imp_surj_on replacement)
  qed

subsubsection "Injective Image of Small RTS"

  context inj_image_rts
  begin

    lemma preserves_reflects_small_rts:
    shows "small_rts A \<longleftrightarrow> small_rts resid"
      using induce_bij_betw_arr_sets
      by (metis (no_types, lifting) A.rts_axioms bij_betw_def rts_axioms
          small_image_iff small_rts.intro small_rts.small small_rts_axioms_def)

  end

subsubsection "Empty RTS is Small"

  context empty_rts
  begin

    sublocale small_rts resid
      apply unfold_locales
      by (metis Collect_empty_eq arr_char small_empty)

    lemma is_small_rts:
    shows "small_rts resid"
      ..

  end

subsubsection "One-Arrow RTS is Small"

  context one_arr_rts
  begin

    sublocale small_rts resid
      by (simp add: Collect_cong arr_char rts_axioms small_rts.intro
          small_rts_axioms.intro)

    lemma is_small_rts:
    shows "small_rts resid"
      ..

  end

subsubsection "Fiber Product of Small RTS's"

  context fiber_product_rts
  begin

    lemma preserves_small_rts:
    assumes "small_rts A" and "small_rts B"
    shows "small_rts resid"
    proof
      interpret A: small_rts A
        using assms(1) by blast
      interpret B: small_rts B
        using assms(2) by blast
      show "small (Collect arr)"
      proof -
        have 1: "Collect arr \<subseteq> {t. A.arr (fst t) \<and> B.arr (snd t)}"
          using arr_char by blast
        obtain \<phi>
          where \<phi>: "inj_on \<phi> (Collect A.arr) \<and> \<phi> ` Collect A.arr \<in> range elts"
          using A.small small_def by metis
        obtain \<psi>
          where \<psi>: "inj_on \<psi> (Collect B.arr) \<and> \<psi> ` Collect B.arr \<in> range elts"
          using B.small small_def by metis
        let ?\<phi>\<psi> = "\<lambda>ab. vpair (\<phi> (fst ab)) (\<psi> (snd ab))"
        have "inj_on ?\<phi>\<psi> (Collect arr)"
          using 1 \<phi> \<psi> arr_char inj_on_def [of \<phi> "Collect A.arr"]
                inj_on_def [of \<psi> "Collect B.arr"] prod.expand
          by (intro inj_onI) force
        moreover have "?\<phi>\<psi> ` Collect arr \<in> range elts"
        proof -
          have "?\<phi>\<psi> ` Collect arr \<subseteq>
                elts (vtimes (set (\<phi> ` Collect A.arr)) (set (\<psi> ` Collect B.arr)))"
            using A.small B.small arr_char by auto
          thus ?thesis
            by (meson down_raw)
        qed
        ultimately show ?thesis
          by (meson small_def)
      qed
    qed

  end

  locale fiber_product_of_small_rts =
    A: small_rts A +
    B: small_rts B +
    fiber_product_rts
  begin

    sublocale small_rts resid
      by (simp add: A.small_rts_axioms B.small_rts_axioms preserves_small_rts)

    lemma is_small_rts:
    shows "small_rts resid"
      ..

  end

subsubsection "Product of Small RTS's"

  context product_rts
  begin

    lemma preserves_small_rts:
    assumes "small_rts A" and "small_rts B"
    shows "small_rts resid"
    proof
      interpret A: small_rts A
        using assms(1) by blast
      interpret B: small_rts B
        using assms(2) by blast
      show "small (Collect arr)"
      proof -
        (* It is slightly shorter to use what has already been shown for fiber product. *)
        interpret One: one_arr_rts \<open>TYPE(bool)\<close>
          by unfold_locales auto
        interpret A: simulation A One.resid \<open>One.terminator A\<close>
          using One.terminator_is_simulation A.rts_axioms by blast
        interpret B: simulation B One.resid \<open>One.terminator B\<close>
          using One.terminator_is_simulation B.rts_axioms by blast
        interpret AxB: fiber_product_of_small_rts A B One.resid
                           \<open>One.terminator A\<close> \<open>One.terminator B\<close> ..
        have "Collect arr \<subseteq> Collect AxB.arr"
          using AxB.arr_char arr_char One.terminator_def
          by (metis Collect_mono)
        moreover have "small (Collect AxB.arr)"
          using AxB.small by blast
        ultimately show ?thesis
          using smaller_than_small by blast
      qed
    qed

  end

  locale product_of_small_rts =
    A: small_rts A +
    B: small_rts B +
    product_rts
  begin

    sublocale small_rts resid
      using A.small_rts_axioms B.small_rts_axioms preserves_small_rts
      by blast

    lemma is_small_rts:
    shows "small_rts resid"
      ..

  end

subsubsection "Exponential of Small RTS's"

  lemma small_function_transformation:
  assumes "small_rts A" and "small_rts B" and "transformation A B F G T"
  shows "small_function T"
  proof -
    interpret A: small_rts A
      using assms(1) by blast
    interpret B: small_rts B
      using assms(2) by blast
    interpret T: transformation A B F G T
      using assms(3) by blast
    have 1: "range T \<subseteq> Collect B.arr \<union> {B.null}"
      using T.extensionality T.preserves_arr by blast
    show ?thesis
    proof (unfold small_function_def, intro conjI)
      show "small (range T)"
        using assms(2) 1 B.small smaller_than_small by blast
      show "at_most_one_popular_value T"
      proof -
        have "\<And>v. popular_value T v \<Longrightarrow> v = B.null"
        proof -
          fix v
          assume v: "popular_value T v"
          have "v \<noteq> B.null \<Longrightarrow> v \<in> range T"
            using v
            by (metis (mono_tags, lifting) empty_Collect_eq rangeI small_empty)
          thus "v = B.null"
            by (metis (mono_tags, lifting) A.small Collect_mono T.extensionality
                smaller_than_small v)
        qed
        thus ?thesis
          using Uniq_def by blast
      qed
    qed
  qed

  text \<open>
    We can't simply use the previous fact to prove the following, because our
    definition of transformation includes extensionality conditions that are
    not part of the definition of simulation.  So, we have to repeat the proof.
  \<close>

  lemma small_function_simulation:
  assumes "small_rts A" and "small_rts B" and "simulation A B F"
  shows "small_function F"
  proof -
    interpret A: small_rts A
      using assms(1) by blast
    interpret B: small_rts B
      using assms(2) by blast
    interpret F: simulation A B F
      using assms(3) by blast
    have 1: "range F \<subseteq> Collect B.arr \<union> {B.null}"
      using F.extensionality F.preserves_reflects_arr by blast
    show ?thesis
    proof (unfold small_function_def, intro conjI)
      show "small (range F)"
        using assms(2) 1 B.small smaller_than_small by blast
      show "at_most_one_popular_value F"
      proof -
        have "\<And>v. popular_value F v \<Longrightarrow> v = B.null"
        proof -
          fix v
          assume v: "popular_value F v"
          have "v \<noteq> B.null \<Longrightarrow> v \<in> range F"
            using v
            by (metis (mono_tags, lifting) empty_Collect_eq rangeI small_empty)
          thus "v = B.null"
            by (metis (mono_tags, lifting) A.small Collect_mono F.extensionality
                smaller_than_small v)
        qed
        thus ?thesis
          using Uniq_def by blast
      qed
    qed
  qed

  lemma small_function_resid:
  fixes A :: "'a resid"
  assumes "small_rts A"
  shows "small_function A"
  and "\<And>t. small_function (A t)"
  proof -
    interpret A: small_rts A
      using assms by blast
    show 1: "small_function A"
    proof (unfold small_function_def, intro conjI)
      show "small (range A)"
      proof -
        have "range A \<subseteq> A ` Collect A.arr \<union> A ` {x. \<not> A.arr x}"
          by blast
        moreover have "small (A ` Collect A.arr)"
          using A.small by blast
        moreover have "small (A ` {x. \<not> A.arr x})"
        proof -
          have "\<And>x. \<not> A.arr x \<Longrightarrow> A x = (\<lambda>x. A.null)"
            using A.con_implies_arr(1) by blast
          hence "A ` {x. \<not> A.arr x} \<subseteq> {\<lambda>x. A.null}"
            by blast
          thus ?thesis
            by (meson small_empty small_insert smaller_than_small)
        qed
        ultimately show ?thesis
          by (meson small_Un smaller_than_small)
      qed
      show "at_most_one_popular_value A"
      proof -
        have "\<And>v. popular_value A v \<Longrightarrow> v \<in> A ` {x. \<not> A.arr x}"
        proof -
          fix v
          assume v: "popular_value A v"
          have "\<not> small {x. \<not> A.arr x \<and> A x = v}"
          proof -
            have "\<not> small ({x. A x = v} - {x. A.arr x \<and> A x = v})"
              by (metis (mono_tags, lifting) A.small Collect_mono
                  Un_Diff_cancel small_Un smaller_than_small sup_ge2 v)
            moreover have "{x. A x = v} - {x. A.arr x \<and> A x = v} =
                           {x. \<not> A.arr x \<and> A x = v}"
              by blast
            ultimately show ?thesis by metis
          qed
          hence "v \<in> A ` {x. \<not> A.arr x \<and> A x = v}"
            by (metis (mono_tags, lifting) empty_Collect_eq image_eqI
                mem_Collect_eq small_empty)
          thus "v \<in> A ` {x. \<not> A.arr x}" by blast
        qed
        moreover have "A ` {x. \<not> A.arr x} \<subseteq> {\<lambda>x. A.null}"
        proof -
          have "\<And>x. \<not> A.arr x \<Longrightarrow> A x = (\<lambda>x. A.null)"
            using A.con_implies_arr(1) by blast
          thus ?thesis by blast
        qed
        ultimately show ?thesis
          by (metis (no_types, lifting) Uniq_def empty_iff singletonD
              subset_singleton_iff)
      qed
    qed
    show 2: "\<And>t. small_function (A t)"
    proof -
      fix t
      show "small_function (A t)"
      proof (unfold small_function_def, intro conjI)
        show "small (range (A t))"
        proof -
          have "range (A t) \<subseteq> Collect A.arr \<union> {A.null}"
            using A.arr_resid by blast
          moreover have "small (Collect A.arr \<union> {A.null})"
            using A.small by simp
          ultimately show ?thesis
            using smaller_than_small by blast
        qed
        show "at_most_one_popular_value (A t)"
        proof -
          have "\<And>v. popular_value (A t) v \<Longrightarrow> v = A.null"
          proof -
            fix v
            assume v: "popular_value (A t) v"
            have "\<not> small {u. A t u = v}"
              using v by blast
            hence "\<not> ({u. A t u = v} \<subseteq> Collect A.arr)"
              using A.small smaller_than_small by blast
            hence "\<exists>u. A t u = v \<and> \<not> A.arr u"
              by blast
            thus "v = A.null"
              using A.con_implies_arr(2) by blast
          qed
          thus ?thesis
            using Uniq_def by blast
         qed
      qed
    qed
  qed

  context exponentiation
  begin

    lemma small_function_some_inj_resid:
    fixes A :: "'a resid"
    assumes "small_rts A"
    shows "small_function (\<lambda>t. some_inj (A t))"
    proof -
      interpret A: small_rts A
        using assms by blast
      show "small_function (\<lambda>t. some_inj (A t))"
      proof (unfold small_function_def, intro conjI)
        show "small (range (\<lambda>t. some_inj (A t)))"
        proof -
          have "range (\<lambda>t. some_inj (A t)) = some_inj ` range (\<lambda>t. A t)"
            by auto
          moreover have "small ..."
            using assms small_function_resid(1)
            by (metis replacement small_function_def)
          ultimately show ?thesis by auto
        qed
        show "at_most_one_popular_value (\<lambda>t. some_inj (A t))"
        proof -
          have 3: "\<And>t v. popular_value (\<lambda>t. some_inj (A t)) v
                            \<Longrightarrow> v \<in> some_inj ` Collect (popular_value A)"
          proof -
            fix t v
            assume v: "popular_value (\<lambda>t. some_inj (A t)) v"
            have "\<not> small {t. A t = inv_into (Collect small_function) some_inj v}"
            (*
              using assms v inj_some_inj small_function_resid(2) inv_into_f_f
                    small_empty
              by (smt (verit) CollectI Collect_cong Collect_empty_eq)
             *)
            proof - (* TODO: Best I have found without smt. *)
              have 1: "\<And>t. A.arr t \<longleftrightarrow> some_inj (A t) \<noteq> v"
              proof
                have 2: "\<And>t. A.arr t \<longleftrightarrow> A t \<noteq> (\<lambda>u. A.null)"
                  using A.con_implies_arr(1) by fastforce
                have 3: "v = some_inj (\<lambda>u. A.null)"
                  using v 2
                  by (metis (mono_tags, lifting) A.small Collect_mono
                      smaller_than_small)
                show "\<And>t. some_inj (A t) \<noteq> v \<Longrightarrow> A.arr t"
                  using 2 3 by force
                show "\<And>t. A.arr t \<Longrightarrow> some_inj (A t) \<noteq> v"
                  using assms 2 3 inj_some_inj app_some_inj small_function_resid(2)
                  by (metis A.not_arr_null)
              qed
              have "{t. A t = inv_into (Collect small_function) some_inj v} =
                    {t. \<not> A.arr t}"
                using 1
                by (metis (no_types, lifting) A.not_arr_null CollectD CollectI
                    app_some_inj assms f_inv_into_f image_eqI inv_into_into
                    small_function_resid(2))
              thus ?thesis
                using v 1 by auto
            qed
            hence "inv_into (Collect small_function) some_inj v
                      \<in> Collect (popular_value A)"
              by auto
            moreover have "some_inj
                             (inv_into (Collect small_function) some_inj v) = v"
              using assms v inj_some_inj
                    f_inv_into_f [of v some_inj "Collect small_function"]
              by (metis (mono_tags) small_function_resid(2) empty_Collect_eq
                  inv_into_f_f mem_Collect_eq small_empty)
            ultimately show "v \<in> some_inj ` Collect (popular_value A)"
              by force
          qed
          show ?thesis
          proof
            fix u v
            assume u: "popular_value (\<lambda>x. some_inj (A x)) u"
            assume v: "popular_value (\<lambda>x. some_inj (A x)) v"
            obtain f where f: "popular_value A f \<and> some_inj f = u"
              using u 3 by blast
            obtain g where g: "popular_value A g \<and> some_inj g = v"
              using v 3 by blast
            have "f = g"
              using assms f g small_function_resid(1) Uniq_D
              unfolding small_function_def
              by auto fastforce
            thus "u = v"
              using f g by blast
          qed
        qed
      qed
    qed

    fun some_inj_resid :: "'a resid \<Rightarrow> 'a"
    where "some_inj_resid A = (some_inj (\<lambda>t. some_inj (A t)))"

    lemma inj_on_some_inj_resid:
    shows "inj_on some_inj_resid {A :: 'a resid. small_rts A}"
    proof
      fix A B :: "'a resid"
      assume A: "A \<in> {A. small_rts A}" and B: "B \<in> {B. small_rts B}"
      assume eq: "some_inj_resid A = some_inj_resid B"
      interpret A: small_rts A
        using A by blast
      interpret B: small_rts B
        using B by blast
      show "A = B"
      proof -
        have "some_inj (\<lambda>t. some_inj (A t)) = some_inj (\<lambda>t. some_inj (B t))"
          using A B eq by simp
        moreover have "small_function (\<lambda>t. some_inj (A t))"
          using A small_function_some_inj_resid by auto
        moreover have "small_function (\<lambda>t. some_inj (B t))"
          using B small_function_some_inj_resid by auto
        ultimately have "(\<lambda>t. some_inj (A t)) = (\<lambda>t. some_inj (B t))"
          using A B inj_some_inj
          by (simp add: inj_onD)
        hence "\<And>t. A t = B t"
          using A B inj_some_inj small_function_resid(2)
          by (metis app_some_inj mem_Collect_eq)
        thus "A = B" by blast
      qed
    qed

  end

  locale exponential_of_small_rts =
    A: small_rts A +
    B: small_rts B +
    exponential_rts
  begin

    lemma small_Collect_fun:
    shows "small {F. F ` Collect A.arr \<subseteq> Collect B.arr \<and>
                     F ` (UNIV - Collect A.arr) \<subseteq> {B.null}}"
    proof -
      let ?\<F> = "{F. F ` Collect A.arr \<subseteq> Collect B.arr \<and>
                    F ` (UNIV - Collect A.arr) \<subseteq> {B.null}}"
      obtain \<phi> where \<phi>: "inj_on \<phi> (Collect A.arr) \<and> \<phi> ` Collect A.arr \<in> range elts"
        using A.small small_def by metis
      obtain \<psi> where \<psi>: "inj_on \<psi> (Collect B.arr) \<and> \<psi> ` Collect B.arr \<in> range elts"
        using B.small small_def by metis
      let ?graph = "\<lambda>F :: 'a \<Rightarrow> 'b. set ((\<lambda>x. vpair (\<phi> x) (\<psi> (F x))) ` Collect A.arr)"
      have "?graph ` ?\<F> \<subseteq> elts (VPow (vtimes (set (\<phi> ` Collect A.arr))
                                              (set (\<psi> ` Collect B.arr))))"
        using A.small B.small small_def
        by (simp add: image_subset_iff set_image_le_iff)
      moreover have "inj_on ?graph ?\<F>"
      proof (intro inj_onI)
        fix F G
        assume F: "F \<in> ?\<F>" and G: "G \<in> ?\<F>"
        and eq: "?graph F = ?graph G"
        show "F = G"
        proof
          fix x
          show "F x = G x"
          proof (cases "A.arr x")
            show "\<not> A.arr x \<Longrightarrow> ?thesis"
              using F G
              by (simp add: image_subset_iff)
            assume x: "A.arr x"
            have "?graph F = ?graph G"
              using eq by simp
            hence "(\<lambda>x. vpair (\<phi> x) (\<psi> (F x))) ` Collect A.arr =
                   (\<lambda>x. vpair (\<phi> x) (\<psi> (G x))) ` Collect A.arr"
              using A.small by auto
            hence "\<exists>x'. A.arr x' \<and> vpair (\<phi> x) (\<psi> (F x)) = vpair (\<phi> x') (\<psi> (G x'))"
              using x by blast
            hence "vpair (\<phi> x) (\<psi> (F x)) = vpair (\<phi> x) (\<psi> (G x))"
              by (metis x \<phi> inj_onD mem_Collect_eq vpair_inject)
            hence "\<psi> (F x) = \<psi> (G x)"
              by blast
            thus ?thesis
              using x F G \<psi> inj_onD [of \<psi> "Collect B.arr" "F x" "G x"] by blast
          qed
        qed
      qed
      ultimately show ?thesis
        by (meson down_raw small_def)
    qed

    lemma small_Collect_simulation:
    shows "small (Collect (simulation A B))"
    proof -
      have "\<And>F. simulation A B F \<Longrightarrow>
                   F ` Collect A.arr \<subseteq> Collect B.arr \<and>
                   F ` (UNIV - Collect A.arr) \<subseteq> {B.null}"
        apply (intro conjI)
         apply (simp add: image_subset_iff simulation.preserves_reflects_arr)
        using simulation.extensionality by fastforce
      thus ?thesis
        by (metis (no_types, lifting) Collect_mono small_Collect_fun smaller_than_small)
    qed

    lemma small_Collect_transformation:
    assumes "simulation A B F" and "simulation A B G"
    shows "small (Collect (transformation A B F G))"
    proof -
      have "\<And>\<tau>. transformation A B F G \<tau> \<Longrightarrow>
                  \<tau> ` Collect A.arr \<subseteq> Collect B.arr \<and>
                  \<tau> ` (UNIV - Collect A.arr) \<subseteq> {B.null}"
        by (metis (mono_tags, lifting) DiffD2 image_subsetI mem_Collect_eq
            singleton_iff transformation.extensionality transformation.preserves_arr)
      thus ?thesis
        by (metis (no_types, lifting) Collect_mono small_Collect_fun
            smaller_than_small)
    qed

    sublocale small_rts resid
    proof
      have "small (\<Union>FG\<in>Collect (simulation A B) \<times> Collect (simulation A B).
                                {FG} \<times> Collect (transformation A B (fst FG) (snd FG)))"
      proof -
        have "small (Collect (simulation A B) \<times> Collect (simulation A B))"
          using small_Collect_simulation by fastforce
        moreover
        have "\<And>FG. FG \<in> Collect (simulation A B) \<times> Collect (simulation A B) \<Longrightarrow>
                    small ({FG} \<times> Collect (transformation A B (fst FG) (snd FG)))"
          using small_Collect_transformation by force
        ultimately show ?thesis by blast
      qed
      moreover have "(\<lambda>t. ((Dom t, Cod t), Map t)) ` Collect arr \<subseteq>
              (\<Union>FG\<in>Collect (simulation A B) \<times> Collect (simulation A B).
                {FG} \<times> Collect (transformation A B (fst FG) (snd FG)))"
      proof
        fix T
        assume T: "T \<in> (\<lambda>t. ((Dom t, Cod t), Map t)) ` Collect arr"
        obtain t where t: "arr t \<and> T = ((Dom t, Cod t), Map t)"
          using T by blast
        have "simulation A B (Dom t) \<and> simulation A B (Cod t) \<and>
              transformation A B (Dom t) (Cod t) (Map t)"
          by (meson arr_char t transformation_def)
        thus "T \<in>
                 (\<Union>FG\<in>Collect (simulation A B) \<times> Collect (simulation A B).
                {FG} \<times> Collect (transformation A B (fst FG) (snd FG)))"
          using t by simp
      qed
      ultimately have "small ((\<lambda>t. ((Dom t, Cod t), Map t)) ` Collect arr)"
        using smaller_than_small by blast
      moreover have "inj_on (\<lambda>t. ((Dom t, Cod t), Map t)) (Collect arr)"
        using not_arr_null null_char MkArr_Map
        by (intro inj_onI) (metis fst_conv mem_Collect_eq snd_eqD)
      ultimately show "small (Collect arr)" by auto
    qed

    lemma is_small_rts:
    shows "small_rts resid"
      ..

  end

  text\<open>
    An RTS-category is \emph{locally small} if each of the hom-RTS's is a small RTS.
  \<close>

  locale locally_small_rts_category =
    rts_category +
  assumes small_homs: "\<lbrakk>obj a; obj b\<rbrakk> \<Longrightarrow> small (H.hom a b)"
  begin

    lemma HOM_is_small_extensional_rts:
    assumes "obj a" and "obj b"
    shows "HOM a b \<in> Collect extensional_rts \<inter> Collect small_rts"
    proof -
      interpret HOM: sub_rts resid \<open>\<lambda>t. t \<in> H.hom a b\<close>
        using assms sub_rts_HOM by fastforce
      interpret HOM: small_rts HOM.resid
        using assms small_homs [of a b] smaller_than_small HOM.arr_char
        apply unfold_locales
        by (simp add: smaller_than_small subset_eq)
      show ?thesis
        using HOM.preserves_extensional_rts V.extensional_rts_axioms
              HOM.small_rts_axioms
        by auto
    qed

  end

end

