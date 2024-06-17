(*  Title:       RTSConstructions
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

theory RTSConstructions
imports Main Preliminaries ZFC_in_HOL.ZFC_Cardinals
begin

section "Notation"

  text \<open>
    Some of the theories in the HOL library that we depend on define global notation involving
    generic symbols that we would like to use here.  It would be best if there were some way
    to import these theories without also having to import this notation, but for now the best
    we can do is to uninstall the notation involving the symbols at issue.
  \<close>

  (* I really don't like global notation -- it's rude. *)
  no_notation Equipollence.eqpoll (infixl "\<approx>" 50)
  no_notation Equipollence.lepoll (infixl "\<lesssim>" 50)
  no_notation Lattices.sup_class.sup (infixl "\<squnion>" 65)
  no_notation ZFC_Cardinals.cmult   (infixl \<open>\<otimes>\<close> 70)

  no_syntax "_Tuple"    :: "[V, Vs] \<Rightarrow> V"                 ("\<langle>(_,/ _)\<rangle>")
  no_syntax "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   ("\<langle>(_,/ _)\<rangle>")

section "Some Constraints on a Type"

subsection "Nondegenerate"

  text \<open>
    We will call a type ``nondegenerate'' if it has at least two elements.
    This means that the type admits RTS's with a non-empty set of arrows
    (after using one of the elements for the required null value).
  \<close>

  locale nondegenerate =
  fixes type :: "'a itself"
  assumes is_nondegenerate: "\<exists>x y :: 'a. x \<noteq> y"

subsection "Lifting"

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

subsection "Pairing"

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

subsection "Exponentiation"

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

subsection "Universe"

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

section "Small RTS's"

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
      using T.extensional T.preserves_arr by blast
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
            by (metis (mono_tags, lifting) A.small Collect_mono T.extensional
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
      using F.extensional F.preserves_reflects_arr by blast
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
            by (metis (mono_tags, lifting) A.small Collect_mono F.extensional
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

section "Injective Images of RTS's"

  text\<open>
    Here we show that the image of an RTS \<open>A\<close> at type @{typ 'a}, under a function from @{typ 'a}
    to @{typ 'b} that is injective on the set of arrows, is an RTS at type @{typ 'b} that is
    isomorphic to \<open>A\<close>.  We will use this, together with the universe assumptions, to obtain
    isomorphic images, of constructions such as product and exponential RTS, that yield results
    that ``live'' at the same type as their arguments.
  \<close>

  locale inj_image_rts =
    A: rts A
    for map :: "'a \<Rightarrow> 'b"
    and A :: "'a resid"  (infix "\\\<^sub>A" 70) +
    assumes inj_map: "inj_on map (Collect A.arr \<union> {A.null})"
  begin

    notation A.con    (infix "\<frown>\<^sub>A" 50)
    notation A.prfx   (infix "\<lesssim>\<^sub>A" 50)
    notation A.cong   (infix "\<sim>\<^sub>A" 50)

    abbreviation Null
    where "Null \<equiv> map A.null"

    abbreviation Arr
    where "Arr t \<equiv> t \<in> map ` Collect A.arr"

    abbreviation map'
    where "map' t \<equiv> inv_into (Collect A.arr) map t"

    definition resid :: "'b resid"  (infix "\\" 70)
    where "t \\ u = (if Arr t \<and> Arr u then map (map' t \\\<^sub>A map' u) else Null)"

    lemma inj_map':
    shows "inj_on map (Collect A.arr)"
      using inj_map by auto

    lemma map_null:
    shows "map A.null \<notin> map ` Collect A.arr"
      using inj_map by simp

    lemma map'_map [simp]:
    assumes "A.arr t"
    shows "map' (map t) = t"
      using assms inj_map by simp

    lemma map_map' [simp]:
    assumes "Arr t"
    shows "map (map' t) = t"
      using assms f_inv_into_f by metis

    sublocale ResiduatedTransitionSystem.partial_magma resid
      by (metis ResiduatedTransitionSystem.partial_magma.intro map_null resid_def)

    lemma null_char:
    shows "null = Null"
      by (metis map_null null_is_zero(2) resid_def)

    sublocale residuation resid
    proof
      show "\<And>t u. t \\ u \<noteq> null \<Longrightarrow> u \\ t \<noteq> null"
        unfolding resid_def null_char
        by (metis A.arr_resid A.conI A.con_sym imageI map_null mem_Collect_eq)
      show "\<And>t u. t \\ u \<noteq> null \<Longrightarrow> (t \\ u) \\ (t \\ u) \<noteq> null"
        unfolding resid_def null_char inj_map
        apply simp
        by (metis CollectI A.arr_resid A.conI A.con_imp_arr_resid imageI
            map'_map map_null)
      show "\<And>v t u. (v \\ t) \\ (u \\ t) \<noteq> null
                        \<Longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
      proof -
        fix t u v
        assume vt_ut: "(v \\ t) \\ (u \\ t) \<noteq> null"
        have 1: "Arr t \<and> Arr u \<and> Arr v"
          using vt_ut
          by (metis map_null null_char resid_def)
        have "(v \\ t) \\ (u \\ t) = map ((map' v \\\<^sub>A map' t) \\\<^sub>A (map' u \\\<^sub>A map' t))"
          using 1 null_char resid_def vt_ut
          apply auto[1]
          by (metis A.arr_resid A.conI map'_map map_null vt_ut)
        also have
            "... = map ((map' v \\\<^sub>A map' u) \\\<^sub>A (map' t \\\<^sub>A map' u))"
          using A.cube by simp
        also have "... = (v \\ u) \\ (t \\ u)"
          using 1 null_char resid_def
          apply auto[1]
            apply (metis CollectI A.conI image_eqI map'_map map_null A.arr_resid)
           apply (metis A.conI A.con_implies_arr(1) image_eqI mem_Collect_eq)
          by (metis CollectI A.conI A.con_implies_arr(2) image_eqI)
        finally show "(v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
          by blast
      qed
    qed

    notation con   (infix "\<frown>" 50)

    lemma con_char:
    shows "t \<frown> u \<longleftrightarrow> Arr t \<and> Arr u \<and> map' t \<frown>\<^sub>A map' u"
      using null_char con_def inj_map resid_def A.con_def
      by (metis (full_types) image_eqI map_null mem_Collect_eq A.arr_resid)

    lemma arr_char:
    shows "arr t \<longleftrightarrow> Arr t"
      using arr_def con_char inj_map by auto

    lemma ide_char\<^sub>I\<^sub>I:
    shows "ide t \<longleftrightarrow> Arr t \<and> A.ide (map' t)"
      unfolding ide_def resid_def con_char
      using inj_map' f_inv_into_f
      by (metis A.ide_def inv_into_f_f mem_Collect_eq A.arr_resid)

    lemma trg_char:
    shows "trg t = (if Arr t then map (A.trg (map' t)) else null)"
      unfolding trg_def resid_def A.trg_def null_char by simp

    sublocale rts resid
    proof
      show "\<And>t. arr t \<Longrightarrow> ide (trg t)"
        using ide_char\<^sub>I\<^sub>I inj_map trg_char trg_def by fastforce
      show 1: "\<And>a t. \<lbrakk>ide a; t \<frown> a\<rbrakk> \<Longrightarrow> t \\ a = t"
        by (simp add: A.resid_arr_ide con_char f_inv_into_f ide_char\<^sub>I\<^sub>I resid_def)
      show "\<And>a t. \<lbrakk>ide a; a \<frown> t\<rbrakk> \<Longrightarrow> ide (a \\ t)"
        by (metis 1 arrE arr_resid con_sym cube ideE ideI)
      show "\<And>t u. t \<frown> u \<Longrightarrow> \<exists>a. ide a \<and> a \<frown> t \<and> a \<frown> u"
        by (metis (full_types) CollectI A.con_imp_coinitial_ax ide_char\<^sub>I\<^sub>I
            image_eqI inj_image_rts.con_char inj_image_rts_axioms map'_map
            A.ide_implies_arr)
      show "\<And>t u v. \<lbrakk>ide (t \\ u); u \<frown> v\<rbrakk> \<Longrightarrow> t \\ u \<frown> v \\ u"
      proof -
        fix t u v
        assume ide: "ide (t \\ u)"
        assume con: "u \<frown> v"
        have "Arr t \<and> Arr u \<and> Arr v"
          using ide con ide_char\<^sub>I\<^sub>I con_char
          by (metis arr_resid_iff_con ide_implies_arr)
        moreover have "A.arr (map' t \\\<^sub>A map' u)"
          using ide ide_char\<^sub>I\<^sub>I resid_def
          by (meson A.arr_resid arr_resid_iff_con con_char ide_implies_arr)
        moreover have "A.arr (map' v \\\<^sub>A map' u)"
          using con con_char
          by (meson A.arr_resid A.con_sym)
        ultimately show "t \\ u \<frown> v \\ u"
          using ide con ide_char\<^sub>I\<^sub>I con_char resid_def A.con_target by simp
      qed
    qed

    notation prfx   (infix "\<lesssim>" 50)
    notation cong   (infix "\<sim>" 50)

    text\<open>
      The function @{term map} and its inverse (both suitably extensionalized) determine an
      isomorphism between \<open>A\<close> and its image.
    \<close>

    abbreviation map\<^sub>e\<^sub>x\<^sub>t
    where "map\<^sub>e\<^sub>x\<^sub>t t \<equiv> if A.arr t then map t else null"

    abbreviation map'\<^sub>e\<^sub>x\<^sub>t
    where "map'\<^sub>e\<^sub>x\<^sub>t t \<equiv> if Arr t then map' t else A.null"

    sublocale Map: simulation A resid map\<^sub>e\<^sub>x\<^sub>t
      using con_char A.con_implies_arr resid_def
      by unfold_locales auto

    sublocale Map': simulation resid A map'\<^sub>e\<^sub>x\<^sub>t
      using arr_char con_char resid_def
      by unfold_locales auto

    sublocale inverse_simulations resid A map\<^sub>e\<^sub>x\<^sub>t map'\<^sub>e\<^sub>x\<^sub>t
      using arr_char map_null null_char
      by unfold_locales auto

    lemma invertible_simulation_map:
    shows "invertible_simulation A resid map\<^sub>e\<^sub>x\<^sub>t"
      using inverse_simulations_axioms inverse_simulations_sym invertible_simulation_def'
      by fast
      
    lemma invertible_simulation_map':
    shows "invertible_simulation resid A map'\<^sub>e\<^sub>x\<^sub>t"
      using inverse_simulations_axioms inverse_simulations_sym invertible_simulation_def'
      by fast

    lemma inj_on_map:
    shows "inj_on map\<^sub>e\<^sub>x\<^sub>t (Collect A.arr)"
      using induce_bij_betw_arr_sets bij_betw_def by blast

    lemma range_map':
    shows "map'\<^sub>e\<^sub>x\<^sub>t ` (Collect arr) = Collect A.arr"
      by (metis (no_types, lifting) bij_betw_imp_surj_on
          inverse_simulations.induce_bij_betw_arr_sets
          inverse_simulations_axioms inverse_simulations_sym)

    lemma cong_char\<^sub>I\<^sub>I:
    shows "t \<sim> u \<longleftrightarrow> Arr t \<and> Arr u \<and> map' t \<sim>\<^sub>A map' u"
      by (metis (full_types) Map'.preserves_resid Map.preserves_ide con_def
          ide_char\<^sub>I\<^sub>I not_arr_null null_char resid_def residuation.ide_implies_arr
          residuation_axioms)

    lemma preserves_weakly_extensional_rts:
    assumes "weakly_extensional_rts A"
    shows "weakly_extensional_rts resid"
      by (metis assms cong_char\<^sub>I\<^sub>I ide_char\<^sub>I\<^sub>I inv_into_injective rts_axioms
          weakly_extensional_rts.intro weakly_extensional_rts.weak_extensionality
          weakly_extensional_rts_axioms.intro)

    lemma preserves_extensional_rts:
    assumes "extensional_rts A"
    shows "extensional_rts resid"
    proof
      interpret A: extensional_rts A
        using assms by blast
      show "\<And>t u. t \<sim> u \<Longrightarrow> t = u"
        using cong_char\<^sub>I\<^sub>I ide_char\<^sub>I\<^sub>I
        by (meson A.extensional inv_into_injective)
    qed

    lemma preserves_reflects_small_rts:
    shows "small_rts A \<longleftrightarrow> small_rts resid"
      using induce_bij_betw_arr_sets
      by (metis (no_types, lifting) A.rts_axioms bij_betw_def rts_axioms
          small_image_iff small_rts.intro small_rts.small small_rts_axioms_def)

  end

  lemma inj_image_rts_comp:
  fixes F :: "'a \<Rightarrow> 'b" and G :: "'b \<Rightarrow> 'c"
  assumes "inj F" and "inj G"
  assumes "rts X"
  shows "inj_image_rts.resid (G \<circ> F) X =
         inj_image_rts.resid G (inj_image_rts.resid F X)"
  proof -
    interpret X: rts X
      using assms(3) by blast
    interpret FX: inj_image_rts F X
      by (metis X.rts_axioms assms(1)
          inj_image_rts_axioms_def inj_image_rts_def inj_on_subset top_greatest)
    interpret GFX: inj_image_rts G FX.resid
      by (metis (mono_tags, lifting) FX.rts_axioms assms(2) inj_def
          inj_image_rts_axioms_def inj_image_rts_def inj_onI)
    interpret GoF_X: inj_image_rts \<open>G o F\<close> X
      by (metis (no_types, opaque_lifting) X.rts_axioms
          assms(1-2) inj_compose inj_image_rts_axioms_def
          inj_image_rts_def inj_on_subset  top_greatest)
    show "GoF_X.resid = GFX.resid"
    proof -
      have "\<And>t u. GoF_X.resid t u = GFX.resid t u"
        unfolding GoF_X.resid_def GFX.resid_def
        using FX.arr_char FX.null_char FX.resid_def GoF_X.map'_map by auto
      thus ?thesis by blast
    qed
  qed

  lemma inj_image_rts_map_comp:
  fixes F :: "'a \<Rightarrow> 'b" and G :: "'b \<Rightarrow> 'c"
  assumes "inj F" and "inj G"
  assumes "rts X"
  shows "inj_image_rts.map\<^sub>e\<^sub>x\<^sub>t (G \<circ> F) X =
         inj_image_rts.map\<^sub>e\<^sub>x\<^sub>t G (inj_image_rts.resid F X) \<circ>
           (inj_image_rts.map\<^sub>e\<^sub>x\<^sub>t F X)"
  and "inj_image_rts.map'\<^sub>e\<^sub>x\<^sub>t (G \<circ> F) X =
       inj_image_rts.map'\<^sub>e\<^sub>x\<^sub>t F X \<circ>
         inj_image_rts.map'\<^sub>e\<^sub>x\<^sub>t G (inj_image_rts.resid F X)"
  proof -
    interpret X: rts X
      using assms(3) by blast
    interpret FX: inj_image_rts F X
      by (metis X.rts_axioms assms(1) inj_image_rts_axioms_def inj_image_rts_def
          inj_on_subset top_greatest)
    interpret GFX: inj_image_rts G FX.resid
      by (metis FX.rts_axioms Int_UNIV_right assms(2) inj_image_rts.intro
          inj_image_rts_axioms.intro inj_on_Int)
    interpret GoF_X: inj_image_rts \<open>G o F\<close> X
      by (metis (no_types, opaque_lifting) X.rts_axioms assms(1-2) inj_compose
          inj_image_rts_axioms_def inj_image_rts_def inj_on_subset top_greatest)
    show "GoF_X.map\<^sub>e\<^sub>x\<^sub>t = GFX.map\<^sub>e\<^sub>x\<^sub>t \<circ> FX.map\<^sub>e\<^sub>x\<^sub>t"
      using FX.null_char GFX.null_char GoF_X.null_char by fastforce
    show "GoF_X.map'\<^sub>e\<^sub>x\<^sub>t = FX.map'\<^sub>e\<^sub>x\<^sub>t \<circ> GFX.map'\<^sub>e\<^sub>x\<^sub>t"
      using FX.arr_char FX.not_arr_null GoF_X.map'_map by fastforce
  qed

section "Empty RTS"

  text\<open>
    For any type, there exists an empty RTS having that type as its arrow type.
    Since types in HOL are nonempty, we may use the guaranteed element @{term undefined}
    as the null value.
  \<close>

  locale empty_rts
  begin

    definition resid :: "'e resid"
    where "resid t u = undefined"

    sublocale ResiduatedTransitionSystem.partial_magma resid
      by unfold_locales (metis resid_def)

    lemma null_char:
    shows "null = undefined"
      by (metis null_is_zero(1) resid_def)

    sublocale residuation resid
      apply unfold_locales
      by (metis resid_def)+
    
    lemma arr_char:
    shows "arr t \<longleftrightarrow> False"
      using null_char resid_def
      by (metis arrE conE)

    lemma ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S:
    shows "ide t \<longleftrightarrow> False"
      using arr_char by force

    lemma con_char:
    shows "con t u \<longleftrightarrow> False"
      by (simp add: con_def null_char resid_def)

    lemma trg_char:
    shows "trg t = null"
      by (simp add: null_char resid_def trg_def)

    sublocale rts resid
      apply unfold_locales
          apply (metis arr_char)
      by (metis con_char)+

    lemma cong_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S:
    shows "cong t u \<longleftrightarrow> False"
      by (simp add: ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S)

    sublocale small_rts resid
      apply unfold_locales
      by (metis Collect_empty_eq arr_char small_empty)

    lemma is_small_rts:
    shows "small_rts resid"
      ..

    sublocale extensional_rts resid
      by unfold_locales (simp add: cong_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S)

    lemma is_extensional_rts:
    shows "extensional_rts resid"
      ..

    lemma src_char:
    shows "src t = null"
      by (simp add: arr_char src_def)

    lemma prfx_char:
    shows "prfx t u \<longleftrightarrow> False"
      using ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S by metis

    lemma composite_of_char:
    shows "composite_of t u v \<longleftrightarrow> False"
      using composite_of_def prfx_char by metis

    lemma composable_char:
    shows "composable t u \<longleftrightarrow> False"
      using composable_def composite_of_char by metis

    lemma seq_char:
    shows "seq t u \<longleftrightarrow> False"
      using arr_char by (metis seqE)

    sublocale rts_with_composites resid
      by unfold_locales (simp add: composable_char seq_char)

    lemma is_rts_with_composites:
    shows "rts_with_composites resid"
      ..

    sublocale extensional_rts_with_composites resid ..

    lemma is_extensional_rts_with_composites:
    shows "extensional_rts_with_composites resid"
      ..

    lemma comp_char:
    shows "comp t u = null"
      by (meson composable_char composable_iff_comp_not_null)

    text\<open>
      There is a unique simulation from an empty RTS to any other RTS.
    \<close>

    definition initiator :: "'e resid \<Rightarrow> 'a \<Rightarrow> 'e"
    where "initiator A \<equiv> (\<lambda>t. ResiduatedTransitionSystem.partial_magma.null A)"

    lemma initiator_is_simulation:
    assumes "rts A"
    shows "simulation resid A (initiator A)"
      using assms initiator_def con_char
      by (metis rts_axioms simulation_axioms.intro simulation_def)

    lemma universality:
    assumes "rts A"
    shows "\<exists>!F. simulation resid A F"
    proof
      show "simulation resid A (initiator A)"
        using assms initiator_is_simulation by blast
      show "\<And>F. simulation resid A F \<Longrightarrow> F = initiator A"
        by (metis HOL.ext initiator_def arr_char simulation.extensional)
    qed

  end

section "One-Transition RTS"

  text\<open>
    For any type having at least two elements, there exists a one-transition RTS
    having that type as its arrow type.  We use the already-distinguished element
    @{term undefined} as the null value and some value distinct from @{term undefined}
    as the single transition.
  \<close>

  locale one_arr_rts =
    nondegenerate arr_type
    for arr_type :: "'t itself"
  begin

    definition the_arr :: 't
    where "the_arr \<equiv> SOME t. t \<noteq> undefined"

    definition resid :: "'t resid"  (infix "\\\<^sub>1" 70)
    where "resid t u = (if t = the_arr \<and> u = the_arr then the_arr else undefined)"

    sublocale ResiduatedTransitionSystem.partial_magma resid
      using resid_def
      by unfold_locales metis

    lemma null_char:
    shows "null = undefined"
      by (metis null_is_zero(1) resid_def)

    sublocale residuation resid
      using null_char resid_def
      by unfold_locales metis+

    notation con  (infix "\<frown>\<^sub>1" 50)

    lemma arr_char:
    shows "arr t \<longleftrightarrow> t = the_arr"
      using null_char resid_def is_nondegenerate
      by (metis (mono_tags, lifting) arr_def con_def someI_ex the_arr_def)

    lemma ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S:
    shows "ide t \<longleftrightarrow> t = the_arr"
      using arr_char ide_def resid_def by auto

    lemma con_char:
    shows "con t u \<longleftrightarrow> arr t \<and> arr u"
      by (metis arr_char con_arr_self con_implies_arr(2) con_sym)

    lemma trg_char:
    shows "trg t = (if arr t then t else null)"
      by (simp add: arr_char null_char resid_def trg_def)

    sublocale rts resid
      using con_char arr_char ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S trg_char ideE
      by unfold_locales metis+

    notation prfx  (infix "\<lesssim>\<^sub>1" 50)
    notation cong  (infix "\<sim>\<^sub>1" 50)

    lemma cong_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S:
    shows "t \<lesssim>\<^sub>1 u \<longleftrightarrow> arr t \<and> arr u"
      using arr_char ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S not_ide_null null_char resid_def by force

    sublocale extensional_rts resid
      using arr_char cong_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S
      by unfold_locales auto

    lemma is_extensional_rts:
    shows "extensional_rts resid"
      ..

    lemma src_char:
    shows "src t = (if t = the_arr then t else null)"
      using arr_char ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S src_def src_ide by presburger

    lemma prfx_char:
    shows "t \<lesssim>\<^sub>1 u \<longleftrightarrow> arr t \<and> arr u"
      by (metis cong_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S)

    lemma composite_of_char:
    shows "composite_of t u v \<longleftrightarrow> arr t \<and> arr u \<and> arr v"
      using composite_of_def
      by (metis composite_of_ide_self prfx_char)

    lemma composable_char:
    shows "composable t u \<longleftrightarrow> arr t \<and> arr u"
      using composable_def composite_of_char by auto

    lemma seq_char:
    shows "seq t u \<longleftrightarrow> arr t \<and> arr u"
      using arr_char composable_char composable_imp_seq by auto

    sublocale rts_with_composites resid
      by unfold_locales (simp add: composable_char seq_char)

    lemma is_rts_with_composites:
    shows "rts_with_composites resid"
      ..

    sublocale extensional_rts_with_composites resid ..

    lemma is_extensional_rts_with_composites:
    shows "extensional_rts_with_composites resid"
      ..

    sublocale small_rts resid
      by (simp add: Collect_cong arr_char rts_axioms small_rts.intro
          small_rts_axioms.intro)

    lemma is_small_rts:
    shows "small_rts resid"
      ..

    lemma comp_char:
    shows "comp t u = (if arr t \<and> arr u then the_arr else null)"
      using arr_char composable_iff_comp_not_null trg_char by auto

    text\<open>
      For an arbitrary RTS \<open>A\<close>, there is a unique simulation from \<open>A\<close> to the one-transition RTS.
    \<close>

    definition terminator :: "'a resid \<Rightarrow> 'a \<Rightarrow> 't"
    where "terminator A \<equiv> (\<lambda>t. if residuation.arr A t then the_arr else null)"

    lemma terminator_is_simulation:
    assumes "rts A"
    shows "simulation A resid (terminator A)"
    proof -
      interpret A: rts A
        using assms by blast
      show ?thesis
        unfolding terminator_def
        using assms ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S ideE A.con_implies_arr
        apply (unfold_locales)
          by auto metis
    qed

    lemma universality:
    assumes "rts A"
    shows "\<exists>!F. simulation A resid F"
    proof
      show "simulation A resid (terminator A)"
        using assms terminator_is_simulation by blast
      show "\<And>F. simulation A resid F \<Longrightarrow> F = terminator A"
        unfolding terminator_def
        by (meson arr_char simulation.extensional
            simulation.preserves_reflects_arr)
    qed

    text\<open>
      A ``global transition'' of an RTS \<open>A\<close> is a transformation from the one-arrow RTS
      to \<open>A\<close>.  An important fact is that equality of simulations and of transformations
      is determined by their compositions with global transitions.
    \<close>

    lemma eq_simulation_iff:
    assumes "weakly_extensional_rts A"
    and "simulation A B F" and "simulation A B G"
    shows "F = G \<longleftrightarrow>
           (\<forall>Q R T. transformation resid A Q R T \<longrightarrow> F \<circ> T = G \<circ> T)"
    proof
      interpret A: weakly_extensional_rts A
        using assms(1) simulation_def by blast
      interpret F: simulation A B F
        using assms(2) by blast
      interpret G: simulation A B G
        using assms(3) by blast
      show "F = G \<Longrightarrow>
              \<forall>Q R T. transformation resid A Q R T \<longrightarrow> F \<circ> T = G \<circ> T"
        by blast
      show "\<forall>Q R T. transformation resid A Q R T \<longrightarrow> F \<circ> T = G \<circ> T
                       \<Longrightarrow> F = G"
      proof -
        have "F \<noteq> G \<Longrightarrow>
                (\<exists>Q R T. transformation resid A Q R T \<and> F \<circ> T \<noteq> G \<circ> T)"
        proof -
          assume 1: "F \<noteq> G"
          obtain t where t: "A.arr t \<and> F t \<noteq> G t"
            using 1 F.extensional G.extensional by fastforce
          interpret T: constant_transformation resid A t
            using t by unfold_locales blast
          have "transformation resid A T.F T.G T.map"
            using T.transformation_axioms by simp
          moreover have "F \<circ> T.map \<noteq> G \<circ> T.map"
            by (metis (mono_tags, lifting) arr_char comp_apply t)
          ultimately show "\<exists>Q R T. transformation resid A Q R T \<and>
                                   F \<circ> T \<noteq> G \<circ> T"
            by blast
        qed
        thus "\<forall>Q R T. transformation resid A Q R T \<longrightarrow> F \<circ> T = G \<circ> T
                 \<Longrightarrow> F = G"
          by blast
      qed
    qed

    lemma eq_transformation_iff:
    assumes "weakly_extensional_rts A" and "weakly_extensional_rts B"
    and "transformation A B F G U" and "transformation A B F G V"
    shows "U = V \<longleftrightarrow>
           (\<forall>Q R T. transformation resid A Q R T \<longrightarrow> U \<circ> T = V \<circ> T)"
    proof
      interpret A: weakly_extensional_rts A
        using assms(1) simulation_def by blast
      interpret B: weakly_extensional_rts B
        using assms(2) simulation_def by blast
      interpret U: transformation A B F G U
        using assms(3) by blast
      interpret V: transformation A B F G V
        using assms(4) by blast
      show "U = V \<Longrightarrow>
              \<forall>Q R T. transformation resid A Q R T \<longrightarrow> U \<circ> T = V \<circ> T"
        by blast
      show "\<forall>Q R T. transformation resid A Q R T \<longrightarrow> U \<circ> T = V \<circ> T
                       \<Longrightarrow> U = V"
      proof -
        have "U \<noteq> V \<Longrightarrow>
                (\<exists>Q R T. transformation resid A Q R T \<and> U \<circ> T \<noteq> V \<circ> T)"
        proof -
          assume 1: "U \<noteq> V"
          obtain t where t: "A.arr t \<and> U t \<noteq> V t"
            using 1 U.extensional V.extensional by fastforce
          interpret T: constant_transformation resid A t
            using t by unfold_locales blast
          have "transformation resid A T.F T.G T.map"
            using T.transformation_axioms by simp
          moreover have "U \<circ> T.map \<noteq> V \<circ> T.map"
            by (metis (mono_tags, lifting) arr_char comp_apply t)
          ultimately show "\<exists>Q R T. transformation resid A Q R T \<and>
                                   U \<circ> T \<noteq> V \<circ> T"
            by blast
        qed
        thus "\<forall>Q R T. transformation resid A Q R T \<longrightarrow> U \<circ> T = V \<circ> T
                         \<Longrightarrow> U = V"
          by blast
      qed
    qed

  end

section "Sub-RTS"

  (*
   * TODO: There is already a sub-RTS construction in ResiduatedTransitionSystem.
   * These should be unified at some point.
   *)

  text\<open>
    A sub-RTS of an RTS \<open>R\<close> may be determined by specifying a subset of the transitions
    of \<open>R\<close> that is closed under residuation and in addition includes some common source
    for every consistent pair of transitions contained in it.
  \<close>

  locale sub_rts =
    R: rts R
  for R :: "'a resid"  (infix "\\\<^sub>R" 70)
  and Arr :: "'a \<Rightarrow> bool" +
  assumes inclusion: "Arr t \<Longrightarrow> R.arr t"
  and resid_closed: "\<lbrakk>Arr t; Arr u; R.con t u\<rbrakk> \<Longrightarrow> Arr (t \\\<^sub>R u)"
  and enough_sources: "\<lbrakk>Arr t; Arr u; R.con t u\<rbrakk> \<Longrightarrow>
                          \<exists>a. Arr a \<and> a \<in> R.sources t \<and> a \<in> R.sources u"
  begin

    definition resid :: "'a resid"  (infix "\\" 70)
    where "resid t u \<equiv> if Arr t \<and> Arr u \<and> R.con t u then t \\\<^sub>R u else R.null"

    sublocale ResiduatedTransitionSystem.partial_magma resid
      using R.not_con_null(2) R.null_is_zero(1) resid_def
      by unfold_locales metis

    lemma null_char:
    shows "null = R.null"
      by (metis R.not_arr_null inclusion null_eqI resid_def)

    sublocale residuation resid
      using R.conE R.con_sym R.not_con_null(1) null_is_zero(1) resid_def
      apply unfold_locales
        apply metis
       apply (metis R.con_def R.con_imp_arr_resid resid_closed)
      by (metis (no_types, lifting) R.con_def R.cube resid_closed)

    lemma arr_char:
    shows "arr t \<longleftrightarrow> Arr t"
      by (metis R.con_arr_self R.con_def R.not_arr_null arrE con_def inclusion
          null_is_zero(2) resid_def residuation.con_implies_arr(1) residuation_axioms)

    lemma ide_char:
    shows "ide t \<longleftrightarrow> Arr t \<and> R.ide t"
      by (metis R.ide_def arrI arr_char con_def ide_def not_arr_null resid_def)

    lemma con_char:
    shows "con t u \<longleftrightarrow> Arr t \<and> Arr u \<and> R.con t u"
      by (metis R.conE arr_char con_def not_arr_null null_is_zero(1) resid_def)

    lemma trg_char:
    shows "trg = (\<lambda>t. if arr t then R.trg t else null)"
      using arr_char trg_def R.trg_def resid_def by fastforce

    sublocale rts resid
      using arr_char ide_char con_char trg_char resid_def resid_closed inclusion
      apply unfold_locales
      using R.prfx_reflexive trg_def apply force
         apply (simp add: R.resid_arr_ide)
        apply simp
       apply (meson R.con_sym R.in_sourcesE enough_sources)
      by (metis (no_types, lifting) R.con_target arr_resid_iff_con con_sym_ax null_char)

    lemma prfx_char:
    shows "prfx t u \<longleftrightarrow> Arr t \<and> Arr u \<and> R.prfx t u"
      using arr_char con_char ide_char
      by (metis R.prfx_implies_con prfx_implies_con resid_closed resid_def)

    lemma cong_char:
    shows "cong t u \<longleftrightarrow> Arr t \<and> Arr u \<and> R.cong t u"
      using prfx_char by blast

    lemma composite_of_char:
    shows "composite_of t u v \<longleftrightarrow> Arr t \<and> Arr u \<and> Arr v \<and> R.composite_of t u v"
    proof
      show "composite_of t u v \<Longrightarrow> Arr t \<and> Arr u \<and> Arr v \<and> R.composite_of t u v"
        by (metis RTSConstructions.sub_rts.resid_def R.composite_of_def
            R.con_sym composite_ofE con_char prfx_char prfx_implies_con sub_rts_axioms)
      show "Arr t \<and> Arr u \<and> Arr v \<and> R.composite_of t u v \<Longrightarrow> composite_of t u v"
        by (metis (full_types) RTSConstructions.sub_rts.resid_def R.composite_of_def
            R.con_sym R.rts_axioms composite_ofI prfx_char resid_closed
            rts.prfx_implies_con sub_rts_axioms)
    qed

    lemma join_of_char:
    shows "join_of t u v \<longleftrightarrow> Arr t \<and> Arr u \<and> Arr v \<and> R.join_of t u v"
      using composite_of_char
      by (metis R.bounded_imp_con R.join_of_def join_of_def resid_closed resid_def)

    lemma preserves_weakly_extensional_rts:
    assumes "weakly_extensional_rts R"
    shows "weakly_extensional_rts resid"
      by (metis assms cong_char ide_char rts_axioms weakly_extensional_rts.intro
          weakly_extensional_rts.weak_extensionality weakly_extensional_rts_axioms.intro)

    lemma preserves_extensional_rts:
    assumes "extensional_rts R"
    shows "extensional_rts resid"
      by (meson assms extensional_rts.cong_char extensional_rts.intro
          extensional_rts_axioms.intro prfx_char rts_axioms)

  end

  locale sub_rts_of_weakly_extensional_rts =
    R: weakly_extensional_rts R +
    sub_rts R Arr
  for R :: "'a resid"  (infix "\\\<^sub>R" 70)
  and Arr :: "'a \<Rightarrow> bool"
  begin

    sublocale weakly_extensional_rts resid
      using R.weakly_extensional_rts_axioms preserves_weakly_extensional_rts
      by blast

    lemma src_char:
    shows "src = (\<lambda>t. if arr t then R.src t else null)"
    proof
      fix t
      show "src t = (if arr t then R.src t else null)"
        by (metis R.src_eqI con_arr_src(2) con_char ide_char ide_src src_def)
    qed

    lemma targets_char:
    assumes "arr t"
    shows "targets t = {R.trg t}"
      using assms trg_char trg_in_targets arr_has_un_target by auto

  end

  locale sub_rts_of_extensional_rts =
    R: extensional_rts R +
    sub_rts R Arr
  for R :: "'a resid"  (infix "\\\<^sub>R" 70)
  and Arr :: "'a \<Rightarrow> bool"
  begin

    sublocale sub_rts_of_weakly_extensional_rts ..

    sublocale extensional_rts resid
      using R.extensional_rts_axioms preserves_extensional_rts
      by blast

  end

section "Fibered Product RTS"

  locale fibered_product_rts =
  A: rts A +
  B: rts B +
  C: weakly_extensional_rts C +
  F: simulation A C F +
  G: simulation B C G
  for A :: "'a resid"  (infix "\\\<^sub>A" 70)
  and B :: "'b resid"  (infix "\\\<^sub>B" 70)
  and C :: "'c resid"  (infix "\\\<^sub>C" 70)
  and F :: "'a \<Rightarrow> 'c"
  and G :: "'b \<Rightarrow> 'c"
  begin

    notation A.con   (infix "\<frown>\<^sub>A" 50)
    notation B.con   (infix "\<frown>\<^sub>B" 50)
    notation C.con   (infix "\<frown>\<^sub>C" 50)
    notation A.prfx  (infix "\<lesssim>\<^sub>A" 50)
    notation B.prfx  (infix "\<lesssim>\<^sub>B" 50)
    notation C.prfx  (infix "\<lesssim>\<^sub>C" 50)
    notation A.cong  (infix "\<sim>\<^sub>A" 50)
    notation B.cong  (infix "\<sim>\<^sub>B" 50)
    notation C.cong  (infix "\<sim>\<^sub>C" 50)

    abbreviation Arr
    where "Arr \<equiv> \<lambda>tu. A.arr (fst tu) \<and> B.arr (snd tu) \<and> F (fst tu) = G (snd tu)"

    abbreviation Ide
    where "Ide \<equiv> \<lambda>tu. A.ide (fst tu) \<and> B.ide (snd tu) \<and> F (fst tu) = G (snd tu)"

    abbreviation Con
    where "Con \<equiv> \<lambda>tu vw. fst tu \<frown>\<^sub>A fst vw \<and> snd tu \<frown>\<^sub>B snd vw \<and>
                          F (fst tu) = G (snd tu) \<and> F (fst vw) = G (snd vw)"

    definition resid :: "('a * 'b) resid" (infix "\\" 70)
    where "tu \\ vw =
           (if Con tu vw then (fst tu \\\<^sub>A fst vw, snd tu \\\<^sub>B snd vw)
            else (A.null, B.null))"

    sublocale ResiduatedTransitionSystem.partial_magma resid
      using resid_def
      by unfold_locales
         (metis B.arr_resid_iff_con B.ex_un_null B.not_arr_null
           B.null_is_zero(2) snd_conv)

    lemma null_char:
    shows "null = (A.null, B.null)"
      unfolding null_def
      using ex_un_null resid_def
            the1_equality [of "\<lambda>n. \<forall>f. n \\ f = n \<and> f \\ n = n" "(A.null, B.null)"]
      by simp

    sublocale residuation resid
    proof
      show "\<And>t u. t \\ u \<noteq> null \<Longrightarrow> u \\ t \<noteq> null"
        by (metis A.con_sym B.con_sym B.residuation_axioms null_char prod.inject
            resid_def residuation.con_def)
      show "\<And>t u. t \\ u \<noteq> null \<Longrightarrow> (t \\ u) \\ (t \\ u) \<noteq> null"
        by (metis (no_types, lifting) A.conE A.conI A.con_imp_arr_resid B.con_def
            B.con_imp_arr_resid F.preserves_resid G.preserves_resid fst_conv null_char
            resid_def snd_conv)
      show "\<And>v t u. (v \\ t) \\ (u \\ t) \<noteq> null \<Longrightarrow> (v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
      proof -
        fix v t u
        assume 1: "(v \\ t) \\ (u \\ t) \<noteq> null"
        have 2: "(v \\ t) \\ (u \\ t) =
                 ((fst v \\\<^sub>A fst t) \\\<^sub>A (fst u \\\<^sub>A fst t),
                  (snd v \\\<^sub>B snd t) \\\<^sub>B (snd u \\\<^sub>B snd t))"
          using 1 resid_def null_char by auto
        also have "... = ((fst v \\\<^sub>A fst u) \\\<^sub>A (fst t \\\<^sub>A fst u),
                          (snd v \\\<^sub>B snd u) \\\<^sub>B (snd t \\\<^sub>B snd u))"
          using A.cube B.cube by simp
        also have "... = (v \\ u) \\ (t \\ u)"
        proof -
          have "Con (v \\ u) (t \\ u)"
          proof -
            have "fst v \\\<^sub>A fst u \<frown>\<^sub>A fst t \\\<^sub>A fst u"
              using 1 2 A.cube
              by (metis (no_types, lifting) A.con_def fst_conv null_char resid_def)
            moreover have "snd v \\\<^sub>B snd u \<frown>\<^sub>B snd t \\\<^sub>B snd u"
              using 1 2 B.cube
              by (metis (no_types, lifting) B.con_def null_char resid_def snd_conv)
            ultimately show ?thesis
              using 1 resid_def
              by (metis (no_types, lifting) A.conI A.con_implies_arr(1) A.not_arr_null
                  A.not_con_null(2) B.conI B.con_implies_arr(1) B.not_arr_null
                  B.not_con_null(2) F.preserves_resid G.preserves_resid fst_eqD
                  null_char snd_eqD)
          qed
          thus ?thesis
            using resid_def null_char by auto
        qed
        finally show "(v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
          by blast
      qed
    qed

    notation con  (infix "\<frown>" 50)

    lemma arr_char:
    shows "arr t \<longleftrightarrow> Arr t"
      by (metis B.arr_def B.conE Pair_inject conE conI null_char resid_def
          A.arr_def arr_def)

    lemma con_char:
    shows "t \<frown> u \<longleftrightarrow> Con t u"
      by (metis B.conE null_char resid_def con_def snd_conv)

    lemma ide_char\<^sub>F\<^sub>P:
    shows "ide t \<longleftrightarrow> Ide t"
      unfolding ide_def
      using con_char resid_def
      by (metis (no_types, lifting) A.ide_def fst_conv prod.exhaust_sel
          B.ide_def snd_conv)

    lemma trg_char:
    shows "trg t = (if arr t then (A.trg (fst t), B.trg (snd t)) else null)"
      by (simp add: A.trg_def B.trg_def con_char null_char resid_def
          arr_def trg_def)

    sublocale rts resid
    proof
      show "\<And>t. arr t \<Longrightarrow> ide (trg t)"
        using trg_char ide_char\<^sub>F\<^sub>P arr_char F.preserves_trg G.preserves_trg
        apply simp
        using F.preserves_trg G.preserves_trg by metis
      show 1: "\<And>a t. \<lbrakk>ide a; t \<frown> a\<rbrakk> \<Longrightarrow> t \\ a = t"
        by (simp add: A.resid_arr_ide B.resid_arr_ide con_char ide_char\<^sub>F\<^sub>P
            resid_def)
      show "\<And>a t. \<lbrakk>ide a; a \<frown> t\<rbrakk> \<Longrightarrow> ide (a \\ t)"
        by (metis 1 arr_resid_iff_con con_sym cube ide_def)
      show "\<And>t u. t \<frown> u \<Longrightarrow> \<exists>a. ide a \<and> a \<frown> t \<and> a \<frown> u"
      proof -
        fix t u
        assume con: "t \<frown> u"
        obtain a where a: "A.ide a \<and> a \<frown>\<^sub>A fst t \<and> a \<frown>\<^sub>A fst u"
          using con con_char A.con_imp_coinitial_ax by fastforce
        obtain b where b: "B.ide b \<and> b \<frown>\<^sub>B snd t \<and> b \<frown>\<^sub>B snd u"
          using con con_char B.con_imp_coinitial_ax by fastforce
        have "F a = G b"
          by (metis C.src_eqI F.preserves_con F.preserves_ide G.preserves_con
              G.preserves_ide a b con con_char)
        thus "\<exists>a. ide a \<and> a \<frown> t \<and> a \<frown> u"
          using a b ide_char\<^sub>F\<^sub>P con con_char by auto
      qed
      show "\<And>t u v. \<lbrakk>ide (t \\ u); u \<frown> v\<rbrakk> \<Longrightarrow> t \\ u \<frown> v \\ u"
        by (metis (no_types, lifting) A.con_target B.con_target arr_char
            arr_resid_iff_con con_char con_sym fst_conv ide_char\<^sub>F\<^sub>P
            ide_implies_arr resid_def snd_conv)
    qed

    notation prfx  (infix "\<lesssim>" 50)
    notation cong  (infix "\<sim>" 50)

    lemma prfx_char:
    shows "t \<lesssim> u \<longleftrightarrow> F (fst t) = G (snd t) \<and> F (fst u) = G (snd u) \<and>
                     fst t \<lesssim>\<^sub>A fst u \<and> snd t \<lesssim>\<^sub>B snd u"
      using A.prfx_implies_con B.prfx_implies_con ide_char\<^sub>F\<^sub>P resid_def
      by auto

    lemma cong_char\<^sub>F\<^sub>P:
    shows "t \<sim> u \<longleftrightarrow> F (fst t) = G (snd t) \<and> F (fst u) = G (snd u) \<and>
                     fst t \<sim>\<^sub>A fst u \<and> snd t \<sim>\<^sub>B snd u"
      using prfx_char by auto

    lemma sources_char:
    shows "sources t =
           {a. F (fst t) = G (snd t) \<and> F (fst a) = G (snd a) \<and>
               fst a \<in> A.sources (fst t) \<and> snd a \<in> B.sources (snd t)}"
      using con_char ide_char\<^sub>F\<^sub>P sources_def by auto

    lemma targets_char\<^sub>F\<^sub>P:
    shows "targets t =
           {a. F (fst t) = G (snd t) \<and> F (fst a) = G (snd a) \<and>
               fst a \<in> A.targets (fst t) \<and> snd a \<in> B.targets (snd t)}"
    proof
      show "targets t \<subseteq> {a. F (fst t) = G (snd t) \<and> F (fst a) = G (snd a) \<and>
                            fst a \<in> A.targets (fst t) \<and> snd a \<in> B.targets (snd t)}"
        using arr_char arr_iff_has_target ide_char\<^sub>F\<^sub>P
        apply auto[1]
          apply (metis arr_char arr_composite_of composite_of_arr_ide in_targetsE
            trg_def)
         apply (metis A.in_targetsI con_char con_implies_arr(1) fst_conv
            in_targetsE not_arr_null trg_char)
        by (metis B.in_targetsI con_char con_implies_arr(1) in_targetsE
            not_arr_null snd_conv trg_char)
      show "{a. F (fst t) = G (snd t) \<and> F (fst a) = G (snd a) \<and>
                fst a \<in> A.targets (fst t) \<and> snd a \<in> B.targets (snd t)} \<subseteq> targets t"
        using A.arr_iff_has_target B.arr_iff_has_target arr_char con_char
          ide_char\<^sub>F\<^sub>P ide_trg targets_def trg_char
        by auto
    qed

    definition P\<^sub>0 :: "'a \<times> 'b \<Rightarrow> 'b"
    where "P\<^sub>0 t \<equiv> if arr t then snd t else B.null"

    definition P\<^sub>1 :: "'a \<times> 'b \<Rightarrow> 'a"
    where "P\<^sub>1 t \<equiv> if arr t then fst t else A.null"

    sublocale P\<^sub>0: simulation resid B P\<^sub>0
      using P\<^sub>0_def con_char resid_def arr_resid con_implies_arr(1-2)
      by unfold_locales auto

    lemma P\<^sub>0_is_simulation:
    shows "simulation resid B P\<^sub>0"
      ..

    sublocale P\<^sub>1: simulation resid A P\<^sub>1
      using P\<^sub>1_def con_char resid_def arr_resid con_implies_arr(1-2)
      by unfold_locales auto

    lemma P\<^sub>1_is_simulation:
    shows "simulation resid A P\<^sub>1"
      ..

    lemma commutativity:
    shows "F o P\<^sub>1 = G o P\<^sub>0"
      using F.extensional G.extensional P\<^sub>1_def P\<^sub>0_def arr_char by auto

    definition tuple :: "'x resid \<Rightarrow> ('x \<Rightarrow> 'a) \<Rightarrow> ('x \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'a \<times> 'b"
    where "tuple X H K \<equiv> \<lambda>t. if residuation.arr X t then (H t, K t) else null"

    lemma universality:
    assumes "rts X" and "simulation X A H" and "simulation X B K"
    and "F o H = G o K"
    shows [intro]: "simulation X resid (tuple X H K)"
    and "P\<^sub>1 \<circ> tuple X H K = H" and "P\<^sub>0 \<circ> tuple X H K = K"
    and "\<exists>!HK. simulation X resid HK \<and> P\<^sub>1 o HK = H \<and> P\<^sub>0 o HK = K"
    proof -
      interpret X: rts X
        using assms(1) by blast
      interpret H: simulation X A H
        using assms(2) by blast
      interpret K: simulation X B K
        using assms(3) by blast
      let ?HK = "tuple X H K"
      interpret HK: simulation X resid ?HK
      proof
        show "\<And>t. \<not> X.arr t \<Longrightarrow> ?HK t = null"
          unfolding tuple_def by simp
        fix t u
        assume con: "X.con t u"
        have 1: "X.arr t \<and> X.arr u"
          using con X.con_implies_arr(1) X.con_implies_arr(2) by force
        show 2: "con (?HK t) (?HK u)"
          by (metis 1 assms(4) comp_apply con con_char fst_conv tuple_def
              H.preserves_con K.preserves_con snd_conv)
        show "?HK (X t u) = resid (?HK t) (?HK u)"
          using 1 2 con resid_def null_char con_char arr_char
          by (simp add: tuple_def)
      qed
      show "simulation X resid (tuple X H K)"
        ..
      show "P\<^sub>1 \<circ> ?HK = H"
      proof
        fix t
        show "(P\<^sub>1 \<circ> ?HK) t = H t"
          using P\<^sub>1_def HK.preserves_reflects_arr
          by (simp add: H.extensional tuple_def)
      qed
      moreover show "P\<^sub>0 \<circ> ?HK = K"
      proof
        fix t
        show "(P\<^sub>0 \<circ> ?HK) t = K t"
          using P\<^sub>0_def HK.preserves_reflects_arr
          by (simp add: K.extensional tuple_def)
      qed
      ultimately
      have "simulation X resid ?HK \<and> P\<^sub>1 \<circ> ?HK = H \<and> P\<^sub>0 \<circ> ?HK = K"
        using HK.simulation_axioms by simp
      moreover have "\<And>M. simulation X resid M \<and> P\<^sub>1 \<circ> M = H \<and> P\<^sub>0 \<circ> M = K
                            \<Longrightarrow> M = ?HK"
        unfolding P\<^sub>1_def P\<^sub>0_def tuple_def
        using simulation.extensional simulation.preserves_reflects_arr
        by fastforce
      ultimately show "\<exists>!HK. simulation X resid HK \<and>
                             P\<^sub>1 o HK = H \<and> P\<^sub>0 o HK = K"
        by auto
    qed

    (* TODO: Show the corresponding universality property for transformations. *)

    lemma preserves_weakly_extensional_rts:
    assumes "weakly_extensional_rts A" and "weakly_extensional_rts B"
    shows "weakly_extensional_rts resid"
      using assms
      by unfold_locales
         (metis con_char ide_char\<^sub>F\<^sub>P prod.exhaust_sel prfx_implies_con
                weakly_extensional_rts.con_ide_are_eq)

    lemma preserves_extensional_rts:
    assumes "extensional_rts A" and "extensional_rts B"
    shows "extensional_rts resid"
      using assms
      by unfold_locales
         (metis (no_types, lifting) extensional_rts.extensional fst_conv ide_char\<^sub>F\<^sub>P
          ide_implies_arr not_arr_null null_char prod.exhaust_sel resid_def snd_conv)

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

  locale fibered_product_of_weakly_extensional_rts =
    A: weakly_extensional_rts A +
    B: weakly_extensional_rts B +
    fibered_product_rts
  begin

    sublocale weakly_extensional_rts resid
      using A.weakly_extensional_rts_axioms B.weakly_extensional_rts_axioms
            preserves_weakly_extensional_rts
      by auto

    lemma is_weakly_extensional_rts:
    shows "weakly_extensional_rts resid"
      ..

    lemma src_char:
    shows "src t = (if arr t then (A.src (fst t), B.src (snd t)) else null)"
    proof (cases "arr t")
      show "\<not> arr t \<Longrightarrow> ?thesis"
        using src_def by presburger
      assume t: "arr t"
      show ?thesis
      proof (intro src_eqI)
        show "ide (if arr t then (A.src (fst t), B.src (snd t)) else null)"
          using t ide_char\<^sub>F\<^sub>P
          by simp (metis A.src_eqI B.src_eqI con_arr_src(2) con_char ide_src)
        show "(if arr t then (A.src (fst t), B.src (snd t)) else null) \<frown> t"
          using t con_char arr_char
          by simp
             (metis A.arr_def A.src_eqI B.arr_def B.src_eqI
                    con_imp_coinitial_ax ide_char\<^sub>F\<^sub>P)
      qed
    qed

  end

  locale fibered_product_of_extensional_rts =
    A: extensional_rts A +
    B: extensional_rts B +
    fibered_product_of_weakly_extensional_rts
  begin

    sublocale fibered_product_of_weakly_extensional_rts A B ..
    sublocale extensional_rts resid
      using A.extensional_rts_axioms B.extensional_rts_axioms preserves_extensional_rts
      by blast

    lemma is_extensional_rts:
    shows "extensional_rts resid"
      ..

  end

  locale fibered_product_of_small_rts =
    A: small_rts A +
    B: small_rts B +
    fibered_product_rts
  begin

    sublocale small_rts resid
      by (simp add: A.small_rts_axioms B.small_rts_axioms preserves_small_rts)

    lemma is_small_rts:
    shows "small_rts resid"
      ..

  end

section "Product RTS"

  text\<open>
    It is possible to define a product construction for RTS's as a special case of the
    fibered product, but some inconveniences result from that approach.
    In addition, we have already defined a product construction in
    @{theory ResiduatedTransitionSystem.ResiduatedTransitionSystem}.
    So, we will build on that existing construction.
  \<close>

  definition pointwise_tuple :: "('x \<Rightarrow> 'a) \<Rightarrow> ('x \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'a \<times> 'b"  ("\<langle>\<langle>_, _\<rangle>\<rangle>")
  where "pointwise_tuple H K \<equiv> (\<lambda>t. (H t, K t))"

  context product_rts
  begin

    definition P\<^sub>0 :: "'a \<times> 'b \<Rightarrow> 'b"
    where "P\<^sub>0 t \<equiv> if arr t then snd t else B.null"

    definition P\<^sub>1 :: "'a \<times> 'b \<Rightarrow> 'a"
    where "P\<^sub>1 t \<equiv> if arr t then fst t else A.null"

    sublocale P\<^sub>0: simulation resid B P\<^sub>0
      using P\<^sub>0_def con_char resid_def arr_resid con_implies_arr(1-2)
      by unfold_locales auto

    lemma P\<^sub>0_is_simulation:
    shows "simulation resid B P\<^sub>0"
      ..

    sublocale P\<^sub>1: simulation resid A P\<^sub>1
      using P\<^sub>1_def con_char resid_def arr_resid con_implies_arr(1-2)
      by unfold_locales auto

    lemma P\<^sub>1_is_simulation:
    shows "simulation resid A P\<^sub>1"
      ..

    abbreviation tuple :: "('x \<Rightarrow> 'a) \<Rightarrow> ('x \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'a \<times> 'b"
    where "tuple \<equiv> pointwise_tuple"

    lemma universality:
    assumes "simulation X A H" and "simulation X B K"
    shows [intro]: "simulation X resid \<langle>\<langle>H, K\<rangle>\<rangle>"
    and "P\<^sub>1 \<circ> \<langle>\<langle>H, K\<rangle>\<rangle> = H" and "P\<^sub>0 \<circ> \<langle>\<langle>H, K\<rangle>\<rangle> = K"
    and "\<exists>!HK. simulation X resid HK \<and> P\<^sub>1 o HK = H \<and> P\<^sub>0 o HK = K"
    proof -
      interpret H: simulation X A H
        using assms(1) by blast
      interpret K: simulation X B K
        using assms(2) by blast
      interpret HK: simulation X resid \<open>\<langle>\<langle>H, K\<rangle>\<rangle>\<close>
      proof
        show "\<And>t. \<not> H.A.arr t \<Longrightarrow> \<langle>\<langle>H, K\<rangle>\<rangle> t = null"
          by (simp add: H.extensional K.extensional pointwise_tuple_def)
        fix t u
        assume con: "H.A.con t u"
        have 1: "H.A.arr t \<and> H.A.arr u"
          using con H.A.con_implies_arr(1-2) by force
        show "con (\<langle>\<langle>H, K\<rangle>\<rangle> t) (\<langle>\<langle>H, K\<rangle>\<rangle> u)"
          using 1 con con_char H.preserves_con K.preserves_con pointwise_tuple_def
          by (metis fst_conv snd_conv)
        thus "\<langle>\<langle>H, K\<rangle>\<rangle> (X t u) = resid (\<langle>\<langle>H, K\<rangle>\<rangle> t) (\<langle>\<langle>H, K\<rangle>\<rangle> u)"
          unfolding pointwise_tuple_def
          using 1 con resid_def null_char con_char arr_char
          by simp
      qed
      show "simulation X resid \<langle>\<langle>H, K\<rangle>\<rangle>" ..
      show "P\<^sub>1 \<circ> \<langle>\<langle>H, K\<rangle>\<rangle> = H"
        unfolding pointwise_tuple_def
        using P\<^sub>1_def HK.preserves_reflects_arr 
        by (auto simp add: H.extensional)
      moreover show "P\<^sub>0 \<circ> \<langle>\<langle>H, K\<rangle>\<rangle> = K"
        unfolding pointwise_tuple_def
        using P\<^sub>0_def HK.preserves_reflects_arr
        by (auto simp add: K.extensional)
      ultimately have "simulation X resid \<langle>\<langle>H, K\<rangle>\<rangle> \<and>
                         P\<^sub>1 \<circ> \<langle>\<langle>H, K\<rangle>\<rangle> = H \<and> P\<^sub>0 \<circ> \<langle>\<langle>H, K\<rangle>\<rangle> = K"
        using HK.simulation_axioms by simp
      moreover have "\<And>M. simulation X resid M \<and> P\<^sub>1 \<circ> M = H \<and> P\<^sub>0 \<circ> M = K
                            \<Longrightarrow> M = \<langle>\<langle>H, K\<rangle>\<rangle>"
      proof
        fix M t
        assume 1: "simulation X resid M \<and> P\<^sub>1 \<circ> M = H \<and> P\<^sub>0 \<circ> M = K"
        interpret M: simulation X resid M
          using 1 by blast
        show "M t = \<langle>\<langle>H, K\<rangle>\<rangle> t"
          using 1 M.extensional M.preserves_reflects_arr
          unfolding P\<^sub>1_def P\<^sub>0_def pointwise_tuple_def
          by force
      qed
      ultimately
      show "\<exists>!HK. simulation X resid HK \<and> P\<^sub>1 o HK = H \<and> P\<^sub>0 o HK = K"
        by auto
    qed

    lemma proj_joint_monic:
    assumes "simulation X resid F" and "simulation X resid G"
    and "P\<^sub>0 \<circ> F = P\<^sub>0 \<circ> G" and "P\<^sub>1 \<circ> F = P\<^sub>1 \<circ> G"
    shows "F = G"
      using assms(1-4) P\<^sub>0_is_simulation P\<^sub>1_is_simulation universality(4)
      by blast

    lemma tuple_proj:
    assumes "simulation X resid F"
    shows "\<langle>\<langle>P\<^sub>1 \<circ> F, P\<^sub>0 \<circ> F\<rangle>\<rangle> = F"
      by (meson P\<^sub>0_is_simulation P\<^sub>1_is_simulation proj_joint_monic assms
          universality(1-3) simulation_comp)

    lemma proj_tuple:
    assumes "simulation X A F" and "simulation X B G"
    shows "P\<^sub>1 \<circ> \<langle>\<langle>F, G\<rangle>\<rangle> = F" and "P\<^sub>0 \<circ> \<langle>\<langle>F, G\<rangle>\<rangle> = G"
      using assms(1-2) universality(2-3) by auto

    lemma preserves_weakly_extensional_rts:
    assumes "weakly_extensional_rts A" and "weakly_extensional_rts B"
    shows "weakly_extensional_rts resid"
      by (metis assms(1-2) ide_char prfx_char prod.exhaust_sel rts_axioms
          weakly_extensional_rts.intro weakly_extensional_rts.weak_extensionality
          weakly_extensional_rts_axioms.intro)

    lemma preserves_extensional_rts:
    assumes "extensional_rts A" and "extensional_rts B"
    shows "extensional_rts resid"
    proof -
      interpret A: extensional_rts A
        using assms(1) by blast
      interpret B: extensional_rts B
        using assms(2) by blast
      show ?thesis
        by unfold_locales
           (metis A.extensional B.extensional cong_char prod.collapse)
    qed

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
        (* It is slightly shorter to use what has already been shown for fibered product. *)
        interpret One: one_arr_rts \<open>TYPE(bool)\<close>
          by unfold_locales auto
        interpret simulation A One.resid \<open>One.terminator A\<close>
          using One.terminator_is_simulation A.rts_axioms by blast
        interpret simulation B One.resid \<open>One.terminator B\<close>
          using One.terminator_is_simulation B.rts_axioms by blast
        interpret AxB: fibered_product_of_small_rts A B One.resid
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

  locale product_of_extensional_rts =
    A: extensional_rts A +
    B: extensional_rts B +
    product_rts
  begin

    sublocale product_of_weakly_extensional_rts A B ..

    sublocale extensional_rts resid
      using A.extensional_rts_axioms B.extensional_rts_axioms preserves_extensional_rts
      by blast

    lemma is_extensional_rts:
    shows "extensional_rts resid"
      ..

    lemma proj_tuple2:
    assumes "transformation X A F G S" and "transformation X B H K T"
    shows "P\<^sub>1 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle> = S" and "P\<^sub>0 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle> = T"
    proof -
      interpret S: transformation X A F G S
        using assms(1) by blast
      interpret T: transformation X B H K T
        using assms(2) by blast
      show "P\<^sub>1 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle> = S"
      proof
        fix t
        show "(P\<^sub>1 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle>) t = S t"
          unfolding pointwise_tuple_def P\<^sub>1_def
          using S.extensional S.preserves_arr T.preserves_arr
          apply auto[1]
          by metis+
      qed
      show "P\<^sub>0 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle> = T"
      proof
        fix t
        show "(P\<^sub>0 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle>) t = T t"
          unfolding pointwise_tuple_def P\<^sub>0_def
          using T.extensional S.preserves_arr T.preserves_arr
          apply auto[1]
          by metis+
      qed
    qed

    lemma universality2:
    assumes "simulation X resid F" and "simulation X resid G"
    and "transformation X A (P\<^sub>1 \<circ> F) (P\<^sub>1 \<circ> G) S"
    and "transformation X B (P\<^sub>0 \<circ> F) (P\<^sub>0 \<circ> G) T"
    shows [intro]: "transformation X resid F G \<langle>\<langle>S, T\<rangle>\<rangle>"
    and "P\<^sub>1 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle> = S" and "P\<^sub>0 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle> = T"
    and "\<exists>!ST. transformation X resid F G ST \<and> P\<^sub>1 o ST = S \<and> P\<^sub>0 o ST = T"
    proof -
      interpret X: rts X
        using assms(1) simulation_def by auto
      interpret A: weakly_extensional_rts A
        using assms(3) transformation_def by blast
      interpret B: weakly_extensional_rts B
        using assms(4) transformation_def by blast
      interpret X: weakly_extensional_rts X
        using assms(4) transformation_def by blast
      interpret F: simulation X resid F
        using assms(1) by blast
      interpret F: simulation_to_weakly_extensional_rts X resid F ..
      interpret G: simulation X resid G
        using assms(2) by blast
      interpret G: simulation_to_weakly_extensional_rts X resid G ..
      interpret P\<^sub>1oF: composite_simulation X resid A F P\<^sub>1 ..
      interpret P\<^sub>1oF: simulation_to_weakly_extensional_rts X A P\<^sub>1oF.map ..
      interpret P\<^sub>1oG: composite_simulation X resid A G P\<^sub>1 ..
      interpret P\<^sub>1oG: simulation_to_weakly_extensional_rts X A P\<^sub>1oF.map ..
      interpret P\<^sub>0oF: composite_simulation X resid B F P\<^sub>0 ..
      interpret P\<^sub>0oF: simulation_to_weakly_extensional_rts X A P\<^sub>1oF.map ..
      interpret P\<^sub>0oG: composite_simulation X resid B G P\<^sub>0 ..
      interpret P\<^sub>0oF: simulation_to_weakly_extensional_rts X A P\<^sub>1oF.map ..
      interpret S: transformation X A \<open>P\<^sub>1 \<circ> F\<close> \<open>P\<^sub>1 \<circ> G\<close> S
        using assms(3) by blast
      interpret S: transformation_to_extensional_rts X A \<open>P\<^sub>1 \<circ> F\<close> \<open>P\<^sub>1 \<circ> G\<close> S ..
      interpret T: transformation X B \<open>P\<^sub>0 \<circ> F\<close> \<open>P\<^sub>0 \<circ> G\<close> T
        using assms(4) by blast
      interpret T: transformation_to_extensional_rts X B \<open>P\<^sub>0 \<circ> F\<close> \<open>P\<^sub>0 \<circ> G\<close> T ..
      interpret ST: transformation X resid F G \<open>\<langle>\<langle>S, T\<rangle>\<rangle>\<close>
      proof
        show "\<And>t. \<not> X.arr t \<Longrightarrow> \<langle>\<langle>S, T\<rangle>\<rangle> t = null"
          by (simp add: S.extensional T.extensional pointwise_tuple_def)
        fix t
        assume t: "X.ide t"
        have arr: "arr (\<langle>\<langle>S, T\<rangle>\<rangle> t)"
          unfolding pointwise_tuple_def
          using t S.preserves_arr T.preserves_arr by auto
        show "src (\<langle>\<langle>S, T\<rangle>\<rangle> t) = F t"
        proof -
          have "F t = ((P\<^sub>1 \<circ> F) t, (P\<^sub>0 \<circ> F) t)"
            using t tuple_proj F.simulation_axioms pointwise_tuple_def
            by metis
          thus ?thesis
            using arr src_char arr_char
            by (simp add: S.preserves_src T.preserves_src t pointwise_tuple_def)
        qed
        show "trg (\<langle>\<langle>S, T\<rangle>\<rangle> t) = G t"
        proof -
          have "G t = ((P\<^sub>1 \<circ> G) t, (P\<^sub>0 \<circ> G) t)"
            using t tuple_proj G.simulation_axioms pointwise_tuple_def
            by metis
          thus ?thesis
            using arr trg_char arr_char
            by (simp add: S.preserves_trg T.preserves_trg t pointwise_tuple_def)
        qed
        next
        fix t
        assume t: "X.arr t"
        have con1: "S (X.src t) \<frown>\<^sub>A P\<^sub>1 (F t)"
        proof -
          have "S t = A.join (S (X.src t)) (P\<^sub>1 (F t))"
            using t S.naturality3'\<^sub>E by auto
          hence "A.prfx (S (X.src t)) (S t) \<and> A.prfx (P\<^sub>1 (F t)) (S t)"
            using t A.join_sym A.arr_prfx_join_self S.preserves_arr
                  A.joinable_iff_arr_join
            by metis
          thus ?thesis
            using t S.preserves_arr A.con_arr_self A.con_prfx(1-2) by blast
        qed
        moreover have con0: "T (X.src t) \<frown>\<^sub>B P\<^sub>0 (F t)"
        proof -
          have "T t = B.join (T (X.src t)) (P\<^sub>0 (F t))"
            using t T.naturality3'\<^sub>E by auto
          hence "B.prfx (T (X.src t)) (T t) \<and> B.prfx (P\<^sub>0 (F t)) (T t)"
            using t B.join_sym B.arr_prfx_join_self T.preserves_arr
                  B.joinable_iff_arr_join
            by metis
          thus ?thesis
            using t T.preserves_arr B.con_arr_self B.con_prfx(1-2) by blast
        qed
        show "\<langle>\<langle>S, T\<rangle>\<rangle> (X.src t) \\ F t = \<langle>\<langle>S, T\<rangle>\<rangle> (X.trg t)"
        proof -
          have "\<langle>\<langle>S, T\<rangle>\<rangle> (X.src t) \\ F t =
                (S (X.src t), T (X.src t)) \\ (P\<^sub>1 (F t), P\<^sub>0 (F t))"
            using t tuple_proj [of X F] F.simulation_axioms
                  pointwise_tuple_def [of S T]
                  pointwise_tuple_def [of P\<^sub>1oF.map P\<^sub>0oF.map]
            apply auto[1]
            by metis
          also have "... = (S (X.src t) \\\<^sub>A P\<^sub>1 (F t), T (X.src t) \\\<^sub>B P\<^sub>0 (F t))"
            using t con0 con1 resid_def by auto
          also have "... = (S (X.trg t), T (X.trg t))"
            using t S.naturality1 T.naturality1 by auto
          also have "... = \<langle>\<langle>S, T\<rangle>\<rangle> (X.trg t)"
            using t pointwise_tuple_def by metis
          finally show ?thesis by blast
        qed
        show "F t \\ \<langle>\<langle>S, T\<rangle>\<rangle> (X.src t) = G t"   
        proof -
          have "F t \\ \<langle>\<langle>S, T\<rangle>\<rangle> (X.src t) =
                (P\<^sub>1 (F t), P\<^sub>0 (F t)) \\ (S (X.src t), T (X.src t))"
            using t tuple_proj [of X F] F.simulation_axioms
                  pointwise_tuple_def [of S T]
                  pointwise_tuple_def [of P\<^sub>1oF.map P\<^sub>0oF.map]
            apply auto[1]
            by metis
          also have "... = (P\<^sub>1 (F t) \\\<^sub>A S (X.src t), P\<^sub>0 (F t) \\\<^sub>B T (X.src t))"
            using t con0 con1 resid_def A.con_sym B.con_sym by auto
          also have "... = (P\<^sub>1oG.map t, P\<^sub>0oG.map t)"
            using t S.naturality2 T.naturality2 by auto
          also have "... = G t"
            using t tuple_proj G.simulation_axioms pointwise_tuple_def by metis
          finally show ?thesis by blast
        qed
        show "join_of (\<langle>\<langle>S, T\<rangle>\<rangle> (X.src t)) (F t) (\<langle>\<langle>S, T\<rangle>\<rangle> t)"
        proof -
          have "A.join_of (S (X.src t)) (P\<^sub>1oF.map t) (S t)"
            using t con1 S.naturality3 [of t] by blast
          moreover have "B.join_of (T (X.src t)) (P\<^sub>0oF.map t) (T t)"
            using t con0 T.naturality3 [of t] by blast
          ultimately show ?thesis
            unfolding pointwise_tuple_def
            using t join_of_char(1-2) F.preserves_reflects_arr P\<^sub>0_def P\<^sub>1_def
            by auto
        qed
      qed
      show 1: "transformation X (\\) F G \<langle>\<langle>S, T\<rangle>\<rangle>" ..
      show 2: "P\<^sub>1 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle> = S" and 3: "P\<^sub>0 \<circ> \<langle>\<langle>S, T\<rangle>\<rangle> = T"
        using proj_tuple2 S.transformation_axioms T.transformation_axioms
        by blast+
      show "\<exists>!ST. transformation X (\\) F G ST \<and> P\<^sub>1 \<circ> ST = S \<and> P\<^sub>0 \<circ> ST = T"
      proof -
        have "\<And>ST. \<lbrakk>transformation X (\\) F G ST; P\<^sub>1 \<circ> ST = S; P\<^sub>0 \<circ> ST = T\<rbrakk>
                       \<Longrightarrow> ST = \<langle>\<langle>S, T\<rangle>\<rangle>"
        proof -
          fix ST
          assume ST: "transformation X resid F G ST"
          assume 0: "P\<^sub>0 \<circ> ST = T"
          assume 1: "P\<^sub>1 \<circ> ST = S"
          interpret ST: transformation X resid F G ST
            using ST by blast
          show "ST = \<langle>\<langle>S, T\<rangle>\<rangle>"
          proof
            fix t
            show "ST t = \<langle>\<langle>S, T\<rangle>\<rangle> t"
              unfolding pointwise_tuple_def
              using 0 1 ST.preserves_arr ST.extensional P\<^sub>0_def P\<^sub>1_def
              apply auto[1]
              by (metis prod.exhaust_sel)
          qed
        qed
        thus ?thesis
          using 1 2 3 by metis
      qed
    qed

    lemma proj_joint_monic2:
    assumes "transformation X resid F G S" and "transformation X resid F G T"
    and "P\<^sub>0 \<circ> S = P\<^sub>0 \<circ> T" and "P\<^sub>1 \<circ> S = P\<^sub>1 \<circ> T"
    shows "S = T"
      using assms transformation_whisker_left [of X resid F G S] universality2(4)
            A.weakly_extensional_rts_axioms B.weakly_extensional_rts_axioms
            P\<^sub>1.simulation_axioms P\<^sub>0.simulation_axioms
      by (metis transformation_def)

    lemma join_char:
    shows "join t u =
           (if joinable t u
            then (A.join (fst t) (fst u), B.join (snd t) (snd u))
            else null)"
      by (metis A.join_is_join_of B.join_is_join_of fst_conv join_is_join_of
          join_of_char(1-2) join_of_unique joinable_iff_join_not_null snd_conv)

    lemma join_simp:
    assumes "joinable t u"
    shows "join t u = (A.join (fst t) (fst u), B.join (snd t) (snd u))"
      using assms join_char by auto

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

  lemma simulation_tuple [intro]:
  assumes "simulation X A H" and "simulation X B K"
  and "Y = product_rts.resid A B"
  shows "simulation X Y \<langle>\<langle>H, K\<rangle>\<rangle>"
    using assms product_rts.universality(1) [of A B X H K]
    by (simp add: product_rts.intro simulation_def)

  lemma simulation_product [intro]:
  assumes "simulation A B H" and "simulation C D K"
  and "X = product_rts.resid A C" and "Y = product_rts.resid B D"
  shows "simulation X Y (product_simulation.map A C H K)"
    using assms
    by (meson product_rts_def product_rts_def product_simulation.intro
        product_simulation.is_simulation simulation_def simulation_def)

  lemma comp_pointwise_tuple:
  shows "\<langle>\<langle>H, K\<rangle>\<rangle> \<circ> L = \<langle>\<langle>H \<circ> L, K \<circ> L\<rangle>\<rangle>"
    unfolding pointwise_tuple_def
    by auto

  lemma comp_product_simulation_tuple2:
  assumes "simulation A A' F" and "simulation B B' G"
  and "transformation X A H\<^sub>0 H\<^sub>1 H" and "transformation X B K\<^sub>0 K\<^sub>1 K"
  shows "product_simulation.map A B F G \<circ> \<langle>\<langle>H, K\<rangle>\<rangle> = \<langle>\<langle>F \<circ> H, G \<circ> K\<rangle>\<rangle>"
  proof -
    interpret X: weakly_extensional_rts X
      using assms(3) transformation.axioms(1) by blast
    interpret A: rts A
      using assms(1) simulation.axioms(1) by blast
    interpret B: rts B
      using assms(2) simulation.axioms(1) by blast
    interpret A': rts A'
      using assms(1) simulation.axioms(2) by blast
    interpret B': rts B'
      using assms(2) simulation.axioms(2) by blast
    interpret AxB: product_rts A B ..
    interpret A'xB': product_rts A' B' ..
    interpret F: simulation A A' F
      using assms by blast
    interpret G: simulation B B' G
       using assms by blast
    interpret FxG: product_simulation A B A' B' F G ..
    interpret H: transformation X A H\<^sub>0 H\<^sub>1 H
      using assms(3) by blast
    interpret K: transformation X B K\<^sub>0 K\<^sub>1 K
      using assms(4) by blast
    show ?thesis
    proof
      fix x
      show "(FxG.map \<circ> \<langle>\<langle>H, K\<rangle>\<rangle>) x = \<langle>\<langle>F \<circ> H, G \<circ> K\<rangle>\<rangle> x"
        using FxG.extensional pointwise_tuple_def F.extensional G.extensional
              H.extensional K.extensional H.preserves_arr K.preserves_arr
        by (cases "X.arr x") (auto simp add: pointwise_tuple_def)
    qed
  qed

  lemma comp_product_simulation_tuple:
  assumes "simulation A A' F" and "simulation B B' G"
  and "simulation X A H" and "simulation X B K"
  shows "product_simulation.map A B F G \<circ> \<langle>\<langle>H, K\<rangle>\<rangle> = \<langle>\<langle>F \<circ> H, G \<circ> K\<rangle>\<rangle>"
  proof -
    (* Proof is repeated because I don't want to have the extensionality assumption. *)
    interpret X: rts X
      using assms(3) simulation.axioms(1) by blast
    interpret A: rts A
      using assms(1) simulation.axioms(1) by blast
    interpret B: rts B
      using assms(2) simulation.axioms(1) by blast
    interpret A': rts A'
      using assms(1) simulation.axioms(2) by blast
    interpret B': rts B'
      using assms(2) simulation.axioms(2) by blast
    interpret AxB: product_rts A B ..
    interpret A'xB': product_rts A' B' ..
    interpret F: simulation A A' F
      using assms by blast
    interpret G: simulation B B' G
       using assms by blast
    interpret FxG: product_simulation A B A' B' F G ..
    interpret H: simulation X A H
      using assms(3) by blast
    interpret K: simulation X B K
      using assms(4) by blast
    show ?thesis
    proof
      fix x
      show "(FxG.map \<circ> \<langle>\<langle>H, K\<rangle>\<rangle>) x = \<langle>\<langle>F \<circ> H, G \<circ> K\<rangle>\<rangle> x"
        using FxG.extensional pointwise_tuple_def F.extensional G.extensional
              H.extensional K.extensional H.preserves_reflects_arr
              K.preserves_reflects_arr
        by (cases "X.arr x") (auto simp add: pointwise_tuple_def)
    qed
  qed

  (*
   * TODO: The (strong) extensionality assumption on B1 and B0 is present because
   * the proof uses transformation_by_components, which requires that assumption.
   * It might be possible to weaken the locale assumptions for transformation_by_components,
   * in which case we would need only weak extensionality of B1 and B0 here.
   *)

  locale product_transformation =
    A1: weakly_extensional_rts A1 +
    A0: weakly_extensional_rts A0 +
    B1: extensional_rts B1 +
    B0: extensional_rts B0 +
    A1xA0: product_rts A1 A0 +
    B1xB0: product_rts B1 B0 +
    F1: simulation A1 B1 F1 +
    F0: simulation A0 B0 F0 +
    G1: simulation A1 B1 G1 +
    G0: simulation A0 B0 G0 +
    T1: transformation A1 B1 F1 G1 T1 +
    T0: transformation A0 B0 F0 G0 T0
  for A1 :: "'a1 resid"      (infix "\\\<^sub>A\<^sub>1" 70)
  and A0 :: "'a0 resid"      (infix "\\\<^sub>A\<^sub>0" 70)
  and B1 :: "'b1 resid"      (infix "\\\<^sub>B\<^sub>1" 70)
  and B0 :: "'b0 resid"      (infix "\\\<^sub>B\<^sub>0" 70)
  and F1 :: "'a1 \<Rightarrow> 'b1"
  and F0 :: "'a0 \<Rightarrow> 'b0"
  and G1 :: "'a1 \<Rightarrow> 'b1"
  and G0 :: "'a0 \<Rightarrow> 'b0"
  and T1 :: "'a1 \<Rightarrow> 'b1"
  and T0 :: "'a0 \<Rightarrow> 'b0"
  begin

    sublocale F1: simulation_to_weakly_extensional_rts A1 B1 F1 ..
    sublocale F0: simulation_to_weakly_extensional_rts A0 B0 F0 ..
    sublocale G1: simulation_to_weakly_extensional_rts A1 B1 G1 ..
    sublocale G0: simulation_to_weakly_extensional_rts A0 B0 G0 ..

    sublocale A1xA0: product_of_weakly_extensional_rts A1 A0 ..
    sublocale B1xB0: product_of_extensional_rts B1 B0 ..
    sublocale F1xF0: product_simulation A1 A0 B1 B0 F1 F0 ..
    sublocale G1xG0: product_simulation A1 A0 B1 B0 G1 G0 ..

    abbreviation (input) map\<^sub>0 :: "'a1 \<times> 'a0 \<Rightarrow> 'b1 \<times> 'b0"
    where "map\<^sub>0 \<equiv> (\<lambda>a. (T1 (fst a), T0 (snd a)))"

    sublocale TC: transformation_by_components
                    A1xA0.resid B1xB0.resid F1xF0.map G1xG0.map map\<^sub>0
    proof
      show "\<And>a. A1xA0.ide a \<Longrightarrow> B1xB0.src (map\<^sub>0 a) = F1xF0.map a"
        unfolding F1xF0.map_def
        using T1.preserves_arr T0.preserves_arr T1.preserves_src T0.preserves_src
              B1xB0.src_char
        by auto
      show "\<And>a. A1xA0.ide a \<Longrightarrow> B1xB0.trg (map\<^sub>0 a) = G1xG0.map a"
        unfolding G1xG0.map_def
        using T1.preserves_arr T0.preserves_arr T1.preserves_trg T0.preserves_trg
              B1xB0.trg_char
        by auto
      fix t
      assume t: "A1xA0.arr t"
      show "B1xB0.resid (map\<^sub>0 (A1xA0.src t)) (F1xF0.map t) =
            map\<^sub>0 (A1xA0.trg t)"
        unfolding F1xF0.map_def
        using t B1xB0.resid_def A1xA0.src_char A1xA0.trg_char
              T1.naturality1 T0.naturality1 A1.con_arr_src(2) T1.preserves_con(2)
              A0.con_arr_src(2) T0.preserves_con(2)
        by auto
      show "B1xB0.resid (F1xF0.map t) (map\<^sub>0 (A1xA0.src t)) =
            G1xG0.map t"
        unfolding F1xF0.map_def G1xG0.map_def
        using t B1xB0.resid_def A1xA0.src_char A1xA0.trg_char
              T1.naturality2 T0.naturality2
        apply auto[1]
         apply (metis B1.conI B1.not_arr_null G1.preserves_reflects_arr)
        by (metis B0.conI B0.not_arr_null G0.preserves_reflects_arr)
      show "B1xB0.joinable (map\<^sub>0 (A1xA0.src t)) (F1xF0.map t)"
        unfolding F1xF0.map_def
        using t A1xA0.src_char T1.naturality3 T0.naturality3
        apply auto[1]
        by (metis B0.joinable_def B1.joinable_def B1xB0.join_of_char(2)
            fst_eqD snd_eqD)
    qed

    definition map :: "'a1 \<times> 'a0 \<Rightarrow> 'b1 \<times> 'b0"
    where "map \<equiv> TC.map"

    sublocale transformation
                A1xA0.resid B1xB0.resid F1xF0.map G1xG0.map map
      unfolding map_def ..

    lemma is_transformation:
    shows "transformation A1xA0.resid B1xB0.resid F1xF0.map G1xG0.map map"
      ..

    lemma map_simp:
    shows "map t = B1xB0.join (map\<^sub>0 (A1xA0.src t)) (F1xF0.map t)"
      unfolding map_def TC.map_def by blast

    lemma map_simp_ide:
    assumes "A1xA0.ide t"
    shows "map t = map\<^sub>0 (A1xA0.src t)"
      unfolding map_def
      using assms TC.map_simp_ide by simp

  end

  lemma comp_product_transformation_tuple:
  assumes "transformation_to_extensional_rts A1 B1 F1 G1 T1"
  and "transformation_to_extensional_rts A0 B0 F0 G0 T0"
  and "simulation X A1 H1" and "simulation X A0 H0"
  shows "product_transformation.map A1 A0 B1 B0 F1 F0 T1 T0 \<circ> \<langle>\<langle>H1, H0\<rangle>\<rangle> =
         \<langle>\<langle>T1 \<circ> H1, T0 \<circ> H0\<rangle>\<rangle>"
  proof -
    interpret X: rts X
      using assms(3) simulation.axioms(1) by blast
    interpret A1: weakly_extensional_rts A1
      using assms(1) transformation_to_extensional_rts.axioms(1)
            transformation.axioms(1)
      by blast
    interpret A0: weakly_extensional_rts A0
      using assms(2) transformation_to_extensional_rts.axioms(1)
            transformation.axioms(1)
      by blast
    interpret B1: extensional_rts B1
      using assms(1) transformation_to_extensional_rts.axioms(2) by blast
    interpret B0: extensional_rts B0
      using assms(2) transformation_to_extensional_rts.axioms(2) by blast
    interpret F1: simulation A1 B1 F1
      using assms(1) transformation_to_extensional_rts.axioms(1)
            transformation.axioms(3) simulation.axioms(3)
      by blast
    interpret F0: simulation A0 B0 F0
      using assms(2) transformation_to_extensional_rts.axioms(1)
            transformation.axioms(3) simulation.axioms(3)
      by blast
    interpret G1: simulation A1 B1 G1
      using assms(1) transformation_to_extensional_rts.axioms(1)
            transformation.axioms(4) simulation.axioms(3)
      by blast
    interpret G0: simulation A0 B0 G0
      using assms(2) transformation_to_extensional_rts.axioms(1)
            transformation.axioms(4) simulation.axioms(3)
      by blast
    interpret T1: transformation_to_extensional_rts A1 B1 F1 G1 T1
      using assms(1) by blast
    interpret T0: transformation_to_extensional_rts A0 B0 F0 G0 T0
      using assms(2) by blast
    interpret A1xA0: product_of_weakly_extensional_rts A1 A0 ..
    interpret B1xB0: product_of_extensional_rts B1 B0 ..
    interpret F1xF0: product_simulation A1 A0 B1 B0 F1 F0 ..
    interpret G1xG0: product_simulation A1 A0 B1 B0 G1 G0 ..
    interpret T1xT0: product_transformation A1 A0 B1 B0 F1 F0 G1 G0 T1 T0
      ..
    interpret H1: simulation X A1 H1
      using assms(3) by blast
    interpret H0: simulation X A0 H0
      using assms(4) by blast
    show ?thesis
    proof
      fix x
      show "(T1xT0.map \<circ> \<langle>\<langle>H1, H0\<rangle>\<rangle>) x = \<langle>\<langle>T1 \<circ> H1, T0 \<circ> H0\<rangle>\<rangle> x"
      proof -
        have "X.arr x \<Longrightarrow>
                B1xB0.join
                  (T1 (fst (A1xA0.src (H1 x, H0 x))),
                   T0 (snd (A1xA0.src (H1 x, H0 x))))
                  (F1 (H1 x), F0 (H0 x)) =
              (T1 (H1 x), T0 (H0 x))"
        proof -
          assume x: "X.arr x"
          have "B1xB0.join
                  (T1 (fst (A1xA0.src (H1 x, H0 x))),
                   T0 (snd (A1xA0.src (H1 x, H0 x))))
                  (F1 (H1 x), F0 (H0 x)) =
                B1xB0.join
                  (T1 (A1.src (H1 x)), T0 (A0.src (H0 x)))
                  (F1 (H1 x), F0 (H0 x))"
            using x A1xA0.src_char by auto
          also have "... = (T1 (H1 x), T0 (H0 x))"
            using x B1xB0.join_char
            by (simp add: B1xB0.join_of_char(2) T0.naturality3'\<^sub>E(1-2)
                T1.naturality3'\<^sub>E(1-2))
          finally show ?thesis by blast
        qed
        thus ?thesis
          using pointwise_tuple_def H1.extensional H0.extensional
                T1.extensional T0.extensional T1xT0.extensional T1xT0.map_def
                T1xT0.TC.map_def comp_product_simulation_tuple
                F1xF0.product_simulation_axioms G1xG0.product_simulation_axioms
          by (cases "X.arr x") (auto simp add: pointwise_tuple_def)
      qed
    qed
  qed

  lemma simulation_interchange:
  assumes "simulation A A' F" and "simulation B B' G"
  and "simulation A' A'' F'" and "simulation B' B'' G'"
  shows "product_simulation.map A B (F' \<circ> F) (G' \<circ> G) =
         product_simulation.map A' B' F' G' \<circ> product_simulation.map A B F G"
  proof -
    interpret F: simulation A A' F
      using assms(1) by blast
    interpret G: simulation B B' G
      using assms(2) by blast
    interpret F': simulation A' A'' F'
      using assms(3) by blast
    interpret G': simulation B' B'' G'
      using assms(4) by blast
    interpret F'oF: composite_simulation A A' A'' F F' ..
    interpret G'oG: composite_simulation B B' B'' G G' ..
    interpret FxG: product_simulation A B A' B' F G ..
    interpret F'xG': product_simulation A' B' A'' B'' F' G' ..
    interpret F'oFxG'oG: product_simulation A B A'' B'' \<open>F' \<circ> F\<close> \<open>G' \<circ> G\<close> ..
    show "F'oFxG'oG.map = F'xG'.map \<circ> FxG.map"
      unfolding F'oFxG'oG.map_def FxG.map_def F'xG'.map_def
      using F.extensional G.extensional F'.extensional G'.extensional by auto
  qed

subsection "Associators"

  text \<open>
    For any RTS's \<open>A\<close>, \<open>B\<close>, and \<open>C\<close>, there exists an invertible ``associator'' simulation
    from the product RTS \<open>(A \<times> B) \<times> C)\<close> to the product RTS \<open>A \<times> (B \<times> C)\<close>.
  \<close>

  locale ASSOC =
    A: rts A +
    B: rts B +
    C: rts C
  for A :: "'a resid"
  and B :: "'b resid"
  and C :: "'c resid"
  begin

    sublocale AxB: product_rts A B ..
    sublocale BxC: product_rts B C ..
    sublocale AxB_xC: product_rts AxB.resid C ..
    sublocale Ax_BxC: product_rts A BxC.resid ..

    text \<open>
      The following definition is expressed in a form that makes it evident that it
      defines a simulation.
    \<close>

    definition map :: "('a \<times> 'b) \<times> 'c \<Rightarrow> 'a \<times> 'b \<times> 'c"
    where "map \<equiv> Ax_BxC.tuple
                   (AxB.P\<^sub>1 \<circ> AxB_xC.P\<^sub>1) 
                   (BxC.tuple (AxB.P\<^sub>0 \<circ> AxB_xC.P\<^sub>1) AxB_xC.P\<^sub>0)"

    sublocale simulation AxB_xC.resid Ax_BxC.resid map
      unfolding map_def
      using AxB.P\<^sub>0.simulation_axioms AxB.P\<^sub>1.simulation_axioms
            AxB_xC.P\<^sub>0.simulation_axioms AxB_xC.P\<^sub>1.simulation_axioms
      by (intro simulation_tuple simulation_comp) auto

    lemma is_simulation:
    shows "simulation AxB_xC.resid Ax_BxC.resid map"
      ..

    text \<open>
      The following explicit formula is more convenient for calculations.
    \<close>

    lemma map_eq:
    shows "map = (\<lambda>x. if AxB_xC.arr x
                      then (fst (fst x), (snd (fst x), snd x))
                      else Ax_BxC.null)"
      unfolding map_def pointwise_tuple_def AxB.P\<^sub>0_def AxB.P\<^sub>1_def
        AxB_xC.P\<^sub>0_def AxB_xC.P\<^sub>1_def
      by auto

    definition map' :: "'a \<times> 'b \<times> 'c \<Rightarrow> ('a \<times> 'b) \<times> 'c"
    where "map' \<equiv> AxB_xC.tuple
                    (AxB.tuple Ax_BxC.P\<^sub>1 (BxC.P\<^sub>1 \<circ> Ax_BxC.P\<^sub>0))
                    (BxC.P\<^sub>0 \<circ> Ax_BxC.P\<^sub>0)"

    sublocale inv: simulation Ax_BxC.resid AxB_xC.resid map'
      unfolding map'_def
      using BxC.P\<^sub>0.simulation_axioms BxC.P\<^sub>1.simulation_axioms
            Ax_BxC.P\<^sub>0.simulation_axioms Ax_BxC.P\<^sub>1.simulation_axioms
      by (intro simulation_tuple simulation_comp) auto

    lemma inv_is_simulation:
    shows "simulation Ax_BxC.resid AxB_xC.resid map'"
      ..

    lemma map'_eq:
    shows "map' =
           (\<lambda>x. if Ax_BxC.arr x
                then ((fst x, fst (snd x)), snd (snd x))
                else AxB_xC.null)"
      unfolding map'_def pointwise_tuple_def BxC.P\<^sub>0_def BxC.P\<^sub>1_def
        Ax_BxC.P\<^sub>0_def Ax_BxC.P\<^sub>1_def
      by auto

    lemma inverse_simulations_map'_map:
    shows "inverse_simulations AxB_xC.resid Ax_BxC.resid map' map"
    proof
      show "map \<circ> map' = I Ax_BxC.resid"
        unfolding map_eq map'_eq by auto
      show "map' \<circ> map = I AxB_xC.resid"
        unfolding map_eq map'_eq by auto
    qed

  end

section "Exponential RTS"

  text \<open>
    The exponential \<open>[A, B]\<close> of RTS's \<open>A\<close> and \<open>B\<close> has states corresponding to simulations
    from \<open>A\<close> to \<open>B\<close> and transitions corresponding to transformations between such simulations.
    Since our definition of transformation has assumed that \<open>A\<close> and \<open>B\<close> are weakly extensional,
    we need to include those assumptions here.  In addition, the definition of residuation
    for the exponential RTS uses the assumption of uniqueness of joins, so we actually assume
    that \<open>B\<close> is extensional.  Things become rather inconvenient if this assumption is not made,
    and I have not investigated whether relaxing it is possible.
  \<close>

  locale consistent_transformations =
    A: weakly_extensional_rts A +
    B: extensional_rts B +
    F: simulation A B F +
    G: simulation A B G +
    H: simulation A B H +
    \<sigma>: transformation A B F G \<sigma> +
    \<tau>: transformation A B F H \<tau>
  for A :: "'a resid"      (infix "\\\<^sub>A" 70)
  and B :: "'b resid"      (infix "\\\<^sub>B" 70)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and H :: "'a \<Rightarrow> 'b"
  and \<sigma> :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b" +
  assumes con: "A.ide a \<longrightarrow> B.con (\<sigma> a) (\<tau> a)"
  begin

    sublocale \<sigma>: transformation_to_extensional_rts A B F G \<sigma> ..
    sublocale \<tau>: transformation_to_extensional_rts A B F H \<tau> ..

    sublocale sym: consistent_transformations A B F H G \<tau> \<sigma>
      by (meson B.residuation_axioms con consistent_transformations_axioms
          consistent_transformations_axioms.intro consistent_transformations_def
          residuation.con_sym)

    text \<open>
      The ``apex'' determined by consistent transformations \<open>\<sigma>\<close> and \<open>\<tau>\<close> is the simulation
      whose value at a transition \<open>t\<close> of \<open>A\<close> may be visualized as the apex of a rectangular
      parallelepiped, which is formed with \<open>t\<close> as its base, the components at \<open>src c\<close> of the
      transformations associated with the two transitions and their residuals,
      and the images of \<open>t\<close> under these transformations.
    \<close>

    abbreviation apex :: "'a \<Rightarrow> 'b"
    where "apex \<equiv> (\<lambda>t. if A.arr t
                       then H t \\\<^sub>B (\<sigma> (A.src t) \\\<^sub>B \<tau> (A.src t))
                       else B.null)"

    abbreviation resid :: "'a \<Rightarrow> 'b"
    where "resid \<equiv> (\<lambda>t. if A.arr t
                        then B.join (\<sigma> (A.src t) \\\<^sub>B \<tau> (A.src t)) (H t)
                        else B.null)"

  end

  text\<open>
    For unknown reasons, it is necessary to close and re-open the context here in order
    to obtain access to \<open>sym\<close> as a sublocale.
  \<close>

  context consistent_transformations
  begin

    lemma sym_apex_eq:
    shows "sym.apex = apex"
    proof
      fix t
      show "sym.apex t = apex t"
        by (metis (full_types) \<sigma>.naturality2 \<tau>.naturality2 B.cube)
    qed

    text\<open>
      The apex associated with two consistent transformations is a simulation.
      The proof that it preserves residuation can be visualized in terms of a
      three-dimensional figure consisting of four rectangular parallelepipeds connected
      into an overall diamond shape, with \<open>Dom \<tau> t\<close> and \<open>Dom \<sigma> u\<close> (which is equal to \<open>Dom \<tau> u\<close>)
      and their residuals at the base of the overall diamond and with \<open>Apex \<sigma> \<tau> t\<close>
      and \<open>Apex \<sigma> \<tau> u\<close> at its peak.
    \<close>

    interpretation apex: simulation A B apex
    proof
      show "\<And>t. \<not> A.arr t \<Longrightarrow> apex t = B.null"
        by simp
      show "\<And>t u. t \<frown>\<^sub>A u \<Longrightarrow> apex t \<frown>\<^sub>B apex u"
      proof -
        fix t u
        assume con: "t \<frown>\<^sub>A u"
        have "apex t \<frown>\<^sub>B apex u \<longleftrightarrow>
              H t \\\<^sub>B (\<sigma> (A.src t) \\\<^sub>B \<tau> (A.src t)) \<frown>\<^sub>B
              H u \\\<^sub>B (\<sigma> (A.src u) \\\<^sub>B \<tau> (A.src u))"
          using A.con_implies_arr(1-2) con by simp
        also have "... \<longleftrightarrow> (F t \\\<^sub>B \<tau> (A.src t)) \\\<^sub>B
                                  (\<sigma> (A.src t) \\\<^sub>B \<tau> (A.src t)) \<frown>\<^sub>B
                           (F u \\\<^sub>B \<tau> (A.src t)) \\\<^sub>B
                                  (\<sigma> (A.src t) \\\<^sub>B \<tau> (A.src t))"
          using A.con_implies_arr(1-2) \<tau>.naturality2 con A.con_imp_eq_src
          by (metis (mono_tags, lifting))
        also have "... \<longleftrightarrow> (F t \\\<^sub>B F u) \\\<^sub>B \<tau> (A.trg u) \<frown>\<^sub>B
                           (\<sigma> (A.src t) \\\<^sub>B F u) \\\<^sub>B \<tau> (A.trg u)"
            using A.con_imp_eq_src \<tau>.naturality1 con B.con_def B.cube by presburger
        also have "... \<longleftrightarrow> (F t \\\<^sub>B F u) \\\<^sub>B \<tau> (A.trg u) \<frown>\<^sub>B
                           \<sigma> (A.trg u) \\\<^sub>B \<tau> (A.trg u)"
          using A.con_imp_eq_src \<sigma>.naturality1 con by presburger
        also have "... \<longleftrightarrow> F (t \\\<^sub>A u) \\\<^sub>B \<tau> (A.trg u) \<frown>\<^sub>B
                           \<sigma> (A.trg u) \\\<^sub>B \<tau> (A.trg u)"
          using F.preserves_resid con by presburger
        also have "... \<longleftrightarrow> True"
          by (metis A.arr_resid A.ide_trg A.src_resid B.con_def B.con_sym
              B.cube \<sigma>.naturality1 \<tau>.naturality1 con sym.con)
        finally show "apex t \<frown>\<^sub>B apex u" by blast
      qed
      show "\<And>t u. t \<frown>\<^sub>A u \<Longrightarrow> apex (t \\\<^sub>A u) = apex t \\\<^sub>B apex u"
        using \<sigma>.naturality1 \<tau>.naturality1 \<tau>.naturality2 B.cube A.arr_resid A.arr_src_iff_arr
              A.con_imp_eq_src A.con_implies_arr(1-2) A.src_resid H.preserves_resid
        by auto (metis (mono_tags, lifting))
    qed

    lemma simulation_apex:
    shows "simulation A B apex"
      ..

    lemma resid_ide:
    assumes "A.ide a"
    shows "resid a = \<sigma> a \\\<^sub>B \<tau> a"
      by (metis (full_types) A.arr_def A.ideE A.weakly_extensional_rts_axioms
          B.join_prfx(2) apex.preserves_ide assms weakly_extensional_rts.src_ide)

    interpretation resid: transformation \<open>(\\<^sub>A)\<close> \<open>(\\<^sub>B)\<close> H apex resid
    proof -
      have 2: "\<And>f. A.ide f \<Longrightarrow> B.joinable (\<sigma> (A.src f) \\\<^sub>B \<tau> (A.src f)) (H f)"
        using B.joinable_iff_arr_join con resid_ide by auto
      show "transformation (\\\<^sub>A) (\\\<^sub>B) H apex resid"
      proof
        show "\<And>f. \<not> A.arr f \<Longrightarrow> resid f = B.null"
          by force
        show 3: "\<And>f. A.ide f \<Longrightarrow> B.src (resid f) = H f"
          using 2 B.src_join \<tau>.preserves_trg con by auto
        show "\<And>f. A.ide f \<Longrightarrow> B.trg (resid f) = apex f"
          using B.apex_arr_prfx(2) apex.preserves_ide resid_ide by force
        show "\<And>f. A.arr f \<Longrightarrow> H f \\\<^sub>B resid (A.src f) = apex f"
          using resid_ide by force
        show "\<And>f. A.arr f \<Longrightarrow> resid (A.src f) \\\<^sub>B H f = resid (A.trg f)"
          using A.ide_src A.ide_trg B.cube \<sigma>.naturality1 \<tau>.naturality1
                \<tau>.naturality2 resid_ide
          by auto metis
        show "\<And>f. A.arr f \<Longrightarrow> B.join_of (resid (A.src f)) (H f) (resid f)"
        proof -
          fix f
          assume f: "A.arr f"
          have 1: "B.joinable (\<sigma> (A.src f) \\\<^sub>B \<tau> (A.src f)) (H f)"
          proof -
            have "(\<sigma> (A.src f) \<squnion>\<^sub>B F f) \\\<^sub>B \<tau> (A.src f) =
                  (\<sigma> (A.src f) \\\<^sub>B \<tau> (A.src f)) \<squnion>\<^sub>B (F f \\\<^sub>B \<tau> (A.src f))"
              by (metis A.prfx_reflexive A.trg_def B.conI B.con_with_join_if(2)
                  B.not_arr_null B.resid_join\<^sub>E(3) H.preserves_reflects_arr
                  \<sigma>.naturality1_ax \<sigma>.naturality3'\<^sub>E(2) \<tau>.naturality1_ax \<tau>.naturality2
                  f sym.con)
            hence "B.join_of (\<sigma> (A.src f) \\\<^sub>B \<tau> (A.src f)) (H f)
                             ((\<sigma> (A.src f) \\\<^sub>B \<tau> (A.src f)) \<squnion>\<^sub>B (F f \\\<^sub>B \<tau> (A.src f)))"
              using f A.ide_trg B.arr_resid_iff_con B.conE B.con_sym B.con_with_join_if(1)
                    B.join_def B.join_is_join_of H.preserves_reflects_arr \<sigma>.naturality1
                    \<sigma>.naturality3'\<^sub>E(2) \<tau>.naturality1 \<tau>.naturality2
              by (metis sym.con)
            thus ?thesis
              using B.joinable_def by blast
          qed
          show "B.join_of (resid (A.src f)) (H f) (resid f)"
            using 1 A.ide_src B.join_is_join_of resid_ide f by auto
        qed
      qed
    qed

    lemma transformation_resid:
    shows "transformation (\\\<^sub>A) (\\\<^sub>B) H apex resid"
      ..

  end

  text\<open>
    Now we can define the exponential \<open>[A, B]\<close> of RTS's \<open>A\<close> and \<open>B\<close>.
  \<close>

  locale exponential_rts =
  A: weakly_extensional_rts A +
  B: extensional_rts B
  for A :: "'a resid"      (infix "\\\<^sub>A" 70)
  and B :: "'b resid"      (infix "\\\<^sub>B" 70)
  begin

    notation A.con   (infix "\<frown>\<^sub>A" 50)
    notation A.prfx  (infix "\<lesssim>\<^sub>A" 50)
    notation B.con   (infix "\<frown>\<^sub>B" 50)
    notation B.join  (infix "\<squnion>\<^sub>B" 52)
    notation B.prfx  (infix "\<lesssim>\<^sub>B" 50)

    datatype ('aa, 'bb) arr =
      Null
    | MkArr \<open>'aa \<Rightarrow> 'bb\<close> \<open>'aa \<Rightarrow> 'bb\<close> \<open>'aa \<Rightarrow> 'bb\<close>

    abbreviation MkIde :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) arr"
    where "MkIde a \<equiv> MkArr a a a"

    fun Dom :: "('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
    where "Dom (MkArr F _ _) = F"
        | "Dom _ = undefined"

    fun Cod :: "('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
    where "Cod (MkArr _ G _) = G"
        | "Cod _ = undefined"

    fun Map :: "('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
    where "Map (MkArr _ _ \<tau>) = \<tau>"
        | "Map _ = undefined"

    abbreviation Arr :: "('a, 'b) arr \<Rightarrow> bool"
    where "Arr \<equiv> \<lambda>\<tau>. \<tau> \<noteq> Null \<and> transformation A B (Dom \<tau>) (Cod \<tau>) (Map \<tau>)"

    abbreviation Ide :: "('a, 'b) arr \<Rightarrow> bool"
    where "Ide \<equiv> \<lambda>\<tau>. \<tau> \<noteq> Null \<and>
                     identity_transformation A B (Dom \<tau>) (Cod \<tau>) (Map \<tau>)"

    text \<open>
      In order to define consistency for transitions of the exponential, we at least need
      to have pointwise consistency of the components of the corresponding transitions.
      Surprisingly, this is sufficient.
    \<close>

    abbreviation Con :: "('a, 'b) arr \<Rightarrow> ('a, 'b) arr \<Rightarrow> bool"
    where "Con \<equiv> \<lambda>\<sigma> \<tau>. Arr \<sigma> \<and> Arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and>
                       (\<forall>a. A.ide a \<longrightarrow> B.con (Map \<sigma> a) (Map \<tau> a))"

    lemma Con_sym:
    assumes "Con \<sigma> \<tau>"
    shows "Con \<tau> \<sigma>"
      using assms B.con_sym by auto

    lemma Con_implies_consistent_transformations:
    assumes "Con \<sigma> \<tau>"
    shows "consistent_transformations
             A B (Dom \<sigma>) (Cod \<sigma>) (Cod \<tau>) (Map \<sigma>) (Map \<tau>)"
    proof -
      interpret \<sigma>: transformation A B \<open>Dom \<sigma>\<close> \<open>Cod \<sigma>\<close> \<open>Map \<sigma>\<close>
        using assms by auto
      interpret \<tau>: transformation A B \<open>Dom \<sigma>\<close> \<open>Cod \<tau>\<close> \<open>Map \<tau>\<close>
        using assms by auto
      show ?thesis
        using assms
        apply intro_locales
        by (simp add: consistent_transformations_axioms_def)
    qed

    definition Apex :: "('a, 'b) arr \<Rightarrow> ('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
    where "Apex \<sigma> \<tau> = (\<lambda>t. if A.arr t
                           then Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))
                           else B.null)"

    lemma Apex_sym:
    assumes "Con \<sigma> \<tau>"
    shows "Apex \<sigma> \<tau> = Apex \<tau> \<sigma>"
      unfolding Apex_def
      using assms Con_implies_consistent_transformations
            consistent_transformations.sym_apex_eq
              [of A B "Dom \<sigma>" "Cod \<sigma>" "Cod \<tau>" "Map \<sigma>" "Map \<tau>"]
      by auto

    lemma Apex_is_simulation [intro]:
    assumes "Con \<sigma> \<tau>"
    shows "simulation A B (Apex \<sigma> \<tau>)"
      unfolding Apex_def
      using assms Con_implies_consistent_transformations
            consistent_transformations.simulation_apex
      by blast

    abbreviation Resid :: "('a, 'b) arr \<Rightarrow> ('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
    where "Resid \<sigma> \<tau> \<equiv> (\<lambda>t. if A.arr t
                            then (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Cod \<tau> t
                            else B.null)"

    definition resid :: "('a, 'b) arr resid"    (infix "\\" 70)
    where "\<sigma> \\ \<tau> =
           (if Con \<sigma> \<tau>
            then MkArr (Cod \<tau>)
                   (consistent_transformations.apex A B (Cod \<tau>) (Map \<sigma>) (Map \<tau>))
                   (consistent_transformations.resid A B (Cod \<tau>) (Map \<sigma>) (Map \<tau>))
            else Null)"

    lemma Dom_resid':
    assumes "Con \<sigma> \<tau>"
    shows "Dom (\<sigma> \\ \<tau>) = Cod \<tau>"
      using assms resid_def by auto

    lemma Cod_resid':
    assumes "Con \<sigma> \<tau>"
    shows "Cod (\<sigma> \\ \<tau>) = Apex \<sigma> \<tau>"
      unfolding Apex_def
      using assms resid_def Con_implies_consistent_transformations by auto

    lemma Map_resid':
    assumes "Con \<sigma> \<tau>"
    shows "Map (\<sigma> \\ \<tau>) = (\<lambda>t. if A.arr t
                               then Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t
                               else B.null)"
      using assms resid_def by auto

    lemma Map_resid_ide':
    assumes "Con \<sigma> \<tau>" and "A.ide a"
    shows "Map (\<sigma> \\ \<tau>) a = Map \<sigma> a \\\<^sub>B Map \<tau> a"
      unfolding resid_def
      using assms Con_implies_consistent_transformations
            consistent_transformations.resid_ide
              [of A B "Dom \<sigma>" "Cod \<sigma>" "Cod \<tau>" "Map \<sigma>" "Map \<tau>"]
      by auto

    lemma transformation_Map_resid:
    assumes "Con \<sigma> \<tau>"
    shows "transformation (\\\<^sub>A) (\\\<^sub>B) (Cod \<tau>) (Apex \<sigma> \<tau>) (Map (\<sigma> \\ \<tau>))"
      using assms Apex_def resid_def Con_implies_consistent_transformations
            consistent_transformations.transformation_resid
              [of A B "Dom \<sigma>" "Cod \<sigma>" "Cod \<tau>" "Map \<sigma>" "Map \<tau>"]
      by auto

    sublocale ResiduatedTransitionSystem.partial_magma resid
    proof
      show "\<exists>!n. \<forall>t. n \\ t = n \<and> t \\ n = n"
        using resid_def by metis
    qed

    lemma null_char:
    shows "null = Null"
      by (metis null_is_zero(2) resid_def)

    sublocale residuation resid
    proof
      show "\<And>\<sigma> \<tau>. \<sigma> \\ \<tau> \<noteq> null \<Longrightarrow> \<tau> \\ \<sigma> \<noteq> null"
        using resid_def null_char Con_sym
        by (metis (no_types, lifting) arr.simps(2))
      show "\<And>\<sigma> \<tau>. \<sigma> \\ \<tau> \<noteq> null \<Longrightarrow> (\<sigma> \\ \<tau>) \\ (\<sigma> \\ \<tau>) \<noteq> null"
      proof -
        fix \<sigma> \<tau>
        assume 1: "\<sigma> \\ \<tau> \<noteq> null"
        have "Con \<sigma> \<tau>"
          using 1
          by (metis (no_types, opaque_lifting) null_char resid_def)
        hence "Con (\<sigma> \\ \<tau>) (\<sigma> \\ \<tau>)"
          using 1 null_char Dom_resid' Cod_resid' transformation_Map_resid
          apply auto[1]
          by (metis A.ideE transformation.preserves_con(1))
        thus "(\<sigma> \\ \<tau>) \\ (\<sigma> \\ \<tau>) \<noteq> null"
          by (simp add: null_char resid_def)
      qed
      show "\<And>\<rho> \<sigma> \<tau>. (\<sigma> \\ \<tau>) \\ (\<rho> \\ \<tau>) \<noteq> null
                       \<Longrightarrow> (\<sigma> \\ \<tau>) \\ (\<rho> \\ \<tau>) = (\<sigma> \\ \<rho>) \\ (\<tau> \\ \<rho>)"
      proof -
        fix \<rho> \<sigma> \<tau>
        assume \<sigma>\<tau>_\<rho>\<sigma>: "(\<sigma> \\ \<tau>) \\ (\<rho> \\ \<tau>) \<noteq> null"
        have \<sigma>\<tau>: "Con \<sigma> \<tau>"
          using \<sigma>\<tau>_\<rho>\<sigma> resid_def
          by (metis (no_types, opaque_lifting) null_char)
        have \<rho>\<tau>: "Con \<rho> \<tau>"
          using \<sigma>\<tau>_\<rho>\<sigma> resid_def
          by (metis (no_types, opaque_lifting) null_char)
        have \<sigma>\<tau>_\<rho>\<tau>: "Con (\<sigma> \\ \<tau>) (\<rho> \\ \<tau>)"
          using \<sigma>\<tau>_\<rho>\<sigma> resid_def
          by (metis (no_types, opaque_lifting) null_char)
        interpret \<sigma>: transformation A B \<open>Dom \<sigma>\<close> \<open>Cod \<sigma>\<close> \<open>Map \<sigma>\<close>
          using \<sigma>\<tau> by blast
        interpret \<tau>: transformation A B \<open>Dom \<sigma>\<close> \<open>Cod \<tau>\<close> \<open>Map \<tau>\<close>
          using \<sigma>\<tau> by auto
        interpret \<rho>: transformation A B \<open>Dom \<sigma>\<close> \<open>Cod \<rho>\<close> \<open>Map \<rho>\<close>
          using \<sigma>\<tau> \<rho>\<tau> by auto
        have 1: "\<And>a. A.ide a \<Longrightarrow> Map \<sigma> a \\\<^sub>B Map \<tau> a \<frown>\<^sub>B Map \<rho> a \\\<^sub>B Map \<tau> a"
          using \<sigma>\<tau> \<rho>\<tau> Map_resid_ide' \<sigma>\<tau>_\<rho>\<tau> by force
        show "(\<sigma> \\ \<tau>) \\ (\<rho> \\ \<tau>) = (\<sigma> \\ \<rho>) \\ (\<tau> \\ \<rho>)"
        proof -
          interpret \<sigma>\<tau>: transformation A B \<open>Cod \<tau>\<close> \<open>Apex \<sigma> \<tau>\<close> \<open>Map (\<sigma> \ \<tau>)\<close>
            using \<sigma>\<tau>_\<rho>\<sigma> \<sigma>\<tau> \<rho>\<tau> resid_def transformation_Map_resid [of \<sigma> \<tau>] by blast
          interpret \<rho>\<tau>: transformation A B \<open>Cod \<tau>\<close> \<open>Apex \<rho> \<tau>\<close> \<open>Map (\<rho> \ \<tau>)\<close>
            using \<sigma>\<tau>_\<rho>\<sigma> \<sigma>\<tau> \<rho>\<tau> resid_def transformation_Map_resid [of \<rho> \<tau>] by blast
          have \<sigma>\<rho>: "Con \<sigma> \<rho>"
            by (metis \<sigma>\<tau> \<rho>\<tau> 1 B.resid_reflects_con)
          have \<tau>\<rho>: "Con \<tau> \<rho>"
            by (metis \<rho>\<tau> B.con_sym)
          interpret \<sigma>\<rho>: transformation A B \<open>Cod \<rho>\<close> \<open>Apex \<sigma> \<rho>\<close> \<open>Map (\<sigma> \ \<rho>)\<close>
            using \<sigma>\<rho> transformation_Map_resid by blast
          interpret \<tau>\<rho>: transformation A B \<open>Cod \<rho>\<close> \<open>Apex \<tau> \<rho>\<close> \<open>Map (\<tau> \ \<rho>)\<close>
            using \<tau>\<rho> transformation_Map_resid by blast
          have \<sigma>\<rho>_\<tau>\<rho>: "Con (\<sigma> \\ \<rho>) (\<tau> \\ \<rho>)"
          proof (intro conjI)
            show "\<sigma> \\ \<rho> \<noteq> Null"
              using \<sigma>\<rho> resid_def by force
            show "\<tau> \\ \<rho> \<noteq> Null"
              by (metis \<sigma>\<tau>_\<rho>\<sigma> \<open>\<And>\<tau> \<sigma>. \<sigma> \ \<tau> \<noteq> null \<Longrightarrow> \<tau> \ \<sigma> \<noteq> null\<close> null_char
                null_is_zero(2))
            show "Dom (\<sigma> \\ \<rho>) = Dom (\<tau> \\ \<rho>)"
              using \<sigma>\<rho> \<tau>\<rho> exponential_rts.resid_def exponential_rts_axioms by force
            show "transformation A B (Dom (\<sigma> \\ \<rho>)) (Cod (\<sigma> \\ \<rho>)) (Map (\<sigma> \\ \<rho>))"
              using \<sigma>\<rho> \<sigma>\<rho>.transformation_axioms Dom_resid' Cod_resid' by auto
            show "transformation A B (Dom (\<tau> \\ \<rho>)) (Cod (\<tau> \\ \<rho>)) (Map (\<tau> \\ \<rho>))"
              using \<tau>\<rho> \<tau>\<rho>.transformation_axioms Dom_resid' Cod_resid' by auto
            show "\<forall>a. A.ide a \<longrightarrow> Map (\<sigma> \\ \<rho>) a \<frown>\<^sub>B Map (\<tau> \\ \<rho>) a"
              using 1 B.con_def B.cube Map_resid_ide' \<sigma>\<rho> \<tau>\<rho> by force
          qed
          interpret \<sigma>\<tau>_\<rho>\<tau>: transformation A B \<open>Apex \<rho> \<tau>\<close> \<open>Apex (\<sigma> \ \<tau>) (\<rho> \ \<tau>)\<close>
                                         \<open>Map ((\<sigma> \ \<tau>) \ (\<rho> \ \<tau>))\<close>
            by (metis \<rho>\<tau> Cod_resid' \<sigma>\<tau>_\<rho>\<tau> transformation_Map_resid)
          interpret \<sigma>\<rho>_\<tau>\<rho>: transformation A B \<open>Apex \<tau> \<rho>\<close> \<open>Apex (\<sigma> \ \<rho>) (\<tau> \ \<rho>)\<close>
                                         \<open>Map ((\<sigma> \ \<rho>) \ (\<tau> \ \<rho>))\<close>
            using \<sigma>\<rho>_\<tau>\<rho> transformation_Map_resid
            by (metis Cod_resid' \<tau>\<rho>)
          show "(\<sigma> \\ \<tau>) \\ (\<rho> \\ \<tau>) = (\<sigma> \\ \<rho>) \\ (\<tau> \\ \<rho>)"
          proof -
            have 2: "\<And>a. A.ide a \<Longrightarrow>
                           Map ((\<sigma> \\ \<tau>) \\ (\<rho> \\ \<tau>)) a = Map ((\<sigma> \\ \<rho>) \\ (\<tau> \\ \<rho>)) a"
              using B.cube Map_resid_ide' \<rho>\<tau> \<sigma>\<rho> \<sigma>\<rho>_\<tau>\<rho> \<sigma>\<tau> \<sigma>\<tau>_\<rho>\<tau> \<tau>\<rho> by auto
            have 3: "Apex (\<sigma> \\ \<rho>) (\<tau> \\ \<rho>) = Apex (\<sigma> \\ \<tau>) (\<rho> \\ \<tau>)"
            proof -
              have "(\<lambda>t. if A.arr t
                         then Cod (\<tau> \\ \<rho>) t \\\<^sub>B
                                (Map (\<sigma> \\ \<rho>) (A.src t) \\\<^sub>B Map (\<tau> \\ \<rho>) (A.src t))
                         else B.null) =
                    (\<lambda>t. if A.arr t
                         then Cod (\<rho> \\ \<tau>) t \\\<^sub>B
                                (Map (\<sigma> \\ \<tau>) (A.src t) \\\<^sub>B Map (\<rho> \\ \<tau>) (A.src t))
                         else B.null)"
              proof
                fix t
                show "(if A.arr t
                         then Cod (\<tau> \\ \<rho>) t \\\<^sub>B
                                (Map (\<sigma> \\ \<rho>) (A.src t) \\\<^sub>B Map (\<tau> \\ \<rho>) (A.src t))
                         else B.null) =
                      (if A.arr t
                         then Cod (\<rho> \\ \<tau>) t \\\<^sub>B
                                (Map (\<sigma> \\ \<tau>) (A.src t) \\\<^sub>B Map (\<rho> \\ \<tau>) (A.src t))
                         else B.null)"
                proof (cases "A.arr t")
                  show "\<not> A.arr t \<Longrightarrow> ?thesis"
                    by auto
                  assume t: "A.arr t"
                  show ?thesis
                    by (metis 2 A.ide_src Apex_def Apex_sym \<sigma>\<rho>_\<tau>\<rho>.naturality2
                        \<sigma>\<tau>_\<rho>\<tau>.naturality2 \<tau>\<rho>)
                qed
              qed
              thus ?thesis
                using Apex_def by simp
            qed
            have "\<And>x y. \<lbrakk>x \<noteq> null; y \<noteq> null;
                         Dom x = Dom y; Cod x = Cod y; Map x = Map y\<rbrakk>
                           \<Longrightarrow> x = y"
              by (metis Cod.elims Dom.simps(1) Map.simps(1) null_char)
            moreover have "(\<sigma> \\ \<rho>) \\ (\<tau> \\ \<rho>) \<noteq> null"
              using \<sigma>\<rho>_\<tau>\<rho> exponential_rts.resid_def exponential_rts_axioms null_char
              by force
            moreover have "Dom ((\<sigma> \\ \<tau>) \\ (\<rho> \\ \<tau>)) = Dom ((\<sigma> \\ \<rho>) \\ (\<tau> \\ \<rho>))"
              using \<rho>\<tau> Apex_sym Cod_resid' Dom_resid' \<sigma>\<rho>_\<tau>\<rho> \<sigma>\<tau>_\<rho>\<tau> \<tau>\<rho> by auto
            moreover have "Cod ((\<sigma> \\ \<tau>) \\ (\<rho> \\ \<tau>)) = Cod ((\<sigma> \\ \<rho>) \\ (\<tau> \\ \<rho>))"
              using Cod_resid' \<sigma>\<rho>_\<tau>\<rho> \<sigma>\<tau>_\<rho>\<tau> 3 by auto
            moreover have "Map ((\<sigma> \\ \<tau>) \\ (\<rho> \\ \<tau>)) = Map ((\<sigma> \\ \<rho>) \\ (\<tau> \\ \<rho>))"
              using \<rho>\<tau> 2 3 \<sigma>\<rho>_\<tau>\<rho>.transformation_axioms \<sigma>\<tau>_\<rho>\<tau>.transformation_axioms
                    transformation_eqI B.extensional_rts_axioms Apex_sym
              by metis
            ultimately show ?thesis
              using \<sigma>\<tau>_\<rho>\<sigma> null_char by blast
          qed
        qed
      qed
    qed

    notation con   (infix "\<frown>" 50)

    lemma con_char:
    shows "\<sigma> \<frown> \<tau> \<longleftrightarrow> Con \<sigma> \<tau>"
      using con_def resid_def null_char by auto

    lemma arr_char:
    shows "arr \<tau> \<longleftrightarrow> Arr \<tau>"
      by (metis A.ide_implies_arr B.arr_def arrE arrI con_char
          transformation.preserves_arr)

    lemma Dom_resid [simp]:
    assumes "\<sigma> \<frown> \<tau>"
    shows "Dom (\<sigma> \\ \<tau>) = Cod \<tau>"
      using assms Dom_resid' con_char by auto

    lemma Cod_resid [simp]:
    assumes "\<sigma> \<frown> \<tau>"
    shows "Cod (\<sigma> \\ \<tau>) = Apex \<sigma> \<tau>"
      using assms Cod_resid' con_char by auto

    lemma Map_resid [simp]:
    assumes "\<sigma> \<frown> \<tau>"
    shows "Map (\<sigma> \\ \<tau>) = (\<lambda>t. if A.arr t
                               then Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t
                               else B.null)"
      using assms Map_resid' con_char by auto

    lemma Map_resid_ide [simp]:
    assumes "con \<sigma> \<tau>" and "A.ide a"
    shows "Map (\<sigma> \\ \<tau>) a = Map \<sigma> a \\\<^sub>B Map \<tau> a"
      using Map_resid_ide' assms(1-2) con_char by blast

    lemma resid_Map:
    assumes "con \<rho> \<sigma>" and "t \<frown>\<^sub>A u"
    shows "Map \<rho> t \\\<^sub>B Map \<sigma> u = Map (\<rho> \\ \<sigma>) (t \\\<^sub>A u)"
    proof -
      interpret \<rho>: transformation A B \<open>Dom \<rho>\<close> \<open>Cod \<rho>\<close> \<open>Map \<rho>\<close>
        using assms(1) arr_char con_implies_arr(1) by blast
      interpret \<rho>: transformation_to_extensional_rts A B \<open>Dom \<rho>\<close> \<open>Cod \<rho>\<close> \<open>Map \<rho>\<close>
        ..
      interpret \<sigma>: transformation A B \<open>Dom \<sigma>\<close> \<open>Cod \<sigma>\<close> \<open>Map \<sigma>\<close>
        using assms(1) arr_char con_implies_arr(2) by blast
      interpret \<sigma>: transformation_to_extensional_rts A B
                     \<open>Dom \<sigma>\<close> \<open>Cod \<sigma>\<close> \<open>Map \<sigma>\<close>
        ..
      interpret \<rho>\<sigma>: transformation A B \<open>Cod \<sigma>\<close> \<open>Apex \<rho> \<sigma>\<close> \<open>Map (\<rho> \ \<sigma>)\<close>
        using assms con_char transformation_Map_resid by auto
      interpret \<rho>\<sigma>: transformation_to_extensional_rts A B
                      \<open>Cod \<sigma>\<close> \<open>Apex \<rho> \<sigma>\<close> \<open>Map (\<rho> \ \<sigma>)\<close>
        ..
      have "Map \<rho> t \\\<^sub>B Map \<sigma> u = Map \<rho> t \\\<^sub>B (Map \<sigma> (A.src u) \<squnion>\<^sub>B Dom \<sigma> u)"
        by (metis \<sigma>.naturality3'\<^sub>E(1))
      also have "... =
                 (Map \<rho> t \\\<^sub>B Map \<sigma> (A.src u)) \\\<^sub>B (Dom \<sigma> u \\\<^sub>B Map \<sigma> (A.src u))"
        using B.resid_join\<^sub>E(2) [of "Map \<sigma> (A.src u)" "Dom \<sigma> u" "Map \<rho> t"]
        by (metis A.con_implies_arr(2) B.conI B.con_sym_ax B.con_with_join_if(2)
            B.join_sym B.joinable_iff_join_not_null B.null_is_zero(2) \<sigma>.naturality3'\<^sub>E(2)
            assms(2))
      also have "... = (Map \<rho> t \\\<^sub>B Map \<sigma> (A.src u)) \\\<^sub>B Cod \<sigma> u"
        using \<sigma>.naturality2 by presburger
      also have "... =
                 ((Map \<rho> (A.src t) \<squnion>\<^sub>B Dom \<rho> t) \\\<^sub>B Map \<sigma> (A.src u)) \\\<^sub>B Cod \<sigma> u"
        by (metis \<rho>.naturality3'\<^sub>E(1))
      also have "... =
                 (((Map \<rho> (A.src t) \\\<^sub>B Map \<sigma> (A.src u)) \<squnion>\<^sub>B
                    (Dom \<rho> t \\\<^sub>B Map \<sigma> (A.src u))))
                    \\\<^sub>B Cod \<sigma> u"
        using B.resid_join\<^sub>E(3)
        by (metis (mono_tags, lifting) A.con_imp_eq_src A.ide_trg A.residuation_axioms
            B.con_sym B.con_with_join_if(2) B.joinable_implies_con \<rho>.naturality1
            \<rho>.naturality3'\<^sub>E(2) \<sigma>.naturality1 \<sigma>.naturality3'\<^sub>E(2) assms(1-2) con_char
            residuation.con_implies_arr(1))
      also have "... = (Map (\<rho> \\ \<sigma>) (A.src t) \<squnion>\<^sub>B Cod \<sigma> t) \\\<^sub>B Cod \<sigma> u"
        by (metis (mono_tags, lifting) A.con_imp_eq_src A.con_implies_arr(1) A.ide_src
            Map_resid_ide \<sigma>.naturality2 assms(1-2) con_char)
      also have "... = Map (\<rho> \\ \<sigma>) (A.src t) \\\<^sub>B Cod \<sigma> u \<squnion>\<^sub>B Cod \<sigma> t \\\<^sub>B Cod \<sigma> u"
        by (metis (full_types) assms(2) A.con_implies_arr(1) B.conE B.conI B.con_sym_ax
            B.resid_join\<^sub>E(3) \<rho>\<sigma>.naturality3'\<^sub>E(1-2) \<rho>\<sigma>.preserves_con(2))
      also have "... = Map (\<rho> \\ \<sigma>) (A.src t) \\\<^sub>B Cod \<sigma> u \<squnion>\<^sub>B Cod \<sigma> (t \\\<^sub>A u)"
        using assms(2) by fastforce
      also have "... = Map (\<rho> \\ \<sigma>) (A.trg u) \<squnion>\<^sub>B Cod \<sigma> (t \\\<^sub>A u)"
        using A.con_imp_eq_src \<rho>\<sigma>.naturality1 assms(2) by presburger
      also have "... = Map (\<rho> \\ \<sigma>) (t \\\<^sub>A u)"
        by (metis A.src_resid \<rho>\<sigma>.naturality3'\<^sub>E(1) assms(2))
      finally show ?thesis by simp
    qed

    lemma resid_def':
    shows "\<sigma> \\ \<tau> =
           (if \<sigma> \<frown> \<tau>
            then MkArr (Cod \<tau>) (Apex \<sigma> \<tau>)
                       (\<lambda>t. if A.arr t
                            then Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t
                            else B.null)
            else null)"
      using Apex_def resid_def con_char null_char Dom_resid Cod_resid Map_resid
      by auto

    lemma trg_simp:
    assumes "arr \<tau>"
    shows "trg \<tau> = MkArr (Cod \<tau>) (Cod \<tau>) (Cod \<tau>)"
    proof -
      interpret \<tau>: transformation A B \<open>Dom \<tau>\<close> \<open>Cod \<tau>\<close> \<open>Map \<tau>\<close>
        using assms arr_char by blast
      have "trg \<tau> = \<tau> \\ \<tau>"
        using assms trg_def by blast
      also have "... = MkArr (Cod \<tau>) (Cod \<tau>) (Cod \<tau>)"
      proof -
        have "Dom (\<tau> \\ \<tau>) = Cod \<tau>"
          using Dom_resid assms by blast
        moreover have "Cod (\<tau> \\ \<tau>) = Cod \<tau>"
        proof -
          have "(\<lambda>t. if A.arr t
                     then Cod \<tau> t \\\<^sub>B (Map \<tau> (A.src t) \\\<^sub>B Map \<tau> (A.src t))
                     else B.null) =
                Cod \<tau>"
          proof
            fix t
            show "(if A.arr t
                   then Cod \<tau> t \\\<^sub>B (Map \<tau> (A.src t) \\\<^sub>B Map \<tau> (A.src t))
                   else B.null) =
                  Cod \<tau> t"
              by (metis A.con_arr_src(1) A.ide_src A.resid_arr_src B.trg_def
                \<tau>.G.extensional \<tau>.G.preserves_resid \<tau>.preserves_trg)
          qed
          thus ?thesis
            using resid_def Apex_def \<tau>.transformation_axioms assms
                  arr_char null_char \<tau>.preserves_arr
            by auto
        qed
        moreover have "Map (\<tau> \\ \<tau>) = Cod \<tau>"
        proof -
          have "(\<lambda>t. if A.arr t
                     then Map \<tau> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t
                     else B.null) =
                Cod \<tau>"
          proof
            fix t
            show "(if A.arr t
                   then Map \<tau> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t
                   else B.null) =
                  Cod \<tau> t"
              by (metis B.arr_resid_iff_con B.join_src B.src_resid B.trg_def
                  \<tau>.G.extensional \<tau>.G.preserves_reflects_arr \<tau>.naturality2)
          qed
          thus ?thesis
            using resid_def \<tau>.transformation_axioms assms arr_char
                  A.ide_implies_arr B.residuation_axioms \<tau>.preserves_arr
                  residuation.arrE
            by auto
        qed
        ultimately show ?thesis
          using assms arr_char
          by (metis Cod.simps(1) Dom.simps(1) Map.simps(1) arr.exhaust arrE
              conE null_char)
      qed
      finally show ?thesis by blast
    qed

    lemma trg_char:
    shows "trg = (\<lambda>\<tau>. if arr \<tau> then MkIde (Cod \<tau>) else null)"
      using trg_simp trg_def by fastforce

    lemma Map_trg [simp]:
    assumes "arr \<tau>"
    shows "Map (trg \<tau>) = Cod \<tau>"
      using assms trg_simp by auto

    lemma resid_Map_self:
    assumes "arr \<sigma>" and "t \<frown>\<^sub>A u"
    shows "Map \<sigma> t \\\<^sub>B Map \<sigma> u = Cod \<sigma> (t \\\<^sub>A u)"
      using assms resid_Map [of \<sigma> \<sigma> t u]
      by (metis Map_trg arrE trg_def)

    lemma ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S [iff]:
    shows "ide \<tau> \<longleftrightarrow> \<tau> \<noteq> null \<and> simulation A B (Map \<tau>) \<and>
                     Dom \<tau> = Map \<tau> \<and> Cod \<tau> = Map \<tau>"
    proof
      show "ide \<tau> \<Longrightarrow> \<tau> \<noteq> null \<and> simulation A B (Map \<tau>) \<and>
                      Dom \<tau> = Map \<tau> \<and> Cod \<tau> = Map \<tau>"
        by (metis Dom_resid Map.simps(1) arr_char ideE ide_implies_arr
            null_char transformation_def trg_simp trg_def)
      show "\<tau> \<noteq> null \<and> simulation A B (Map \<tau>) \<and>
            Dom \<tau> = Map \<tau> \<and> Cod \<tau> = Map \<tau>
               \<Longrightarrow> ide \<tau>"
      proof -
        assume 1: "\<tau> \<noteq> null \<and> simulation A B (Map \<tau>) \<and>
                   Dom \<tau> = Map \<tau> \<and> Cod \<tau> = Map \<tau>"
        interpret \<tau>: simulation A B \<open>Map \<tau>\<close>
          using 1 by blast
        interpret \<tau>: simulation_as_transformation A B \<open>Map \<tau>\<close> ..
        show "ide \<tau>"
          by (metis 1 Cod.elims Dom.simps(1) Map.simps(1)
              \<tau>.transformation_axioms arr_char arr_def ide_def null_char
              trg_simp trg_def)
      qed
    qed

    sublocale rts resid
    proof
      show "\<And>t. arr t \<Longrightarrow> ide (trg t)"
        using arr_char ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S trg_simp
        by (metis (full_types) Cod.simps(1) arr.simps(2) con_def con_imp_arr_resid
          con_implies_arr(2) ide_def null_char trg_def)
      show "\<And>a t. \<lbrakk>ide a; t \<frown> a\<rbrakk> \<Longrightarrow> t \\ a = t"
      proof -
        fix a t
        assume a: "ide a"
        assume con: "t \<frown> a"
        interpret a: identity_transformation A B \<open>Dom a\<close> \<open>Cod a\<close> \<open>Map a\<close>
          using a ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S
          by (metis con con_char identity_transformation_axioms_def
              identity_transformation_def simulation.preserves_ide)
        interpret t: transformation A B \<open>Dom a\<close> \<open>Cod t\<close> \<open>Map t\<close>
           using con con_char by metis
        have "t \\ a = MkArr (Cod a) (Apex t a)
                             (\<lambda>ta. if A.arr ta
                                   then (Map t (A.src ta) \\\<^sub>B Map a (A.src ta)) \<squnion>\<^sub>B
                                          Cod a ta
                                   else B.null)"
          using con ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S con_char resid_def Apex_def
          by simp metis
        moreover have "Apex t a = Cod t"
        proof -
          have "(\<lambda>u. if A.arr u
                     then Cod a u \\\<^sub>B (Map t (A.src u) \\\<^sub>B Map a (A.src u))
                     else B.null) =
                Cod t"
          proof
            fix u
            show "(if A.arr u
                   then Cod a u \\\<^sub>B (Map t (A.src u) \\\<^sub>B Map a (A.src u))
                   else B.null) =
                  Cod t u"
              by (metis A.src_src A.trg_src a a.src_eq_trg ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S
                  t.G.extensional t.naturality1 t.naturality2)
          qed
          thus ?thesis
            using a con ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S con_char Apex_def by simp
        qed
        moreover have "(\<lambda>u. if A.arr u
                            then Map t (A.src u) \\\<^sub>B Map a (A.src u) \<squnion>\<^sub>B Cod a u
                            else B.null) =
                       Map t"
        proof
          fix u
          show "(if A.arr u
                 then Map t (A.src u) \\\<^sub>B Map a (A.src u) \<squnion>\<^sub>B Cod a u
                 else B.null) =
                Map t u"
            by (metis (full_types) A.arr_src_iff_arr A.ide_src A.src_src
                B.join_is_join_of B.join_of_unique B.joinable_def B.resid_arr_src
                a ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S t.naturality3 t.preserves_arr t.preserves_src
                t.transformation_axioms transformation.extensional)
        qed
        ultimately show "t \\ a = t"
          using con con_char
          by (metis Cod.elims Dom.simps(1) Map.simps(1) a.src_eq_trg)
      qed
      thus "\<And>a t. \<lbrakk>ide a; a \<frown> t\<rbrakk> \<Longrightarrow> ide (a \\ t)"
        by (metis arrE arr_resid con_sym cube ideE ideI)
      show "\<And>t u. t \<frown> u \<Longrightarrow> \<exists>a. ide a \<and> a \<frown> t \<and> a \<frown> u"
      proof -
        fix t u
        assume con: "t \<frown> u"
        interpret t: transformation A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
          using con con_char by blast
        interpret u: transformation A B \<open>Dom t\<close> \<open>Cod u\<close> \<open>Map u\<close>
          using con con_char by auto
        interpret Dom_t: transformation A B \<open>Dom t\<close> \<open>Dom t\<close> \<open>Dom t\<close>
          by (metis Cod.simps(1) Dom.simps(1) Map.simps(1) arr.simps(2)
              arr_char ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S ide_implies_arr null_char
              t.F.simulation_axioms)
        interpret Dom_t: identity_transformation A B \<open>Dom t\<close> \<open>Dom t\<close> \<open>Dom t\<close>
          by unfold_locales auto
        have "ide (MkIde (Dom t))"
          by (simp add: null_char t.F.simulation_axioms)
        moreover have "MkIde (Dom t) \<frown> t"
          using con con_char Dom_t.transformation_axioms Dom_t.identity
                t.transformation_axioms
          by simp
             (metis A.ide_iff_src_self A.ide_implies_arr B.not_ide_null
               B.conI t.G.preserves_ide t.naturality2)
        moreover have "MkIde (Dom t) \<frown> u"
          using con con_char Dom_t.transformation_axioms Dom_t.identity
                u.transformation_axioms
          by simp
             (metis A.ide_iff_src_self A.ide_implies_arr B.not_ide_null
               B.conI u.G.preserves_ide u.naturality2)
        ultimately show "\<exists>a. ide a \<and> a \<frown> t \<and> a \<frown> u" by blast
      qed
      show "\<And>t u v. \<lbrakk>ide (t \\ u); u \<frown> v\<rbrakk> \<Longrightarrow> t \\ u \<frown> v \\ u"
        by (metis (no_types, opaque_lifting) Dom_resid conI con_implies_arr(1)
            cube ideE resid_arr_self conE con_imp_arr_resid trg_simp)
    qed

    lemma is_rts:
    shows "rts resid"
      ..

    sublocale extensional_rts resid
    proof
      fix t u
      assume cong: "cong t u"
      interpret t: transformation A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
        using cong con_char prfx_implies_con by blast
      interpret u: transformation A B \<open>Dom t\<close> \<open>Cod u\<close> \<open>Map u\<close>
        using cong con_char prfx_implies_con by metis
      interpret tu: transformation A B \<open>Cod u\<close> \<open>Apex t u\<close> \<open>Map (t \ u)\<close>
        using cong transformation_Map_resid
        by (metis con_char prfx_implies_con)
      interpret tu: identity_transformation A B \<open>Cod u\<close> \<open>Apex t u\<close> \<open>Map (t \ u)\<close>
        by unfold_locales (meson ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S cong simulation.preserves_ide)
      interpret ut: transformation A B \<open>Cod t\<close> \<open>Apex t u\<close> \<open>Map (u \ t)\<close>
        using cong transformation_Map_resid Apex_sym
        by (metis con_char prfx_implies_con)
      interpret ut: identity_transformation A B \<open>Cod t\<close> \<open>Apex t u\<close> \<open>Map (u \ t)\<close>
        by unfold_locales (meson ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S cong simulation.preserves_ide)
      have 1: "\<And>a. A.ide a \<Longrightarrow> Map t a = Map u a"
        by (metis B.cong_char Map_resid_ide congE cong tu.identity ut.identity)
      show "t = u"
        using t.transformation_axioms u.transformation_axioms
              transformation_eqI
        by (metis (no_types, lifting) "1" B.extensional_rts_axioms Cod.elims
            Dom.simps(1) Map.simps(1) resid_def cong not_ide_null null_char
            tu.src_eq_trg ut.src_eq_trg)
    qed

    lemma is_extensional_rts:
    shows "extensional_rts resid"
      ..

    lemma conI\<^sub>E\<^sub>R\<^sub>T\<^sub>S [intro]:
    assumes "coinitial \<sigma> \<tau>"
    and "\<And>a. A.ide a \<Longrightarrow> Map \<sigma> a \<frown>\<^sub>B Map \<tau> a"
    shows "\<sigma> \<frown> \<tau>"
      using assms con_char
      by (metis (full_types) coinitialE\<^sub>W\<^sub>E con_arr_src(1))

    lemma conE\<^sub>E\<^sub>R\<^sub>T\<^sub>S [elim]:
    assumes "\<sigma> \<frown> \<tau>"
    and "\<lbrakk>coinitial \<sigma> \<tau>; \<And>t u. A.con t u \<Longrightarrow> Map \<sigma> t \<frown>\<^sub>B Map \<tau> u\<rbrakk> \<Longrightarrow> T"
    shows T
      by (metis A.arr_resid_iff_con B.arr_resid_iff_con arr_char
          arr_resid_iff_con assms(1) assms(2) con_imp_coinitial resid_Map
          transformation.preserves_arr)

    lemma arrI [intro]:
    assumes "f \<noteq> null" and "transformation A B (Dom f) (Cod f) (Map f)"
    shows "arr f"
      using assms arr_char null_char by simp

    lemma arrE [elim]:
    assumes "arr f"
    and "\<lbrakk>f \<noteq> null; transformation A B (Dom f) (Cod f) (Map f)\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms arr_char null_char by simp

    lemma arr_MkArr [iff]:
    shows "arr (MkArr F G \<tau>) \<longleftrightarrow> transformation A B F G \<tau>"
      using arr_char null_char transformation_def by fastforce

    lemma src_simp:
    assumes "arr \<tau>"
    shows "src \<tau> = MkIde (Dom \<tau>)"
      by (metis Dom_resid arr_src_iff_arr assms con_arr_src(1) resid_arr_src
          trg_simp trg_src)

    lemma src_char:
    shows "src = (\<lambda>\<tau>. if arr \<tau> then MkIde (Dom \<tau>) else null)"
      using src_simp src_def by auto

    lemma Map_src [simp]:
    assumes "arr \<tau>"
    shows "Map (src \<tau>) = Dom \<tau>"
      using assms src_simp by auto

    lemma ide_MkIde [iff]:
    shows "ide (MkIde F) \<longleftrightarrow> simulation A B F"
      using ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S null_char by auto

    (* TODO: This is pretty trivial, but sledgehammer typically has trouble finding this fact. *)
    lemma MkArr_Map:
    assumes "\<tau> \<noteq> Null"
    shows "\<tau> = MkArr (Dom \<tau>) (Cod \<tau>) (Map \<tau>)"
      using assms by (cases \<tau>) auto

    lemma MkIde_Dom:
    assumes "arr \<tau>"
    shows "MkIde (Dom \<tau>) = src \<tau>"
      using assms arr_char src_char by auto

    lemma MkIde_Cod:
    assumes "arr \<tau>"
    shows "MkIde (Cod \<tau>) = trg \<tau>"
      using assms arr_char trg_char by auto

    lemma MkIde_Map:
    assumes "ide a"
    shows "MkIde (Map a) = a"
      using assms trg_char trg_ide by auto

    lemma arr_eqI:
    assumes "arr \<sigma>" and "arr \<tau>" and "Dom \<sigma> = Dom \<tau>" and "Cod \<sigma> = Cod \<tau>"
    and "\<And>a. A.ide a \<Longrightarrow> Map \<sigma> a = Map \<tau> a"
    shows "\<sigma> = \<tau>"
    proof -
      interpret \<sigma>: transformation A B \<open>Dom \<sigma>\<close> \<open>Cod \<sigma>\<close> \<open>Map \<sigma>\<close>
        using assms(1) by blast
      interpret \<sigma>: transformation_to_extensional_rts A B
                     \<open>Dom \<sigma>\<close> \<open>Cod \<sigma>\<close> \<open>Map \<sigma>\<close> ..
      interpret \<tau>: transformation A B \<open>Dom \<tau>\<close> \<open>Cod \<tau>\<close> \<open>Map \<tau>\<close>
        using assms(2) by blast
      interpret \<tau>: transformation_to_extensional_rts A B
                     \<open>Dom \<tau>\<close> \<open>Cod \<tau>\<close> \<open>Map \<tau>\<close> ..
      have "Map \<sigma> = Map \<tau>"
        by (metis assms(3-5) B.extensional_rts_axioms \<sigma>.transformation_axioms
            \<tau>.transformation_axioms transformation_eqI)
      thus ?thesis
        using assms
        by (metis MkArr_Map arr_char)
    qed

    lemma seq_char:
    shows "seq \<sigma> \<tau> \<longleftrightarrow> Arr \<sigma> \<and> Arr \<tau> \<and> Cod \<sigma> = Dom \<tau>"
      using arr_char src_char trg_char
      by (metis (no_types, lifting) Map_src Map_trg seqE\<^sub>W\<^sub>E seqI\<^sub>W\<^sub>E(1))

    notation prfx  (infix "\<lesssim>" 50)

    lemma prfx_char:
    shows "\<sigma> \<lesssim> \<tau> \<longleftrightarrow> arr \<sigma> \<and> arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and>
                     (\<forall>a. A.ide a \<longrightarrow> Map \<sigma> a \<lesssim>\<^sub>B Map \<tau> a)"
    proof
      show "\<sigma> \<lesssim> \<tau> \<Longrightarrow> arr \<sigma> \<and> arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and>
                      (\<forall>a. A.ide a \<longrightarrow> Map \<sigma> a \<lesssim>\<^sub>B Map \<tau> a)"
        by (metis Map_resid_ide con_char con_implies_arr(1-2) ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S
            prfx_implies_con simulation.preserves_ide)
      show "arr \<sigma> \<and> arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and>
            (\<forall>a. A.ide a \<longrightarrow> Map \<sigma> a \<lesssim>\<^sub>B Map \<tau> a) \<Longrightarrow> \<sigma> \<lesssim> \<tau>"
      proof -
        assume 1: "arr \<sigma> \<and> arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and>
                   (\<forall>a. A.ide a \<longrightarrow> Map \<sigma> a \<lesssim>\<^sub>B Map \<tau> a)"
        have 2: "\<sigma> \<frown> \<tau>"
          using 1 con_char arr_char B.prfx_implies_con by force
        interpret \<sigma>\<tau>: transformation A B \<open>Cod \<tau>\<close> \<open>Apex \<sigma> \<tau>\<close> \<open>Map (\<sigma> \ \<tau>)\<close>
          using 2 con_char transformation_Map_resid by auto
        interpret \<sigma>\<tau>: simulation A B \<open>Map (\<sigma> \ \<tau>)\<close>
        proof
          show "\<And>t. \<not> A.arr t \<Longrightarrow> Map (\<sigma> \\ \<tau>) t = B.null"
            using \<sigma>\<tau>.extensional by blast
          show 3: "\<And>t u. t \<frown>\<^sub>A u \<Longrightarrow> Map (\<sigma> \\ \<tau>) t \<frown>\<^sub>B Map (\<sigma> \\ \<tau>) u"
            using \<sigma>\<tau>.preserves_con by blast
          show "\<And>t u. t \<frown>\<^sub>A u \<Longrightarrow>
                       Map (\<sigma> \\ \<tau>) (t \\\<^sub>A u) = Map (\<sigma> \\ \<tau>) t \\\<^sub>B Map (\<sigma> \\ \<tau>) u"
            by (metis 1 2 3 A.arr_resid A.con_arr_src(1) A.ide_src A.resid_arr_src
                B.resid_arr_ide arr_resid_iff_con Map_resid_ide resid_Map_self)
        qed
        show "\<sigma> \<lesssim> \<tau>"
        proof
          show "\<sigma> \\ \<tau> \<noteq> null \<and> simulation A B (Map (\<sigma> \\ \<tau>)) \<and>
                Dom (\<sigma> \\ \<tau>) = Map (\<sigma> \\ \<tau>) \<and> Cod (\<sigma> \\ \<tau>) = Map (\<sigma> \\ \<tau>)"
          proof (intro conjI)
            show "\<sigma> \\ \<tau> \<noteq> null"
              using 2 by blast
            show "simulation A B (Map (\<sigma> \\ \<tau>))"
              ..
            show 3: "Dom (\<sigma> \\ \<tau>) = Map (\<sigma> \\ \<tau>)"
            proof -
              have "Dom (\<sigma> \\ \<tau>) = Cod \<tau>"
                using 2 con_char by auto
              also have "... = Map (\<sigma> \\ \<tau>)"
              proof -
                have "\<And>t. A.arr t \<Longrightarrow>
                            Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) = B.src (Cod \<tau> t)"
                  by (metis 1 2 A.ide_src B.src_ide B.src_join_of(1-2) Map_resid_ide
                      \<sigma>\<tau>.naturality3)
                hence "\<And>t. Map (\<sigma> \\ \<tau>) t = Cod \<tau> t"
                  using 1 2 B.join_src \<sigma>\<tau>.F.extensional con_char by auto
                thus ?thesis by auto
              qed
              finally show ?thesis by blast
            qed
            show "Cod (\<sigma> \\ \<tau>) = Map (\<sigma> \\ \<tau>)"
            proof -
              have "Cod (\<sigma> \\ \<tau>) = Apex \<sigma> \<tau>"
                using 2 con_char by auto
              also have "... = Map (\<sigma> \\ \<tau>)"
              proof
                fix t
                show "Apex \<sigma> \<tau> t = Map (\<sigma> \\ \<tau>) t"
                  using 1 Map_resid [of \<sigma> \<tau>]
                  by (metis (no_types, lifting) 2 3 A.con_arr_src(1) A.resid_arr_src
                      Apex_def Dom_resid \<sigma>\<tau>.naturality2 \<sigma>\<tau>.preserves_resid)
              qed
              finally show ?thesis by blast
            qed
          qed
        qed
      qed
    qed

    lemma Map_preserves_prfx:
    assumes "\<sigma> \<lesssim> \<tau>" and "A.arr t"
    shows "Map \<sigma> t \<lesssim>\<^sub>B Map \<tau> t"
      by (metis A.rts_axioms Map_resid_ide assms(1-2) prfx_char resid_Map
          rts.cong_reflexive rts.prfx_implies_con rts_axioms)

subsubsection "Joins in an Exponential RTS"

    notation join  (infix "\<squnion>" 52)

    lemma join_char:
    shows "joinable \<sigma> \<tau> \<longleftrightarrow>
           arr \<sigma> \<and> arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and>
           (\<forall>t. A.arr t \<longrightarrow>
                  B.joinable (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) (Dom \<sigma> t))"
    and "\<sigma> \<squnion> \<tau> =
         (if joinable \<sigma> \<tau>
          then MkArr (Dom \<tau>) (Apex \<sigma> \<tau>)
                     (\<lambda>t. (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<tau> t)
          else null)"
    proof (intro iffI)
      have *: "joinable \<sigma> \<tau> \<Longrightarrow>
                 arr \<sigma> \<and> arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and> \<sigma> \<squnion> \<tau> \<noteq> Null \<and>
                 Dom (\<sigma> \<squnion> \<tau>) = Dom \<sigma> \<and> Cod (\<sigma> \<squnion> \<tau>) = Apex \<sigma> \<tau> \<and>
                 Map (\<sigma> \<squnion> \<tau>) =
                   (\<lambda>t. (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<tau> t) \<and>
                 transformation A B (Dom \<sigma>) (Apex \<sigma> \<tau>) (Map (join \<sigma> \<tau>)) \<and>
                 (\<forall>a. A.ide a \<longrightarrow> B.joinable (Map \<sigma> a \<squnion>\<^sub>B Map \<tau> a) (Dom \<tau> a)) \<and>
                 (\<forall>t. (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<tau> t =
                       Map (\<sigma> \<squnion> \<tau>) t)"
      proof (intro conjI)
        assume 1: "joinable \<sigma> \<tau>"
        show \<sigma>: "arr \<sigma>"
          using 1 con_implies_arr(1) joinable_implies_con by blast
        show \<tau>: "arr \<tau>"
          using 1 con_implies_arr(2) joinable_implies_con by blast
        show "Dom \<sigma> = Dom \<tau>"
          using 1 con_char joinable_implies_con by presburger
        have 2: "join_of \<sigma> \<tau> (\<sigma> \<squnion> \<tau>)"
          using 1 join_is_join_of by simp
        show "\<sigma> \<squnion> \<tau> \<noteq> Null"
          using 1 joinable_iff_join_not_null null_char by force
        show Dom: "Dom (\<sigma> \<squnion> \<tau>) = Dom \<sigma>"
          by (metis (no_types, opaque_lifting) "1" arr_prfx_join_self not_ide_null null_char
              resid_def)
        show Cod: "Cod (\<sigma> \<squnion> \<tau>) = Apex \<sigma> \<tau>"
          using 1 trg_simp Cod_resid trg_join joinable_implies_con arr_resid
          by (metis arr.inject joinable_iff_arr_join)
        interpret \<sigma>\<tau>: transformation A B \<open>Dom \<sigma>\<close> \<open>Apex \<sigma> \<tau>\<close> \<open>Map (\<sigma> \<squnion> \<tau>)\<close>
          using Dom Cod 1 joinable_implies_con con_char arr_char
          by (metis joinable_iff_arr_join)
        interpret \<sigma>\<tau>: transformation_to_extensional_rts A B
                        \<open>Dom \<sigma>\<close> \<open>Apex \<sigma> \<tau>\<close> \<open>Map (\<sigma> \<squnion> \<tau>)\<close> ..
        show "transformation A B (Dom \<sigma>) (Apex \<sigma> \<tau>) (Map (\<sigma> \<squnion> \<tau>))" ..
        have 3: "\<And>a. A.ide a \<Longrightarrow> Map \<sigma> a \<squnion>\<^sub>B Map \<tau> a = Map (\<sigma> \<squnion> \<tau>) a"
        proof (intro B.join_eqI)
          fix a
          assume a: "A.ide a"
          show "Map \<sigma> a \<lesssim>\<^sub>B Map (\<sigma> \<squnion> \<tau>) a"
            using 1 a arr_prfx_join_self prfx_char by blast
          show "Map \<tau> a \<lesssim>\<^sub>B Map (\<sigma> \<squnion> \<tau>) a"
            using join_sym
            by (meson 2 a composite_ofE join_ofE prfx_char)
          show "Map (\<sigma> \<squnion> \<tau>) a \\\<^sub>B Map \<tau> a = Map \<sigma> a \\\<^sub>B Map \<tau> a"
            by (metis 1 2 Map_resid_ide a composite_ofE con_prfx_composite_of(1)
                extensional join_ofE joinable_implies_con con_sym)
          show "Map (\<sigma> \<squnion> \<tau>) a \\\<^sub>B Map \<sigma> a = Map \<tau> a \\\<^sub>B Map \<sigma> a"
            by (metis 1 Map_resid_ide \<open>Dom \<sigma> = Dom \<tau>\<close> \<sigma> \<tau> a arr_prfx_join_self
                join_src joinable_iff_arr_join joinable_implies_con prfx_implies_con
                resid_join\<^sub>E(3) resid_src_arr con_sym src_simp trg_def)
        qed
        show "\<forall>a. A.ide a \<longrightarrow> B.joinable (Map \<sigma> a \<squnion>\<^sub>B Map \<tau> a) (Dom \<tau> a)"
          by (metis 3 A.ide_iff_src_self A.ide_implies_arr \<open>Dom \<sigma> = Dom \<tau>\<close>
              \<sigma>\<tau>.naturality3'\<^sub>E(2))
        show "\<forall>t. (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<tau> t =
                  Map (\<sigma> \<squnion> \<tau>) t"
          by (metis "3" A.ide_src B.joinable_iff_join_not_null B.joinable_implies_con
              B.null_is_zero(2) B.residuation_axioms \<open>Dom \<sigma> = Dom \<tau>\<close>
              \<sigma>\<tau>.F.extensional \<sigma>\<tau>.naturality3'\<^sub>E(1) residuation.conE)
        thus "Map (\<sigma> \<squnion> \<tau>) =
              (\<lambda>t. (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<tau> t)"
          by auto
      qed
      show "\<sigma> \<squnion> \<tau> =
            (if joinable \<sigma> \<tau>
             then MkArr (Dom \<tau>) (Apex \<sigma> \<tau>)
                        (\<lambda>t. (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<tau> t)
             else null)"
        using * MkArr_Map joinable_iff_join_not_null by fastforce
      show "joinable \<sigma> \<tau> \<Longrightarrow>
              arr \<sigma> \<and> arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and>
              (\<forall>t. A.arr t \<longrightarrow>
                     B.joinable (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) (Dom \<sigma> t))"
        using *
        by (metis (no_types, lifting) B.joinable_iff_arr_join transformation.preserves_arr)
      show "arr \<sigma> \<and> arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and>
            (\<forall>t. A.arr t \<longrightarrow>
                   B.joinable (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) (Dom \<sigma> t))
               \<Longrightarrow> joinable \<sigma> \<tau>"
      proof -
        assume 1: "arr \<sigma> \<and> arr \<tau> \<and> Dom \<sigma> = Dom \<tau> \<and>
                   (\<forall>t. A.arr t \<longrightarrow>
                          B.joinable (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) (Dom \<sigma> t))"
        interpret \<sigma>: transformation A B \<open>Dom \<sigma>\<close> \<open>Cod \<sigma>\<close> \<open>Map \<sigma>\<close>
          using 1 arr_char by blast
        interpret \<tau>: transformation A B \<open>Dom \<sigma>\<close> \<open>Cod \<tau>\<close> \<open>Map \<tau>\<close>
          using 1 arr_char by auto
        interpret Apex: simulation A B \<open>Apex \<sigma> \<tau>\<close>
          using 1 arr_char Apex_is_simulation
          by (metis A.ide_iff_src_self A.ide_implies_arr B.con_implies_arr(1)
              B.joinable_iff_join_not_null B.joinable_implies_con B.not_arr_null)
        let ?Map = "\<lambda>a. Map \<sigma> a \<squnion>\<^sub>B Map \<tau> a"
        interpret \<sigma>\<tau>: transformation_by_components
                        A B \<open>Dom \<sigma>\<close> \<open>Apex \<sigma> \<tau>\<close> ?Map
        proof
          show 2: "\<And>a. A.ide a \<Longrightarrow> B.src (?Map a) = Dom \<sigma> a"
            by (metis (full_types) 1 A.ide_implies_arr A.src_ide B.join_sym
                B.joinable_iff_join_not_null B.src_join B.src_src \<sigma>.preserves_src)
          show "\<And>a. A.ide a \<Longrightarrow> B.trg (?Map a) = Apex \<sigma> \<tau> a"
            by (metis (full_types) 2 A.ide_iff_src_self A.ide_implies_arr Apex_def
                B.con_arr_src(2) B.joinable_iff_arr_join B.joinable_iff_join_not_null
                B.not_ide_null B.null_is_zero(2) B.resid_join\<^sub>E(1) B.resid_src_arr
                B.src_trg B.trg_def \<sigma>.F.preserves_ide \<tau>.naturality2)
          show "\<And>t. A.arr t \<Longrightarrow>
                      (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \\\<^sub>B Dom \<sigma> t =
                      Map \<sigma> (A.trg t) \<squnion>\<^sub>B Map \<tau> (A.trg t)"
            by (metis (full_types) 1 B.conE B.conI B.con_sym_ax B.join_def
                B.joinable_implies_con B.null_is_zero(2) B.resid_join\<^sub>E(3)
                \<sigma>.naturality1 \<tau>.naturality1)
          show "\<And>t. A.arr t \<Longrightarrow>
                      Dom \<sigma> t \\\<^sub>B (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) = Apex \<sigma> \<tau> t"
            by (metis 1 Apex_def B.con_implies_arr(2) B.joinable_implies_con
                \<tau>.naturality2 B.joinable_iff_arr_join B.resid_join\<^sub>E(1) B.con_sym)
          show "\<And>t. A.arr t \<Longrightarrow>
                       B.joinable (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) (Dom \<sigma> t)"
            using 1 by blast
        qed
        let ?Cod_\<sigma>\<tau> = "\<lambda>t. if A.arr t
                           then Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))
                           else B.null"
        let ?Map_\<sigma>\<tau> = "\<lambda>t. if A.arr t
                           then (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<sigma> t
                           else B.null"
        have \<sigma>\<tau>': "transformation A B (Dom \<tau>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>"
          using 1 Apex_def \<sigma>\<tau>.map_eq \<sigma>\<tau>.transformation_axioms by presburger
        let ?\<sigma>\<tau> = "MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map"
        have \<sigma>\<tau>: "arr ?\<sigma>\<tau>"
          using arr_char \<sigma>\<tau>.transformation_axioms by blast
        have con_\<sigma>_\<sigma>\<tau>: "\<sigma> \<frown> ?\<sigma>\<tau>"
          using 1 con_char \<sigma>.transformation_axioms \<sigma>\<tau>.transformation_axioms
            \<sigma>\<tau>.map_simp_ide
          by auto
             (metis (no_types, lifting) A.ide_implies_arr B.arr_prfx_join_self
              B.joinable_iff_join_not_null B.not_arr_null B.prfx_implies_con
              transformation.preserves_arr)
        have con_\<tau>_\<sigma>\<tau>: "\<tau> \<frown> ?\<sigma>\<tau>"
          using 1 con_char \<tau>.transformation_axioms \<sigma>\<tau>.transformation_axioms
            \<sigma>\<tau>.map_simp_ide
          by auto
             (metis (no_types, lifting) A.ide_implies_arr B.arr_prfx_join_self B.conI
              B.join_sym B.joinable_iff_join_not_null B.not_arr_null B.not_ide_null
              transformation.preserves_arr)
        have 4: "Apex \<sigma> ?\<sigma>\<tau> = Apex \<sigma> \<tau>"
        proof
          fix t
          have "A.arr t \<Longrightarrow>
                  (Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))) \\\<^sub>B
                     (Map \<sigma> (A.src t) \\\<^sub>B (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t))) =
                   Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
          proof -
            assume t: "A.arr t"
            have 4: "Map \<sigma> (A.src t) \<lesssim>\<^sub>B
                     (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<tau> (A.src t)"
              using t 1 B.arr_prfx_join_self B.joinable_iff_join_not_null \<sigma>\<tau>.map_def
                    \<sigma>\<tau>.map_simp_ide
              by (metis (no_types, lifting) A.arr_src_iff_arr A.ide_src A.src_src)
            have "Map \<sigma> (A.src t) \\\<^sub>B
                    ((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<tau> (A.src t)) =
                  B.src (Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t)))"
              by (metis (no_types, lifting) 1 4 A.ide_src A.src_src
                  Apex.preserves_reflects_arr B.ide_iff_src_self B.ide_implies_arr
                  B.not_arr_null B.src_resid \<sigma>\<tau>.map_def \<sigma>\<tau>.map_simp_ide \<sigma>\<tau>.naturality2
                  Apex_def B.conI t)
            thus "(Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))) \\\<^sub>B
                     (Map \<sigma> (A.src t) \\\<^sub>B (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t))) =
                  Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
              by (metis (no_types, lifting) 1 4 A.ide_src A.src_src B.arr_src_iff_arr
                  B.prfx_implies_con B.resid_arr_src \<sigma>\<tau>.map_def \<sigma>\<tau>.map_simp_ide
                  B.arr_resid t)
          qed
          thus "Apex \<sigma> ?\<sigma>\<tau> t = Apex \<sigma> \<tau> t"
            unfolding Apex_def by simp
        qed
        have 5: "Apex \<tau> ?\<sigma>\<tau> = Apex \<sigma> \<tau>"
        proof
          fix t
          have "A.arr t \<Longrightarrow>
                  (Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))) \\\<^sub>B
                     (Map \<tau> (A.src t) \\\<^sub>B (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t))) =
                  Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
          proof -
            assume t: "A.arr t"
            show "(Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))) \\\<^sub>B
                     (Map \<tau> (A.src t) \\\<^sub>B (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t))) =
                  Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
            proof -
              have "Map \<tau> (A.src t) \\\<^sub>B (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) =
                    B.src (Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t)))"
              proof -
                have "Map \<tau> (A.src t) \\\<^sub>B (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) =
                      (Map \<tau> (A.src t) \\\<^sub>B Map \<tau> (A.src t)) \\\<^sub>B
                        (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
                  by (metis (no_types, lifting) 1 A.arr_src_if_arr A.ide_src
                      B.arr_prfx_join_self B.join_sym B.joinable_iff_join_not_null
                      B.prfx_implies_con B.resid_join\<^sub>E(1) \<sigma>\<tau>.map_def \<sigma>\<tau>.map_simp_ide
                      t)
                also have "... = B.trg (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
                  using B.apex_sym B.cube B.trg_def by auto
                also have
                    "... = B.src (Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t)))"
                  by (metis Apex.preserves_reflects_arr Apex_def B.arr_resid_iff_con
                      B.src_resid t)
                finally show ?thesis by blast
              qed
              thus ?thesis
                by (metis B.arr_resid_iff_con B.con_def B.con_implies_arr(1)
                    B.resid_arr_src)
            qed
          qed
          thus "Apex \<tau> ?\<sigma>\<tau> t = Apex \<sigma> \<tau> t"
            unfolding Apex_def by simp
        qed
        have "\<sigma> \<squnion> \<tau> = MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map"
        proof (intro join_eqI)
          show "\<sigma> \<lesssim> MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map"
          proof -
            have "\<sigma> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map = trg ?\<sigma>\<tau>"
            proof -
              have "Dom (\<sigma> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) = Dom (trg ?\<sigma>\<tau>)"
                using \<sigma>\<tau> con_\<sigma>_\<sigma>\<tau> trg_simp by fastforce
              moreover
              have "Cod (\<sigma> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) = Cod (trg ?\<sigma>\<tau>)"
                using \<sigma>\<tau> 4 con_\<sigma>_\<sigma>\<tau> trg_simp by fastforce
              moreover
              have "Map (\<sigma> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) = Map (trg ?\<sigma>\<tau>)"
              proof -
                have "Map (\<sigma> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) = Apex \<sigma> \<tau>"
                proof
                  fix t
                  show "Map (\<sigma> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) t =
                        Apex \<sigma> \<tau> t"
                  proof (cases "A.arr t")
                    show "\<not> A.arr t \<Longrightarrow> ?thesis"
                      by (simp add: Apex.extensional con_\<sigma>_\<sigma>\<tau>)
                    assume t: "A.arr t"
                    have "Map \<sigma> (A.src t) \\\<^sub>B
                            (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Apex \<sigma> \<tau> t =
                          Apex \<sigma> \<tau> t"
                      by (metis Apex.preserves_reflects_arr B.arr_prfx_join_self
                          B.arr_resid_iff_con B.con_implies_arr(2) B.con_target
                          B.join_prfx(1) B.joinable_iff_arr_join
                          B.joinable_implies_con B.resid_ide_arr \<sigma>\<tau>.joinable
                          \<sigma>\<tau>.naturality2 t)
                    thus ?thesis
                      by (simp add: con_\<sigma>_\<sigma>\<tau> t)
                  qed
                qed
                thus ?thesis
                  using \<sigma>\<tau> trg_simp by force
              qed
              ultimately show ?thesis
                using \<sigma>\<tau> con_\<sigma>_\<sigma>\<tau> resid_def' trg_simp by fastforce
            qed
            thus ?thesis
              using \<sigma>\<tau> ide_trg by presburger
          qed
          show "\<tau> \<lesssim> MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map"
          proof -
            have "\<tau> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map = trg ?\<sigma>\<tau>"
            proof -
              have "Dom (\<tau> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) = Dom (trg ?\<sigma>\<tau>)"
                using \<sigma>\<tau> con_\<tau>_\<sigma>\<tau> trg_def by fastforce
              moreover have "Cod (\<tau> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) =
                             Cod (trg ?\<sigma>\<tau>)"
                using \<sigma>\<tau> 5 Cod.simps(1) Cod_resid con_\<tau>_\<sigma>\<tau> trg_simp by presburger
              moreover have "Map (\<tau> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) =
                             Map (trg ?\<sigma>\<tau>)"
              proof -
                have "Map (\<tau> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) = Apex \<sigma> \<tau>"
                proof
                  fix t
                  show "Map (\<tau> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) t =
                        Apex \<sigma> \<tau> t"
                  proof (cases "A.arr t")
                    show "\<not> A.arr t \<Longrightarrow> ?thesis"
                      by (simp add: Apex.extensional con_\<tau>_\<sigma>\<tau>)
                    assume t: "A.arr t"
                    have "Map (\<tau> \\ MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map) t =
                          Map \<tau> (A.src t) \\\<^sub>B \<sigma>\<tau>.map (A.src t) \<squnion>\<^sub>B Apex \<sigma> \<tau> t"
                      using \<sigma>\<tau> Map_resid
                      by (simp add: con_\<tau>_\<sigma>\<tau> t)
                    also have "... = Map \<tau> (A.src t) \\\<^sub>B
                                       ((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B
                                           Dom \<sigma> (A.src t))
                                        \<squnion>\<^sub>B Apex \<sigma> \<tau> t"
                      using t \<sigma>\<tau>.map_def by simp
                    also have "... = ((Map \<tau> (A.src t) \\\<^sub>B
                                         (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t))) \\\<^sub>B
                                         (Dom \<sigma> (A.src t) \\\<^sub>B
                                            (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t))))
                                         \<squnion>\<^sub>B Apex \<sigma> \<tau> t"
                      by (metis (no_types, lifting) t A.arr_src_iff_arr
                          A.ide_src A.src_src A.trg_src B.cube \<sigma>\<tau>.map_def
                          \<sigma>\<tau>.map_simp_ide \<sigma>\<tau>.naturality1 \<tau>.naturality1)
                    also have "... = (((Map \<tau> (A.src t) \\\<^sub>B Map \<tau> (A.src t)) \\\<^sub>B
                                         (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))) \\\<^sub>B
                                        (Dom \<sigma> (A.src t) \\\<^sub>B
                                           (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t))))
                                         \<squnion>\<^sub>B Apex \<sigma> \<tau> t"
                      by (metis (no_types, lifting) A.arr_src_iff_arr A.ide_src
                          B.arr_prfx_join_self B.join_sym
                          B.joinable_iff_join_not_null B.not_arr_null
                          B.prfx_implies_con B.resid_join\<^sub>E(1) \<sigma>\<tau>.map_simp_ide
                          \<sigma>\<tau>.preserves_arr t)
                    also have "... = ((Cod \<tau> (A.src t) \\\<^sub>B
                                         (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))) \\\<^sub>B
                                        (Dom \<sigma> (A.src t) \\\<^sub>B
                                           (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t))))
                                         \<squnion>\<^sub>B Apex \<sigma> \<tau> t"
                      by (simp add: t \<tau>.preserves_trg B.resid_arr_self)
                    also have "... = (Apex \<sigma> \<tau> (A.src t) \\\<^sub>B
                                        (Dom \<sigma> (A.src t) \\\<^sub>B
                                           (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t))))
                                         \<squnion>\<^sub>B Apex \<sigma> \<tau> t"
                      by (simp add: Apex_def \<tau>.G.extensional)
                    also have "... = (Apex \<sigma> \<tau> (A.src t) \\\<^sub>B Apex \<sigma> \<tau> (A.src t)) \<squnion>\<^sub>B
                                        Apex \<sigma> \<tau> t"
                      by (metis A.arr_src_iff_arr A.src_src \<sigma>\<tau>.naturality2 t)
                    also have "... = Apex \<sigma> \<tau> (A.src t) \<squnion>\<^sub>B Apex \<sigma> \<tau> t"
                      by (metis A.ideE A.ide_src Apex.preserves_resid t)
                    also have "... = Apex \<sigma> \<tau> t"
                      by (metis A.ide_src Apex.preserves_reflects_arr
                          B.arr_resid_iff_con B.join_src B.src_resid \<sigma>\<tau>.naturality2
                          \<sigma>\<tau>.preserves_trg t)
                    finally show ?thesis by blast
                  qed
                qed
                thus ?thesis
                  using \<sigma>\<tau> trg_simp by force
              qed
              ultimately show ?thesis
                using \<sigma>\<tau> con_\<tau>_\<sigma>\<tau> resid_def' trg_simp by fastforce
            qed
            thus ?thesis
              using \<sigma>\<tau> ide_trg by presburger
          qed
          have 5: "\<And>a. A.ide a \<Longrightarrow> Map \<sigma> a \<frown>\<^sub>B Map \<tau> a"
            by (metis A.ide_iff_src_self B.not_ide_null B.null_is_zero(2)
                B.residuation_axioms Apex.preserves_ide Apex_def residuation.con_def)
          have 6: "\<forall>a. A.ide a \<longrightarrow>
                         (Map \<sigma> a \<squnion>\<^sub>B Map \<tau> a) \<squnion>\<^sub>B Dom \<tau> a \<frown>\<^sub>B Map \<sigma> a"
            by (metis (no_types, lifting) "1" A.ide_iff_src_self
                B.arr_prfx_join_self B.conI B.con_sym B.join_def B.not_arr_null
                B.prfx_implies_con B.src_def \<sigma>.F.preserves_ide \<sigma>\<tau>.map_eq
                \<sigma>\<tau>.map_simp_ide \<sigma>\<tau>.preserves_src)
          show "MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map \\ \<tau> = \<sigma> \\ \<tau>"
          proof -
            have "\<And>a. A.ide a \<Longrightarrow>
                        (Map \<sigma> a \<squnion>\<^sub>B Map \<tau> a) \<squnion>\<^sub>B Dom \<tau> a \<frown>\<^sub>B Map \<tau> a"
              using B.con_sym \<sigma>\<tau>.map_def con_\<tau>_\<sigma>\<tau> con_char by force
            moreover
            have "transformation A B (Dom \<tau>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>"
              using \<sigma>\<tau>' by simp
            moreover
            have "(\<lambda>t. if A.arr t
                       then Cod \<tau> t \\\<^sub>B
                              (Map (MkArr (Dom \<sigma>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>) (A.src t) \\\<^sub>B
                                 Map \<tau> (A.src t))
                       else B.null) =
                  ?Cod_\<sigma>\<tau>"
            proof
              fix t
              show "(if A.arr t
                     then Cod \<tau> t \\\<^sub>B
                            (Map (MkArr (Dom \<sigma>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>) (A.src t) \\\<^sub>B
                               Map \<tau> (A.src t))
                     else B.null) =
                    (if A.arr t
                     then Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))
                     else B.null)"
              proof -
                have "A.arr t \<Longrightarrow>
                        Cod \<tau> t \\\<^sub>B
                          (((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<sigma> (A.src t))
                              \\\<^sub>B Map \<tau> (A.src t)) =
                        Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
                proof -
                  assume t: "A.arr t"
                  show "Cod \<tau> t \\\<^sub>B
                          (((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<sigma> (A.src t))
                              \\\<^sub>B Map \<tau> (A.src t)) =
                        Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
                  proof -
                    have "Cod \<tau> t \\\<^sub>B
                            (((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<sigma> (A.src t))
                                 \\\<^sub>B Map \<tau> (A.src t)) =
                          Cod \<tau> t \\\<^sub>B
                            ((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \\\<^sub>B
                                Map \<tau> (A.src t))"
                      using \<sigma>\<tau>.map_def \<sigma>\<tau>.map_simp_ide t by force
                    also have "... = Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B
                                                    Map \<tau> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
                      by (metis 1 B.arr_prfx_join_self B.conE B.con_sym_ax B.join_def
                          B.join_sym B.null_is_zero(2) B.prfx_implies_con
                          B.resid_join\<^sub>E(3) t)
                    also have "... = Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B
                                                    Cod \<tau> (A.src t))"
                      using A.ide_src A.trg_src B.trg_def \<tau>.preserves_trg t by presburger
                    also have "... = Cod \<tau> t \\\<^sub>B (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t))"
                      by (metis 5 A.ide_src B.arr_resid_iff_con B.join_src B.join_sym
                          B.src_resid \<tau>.preserves_trg t)
                    finally show ?thesis by blast
                  qed
                qed
                thus ?thesis by auto
              qed
            qed
            moreover
            have "(\<lambda>t. if A.arr t
                       then (Map (MkArr (Dom \<sigma>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>) (A.src t) \\\<^sub>B
                               Map \<tau> (A.src t))
                              \<squnion>\<^sub>B Cod \<tau> t
                       else B.null) =
                  (\<lambda>t. if A.arr t
                       then Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t
                       else B.null)"
            proof
              fix t
              show "(if A.arr t
                     then Map (MkArr (Dom \<sigma>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>) (A.src t) \\\<^sub>B
                            Map \<tau> (A.src t)
                            \<squnion>\<^sub>B Cod \<tau> t
                     else B.null) =
                    (if A.arr t
                     then Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t
                     else B.null)"
              proof -
                have "A.arr t \<Longrightarrow>
                        ((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B
                            Dom \<sigma> (A.src t)) \\\<^sub>B
                          Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t =
                        Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t"
                proof -
                  assume t: "A.arr t"
                  show "((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B
                            Dom \<sigma> (A.src t)) \\\<^sub>B
                          Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t =
                        Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t"
                  proof -
                    have "((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B
                             Dom \<sigma> (A.src t)) \\\<^sub>B
                            Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> t =
                           ((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \\\<^sub>B
                              Map \<tau> (A.src t))
                             \<squnion>\<^sub>B Cod \<tau> t"
                      using \<sigma>\<tau>.map_def \<sigma>\<tau>.map_simp_ide t by fastforce
                    also have "... = (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B
                                        Map \<tau> (A.src t) \\\<^sub>B Map \<tau> (A.src t))
                                       \<squnion>\<^sub>B Cod \<tau> t"
                      by (metis 1 B.arr_prfx_join_self B.conE B.con_sym_ax B.join_def
                          B.join_sym B.null_is_zero(2) B.prfx_implies_con B.resid_join\<^sub>E(3)
                          t)
                    also have "... =
                               (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t) \<squnion>\<^sub>B Cod \<tau> (A.src t))
                                  \<squnion>\<^sub>B Cod \<tau> t"
                      by (simp add: \<tau>.preserves_trg B.resid_arr_self t)
                    also have "... = (Map \<sigma> (A.src t) \\\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Cod \<tau> t"
                      by (metis 5 A.ide_src B.arr_resid_iff_con B.join_src B.join_sym
                          B.src_resid \<tau>.preserves_trg t)
                    finally show ?thesis by blast
                  qed
                qed
                thus ?thesis by auto
              qed
            qed
            ultimately show ?thesis
              unfolding resid_def \<sigma>\<tau>.map_eq Apex_def
              using 1 5 arr_char \<sigma>.transformation_axioms
              by auto
          qed
          show "MkArr (Dom \<sigma>) (Apex \<sigma> \<tau>) \<sigma>\<tau>.map \\ \<sigma> = \<tau> \\ \<sigma>"
          proof -
            have "(\<lambda>t. if A.arr t
                       then Cod \<sigma> t \\\<^sub>B
                              (Map (MkArr (Dom \<sigma>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>) (A.src t) \\\<^sub>B
                                 Map \<sigma> (A.src t))
                       else B.null) =
                  (\<lambda>t. if A.arr t
                       then Cod \<sigma> t \\\<^sub>B (Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t))
                       else B.null)"
            proof
              fix t
              show "(if A.arr t
                     then Cod \<sigma> t \\\<^sub>B
                            (Map (MkArr (Dom \<sigma>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>) (A.src t) \\\<^sub>B
                               Map \<sigma> (A.src t))
                     else B.null) =
                    (if A.arr t
                     then Cod \<sigma> t \\\<^sub>B (Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t))
                     else B.null)"
              proof (cases "A.arr t")
                show "\<not> A.arr t \<Longrightarrow> ?thesis"
                  by simp
                assume t: "A.arr t"
                show ?thesis
                proof -
                  have "Cod \<sigma> t \\\<^sub>B
                          (((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B
                               Dom \<sigma> (A.src t)) \\\<^sub>B
                             Map \<sigma> (A.src t)) =
                        Cod \<sigma> t \\\<^sub>B
                          ((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \\\<^sub>B
                              Map \<sigma> (A.src t))"
                    using \<sigma>\<tau>.map_def \<sigma>\<tau>.map_simp_ide t by fastforce
                  also have "... = Cod \<sigma> t \\\<^sub>B
                                     ((Map \<sigma> (A.src t) \\\<^sub>B Map \<sigma> (A.src t)) \<squnion>\<^sub>B
                                        (Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t)))"
                    by (metis 1 B.arr_prfx_join_self B.conE B.con_sym_ax B.join_def
                        B.null_is_zero(2) B.prfx_implies_con B.resid_join\<^sub>E(3) t)
                  also have "... = Cod \<sigma> t \\\<^sub>B
                                     (Cod \<sigma> (A.src t) \<squnion>\<^sub>B
                                        (Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t)))"
                    using A.ide_src A.trg_src B.trg_def \<sigma>.preserves_trg t by presburger
                  also have "... = Cod \<sigma> t \\\<^sub>B (Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t))"
                    by (metis (no_types, lifting) "5" A.ide_src B.arr_resid_iff_con
                        B.conI B.join_src B.src_resid \<sigma>.preserves_trg B.con_sym_ax t)
                  finally show ?thesis by auto
                qed
              qed
            qed
            moreover
            have "(\<lambda>t. if A.arr t
                       then (Map (MkArr (Dom \<sigma>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>) (A.src t) \\\<^sub>B
                                    Map \<sigma> (A.src t))
                              \<squnion>\<^sub>B Cod \<sigma> t
                       else B.null) =
                  (\<lambda>t. if A.arr t
                       then Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t) \<squnion>\<^sub>B Cod \<sigma> t
                       else B.null)"
            proof
              fix t
              show "(if A.arr t
                     then (Map (MkArr (Dom \<sigma>) ?Cod_\<sigma>\<tau> ?Map_\<sigma>\<tau>) (A.src t) \\\<^sub>B
                                  Map \<sigma> (A.src t))
                            \<squnion>\<^sub>B Cod \<sigma> t
                     else B.null) =
                    (if A.arr t
                     then Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t) \<squnion>\<^sub>B Cod \<sigma> t
                     else B.null)"
              proof (cases "A.arr t")
                show "\<not> A.arr t \<Longrightarrow> ?thesis"
                  by simp
                assume t: "A.arr t"
                show ?thesis
                proof -
                  have "(((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B
                             Dom \<sigma> (A.src t)) \\\<^sub>B
                           Map \<sigma> (A.src t)) \<squnion>\<^sub>B Cod \<sigma> t =
                        ((Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \\\<^sub>B
                           Map \<sigma> (A.src t)) \<squnion>\<^sub>B Cod \<sigma> t"
                    using \<sigma>\<tau>.map_def \<sigma>\<tau>.map_simp_ide t by fastforce
                  also have "... = (Map \<sigma> (A.src t) \\\<^sub>B Map \<sigma> (A.src t) \<squnion>\<^sub>B
                                      Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t))
                                      \<squnion>\<^sub>B Cod \<sigma> t"
                    by (metis Apex.preserves_reflects_arr B.arr_prfx_join_self B.conI
                        B.joinable_iff_join_not_null B.not_arr_null B.not_ide_null
                        B.null_is_zero(2) B.resid_join\<^sub>E(3) \<sigma>\<tau>.naturality2 t)
                  also have "... = (Cod \<sigma> (A.src t) \<squnion>\<^sub>B
                                      (Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t)))
                                      \<squnion>\<^sub>B Cod \<sigma> t"
                    using A.ide_src A.trg_src B.trg_def \<sigma>.preserves_trg t
                    by presburger
                  also have "... = (Map \<tau> (A.src t) \\\<^sub>B Map \<sigma> (A.src t)) \<squnion>\<^sub>B Cod \<sigma> t"
                    by (metis (no_types, lifting) "5" A.ide_src B.arr_resid_iff_con
                        B.conI B.join_src B.src_resid \<sigma>.preserves_trg B.con_sym_ax t)
                  finally show ?thesis by auto
                qed
              qed
            qed
            ultimately show ?thesis
              unfolding resid_def \<sigma>\<tau>.map_eq Apex_def
              using 1 5 6 \<sigma>\<tau>' \<sigma>.transformation_axioms arr_char B.con_sym
              by simp
          qed
        qed
        thus "joinable \<sigma> \<tau>"
          by (metis \<sigma>\<tau> joinable_iff_join_not_null not_arr_null)
      qed
    qed

    lemma Dom_join:
    assumes "joinable \<sigma> \<tau>"
    shows "Dom (\<sigma> \<squnion> \<tau>) = Dom \<sigma>"
      using assms join_char by auto

    lemma Cod_join:
    assumes "joinable \<sigma> \<tau>"
    shows "Cod (\<sigma> \<squnion> \<tau>) = Apex \<sigma> \<tau>"
      using assms join_char by auto

    lemma Map_join:
    assumes "joinable \<sigma> \<tau>"
    shows "Map (\<sigma> \<squnion> \<tau>) =
           (\<lambda>t. (Map \<sigma> (A.src t) \<squnion>\<^sub>B Map \<tau> (A.src t)) \<squnion>\<^sub>B Dom \<tau> t)"
      using assms join_char by auto

  end

subsection "Exponential of Small RTS's"

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
        using simulation.extensional by fastforce
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
            singleton_iff transformation.extensional transformation.preserves_arr)
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

  subsection "Exponential into RTS with Composites"

  locale exponential_into_rts_with_composites =
    A: rts A +
    B: rts_with_composites B +
    exponential_rts
  begin

    interpretation B: extensional_rts B ..
    interpretation B: extensional_rts_with_composites B ..

    notation B.comp  (infixr "\<cdot>\<^sub>B" 55)

    abbreviation COMP :: "('a, 'b) arr \<Rightarrow> ('a, 'b) arr \<Rightarrow> ('a, 'b) arr"
    where "COMP t u \<equiv> MkArr (Dom t) (Cod u)
                        (\<lambda>x. Map t (A.src x) \<cdot>\<^sub>B Map u (A.src x) \<squnion>\<^sub>B Dom t x)"

    lemma composite_of_iff:
    shows "composite_of t u v \<longleftrightarrow> seq t u \<and> v = COMP t u"
    proof
      show "\<And>v. seq t u \<and> v = COMP t u \<Longrightarrow> composite_of t u v"
      proof (elim conjE)
        fix v
        assume tu: "seq t u"
        interpret T: transformation A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
          using tu arr_char by blast
        interpret U: transformation A B \<open>Cod t\<close> \<open>Cod u\<close> \<open>Map u\<close>
          using tu arr_char src_simp
          by (metis Map_src Map_trg seqE\<^sub>W\<^sub>E)
        interpret TU: transformation_by_components A B \<open>Dom t\<close> \<open>Cod u\<close>
                        \<open>\<lambda>a. B.comp (Map t a) (Map u a)\<close>
        proof
          show "\<And>a. A.ide a \<Longrightarrow> B.src (B.comp (Map t a) (Map u a)) = Dom t a"
            by (metis A.ide_implies_arr B.rts_with_composites_axioms B.seqI\<^sub>W\<^sub>E(2)
                T.preserves_src T.preserves_trg U.preserves_arr U.preserves_src
                exponential_rts_axioms exponential_rts_def
                extensional_rts_with_composites.src_comp\<^sub>E\<^sub>C
                extensional_rts_with_composites_def)
          show 1: "\<And>a. A.ide a \<Longrightarrow> B.trg (B.comp (Map t a) (Map u a)) = Cod u a"
            by (metis A.ide_implies_arr B.arr_src_iff_arr B.composable_iff_arr_comp
                B.trg_comp T.F.preserves_reflects_arr U.preserves_trg
                \<open>\<And>a. A.ide a \<Longrightarrow> B.src (B.comp (Map t a) (Map u a)) = Dom t a\<close>)
          fix x
          assume x: "A.arr x"
          show "B.comp (Map t (A.src x)) (Map u (A.src x)) \\\<^sub>B Dom t x =
                B.comp (Map t (A.trg x)) (Map u (A.trg x))"
          proof -
            have "B.comp (Map t (A.src x)) (Map u (A.src x)) \\\<^sub>B Dom t x =
                  B.comp (Map t (A.src x) \\\<^sub>B Dom t x)
                         (Map u (A.src x) \\\<^sub>B (Dom t x \\\<^sub>B Map t (A.src x)))"
              by (metis (full_types) 1 A.arr_src_iff_arr A.ide_src B.arr_resid_iff_con
                  B.arr_trg_iff_arr B.comp_def B.con_compI(2) B.not_arr_null
                  T.transformation_axioms U.G.preserves_reflects_arr
                  U.transformation_axioms exponential_rts_axioms exponential_rts_def
                  extensional_rts.resid_comp(2) transformation.naturality2_ax x)
            also have "... = B.comp (Map t (A.trg x)) (Map u (A.trg x))"
              using T.naturality1 T.naturality2 U.naturality1 by presburger
            finally
            show "B.comp (Map t (A.src x)) (Map u (A.src x)) \\\<^sub>B Dom t x =
                  B.comp (Map t (A.trg x)) (Map u (A.trg x))"
              by blast
          qed
          show 1: "Dom t x \\\<^sub>B B.comp (Map t (A.src x)) (Map u (A.src x)) =
                   Cod u x"
            using x
            by (metis A.arr_trg_iff_arr A.ide_trg B.arr_resid_iff_con B.arr_trg_iff_arr
                B.resid_comp(1) T.naturality2 U.G.preserves_reflects_arr U.naturality2
                \<open>B.comp (Map t (A.src x)) (Map u (A.src x)) \\<^sub>B Dom t x =
                 B.comp (Map t (A.trg x)) (Map u (A.trg x))\<close>
                \<open>\<And>a. A.ide a \<Longrightarrow> B.trg (B.comp (Map t a) (Map u a)) = Cod u a\<close>)
          show "B.joinable (B.comp (Map t (A.src x)) (Map u (A.src x))) (Dom t x)"
            using x B.joinable_iff_con
            by (metis 1 B.conI B.con_sym_ax B.not_arr_null
                U.G.preserves_reflects_arr)
        qed
        have "composite_of t u (MkArr (Dom t) (Cod u) TU.map)"
        proof
          have 1: "arr (MkArr (Dom t) (Cod u) TU.map)"
            using arr_char TU.transformation_axioms by blast
          have "src (MkArr (Dom t) (Cod u) TU.map) = src t"
            using 1 tu src_simp
            by (metis (no_types, lifting) Dom.simps(1) seqE\<^sub>W\<^sub>E)
          have 3: "trg (MkArr (Dom t) (Cod u) TU.map) = trg u"
            using 1 trg_simp tu
            by (metis (no_types, lifting) Cod.simps(1) seqE\<^sub>W\<^sub>E)
          have "\<forall>a. A.ide a \<longrightarrow>
                      Map t a \<lesssim>\<^sub>B Map (MkArr (Dom t) (Cod u) TU.map) a"
            using TU.map_simp_ide
            by (metis (no_types, lifting) A.ide_implies_arr B.prfx_comp
                Map.simps(1) TU.preserves_arr)
          thus 2: "t \<lesssim> MkArr (Dom t) (Cod u) TU.map"
            using 1 src_simp tu prfx_char [of t "MkArr (Dom t) (Cod u) TU.map"]
            by auto
          have "MkArr (Dom t) (Cod u) TU.map \\ t = u"
          proof -
            have "Dom (MkArr (Dom t) (Cod u) TU.map \\ t) = Dom u"
              by (metis (mono_tags, lifting) "2" Dom_resid conI con_sym_ax
                  exponential_rts.Map_src exponential_rts.Map_trg
                  exponential_rts.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S exponential_rts_axioms seqE\<^sub>W\<^sub>E tu)
            moreover have "Cod (MkArr (Dom t) (Cod u) TU.map \\ t) = Cod u"
              by (metis (no_types, lifting) "1" "2" Cod.simps(1) Map_trg apex_sym
                  arr_resid conI con_sym_ax not_ide_null src_ide src_resid trg_ide)
            moreover have "Map (MkArr (Dom t) (Cod u) TU.map \\ t) = Map u"
            proof -
              have "\<And>a. A.ide a \<Longrightarrow>
                          Map (MkArr (Dom t) (Cod u) TU.map \\ t) a = Map u a"
                by (metis (no_types, lifting) "2" A.ide_implies_arr B.comp_resid_prfx
                    Map.simps(1) Map_resid_ide TU.map_simp_ide TU.preserves_arr
                    conI con_sym_ax not_ide_null)
              thus ?thesis
                using transformation_eqI
                        [of A B "Dom u" "Cod u"
                            "Map (MkArr (Dom t) (Cod u) TU.map \\ t)" "Map u"]
                      2 arr_char U.transformation_axioms
                by (metis (no_types, lifting) B.extensional_rts_axioms Dom_resid
                    arr_resid calculation(1-2) conI con_sym_ax not_ide_null)
            qed
            ultimately show ?thesis
              using 1
              by (metis (no_types, lifting) "2" MkArr_Map arr_char con_sym_ax
                  not_ide_null null_char seqE\<^sub>W\<^sub>E tu)
          qed
          thus "cong (MkArr (Dom t) (Cod u) TU.map \\ t) u"
            by (metis (full_types) 1 3 ide_trg trg_def)
        qed
        thus "v = COMP t u \<Longrightarrow> composite_of t u v"
          unfolding TU.map_def by blast
      qed
      thus "composite_of t u v \<Longrightarrow> seq t u \<and> v = COMP t u"
        by (metis (no_types, lifting) arrE arr_composite_of comp_is_composite_of(2)
            composable_imp_seq comp_def)
    qed

    corollary is_rts_with_composites:
    shows "rts_with_composites resid"
      using composite_of_iff composable_def
      by unfold_locales auto

    sublocale rts_with_composites resid
      using is_rts_with_composites by blast
    sublocale extensional_rts_with_composites resid ..

    lemma naturality:
    assumes "arr \<tau>" and "A.arr u"
    shows "Dom \<tau> u \<cdot>\<^sub>B Map \<tau> (A.trg u) = Map \<tau> (A.src u) \<cdot>\<^sub>B Cod \<tau> u"
    proof -
      interpret \<tau>: transformation A B \<open>Dom \<tau>\<close> \<open>Cod \<tau>\<close> \<open>Map \<tau>\<close>
        using assms arr_char by blast
      show ?thesis
        using assms(2) \<tau>.naturality1 \<tau>.naturality2 \<tau>.naturality3
        by (metis B.diamond_commutes)
    qed

    lemma Dom_comp [simp]:
    assumes "seq \<sigma> \<tau>"
    shows "Dom (comp \<sigma> \<tau>) = Dom \<sigma>"
      using assms
      by (metis Map_src composable_iff_arr_comp has_composites seqE\<^sub>W\<^sub>E src_comp)

    lemma Cod_comp [simp]:
    assumes "seq \<sigma> \<tau>"
    shows "Cod (comp \<sigma> \<tau>) = Cod \<tau>"
      using assms
      by (metis Map_trg composable_iff_arr_comp has_composites seqE\<^sub>W\<^sub>E trg_comp)

    lemma Map_comp [simp]:
    assumes "seq \<sigma> \<tau>"
    shows "Map (comp \<sigma> \<tau>) =
           (\<lambda>x. Map \<sigma> (A.src x) \<cdot>\<^sub>B Map \<tau> (A.src x) \<squnion>\<^sub>B Dom \<sigma> x)"
      using assms composite_of_iff comp_is_composite_of has_composites
      by simp

    lemma Map_comp_ide:
    assumes "seq \<sigma> \<tau>" and "A.ide x"
    shows "Map (comp \<sigma> \<tau>) x = Map \<sigma> x \<cdot>\<^sub>B Map \<tau> x"
    proof -
      have 1: "B.src (Map \<tau> x) = Dom \<tau> (A.src x)"
        using assms
        by (metis A.src_ide seq_char transformation.preserves_src)
      have "(Map \<sigma> (A.src x) \<cdot>\<^sub>B Map \<tau> (A.src x)) \<squnion>\<^sub>B Dom \<sigma> x =
            Map \<sigma> (A.src x) \<cdot>\<^sub>B Map \<tau> (A.src x)"
      proof -
        have "B.seq (Map \<sigma> (A.src x)) (Map \<tau> (A.src x))"
          by (metis assms(1-2) 1 A.ideE A.ide_implies_arr A.src_ide
              B.seqI\<^sub>W\<^sub>E(2) B.trg_def seq_char resid_Map_self seqE
              transformation.preserves_arr)
        hence "B.src (Map \<sigma> (A.src x) \<cdot>\<^sub>B Map \<tau> (A.src x)) = Dom \<sigma> x"
          using assms A.src_ide seq_char transformation.preserves_src B.src_comp
          by (metis B.composable_iff_seq)
        thus ?thesis
          using assms B.join_src [of "Map \<sigma> (A.src x) \<cdot>\<^sub>B Map \<tau> (A.src x)"] B.join_sym
                B.seq_implies_arr_comp \<open>B.seq (Map \<sigma> (A.src x)) (Map \<tau> (A.src x))\<close>
          by presburger
      qed
      thus ?thesis
        using assms by force
    qed

  end

subsection "Exponential by One"

  text\<open>
    The isomorphism between an RTS \<open>A\<close> and the exponential \<open>[\<^bold>\<one>, A]\<close> is important
    in various situations.
  \<close>

  locale exponential_by_One =
    One: one_arr_rts +
    A: extensional_rts A
  for A :: "'a resid"      (infix "\\\<^sub>A" 70)
  begin

    sublocale exponential_rts One.resid A ..
    notation resid   (infix "\\" 70)
    notation con     (infix "\<frown>" 50)

    abbreviation Up :: "'a \<Rightarrow> ('b, 'a) arr"
    where "Up t \<equiv>
           if A.arr t
           then MkArr
                  (constant_simulation.map One.resid A (A.src t))
                  (constant_simulation.map One.resid A (A.trg t))
                  (constant_transformation.map One.resid A t)
           else null"

    abbreviation Dn :: "('b, 'a) arr \<Rightarrow> 'a"
    where "Dn t \<equiv> if arr t then Map t One.the_arr else A.null"

    sublocale Up: simulation A resid Up
    proof
      show "\<And>t. \<not> A.arr t \<Longrightarrow> Up t = null"
        by simp
      fix t u
      assume tu: "t \<frown>\<^sub>A u"
      interpret T: constant_transformation One.resid A t
        using tu A.con_implies_arr
        by unfold_locales blast
      interpret U: constant_transformation One.resid A u
        using tu A.con_implies_arr
        by unfold_locales blast
      interpret TU: constant_transformation One.resid A \<open>A t u\<close>
        using tu
        by unfold_locales auto
      have 2: "T.F = U.F"
        using tu A.con_implies_arr A.con_imp_eq_src by auto
      have 3: "TU.F = U.G"
        using tu by auto
      show 1: "Up t \<frown> Up u"
      proof
        show "coinitial (Up t) (Up u)"
          using tu 2 A.con_implies_arr sources_char src_char
                T.transformation_axioms U.transformation_axioms
          by (intro coinitialI) auto
        show "\<And>a. One.ide a \<Longrightarrow> Map (Up t) a \<frown>\<^sub>A Map (Up u) a"
          by (simp add: T.arr_t U.arr_t tu)
      qed
      show "Up (t \\\<^sub>A u) = Up t \\ Up u"
      proof (intro arr_eqI)
        show "arr (Up (t \\\<^sub>A u))"
          using tu TU.transformation_axioms by simp
        show "arr (Up t \\ Up u)"
          using 1 by auto
        show "Dom (Up (t \\\<^sub>A u)) = Dom (Up t \\ Up u)"
          using tu 2 3 A.con_implies_arr resid_def
                T.transformation_axioms U.transformation_axioms
          by simp
        show "Cod (Up (t \\\<^sub>A u)) = Cod (Up t \\ Up u)"
        proof -
          have "TU.G =
                (\<lambda>t. if One.arr t
                     then Cod (MkArr U.F U.G U.map) t \\\<^sub>A
                            (Map (MkArr U.F T.G T.map) (One.src t) \\\<^sub>A
                               Map (MkArr U.F U.G U.map) (One.src t))
                     else A.null)"
            using A.apex_sym A.cube A.trg_def by auto
          thus ?thesis
            using tu 2 3 A.con_implies_arr resid_def
                  T.transformation_axioms U.transformation_axioms
            by simp
        qed
        show "\<And>a. One.ide a \<Longrightarrow>
                     Map (Up (t \\\<^sub>A u)) a = Map (Up t \\ Up u) a"
          using tu 2 A.con_implies_arr resid_def
                T.transformation_axioms U.transformation_axioms
          apply simp
          by (metis "3" A.join_src A.join_sym TU.arr_t One.arr_char)
      qed
    qed

    sublocale Dn: simulation resid A Dn
    proof
      show "\<And>t. \<not> arr t \<Longrightarrow> Dn t = A.null"
        by simp
      fix t u
      assume tu: "t \<frown> u"
      interpret T: transformation One.resid A \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
        using tu con_implies_arr arr_char by blast
      interpret U: transformation One.resid A \<open>Dom u\<close> \<open>Cod u\<close> \<open>Map u\<close>
        using tu con_implies_arr arr_char by blast
      interpret TU: transformation One.resid A \<open>Cod u\<close> \<open>Apex t u\<close> \<open>Resid t u\<close>
        using tu transformation_Map_resid [of t u] resid_def [of t u] con_char
        by auto
      show 1: "Dn t \<frown>\<^sub>A Dn u"
        using tu con_implies_arr con_char One.ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S by auto
      have 2: "Dom t = Dom u"
        using tu con_char by auto
      show "Dn (t \\ u) = Dn t \\\<^sub>A Dn u"
        using tu 1 2 con_implies_arr resid_def One.ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S One.arr_char
              null_char not_arr_null T.transformation_axioms U.transformation_axioms
              One.src_char A.null_is_zero A.not_arr_null TU.transformation_axioms
              Apex_def
        apply auto[1]
        by (metis (no_types, lifting) A.join_src A.join_sym A.residuation_axioms
            A.src_resid U.preserves_trg residuation.arr_resid)
    qed

    lemma inverse_simulations_Dn_Up:
    shows "inverse_simulations A resid Dn Up"
    proof
      show "Dn \<circ> Up = I A"
        using One.arr_char by auto
      show "Up \<circ> Dn = I resid"
      proof
        interpret UpoDown: composite_simulation resid A resid Dn Up ..
        fix t
        show "(Up \<circ> Dn) t = I resid t"
        proof (cases "arr t", intro arr_eqI)
          show "\<not> arr t \<Longrightarrow> (Up \<circ> Dn) t = I resid t"
            by auto
          show "arr t \<Longrightarrow> arr (UpoDown.map t)" by blast
          show "arr t \<Longrightarrow> arr (I resid t)" by simp
          fix t
          assume t: "arr t"
          interpret T: transformation One.resid A \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
            using t arr_char [of t] by blast
          show "Dom (UpoDown.map t) = Dom (I resid t)"
            using t T.F.extensional T.preserves_arr One.arr_char One.ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S
                  T.preserves_src
            by auto
          show "Cod (UpoDown.map t) = Cod (I resid t)"
            using t T.G.extensional T.preserves_arr One.arr_char One.ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S
                  T.preserves_trg
            by auto
          show "\<And>a. One.ide a \<Longrightarrow> Map (UpoDown.map t) a = Map (I resid t) a"
            using t T.preserves_arr One.arr_char by auto
        qed
      qed
    qed

  end

subsection "Evaluation Map"

  locale evaluation_map =
    A: weakly_extensional_rts A +
    B: extensional_rts B
  for A :: "'a resid"          (infix "\\\<^sub>A" 55)
  and B :: "'b resid"          (infix "\\\<^sub>B" 55)
  begin

    sublocale AB: exponential_rts A B ..
    sublocale ABxA: product_rts AB.resid A ..

    notation AB.resid        (infix "\\\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]" 55)
    notation ABxA.resid      (infix "\\\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]\<^sub>x\<^sub>A" 55)
    notation AB.con          (infix "\<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]" 50)
    notation ABxA.con        (infix "\<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]\<^sub>\<times>\<^sub>A" 50)

    definition map :: "('a, 'b) AB.arr \<times> 'a \<Rightarrow> 'b"
    where "map Fg \<equiv> if ABxA.arr Fg then AB.Map (fst Fg) (snd Fg) else B.null"

    lemma map_simp:
    assumes "ABxA.arr Fg"
    shows "map Fg = AB.Map (fst Fg) (snd Fg)"
      using assms map_def by auto

    lemma is_simulation:
    shows "simulation ABxA.resid B map"
    proof
      show "\<And>Fg. \<not> ABxA.arr Fg \<Longrightarrow> map Fg = B.null"
        using map_def by auto
      fix Fg Fg'
      assume con: "Fg \<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]\<^sub>\<times>\<^sub>A Fg'"
      let ?F = "fst Fg" and ?g = "snd Fg"
      let ?F' = "fst Fg'" and ?g' = "snd Fg'"
      have con_FF': "?F \<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>] ?F'"
        using con by blast
      have con_gg': "?g \<frown>\<^sub>A ?g'"
       using con by blast
      interpret F: transformation A B \<open>AB.Dom ?F\<close> \<open>AB.Cod ?F\<close> \<open>AB.Map ?F\<close>
        using AB.con_char con_FF' by auto
      interpret F': transformation A B
                      \<open>AB.Dom ?F\<close> \<open>AB.Cod ?F'\<close> \<open>AB.Map ?F'\<close>
        using AB.con_char con_FF' by metis
      interpret F_F': transformation A B \<open>AB.Cod ?F'\<close> \<open>AB.Apex ?F ?F'\<close>
                        \<open>AB.Map (AB.resid ?F ?F')\<close>
        using AB.con_char AB.transformation_Map_resid con_FF' by auto
      show "map Fg \<frown>\<^sub>B map Fg'"
        by (metis A.arr_resid AB.resid_Map ABxA.con_implies_arr(2) B.conI
            B.not_arr_null F_F'.preserves_arr con con_FF' con_gg' map_def
            ABxA.con_implies_arr(1))
      show "map (Fg \\\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]\<^sub>x\<^sub>A Fg') = map Fg \\\<^sub>B map Fg'"
        by (metis AB.resid_Map ABxA.arr_resid ABxA.con_implies_arr(2)
            ABxA.resid_def con con_FF' con_gg' fst_conv map_def
            ABxA.con_implies_arr(1) snd_conv)
    qed

    sublocale simulation ABxA.resid B map
      using is_simulation by auto
    sublocale binary_simulation AB.resid A B map ..

    lemma src_map:
    assumes "AB.arr Fg" and "A.arr f"
    shows "B.src (map (Fg, f)) = AB.Dom Fg (A.src f)"
    proof -
      interpret F: transformation A B \<open>AB.Dom Fg\<close> \<open>AB.Cod Fg\<close> \<open>AB.Map Fg\<close>
        using assms AB.arr_char by auto
      show ?thesis
        by (metis A.ide_src ABxA.arr_char B.src_join_of(1) F.naturality3
            F.preserves_src assms(1-2) fst_conv map_def snd_conv)
    qed

    lemma trg_map:
    assumes "AB.arr Fg" and "A.arr f"
    shows "B.trg (map (Fg, f)) = AB.Cod Fg (A.trg f)"
    proof -
      interpret F: transformation A B \<open>AB.Dom Fg\<close> \<open>AB.Cod Fg\<close> \<open>AB.Map Fg\<close>
        using assms AB.arr_char by auto
      show ?thesis
        by (metis ABxA.arr_char B.apex_sym B.trg_join_of(1) F.G.preserves_trg
            F.naturality2_ax F.naturality3 assms(1-2) fst_conv map_def snd_conv)
    qed

  end

  subsection "Currying"

  locale Currying =
  A: weakly_extensional_rts A +
  B: weakly_extensional_rts B +
  C: extensional_rts C
  for A :: "'a resid"           (infix "\\\<^sub>A" 55)
  and B :: "'b resid"           (infix "\\\<^sub>B" 55)
  and C :: "'c resid"           (infix "\\\<^sub>C" 55)
  begin

    sublocale AxB: product_of_weakly_extensional_rts A B ..
    sublocale BC: exponential_rts B C ..
    sublocale BCxB: product_rts BC.resid B ..
    sublocale E: evaluation_map B C ..

    notation A.con              (infix "\<frown>\<^sub>A" 50)
    notation B.con              (infix "\<frown>\<^sub>B" 50)
    notation C.con              (infix "\<frown>\<^sub>C" 50)
    notation C.prfx             (infix "\<lesssim>\<^sub>C" 50)
    notation C.join             (infixr "\<squnion>\<^sub>C" 52)
    notation AxB.resid          (infix "\\\<^sub>A\<^sub>x\<^sub>B" 55)
    notation AxB.con            (infix "\<frown>\<^sub>A\<^sub>x\<^sub>B" 52)
    notation AxB.prfx           (infix "\<lesssim>\<^sub>A\<^sub>x\<^sub>B" 52)
    notation BC.resid           (infix "\\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]" 55)
    notation BC.con             (infix "\<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]" 52)
    notation BC.join            (infixr "\<squnion>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]" 52)
    notation BCxB.resid         (infix "\\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>x\<^sub>B" 55)
    notation BCxB.con           (infix "\<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>x\<^sub>B" 52)

    definition Curry :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)
                           \<Rightarrow> 'a \<Rightarrow> ('b, 'c) BC.arr"
    where "Curry F G \<tau> f =
           (if A.arr f
            then BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. G (A.trg f, g)) (\<lambda>g. \<tau> (f, g))
            else BC.null)"

    abbreviation Curry3 :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('b, 'c) BC.arr"
    where "Curry3 F \<equiv> Curry F F F"

    definition Uncurry :: "('a \<Rightarrow> ('b, 'c) BC.arr) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c"
    where "Uncurry \<tau> f \<equiv> if AxB.arr f then E.map (\<tau> (fst f), snd f) else C.null"

    lemma Curry_simp:
    assumes "A.arr f"
    shows "Curry F G \<tau> f =
           BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. G (A.trg f, g)) (\<lambda>g. \<tau> (f, g))"
      using assms Curry_def by auto

    lemma Uncurry_simp:
    assumes "AxB.arr f"
    shows "Uncurry \<tau> f = E.map (\<tau> (fst f), snd f)"
      using assms Uncurry_def by auto

    lemma Dom_Curry:
    assumes "A.arr f"
    shows "BC.Dom (Curry F G \<tau> f) = (\<lambda>g. F (A.src f, g))"
      using assms Curry_simp by simp
   
    lemma Cod_Curry:
    assumes "A.arr f"
    shows "BC.Cod (Curry F G \<tau> f) = (\<lambda>g. G (A.trg f, g))"
      using assms Curry_simp by simp
   
    lemma Map_Curry:
    assumes "A.arr f"
    shows "BC.Map (Curry F G \<tau> f) = (\<lambda>g. \<tau> (f, g))"
      using assms Curry_simp by simp
   
    lemma Map_simulation_expansion:
    assumes "simulation A BC.resid G" and "AxB.arr f"
    shows "BC.Map (G (fst f)) (snd f) =
           BC.Map (G (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
             BC.Map (G (A.src (fst f))) (snd f)"
    proof -
      interpret G: simulation A BC.resid G
        using assms(1) by blast
      interpret G: simulation_to_extensional_rts A BC.resid G ..
      show ?thesis
      proof (intro C.join_eqI')
        show "BC.Map (G (fst f)) (B.src (snd f)) \<lesssim>\<^sub>C BC.Map (G (fst f)) (snd f)"
          by (metis B.con_arr_src(2) B.resid_src_arr B.trg_def
              BC.Map_preserves_prfx BC.cong_reflexive BC.resid_Map_self
              G.preserves_reflects_arr assms(2) AxB.arr_char B.arrE)
        show "BC.Map (G (A.src (fst f))) (snd f) \<lesssim>\<^sub>C BC.Map (G (fst f)) (snd f)"
          by (meson A.source_is_prfx A.src_in_sources BC.Map_preserves_prfx
              G.preserves_prfx assms(2) AxB.arr_char)
        show "BC.Map (G (fst f)) (snd f) \\\<^sub>C BC.Map (G (A.src (fst f))) (snd f) =
              BC.Map (G (fst f)) (B.src (snd f)) \\\<^sub>C
                BC.Map (G (A.src (fst f))) (snd f)"
          by (metis A.con_arr_src(1) AxB.arr_char AxB.con_char B.con_arr_src(2)
              B.resid_src_arr B.trg_def BC.resid_Map G.preserves_con assms(2)
              AxB.arrE)
        show "BC.Map (G (fst f)) (snd f) \\\<^sub>C BC.Map (G (fst f)) (B.src (snd f)) =
              BC.Map (G (A.src (fst f))) (snd f) \\\<^sub>C
                BC.Map (G (fst f)) (B.src (snd f))"
          by (metis A.con_arr_src(2) A.resid_arr_self A.resid_src_arr
              B.con_arr_src(1) BC.resid_Map G.preserves_con
              G.preserves_resid assms(2) AxB.arr_char A.arrE)
      qed
    qed

    lemma Map_simulation_monotone:
    assumes "simulation A BC.resid G" and "f \<lesssim>\<^sub>A\<^sub>x\<^sub>B g"
    shows "BC.Map (G (fst f)) (snd f) \<lesssim>\<^sub>C BC.Map (G (fst g)) (snd g)"
    proof -
      interpret G: simulation A BC.resid G
        using assms(1) by blast
      interpret G: simulation_to_extensional_rts A BC.resid G ..
      show ?thesis
        using assms(2)
        by (metis AxB.con_char AxB.prfx_char AxB.prfx_implies_con
            BC.Map_resid_ide BC.arrE BC.con_def BC.ide_implies_arr
            BC.prfx_char BC.resid_Map G.preserves_prfx)
    qed

    lemma Curry_preserves_simulations [intro]:
    assumes "simulation AxB.resid C F"
    shows "simulation A BC.resid (Curry3 F)"
    proof -
      interpret F: simulation AxB.resid C F
        using assms by auto
      interpret F: binary_simulation_between_weakly_extensional_rts A B C F ..
      show ?thesis
      proof
        show "\<And>t. \<not> A.arr t \<Longrightarrow> Curry3 F t = BC.null"
          using Curry_def by simp
        fix t u
        assume con: "t \<frown>\<^sub>A u"
        interpret Ft: transformation B C \<open>\<lambda>g. F (A.src u, g)\<close> \<open>\<lambda>g. F (A.trg t, g)\<close>
                        \<open>\<lambda>g. F (t, g)\<close>
          using con F.fixing_arr_gives_transformation_1 [of t] A.con_implies_arr(1)
                A.con_imp_eq_src
          by simp
        interpret Fu: transformation B C \<open>\<lambda>g. F (A.src u, g)\<close> \<open>\<lambda>g. F (A.trg u, g)\<close>
                        \<open>\<lambda>g. F (u, g)\<close>
          using con F.fixing_arr_gives_transformation_1 [of u] A.con_implies_arr(2)
                A.con_imp_eq_src
          by simp
        show *: "Curry3 F t \<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry3 F u"
          using con Curry_def BC.con_char Curry_simp A.con_implies_arr
                A.con_imp_eq_src Ft.transformation_axioms Fu.transformation_axioms
          by simp
        show "Curry3 F (t \\\<^sub>A u) = Curry3 F t \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry3 F u"
        proof -
          have "BC.Dom (Curry3 F (t \\\<^sub>A u)) =
                BC.Dom (Curry3 F t \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry3 F u)"
            using * A.arr_resid A.con_implies_arr(2) A.src_resid BC.Dom_resid
                  Cod_Curry Dom_Curry con
            by presburger
          moreover have "BC.Cod (Curry3 F (t \\\<^sub>A u)) =
                         BC.Cod (Curry3 F t \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry3 F u)"
          proof -
            have "BC.Cod (Curry3 F (t \\\<^sub>A u)) = (\<lambda>g. F (A.trg (t \\\<^sub>A u), g))"
              using Cod_Curry con by force
            also have "... = BC.Apex (BC.MkArr (\<lambda>g. F (A.src u, g))
                                        (\<lambda>g. F (A.trg t, g)) (\<lambda>g. F (t, g)))
                                     (BC.MkArr (\<lambda>g. F (A.src u, g))
                                        (\<lambda>g. F (A.trg u, g)) (\<lambda>g. F (u, g)))"
            proof -
              have "(\<lambda>g. F (A.trg (t \\\<^sub>A u), g)) =
                    (\<lambda>g. if B.arr g
                          then BC.Cod (BC.MkArr (\<lambda>g. F (A.src u, g))
                                           (\<lambda>g. F (A.trg u, g)) (\<lambda>g. F (u, g))) g \\\<^sub>C
                                 (BC.Map (BC.MkArr
                                              (\<lambda>g. F (A.src u, g)) (\<lambda>g. F (A.trg t, g))
                                              (\<lambda>g. F (t, g)))
                                         (B.src g) \\\<^sub>C
                                    BC.Map (BC.MkArr
                                                (\<lambda>g. F (A.src u, g)) (\<lambda>g. F (A.trg u, g))
                                                (\<lambda>g. F (u, g)))
                                         (B.src g))
                          else C.null)"
              proof
                fix g
                show "F (A.trg (t \\\<^sub>A u), g) =
                      (if B.arr g
                       then BC.Cod (BC.MkArr
                                        (\<lambda>g. F (A.src u, g)) (\<lambda>g. F (A.trg u, g))
                                        (\<lambda>g. F (u, g))) g \\\<^sub>C
                              (BC.Map (BC.MkArr
                                           (\<lambda>g. F (A.src u, g)) (\<lambda>g. F (A.trg t, g))
                                           (\<lambda>g. F (t, g)))
                                      (B.src g) \\\<^sub>C
                                 BC.Map (BC.MkArr (\<lambda>g. F (A.src u, g))
                                             (\<lambda>g. F (A.trg u, g)) (\<lambda>g. F (u, g)))
                                        (B.src g))
                       else C.null)"
                proof (cases "B.arr g")
                  show "\<not> B.arr g \<Longrightarrow> ?thesis"
                    by (metis A.arr_resid A.ide_trg F.fixing_ide_gives_simulation_1 con
                        simulation.extensional)
                  assume g: "B.arr g"
                  have "F (t, B.src g) \\\<^sub>C F (u, B.src g) = F (t \\\<^sub>A u, B.src g)"
                    using g con F.preserves_resid AxB.resid_def AxB.con_char
                    by (metis AxB.con_arr_self B.arr_src_iff_arr B.trg_def B.trg_src
                        F.preserves_reflects_arr Ft.preserves_arr fst_conv snd_conv)
                  moreover have "F (A.trg (t \\\<^sub>A u), g) =
                                 F (A.trg u, g) \\\<^sub>C F (t \\\<^sub>A u, B.src g)"
                    using con g F.preserves_resid AxB.resid_def AxB.con_char
                    by auto
                       (metis (no_types, lifting) A.arr_resid A.con_imp_arr_resid
                        A.resid_src_arr A.src_resid A.trg_def B.con_arr_src(1)
                        B.resid_arr_src A.con_def)
                  ultimately show ?thesis
                    using con BC.Apex_def A.con_implies_arr F.extensional
                          F.preserves_trg F.preserves_resid AxB.resid_def
                    by auto
                qed
              qed
              thus ?thesis
                using con BC.Apex_def A.con_implies_arr F.extensional F.preserves_trg
                by auto
            qed
            also have "... = BC.Cod (Curry3 F t \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry3 F u)"
              using con Curry_def A.con_implies_arr A.con_imp_eq_src BC.Apex_def
                    Ft.transformation_axioms Fu.transformation_axioms BC.resid_def
              by simp
            finally show ?thesis by blast
          qed
          moreover have "BC.Map (Curry3 F (t \\\<^sub>A u)) =
                         BC.Map (Curry3 F t \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry3 F u)"
          proof -
            have "BC.Map (Curry3 F (t \\\<^sub>A u)) = (\<lambda>g. F (t \\\<^sub>A u, g))"
              using con Curry_def A.con_implies_arr A.con_imp_eq_src BC.Map_resid
              by simp
            also have "... =
                       (\<lambda>g. if B.arr g
                             then BC.Map (BC.MkArr (\<lambda>g. F (A.src u, g))
                                                   (\<lambda>g. F (A.trg t, g))
                                                   (\<lambda>g. F (t, g)))
                                          (B.src g) \\\<^sub>C
                                    BC.Map (BC.MkArr (\<lambda>g. F (A.src u, g))
                                                     (\<lambda>g. F (A.trg u, g))
                                                     (\<lambda>g. F (u, g)))
                                           (B.src g) \<squnion>\<^sub>C
                                  BC.Cod (BC.MkArr (\<lambda>g. F (A.src u, g))
                                                   (\<lambda>g. F (A.trg u, g))
                                                   (\<lambda>g. F (u, g)))
                                         g
                             else C.null)"
            proof
              fix g
              show "F (t \\\<^sub>A u, g) =
                    (if B.arr g
                     then BC.Map (BC.MkArr (\<lambda>g. F (A.src u, g))
                                           (\<lambda>g. F (A.trg t, g))
                                           (\<lambda>g. F (t, g)))
                                 (B.src g) \\\<^sub>C
                            BC.Map (BC.MkArr (\<lambda>g. F (A.src u, g))
                                             (\<lambda>g. F (A.trg u, g))
                                             (\<lambda>g. F (u, g)))
                                   (B.src g) \<squnion>\<^sub>C
                          BC.Cod (BC.MkArr (\<lambda>g. F (A.src u, g))
                                           (\<lambda>g. F (A.trg u, g))
                                           (\<lambda>g. F (u, g)))
                                 g
                     else C.null)"
              proof (cases "B.arr g")
                show "\<not> B.arr g \<Longrightarrow> ?thesis"
                  using F.extensional by simp
                assume g: "B.arr g"
                have "F (t \\\<^sub>A u, g) =
                      F (t, B.src g) \\\<^sub>C F (u, B.src g) \<squnion>\<^sub>C F (A.trg u, g)"
                proof -
                  have "F (t, B.src g) \\\<^sub>C F (u, B.src g) = F (t \\\<^sub>A u, B.src g)"
                    by (metis (no_types, lifting) AxB.con_char AxB.resid_def
                        B.ide_def B.ide_src F.preserves_resid con g fst_eqD snd_eqD)
                  moreover have "F (t \\\<^sub>A u, B.src g) \<squnion>\<^sub>C F (A.trg u, g) =
                                 F (t \\\<^sub>A u, g)"
                  proof -
                    have "C.join_of (F (t \\\<^sub>A u, B.src g)) (F (A.trg u, g))
                            (F (t \\\<^sub>A u, g))"
                      using F.preserves_joins BCxB.join_of_char
                      by (metis A.arr_resid A.join_of_arr_src(2) A.src_in_sources
                          A.src_resid AxB.join_of_char(1) B.join_of_arr_src(1)
                          B.src_in_sources con g fst_eqD snd_conv)
                    thus ?thesis
                      by (meson C.join_is_join_of C.join_of_unique C.joinable_def)
                  qed
                  ultimately show ?thesis by auto
                qed
                thus ?thesis
                  using g by simp
              qed
            qed
            finally show ?thesis
              using con Curry_def A.con_implies_arr A.con_imp_eq_src BC.Map_resid'
                    Ft.transformation_axioms Fu.transformation_axioms
              by simp
          qed
          moreover have "Curry3 F (t \\\<^sub>A u) \<noteq> BC.Null"
            using BC.arr_char
            by (simp add: con Curry_def)
          moreover have "Curry3 F t \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry3 F u \<noteq> BC.Null"
            using con BC.arr_char "*" BC.null_char BC.con_def by force
          moreover
          have "\<And>x y. BC.Dom x = BC.Dom y \<and> BC.Cod x = BC.Cod y \<and>
                       BC.Map x = BC.Map y \<and> x \<noteq> BC.Null \<and> y \<noteq> BC.Null
                          \<Longrightarrow> x = y"
            by (metis BC.Cod.simps(1) BC.Dom.simps(1) BC.Map.elims)
          ultimately show ?thesis by blast
        qed
      qed
    qed

    lemma Uncurry_preserves_simulations [intro]:
    assumes "simulation A BC.resid F"
    shows "simulation AxB.resid C (Uncurry F)"
    proof -
      interpret F: simulation A BC.resid F using assms by auto
      show ?thesis
      proof
        show "\<And>t. \<not> AxB.arr t \<Longrightarrow> Uncurry F t = C.null"
          using Uncurry_def by presburger
        show "\<And>t u. t \<frown>\<^sub>A\<^sub>x\<^sub>B u \<Longrightarrow> Uncurry F t \<frown>\<^sub>C Uncurry F u"
          using Uncurry_def AxB.con_implies_arr(1) AxB.con_implies_arr(2)
          by auto
        fix t u :: "'a * 'b"
        assume con: "t \<frown>\<^sub>A\<^sub>x\<^sub>B u"
        have "Uncurry F (t \\\<^sub>A\<^sub>x\<^sub>B u) = E.map (F (fst (t \\\<^sub>A\<^sub>x\<^sub>B u)), snd (t \\\<^sub>A\<^sub>x\<^sub>B u))"
          using AxB.arr_resid Uncurry_def con by presburger
        also have "... = Uncurry F t \\\<^sub>C Uncurry F u"
          using AxB.con_implies_arr(1) AxB.con_implies_arr(2) AxB.resid_def
            BCxB.resid_def E.preserves_resid Uncurry_simp con
          by auto
        finally show "Uncurry F (t \\\<^sub>A\<^sub>x\<^sub>B u) = Uncurry F t \\\<^sub>C Uncurry F u"
          by auto
      qed
    qed

    lemma Curry_preserves_transformations:
    assumes "transformation AxB.resid C F G \<tau>"
    shows "transformation A BC.resid (Curry3 F) (Curry3 G) (Curry F G \<tau>)"
    proof -
      interpret \<tau>: transformation AxB.resid C F G \<tau> using assms by auto
      interpret \<tau>: transformation_to_extensional_rts AxB.resid C F G \<tau> ..
      interpret \<tau>: transformation_of_binary_simulations A B C F G \<tau> ..
      interpret Curry_F: simulation A BC.resid \<open>Curry F F F\<close>
        using Curry_preserves_simulations \<tau>.F.simulation_axioms by simp
      interpret Curry_G: simulation A BC.resid \<open>Curry G G G\<close>
        using Curry_preserves_simulations \<tau>.G.simulation_axioms by simp
      show ?thesis
      proof
        fix f
        show "\<not> A.arr f \<Longrightarrow> Curry F G \<tau> f = BC.null"
          using Curry_def by simp
        show "A.ide f \<Longrightarrow> BC.src (Curry F G \<tau> f) = Curry3 F f"
          unfolding Curry_def
          using BC.src_simp A.ide_implies_arr A.src_ide A.trg_ide BC.Dom.simps(1)
            BC.arr_MkArr \<tau>.fixing_ide_gives_transformation_1
          by presburger
        show "A.ide f \<Longrightarrow> BC.trg (Curry F G \<tau> f) = Curry3 G f"
          unfolding Curry_def
          using BC.trg_simp A.ide_implies_arr A.src_ide A.trg_ide BC.Cod.simps(1)
            BC.arr_MkArr \<tau>.fixing_ide_gives_transformation_1
          by presburger
        assume f: "A.arr f"
        interpret \<tau>_src: transformation B C
                           \<open>\<lambda>g. F (A.src f, g)\<close> \<open>\<lambda>g. G (A.src f, g)\<close> \<open>\<lambda>g. \<tau> (A.src f, g)\<close>
          using f \<tau>.fixing_ide_gives_transformation_1 by auto
        interpret \<tau>_trg: transformation B C
                           \<open>\<lambda>g. F (A.trg f, g)\<close> \<open>\<lambda>g. G (A.trg f, g)\<close> \<open>\<lambda>g. \<tau> (A.trg f, g)\<close>
          using f \<tau>.fixing_ide_gives_transformation_1 by auto
        interpret \<tau>.F: binary_simulation_between_weakly_extensional_rts A B C F ..
        interpret F_f: transformation B C
                         \<open>\<lambda>g. F (A.src f, g)\<close> \<open>\<lambda>g. F (A.trg f, g)\<close> \<open>\<lambda>g. F (f, g)\<close>
          using f \<tau>.F.fixing_arr_gives_transformation_1 by metis
        show A: "Curry F G \<tau> (A.src f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry3 F f = Curry F G \<tau> (A.trg f)"
        proof -
          have "Curry F G \<tau> (A.src f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry3 F f =
                BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. G (A.src f, g))
                    (\<lambda>g. \<tau> (A.src f, g)) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                  BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. F (A.trg f, g)) (\<lambda>g. F (f, g))"
            using Curry_def f by simp
          also have "... = BC.MkArr (\<lambda>g. F (A.trg f, g)) (\<lambda>g. G (A.trg f, g))
                               (\<lambda>g. \<tau> (A.trg f, g))"
            (is "?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2 = ?RHS")
          proof -
            have 1: "?LHS1 \<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2"
              using f BC.con_char \<tau>_src.transformation_axioms
                    F_f.transformation_axioms
              apply simp
              by (metis B.ide_iff_src_self B.ide_iff_trg_self C.conE C.conI
                  C.con_arr_src(1) \<tau>.fixing_ide_gives_transformation_0
                  \<tau>_trg.naturality1 \<tau>_trg.preserves_arr \<tau>_trg.preserves_src
                  B.ide_implies_arr transformation.naturality1)
            have "BC.Dom (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) = BC.Dom ?RHS"
              using 1 f BC.Dom_resid BC.con_char by simp
            moreover have "BC.Cod (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) = BC.Cod ?RHS"
            proof -
              have "BC.Cod (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) = BC.Apex ?LHS1 ?LHS2"
                using 1 f BC.Cod_resid BC.con_char by fastforce
              also have "... = (\<lambda>g. G (A.trg f, g))"
              proof
                fix g
                show "BC.Apex ?LHS1 ?LHS2 g = G (A.trg f, g)"
                  unfolding BC.Apex_def
                  using f
                  by (metis B.ide_src BC.Cod.simps(1) BC.Map.simps(1)
                      \<tau>.fixing_ide_gives_transformation_0 \<tau>_trg.G.extensional
                      \<tau>_trg.naturality2 transformation.naturality1_ax)
              qed
              also have "... = BC.Cod ?RHS"
                using 1 f BC.Cod_resid BC.con_char by fastforce
              finally show ?thesis by blast
            qed
            moreover have "BC.Map (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) = BC.Map ?RHS"
            proof
              fix g
              have "\<tau> (A.src f, B.src g) \\\<^sub>C F (f, B.src g) \<squnion>\<^sub>C F (A.trg f, g) =
                      \<tau> (A.trg f, g)"
              proof -
                have "\<tau> (A.src f, B.src g) \\\<^sub>C F (f, B.src g) \<squnion>\<^sub>C F (A.trg f, g) =
                      \<tau> (A.trg f, B.src g) \<squnion>\<^sub>C F (A.trg f, g)"
                  by (metis AxB.src_char AxB.trg_char B.src_src B.trg_src
                      C.null_is_zero(2) F_f.extensional F_f.preserves_arr
                      \<tau>.F.preserves_reflects_arr \<tau>.naturality1 \<tau>_trg.extensional
                      fst_conv snd_conv)
                also have "... = \<tau> (A.trg f, g)"
                  by (metis B.arr_src_iff_arr C.arr_prfx_join_self C.join_def
                      C.join_is_join_of C.join_of_unique C.joinable_def
                      C.not_ide_null C.null_is_zero(1) \<tau>_trg.extensional
                      \<tau>_trg.naturality3)
                finally show ?thesis by blast
              qed
              moreover have "\<not> B.arr g \<Longrightarrow> C.null = \<tau> (A.trg f, g)"
                using \<tau>_trg.extensional by presburger
              ultimately show "BC.Map (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) g = BC.Map ?RHS g"
                using 1
                by (cases "B.arr g", simp_all)
            qed
            ultimately show ?thesis
              using 1 BC.con_char BC.resid_def by auto
          qed
          also have "... = Curry F G \<tau> (A.trg f)"
            using Curry_def f by simp
          finally show ?thesis by auto
        qed
        show "Curry3 F f \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry F G \<tau> (A.src f) = Curry3 G f"
        proof -
          have "Curry3 F f \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] Curry F G \<tau> (A.src f) =
                BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. F (A.trg f, g))
                    (\<lambda>g. F (f, g)) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                  BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. G (A.src f, g))
                      (\<lambda>g. \<tau> (A.src f, g))"
            unfolding Curry_def
            using f by simp
          also have "... = BC.MkArr (\<lambda>g. G (A.src f, g)) (\<lambda>g. G (A.trg f, g))
                               (\<lambda>g. G (f, g))"
            (is "?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2 = ?RHS")
          proof -
            have 1: "BC.con ?LHS1 ?LHS2"
              using A f BC.con_sym_ax BC.null_char Curry_simp by auto
            have "BC.Dom (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) = BC.Dom ?RHS"
              using 1 f BC.Dom_resid BC.con_char by auto
            moreover have "BC.Cod (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) = BC.Cod ?RHS"
            proof -
              have "BC.Cod (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) = BC.Apex ?LHS1 ?LHS2"
                using 1 f BC.Dom_resid BC.con_char by fastforce
              also have "... = (\<lambda>g. G (A.trg f, g))"
              proof
                fix g
                have "G (A.src f, g) \\\<^sub>C (F (f, B.src g) \\\<^sub>C \<tau> (A.src f, B.src g)) =
                        G (A.trg f, g)"
                proof -
                  have "G (A.src f, g) \\\<^sub>C (F (f, B.src g) \\\<^sub>C \<tau> (A.src f, B.src g)) =
                        G (A.src f, g) \\\<^sub>C G (f, B.src g)"
                    by (metis AxB.src_char B.arr_src_iff_arr B.src_src C.con_sym_ax
                        C.null_is_zero(2) F_f.preserves_arr \<tau>.F.preserves_reflects_arr
                        \<tau>.naturality2 \<tau>_src.G.extensional fst_conv snd_conv)
                  also have "... = G ((A.src f, g) \\\<^sub>A\<^sub>x\<^sub>B (f, B.src g))"
                    by (metis A.con_arr_src(2) AxB.con_char B.arr_src_iff_arr
                        B.con_arr_src(1) C.null_is_zero(2) \<tau>.G.extensional
                        \<tau>.G.preserves_resid \<tau>_src.extensional calculation f
                        AxB.arr_resid_iff_con fst_conv snd_conv)
                  also have "... = G (A.src f \\\<^sub>A f, g \\\<^sub>B B.src g)"
                    using AxB.resid_def B.arr_resid_iff_con \<tau>.G.extensional f
                    by auto
                  also have "... = G (A.trg f, g)"
                    by (metis A.resid_src_arr B.resid_arr_src B.resid_reflects_con
                        \<tau>_trg.G.extensional f B.arr_def B.arr_resid_iff_con)
                  finally show ?thesis by blast
                qed
                moreover have "\<not> B.arr g \<Longrightarrow> C.null = G (A.trg f, g)"
                  using \<tau>_trg.G.extensional by presburger
                ultimately show "BC.Apex ?LHS1 ?LHS2 g = G (A.trg f, g)"
                  using BC.Apex_def f
                  by (cases "B.arr g", simp_all)
              qed
              also have "... = BC.Cod ?RHS"
                using 1 f by fastforce
              finally show ?thesis by blast
            qed
            moreover have "BC.Map (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) = BC.Map ?RHS"
            proof
              fix g
              show "BC.Map (?LHS1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] ?LHS2) g = BC.Map ?RHS g"
              proof -
                have "F (f, B.src g) \\\<^sub>C \<tau> (A.src f, B.src g) \<squnion>\<^sub>C G (A.src f, g) =
                      G (f, g)"
                proof (cases "B.arr g")
                  show "\<not> B.arr g \<Longrightarrow> ?thesis"
                    by (metis B.arr_src_iff_arr C.arr_prfx_join_self
                        C.joinable_iff_join_not_null C.not_ide_null C.null_is_zero(1)
                        F_f.extensional \<tau>.naturality2)
                  assume g: "B.arr g"
                  have "F (f, B.src g) \\\<^sub>C \<tau> (A.src f, B.src g) \<squnion>\<^sub>C G (A.src f, g) =
                        G (f, B.src g) \<squnion>\<^sub>C G (A.src f, g)"
                    by (metis AxB.src_char B.arr_src_iff_arr B.src_src F_f.preserves_arr
                        \<tau>.F.preserves_reflects_arr \<tau>.naturality2 g fst_conv snd_conv)
                  also have "... = G (f, g)"
                    using f g
                          \<tau>.G.preserves_joins
                            [of "(f, B.src g)" "(A.src f, g)" "(f, g)"]
                    by (metis A.join_of_arr_src(2) A.src_in_sources AxB.join_of_char(1)
                        B.join_of_arr_src(1) B.src_in_sources C.join_is_join_of
                        C.join_of_unique C.joinable_def fst_conv snd_conv)
                  finally show ?thesis by blast
                qed
                thus ?thesis
                  using 1 f BC.Map_resid BC.con_char \<tau>.G.extensional by auto
              qed
            qed
            ultimately show ?thesis
              using 1 BC.con_char BC.resid_def by auto
          qed
          also have "... = Curry3 G f"
            using Curry_def f by simp
          finally show ?thesis by blast
        qed
        show "BC.join_of (Curry F G \<tau> (A.src f)) (Curry3 F f) (Curry F G \<tau> f)"
        proof -
          have *: "\<And>t. B.arr t \<Longrightarrow>
                          (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) \<squnion>\<^sub>C F (A.src f, t) =
                          \<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, t)"
          proof -
            fix t
            assume t: "B.arr t"
            have 1: "C.joinable (\<tau> (A.src f, B.src t)) (F (f, t))"
              by (metis AxB.product_of_weakly_extensional_rts_axioms F_f.preserves_arr
                  \<tau>.F.preserves_reflects_arr \<tau>.naturality3'\<^sub>E(2) fst_conv
                  product_of_weakly_extensional_rts.src_char snd_conv t)
            show "(\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) \<squnion>\<^sub>C F (A.src f, t) =
                  \<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, t)"
            proof (intro C.join_eqI)
              show 2: "\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t) \<lesssim>\<^sub>C
                         \<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, t)"
                by (metis A.ide_trg A.trg_def AxB.prfx_char AxB.src_char
                    B.arr_src_iff_arr B.ide_trg B.resid_src_arr B.src_src
                    F_f.preserves_arr \<tau>.F.preserves_reflects_arr \<tau>.naturality3'\<^sub>E(1)
                    \<tau>.preserves_prfx f fst_conv snd_conv t)
              show 3: "F (A.src f, t) \<lesssim>\<^sub>C \<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, t)"
                by (metis (full_types) 1 t C.arr_prfx_join_self C.join_is_join_of
                    C.join_of_symmetric C.join_of_unique C.joinable_def
                    C.prfx_transitive F_f.naturality3)
              show 4: "(\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, t)) \\\<^sub>C F (A.src f, t) =
                       (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) \\\<^sub>C F (A.src f, t)"
              proof -
                have "(\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, t)) \\\<^sub>C F (A.src f, t) =
                      \<tau> (A.src f, B.src t) \\\<^sub>C F (A.src f, t) \<squnion>\<^sub>C
                        F (f, t) \\\<^sub>C F (A.src f, t)"
                  by (meson 1 3 C.ide_implies_arr C.resid_join\<^sub>E(3) C.residuation_axioms
                      residuation.arr_resid_iff_con)
                also have "... = \<tau> (A.src f, B.src t) \\\<^sub>C F (A.src f, t) \<squnion>\<^sub>C
                                     F (f, B.src t) \\\<^sub>C F (A.src f, t)"
                  by (metis C.composite_ofE C.extensional F_f.naturality1
                      F_f.naturality1' t)
                also have "... = (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) \\\<^sub>C
                                   F (A.src f, t)"
                  by (metis 2 3 C.con_prfx(1) C.joinable_iff_arr_join C.resid_join\<^sub>E(3)
                      C.con_implies_arr(1) C.prfx_implies_con)
                finally show ?thesis by blast
              qed
              show "(\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, t)) \\\<^sub>C
                      (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) =
                    F (A.src f, t) \\\<^sub>C (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t))"
              proof -
                have "(\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, t)) \\\<^sub>C
                        (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) =
                      \<tau> (A.src f, B.src t) \\\<^sub>C (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) \<squnion>\<^sub>C
                        F (f, t) \\\<^sub>C (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t))"
                  using 1 2 C.prfx_implies_con C.resid_join\<^sub>E(3) by blast
                also have "... = C.src (F (f, t) \\\<^sub>C
                                    (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t))) \<squnion>\<^sub>C
                                   F (f, t) \\\<^sub>C (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t))"
                proof -
                  have "C.src (F (f, t) \\\<^sub>C (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t))) =
                        C.trg (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t))"
                    by (metis "2" C.arr_prfx_join_self C.conI C.con_sym_ax
                        C.ide_implies_arr C.join_of_symmetric C.joinable_def
                        C.joinable_iff_join_not_null C.not_arr_null C.null_is_zero(1)
                        C.src_resid calculation)
                  also have "... = \<tau> (A.src f, B.src t) \\\<^sub>C
                                     (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t))"
                    by (metis C.arr_prfx_join_self C.join_def C.null_is_zero(2)
                        C.prfx_implies_con C.resid_join\<^sub>E(1) C.trg_def C.trg_join)
                  finally show ?thesis by argo
                qed
                also have "... = F (f, t) \\\<^sub>C
                                   (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t))"
                  by (metis C.arr_prfx_join_self C.arr_resid_iff_con C.conI
                      C.ide_implies_arr C.join_def C.join_src C.null_is_zero(2)
                      C.resid_join\<^sub>E(1))
                also have "... = (F (A.src f, t) \\\<^sub>C F (f, B.src t)) \\\<^sub>C
                                   (\<tau> (A.src f, B.src t) \\\<^sub>C F (f, B.src t))"
                proof -
                  have "F (f, t) \\\<^sub>C (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) =
                        (F (f, t) \\\<^sub>C F (f, B.src t)) \\\<^sub>C
                          (\<tau> (A.src f, B.src t) \\\<^sub>C F (f, B.src t))"
                    by (metis 2 C.con_sym_ax C.extensional_rts_axioms C.join_def
                        C.not_ide_null C.null_is_zero(2) C.residuation_axioms
                        extensional_rts.resid_join\<^sub>E(1) residuation.conI)
                  also have "... = (F (A.src f, t) \\\<^sub>C F (f, B.src t)) \\\<^sub>C
                                     (\<tau> (A.src f, B.src t) \\\<^sub>C F (f, B.src t))"
                    by (metis C.composite_ofE C.extensional C.join_ofE
                        F_f.naturality3 t)
                  finally show ?thesis by blast
                qed
                also have "... = F (A.src f, t) \\\<^sub>C
                                   (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t))"
                  by (metis 3 4 C.conI C.con_sym_ax C.join_def C.not_ide_null
                      C.null_is_zero(2) C.resid_join\<^sub>E(1))
                finally show ?thesis by blast
              qed
            qed
          qed
          have 1: "BC.joinable
                     (BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. G (A.src f, g))
                               (\<lambda>g. \<tau> (A.src f, g)))
                     (BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. F (A.trg f, g))
                               (\<lambda>g. F (f, g)))"
            using * BC.join_char(1) C.joinable_iff_join_not_null
                  F_f.preserves_arr F_f.transformation_axioms AxB.src_char
                  \<tau>.naturality3'\<^sub>E(2) \<tau>_src.transformation_axioms
            by force
          moreover have "BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. G (A.src f, g))
                                  (\<lambda>g. \<tau> (A.src f, g)) \<squnion>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                           BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. F (A.trg f, g))
                                    (\<lambda>g. F (f, g)) =
                         BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. G (A.trg f, g))
                                  (\<lambda>g. \<tau> (f, g))"
          proof -
            have "BC.Apex
                    (BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. G (A.src f, g))
                              (\<lambda>g. \<tau> (A.src f, g)))
                    (BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. F (A.trg f, g))
                              (\<lambda>g. F (f, g))) =
                  (\<lambda>g. G (A.trg f, g))"
            proof
              fix t
              show "BC.Apex
                      (BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. G (A.src f, g))
                                (\<lambda>g. \<tau> (A.src f, g)))
                      (BC.MkArr (\<lambda>g. F (A.src f, g)) (\<lambda>g. F (A.trg f, g))
                                (\<lambda>g. F (f, g))) t =
                    G (A.trg f, t)"
                using f \<tau>.naturality1 [of "(f, B.src t)"]
                      \<tau>.naturality2 [of "(A.trg f, t)"] AxB.trg_char AxB.src_char
                      \<tau>.G.extensional BC.Apex_def 
                by force
            qed
            moreover
            have "(\<lambda>t. (\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) \<squnion>\<^sub>C F (A.src f, t)) =
                  (\<lambda>g. \<tau> (f, g))"
            proof
              fix t
              have "B.arr t \<Longrightarrow> AxB.src (f, t) = (A.src f, B.src t)"
                by (simp add: AxB.src_char f)
              thus "(\<tau> (A.src f, B.src t) \<squnion>\<^sub>C F (f, B.src t)) \<squnion>\<^sub>C F (A.src f, t) =
                    \<tau> (f, t)"
                by (metis * B.arr_src_iff_arr C.arr_prfx_join_self C.con_sym_ax
                    C.join_def C.join_sym C.not_ide_null C.null_is_zero(2)
                    F_f.extensional \<tau>.naturality3'\<^sub>E(1))
            qed
            ultimately show ?thesis
              using 1 BC.join_char(2) by auto
          qed
          ultimately show ?thesis
            using 1 BC.join_is_join_of Curry_def f by fastforce
        qed
      qed
    qed

    lemma Uncurry_preserves_transformations:
    assumes "transformation A BC.resid F G \<tau>"
    shows "transformation AxB.resid C (Uncurry F) (Uncurry G) (Uncurry \<tau>)"
    proof -
      interpret \<tau>: transformation A BC.resid F G \<tau> using assms by auto
      interpret \<tau>: transformation_to_extensional_rts A BC.resid F G \<tau> ..
      interpret Uncurry_F: simulation AxB.resid C \<open>Uncurry F\<close>
        using \<tau>.F.simulation_axioms Uncurry_preserves_simulations by blast
      interpret Uncurry_G: simulation AxB.resid C \<open>Uncurry G\<close>
        using \<tau>.G.simulation_axioms Uncurry_preserves_simulations by blast
      interpret Uncurry_F: binary_simulation_between_weakly_extensional_rts
                             A B C \<open>Uncurry F\<close>
        ..
      interpret Uncurry_G: binary_simulation_between_weakly_extensional_rts
                             A B C \<open>Uncurry G\<close>
        ..
      show ?thesis
      proof
        show "\<And>t. \<not> AxB.arr t \<Longrightarrow> Uncurry \<tau> t = C.null"
          by (meson Uncurry_def)
        show "\<And>a. AxB.ide a \<Longrightarrow> C.src (Uncurry \<tau> a) = Uncurry F a"
          by (metis A.ide_implies_arr AxB.ide_char AxB.ide_implies_arr
              B.ide_implies_arr B.src_ide BC.Map_src Uncurry_simp
              E.map_def E.preserves_reflects_arr E.src_map
              Uncurry_F.preserves_reflects_arr \<tau>.preserves_arr \<tau>.preserves_src
              fst_conv snd_conv)
        show "\<And>a. AxB.ide a \<Longrightarrow> C.trg (Uncurry \<tau> a) = Uncurry G a"
          unfolding Uncurry_def
          using E.trg_map E.map_def BC.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S \<tau>.G.preserves_ide
          apply auto[1]
           apply (metis BC.Dom_resid BC.con_arr_src(2) BC.resid_src_arr
              \<tau>.preserves_trg)
          by (meson A.ide_implies_arr \<tau>.preserves_arr)
        fix f
        assume f: "AxB.arr f"
        interpret F_fst: transformation B C
                           \<open>BC.Map (F (A.src (fst f)))\<close>
                           \<open>BC.Map (F (A.trg (fst f)))\<close>
                           \<open>BC.Map (F (fst f))\<close>
        proof -
          have "(\<lambda>t2. Uncurry F (A.src (fst f), t2)) = BC.Map (F (A.src (fst f)))"
          proof
            fix t2
            show "Uncurry F (A.src (fst f), t2) = BC.Map (F (A.src (fst f))) t2"
              using Uncurry_def E.map_def f
              apply (cases "B.arr t2")
               apply auto[2]
              by (metis A.ide_src BC.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S \<tau>.F.preserves_ide
                  simulation.extensional)
          qed
          moreover have "(\<lambda>t2. Uncurry F (A.trg (fst f), t2)) =
                         BC.Map (F (A.trg (fst f)))"
          proof
            fix t2
            show "Uncurry F (A.trg (fst f), t2) = BC.Map (F (A.trg (fst f))) t2"
              using Uncurry_def E.map_def f
              apply (cases "B.arr t2")
               apply auto[2]
              by (metis A.ide_trg BC.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S \<tau>.F.preserves_ide
                  simulation.extensional)
          qed
          moreover have "(\<lambda>t2. Uncurry F (fst f, t2)) = BC.Map (F (fst f))"
          proof
            fix t2
            show "Uncurry F (fst f, t2) = BC.Map (F (fst f)) t2"
              using Uncurry_def E.map_def f
              apply (cases "B.arr t2")
               apply auto[2]
              by (metis BC.arrE \<tau>.F.preserves_reflects_arr
                  transformation.extensional)
          qed
          ultimately
          show "transformation B C
                 (BC.Map (F (A.src (fst f)))) (BC.Map (F (A.trg (fst f))))
                 (BC.Map (F (fst f)))"
            using f Uncurry_F.fixing_arr_gives_transformation_1 [of "fst f"]
            by fastforce
        qed
        interpret \<tau>_fst: transformation B C
                           \<open>BC.Map (F (A.src (fst f)))\<close>
                           \<open>BC.Map (G (A.trg (fst f)))\<close>
                           \<open>BC.Map (\<tau> (fst f))\<close>
          using f \<tau>.preserves_arr BC.arr_char
          by (metis A.ide_src BC.Map.simps(1) BC.apex_sym BC.src_simp
              BC.src_join_of(1) BC.trg_simp BC.trg_join_of(1) \<tau>.G.preserves_trg
              \<tau>.naturality2 \<tau>.naturality3 \<tau>.preserves_src AxB.arr_char)
        have 1: "Uncurry \<tau> (AxB.src f) \\\<^sub>C Uncurry \<tau> f = Uncurry G (AxB.trg f)"
        proof -
          have "Uncurry \<tau> (AxB.src f) \\\<^sub>C Uncurry \<tau> f =
                BC.Map (\<tau> (A.src (fst f)))
                       (B.src (snd f)) \\\<^sub>C BC.Map (\<tau> (fst f)) (snd f)"
            using Uncurry_def E.map_def f AxB.src_char AxB.trg_char
                  \<tau>.preserves_arr
            by simp
          also have X: "... = BC.Map (\<tau> (A.src (fst f))) (B.src (snd f)) \\\<^sub>C
                              (BC.Map (\<tau> (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                                 BC.Map (F (A.src (fst f))) (snd f))"
            using f \<tau>_fst.naturality3 C.join_is_join_of C.join_of_unique
            by (metis AxB.arr_char C.joinable_def)
          also have "... = (BC.Map (\<tau> (A.src (fst f))) (B.src (snd f)) \\\<^sub>C
                              BC.Map (F (A.src (fst f))) (snd f)) \\\<^sub>C
                           (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                              BC.Map (F (A.src (fst f))) (snd f))"
            using C.resid_join\<^sub>E(1)
            by (metis (no_types, lifting) X AxB.arr_char C.conE C.conI
                C.con_sym_ax C.con_with_join_of_iff(1) C.joinable_iff_join_not_null
                C.null_is_zero(2) \<tau>_fst.naturality3 f)
          also have "... = BC.Map (\<tau> (A.src (fst f))) (B.trg (snd f)) \\\<^sub>C
                           (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                              BC.Map (F (A.src (fst f))) (snd f))"
            by (metis (no_types, lifting) A.arr_src_iff_arr A.ide_src A.src_src
                A.trg_src AxB.arr_char BC.Dom_resid BC.arrE BC.con_arr_src(1)
                BC.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S \<tau>.F.preserves_ide \<tau>.naturality1 \<tau>.preserves_arr
                \<tau>.preserves_src f transformation.naturality1)
          also have "... = BC.Map (\<tau> (A.src (fst f))) (B.trg (snd f)) \\\<^sub>C
                           BC.Map (\<tau> (fst f)) (B.trg (snd f))"
            using f \<tau>_fst.naturality1 by fastforce
          also have "... = BC.Map (G (A.trg (fst f))) (B.trg (snd f))"
            by (metis A.ide_trg A.resid_src_arr AxB.arr_char B.arr_trg_iff_arr
                BC.Map_preserves_prfx C.apex_sym C.arr_resid_iff_con
                C.ide_iff_src_self C.prfx_implies_con C.src_resid \<tau>.preserves_prfx
                \<tau>_fst.G.preserves_trg \<tau>_fst.naturality1 \<tau>_fst.naturality2 f)
          also have "... = Uncurry G (AxB.trg f)"
            using Uncurry_def E.map_def f AxB.src_char AxB.trg_char \<tau>.preserves_arr
            by simp
          finally show ?thesis by blast
        qed
        have 2: "Uncurry F f \\\<^sub>C Uncurry \<tau> f = Uncurry G (AxB.trg f)"
        proof -
          have "Uncurry F f \\\<^sub>C Uncurry \<tau> f =
                BC.Map (F (fst f)) (snd f) \\\<^sub>C BC.Map (\<tau> (fst f)) (snd f)"
            using Uncurry_def E.map_def f AxB.src_char AxB.trg_char \<tau>.preserves_arr
            by simp
          also have "... = (BC.Map (F (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                            BC.Map (F (A.src (fst f))) (snd f)) \\\<^sub>C
                              BC.Map (\<tau> (fst f)) (snd f)"
            by (metis AxB.arr_char C.join_is_join_of C.join_of_unique
                C.joinable_def F_fst.naturality3 f)
          also have "... = (BC.Map (F (fst f)) (B.src (snd f)) \\\<^sub>C
                              BC.Map (\<tau> (fst f)) (snd f)) \<squnion>\<^sub>C
                           (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                              BC.Map (\<tau> (fst f)) (snd f))"
          proof -
            have 1: "C.joinable (BC.Map (F (fst f)) (B.src (snd f)))
                                (BC.Map (F (A.src (fst f))) (snd f))"
              by (meson AxB.arr_char C.joinable_def F_fst.naturality3 f)
            moreover have "BC.Map (\<tau> (fst f)) (snd f) \<frown>\<^sub>C
                           (BC.Map (F (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                              BC.Map (F (A.src (fst f))) (snd f))"
            proof -
              have 2: "BC.Map (F (A.src (fst f))) (snd f) \<frown>\<^sub>C
                       BC.Map (\<tau> (fst f)) (snd f)"
                using f
                by (meson AxB.arr_char C.arrE C.con_with_join_of_iff(2)
                    C.join_of_symmetric \<tau>_fst.naturality3 \<tau>_fst.preserves_arr)
              moreover have "BC.Map (\<tau> (fst f)) (snd f) \\\<^sub>C
                               BC.Map (F (A.src (fst f))) (snd f) \<frown>\<^sub>C
                             BC.Map (F (fst f)) (B.src (snd f)) \\\<^sub>C
                               BC.Map (F (A.src (fst f))) (snd f)"
              proof -
                have "BC.Map (F (fst f)) (B.src (snd f)) \\\<^sub>C
                        BC.Map (F (A.src (fst f))) (snd f) =
                      BC.Map (F (fst f)) (B.trg (snd f))"
                  using f F_fst.naturality1 by blast
                moreover
                have "BC.Map (\<tau> (fst f)) (snd f) \\\<^sub>C
                        BC.Map (F (A.src (fst f))) (snd f) =
                      BC.Map (\<tau> (fst f)) (B.trg (snd f))"
                  by (metis 2 C.composite_ofE C.cong_char C.join_ofE
                      C.residuation_axioms F_fst.F.simulation_axioms
                      \<tau>_fst.naturality1 \<tau>_fst.naturality3
                      residuation.con_implies_arr(1)
                      simulation.preserves_reflects_arr)
                moreover have "BC.Map (F (fst f)) (B.trg (snd f)) \<frown>\<^sub>C
                               BC.Map (\<tau> (fst f)) (B.trg (snd f))"
                proof -
                  have "BC.con (F (fst f)) (\<tau> (fst f))"
                    by (meson AxB.arr_char BC.con_with_join_of_iff(2)
                        BC.join_of_symmetric BC.residuation_axioms \<tau>.preserves_arr
                        assms f residuation.arr_def transformation.naturality3)
                  thus ?thesis
                    using f BC.con_char by simp
                qed
                ultimately show ?thesis
                  using C.con_sym by presburger
              qed
              ultimately show ?thesis
              using 1 C.con_with_join_of_iff(1) C.con_sym C.join_is_join_of
                C.joinable_implies_con
                by blast
            qed
            ultimately show ?thesis
              using C.resid_join\<^sub>E(3) by blast
          qed
          also have "... = BC.Map (G (A.trg (fst f))) (B.trg (snd f)) \<squnion>\<^sub>C
                           (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                              BC.Map (\<tau> (fst f)) (snd f))"
          proof -
            have "BC.Map (F (fst f)) (B.src (snd f)) \\\<^sub>C
                    BC.Map (\<tau> (fst f)) (snd f) =
                  BC.Map (F (fst f)) (B.src (snd f)) \\\<^sub>C
                    (BC.Map (\<tau> (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                       BC.Map (F (A.src (fst f))) (snd f))"
              using f \<tau>_fst.naturality3 C.join_is_join_of C.join_of_unique
              by (metis AxB.arr_char C.joinable_def)
            also have "... = (BC.Map (F (fst f)) (B.src (snd f)) \\\<^sub>C
                                BC.Map (\<tau> (fst f)) (B.src (snd f))) \\\<^sub>C
                             (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                BC.Map (\<tau> (fst f)) (B.src (snd f)))"
              by (metis (no_types, lifting) AxB.arr_char C.conI C.con_sym_ax
                  C.con_with_join_if(1) C.join_sym C.joinable_def
                  C.joinable_iff_join_not_null C.null_is_zero(2)
                  C.resid_join\<^sub>E(1) \<tau>_fst.naturality3 f C.conE)
            also have "... = BC.Map (G (A.trg (fst f))) (B.src (snd f)) \\\<^sub>C
                             (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                BC.Map (\<tau> (fst f)) (B.src (snd f)))"
            proof -
              have "BC.resid (F (fst f)) (\<tau> (fst f)) = G (A.trg (fst f))"
                by (metis AxB.arr_char BC.arrE BC.arr_prfx_join_self BC.con_def
                    BC.join_is_join_of BC.join_of_symmetric BC.join_of_unique
                    BC.joinable_def BC.resid_join\<^sub>E(1) BC.trg_def
                    \<tau>.G.preserves_trg \<tau>.naturality2 \<tau>.naturality3 f
                    BC.ide_implies_arr)
              thus ?thesis
                using f BC.Map_resid_ide
                by (metis A.arr_trg_iff_arr AxB.arr_char B.ide_src
                    \<tau>.G.preserves_reflects_arr BC.arr_resid_iff_con)
            qed
            also have "... = BC.Map (G (A.trg (fst f))) (B.src (snd f)) \\\<^sub>C
                               BC.Map (G (A.trg (fst f))) (snd f)"
              using AxB.arr_char \<tau>_fst.naturality2 f by presburger
            also have "... = BC.Map (G (A.trg (fst f))) (B.trg (snd f))"
              by (metis AxB.arr_char B.con_arr_src(2) B.resid_src_arr
                  \<tau>_fst.G.preserves_resid f)
            finally show ?thesis by simp
          qed
          also have "... = BC.Map (G (A.trg (fst f))) (B.trg (snd f)) \<squnion>\<^sub>C
                           BC.Map (G (A.trg (fst f))) (B.trg (snd f))"
          proof -
            have "BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                     BC.Map (\<tau> (fst f)) (snd f) =
                  BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                    (BC.Map (\<tau> (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                       BC.Map (F (A.src (fst f))) (snd f))"
              by (metis AxB.arr_char C.join_is_join_of C.join_of_unique
                  C.joinable_def \<tau>_fst.naturality3 f)
            also have "... = (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                BC.Map (F (A.src (fst f))) (snd f)) \\\<^sub>C
                             (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                                BC.Map (F (A.src (fst f))) (snd f))"
              by (metis (no_types, lifting) AxB.arr_char C.conE C.conI
                  C.con_sym_ax C.con_with_join_of_iff(1) C.join_def
                  C.null_is_zero(2) C.resid_join\<^sub>E(1) \<tau>_fst.naturality3
                  calculation f)
            also have "... = BC.Map (F (A.src (fst f))) (B.trg (snd f)) \\\<^sub>C
                             (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                                BC.Map (F (A.src (fst f))) (snd f))"
              using AxB.arr_char C.trg_def F_fst.F.preserves_trg f
              by presburger
            also have "... = BC.Map (G (A.trg (fst f))) (B.trg (snd f))"
              by (metis B.src_trg \<tau>_fst.naturality1 \<tau>_fst.naturality2)
            finally show ?thesis by simp
          qed
          also have "... = BC.Map (G (A.trg (fst f))) (B.trg (snd f))"
            using C.join_arr_self f by auto
          also have "... = Uncurry G (AxB.trg f)"
            using Uncurry_def E.map_def f AxB.src_char AxB.trg_char
                  \<tau>.preserves_arr
            by simp
          finally show ?thesis by blast
        qed
        have 3: "Uncurry \<tau> (AxB.src f) =
                 BC.Map (\<tau> (A.src (fst f))) (B.src (snd f))"
          using Uncurry_def E.map_def f AxB.src_char AxB.trg_char
                \<tau>.preserves_arr
          by simp
        have 4: "Uncurry F f = BC.Map (F (fst f)) (snd f)"
          using Uncurry_def E.map_def f by simp
        have 5: "Uncurry \<tau> (AxB.trg f) =
                 BC.Map (\<tau> (A.trg (fst f))) (B.trg (snd f))"
          using Uncurry_def E.map_def f AxB.src_char AxB.trg_char
                \<tau>.preserves_arr
          by simp
        show 6: "Uncurry \<tau> (AxB.src f) \\\<^sub>C Uncurry F f = Uncurry \<tau> (AxB.trg f)"
          using 3 4 5 AxB.arr_char B.con_arr_src(2) B.resid_src_arr
                BC.joinable_implies_con BC.resid_Map \<tau>.naturality1
                \<tau>.naturality3'\<^sub>E(2) f
          by presburger
        show 7: "Uncurry F f \\\<^sub>C Uncurry \<tau> (AxB.src f) = Uncurry G f"
          by (metis 3 4 AxB.arr_char B.con_arr_src(1) B.resid_arr_src BC.con_sym
              BC.joinable_implies_con BC.resid_Map Uncurry_simp E.map_def
              E.preserves_reflects_arr Uncurry_G.preserves_reflects_arr
              \<tau>.naturality2 \<tau>.naturality3'\<^sub>E(2) f fst_conv snd_conv)
        show "C.join_of (Uncurry \<tau> (AxB.src f)) (Uncurry F f) (Uncurry \<tau> f)"
        proof (intro C.join_ofI C.composite_ofI)
          have 8: "Uncurry \<tau> f \\\<^sub>C Uncurry \<tau> (AxB.src f) = Uncurry G f"
          proof -
            have "Uncurry \<tau> f \\\<^sub>C Uncurry \<tau> (AxB.src f) =
                  BC.Map (\<tau> (fst f)) (snd f) \\\<^sub>C BC.Map (\<tau> (A.src (fst f)))
                         (B.src (snd f))"
              using Uncurry_def E.map_def f AxB.src_char AxB.trg_char
                    \<tau>.preserves_arr
              by simp
            also have "... = (BC.Map (\<tau> (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                              BC.Map (F (A.src (fst f))) (snd f)) \\\<^sub>C
                                BC.Map (\<tau> (A.src (fst f))) (B.src (snd f))"
              by (metis AxB.arr_char C.join_is_join_of C.join_of_unique
                  C.joinable_def \<tau>_fst.naturality3 f)
            also have "... = BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                               BC.Map (\<tau> (A.src (fst f))) (B.src (snd f)) \<squnion>\<^sub>C
                             BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                               BC.Map (\<tau> (A.src (fst f))) (B.src (snd f))"
              by (metis 1 AxB.ide_trg C.conE C.conI C.join_def C.null_is_zero(2)
                  C.prfx_implies_con C.resid_join\<^sub>E(3) Uncurry_G.preserves_ide
                  calculation f C.con_sym)
            also have "... = BC.Map (G (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                             BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                               BC.Map (\<tau> (A.src (fst f))) (B.src (snd f))"
            proof -
              have "\<tau> (fst f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] \<tau> (A.src (fst f)) = G (fst f)"
                by (metis (no_types, lifting) A.con_arr_src(2)
                    BC.arr_resid_iff_con BC.join_src BC.resid_join\<^sub>E(3)
                    BC.src_resid BC.trg_def \<tau>.G.preserves_reflects_arr
                    \<tau>.naturality2 \<tau>.naturality3'\<^sub>E(2) \<tau>.naturality3'\<^sub>E(1)
                    \<tau>.preserves_con(1) f AxB.arr_char)
              thus ?thesis
                using f BC.Map_resid_ide BC.con_char
                by (metis (no_types, lifting) AxB.arr_char B.ide_src BC.arr_char
                    BC.resid_def \<tau>.G.preserves_reflects_arr)
            qed
            also have "... = BC.Map (G (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                             BC.Map (G (A.src (fst f))) (snd f)"
              by (metis A.arr_src_iff_arr A.ide_src A.trg_src
                  B.con_arr_src(1) B.resid_arr_src BC.joinable_implies_con
                  BC.prfx_implies_con BC.resid_Map BC.resid_arr_ide
                  \<tau>.F.preserves_ide \<tau>.G.preserves_ide \<tau>.naturality1 \<tau>.naturality2
                  \<tau>.naturality3'\<^sub>E(2) f AxB.arr_char)
            also have "... = BC.Map (G (fst f)) (snd f)"
              using Map_simulation_expansion \<tau>.G.simulation_axioms f
              by presburger
            also have "... = Uncurry G f"
              using Uncurry_def E.map_def f AxB.src_char AxB.trg_char
                    \<tau>.preserves_arr
              by simp
            finally show ?thesis by simp
          qed
          have 9: "Uncurry \<tau> f \\\<^sub>C Uncurry F f = Uncurry \<tau> (AxB.trg f)"
          proof -
            have "Uncurry \<tau> f \\\<^sub>C Uncurry F f =
                  BC.Map (\<tau> (fst f)) (snd f) \\\<^sub>C BC.Map (F (fst f)) (snd f)"
              using Uncurry_def E.map_def f AxB.src_char AxB.trg_char
                    \<tau>.preserves_arr
              by simp
            also have "... = (BC.Map (\<tau> (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                                BC.Map (F (A.src (fst f))) (snd f)) \\\<^sub>C
                             BC.Map (F (fst f)) (snd f)"
              by (metis AxB.arr_char C.join_is_join_of C.join_of_unique
                  C.joinable_def \<tau>_fst.naturality3 f)
            also have "... = BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                               BC.Map (F (fst f)) (snd f) \<squnion>\<^sub>C
                             BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                               BC.Map (F (fst f)) (snd f)"
              by (metis 1 2 8 C.conI C.con_sym_ax C.join_def C.not_arr_null
                  C.null_is_zero(2) C.resid_join\<^sub>E(3)
                  Uncurry_G.preserves_reflects_arr calculation f)
            also have "... = BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                               (BC.Map (F (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                                  BC.Map (F (A.src (fst f))) (snd f)) \<squnion>\<^sub>C
                                BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                  (BC.Map (F (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                                     BC.Map (F (A.src (fst f))) (snd f))"
              by (metis AxB.arr_char C.join_is_join_of C.join_of_unique
                  C.joinable_def F_fst.naturality3 f)
            also have "... = (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                                BC.Map (F (fst f)) (B.src (snd f))) \\\<^sub>C
                               (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                  BC.Map (F (fst f)) (B.src (snd f))) \<squnion>\<^sub>C
                                (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                   (BC.Map (F (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                                    BC.Map (F (A.src (fst f))) (snd f)))"
            proof -
              have "BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                      (BC.Map (F (fst f)) (B.src (snd f)) \<squnion>\<^sub>C
                    BC.Map (F (A.src (fst f))) (snd f)) =
                    (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                       BC.Map (F (A.src (fst f))) (snd f)) \\\<^sub>C
                    (BC.Map (F (fst f)) (B.src (snd f)) \\\<^sub>C
                       BC.Map (F (A.src (fst f))) (snd f))"
                using C.resid_join\<^sub>E(1) [of "BC.Map (F (fst f)) (B.src (snd f))"
                                           "BC.Map (F (A.src (fst f))) (snd f)"
                                           "BC.Map (\<tau> (fst f)) (B.src (snd f))"]
                by (metis AxB.arr_char C.conI C.con_sym_ax C.con_with_join_if(2)
                    C.joinable_def C.null_is_zero(2) F_fst.naturality3 f)
              also have "... = (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                                  BC.Map (F (fst f)) (B.src (snd f))) \\\<^sub>C
                                 (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                    BC.Map (F (fst f)) (B.src (snd f)))"
                using C.cube by blast
              finally show ?thesis by presburger
            qed
            also have "... = (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                                BC.Map (F (fst f)) (B.src (snd f))) \\\<^sub>C
                               (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                  BC.Map (F (fst f)) (B.src (snd f))) \<squnion>\<^sub>C
                             (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                BC.Map (F (fst f)) (B.src (snd f))) \\\<^sub>C
                               (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                  BC.Map (F (fst f)) (B.src (snd f)))"
              using C.resid_join\<^sub>E(2) [of "BC.Map (F (fst f)) (B.src (snd f))"
                                         "BC.Map (F (A.src (fst f))) (snd f)"
                                         "BC.Map (F (A.src (fst f))) (snd f)"]
              by (metis (no_types, lifting) AxB.arr_char C.conI
                  C.con_with_join_if(2) C.join_sym C.joinable_def
                  C.joinable_iff_join_not_null C.joinable_implies_con
                  F_fst.naturality3 f)
            also have "... = (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                                BC.Map (F (fst f)) (B.src (snd f))) \\\<^sub>C
                               (BC.Map (F (A.src (fst f))) (snd f) \\\<^sub>C
                                  BC.Map (F (fst f)) (B.src (snd f))) \<squnion>\<^sub>C
                                BC.Map (F (A.trg (fst f))) (B.trg (snd f))"
              using C.apex_sym C.trg_def F_fst.naturality1 F_fst.preserves_trg f
              by auto
            also have "... = (BC.Map (\<tau> (fst f)) (B.src (snd f)) \\\<^sub>C
                                BC.Map (F (fst f)) (B.src (snd f))) \\\<^sub>C
                               BC.Map (F (A.trg (fst f))) (snd f) \<squnion>\<^sub>C
                             BC.Map (F (A.trg (fst f))) (B.trg (snd f))"
              using AxB.arr_char F_fst.naturality2 f by presburger
            also have "... = BC.Map (\<tau> (A.trg (fst f))) (B.src (snd f)) \\\<^sub>C
                               BC.Map (F (A.trg (fst f))) (snd f) \<squnion>\<^sub>C
                             BC.Map (F (A.trg (fst f))) (B.trg (snd f))"
            proof -
              have "\<tau> (fst f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] F (fst f) =
                    (\<tau> (A.src (fst f)) \<squnion>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] F (fst f)) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] F (fst f)"
                by (metis AxB.arr_char BC.join_is_join_of BC.join_of_unique
                    BC.joinable_def \<tau>.naturality3 f)
              also have "... = \<tau> (A.src (fst f)) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] F (fst f) \<squnion>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                                 F (fst f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] F (fst f)"
                by (metis AxB.arr_char BC.arr_prfx_join_self BC.con_def BC.join_sym
                    BC.joinable_def BC.joinable_iff_join_not_null BC.not_ide_null
                    BC.resid_join\<^sub>E(3) \<tau>.naturality3 f)
              also have "... = \<tau> (A.src (fst f)) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] F (fst f)"
                by (metis A.arr_trg_iff_arr AxB.arr_char BC.join_src BC.join_sym
                    BC.src_resid BC.trg_def \<tau>.naturality1 \<tau>.preserves_arr f
                    BC.arr_resid_iff_con)
              also have "... = \<tau> (A.trg (fst f))"
                using \<tau>.naturality1 f by blast
              finally have "\<tau> (fst f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] F (fst f) = \<tau> (A.trg (fst f))"
                by blast
              thus ?thesis
                using BC.Map_resid_ide
                by (metis A.arr_trg_iff_arr B.ide_src BC.arr_resid_iff_con
                    \<tau>.preserves_arr f AxB.arr_char)
            qed
            also have "... =  BC.Map (\<tau> (A.trg (fst f))) (B.trg (snd f)) \<squnion>\<^sub>C
                                BC.Map (F (A.trg (fst f))) (B.trg (snd f))"
              by (metis (no_types, lifting) A.ide_trg A.src_trg AxB.arr_char BC.arrE
                  BC.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S BC.prfx_char \<tau>.F.preserves_ide \<tau>.G.preserves_ide
                  \<tau>.naturality2 f transformation.naturality1)
            also have "... = BC.Map (\<tau> (A.trg (fst f))) (B.trg (snd f))"
              by (metis (full_types) 1 2 5 6 7 8 AxB.cong_reflexive C.extensional
                  Uncurry_G.preserves_prfx calculation f C.cube)
            also have "... = Uncurry \<tau> (AxB.trg f)"
              using Uncurry_def E.map_def f AxB.src_char AxB.trg_char \<tau>.preserves_arr
              by simp
            finally show ?thesis by blast
          qed
          show "Uncurry \<tau> (AxB.src f) \<lesssim>\<^sub>C Uncurry \<tau> f"
            using f 1 Uncurry_G.preserves_ide AxB.ide_trg by presburger
          show "Uncurry F f \<lesssim>\<^sub>C Uncurry \<tau> f"
            using f 2 Uncurry_G.preserves_ide AxB.ide_trg by presburger
          show 10: "C.cong (Uncurry \<tau> f \\\<^sub>C Uncurry \<tau> (AxB.src f))
                       (Uncurry F f \\\<^sub>C Uncurry \<tau> (AxB.src f))"
            using 7 8 C.ide_trg C.trg_def f by auto
          show "C.cong (Uncurry \<tau> f \\\<^sub>C Uncurry F f)
                       (Uncurry \<tau> (AxB.src f) \\\<^sub>C Uncurry F f)"
            using 6 9 C.cube 10 by presburger
        qed
      qed
    qed

    lemma Uncurry_Curry:
    assumes "transformation AxB.resid C F G \<tau>"
    shows "Uncurry (Curry F G \<tau>) = \<tau>"
    proof
      interpret \<tau>: transformation AxB.resid C F G \<tau> using assms by auto
      interpret Curry_\<tau>: transformation A BC.resid
                           \<open>Curry3 F\<close> \<open>Curry3 G\<close> \<open>Curry F G \<tau>\<close>
        using assms Curry_preserves_transformations \<tau>.transformation_axioms
        by simp
      fix f
      have "\<not> AxB.arr f \<Longrightarrow> Uncurry (Curry F G \<tau>) f = \<tau> f"
        using Curry_def Uncurry_def \<tau>.extensional by auto
      moreover have "AxB.arr f \<Longrightarrow> Uncurry (Curry F G \<tau>) f = \<tau> f"
        by (simp add: Curry_\<tau>.preserves_arr Currying.Uncurry_def Currying_axioms
            E.map_def Map_Curry)
      ultimately show "Uncurry (Curry F G \<tau>) f = \<tau> f" by blast
    qed

    lemma Curry_Uncurry:
    assumes "transformation A BC.resid F G \<tau>"
    shows "Curry (Uncurry F) (Uncurry G) (Uncurry \<tau>) = \<tau>"
    proof
      interpret \<tau>: transformation A BC.resid F G \<tau>
        using assms by blast
      interpret Uncurry_\<tau>: transformation AxB.resid C
                             \<open>Uncurry F\<close> \<open>Uncurry G\<close> \<open>Uncurry \<tau>\<close>
        using assms Uncurry_preserves_transformations by auto
      fix f
      show "Curry (Uncurry F) (Uncurry G) (Uncurry \<tau>) f = \<tau> f"
      proof (cases "A.arr f")
        show "\<not> A.arr f \<Longrightarrow> ?thesis"
          using Curry_def \<tau>.extensional by auto
        assume f: "A.arr f"
        have "Curry (Uncurry F) (Uncurry G) (Uncurry \<tau>) f \<noteq> BC.null"
          by (metis A.not_arr_null \<tau>.F.extensional \<tau>.F.preserves_reflects_arr
              Curry_preserves_transformations f transformation.preserves_arr
              Uncurry_\<tau>.transformation_axioms)
        moreover
          have "BC.Dom (Curry (Uncurry F) (Uncurry G) (Uncurry \<tau>) f) =
                BC.Dom (\<tau> f)"
        proof
          fix g
          show "BC.Dom (Curry (Uncurry F) (Uncurry G) (Uncurry \<tau>) f) g =
                BC.Dom (\<tau> f) g"
            using Curry_def Uncurry_def E.map_def f Uncurry_\<tau>.preserves_arr
              \<tau>.preserves_arr
            apply auto[1]
             apply (metis A.ide_src BC.Map.simps(1) BC.src_simp BC.src_join_of(1)
                 \<tau>.naturality3 \<tau>.preserves_src)
            by (metis BC.arrE simulation.extensional transformation_def)
        qed
        moreover
          have "BC.Cod (Curry (Uncurry F) (Uncurry G) (Uncurry \<tau>) f) =
                BC.Cod (\<tau> f)"
        proof
          fix g
          have "BC.Cod (\<tau> f) = BC.Map (G (A.trg f))"
          proof -
            have "BC.trg (\<tau> f) = G (A.trg f)"
              using f \<tau>.preserves_trg
              by (metis BC.trg_join_of(2) \<tau>.G.preserves_trg \<tau>.naturality3
                  \<tau>.naturality2)
            thus ?thesis
              using f BC.trg_simp \<tau>.preserves_arr
              by (metis BC.Map.simps(1))
          qed
          thus "BC.Cod (Curry (Uncurry F) (Uncurry G) (Uncurry \<tau>) f) g =
                BC.Cod (\<tau> f) g"
            using Curry_def Uncurry_def E.map_def f Uncurry_\<tau>.preserves_arr
            apply auto[1]
            by (metis A.ide_trg BC.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S \<tau>.G.preserves_ide
                simulation.extensional)
        qed
        moreover
          have "BC.Map (Curry (Uncurry F) (Uncurry G) (Uncurry \<tau>) f) =
                BC.Map (\<tau> f)"
        proof
          fix g
          show "BC.Map (Curry (Uncurry F) (Uncurry G) (Uncurry \<tau>) f) g =
                BC.Map (\<tau> f) g"
            using Curry_def Uncurry_def E.map_def f Uncurry_\<tau>.preserves_arr
              \<tau>.preserves_arr
            apply auto[1]
            by (metis BC.arrE transformation.extensional)
        qed
        ultimately show ?thesis
          using BC.null_char
          by (metis BC.MkArr_Map BC.not_arr_null \<tau>.preserves_arr f)
      qed
    qed

    lemma src_Curry:
    assumes "transformation AxB.resid C F G \<tau>" and "A.arr f"
    shows "BC.src (Curry F G \<tau> f) = Curry3 F (A.src f)"
    proof -
      interpret \<tau>: transformation A \<open>(\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>])\<close> \<open>Curry3 F\<close> \<open>Curry3 G\<close>
                    \<open>Curry F G \<tau>\<close>
        using assms Curry_preserves_transformations by blast
      show ?thesis
        using assms(2)
        by (metis A.ide_src BC.src_join_of(1) \<tau>.naturality3 \<tau>.preserves_src)
    qed

    lemma trg_Curry:
    assumes "transformation AxB.resid C F G \<tau>" and "A.arr f"
    shows "BC.trg (Curry F G \<tau> f) = Curry3 G (A.trg f)"
    proof -
      interpret \<tau>: transformation A \<open>(\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>])\<close> \<open>Curry3 F\<close> \<open>Curry3 G\<close>
                     \<open>Curry F G \<tau>\<close>
        using assms Curry_preserves_transformations by blast
      show ?thesis
        using assms(2)
        by (metis BC.trg_join_of(2) \<tau>.G.preserves_trg \<tau>.naturality3 \<tau>.naturality2)
    qed

    lemma src_Uncurry:
    assumes "transformation A BC.resid F G \<tau>" and "AxB.arr f"
    shows "C.src (Uncurry \<tau> f) = Uncurry F (AxB.src f)"
    proof -
      interpret \<tau>: transformation AxB.resid C \<open>Uncurry F\<close> \<open>Uncurry G\<close>
                     \<open>Uncurry \<tau>\<close>
        using assms Uncurry_preserves_transformations by blast
      show ?thesis
        using assms(2)
        by (metis AxB.ide_src C.src_join_of(1) \<tau>.naturality3 \<tau>.preserves_src)
    qed

    lemma trg_Uncurry:
    assumes "transformation A BC.resid F G \<tau>" and "AxB.arr f"
    shows "C.trg (Uncurry \<tau> f) = Uncurry G (AxB.trg f)"
    proof -
      interpret \<tau>: transformation AxB.resid C \<open>Uncurry F\<close> \<open>Uncurry G\<close>
                     \<open>Uncurry \<tau>\<close>
        using assms Uncurry_preserves_transformations by blast
      show ?thesis
        using assms(2)
        by (metis C.trg_join_of(2) \<tau>.G.preserves_trg \<tau>.naturality3 \<tau>.naturality2)
    qed

  end

  subsection "Currying and Uncurrying as Inverse Simulations"

  context Currying
  begin

    sublocale AxB_C: exponential_rts AxB.resid C ..
    sublocale A_BC: exponential_rts A BC.resid ..

    notation AxB_C.resid         (infix "\\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>]" 55)
    notation AxB_C.con           (infix "\<frown>\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>]" 55)
    notation A_BC.resid          (infix "\\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>]" 55)
    notation A_BC.con            (infix "\<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>]" 50)

    definition CURRY :: "('a \<times> 'b, 'c) AxB_C.arr \<Rightarrow> ('a, ('b, 'c) BC.arr) A_BC.arr"
    where "CURRY \<equiv>
           (\<lambda>X. if AxB_C.arr X
                then A_BC.MkArr
                       (Curry (AxB_C.Dom X) (AxB_C.Dom X) (AxB_C.Dom X))
                       (Curry (AxB_C.Cod X) (AxB_C.Cod X) (AxB_C.Cod X))
                       (Curry (AxB_C.Dom X) (AxB_C.Cod X) (AxB_C.Map X))
                else A_BC.null)"

    lemma Dom_CURRY [simp]:
    assumes "AxB_C.arr f"
    shows "A_BC.Dom (CURRY f) =
           Curry (AxB_C.Dom f) (AxB_C.Dom f) (AxB_C.Dom f)"
      using assms CURRY_def by auto

    lemma Cod_CURRY [simp]:
    assumes "AxB_C.arr f"
    shows "A_BC.Cod (CURRY f) =
           Curry (AxB_C.Cod f) (AxB_C.Cod f) (AxB_C.Cod f)"
      using assms CURRY_def by auto

    lemma Map_CURRY [simp]:
    assumes "AxB_C.arr f"
    shows "A_BC.Map (CURRY f) =
           Curry (AxB_C.Dom f) (AxB_C.Cod f) (AxB_C.Map f)"
      using assms CURRY_def by auto

    lemma CURRY_preserves_con:
    assumes con: "AxB_C.con t u"
    shows "A_BC.con (CURRY t) (CURRY u)"
    proof (unfold A_BC.con_char, intro conjI)
      have t: "AxB_C.arr t"
        using AxB_C.con_implies_arr(1) con by blast
      have u: "AxB_C.arr u"
        using AxB_C.con_implies_arr(2) con by blast
      show "CURRY t \<noteq> AxB_C.Null"
        unfolding CURRY_def
        using AxB_C.con_implies_arr(1) con by force
      show "transformation A BC.resid
              (A_BC.Dom (CURRY t)) (A_BC.Cod (CURRY t))
              (A_BC.Map (CURRY t))"
        using CURRY_def A_BC.null_char \<open>CURRY t \<noteq> AxB_C.Null\<close>
              Curry_preserves_transformations
        by fastforce
      show "CURRY u \<noteq> AxB_C.Null"
        unfolding CURRY_def
        using AxB_C.con_implies_arr(2) con by force
      show "transformation A BC.resid
              (A_BC.Dom (CURRY u)) (A_BC.Cod (CURRY u))
              (A_BC.Map (CURRY u))"
        using CURRY_def A_BC.null_char \<open>CURRY u \<noteq> AxB_C.Null\<close>
              Curry_preserves_transformations
        by auto
      show "A_BC.Dom (CURRY t) = A_BC.Dom (CURRY u)"
        using CURRY_def A_BC.Dom.simps(1) A_BC.null_char AxB_C.con_char
              \<open>CURRY t \<noteq> AxB_C.Null\<close> \<open>CURRY u \<noteq> AxB_C.Null\<close> con
        by presburger
      show "\<forall>a. A.ide a \<longrightarrow>
                  BC.con (A_BC.Map (CURRY t) a) (A_BC.Map (CURRY u) a)"
      proof (intro allI impI)
        fix a
        assume a: "A.ide a"
        have "A_BC.Map (CURRY t) a =
              Curry (AxB_C.Dom t) (AxB_C.Cod t) (AxB_C.Map t) a"
          using a t CURRY_def by simp
        moreover have "A_BC.Map (CURRY u) a =
                       Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u) a"
          using a u CURRY_def by simp
        moreover
        have "BC.con (Curry (AxB_C.Dom t) (AxB_C.Cod t) (AxB_C.Map t) a)
                     (Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u) a)"
          unfolding BC.con_char
          using a t u con
          apply clarsimp
          apply (intro conjI)
          subgoal using AxB_C.arr_char AxB_C.null_char
            Curry_preserves_transformations
            by (metis A.ide_implies_arr BC.arr_char
              transformation.preserves_arr)
          subgoal using AxB_C.arr_char AxB_C.null_char
            Curry_preserves_transformations
            by (metis A.ide_implies_arr BC.arr_char
              transformation.preserves_arr)
          subgoal using AxB_C.arr_char AxB_C.null_char
            Curry_preserves_transformations
            by (metis A.ide_implies_arr BC.arr_char
              transformation.preserves_arr)
          subgoal by (meson A.ide_implies_arr AxB_C.arrE BC.arr_char
              Curry_preserves_transformations Currying_axioms
              transformation.preserves_arr)
          (* remaining 2 subgoals *) unfolding Curry_def
            using AxB_C.con_char
            by auto
        ultimately
        show "BC.con (A_BC.Map (CURRY t) a) (A_BC.Map (CURRY u) a)"
          by auto
      qed
    qed

    lemma CURRY_is_extensional:
    assumes "\<not> AxB_C.arr t"
    shows "CURRY t = A_BC.null"
      using assms CURRY_def by simp

    lemma CURRY_preserves_arr:
    assumes "AxB_C.arr t"
    shows "A_BC.arr (CURRY t)"
      using assms CURRY_preserves_con by blast

    lemma Dom_Map_CURRY_resid:
    assumes con: "AxB_C.con t u" and f: "A.arr f"
    shows "BC.Dom (A_BC.Map (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) f) =
           BC.Dom (A_BC.Map (CURRY t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u) f)"
    proof -
      have t: "AxB_C.arr t"
        using assms(1) AxB_C.con_implies_arr(1) by blast
      have u: "AxB_C.arr u"
        using assms(1) AxB_C.con_implies_arr(2) by blast
      have "A_BC.con (CURRY t) (CURRY u)"
        using con CURRY_preserves_con by simp
      interpret Curry_trg_u: simulation A BC.resid \<open>Curry3 (AxB_C.Cod t)\<close>
        using t
        by (meson AxB_C.arrE Curry_preserves_simulations transformation_def)
      interpret Curry_trg_u: simulation_to_extensional_rts A BC.resid
                               \<open>Curry3 (AxB_C.Cod t)\<close>
        ..
      interpret Curry_trg_u: transformation A BC.resid
                               \<open>Curry3 (AxB_C.Cod u)\<close>
                               \<open>Curry3 (AxB_C.Cod u)\<close>
                               \<open>Curry3 (AxB_C.Cod u)\<close>
        using u
        by (metis A_BC.arr_MkArr A_BC.arr_trg_iff_arr A_BC.trg_char
            Cod_CURRY CURRY_preserves_arr)
      interpret Curry_u: transformation A BC.resid
                           \<open>Curry3 (AxB_C.Dom u)\<close>
                           \<open>Curry3 (AxB_C.Cod u)\<close>
                           \<open>Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)\<close>
        using u Curry_preserves_transformations by blast
      interpret Curry_u: transformation_to_extensional_rts A BC.resid
                           \<open>Curry3 (AxB_C.Dom u)\<close>
                           \<open>Curry3 (AxB_C.Cod u)\<close>
                           \<open>Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)\<close>
        ..
      have "BC.Dom (A_BC.Map (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) f) =
            (\<lambda>g. AxB_C.Cod u (A.src f, g))"
        using f con Dom_Curry by simp
      also
      have "... = BC.Dom (Curry3 (AxB_C.Cod u) f)"
        using f u Dom_Curry by auto
      also
      have "... = BC.Dom
                    (BC.join
                      (A_BC.Map (CURRY t) (A.src f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                         Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)
                               (A.src f))
                      (Curry3 (AxB_C.Cod u) f))"
      proof -
        have "BC.joinable
                (Curry3 (AxB_C.Cod u) f)
                (A_BC.Map (CURRY t) (A.src f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                   Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u) (A.src f))"
        proof -
          have "BC.joinable
                  (Curry3 (AxB_C.Dom u) f)
                  (A_BC.Map (CURRY t) (A.src f))"
            using u f
            by (metis A_BC.con_char BC.join_of_symmetric BC.joinable_def
                Dom_CURRY \<open>A_BC.con (CURRY t) (CURRY u)\<close>
                transformation.naturality3)
          moreover
          have 1: "Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)
                     (A.src f) \<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                   (Curry3 (AxB_C.Dom u) f \<squnion>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                      A_BC.Map (CURRY t) (A.src f))"
          proof (intro BC.con_with_join_if)
            show "BC.joinable
                    (Curry3 (AxB_C.Dom u) f)
                    (A_BC.Map (CURRY t) (A.src f))"
              using calculation by blast
            show "A_BC.Map (CURRY t) (A.src f) \<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                  Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u) (A.src f)"
              using A_BC.con_char \<open>CURRY t \<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u\<close> f u by auto
            show "Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)
                   (A.src f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                    A_BC.Map (CURRY t) (A.src f) \<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                  Curry3 (AxB_C.Dom u) f \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>] A_BC.Map (CURRY t) (A.src f)"
              using u A.ide_trg A_BC.con_char BC.conE BC.conI BC.con_sym_ax
                    BC.cube Dom_CURRY Map_CURRY
                    \<open>CURRY t \<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u\<close>
                    f transformation.naturality1
              by (metis (full_types))
          qed
          ultimately
          have "(Curry3 (AxB_C.Dom u) f \<squnion>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                   A_BC.Map (CURRY t) (A.src f)) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                   Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u) (A.src f) =
                 Curry3 (AxB_C.Dom u) f \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                   Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)
                     (A.src f) \<squnion>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                 A_BC.Map (CURRY t) (A.src f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                   Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u) (A.src f)"
            using BC.resid_join\<^sub>E(3)
                    [of "Curry3 (AxB_C.Dom u) f" "A_BC.Map (CURRY t) (A.src f)"
                        "Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)
                               (A.src f)"]
            by blast
          hence "BC.joinable
                   (Curry3 (AxB_C.Dom u) f \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                      Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)
                        (A.src f))
                   (A_BC.Map (CURRY t) (A.src f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                      Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)
                        (A.src f))"
            by (metis 1 BC.arr_resid BC.con_sym BC.joinable_iff_arr_join)
          moreover
          have "Curry3 (AxB_C.Cod u) f =
                Curry3 (AxB_C.Dom u) f \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                  Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u) (A.src f)"
            using f u Curry_u.naturality2 by presburger
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          using f u BC.src_char BC.src_join BC.Dom_join BC.join_sym by auto
      qed
      also have "... = BC.Dom (A_BC.Map (CURRY t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u) f)"
        using f u con CURRY_preserves_con A_BC.Map_resid Dom_Curry
              Cod_Curry Cod_CURRY
        by simp
      finally show ?thesis by blast
    qed

    lemma Cod_Map_CURRY_resid:
    assumes con: "AxB_C.con t u" and f: "A.arr f"
    shows "BC.Cod (A_BC.Map (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) f) =
           BC.Cod (A_BC.Apex (CURRY t) (CURRY u) f)"
    proof -
      have t: "AxB_C.arr t"
        using assms(1) AxB_C.con_implies_arr(1) by blast
      have u: "AxB_C.arr u"
        using assms(1) AxB_C.con_implies_arr(2) by blast
      interpret Apex: simulation
                        A BC.resid \<open>A_BC.Apex (CURRY t) (CURRY u)\<close>
        using assms CURRY_preserves_con A_BC.Apex_is_simulation A_BC.con_char
        by blast
      interpret Cod_u: simulation AxB.resid C \<open>AxB_C.Cod u\<close>
        using AxB_C.ide_trg AxB_C.trg_char u by force
      interpret t: transformation
                     AxB.resid C \<open>AxB_C.Dom t\<close> \<open>AxB_C.Cod t\<close> \<open>AxB_C.Map t\<close>
        using t AxB_C.arr_char by blast
      interpret u: transformation
                     AxB.resid C \<open>AxB_C.Dom u\<close> \<open>AxB_C.Cod u\<close> \<open>AxB_C.Map u\<close>
        using u AxB_C.arr_char by blast

      have "BC.Cod (A_BC.Map (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) f) =
            BC.Cod (Curry3 (AxB_C.Apex t u) f)"
        by (simp add: con Curry_def)
      also have "... = BC.Cod (A_BC.Apex (CURRY t) (CURRY u) f)"
      proof
        fix g
        show "BC.Cod (Curry3 (AxB_C.Apex t u) f) g =
              BC.Cod (A_BC.Apex (CURRY t) (CURRY u) f) g"
        proof (cases "B.arr g")
          assume g: "\<not> B.arr g"
          show ?thesis
            using f g Curry_def AxB_C.Apex_def A_BC.Apex_def
                  CURRY_preserves_con
            apply simp
            using BC.Apex_def BC.Cod_resid BC.arr_resid_iff_con
                  Apex.preserves_reflects_arr
            by presburger
          next
          assume g: "B.arr g"
          show ?thesis
          proof -
            have "BC.Cod (Curry3 (AxB_C.Apex t u) f) g =
                  AxB_C.Cod u (A.trg f, g) \\\<^sub>C
                    (AxB_C.Map t (AxB.src (A.trg f, g)) \\\<^sub>C
                       AxB_C.Map u (AxB.src (A.trg f, g)))"
              using assms t u f g AxB.con_char Cod_Curry AxB_C.Apex_def
              by simp
            also have "... = BC.Cod
                               (A_BC.Cod (CURRY u) f \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                                 (A_BC.Map (CURRY t) (A.src f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                                  A_BC.Map (CURRY u) (A.src f))) g"
            proof -
              have "BC.con (A_BC.Map (CURRY t) (A.src f)) 
                             (A_BC.Map (CURRY u) (A.src f))"
                using assms f g t u AxB_C.con_char BC.con_char
                      CURRY_preserves_con
                by (metis (no_types, lifting) A_BC.Apex_def BC.arr_char
                    BC.conI BC.null_char Apex.simulation_axioms
                    simulation.preserves_reflects_arr)
              moreover have "BC.con (A_BC.Cod (CURRY u) f)
                                      (A_BC.Map (CURRY t) (A.src f) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                                         A_BC.Map (CURRY u) (A.src f))"
                using assms f g t u AxB_C.con_char BC.con_char
                      CURRY_preserves_con
                by (metis A_BC.Apex_def BC.arr_char BC.conI BC.null_char
                  Apex.simulation_axioms simulation.preserves_reflects_arr)
              moreover have "AxB_C.Cod u (A.trg f, g) \\\<^sub>C
                               (AxB_C.Map t (AxB.src (A.trg f, g)) \\\<^sub>C
                                AxB_C.Map u (AxB.src (A.trg f, g))) =
                             (AxB_C.Cod u (A.src f, g) \\\<^sub>C
                                (AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                   AxB_C.Map u (A.src f, B.src g))) \\\<^sub>C
                             (AxB_C.Cod u (f, B.src g) \\\<^sub>C
                                (AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                   AxB_C.Map u (A.src f, B.src g) \<squnion>\<^sub>C
                                 AxB_C.Cod u (A.src f, B.src g)))"
              proof -
                have "(AxB_C.Cod u (A.src f, g) \\\<^sub>C
                                (AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                   AxB_C.Map u (A.src f, B.src g))) \\\<^sub>C
                             (AxB_C.Cod u (f, B.src g) \\\<^sub>C
                                (AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                   AxB_C.Map u (A.src f, B.src g) \<squnion>\<^sub>C
                                 AxB_C.Cod u (A.src f, B.src g))) =
                      (AxB_C.Cod u (A.src f, g) \\\<^sub>C
                        (AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                           AxB_C.Map u (A.src f, B.src g))) \\\<^sub>C
                        (AxB_C.Cod u (f, B.src g) \\\<^sub>C
                          (AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                             AxB_C.Map u (A.src f, B.src g)))"
                proof -
                  have "C.src (AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                 AxB_C.Map u (A.src f, B.src g)) =
                        AxB_C.Cod u (A.src f, B.src g)"
                  proof -
                    have "C.src (AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                   AxB_C.Map u (A.src f, B.src g)) =
                          C.trg (AxB_C.Map u (A.src f, B.src g))"
                      using AxB_C.con_char con f g by force
                    also have "... = AxB_C.Cod u (A.src f, B.src g)"
                      by (metis A.ide_src AxB.product_rts_axioms
                          AxB_C.Map.simps(1) AxB_C.Map_resid_ide
                          AxB_C.con_arr_self AxB_C.trg_char
                          AxB_C.trg_def B.ide_src C.trg_def f g
                          fst_conv product_rts.ide_char snd_conv u)
                    finally show ?thesis by blast
                  qed
                  thus ?thesis
                    using C.join_src
                    by (metis C.arr_resid C.conI C.join_sym
                        C.null_is_zero(1-2))
                qed
                also have "... = (AxB_C.Cod u (A.src f, g) \\\<^sub>C
                                    AxB_C.Cod u (f, B.src g)) \\\<^sub>C
                                 ((AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                     AxB_C.Map u (A.src f, B.src g)) \\\<^sub>C
                                  AxB_C.Cod u (f, B.src g))"
                  using C.cube by blast
                also have "... = AxB_C.Cod u (A.trg f, g) \\\<^sub>C
                                 ((AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                     AxB_C.Map u (A.src f, B.src g)) \\\<^sub>C
                                  AxB_C.Cod u (f, B.src g))"
                  by (metis A.con_arr_src(2) A.resid_src_arr AxB.con_char
                      AxB.resid_def B.con_arr_src(1) B.resid_arr_src
                      Cod_u.preserves_resid f g fst_conv snd_conv)
                also have "... = AxB_C.Cod u (A.trg f, g) \\\<^sub>C
                                 ((AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                     AxB_C.Map u (A.src f, B.src g)) \\\<^sub>C
                                  (AxB_C.Dom u (f, B.src g) \\\<^sub>C
                                     AxB_C.Map u (A.src f, B.src g)))"
                  by (metis AxB.arr_char AxB.src_char B.arr_src_iff_arr
                      B.src_src f g fst_conv snd_conv u.naturality2)
                also have "... = AxB_C.Cod u (A.trg f, g) \\\<^sub>C
                                 ((AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                     AxB_C.Dom u (f, B.src g)) \\\<^sub>C
                                  (AxB_C.Map u (A.src f, B.src g) \\\<^sub>C
                                     AxB_C.Dom u (f, B.src g)))"
                  using C.cube by presburger
                also have "... = AxB_C.Cod u (A.trg f, g) \\\<^sub>C
                                 ((AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                                     AxB_C.Dom t (f, B.src g)) \\\<^sub>C
                                  (AxB_C.Map u (A.src f, B.src g) \\\<^sub>C
                                     AxB_C.Dom u (f, B.src g)))"
                  using assms
                  by (simp add: AxB_C.con_char)
                also have "... = AxB_C.Cod u (A.trg f, g) \\\<^sub>C
                                 (AxB_C.Map t (A.trg f, B.src g) \\\<^sub>C
                                    AxB_C.Map u (A.trg f, B.src g))"
                proof -
                  have "AxB_C.Map t (A.src f, B.src g) \\\<^sub>C
                          AxB_C.Dom t (f, B.src g) =
                        AxB_C.Map t (A.trg f, B.src g)"
                    by (metis AxB.arr_char AxB.src_char AxB.trg_char
                        B.arr_src_iff_arr B.src_src B.trg_src f g
                        fst_conv snd_conv t.naturality1)
                  moreover have "AxB_C.Map u (A.src f, B.src g) \\\<^sub>C
                                   AxB_C.Dom u (f, B.src g) =
                                 AxB_C.Map u (A.trg f, B.src g)"
                    by (metis AxB.arr_char AxB.src_char AxB.trg_char
                        B.arr_src_iff_arr B.src_src B.trg_src f g
                        fst_conv snd_conv u.naturality1)
                  ultimately show ?thesis by presburger
                qed
                also have "... = AxB_C.Cod u (A.trg f, g) \\\<^sub>C
                                   (AxB_C.Map t (AxB.src (A.trg f, g)) \\\<^sub>C
                                      AxB_C.Map u (AxB.src (A.trg f, g)))"
                  by (simp add: AxB.src_char f g)
                finally show ?thesis by argo
              qed
              ultimately show ?thesis
                using assms f g t u AxB_C.con_char CURRY_preserves_con BC.Apex_def
                      Dom_Curry Cod_Curry Map_Curry BC.Cod_resid BC.Dom_resid
                by simp
            qed
            also have "... = BC.Cod (A_BC.Apex (CURRY t) (CURRY u) f) g"
              using assms f g CURRY_preserves_con CURRY_preserves_arr A_BC.Apex_def
              by simp
            finally show ?thesis by auto
          qed
        qed
      qed
      finally show ?thesis by blast
    qed
              
    lemma Map_Map_CURRY_resid:
    assumes con: "AxB_C.con t u" and f1: "A.arr f1"
    shows "BC.Map (A_BC.Map (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) f1) =
           BC.Map (A_BC.Map (A_BC.resid (CURRY t) (CURRY u)) f1)"
    proof -
      have t: "AxB_C.arr t"
        using assms(1) AxB_C.con_implies_arr(1) by blast
      have u: "AxB_C.arr u"
        using assms(1) AxB_C.con_implies_arr(2) by blast
      interpret t: transformation
                     AxB.resid C \<open>AxB_C.Dom t\<close> \<open>AxB_C.Cod t\<close> \<open>AxB_C.Map t\<close>
        using t AxB_C.arr_char [of t] by blast
      interpret t: transformation_of_binary_simulations
                     A B C \<open>AxB_C.Dom t\<close> \<open>AxB_C.Cod t\<close> \<open>AxB_C.Map t\<close>
        ..
      interpret u: transformation
                     AxB.resid C \<open>AxB_C.Dom u\<close> \<open>AxB_C.Cod u\<close> \<open>AxB_C.Map u\<close>
        using u AxB_C.arr_char [of u] by blast
      interpret u: transformation_of_binary_simulations
                     A B C \<open>AxB_C.Dom u\<close> \<open>AxB_C.Cod u\<close> \<open>AxB_C.Map u\<close>
        ..
      interpret tu: transformation
                      AxB.resid C \<open>AxB_C.Cod u\<close> \<open>AxB_C.Apex t u\<close>
                      \<open>AxB_C.Map (t \\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)\<close>
        using con AxB_C.arr_char [of "t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u"] by simp
      interpret tu: transformation_to_extensional_rts AxB.resid C
                      \<open>AxB_C.Cod u\<close> \<open>AxB_C.Apex t u\<close> \<open>AxB_C.Map (t \\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)\<close>
        ..
      interpret Curry_t: transformation A BC.resid
                           \<open>Curry3 (AxB_C.Dom t)\<close>
                           \<open>Curry3 (AxB_C.Cod t)\<close>
                           \<open>Curry (AxB_C.Dom t) (AxB_C.Cod t) (AxB_C.Map t)\<close>
        using t Curry_preserves_transformations by blast
      interpret Curry_u: transformation A BC.resid
                           \<open>Curry3 (AxB_C.Dom u)\<close>
                           \<open>Curry3 (AxB_C.Cod u)\<close>
                           \<open>Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)\<close>
        using u Curry_preserves_transformations by blast
      interpret Apex: simulation
                        A BC.resid \<open>A_BC.Apex (CURRY t) (CURRY u)\<close>
        using assms CURRY_preserves_con A_BC.Apex_is_simulation A_BC.con_char
        by blast
      interpret Apex: simulation_to_extensional_rts
                        A BC.resid \<open>A_BC.Apex (CURRY t) (CURRY u)\<close>
        ..
      interpret Cod_u: simulation AxB.resid C \<open>AxB_C.Cod u\<close>
        using AxB_C.ide_trg AxB_C.trg_char u by force
      interpret Cod_u: binary_simulation A B C \<open>AxB_C.Cod u\<close> ..
      interpret Cod_u: binary_simulation_between_weakly_extensional_rts
                         A B C \<open>AxB_C.Cod u\<close>
        ..

      have *: "\<And>f2. B.arr f2 \<Longrightarrow>
                    ((AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                        AxB_C.Map u (A.src f1, B.src f2) \<squnion>\<^sub>C
                      AxB_C.Cod u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                     AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
                    AxB_C.Cod u (A.src f1, f2) =
                    AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2)"
      proof -
        fix f2
        assume f2: "B.arr f2"
        have 1:
          "Curry (AxB_C.Dom t) (AxB_C.Cod t) (AxB_C.Map t) (A.src f1) \<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
           Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u) (A.src f1)"
          by (metis A.ide_src A_BC.con_char con Map_CURRY f1
              CURRY_preserves_con t u)
        have "((AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                  AxB_C.Map u (A.src f1, B.src f2) \<squnion>\<^sub>C
                AxB_C.Cod u (A.src f1, B.src f2)) \<squnion>\<^sub>C
               AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
              AxB_C.Cod u (A.src f1, f2) =
              (AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                 AxB_C.Map u (A.src f1, B.src f2) \<squnion>\<^sub>C
               AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
              AxB_C.Cod u (A.src f1, f2)"
          using AxB_C.Map_resid_ide con f1 f2 by force
        also have "... = (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                          AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C AxB_C.Cod u (A.src f1, f2)"
          using f1 f2 con AxB_C.Map_resid_ide by simp
        also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \<squnion>\<^sub>C
                         AxB_C.Cod u (A.src f1, f2)"
          using AxB.src_char AxB_C.Map_resid_ide con f1 f2 by force
        also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2)"
        proof (intro C.join_eqI)
          show 2: "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \<lesssim>\<^sub>C
                   AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2)"
          proof -
            have "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \\\<^sub>C
                    AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) =
                 AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \\\<^sub>C
                    (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2)) \<squnion>\<^sub>C
                       AxB_C.Cod u (f1, f2))"
              using f1 f2 AxB.prfx_char tu.naturality3
              by (metis AxB.arr_char C.join_is_join_of C.join_of_unique
                  C.joinable_def fst_conv snd_conv)
            also have "... = (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \\\<^sub>C
                                AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2))) \\\<^sub>C
                             (AxB_C.Cod u (f1, f2) \\\<^sub>C
                                AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2)))"
              using C.resid_join\<^sub>E(2)
                      [of "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2))"
                          "AxB_C.Cod u (f1, f2)"
                          "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2)"]
              by (metis A.cong_reflexive AxB.prfx_char B.ide_trg
                  B.resid_src_arr C.conI C.joinable_iff_join_not_null
                  C.not_ide_null C.null_is_zero(2) calculation
                  f1 f2 fst_conv snd_conv tu.preserves_prfx)
            also have "... = AxB_C.Apex t u (f1, B.src f2) \\\<^sub>C
                             (AxB_C.Cod u (f1, f2) \\\<^sub>C
                                AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2)))"
            proof -
              have "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \\\<^sub>C
                                AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2)) =
                    (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                     AxB_C.Cod u (f1, B.src f2)) \\\<^sub>C
                      AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2))"
                using AxB.src_char AxB_C.Map_resid_ide con f1 f2 by fastforce
              also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                 AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2)) \<squnion>\<^sub>C
                               AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                 AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2))"
                using C.resid_join\<^sub>E(3)
                by (metis AxB.arr_char AxB.src_char B.arr_src_iff_arr B.src_src
                    C.arr_prfx_join_self C.joinable_def C.prfx_implies_con
                    f1 f2 fst_conv snd_conv tu.naturality3)
              also have "... = AxB_C.Apex t u (A.src f1, B.src f2) \<squnion>\<^sub>C
                               AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                 AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (AxB.src (f1, f2))"
                using AxB.src_char C.trg_def f1 f2 tu.preserves_trg by fastforce
              also have "... = AxB_C.Apex t u (A.src f1, B.src f2) \<squnion>\<^sub>C
                               AxB_C.Apex t u (f1, B.src f2)"
                using AxB.src_char AxB_C.Map_resid_ide AxB_C.Apex_def con f2
                by force
              also have "... = AxB_C.Apex t u (f1, B.src f2)"
              proof -
                have "C.prfx (AxB_C.Apex t u (A.src f1, B.src f2))
                             (AxB_C.Apex t u (f1, B.src f2))"
                  by (simp add: f1 f2)
                thus ?thesis
                  by (metis AxB.arr_char AxB.ide_src AxB.src_char
                      B.arr_src_iff_arr C.join_src C.prfx_implies_con
                      C.src_ide f1 f2 fst_conv snd_conv transformation_def
                      tu.G.preserves_ide tu.G.preserves_reflects_arr
                      tu.transformation_axioms
                      weakly_extensional_rts.con_imp_eq_src)
              qed
              finally show ?thesis by auto
            qed
            also
            have "... = AxB_C.Apex t u (f1, B.src f2) \\\<^sub>C AxB_C.Apex t u (f1, f2)"
              by (simp add: f1 f2 tu.naturality2)
            also have "... = AxB_C.Apex t u (A.trg f1, B.trg f2)"
              by (metis A.residuation_axioms A.trg_def AxB.con_char AxB.resid_def
                  B.con_arr_src(2) B.resid_src_arr f1 f2 fst_conv residuation.arrE
                  snd_conv tu.G.preserves_resid)
            finally have "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \\\<^sub>C
                            AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) =
                          AxB_C.Apex t u (A.trg f1, B.trg f2)"
              by blast
            moreover have "C.ide ..."
              by (simp add: f1 f2)
            ultimately show ?thesis by simp
          qed
          show 3: "AxB_C.Cod u (A.src f1, f2) \<lesssim>\<^sub>C
                   AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2)"
          proof -
            have "AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                    AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) =
                  AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                    (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                     AxB_C.Cod u (f1, f2))"
              using AxB.src_char AxB_C.Map_resid_ide con f1 f2 by force
            also
            have "... = (AxB_C.Cod u (A.src f1, f2) \\\<^sub>C AxB_C.Cod u (f1, f2)) \\\<^sub>C
                           (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                              AxB_C.Cod u (f1, f2))"
            proof -
              have "C.joinable (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2))
                               (AxB_C.Cod u (f1, f2))"
                by (metis AxB.arr_char AxB.src_char C.joinable_def f1 f2
                    fst_conv snd_conv tu.naturality3)
              moreover have "AxB_C.Cod u (A.src f1, f2) \<frown>\<^sub>C
                             AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                               AxB_C.Cod u (f1, f2)"
                by (metis A.con_arr_src(1) A.ide_trg A.resid_src_arr
                    AxB.con_char AxB.prfx_char B.ide_trg B.residuation_axioms
                    B.trg_def C.con_sym C.con_target C.con_with_join_if(2)
                    C.joinable_implies_con calculation f1 f2 fst_conv
                    residuation.arrE snd_conv u.G.preserves_con
                    u.G.preserves_prfx)
              ultimately show ?thesis
                using C.resid_join\<^sub>E(1) by fastforce
            qed
            also have "... = AxB_C.Cod u (A.trg f1, B.trg f2) \\\<^sub>C
                               (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                  AxB_C.Cod u (f1, f2))"
            proof -
              have "AxB_C.Cod u (A.src f1, f2) \\\<^sub>C AxB_C.Cod u (f1, f2) =
                    AxB_C.Cod u (A.trg f1, B.trg f2)"
                (* TODO: Rearrange interpretations above. *)
                using u.G.preserves_resid [of "(A.src f1, f2)" "(f1, f2)"]
                by (simp add: AxB.resid_def B.trg_def f1 f2)
              thus ?thesis
                by presburger
            qed
            also have "... = AxB_C.Cod u (A.trg f1, B.trg f2) \\\<^sub>C
                               AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.trg f1, B.trg f2)"
              by (metis (no_types, lifting) AxB.arr_char AxB.src_char AxB.trg_char
                  f1 f2 fst_conv snd_conv tu.naturality1)
            also have "... = AxB_C.Apex t u (A.trg f1, B.trg f2)"
              by (metis A.src_trg AxB.src_char AxB_C.Apex_def B.src_trg
                  C.null_is_zero(2) fst_conv snd_conv tu.extensional
                  tu.naturality2)
            finally have "AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                            AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) =
                          AxB_C.Apex t u (A.trg f1, B.trg f2)"
              by blast
            moreover have "C.ide ..."
              by (simp add: f1 f2)
            ultimately show ?thesis by simp
          qed
          show 4: "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) \\\<^sub>C
                     AxB_C.Cod u (A.src f1, f2) =
                   AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \\\<^sub>C
                     AxB_C.Cod u (A.src f1, f2)"
          proof -
            have "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) \\\<^sub>C
                    AxB_C.Cod u (A.src f1, f2) =
                  (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                   AxB_C.Cod u (f1, f2)) \\\<^sub>C
                     AxB_C.Cod u (A.src f1, f2)"
              by (metis (no_types, lifting) AxB.ide_src AxB.src_char
                  AxB_C.Map_resid AxB_C.Map_resid_ide C.arr_def
                  C.ide_iff_src_self C.ide_implies_arr C.not_arr_null
                  C.prfx_implies_con C.src_resid C.trg_def 2 con
                  fst_conv snd_conv)
            also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                               AxB_C.Cod u (A.src f1, f2) \<squnion>\<^sub>C
                             AxB_C.Cod u (f1, f2) \\\<^sub>C AxB_C.Cod u (A.src f1, f2)"
              by (metis C.conE C.conI C.con_sym C.joinable_iff_join_not_null
                  C.null_is_zero(2) C.prfx_implies_con C.resid_join\<^sub>E(3) 3 calculation)
            also have 4: "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.trg f2) \<squnion>\<^sub>C
                                AxB_C.Cod u (f1, f2) \\\<^sub>C AxB_C.Cod u (A.src f1, f2)"
              by (metis A.src_src A.trg_src AxB.src_char AxB.trg_char C.con_sym_ax
                  C.not_ide_null C.null_is_zero(2) 3 fst_conv snd_conv tu.naturality1
                  u.G.extensional)
            also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.trg f2) \<squnion>\<^sub>C
                             AxB_C.Cod u (f1, B.trg f2)"
              using f1 f2 u.G.preserves_con AxB.resid_def B.trg_def
                    u.G.preserves_resid [of "(f1, f2)" "(A.src f1, f2)"]
                   
              by simp
            also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.trg f2)"
              using AxB.src_char AxB_C.Map_resid_ide con f1 f2 by force
            finally have L: "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) \\\<^sub>C
                               AxB_C.Cod u (A.src f1, f2) =
                             AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.trg f2)"
              by blast

            have 5: "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \\\<^sub>C
                       AxB_C.Cod u (A.src f1, f2) =
                     (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                      AxB_C.Cod u (f1, B.src f2)) \\\<^sub>C AxB_C.Cod u (A.src f1, f2)"
              using AxB.src_char AxB_C.Map_resid_ide con f1 f2 by auto
            also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                               AxB_C.Cod u (A.src f1, f2) \<squnion>\<^sub>C
                             AxB_C.Cod u (f1, B.src f2) \\\<^sub>C AxB_C.Cod u (A.src f1, f2)"
            proof -
              have "C.joinable (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2))
                               (AxB_C.Cod u (f1, B.src f2))"
                by (metis AxB.arr_char AxB.src_char B.arr_src_iff_arr B.src_src
                    C.joinable_def f1 f2 fst_conv snd_conv tu.naturality3)
              moreover have "AxB_C.Cod u (A.src f1, f2) \<frown>\<^sub>C
                             AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                               AxB_C.Cod u (f1, B.src f2)"
                by (metis 2 3 5 C.arr_resid_iff_con C.con_sym C.con_target
                    C.prfx_implies_con C.resid_reflects_con)
              ultimately show ?thesis
                using C.resid_join\<^sub>E(3) by blast
            qed
            also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                               AxB_C.Cod u (A.src f1, f2) \<squnion>\<^sub>C
                             AxB_C.Cod u (f1, B.trg f2)"
              using u.G.preserves_resid [of "(f1, B.src f2)" "(A.src f1, f2)"]
              by (simp add: AxB.resid_def f1 f2)
            also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.trg f2) \<squnion>\<^sub>C
                             AxB_C.Cod u (f1, B.trg f2)"
              using tu.naturality1 [of "(A.src f1, f2)"]
              by (simp add: AxB.src_char AxB.trg_char f1 f2)
            also have "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.trg f2)"
              using AxB.src_char AxB_C.Map_resid_ide con f1 f2 by force
            finally have R: "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \\\<^sub>C
                               AxB_C.Cod u (A.src f1, f2) =
                             AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.trg f2)"
              by blast

            show ?thesis
              using L R by auto
          qed
          show "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) \\\<^sub>C
                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) =
                AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2)"
          proof -
            have 5: "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) \\\<^sub>C
                       AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) =
                     (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                       AxB_C.Cod u (f1, f2)) \\\<^sub>C
                       AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2)"
              by (metis (no_types, lifting) AxB.ide_src AxB.src_char
                  AxB_C.Map_resid AxB_C.Map_resid_ide C.arr_def
                  C.ide_iff_src_self C.ide_implies_arr C.not_arr_null
                  C.prfx_implies_con C.src_resid C.trg_def 3 con
                  fst_conv snd_conv)
            also have 6: "... = AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) \<squnion>\<^sub>C
                                AxB_C.Cod u (f1, f2) \\\<^sub>C
                                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2)"
              by (metis C.conI C.con_sym_ax C.joinable_iff_join_not_null C.not_ide_null
                  C.null_is_zero(2) C.resid_join\<^sub>E(3) 2 calculation)
            also have "... = (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2)) \<squnion>\<^sub>C
                             AxB_C.Apex t u (A.trg f1, f2)"
            proof -
              have "AxB_C.Cod u (f1, f2) \\\<^sub>C
                      AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) =
                    (AxB_C.Cod u (f1, B.src f2) \<squnion>\<^sub>C AxB_C.Cod u (A.src f1, f2)) \\\<^sub>C
                      AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2)"
              proof -
                have "AxB.join_of (f1, B.src f2) (A.src f1, f2) (f1, f2)"
                  using f1 f2
                  by (simp add: A.join_of_arr_src(2) AxB.join_of_char(1)
                      B.join_of_arr_src(1))
                thus ?thesis
                  using f1 f2 u.G.preserves_joins AxB.join_of_char
                        C.join_is_join_of C.join_of_unique C.joinable_def
                  by metis
              qed
              also have "... = (AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2)) \<squnion>\<^sub>C
                               (AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2))"
                using C.resid_join\<^sub>E(3) [of "AxB_C.Cod u (f1, B.src f2)"
                                           "AxB_C.Cod u (A.src f1, f2)"
                                           "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2)"]
                by (metis 2 5 6 C.conE C.conI C.con_sym_ax
                    C.join_def C.joinable_implies_con C.null_is_zero(2)
                    C.prfx_implies_con calculation)
              also have "... = (AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                  (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                                   AxB_C.Cod u (f1, B.src f2))) \<squnion>\<^sub>C
                               (AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                  (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                                   AxB_C.Cod u (f1, B.src f2)))"
                using f2 AxB.src_char AxB_C.Map_resid_ide 2 con
                by force
              also have "... = (AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                  AxB_C.Cod u (f1, B.src f2)) \\\<^sub>C
                                 (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                    AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
                                 AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                   (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                                    AxB_C.Cod u (f1, B.src f2))"
              proof -
                have "AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                        (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                           AxB_C.Cod u (f1, B.src f2)) =
                      (AxB_C.Cod u (f1, B.src f2) \\\<^sub>C AxB_C.Cod u (f1, B.src f2)) \\\<^sub>C
                         (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                            AxB_C.Cod u (f1, B.src f2))"
                  by (metis (no_types, lifting) C.arr_prfx_join_self
                      C.conI C.con_sym_ax C.joinable_iff_join_not_null
                      C.not_ide_null C.null_is_zero(1) C.resid_join\<^sub>E(1)
                      5 2 calculation)
                thus ?thesis by argo
              qed
              also have "... = (AxB_C.Cod u (A.trg f1, B.src f2) \\\<^sub>C
                                  (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                   AxB_C.Cod u (f1, B.src f2))) \<squnion>\<^sub>C
                               (AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                 (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                                  AxB_C.Cod u (f1, B.src f2)))"
                using u.G.preserves_trg [of "(f1, B.src f2)"] AxB.trg_char
                      C.trg_def f1 f2
                by force
              also have "... = (AxB_C.Cod u (A.trg f1, B.src f2) \\\<^sub>C
                                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.trg f1, B.src f2)) \<squnion>\<^sub>C
                               (AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                  (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                                   AxB_C.Cod u (f1, B.src f2)))"
                using tu.naturality1 [of "(f1, B.src f2)"] AxB.src_char
                      AxB.trg_char f1 f2
                by force
              also have "... = AxB_C.Apex t u (A.trg f1, B.src f2) \<squnion>\<^sub>C
                               (AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                 (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                                  AxB_C.Cod u (f1, B.src f2)))"
                by (metis A.src_trg AxB.src_char AxB_C.Apex_def B.src_src
                          C.ex_un_null C.null_is_zero(1) fst_conv snd_conv
                          tu.extensional tu.naturality2)
              also have "... = AxB_C.Apex t u (A.trg f1, B.src f2) \<squnion>\<^sub>C
                               ((AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                   AxB_C.Cod u (f1, B.src f2)) \\\<^sub>C
                                 (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                    AxB_C.Cod u (f1, B.src f2)))"
                by (metis C.arr_prfx_join_self C.conI C.con_sym_ax
                    C.joinable_iff_join_not_null C.not_ide_null C.null_is_zero(2)
                    C.resid_join\<^sub>E(1) 2 5 calculation)
              also have "... = AxB_C.Apex t u (A.trg f1, B.src f2) \<squnion>\<^sub>C
                               (AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                  AxB_C.Cod u (f1, B.src f2)) \\\<^sub>C
                                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.trg f1, B.src f2)"
                by (metis AxB.src_char AxB.trg_char B.src_src B.trg_src
                          C.not_ide_null C.null_is_zero(1) 2 fst_conv
                          snd_conv tu.extensional tu.naturality1)
              also have "... = AxB_C.Apex t u (A.trg f1, B.src f2) \<squnion>\<^sub>C
                               AxB_C.Cod u (A.trg f1, f2) \\\<^sub>C
                                 AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.trg f1, B.src f2)"
                using u.G.preserves_resid [of "(A.src f1, f2)" "(f1, B.src f2)"]
                      AxB.resid_def f1 f2
                by auto
              also have "... = AxB_C.Apex t u (A.trg f1, B.src f2) \<squnion>\<^sub>C
                               AxB_C.Apex t u (A.trg f1, f2)"
                by (metis A.arr_trg_iff_arr A.src_trg AxB.arr_char AxB.src_char
                          f1 f2 fst_conv snd_conv tu.naturality2)
              also have "... = AxB_C.Apex t u (A.trg f1, f2)"
              proof -
                have "AxB.join_of (A.trg f1, B.src f2) (A.trg f1, f2) (A.trg f1, f2)"
                  by (simp add: AxB.join_of_arr_src(1) f1 f2)
                thus ?thesis
                  using tu.G.preserves_joins C.join_is_join_of
                        C.join_of_unique C.joinable_def
                  by meson
              qed
              finally have "AxB_C.Cod u (f1, f2) \\\<^sub>C
                              AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) =
                            AxB_C.Apex t u (A.trg f1, f2)"
                by blast
              thus ?thesis by auto
            qed
            also have "... = (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2)) \\\<^sub>C
                               (AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2)) \<squnion>\<^sub>C
                             AxB_C.Apex t u (A.trg f1, f2)"
            proof -
              have "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                      AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) =
                    AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                      (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                       AxB_C.Cod u (f1, B.src f2))"
                using f1 f2 AxB.src_char AxB_C.Map_resid_ide con by auto
              also have "... = (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2)) \\\<^sub>C
                                (AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                   AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2))"
              proof -
                have "C.joinable (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2))
                                 (AxB_C.Cod u (f1, B.src f2))"
                  by (metis C.arr_prfx_join_self C.con_sym_ax
                      C.joinable_iff_join_not_null C.not_ide_null C.null_is_zero(1)
                      2 5 6 calculation)
                moreover have "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<frown>\<^sub>C
                               AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                                 AxB_C.Cod u (f1, B.src f2)"
                  using C.arr_prfx_join_self C.prfx_implies_con calculation
                  by presburger
                ultimately have "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                   (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                                    AxB_C.Cod u (f1, B.src f2)) =
                                 (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                    AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2)) \\\<^sub>C
                                      (AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                         AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2))"
                  using f1 f2 C.resid_join\<^sub>E(2) by blast
                thus ?thesis by blast
              qed
              finally have "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                              AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) =
                            (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                               AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2)) \\\<^sub>C
                                  (AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                     AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2))"
                by blast
              thus ?thesis by argo
            qed
            also have "... = AxB_C.Apex t u (A.src f1, B.src f2) \\\<^sub>C
                                (AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                  AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2)) \<squnion>\<^sub>C
                             AxB_C.Apex t u (A.trg f1, f2)"
              by (metis AxB.ide_src AxB.src_char C.not_ide_null
                        C.null_is_zero(2) C.trg_def 2 fst_conv snd_conv tu.extensional
                        tu.preserves_trg)
            also have "... = AxB_C.Apex t u (A.src f1, B.src f2) \\\<^sub>C
                               AxB_C.Apex t u (f1, B.src f2) \<squnion>\<^sub>C
                             AxB_C.Apex t u (A.trg f1, f2)"
              by (metis AxB.src_char B.src_trg B.trg_src C.con_sym_ax
                  C.not_ide_null C.null_is_zero(2) 4 3 fst_conv snd_conv
                  tu.extensional tu.naturality2)
            also have "... = AxB_C.Apex t u (A.trg f1, B.src f2) \<squnion>\<^sub>C
                             AxB_C.Apex t u (A.trg f1, f2)"
              using tu.G.preserves_trg [of "(f1, B.src f2)"]
              by (simp add: AxB.trg_char C.con_imp_coinitial C.resid_ide(2) f1 f2)
            also have "... = AxB_C.Apex t u (A.trg f1, f2)"
            proof -
              have "AxB.join_of (A.trg f1, B.src f2) (A.trg f1, f2) (A.trg f1, f2)"
                by (simp add: AxB.join_of_arr_src(1) f1 f2)
              thus ?thesis
                using tu.G.preserves_joins C.join_is_join_of C.join_of_unique
                      C.joinable_def
                by meson
            qed
            finally have L: "AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2) \\\<^sub>C
                                 AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) =
                             AxB_C.Apex t u (A.trg f1, f2)"
              by blast

            have R: "AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                       AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) =
                     AxB_C.Apex t u (A.trg f1, f2)"
            proof -
              have "AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                      AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, B.src f2) =
                    AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                      (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \<squnion>\<^sub>C
                       AxB_C.Cod u (f1, B.src f2))"
                using AxB.src_char AxB_C.Map_resid_ide con f1 f2 by force
              also have "... = (AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                  AxB_C.Cod u (f1, B.src f2)) \\\<^sub>C
                                 (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                    AxB_C.Cod u (f1, B.src f2))"
                by (metis C.conI C.con_sym_ax C.joinable_iff_join_not_null
                    C.not_ide_null C.null_is_zero(2) C.resid_join\<^sub>E(1) 3 4
                    calculation)
              also have "... = AxB_C.Cod u (A.trg f1, f2) \\\<^sub>C
                                 (AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.src f1, B.src f2) \\\<^sub>C
                                    AxB_C.Cod u (f1, B.src f2))"
                using u.G.preserves_resid [of "(A.src f1, f2)" "(f1, B.src f2)"]
                by (simp add: AxB.resid_def f1 f2)
              also have "... = AxB_C.Cod u (A.trg f1, f2) \\\<^sub>C
                                 AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (A.trg f1, B.src f2)"
                by (metis AxB.src_char AxB.trg_char B.src_src B.trg_src
                    C.ex_un_null C.not_ide_null C.null_is_zero(2) 2
                    fst_conv snd_conv tu.extensional tu.naturality1)
              also have "... = AxB_C.Apex t u (A.trg f1, f2)"
                by (metis A.src_trg AxB.src_char C.conI C.con_sym_ax
                    C.prfx_implies_con C.residuation_axioms L 2 fst_conv
                    residuation.arr_resid snd_conv tu.G.preserves_reflects_arr
                    tu.naturality2)
              finally show ?thesis by blast
            qed
            show ?thesis
              using L R by simp
          qed
        qed
        finally show "((AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                          AxB_C.Map u (A.src f1, B.src f2) \<squnion>\<^sub>C
                        AxB_C.Cod u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                       AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
                      AxB_C.Cod u (A.src f1, f2) =
                      AxB_C.Map (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) (f1, f2)"
         by simp
      qed
      have "BC.Map (A_BC.Map (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) f1) =
            (\<lambda>f2. if B.arr f2
                  then AxB_C.Map t (AxB.src (f1, f2)) \\\<^sub>C
                         AxB_C.Map u (AxB.src (f1, f2)) \<squnion>\<^sub>C
                       AxB_C.Cod u (f1, f2)
                  else C.null)"
        unfolding curry_def
        using f1 con Curry_simp by simp
      also have "... = (\<lambda>f2. if B.arr f2
                             then ((AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                      AxB_C.Map u (A.src f1, B.src f2) \<squnion>\<^sub>C
                                    AxB_C.Cod u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                                   AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
                                  AxB_C.Cod u (A.src f1, f2)
                             else C.null)"
        using * con f1 by auto
      also
      have "... = BC.Map (A_BC.Map (A_BC.resid (CURRY t) (CURRY u)) f1)"
      proof -
        have 1: "Curry
                   (AxB_C.Dom t) (AxB_C.Cod t) (AxB_C.Map t) (A.src f1) \<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                 Curry
                   (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u) (A.src f1)"
          by (metis A.ide_src A_BC.con_char Map_CURRY con
              CURRY_preserves_con f1 t u)
        moreover
        have "BC.Dom
                (Curry (AxB_C.Dom t) (AxB_C.Cod t) (AxB_C.Map t)
                   (A.src f1) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                   Curry (AxB_C.Dom u) (AxB_C.Cod u) (AxB_C.Map u)
                     (A.src f1)) =
              (\<lambda>f2. AxB_C.Cod u (A.src f1, f2))"
          using f1 t u 1 BC.Dom_resid Map_Curry Dom_Curry Cod_Curry by simp
        moreover have "transformation B C (\<lambda>f2. AxB_C.Cod u (A.src f1, f2))
                                          (\<lambda>f2. AxB_C.Cod u (A.trg f1, f2))
                                          (\<lambda>f2. AxB_C.Cod u (f1, f2))"
          using f1 Cod_u.fixing_arr_gives_transformation_1 by simp
        ultimately
        have "BC.Map (A_BC.Map (A_BC.resid (CURRY t) (CURRY u)) f1) =
              (\<lambda>f2. (BC.Resid
                       (A_BC.MkArr
                          (\<lambda>g. AxB_C.Dom t (A.src f1, g))
                          (\<lambda>g. AxB_C.Cod t (A.src f1, g))
                          (\<lambda>g. AxB_C.Map t (A.src f1, g)))
                       (A_BC.MkArr
                          (\<lambda>g. AxB_C.Dom u (A.src f1, g))
                          (\<lambda>g. AxB_C.Cod u (A.src f1, g))
                          (\<lambda>g. AxB_C.Map u (A.src f1, g)))
                       (B.src f2) \<squnion>\<^sub>C
                     AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
                    AxB_C.Cod u (A.src f1, f2))"
          using * t u f1 C.joinable_iff_arr_join tu.preserves_arr con
                CURRY_preserves_con A_BC.Map_resid BC.join_char
                Map_CURRY BC.Map_resid_ide Map_Curry Dom_Curry Curry_def
          by auto
        also have "... = (\<lambda>f2. if B.arr f2
                               then ((AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                      AxB_C.Map u (A.src f1, B.src f2) \<squnion>\<^sub>C
                                    AxB_C.Cod u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                                   AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
                                  AxB_C.Cod u (A.src f1, f2)
                               else C.null)"
        proof
          fix f2
          show "(BC.Resid
                   (A_BC.MkArr
                      (\<lambda>g. AxB_C.Dom t (A.src f1, g))
                      (\<lambda>g. AxB_C.Cod t (A.src f1, g))
                      (\<lambda>g. AxB_C.Map t (A.src f1, g)))
                   (A_BC.MkArr
                      (\<lambda>g. AxB_C.Dom u (A.src f1, g))
                      (\<lambda>g. AxB_C.Cod u (A.src f1, g))
                      (\<lambda>g. AxB_C.Map u (A.src f1, g)))
                   (B.src f2) \<squnion>\<^sub>C
                  AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
                 AxB_C.Cod u (A.src f1, f2) =
                (if B.arr f2
                 then ((AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                        AxB_C.Map u (A.src f1, B.src f2) \<squnion>\<^sub>C
                       AxB_C.Cod u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                      AxB_C.Cod u (f1, B.src f2)) \<squnion>\<^sub>C
                     AxB_C.Cod u (A.src f1, f2)
                 else C.null)"
            apply (cases "B.arr f2")
             apply force
            using B.src_def C.arr_prfx_join_self C.join_def
            by fastforce
        qed
        finally show ?thesis by simp
      qed
      finally show ?thesis by blast
    qed

    lemma Cod_Curry_Apex:
    assumes con: "AxB_C.con t u" and f1: "A.arr f1"
    shows "BC.Cod
             (Curry (AxB_C.Apex t u) (AxB_C.Apex t u) (AxB_C.Apex t u) f1) =
           BC.Cod (A_BC.Map (A_BC.resid (CURRY t) (CURRY u)) f1)"
    proof -
      have "BC.Cod (Curry3 (AxB_C.Apex t u) f1) =
            BC.Cod (A_BC.Map (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) f1)"
        by (simp add: assms(1) Curry_def)
      also have "... = BC.Cod (A_BC.Apex (CURRY t) (CURRY u) f1)"
        using assms Cod_Map_CURRY_resid by simp
      also have "... =
                 BC.Cod (A_BC.Map (A_BC.resid (CURRY t) (CURRY u)) f1)"
      proof -
        have "BC.trg (A_BC.Map (CURRY t) (A.src f1) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                          A_BC.Map (CURRY u) (A.src f1) \<squnion>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                        A_BC.Cod (CURRY u) f1) =
              BC.trg (A_BC.Cod (CURRY u) f1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                          (A_BC.Map (CURRY t) (A.src f1) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                             A_BC.Map (CURRY u) (A.src f1)))"
          by (metis A_BC.Map_preserves_prfx A_BC.Map_resid
              A_BC.cong_reflexive BC.apex_sym BC.joinable_iff_join_not_null
              BC.not_ide_null BC.null_is_zero(2) BC.trg_join
              CURRY_preserves_con con f1 A_BC.arr_resid)
        hence "BC.Cod (A_BC.Map (CURRY t) (A.src f1) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                           A_BC.Map (CURRY u) (A.src f1) \<squnion>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                         A_BC.Cod (CURRY u) f1) =
               BC.Cod (A_BC.Cod (CURRY u) f1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                         (A_BC.Map (CURRY t) (A.src f1) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                            A_BC.Map (CURRY u) (A.src f1)))"
          using BC.trg_char
          by (metis (no_types, lifting) BC.Map_trg BC.arr_trg_iff_arr
              BC.con_imp_arr_resid BC.join_char(2)
              BC.joinable_iff_arr_join BC.trg_def)
        thus ?thesis
          using assms CURRY_preserves_con A_BC.Map_resid A_BC.Apex_def
          by simp
      qed
      finally show ?thesis by blast
    qed

    lemma Curry_preserves_Apex:
    assumes "AxB_C.con t u"
    shows "Curry3 (AxB_C.Apex t u) = A_BC.Apex (CURRY t) (CURRY u)"
      (is "?LHS = ?RHS")
    proof -
      have t: "AxB_C.arr t"
        using assms AxB_C.con_implies_arr(1) by blast
      have u: "AxB_C.arr u"
        using assms AxB_C.con_implies_arr(2) by blast
      interpret Apex: simulation
                        A BC.resid \<open>A_BC.Apex (CURRY t) (CURRY u)\<close>
        using assms CURRY_preserves_con A_BC.Apex_is_simulation A_BC.con_char
        by blast
      interpret Cod_u: simulation AxB.resid C \<open>AxB_C.Cod u\<close>
        using AxB_C.ide_trg AxB_C.trg_char u by force
      interpret Curry_Apex: simulation A BC.resid
                              \<open>Curry (AxB_C.Apex t u) (AxB_C.Apex t u)
                              (AxB_C.Apex t u)\<close>
        using Curry_preserves_simulations AxB_C.Apex_is_simulation
              AxB_C.con_char assms
        by blast
      show ?thesis
      proof
        fix f1
        show "?LHS f1 = ?RHS f1"
        proof (cases "A.arr f1")
          show "\<not> A.arr f1 \<Longrightarrow> ?thesis"
            using A_BC.Apex_def Curry_def by force
          assume f1: "A.arr f1"
          interpret Apex_curry: transformation B C
                                  \<open>BC.Dom (A_BC.Apex (CURRY t) (CURRY u) f1)\<close>
                                  \<open>BC.Cod (A_BC.Apex (CURRY t) (CURRY u) f1)\<close>
                                  \<open>BC.Map (A_BC.Apex (CURRY t) (CURRY u) f1)\<close>
            using f1 BC.arr_char by blast
          interpret Map_Curry_Apex:
                    transformation B C
                      \<open>BC.Dom
                          (Curry
                             (AxB_C.Apex t u)
                             (AxB_C.Apex t u)
                             (AxB_C.Apex t u)
                          f1)\<close>
                      \<open>BC.Cod
                          (Curry
                             (AxB_C.Apex t u)
                             (AxB_C.Apex t u)
                             (AxB_C.Apex t u)
                          f1)\<close>
                      \<open>BC.Map
                         (Curry
                            (AxB_C.Apex t u)
                            (AxB_C.Apex t u)
                            (AxB_C.Apex t u)
                         f1)\<close>
            using f1 Curry_Apex.preserves_reflects_arr BC.arr_char
            by blast
          show ?thesis
          proof -
            have "BC.Dom (?LHS f1) = BC.Dom (?RHS f1)"
              by (metis A.con_arr_src(1) A.con_arr_src(2) A.con_implies_arr(1)
                  A.ide_src A.resid_arr_src A_BC.Apex_def A_BC.Map_resid_ide
                  BC.Dom_resid BC.arr_resid_iff_con Apex.preserves_reflects_arr
                  Cod_Curry_Apex Curry_Apex.preserves_con
                  Curry_Apex.preserves_resid assms CURRY_preserves_con f1)
            moreover
            have "BC.Cod (?LHS f1) = BC.Cod (?RHS f1)"
              using Cod_Curry_Apex Cod_Map_CURRY_resid assms f1 Curry_def
              by auto
            moreover
            have "BC.Map (?LHS f1) = BC.Map (?RHS f1)"
            proof
              fix f2
              show "BC.Map (?LHS f1) f2 = BC.Map (?RHS f1) f2"
              proof (cases "B.arr f2")
                show "\<not> B.arr f2 \<Longrightarrow> ?thesis"
                  by (simp add: Apex_curry.extensional
                      Map_Curry_Apex.extensional)
                assume f2: "B.arr f2"
                show ?thesis
                proof -
                  have 0: "BC.Map (?LHS f1) f2 =
                           AxB_C.Cod u (f1, f2) \\\<^sub>C
                             (AxB_C.Map t (AxB.src (f1, f2)) \\\<^sub>C
                                AxB_C.Map u (AxB.src (f1, f2)))"
                    using assms t u f1 f2 AxB.con_char Map_Curry AxB_C.Apex_def
                    by simp
                  also have "... =
                             BC.Map
                               (A_BC.Cod (CURRY u) f1 \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                                  (A_BC.Map (CURRY t) (A.src f1) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                                     A_BC.Map (CURRY u) (A.src f1))) f2"
                  proof -
                    have 1: "AxB.join_of (f1, B.src f2) (A.src f1, f2) (f1, f2)"
                      by (simp add: A.join_of_arr_src(2) AxB.join_of_char(1)
                          B.join_of_arr_src(1) f1 f2)
                    have "A_BC.Map (CURRY t) (A.src f1) \<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                          A_BC.Map (CURRY u) (A.src f1)"
                      using A.ide_src A_BC.con_char assms CURRY_preserves_con f1
                      by presburger
                    moreover have "A_BC.Cod (CURRY u) f1 \<frown>\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                                   A_BC.Map (CURRY t) (A.src f1) \\\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]
                                     A_BC.Map (CURRY u) (A.src f1)"
                      by (metis A_BC.Apex_def BC.arrE BC.conI
                          Apex.preserves_reflects_arr f1)
                    moreover have "AxB_C.Cod u (f1, f2) \\\<^sub>C
                                     (AxB_C.Map t (AxB.src (f1, f2)) \\\<^sub>C
                                        AxB_C.Map u (AxB.src (f1, f2))) =
                                   AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                                     ((AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                         AxB_C.Map u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                                      AxB_C.Cod u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                                     AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                                       (AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                          AxB_C.Map u (A.src f1, B.src f2))"
                    proof -
                      have "AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                              ((AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                  AxB_C.Map u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                                 AxB_C.Cod u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                            AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                              (AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                 AxB_C.Map u (A.src f1, B.src f2)) =
                            AxB_C.Cod u (f1, B.src f2) \\\<^sub>C
                              (AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                 AxB_C.Map u (A.src f1, B.src f2)) \<squnion>\<^sub>C
                            AxB_C.Cod u (A.src f1, f2) \\\<^sub>C
                              (AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                 AxB_C.Map u (A.src f1, B.src f2))"
                        using AxB_C.Map_resid_ide assms f1 f2 by fastforce
                      also have "... = (AxB_C.Cod u (f1, B.src f2) \<squnion>\<^sub>C
                                        AxB_C.Cod u (A.src f1, f2)) \\\<^sub>C
                                         (AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                            AxB_C.Map u (A.src f1, B.src f2))"
                      proof -
                        have "C.joinable (AxB_C.Cod u (f1, B.src f2))
                                         (AxB_C.Cod u (A.src f1, f2))"
                          using 1 Cod_u.preserves_joins C.joinable_def by blast
                        moreover have "AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                         AxB_C.Map u (A.src f1, B.src f2) \<frown>\<^sub>C
                                       AxB_C.Cod u (f1, B.src f2) \<squnion>\<^sub>C
                                       AxB_C.Cod u (A.src f1, f2)"
                          by (metis (no_types, lifting) 0 1
                              AxB.join_of_un_upto_cong AxB.prfx_implies_con
                              AxB.residuation_axioms AxB.src_char
                              C.join_is_join_of C.join_of_unique C.joinable_def
                              C.residuation_axioms Cod_u.preserves_joins
                              Map_Curry_Apex.preserves_arr f2 fst_conv
                              residuation.arrI residuation.arr_resid_iff_con
                              residuation.con_sym snd_conv)
                        ultimately show ?thesis
                          using C.resid_join\<^sub>E(3) by simp
                      qed
                      also have "... = AxB_C.Cod u (f1, f2) \\\<^sub>C
                                        (AxB_C.Map t (A.src f1, B.src f2) \\\<^sub>C
                                           AxB_C.Map u (A.src f1, B.src f2))"
                        using 1 f1 f2 Cod_u.preserves_joins C.join_is_join_of
                              C.join_of_unique
                        by (metis C.joinable_def)
                      finally show ?thesis
                        by (simp add: AxB.src_char f1 f2)
                    qed
                    ultimately show ?thesis
                      using f1 f2 t u AxB_C.con_char BC.Map_resid BC.Apex_def
                            Cod_Curry Map_Curry
                      by simp
                  qed
                  also have "... = BC.Map (?RHS f1) f2"
                    using assms f1 f2 CURRY_preserves_con CURRY_preserves_arr
                          A_BC.Apex_def
                    by simp
                  finally show ?thesis by auto
                qed
              qed
            qed
            moreover have "?LHS f1 \<noteq> BC.Null"
              by (simp add: f1 Curry_def)
            moreover have "?RHS f1 \<noteq> BC.Null"
              using BC.arr_char f1 by blast
            ultimately show ?thesis
              by (metis BC.MkArr_Map)
          qed
        qed
      qed
    qed

    sublocale CURRY: simulation AxB_C.resid A_BC.resid CURRY
    proof
      show "\<And>t. \<not> AxB_C.arr t \<Longrightarrow> CURRY t = A_BC.null"
        unfolding CURRY_def
        by auto
      fix t u
      assume con: "AxB_C.con t u"
      have t: "AxB_C.arr t"
        using AxB_C.con_implies_arr(1) con by blast
      have u: "AxB_C.arr u"
        using AxB_C.con_implies_arr(2) con by blast
      show "A_BC.con (CURRY t) (CURRY u)"
        using con CURRY_preserves_con by simp
      show "CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) = CURRY t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u"
      proof -
        have 1: "AxB_C.Dom (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) = AxB_C.Cod u"
          using con AxB_C.con_char by auto
        have 2: "AxB_C.Cod (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) = AxB_C.Apex t u"
          using con AxB_C.con_char by auto
        have "A_BC.Dom (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) =
              A_BC.Dom (CURRY t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u)"
          using con 1 2 t u AxB_C.con_char
          apply simp
          using \<open>CURRY t \<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u\<close> by force
        moreover
        have "A_BC.Cod (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) =
              A_BC.Cod (CURRY t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u)"
          using con 1 2 t u AxB_C.con_char Curry_preserves_Apex
          apply simp
          using \<open>CURRY t \<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u\<close> by force
        moreover
        have "A_BC.Map (CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u)) =
              A_BC.Map (CURRY t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u)"
          (is "?LHS = ?RHS")
        proof
          fix f1
          show "?LHS f1 = ?RHS f1"
          proof (cases "A.arr f1")
            show "\<not> A.arr f1 \<Longrightarrow> ?thesis"
              by (simp add: \<open>A_BC.con (CURRY t) (CURRY u)\<close> con Curry_def)
            assume f1: "A.arr f1"
            have "BC.Dom (?LHS f1) = BC.Dom (?RHS f1)"
              using Dom_Map_CURRY_resid con f1 by blast
            moreover
            have "BC.Cod (?LHS f1) = BC.Cod (?RHS f1)"
              using Cod_Map_CURRY_resid Cod_Curry_Apex con
                    Curry_preserves_Apex f1
              by force
            moreover
            have "BC.Map (?LHS f1) = BC.Map (?RHS f1)"
              using f1 con Map_Map_CURRY_resid by blast
            moreover have "?LHS f1 \<noteq> A_BC.Null"
              by (simp add: con f1 Curry_def)
            moreover have "?RHS f1 \<noteq> A_BC.Null"
              by (metis A.arrE A_BC.arr_def A_BC.arr_resid A_BC.conE\<^sub>E\<^sub>R\<^sub>T\<^sub>S
                  BC.con_char \<open>CURRY t \<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u\<close> f1)
            ultimately show ?thesis
              by (metis BC.MkArr_Map)
          qed
        qed
        moreover have "CURRY t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY u \<noteq> AxB_C.Null"
          using A_BC.null_char \<open>A_BC.con (CURRY t) (CURRY u)\<close> by auto
        moreover have "CURRY (t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] u) \<noteq> A_BC.Null"
          using con A_BC.arr_char AxB_C.arr_resid CURRY_preserves_arr
          by presburger
        ultimately show ?thesis
          by (metis A_BC.MkArr_Map)
      qed
    qed

    lemma CURRY_is_simulation:
    shows "simulation AxB_C.resid A_BC.resid CURRY"
      ..

    definition UNCURRY
                 :: "('a, ('b, 'c) BC.arr) A_BC.arr \<Rightarrow> ('a \<times> 'b, 'c) AxB_C.arr"
    where "UNCURRY f \<equiv> if A_BC.arr f
                       then AxB_C.MkArr (Uncurry (A_BC.Dom f))
                                        (Uncurry (A_BC.Cod f))
                                        (Uncurry (A_BC.Map f))
                       else AxB_C.null"

    lemma Dom_UNCURRY [simp]:
    assumes "A_BC.arr f"
    shows "AxB_C.Dom (UNCURRY f) = Uncurry (A_BC.Dom f)"
      using assms UNCURRY_def by auto

    lemma Cod_UNCURRY [simp]:
    assumes "A_BC.arr f"
    shows "AxB_C.Cod (UNCURRY f) = Uncurry (A_BC.Cod f)"
      using assms UNCURRY_def by auto

    lemma Map_UNCURRY [simp]:
    assumes "A_BC.arr f"
    shows "AxB_C.Map (UNCURRY f) = Uncurry (A_BC.Map f)"
      using assms UNCURRY_def by auto

    lemma UNCURRY_CURRY [simp]:
    assumes "AxB_C.arr t"
    shows "UNCURRY (CURRY t) = t"
    proof -
      interpret CURRY: simulation AxB_C.resid A_BC.resid CURRY
        using CURRY_is_simulation by simp
      have "UNCURRY (CURRY t) =
            AxB_C.MkArr
              (Uncurry (A_BC.Dom (CURRY t)))
              (Uncurry (A_BC.Cod (CURRY t)))
              (Uncurry (A_BC.Map (CURRY t)))"
        using assms UNCURRY_def by auto
      also have "... = AxB_C.MkArr
                         (Uncurry (Curry3 (AxB_C.Dom t)))
                         (Uncurry (Curry3 (AxB_C.Cod t)))
                         (Uncurry
                            (Curry (AxB_C.Dom t) (AxB_C.Cod t) (AxB_C.Map t)))"
        using assms by simp
      also have "... =
                 AxB_C.MkArr (AxB_C.Dom t) (AxB_C.Cod t) (AxB_C.Map t)"
        by (metis AxB_C.arr_MkArr AxB_C.arr_char AxB_C.ide_MkIde
            AxB_C.ide_implies_arr Uncurry_Curry assms transformation_def)
      also have "... = t"
        using assms AxB_C.MkArr_Map AxB_C.arr_char by auto
      finally show ?thesis by blast
    qed

    lemma CURRY_UNCURRY [simp]:
    assumes "A_BC.arr t"
    shows "CURRY (UNCURRY t) = t"
    proof -
      have 1: "AxB_C.arr (UNCURRY t)"
        using assms AxB_C.arr_char UNCURRY_def Uncurry_preserves_transformations
        by fastforce
      have "CURRY (UNCURRY t) = 
            A_BC.MkArr
              (Curry3 (Uncurry (A_BC.Dom t)))
              (Curry3 (Uncurry (A_BC.Cod t)))
              (Curry (Uncurry (A_BC.Dom t)) (Uncurry (A_BC.Cod t))
                     (Uncurry (A_BC.Map t)))"
        using assms 1 CURRY_def by simp
      also have "... = A_BC.MkArr (A_BC.Dom t) (A_BC.Cod t) (A_BC.Map t)"
        by (metis A_BC.arrE A_BC.arr_MkArr A_BC.arr_src_iff_arr
            A_BC.arr_trg_iff_arr A_BC.src_char A_BC.trg_char Curry_Uncurry assms)
      also have "... = t"
        using assms A_BC.MkArr_Map A_BC.arr_char by force
      finally show ?thesis by blast
    qed

    lemma UNCURRY_is_simulation:
    shows "simulation A_BC.resid AxB_C.resid UNCURRY"
    proof
      show "\<And>t. \<not> A_BC.arr t \<Longrightarrow> UNCURRY t = AxB_C.null"
        using UNCURRY_def by auto
      show *: "\<And>t u. A_BC.con t u \<Longrightarrow> AxB_C.con (UNCURRY t) (UNCURRY u)"
      proof -
        fix t u
        assume con: "A_BC.con t u"
        have t: "A_BC.arr t"
          using con
          by (simp add: A_BC.con_implies_arr(1))
        have u: "A_BC.arr u"
          using con
          by (simp add: A_BC.con_implies_arr(2))
        show "AxB_C.con (UNCURRY t) (UNCURRY u)"
        proof (unfold AxB_C.con_char, intro conjI)
          show "UNCURRY t \<noteq> AxB_C.Null"
            using t UNCURRY_def by simp
          show "UNCURRY u \<noteq> AxB_C.Null"
            using u UNCURRY_def by simp
          show "transformation AxB.resid C
                  (AxB_C.Dom (UNCURRY t)) (AxB_C.Cod (UNCURRY t))
                  (AxB_C.Map (UNCURRY t))"
            using t A_BC.arr_char Uncurry_preserves_transformations by simp
          show "transformation AxB.resid C
                  (AxB_C.Dom (UNCURRY u)) (AxB_C.Cod (UNCURRY u))
                  (AxB_C.Map (UNCURRY u))"
            using u A_BC.arr_char Uncurry_preserves_transformations by simp
          show "AxB_C.Dom (UNCURRY t) = AxB_C.Dom (UNCURRY u)"
            using t u con A_BC.con_char by simp
          show "\<forall>ab. AxB.ide ab \<longrightarrow>
                       AxB_C.Map (UNCURRY t) ab \<frown>\<^sub>C
                       AxB_C.Map (UNCURRY u) ab"
            using A_BC.con_char Uncurry_simp con t u by auto
        qed
      qed
      show "\<And>t u. t \<frown>\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] u \<Longrightarrow>
                     UNCURRY (t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] u) =
                     UNCURRY t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] UNCURRY u"
      proof -
        fix t u
        assume con: "A_BC.con t u"
        have con': "UNCURRY t \<frown>\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] UNCURRY u"
          using con * by simp
        hence 1: "CURRY (UNCURRY t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] UNCURRY u) =
                  CURRY (UNCURRY t) \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] CURRY (UNCURRY u)"
          by auto
        also have 2: "... = t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] u"
          using A_BC.con_implies_arr(1) A_BC.con_implies_arr(2) con by force
        also have "... = CURRY (UNCURRY (t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] u))"
          by (simp add: con)
        finally have "CURRY (UNCURRY t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] UNCURRY u) =
                      CURRY (UNCURRY (t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] u))"
          by blast
        thus "UNCURRY (t \\\<^sub>[\<^sub>A\<^sub>,\<^sub>[\<^sub>B\<^sub>,\<^sub>C\<^sub>]\<^sub>] u) = UNCURRY t \\\<^sub>[\<^sub>A\<^sub>x\<^sub>B\<^sub>,\<^sub>C\<^sub>] UNCURRY u"
          using con
          by (metis AxB_C.residuation_axioms UNCURRY_CURRY 1 2 con'
              residuation.arr_resid)
      qed
    qed

    sublocale UNCURRY: simulation A_BC.resid AxB_C.resid UNCURRY
      using UNCURRY_is_simulation by blast

    interpretation inverse_simulations
                     A_BC.resid AxB_C.resid CURRY UNCURRY
      using CURRY_UNCURRY UNCURRY_CURRY CURRY.extensional
            UNCURRY.extensional
      by unfold_locales auto

    sublocale CURRY: invertible_simulation AxB_C.resid A_BC.resid CURRY
      ..

    lemma invertible_simulation_CURRY:
    shows "invertible_simulation AxB_C.resid A_BC.resid CURRY"
      ..

    sublocale UNCURRY: invertible_simulation
                         A_BC.resid AxB_C.resid UNCURRY
      ..

    lemma invertible_simulation_UNCURRY:
    shows "invertible_simulation A_BC.resid AxB_C.resid UNCURRY"
      ..

    sublocale inverse_simulations A_BC.resid AxB_C.resid CURRY UNCURRY
      ..

    lemma inverse_simulations_CURRY_UNCURRY:
    shows "inverse_simulations A_BC.resid AxB_C.resid CURRY UNCURRY"
      ..

  end

subsection "Coextension of a Simulation"

  text \<open>
    Here we define the coextension, of a simulation \<open>G\<close> from \<open>X \<times> A\<close> to \<open>B\<close>,
    to a simulation \<open>F\<close> from \<open>X\<close> to \<open>[A, B]\<close>, and we prove that it is universal
    for the property \<open>eval \<circ> (F \<times> A) = G\<close>.
  \<close>

  context evaluation_map
  begin

    abbreviation (input) coext
       :: "'c resid \<Rightarrow> ('c \<times> 'a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> ('a, 'b) AB.arr"
    where "coext X G \<equiv> Currying.Curry3 X A B G"

    lemma Uncurry_simulation_expansion:
    assumes "weakly_extensional_rts X"
    and "simulation X AB.resid F"
    shows "Currying.Uncurry X A B F =
           map \<circ> (product_simulation.map X A F (I A))"
    proof -
      interpret X: weakly_extensional_rts X
        using assms(1) by blast
      interpret XxA: product_rts X A ..
      interpret F: simulation X AB.resid F
        using assms by blast
      interpret Currying X A B ..
      interpret A: identity_simulation A ..
      interpret FxA: product_simulation X A AB.resid A F A.map ..
      show "Uncurry F = map \<circ> FxA.map"
        using Uncurry_def map_def FxA.map_def by auto
    qed

    lemma universality:
    assumes "weakly_extensional_rts X"
    and "simulation (product_rts.resid X A) B G"
    shows "simulation X AB.resid (Currying.Curry3 X A B G)"
    and "Currying.Uncurry X A B (coext X G) = G"
    and "\<exists>!F. simulation X AB.resid F \<and> Currying.Uncurry X A B F = G"
    proof -
      interpret X: weakly_extensional_rts X
        using assms(1) by blast
      interpret XxA: product_rts X A ..
      interpret simulation XxA.resid B G
        using assms by blast
      interpret Currying X A B ..
      interpret A: identity_simulation A ..
      let ?F = "Curry G G G"
      interpret F: simulation X AB.resid ?F
        using assms Curry_preserves_simulations by blast
      interpret FxA: product_simulation X A AB.resid A ?F A.map ..
      show "simulation X (\\\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]) ?F"
        using F.simulation_axioms by blast
      show "Uncurry (coext X G) = G"
        using Uncurry_simulation_expansion Uncurry_Curry Uncurry_def
              FxA.map_def Map_Curry map_def XxA.arr_char extensional
        by auto
      moreover
      have "\<And>F'. simulation X AB.resid F' \<and> Uncurry F' = G \<Longrightarrow> F' = ?F"
      proof -
        fix F'
        assume F': "simulation X AB.resid F' \<and> Uncurry F' = G"
        interpret F': simulation X AB.resid F'
          using F' by blast
        interpret F': simulation_as_transformation X AB.resid F' ..
        interpret F'xA: product_simulation X A AB.resid A F' A.map ..
        have "Uncurry F' = G"
          using F' F'xA.map_def Uncurry_def Map_Curry map_def XxA.arr_char
            extensional
          by auto
        hence "Curry (Uncurry F') (Uncurry F') (Uncurry F') = ?F"
          by simp
        thus "F' = ?F"
          using Curry_Uncurry F'.transformation_axioms by simp
      qed
      ultimately show "\<exists>!F. simulation X AB.resid F \<and> Uncurry F = G"
        using F.simulation_axioms
        by (metis (no_types, lifting))
    qed

    lemma comp_coext_simulation:
    assumes "weakly_extensional_rts X" and "weakly_extensional_rts X'"
    and "simulation X X' G"
    and "simulation (product_rts.resid X' A) B H"
    shows "coext X' H \<circ> G  = coext X (H \<circ> product_simulation.map X A G (I A))"
    proof -
      interpret X: weakly_extensional_rts X
        using assms(1) by blast
      interpret X': weakly_extensional_rts X'
        using assms(2) by blast
      interpret XxA: product_rts X A ..
      interpret X'xA: product_rts X' A ..
      interpret G: simulation X X' G
        using assms(3) by blast
      interpret H: simulation X'xA.resid B H
        using assms(4) by blast
      interpret A: identity_simulation A ..
      interpret GxA: product_simulation X A X' A G A.map ..
      interpret coext_H: simulation X' AB.resid \<open>coext X' H\<close>
        using universality H.simulation_axioms X'.weakly_extensional_rts_axioms
        by auto
      interpret coext_H_o_G: simulation X AB.resid \<open>coext X' H \<circ> G\<close>
        using universality(1) [of X' H] simulation_comp G.simulation_axioms
          H.simulation_axioms X'.weakly_extensional_rts_axioms
        by auto
      interpret coext_H_o_G_x_A: product_simulation X A AB.resid A
                                   \<open>coext X' H \<circ> G\<close> A.map ..

      have "coext X' H \<circ> G = coext X (map \<circ> coext_H_o_G_x_A.map)"
        using universality(1-3) X.weakly_extensional_rts_axioms
          coext_H_o_G.simulation_axioms coext_H_o_G_x_A.simulation_axioms
          simulation_axioms simulation_comp [of _ _ coext_H_o_G_x_A.map _ map]
          Uncurry_simulation_expansion
        by (metis (no_types, lifting))
      also have "... = coext X
                         (map \<circ> (product_simulation.map X' A (coext X' H) A.map
                                   \<circ> GxA.map))"
        using simulation_interchange
                [of X X' G A A A.map AB.resid "coext X' H" A A.map]
              G.simulation_axioms A.simulation_axioms coext_H.simulation_axioms
              comp_simulation_identity [of A A A.map] A.simulation_axioms
          by simp
      also have "... = coext X
                         (map \<circ> product_simulation.map X' A (coext X' H) A.map
                                  \<circ> GxA.map)"
        using fun.map_comp by metis
      also have "... = coext X (H \<circ> GxA.map)"
        using H.simulation_axioms X'.weakly_extensional_rts_axioms universality(2)
              Uncurry_simulation_expansion coext_H.simulation_axioms
        by fastforce
      finally have "coext X' H \<circ> G = coext X (H \<circ> GxA.map)" by blast
      thus ?thesis by fastforce
    qed

  end

  (* TODO: See if the extensionality assumption on A can be weakened. *)
  locale evaluation_map_between_extensional_rts =
    evaluation_map +
  A: extensional_rts A
  begin

    lemma Uncurry_transformation_expansion:
    assumes "weakly_extensional_rts X"
    and "transformation X AB.resid F G T"
    shows "Currying.Uncurry X A B T =
           map \<circ> product_transformation.map X A AB.resid A F (I A) T (I A)"
    proof -
      interpret X: weakly_extensional_rts X
        using assms(1) by blast
      interpret XxA: product_rts X A ..
      interpret F: simulation X AB.resid F
        using assms transformation_def by blast
      interpret G: simulation X AB.resid G
        using assms transformation_def by blast
      interpret T: transformation X AB.resid F G T
        using assms by blast
      interpret Currying X A B ..
      interpret Uncurry_F: simulation XxA.resid B \<open>Uncurry F\<close>
        using F.simulation_axioms Uncurry_preserves_simulations by blast
      interpret Uncurry_G: simulation XxA.resid B \<open>Uncurry G\<close>
        using G.simulation_axioms Uncurry_preserves_simulations by blast
      interpret Uncurry_T: transformation
                             XxA.resid B \<open>Uncurry F\<close> \<open>Uncurry G\<close> \<open>Uncurry T\<close>
        using T.transformation_axioms Uncurry_preserves_transformations by blast
      interpret A: identity_simulation A ..
      interpret A: simulation_as_transformation A A A.map ..
      interpret TxA: product_transformation
                       X A AB.resid A F A.map G A.map T A.map ..
      show"Uncurry T = map \<circ> TxA.map"
      proof (intro transformation_eqI
                     [of XxA.resid B "Uncurry F" "Uncurry G" "Uncurry T"
                         "map \<circ> TxA.map"])
        show "transformation XxA.resid B (Uncurry F) (Uncurry G) (Uncurry T)"
          using Uncurry_T.transformation_axioms by blast
        show "transformation
                XxA.resid B (Uncurry F) (Uncurry G) (map \<circ> TxA.map)"
          using simulation_axioms F.simulation_axioms G.simulation_axioms
                TxA.transformation_axioms
                transformation_whisker_left
                  [of XxA.resid ABxA.resid TxA.F1xF0.map TxA.G1xG0.map
                      TxA.map B map]
                X.weakly_extensional_rts_axioms B.weakly_extensional_rts_axioms
                Uncurry_simulation_expansion [of X F]
                Uncurry_simulation_expansion [of X G]
          by presburger
        show "extensional_rts B"
          using B.extensional_rts_axioms by blast
        fix xa
        assume xa: "XxA.ide xa"
        show "Uncurry T xa = (map \<circ> TxA.map) xa"
          using xa Uncurry_def map_def TxA.map_def by auto
      qed
    qed

    lemma universality2:
    assumes "weakly_extensional_rts X"
    and "transformation (product_rts.resid X A) B F G T"
    shows "transformation X AB.resid
             (Currying.Curry3 X A B F) (Currying.Curry3 X A B G)
             (Currying.Curry X A B F G T)"
    and "Currying.Uncurry X A B (Currying.Curry X A B F G T) = T"
    and "\<exists>!T'. transformation X AB.resid
                 (Currying.Curry3 X A B F) (Currying.Curry3 X A B G)
                 T' \<and>
               Currying.Uncurry X A B T' = T"
    proof -
      interpret X: weakly_extensional_rts X
        using assms(1) by blast
      interpret XxA: product_rts X A ..
      interpret XxA: product_of_weakly_extensional_rts X A ..
      interpret F: simulation XxA.resid B F
        using assms transformation_def by blast
      interpret F: simulation_as_transformation XxA.resid B F ..
      interpret G: simulation XxA.resid B G
        using assms transformation_def by blast
      interpret G: simulation_as_transformation XxA.resid B G ..
      interpret T: transformation XxA.resid B F G T
        using assms transformation_def by blast
      interpret T: transformation_to_extensional_rts XxA.resid B F G T ..
      interpret Currying X A B ..
      interpret A: identity_simulation A ..

      let ?F' = "Curry3 F"
      interpret F': simulation X AB.resid ?F'
        using F.simulation_axioms Curry_preserves_simulations by blast
      let ?G' = "Curry3 G"
      interpret G': simulation X AB.resid ?G'
        using G.simulation_axioms Curry_preserves_simulations by blast
      let ?T' = "Curry F G T"
      interpret T': transformation X AB.resid ?F' ?G' ?T'
        using T.transformation_axioms Curry_preserves_transformations
        by blast

      interpret ABxA: product_of_extensional_rts AB.resid A ..
      interpret BxA: product_of_extensional_rts B A ..

      interpret IA: identity_simulation A ..
      interpret IA: simulation_as_transformation A A A.map ..
      interpret T'xA: product_transformation
                         X A AB.resid A ?F' \<open>I A\<close> ?G' \<open>I A\<close> ?T' \<open>I A\<close> ..

      show "transformation X AB.resid ?F' ?G' ?T'" ..
      moreover show "Uncurry (Curry F G T) = T"
      proof -
        have "map \<circ> T'xA.map = T"
        proof
          fix t
          show "(map \<circ> T'xA.map) t = T t"
          proof (cases "XxA.arr t")
            show "\<not> XxA.arr t \<Longrightarrow> ?thesis"
              using T.extensional T'xA.extensional extensional by simp
            assume t: "XxA.arr t"
            have 0: "X.arr (fst (XxA.src t))"
              using t XxA.arr_src_iff_arr by blast
            have 1: "A.arr (snd (XxA.src t))"
              using t XxA.arr_src_iff_arr by blast
            have 2: "AB.arr (fst (ABxA.join
                                   (Curry F G T (fst (XxA.src t)),
                                                 snd (XxA.src t))
                                   (T'xA.F1xF0.map t)))"
              using t 0 1 ABxA.arr_char BxA.joinable_iff_arr_join
                    T'xA.TC.joinable T'xA.map_simp T'xA.preserves_arr
              by presburger
            have 3: "A.arr (snd (ABxA.join
                                   (Curry F G T (fst (XxA.src t)),
                                                 snd (XxA.src t))
                                   (T'xA.F1xF0.map t)))"
              using t 0 1 ABxA.arr_char BxA.joinable_iff_arr_join
                    T'xA.TC.joinable T'xA.map_simp T'xA.preserves_arr
              by presburger

            have *: "(map \<circ> T'xA.map) t =
                     AB.Map
                       (fst (ABxA.join
                               (Curry F G T (X.src (fst t)), A.src (snd t))
                               (Curry F F F (fst t), snd t)))
                       (snd (ABxA.join
                               (Curry F G T (X.src (fst t)), A.src (snd t))
                               (Curry F F F (fst t), snd t)))"
              unfolding map_def T'xA.map_simp
              using t 0 1 2 3 XxA.src_char trg_Curry
                    T'xA.F1xF0.map_simp [of "fst t" "snd t"]
              by simp

            have 6: "ABxA.joinable
                       (Curry F G T (X.src (fst t)), A.src (snd t))
                       (Curry F F F (fst t), snd t)"
            proof -
              have "AB.joinable (Curry F G T (X.src (fst t))) (Curry3 F (fst t))"
              proof -
                have "AB.arr (Curry F G T (X.src (fst t)))"
                  using t T'.preserves_arr X.arr_src_if_arr by blast
                moreover have "AB.arr (Curry F F F (fst t))"
                  using t AB.joinable_def T'.naturality3 by simp
                moreover have "AB.Dom (Curry F G T (X.src (fst t))) =
                               AB.Dom (Curry3 F (fst t))"
                  using t Dom_Curry by auto
                moreover
                have "\<And>u. A.arr u
                              \<Longrightarrow> B.joinable
                                    (AB.Map (Curry F G T (X.src (fst t))) (A.src u) \<squnion>\<^sub>B
                                       AB.Map (Curry3 F (fst t)) (A.src u))
                                    (AB.Dom (Curry F G T (X.src (fst t))) u)"
                proof -
                  fix u
                  assume u: "A.arr u"
                  have "AB.Map (Curry F G T (X.src (fst t))) (A.src u) \<lesssim>\<^sub>B
                        AB.Map (Curry F G T (fst t)) u"
                    using t u Map_Curry B.composite_of_def T.naturality2'
                          XxA.src_char
                    by auto
                  moreover have "AB.Map (Curry3 F (fst t)) (A.src u) \<lesssim>\<^sub>B
                                 AB.Map (Curry F G T (fst t)) u"
                  proof -
                    have "F (fst t, A.src u) \<lesssim>\<^sub>B T (fst t, u)"
                    proof -
                      have 1: "F (fst t, A.src u) \\\<^sub>B T (fst t, u) =
                               F (fst t, A.src u) \\\<^sub>B
                                 (T (X.src (fst t), A.src u) \<squnion>\<^sub>B F (fst t, u))"
                        using t u T.naturality3 [of "(fst t, u)"] XxA.arr_char
                              XxA.src_char B.join_is_join_of B.join_of_unique
                              B.joinable_def
                        apply auto[1]
                        by metis
                      also have "... = (F (fst t, A.src u) \\\<^sub>B F (fst t, u)) \\\<^sub>B
                                       (T (X.src (fst t), A.src u) \\\<^sub>B F (fst t, u))"
                      proof -
                        have "B.joinable
                                (F (fst t, u))
                                (T (X.src (fst t), A.src u))"
                          using t u XxA.arr_char
                          by (metis B.join_sym B.joinable_iff_join_not_null
                              B.not_arr_null T.naturality3'\<^sub>E(1) T.preserves_arr
                              XxA.src_char fst_conv snd_conv)
                        moreover have "F (fst t, A.src u) \<frown>\<^sub>B
                                       F (fst t, u) \<squnion>\<^sub>B T (X.src (fst t), A.src u)"
                          using t u 1
                          by (metis A.con_arr_src(1) B.conE B.conI B.con_sym
                              B.join_sym T.preserves_con(2) XxA.con_arr_self
                              XxA.con_char fst_conv snd_conv)
                        ultimately show ?thesis
                          using t u B.resid_join\<^sub>E(2) B.join_sym by simp
                      qed
                      also have "... = F (X.trg (fst t), A.trg u) \\\<^sub>B
                                       (T (X.src (fst t), A.src u) \\\<^sub>B F (fst t, u))"
                        using t u XxA.con_char XxA.resid_def X.trg_def
                              F.preserves_resid [of "(fst t, A.src u)" "(fst t, u)"]
                             
                        by simp
                      moreover have "B.ide ..."
                      proof -
                        have "B.ide (F (X.trg (fst t), A.trg u))"
                          using t u F.preserves_ide XxA.ide_char by simp
                        moreover have "B.coinitial
                                          (F (X.trg (fst t), A.trg u))
                                          (T (X.src (fst t), A.src u) \\\<^sub>B F (fst t, u))"
                        proof
                          show "B.arr (F (X.trg (fst t), A.trg u))"
                            using t u F.preserves_reflects_arr by simp
                          show "B.src (F (X.trg (fst t), A.trg u)) =
                                B.src (T (X.src (fst t), A.src u) \\\<^sub>B F (fst t, u))"
                            using t u XxA.arr_char [of "(fst t, u)"]
                            by (metis B.src_ide T.naturality1 T.preserves_src
                                XxA.arr_char XxA.ide_trg XxA.src_char XxA.trg_char
                                calculation fst_conv snd_conv)
                        qed
                        ultimately show ?thesis
                          using t u B.resid_ide(2) by auto
                      qed
                      ultimately show ?thesis by simp
                    qed
                    thus ?thesis
                      using t u Map_Curry by auto
                  qed
                  moreover have "AB.Dom (Curry F G T (X.src (fst t))) u \<lesssim>\<^sub>B
                                 AB.Map (Curry F G T (fst t)) u"
                    using t u Dom_Curry Map_Curry
                    apply auto[1]
                    using A.trg_def T.general_naturality(2) XxA.ide_trg
                          XxA.resid_def XxA.trg_char
                    by force
                  ultimately show "B.joinable
                                     (AB.Map (Curry F G T (X.src (fst t))) (A.src u) \<squnion>\<^sub>B
                                        AB.Map (Curry F F F (fst t)) (A.src u))
                                     (AB.Dom (Curry F G T (X.src (fst t))) u)"
                    by (meson A.weakly_extensional_rts_axioms AB.joinable_def
                        B.extensional_rts_axioms T'.naturality3 XxA.arr_char
                        exponential_rts.intro exponential_rts.join_char(1) t u)
                qed
                ultimately show ?thesis
                  unfolding AB.join_char(1)
                  using t Map_Curry Dom_Curry
                  by (intro allI impI conjI) auto
              qed
              moreover have "A.joinable (A.src (snd t)) (snd t)"
                using t A.join_src A.join_sym A.joinable_iff_join_not_null by force
              ultimately show ?thesis
                using ABxA.join_of_char(2) by auto
            qed
            hence "ABxA.join
                     (Curry F G T (X.src (fst t)), A.src (snd t))
                     (Curry3 F (fst t), snd t) =
                   (AB.join (Curry F G T (X.src (fst t))) (Curry3 F (fst t)),
                    A.join (A.src (snd t)) (snd t))"
              using t 0 1 2 3 ABxA.join_simp by auto
            also have "... = (AB.join
                                (Curry F G T (X.src (fst t)))
                                (Curry3 F (fst t)), snd t)"
              using t A.join_src A.join_sym XxA.src_char by simp
            also have "... = (Curry F G T (fst t), snd t)"
            proof -
              have "AB.join
                      (Curry F G T (X.src (fst t)))
                      (Curry3 F (fst t)) =
                    Curry F G T (fst t)"
              proof (intro AB.arr_eqI)
                show 4: "AB.arr
                           (AB.join
                               (Curry F G T (X.src (fst t)))
                               (Curry3 F (fst t)))"
                  using t "2" T'xA.F1xF0.map_def XxA.src_char calculation
                  by auto
                show 5: "AB.arr (Curry F G T (fst t))"
                  using t T'.preserves_arr by blast
                show "AB.Dom
                        (AB.join
                           (Curry F G T (X.src (fst t)))
                           (Curry3 F (fst t))) =
                      AB.Dom (Curry F G T (fst t))"
                  using t Dom_Curry
                  by (metis 6 AB.join_is_join_of AB.join_of_unique
                      ABxA.join_of_char(2) T'.naturality3 XxA.arr_char fst_conv)
                show "AB.Cod
                        (AB.join
                           (Curry F G T (X.src (fst t))) (Curry3 F (fst t))) =
                      AB.Cod (Curry F G T (fst t))"
                  using t Cod_Curry
                  by (metis 6 AB.join_is_join_of AB.join_of_unique
                      ABxA.join_of_char(2) T'.naturality3 XxA.arr_char fst_conv)
                show "\<And>a. A.ide a \<Longrightarrow>
                             AB.Map
                               (AB.join
                                  (Curry F G T (X.src (fst t)))
                                  (Curry3 F (fst t)))
                               a =
                             AB.Map (Curry F G T (fst t)) a"
                  using t Map_Curry AB.Map_join
                  apply auto[1]
                  by (metis (no_types, lifting) 4 AB.join_is_join_of
                      AB.join_of_unique AB.joinable_iff_arr_join T'.naturality3)
              qed
              thus ?thesis by simp
            qed
            finally have "ABxA.join
                            (Curry F G T (X.src (fst t)), A.src (snd t))
                            (Curry3 F (fst t), snd t) =
                          (Curry F G T (fst t), snd t)"
              by blast
            hence "(map \<circ> T'xA.map) t = AB.Map (Curry F G T (fst t)) (snd t)"
              using * by auto
            also have "... = T t"
              using t Map_Curry by simp
            finally show "(map \<circ> T'xA.map) t = T t" by blast
          qed
        qed
        thus ?thesis
          using Uncurry_transformation_expansion [of X ?F' ?G' ?T']
                X.weakly_extensional_rts_axioms T.transformation_axioms
                Uncurry_Curry
          by blast
      qed
      moreover
      have "\<And>T''. \<lbrakk>transformation X (\\\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]) (coext X F) (coext X G) T'';
                    Uncurry T'' = T\<rbrakk>
                      \<Longrightarrow> T'' = ?T'"
      proof -
        fix T''
        assume T'': "transformation X (\\\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]) (coext X F) (coext X G) T''"
        assume 1: "Uncurry T'' = T"
        interpret T'': transformation X AB.resid \<open>coext X F\<close> \<open>coext X G\<close> T''
          using T'' by blast
        interpret T''xA: product_transformation X A AB.resid A
                           \<open>coext X F\<close> \<open>I A\<close> \<open>coext X G\<close> \<open>I A\<close> T'' \<open>I A\<close> ..
        show "T'' = ?T'"
        proof (intro transformation_eqI)
          show "transformation X (\\\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]) (coext X F) (coext X G) T''"
            by fact
          show "transformation X (\\\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]) (coext X F) (coext X G) ?T'"
            ..
          show "extensional_rts AB.resid"
            ..
          fix x
          assume x: "X.ide x"
          show "T'' x = Curry F G T x"
          proof (intro AB.arr_eqI)
            show "AB.arr (T'' x)"
              using x T''.preserves_arr by blast
            show "AB.arr (Curry F G T x)"
              using x T'.preserves_arr by blast
            show "AB.Dom (T'' x) = AB.Dom (Curry F G T x)"
              unfolding Curry_def Uncurry_def
              using x map_def
              apply auto[1]
              by (metis (no_types, opaque_lifting) AB.Map_src Map_Curry
                  T''.preserves_src X.ide_implies_arr \<open>AB.arr (T'' x)\<close>)
            show "AB.Cod (T'' x) = AB.Cod (Curry F G T x)"
              unfolding Curry_def Uncurry_def
              using x map_def
              apply auto[1]
              by (metis (no_types, opaque_lifting) AB.Map_trg Map_Curry
                  T''.preserves_trg X.ide_implies_arr \<open>AB.arr (T'' x)\<close>)
            fix a
            assume a: "A.ide a"
            have "AB.Map (T'' x) a = T (x, a)"
            proof -
              have "AB.Map (T'' x) a = AB.Map (Curry F G (Uncurry T'') x) a"
                using T'' Curry_Uncurry [of "coext X F" "coext X G" T'']
                      Uncurry_Curry F.transformation_axioms
                      G.transformation_axioms
                by simp
              also have "... = AB.Map (Curry F G T x) a"
                unfolding Curry_def Uncurry_def
                using a x 1 map_def T''xA.map_simp_ide
                      T''.transformation_axioms X.weakly_extensional_rts_axioms
                      Uncurry_transformation_expansion
                        [of X "Curry3 F" "Curry3 G" T'']
                by auto
              also have "... = T (x, a)"
                unfolding Curry_def
                using a x by simp
              finally show ?thesis by simp
            qed
            thus "AB.Map (T'' x) a = AB.Map (Curry F G T x) a"
              unfolding Curry_def Uncurry_def
              using x a map_def by auto
          qed
        qed
      qed
      ultimately
      show "\<exists>!T'. transformation X (\\\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]) (Curry3 F) (Curry3 G) T' \<and>
                  Uncurry T' = T"
        by blast
    qed

  end

subsection "Compositors"

  text \<open>
    For any RTS's \<open>A\<close>, \<open>B\<close>, and \<open>C\<close>, there exists a ``compositor'' simulation
    from the product of exponential RTS's \<open>[B, C] \<times> [A, B]\<close> to the exponential RTS \<open>[A, C]\<close>.
  \<close>

  locale COMP =
    A: extensional_rts A +
    B: extensional_rts B +
    C: extensional_rts C
  for A :: "'a resid"
  and B :: "'b resid"
  and C :: "'c resid"
  begin

    sublocale AC: exponential_rts A C ..
    sublocale AB: exponential_rts A B ..
    sublocale BC: exponential_rts B C ..

    sublocale BCxAB: product_rts BC.resid AB.resid ..
    sublocale BCxAB: product_of_extensional_rts BC.resid AB.resid ..

    interpretation AB: identity_simulation AB.resid ..
    interpretation BC: identity_simulation BC.resid ..

    interpretation ABxA: product_rts AB.resid A ..
    interpretation BCxB: product_rts BC.resid B ..
    interpretation BCxAB: identity_simulation BCxAB.resid ..
    interpretation BCxAB_x_A: product_rts BCxAB.resid A ..
    interpretation BC_x_ABxA: product_rts BC.resid ABxA.resid ..

    interpretation E_AB: RTSConstructions.evaluation_map A B ..
    interpretation E_BC: RTSConstructions.evaluation_map B C ..
    interpretation BCxE_AB: product_simulation
                              BC.resid ABxA.resid BC.resid B
                              BC.map E_AB.map ..

    interpretation ASSOC_BC_AB_A: ASSOC BC.resid AB.resid A ..
    sublocale Currying: Currying BCxAB.resid A C ..

    text \<open>
      The following definition is expressed in a form that makes it evident that it
      defines a simulation.
    \<close>

    definition map :: "('b, 'c) BC.arr \<times> ('a, 'b) AB.arr \<Rightarrow> ('a, 'c) AC.arr"
    where "map = (\<lambda>F. Currying.Curry3 F)
                   (E_BC.map \<circ> BCxE_AB.map \<circ> ASSOC_BC_AB_A.map)"

    sublocale simulation BCxAB.resid AC.resid map
      unfolding map_def
      using E_BC.simulation_axioms BCxE_AB.simulation_axioms
            ASSOC_BC_AB_A.simulation_axioms simulation_comp
      by auto

    lemma is_simulation:
    shows "simulation BCxAB.resid AC.resid map"
      ..

    sublocale binary_simulation BC.resid AB.resid AC.resid map ..

    lemma is_binary_simulation:
    shows "binary_simulation BC.resid AB.resid AC.resid map"
      ..

    sublocale E_BC_o_BCxE_AB: composite_simulation
                                BC_x_ABxA.resid BCxB.resid C
                                BCxE_AB.map E_BC.map
      ..

    text \<open>
      The following explicit formula is more useful for calculations.
      There is a bit of work involved to show that the two versions are equal,
      but notice that as a consequence we obtain a proof that the explicit formula
      actually defines a simulation.  A similar amount of work would be required
      to show this directly.
    \<close>

    lemma map_eq:
    shows "map = (\<lambda>gf. if BCxAB.arr gf
                       then AC.MkArr
                              (BC.Dom (fst gf) \<circ> AB.Dom (snd gf))
                              (BC.Cod (fst gf) \<circ> AB.Cod (snd gf))
                              (BC.Map (fst gf) \<circ> AB.Map (snd gf))
                       else AC.Null)"
    proof
      fix gf
      show "map gf = (if BCxAB.arr gf
                      then AC.MkArr
                             (BC.Dom (fst gf) \<circ> AB.Dom (snd gf))
                             (BC.Cod (fst gf) \<circ> AB.Cod (snd gf))
                             (BC.Map (fst gf) \<circ> AB.Map (snd gf))
                      else AC.Null)"
      proof (cases "BCxAB.arr gf")
        show "\<not> BCxAB.arr gf \<Longrightarrow> ?thesis"
          using map_def Currying.Curry_def AC.null_char by presburger
        assume gf: "BCxAB.arr gf"
        have "AC.Dom (map gf) = BC.Dom (fst gf) \<circ> AB.Dom (snd gf)"
        proof -
          have "AC.Dom (map gf) =
                (\<lambda>t. E_BC.map
                       (BCxE_AB.map (ASSOC_BC_AB_A.map (BCxAB.src gf, t))))"
            using gf Currying.Dom_Curry map_def by simp
          also have "... = BC.Dom (fst gf) \<circ> AB.Dom (snd gf)"
          proof
            fix t
            have "E_BC.map
                    (BCxE_AB.map (ASSOC_BC_AB_A.map (BCxAB.src gf, t))) =
                  (if A.arr t
                   then E_BC.map
                          (BCxE_AB.map (fst (BCxAB.src gf), snd (BCxAB.src gf), t))
                   else C.null)"
              using gf ASSOC_BC_AB_A.map_def BCxAB.arr_src_iff_arr
                  BCxAB.extensional
              by (metis (no_types, lifting) ASSOC_BC_AB_A.map_eq
                  ASSOC_BC_AB_A.preserves_reflects_arr BCxAB_x_A.arr_char
                  BCxE_AB.preserves_reflects_arr E_BC.extensional
                  fst_conv snd_conv)
            also have "... = E_BC.map
                               (BCxE_AB.map
                                 (fst (BCxAB.src gf),
                                  snd (BCxAB.src gf), t))"
              using BCxE_AB.map_def E_BC.extensional by fastforce
            also have "... = E_BC.map
                               (BCxE_AB.map
                                 (BC.src (fst gf), AB.src (snd gf), t))"
              by (metis (no_types, lifting) AB.src_eqI BC.src_eqI
                  BCxAB.con_arr_src(2) BCxAB.con_char BCxAB.ide_char
                  BCxAB.ide_src gf)
            also have "... = E_BC.map
                               (BC.src (fst gf),
                                E_AB.map (AB.src (snd gf), t))"
              using gf AB.src_simp BCxE_AB.map_simp BCxE_AB.map_def
                E_BC.extensional
              by simp
            also have "... = E_BC.map (BC.src (fst gf), AB.Dom (snd gf) t)"
              using gf E_AB.extensional
                    E_AB.map_simp [of "(AB.src (snd gf), t)"]
                    AB.src_simp [of "snd gf"]
              apply auto[1]
              by (metis (no_types, lifting) AB.arr_MkArr AB.arr_src_iff_arr
                  transformation.extensional)
            also have "... = BC.Dom (fst gf) (AB.Dom (snd gf) t)"
              using gf BC.src_simp E_BC.map_simp E_BC.extensional
              apply auto[1]
              by (metis (mono_tags, lifting) BC.Map.simps(1) BC.arr_MkArr
                  BC.arr_src_iff_arr transformation.extensional)
            also have "... = (BC.Dom (fst gf) \<circ> AB.Dom (snd gf)) t"
              by simp
            finally show "E_BC.map
                            (BCxE_AB.map
                              (ASSOC_BC_AB_A.map (BCxAB.src gf, t))) =
                          (BC.Dom (fst gf) \<circ> AB.Dom (snd gf)) t"
              by blast
          qed
          finally show ?thesis by blast
        qed
        moreover have "AC.Cod (map gf) = BC.Cod (fst gf) \<circ> AB.Cod (snd gf)"
        proof -
          have "AC.Cod (map gf) =
                (\<lambda>t. E_BC.map
                       (BCxE_AB.map (ASSOC_BC_AB_A.map (BCxAB.trg gf, t))))"
            using gf Currying.Cod_Curry map_def by simp
          also have "... = BC.Cod (fst gf) \<circ> AB.Cod (snd gf)"
          proof
            fix t
            have "E_BC.map
                    (BCxE_AB.map (ASSOC_BC_AB_A.map (BCxAB.trg gf, t))) =
                  (if A.arr t
                   then E_BC.map
                          (BCxE_AB.map
                            (fst (BCxAB.trg gf), snd (BCxAB.trg gf), t))
                   else C.null)"
              using gf ASSOC_BC_AB_A.map_def BCxAB.arr_trg_iff_arr
                BCxAB.extensional
              by (metis (no_types, lifting) ASSOC_BC_AB_A.map_eq
                  ASSOC_BC_AB_A.preserves_reflects_arr BCxAB_x_A.arr_char
                  BCxE_AB.preserves_reflects_arr E_BC.extensional
                  fst_conv snd_conv)
            also have "... = E_BC.map
                               (BCxE_AB.map
                                  (fst (BCxAB.trg gf), snd (BCxAB.trg gf), t))"
              using BCxE_AB.map_def E_BC.extensional by fastforce
            also have "... = E_BC.map
                               (BCxE_AB.map
                                  (BC.trg (fst gf), AB.trg (snd gf), t))"
              using BCxAB.trg_char gf by auto
            also have "... = E_BC.map
                               (BC.trg (fst gf), E_AB.map (AB.trg (snd gf), t))"
              using gf AB.trg_simp BCxE_AB.map_simp
              by (simp add: BCxE_AB.map_def E_BC.extensional)
            also have "... = E_BC.map (BC.trg (fst gf), AB.Cod (snd gf) t)"
              using gf E_AB.extensional E_AB.map_simp [of "(AB.trg (snd gf), t)"]
                    AB.trg_simp [of "snd gf"]
              apply auto[1]
              by (metis (no_types, lifting) AB.arr_MkArr AB.arr_trg_iff_arr
                  transformation.extensional)
            also have "... = BC.Cod (fst gf) (AB.Cod (snd gf) t)"
              using gf BC.trg_simp BCxE_AB.map_simp E_BC.map_simp E_BC.extensional
              apply auto[1]
              by (metis (mono_tags, lifting) BC.Map.simps(1) BC.arr_MkArr
                  BC.arr_trg_iff_arr transformation.extensional)
            also have "... = (BC.Cod (fst gf) \<circ> AB.Cod (snd gf)) t"
              by simp
            finally show "E_BC.map
                            (BCxE_AB.map
                               (ASSOC_BC_AB_A.map (BCxAB.trg gf, t))) =
                          (BC.Cod (fst gf) \<circ> AB.Cod (snd gf)) t"
              by blast
          qed
          finally show ?thesis by blast
        qed
        moreover have "AC.Map (map gf) = BC.Map (fst gf) \<circ> AB.Map (snd gf)"
        proof -
          have "AC.Map (map gf) =
                (\<lambda>t. E_BC.map (BCxE_AB.map (ASSOC_BC_AB_A.map (gf, t))))"
            using gf Currying.Map_Curry map_def by simp
          also have "... = BC.Map (fst gf) \<circ> AB.Map (snd gf)"
          proof
            fix t
            have "E_BC.map (BCxE_AB.map (ASSOC_BC_AB_A.map (gf, t))) =
                  (if A.arr t
                   then E_BC.map (BCxE_AB.map (fst gf, snd gf, t))
                   else C.null)"
              using gf ASSOC_BC_AB_A.map_def
              by (metis (no_types, lifting) ASSOC_BC_AB_A.map_eq
                  ASSOC_BC_AB_A.preserves_reflects_arr BCxAB_x_A.arr_char
                  BCxE_AB.preserves_reflects_arr E_BC.extensional fst_conv snd_conv)
            also have "... = E_BC.map (BCxE_AB.map (fst gf, snd gf, t))"
              using BCxE_AB.map_def E_BC_o_BCxE_AB.extensional by force
            also have "... = BC.Map (fst gf) (AB.Map (snd gf) t)"
              using gf E_AB.map_def E_BC.map_def BCxE_AB.map_def AB.arr_char
                BC.arr_char
              apply (auto simp add: transformation.preserves_arr)[1]
              by (simp add: transformation_axioms_def transformation_def)
            also have "... = (BC.Map (fst gf) \<circ> AB.Map (snd gf)) t"
              by simp
            finally show "E_BC.map
                            (BCxE_AB.map (ASSOC_BC_AB_A.map (gf, t))) =
                          (BC.Map (fst gf) \<circ> AB.Map (snd gf)) t"
              by blast
          qed
          finally show ?thesis by blast
        qed
        ultimately show ?thesis
          using gf Currying.Curry_simp map_def
          by (simp add: Currying.Curry_def AC.null_char)
      qed
    qed

  end

subsection "Functoriality of Exponential"

  text \<open>
    Here we show that the covariant and contravariant exponential RTS constructions are
    ``meta-functorial'': they preserve identity simulations and compositions of simulations.
    We say ``meta-functorial'', rather than ``functorial'', because we do not have formal
    categories to serve as the domain and codomain for these constructions.
  \<close>

  abbreviation cov_Exp
    :: "'c resid \<Rightarrow> 'a resid \<Rightarrow> 'b resid \<Rightarrow> ('a \<Rightarrow> 'b)
           \<Rightarrow> ('c, 'a) exponential_rts.arr \<Rightarrow> ('c, 'b) exponential_rts.arr"  ("Exp\<^sup>\<rightarrow>")
  where "Exp\<^sup>\<rightarrow> X B C \<equiv>
         \<lambda>G t2. COMP.map X B C (exponential_rts.MkIde G, t2)"

  abbreviation cnt_Exp
    :: "'a resid \<Rightarrow> 'b resid \<Rightarrow> 'c resid \<Rightarrow> ('a \<Rightarrow> 'b)
           \<Rightarrow> ('b, 'c) exponential_rts.arr \<Rightarrow> ('a, 'c) exponential_rts.arr"  ("Exp\<^sup>\<leftarrow>")
  where "Exp\<^sup>\<leftarrow> A B X \<equiv>
         \<lambda>F t1. COMP.map A B X (t1, exponential_rts.MkIde F)"

  lemma cov_Exp_eq:
  assumes "extensional_rts X" and "extensional_rts B" and "extensional_rts C"
  shows "Exp\<^sup>\<rightarrow> X B C G =
         (\<lambda>t2. if simulation B C G \<and> residuation.arr (exponential_rts.resid X B) t2
               then exponential_rts.MkArr
                      (G \<circ> exponential_rts.Dom t2)
                      (G \<circ> exponential_rts.Cod t2)
                      (G \<circ> exponential_rts.Map t2)
               else exponential_rts.Null)"
  proof
    interpret X: extensional_rts X
      using assms(1) by blast
    interpret B: extensional_rts B
      using assms(2) by blast
    interpret C: extensional_rts C
      using assms(3) by blast
    interpret XB: exponential_rts X B ..
    interpret XC: exponential_rts X C ..
    interpret COMP: COMP X B C ..
    fix t2
    show "Exp\<^sup>\<rightarrow> X B C G t2 =
          (if simulation B C G \<and> XB.arr t2
           then XC.MkArr (G \<circ> XB.Dom t2) (G \<circ> XB.Cod t2) (G \<circ> XB.Map t2)
           else XC.Null)"
      using COMP.map_eq apply simp
      using COMP.BC.ide_implies_arr transformation.axioms(4) by blast
  qed

  lemma cnt_Exp_eq:
  assumes "extensional_rts X" and "extensional_rts A" and "extensional_rts B"
  shows "Exp\<^sup>\<leftarrow> A B X F =
         (\<lambda>t1. if residuation.arr (exponential_rts.resid B X) t1 \<and> simulation A B F
               then exponential_rts.MkArr
                      (exponential_rts.Dom t1 \<circ> F)
                      (exponential_rts.Cod t1 \<circ> F)
                      (exponential_rts.Map t1 \<circ> F)
         else exponential_rts.Null)"
  proof
    interpret X: extensional_rts X
      using assms(1) by blast
    interpret A: extensional_rts A
      using assms(2) by blast
    interpret B: extensional_rts B
      using assms(3) by blast
    interpret AX: exponential_rts A X ..
    interpret BX: exponential_rts B X ..
    interpret COMP: COMP A B X ..
    fix t1
    show "Exp\<^sup>\<leftarrow> A B X F t1 =
          (if BX.arr t1 \<and> simulation A B F
           then AX.MkArr (BX.Dom t1 \<circ> F) (BX.Cod t1 \<circ> F) (BX.Map t1 \<circ> F)
           else AX.Null)"
      using COMP.map_eq apply simp
      using COMP.AB.ide_implies_arr transformation_def by blast
  qed

  lemma simulation_cov_Exp:
  assumes "extensional_rts X" and "extensional_rts B" and "extensional_rts C"
  and "simulation B C G"
  shows "simulation (exponential_rts.resid X B) (exponential_rts.resid X C)
           (Exp\<^sup>\<rightarrow> X B C G)"
  proof -
    interpret COMP X B C
      using assms COMP_def by blast
    show ?thesis
      using assms(4) fixing_ide_gives_simulation_1 by blast
  qed

  lemma simulation_cnt_Exp:
  assumes "extensional_rts X" and "extensional_rts A" and "extensional_rts B"
  and "simulation A B F"
  shows "simulation (exponential_rts.resid B X) (exponential_rts.resid A X)
           (Exp\<^sup>\<leftarrow> A B X F)"
  proof -
    interpret COMP A B X
      using assms COMP_def by blast
    show ?thesis
      using assms(4) fixing_ide_gives_simulation_0 by blast
  qed

  lemma cov_Exp_ide:
  assumes "extensional_rts X" and "extensional_rts B"
  shows "Exp\<^sup>\<rightarrow> X B B (I B) = I (exponential_rts.resid X B)"
  proof -
    interpret X: extensional_rts X
      using assms(1) by blast
    interpret B: extensional_rts B
      using assms(2) by blast
    interpret XB: exponential_rts X B ..
    interpret BB: exponential_rts B B ..
    interpret B: identity_simulation B
      using assms
      by (simp add: extensional_rts.axioms(1) identity_simulation.intro)
    interpret I_XB: identity_simulation XB.resid ..
    interpret COMP X B B
      using assms COMP_def by blast
    interpret XB: simulation XB.resid XB.resid \<open>Exp\<^sup>\<rightarrow> X B B B.map\<close>
      using simulation_cov_Exp X.extensional_rts_axioms B.extensional_rts_axioms
            B.simulation_axioms
      by blast
    show ?thesis
    proof
      fix t2
      show "COMP.map X B B (BB.MkIde B.map, t2) = I_XB.map t2"
      proof (cases "XB.arr t2")
        show "\<not> XB.arr t2 \<Longrightarrow> ?thesis"
          using XB.extensional XB.extensional by presburger
        assume t2: "XB.arr t2"
        interpret t2: transformation X B \<open>XB.Dom t2\<close> \<open>XB.Cod t2\<close> \<open>XB.Map t2\<close>
          using t2 by blast
        have "B.map \<circ> XB.Dom t2 = XB.Dom t2"
          using comp_identity_simulation t2.F.simulation_axioms by blast
        moreover have "B.map \<circ> XB.Cod t2 = XB.Cod t2"
          using comp_identity_simulation t2.G.simulation_axioms by blast
        moreover have "B.map \<circ> XB.Map t2 = XB.Map t2"
        proof
          fix x
          show "(B.map \<circ> XB.Map t2) x = XB.Map t2 x"
            apply simp
            by (metis t2.extensional t2.preserves_arr)
        qed
        ultimately show ?thesis
          using t2 map_eq comp_identity_simulation XB.MkArr_Map XB.arr_char
                XB.preserves_reflects_arr
          by force
      qed
    qed
  qed

  lemma cnt_Exp_ide:
  assumes "extensional_rts X" and "extensional_rts B"
  shows "Exp\<^sup>\<leftarrow> B B X (I B) = I (exponential_rts.resid B X)"
  proof -
    interpret X: extensional_rts X
      using assms(1) by blast
    interpret B: extensional_rts B
      using assms(2) by blast
    interpret BX: exponential_rts B X ..
    interpret BB: exponential_rts B B ..
    interpret B: identity_simulation B
      using assms
      by (simp add: extensional_rts.axioms(1) identity_simulation.intro)
    interpret I_BX: identity_simulation BX.resid ..
    interpret COMP B B X
      using assms COMP_def by blast
    interpret BX: simulation BX.resid BX.resid \<open>Exp\<^sup>\<leftarrow> B B X B.map\<close>
      using X.extensional_rts_axioms B.extensional_rts_axioms simulation_cnt_Exp
            B.simulation_axioms
      by blast
    show ?thesis
    proof
      fix t1
      show "COMP.map B B X (t1, BB.MkIde (I B)) = I_BX.map t1"
      proof (cases "BX.arr t1")
        show "\<not> BX.arr t1 \<Longrightarrow> ?thesis"
          using BX.extensional [of t1] BX.extensional [of t1] by presburger
        assume t1: "BX.arr t1"
        interpret t1: transformation B X \<open>BX.Dom t1\<close> \<open>BX.Cod t1\<close> \<open>BX.Map t1\<close>
          using t1 by blast
        have "BX.Dom t1 \<circ> B.map = BX.Dom t1"
          using comp_simulation_identity t1.F.simulation_axioms by blast
        moreover have "BX.Cod t1 \<circ> B.map = BX.Cod t1"
          using comp_simulation_identity t1.G.simulation_axioms by blast
        moreover have "BX.Map t1 \<circ> B.map = BX.Map t1"
        proof
          fix x
          show "(BX.Map t1 \<circ> B.map) x = BX.Map t1 x"
            using t1.extensional by fastforce
        qed
        ultimately show ?thesis
          using t1 map_eq comp_identity_simulation BX.MkArr_Map BX.arr_char
                BX.preserves_reflects_arr
          by force
      qed
    qed
  qed

  lemma cov_Exp_comp:
  assumes "extensional_rts X" and "extensional_rts B" and "extensional_rts C"
  and "extensional_rts D" and "simulation B C F" and "simulation C D G"
  shows "Exp\<^sup>\<rightarrow> X B D (G \<circ> F) = Exp\<^sup>\<rightarrow> X C D G \<circ> Exp\<^sup>\<rightarrow> X B C F"
  proof -
    interpret X: extensional_rts X
      using assms(1) by blast
    interpret B: extensional_rts B
      using assms(2) by blast
    interpret C: extensional_rts C
      using assms(3) by blast
    interpret D: extensional_rts D
      using assms(4) by blast
    interpret XB: exponential_rts X B ..
    interpret BC: exponential_rts B C ..
    interpret CD: exponential_rts C D ..
    interpret BD: exponential_rts B D ..
    interpret XC: exponential_rts X C ..
    interpret XD: exponential_rts X D ..
    interpret F: simulation B C F
      using assms(5) by blast
    interpret G: simulation C D G
      using assms(6) by blast
    interpret GoF: composite_simulation B C D F G ..
    interpret XBC: COMP X B C
      using assms COMP_def by blast
    interpret XCD: COMP X C D
      using assms COMP_def by blast
    interpret XBD: COMP X B D
      using assms COMP_def by blast
    interpret EXP_F: simulation XB.resid XC.resid \<open>Exp\<^sup>\<rightarrow> X B C F\<close>
      using assms simulation_cov_Exp by blast
    interpret EXP_G: simulation XC.resid XD.resid \<open>Exp\<^sup>\<rightarrow> X C D G\<close>
      using assms simulation_cov_Exp by blast
    interpret EXP_GoF: simulation XB.resid XD.resid \<open>Exp\<^sup>\<rightarrow> X B D (G \<circ> F)\<close>
      using assms GoF.simulation_axioms simulation_cov_Exp
      by blast
    interpret F: simulation_as_transformation B C F ..
    interpret G: simulation_as_transformation C D G ..
    show "Exp\<^sup>\<rightarrow> X B D (G \<circ> F) = Exp\<^sup>\<rightarrow> X C D G \<circ> Exp\<^sup>\<rightarrow> X B C F"
    proof
      fix t2
      show "Exp\<^sup>\<rightarrow> X B D (G \<circ> F) t2 = (Exp\<^sup>\<rightarrow> X C D G \<circ> Exp\<^sup>\<rightarrow> X B C F) t2"
      proof (cases "XB.arr t2")
        show "\<not> XB.arr t2 \<Longrightarrow> ?thesis"
          using EXP_GoF.extensional EXP_F.extensional EXP_G.extensional
          by simp
        assume t2: "XB.arr t2"
        interpret t2: transformation X B \<open>XB.Dom t2\<close> \<open>XB.Cod t2\<close> \<open>XB.Map t2\<close>
          using t2 by blast
        show ?thesis
          using t2 XBD.map_eq XCD.map_eq XBC.map_eq transformation_whisker_left
                F.transformation_axioms G.transformation_axioms
                t2.transformation_axioms C.weakly_extensional_rts_axioms
                D.weakly_extensional_rts_axioms F.simulation_axioms
                G.simulation_axioms
                transformation_whisker_left
                  [of X B "XB.Dom t2" "XB.Cod t2" "XB.Map t2" C F]
          by auto
      qed
    qed
  qed

  lemma cnt_Exp_comp:
  assumes "extensional_rts X" and "extensional_rts B" and "extensional_rts C"
  and "extensional_rts D" and "simulation B C F" and "simulation C D G"
  shows "Exp\<^sup>\<leftarrow> B D X (G \<circ> F) = Exp\<^sup>\<leftarrow> B C X F \<circ> Exp\<^sup>\<leftarrow> C D X G"
  proof -
    interpret X: extensional_rts X
      using assms(1) by blast
    interpret B: extensional_rts B
      using assms(2) by blast
    interpret C: extensional_rts C
      using assms(3) by blast
    interpret D: extensional_rts D
      using assms(4) by blast
    interpret BC: exponential_rts B C ..
    interpret CD: exponential_rts C D ..
    interpret BD: exponential_rts B D ..
    interpret BX: exponential_rts B X ..
    interpret CX: exponential_rts C X ..
    interpret DX: exponential_rts D X ..
    interpret F: simulation B C F
      using assms(5) by blast
    interpret G: simulation C D G
      using assms(6) by blast
    interpret GoF: composite_simulation B C D F G ..
    interpret BCX: COMP B C X
      using assms COMP_def by blast
    interpret CDX: COMP C D X
      using assms COMP_def by blast
    interpret BDX: COMP B D X
      using assms COMP_def by blast
    interpret EXP_F: simulation CX.resid BX.resid \<open>Exp\<^sup>\<leftarrow> B C X F\<close>
      using assms simulation_cnt_Exp by blast
    interpret EXP_G: simulation DX.resid CX.resid \<open>Exp\<^sup>\<leftarrow> C D X G\<close>
      using assms simulation_cnt_Exp by blast
    interpret EXP_GoF: simulation DX.resid BX.resid \<open>Exp\<^sup>\<leftarrow> B D X (G \<circ> F)\<close>
      using assms GoF.simulation_axioms simulation_cnt_Exp
      by blast
    interpret F: simulation_as_transformation B C F ..
    interpret G: simulation_as_transformation C D G ..
    show "Exp\<^sup>\<leftarrow> B D X (G \<circ> F) = Exp\<^sup>\<leftarrow> B C X F \<circ> Exp\<^sup>\<leftarrow> C D X G"
    proof
      fix t1
      show "Exp\<^sup>\<leftarrow> B D X (G \<circ> F) t1 = (Exp\<^sup>\<leftarrow> B C X F \<circ> Exp\<^sup>\<leftarrow> C D X G) t1"
      proof (cases "DX.arr t1")
        show "\<not> DX.arr t1 \<Longrightarrow> ?thesis"
          using EXP_GoF.extensional EXP_F.extensional EXP_G.extensional
          by simp
        assume t1: "DX.arr t1"
        interpret t1: transformation D X \<open>DX.Dom t1\<close> \<open>DX.Cod t1\<close> \<open>DX.Map t1\<close>
          using t1 by blast
        show ?thesis
          using t1 BDX.map_eq CDX.map_eq BCX.map_eq
                F.transformation_axioms G.transformation_axioms
                t1.transformation_axioms B.weakly_extensional_rts_axioms
                C.weakly_extensional_rts_axioms F.simulation_axioms
                G.simulation_axioms transformation_whisker_right
                transformation_whisker_right
                  [of D X "DX.Dom t1" "DX.Cod t1" "DX.Map t1" C G]
          by auto
      qed
    qed
  qed

  lemma cov_Exp_preserves_inverse_simulations:
  assumes "extensional_rts X" and "extensional_rts B" and "extensional_rts C"
  and "inverse_simulations B C G F"
  shows "inverse_simulations
            (exponential_rts.resid X B) (exponential_rts.resid X C)
            (Exp\<^sup>\<rightarrow> X C B G) (Exp\<^sup>\<rightarrow> X B C F)"
  proof -
    interpret X: extensional_rts X
      using assms(1) by blast
    interpret B: extensional_rts B
      using assms(2) by blast
    interpret C: extensional_rts C
      using assms(3) by blast
    interpret XB: exponential_rts X B ..
    interpret XC: exponential_rts X C ..
    interpret B: identity_simulation B
      using assms
      by (simp add: extensional_rts.axioms(1) identity_simulation.intro)
    interpret XB: identity_simulation XB.resid ..
    interpret C: identity_simulation C
      using assms
      by (simp add: extensional_rts.axioms(1) identity_simulation.intro)
    interpret XC: identity_simulation XC.resid ..
    interpret F: simulation B C F
      using assms(3-4) inverse_simulations_def by auto
    interpret G: simulation C B G
      using assms
      by (simp add: inverse_simulations_def)
    interpret XBC: COMP X B C
      using assms COMP_def by blast
    interpret XCB: COMP X C B
      using assms COMP_def by blast
    interpret XBB: COMP X B B
      using assms COMP_def by blast
    interpret XCC: COMP X C C
      using assms COMP_def by blast
    interpret HOM_F: simulation XB.resid XC.resid \<open>Exp\<^sup>\<rightarrow> X B C F\<close>
      using assms simulation_cov_Exp F.simulation_axioms by blast
    interpret HOM_G: simulation XC.resid XB.resid \<open>Exp\<^sup>\<rightarrow> X C B G\<close>
      using assms simulation_cov_Exp G.simulation_axioms by blast
    interpret FG: inverse_simulations B C G F
      using assms by blast
    show ?thesis
    proof
      show "Exp\<^sup>\<rightarrow> X B C F \<circ> Exp\<^sup>\<rightarrow> X C B G = XC.map"
      proof -
        have "Exp\<^sup>\<rightarrow> X B C F \<circ> Exp\<^sup>\<rightarrow> X C B G = Exp\<^sup>\<rightarrow> X C C (F \<circ> G)"
          using assms cov_Exp_comp [of X C B C G F] F.simulation_axioms
            G.simulation_axioms
          by presburger
        also have "... = Exp\<^sup>\<rightarrow> X C C C.map"
          using FG.inv by simp
        also have "... = XC.map"
          using assms cov_Exp_ide by blast
        finally show ?thesis by blast
      qed
      show "Exp\<^sup>\<rightarrow> X C B G \<circ> Exp\<^sup>\<rightarrow> X B C F = XB.map"
      proof -
        have "Exp\<^sup>\<rightarrow> X C B G \<circ> Exp\<^sup>\<rightarrow> X B C F = Exp\<^sup>\<rightarrow> X B B (G \<circ> F)"
          using assms cov_Exp_comp [of X B C B F G] F.simulation_axioms
            G.simulation_axioms
          by presburger
        also have "... = Exp\<^sup>\<rightarrow> X B B B.map"
          using FG.inv' by simp
        also have "... = XB.map"
          using assms cov_Exp_ide by blast
        finally show ?thesis by blast
      qed
    qed
  qed

  lemma cov_Exp_preserves_invertible_simulations:
  assumes "extensional_rts X" and "extensional_rts B" and "extensional_rts C"
  and "invertible_simulation B C F"
  shows "invertible_simulation
            (exponential_rts.resid X B) (exponential_rts.resid X C)
            (Exp\<^sup>\<rightarrow> X B C F)"
  proof -
    obtain G where G: "inverse_simulations B C G F"
      using assms inverse_simulations_def invertible_simulation_def' by blast
    have "inverse_simulations
            (exponential_rts.resid X B) (exponential_rts.resid X C)
            (Exp\<^sup>\<rightarrow> X C B G) (Exp\<^sup>\<rightarrow> X B C F)"
      using assms G cov_Exp_preserves_inverse_simulations by blast
    thus ?thesis
      using inverse_simulations_def invertible_simulation_def' by blast
  qed

  lemma cnt_Exp_preserves_inverse_simulations:
  assumes "extensional_rts X" and "extensional_rts B" and "extensional_rts C"
  and "inverse_simulations B C G F"
  shows "inverse_simulations
            (exponential_rts.resid B X) (exponential_rts.resid C X)
            (Exp\<^sup>\<leftarrow> B C X F) (Exp\<^sup>\<leftarrow> C B X G)"
  proof -
    interpret X: extensional_rts X
      using assms(1) by blast
    interpret B: extensional_rts B
      using assms(2) by blast
    interpret C: extensional_rts C
      using assms(3) by blast
    interpret BX: exponential_rts B X ..
    interpret CX: exponential_rts C X ..
    interpret B: identity_simulation B
      using assms
      by (simp add: extensional_rts.axioms(1) identity_simulation.intro)
    interpret BX: identity_simulation BX.resid ..
    interpret C: identity_simulation C
      using assms
      by (simp add: extensional_rts.axioms(1) identity_simulation.intro)
    interpret CX: identity_simulation CX.resid ..
    interpret F: simulation B C F
      using assms(3-4) inverse_simulations_def by auto
    interpret G: simulation C B G
      using assms by (simp add: inverse_simulations_def)
    interpret HOM_F: simulation CX.resid BX.resid \<open>Exp\<^sup>\<leftarrow> B C X F\<close>
      using assms simulation_cnt_Exp [of X B C F] F.simulation_axioms by blast
    interpret HOM_G: simulation BX.resid CX.resid \<open>Exp\<^sup>\<leftarrow> C B X G\<close>
      using assms simulation_cnt_Exp [of X C B G] G.simulation_axioms by blast
    interpret FG: inverse_simulations B C G F
      using assms by blast
    show ?thesis
    proof
      show "Exp\<^sup>\<leftarrow> C B X G \<circ> Exp\<^sup>\<leftarrow> B C X F = CX.map"
        using assms cnt_Exp_comp [of X C B C G F] F.simulation_axioms
              G.simulation_axioms FG.inv cnt_Exp_ide
        by force
      show "Exp\<^sup>\<leftarrow> B C X F \<circ> Exp\<^sup>\<leftarrow> C B X G = BX.map"
        using assms cnt_Exp_comp [of X B C B F G] F.simulation_axioms
              G.simulation_axioms FG.inv' cnt_Exp_ide
        by force
    qed
  qed

  lemma cnt_Exp_preserves_invertible_simulations:
  assumes "extensional_rts X" and "extensional_rts B" and "extensional_rts C"
  and "invertible_simulation B C F"
  shows "invertible_simulation
            (exponential_rts.resid C X) (exponential_rts.resid B X)
            (Exp\<^sup>\<leftarrow> B C X F)"
  proof -
    obtain G where G: "inverse_simulations B C G F"
      using assms inverse_simulations_def invertible_simulation_def' by blast
    show ?thesis
      using assms G cnt_Exp_preserves_inverse_simulations
            inverse_simulations_sym inverse_simulations_def invertible_simulation_def'
      by fast
  qed

end
