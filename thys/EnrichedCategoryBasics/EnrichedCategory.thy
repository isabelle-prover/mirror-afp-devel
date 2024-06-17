(*  Title:       EnrichedCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

text \<open>
  The notion of an enriched category \<^cite>\<open>"kelly-enriched-category"\<close>
  generalizes the concept of category by replacing the hom-sets of an ordinary category by
  objects of an arbitrary monoidal category \<open>M\<close>.
  The choice, for each object \<open>a\<close>, of a distinguished element \<open>id a : a \<rightarrow> a\<close> as an identity,
  is replaced by an arrow \<open>Id a : \<I> \<rightarrow> Hom a a\<close> of \<open>M\<close>.  The composition operation is similarly
  replaced by a family of arrows \<open>Comp a b c : Hom B C \<otimes> Hom A B \<rightarrow> Hom A C\<close> of \<open>M\<close>.
  The identity and composition are required to satisfy unit and associativity laws which are
  expressed as commutative diagrams in \<open>M\<close>.
\<close>

theory EnrichedCategory
imports ClosedMonoidalCategory
begin

  (* TODO: Move this. *)
  context monoidal_category
  begin

    abbreviation \<iota>'  ("\<iota>\<^sup>-\<^sup>1")
    where "\<iota>' \<equiv> inv \<iota>"

  end

  (* TODO: Put the following with the rest of the symmetric monoidal category development. *)
  context elementary_symmetric_monoidal_category
  begin

    lemma sym_unit:
    shows "\<iota> \<cdot> \<s>[\<I>, \<I>] = \<iota>"
      by (simp add: \<iota>_def unitor_coherence unitor_coincidence(2))

    lemma sym_inv_unit:
    shows "\<s>[\<I>, \<I>] \<cdot> inv \<iota> = inv \<iota>"
      using sym_unit
      by (metis MC.unit_is_iso arr_inv cod_inv comp_arr_dom comp_cod_arr
          iso_cancel_left iso_is_arr)

  end

  section "Basic Definitions"

  (*
   * TODO: The arguments of Comp here are the reverse of the way they are in ConcreteCategory,
   * because I have found that ordering confusing.  At some point these should be made
   * consistent in the way that seems to work out the best.
   *)

  locale enriched_category =
    monoidal_category +
  fixes Obj :: "'o set"
  and Hom :: "'o \<Rightarrow> 'o \<Rightarrow> 'a"
  and Id :: "'o \<Rightarrow> 'a"
  and Comp :: "'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'a"
  assumes ide_Hom [intro, simp]: "\<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow> ide (Hom a b)"
    and Id_in_hom [intro]: "a \<in> Obj \<Longrightarrow> \<guillemotleft>Id a : \<I> \<rightarrow> Hom a a\<guillemotright>"
    and Comp_in_hom [intro]: "\<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj\<rbrakk> \<Longrightarrow>
                                 \<guillemotleft>Comp a b c : Hom b c \<otimes> Hom a b \<rightarrow> Hom a c\<guillemotright>"
    and Comp_Hom_Id: "\<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow>
                        Comp a a b \<cdot> (Hom a b \<otimes> Id a) = \<r>[Hom a b]"
    and Comp_Id_Hom: "\<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow>
                        Comp a b b \<cdot> (Id b \<otimes> Hom a b) = \<l>[Hom a b]"
    and Comp_assoc: "\<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj; d \<in> Obj\<rbrakk> \<Longrightarrow>
                       Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b) =
                       Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                         \<a>[Hom c d, Hom b c, Hom a b]"

  text\<open>
    A functor from an enriched category \<open>A\<close> to an enriched category \<open>B\<close> consists of
    an object map \<open>F\<^sub>o : Obj\<^sub>A \<rightarrow> Obj\<^sub>B\<close> and a map \<open>F\<^sub>a\<close> that assigns to each pair of objects
    \<open>a\<close> \<open>b\<close> in \<open>Obj\<^sub>A\<close> an arrow \<open>F\<^sub>a a b : Hom\<^sub>A a b \<rightarrow> Hom\<^sub>B (F\<^sub>o a) (F\<^sub>o b)\<close> of the underlying
    monoidal category, subject to equations expressing that identities and composition
    are preserved.
  \<close>

  locale enriched_functor =
    monoidal_category C T \<alpha> \<iota> +
    A: enriched_category C T \<alpha> \<iota> Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A +
    B: enriched_category C T \<alpha> \<iota> Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B
  for C :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"  (infixr \<open>\<cdot>\<close> 55)
  and T :: "'m \<times> 'm \<Rightarrow> 'm"
  and \<alpha> :: "'m \<times> 'm \<times> 'm \<Rightarrow> 'm"
  and \<iota> :: "'m"
  and Obj\<^sub>A :: "'a set"
  and Hom\<^sub>A :: "'a \<Rightarrow> 'a \<Rightarrow> 'm"
  and Id\<^sub>A :: "'a \<Rightarrow> 'm"
  and Comp\<^sub>A :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm"
  and Obj\<^sub>B :: "'b set"
  and Hom\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'm"
  and Id\<^sub>B :: "'b \<Rightarrow> 'm"
  and Comp\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'm"
  and F\<^sub>o :: "'a \<Rightarrow> 'b"
  and F\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'm" +
  assumes extensionality: "a \<notin> Obj\<^sub>A \<or> b \<notin> Obj\<^sub>A \<Longrightarrow> F\<^sub>a a b = null"
  assumes preserves_Obj [intro]: "a \<in> Obj\<^sub>A \<Longrightarrow> F\<^sub>o a \<in> Obj\<^sub>B"
  and preserves_Hom: "\<lbrakk>a \<in> Obj\<^sub>A; b \<in> Obj\<^sub>A\<rbrakk> \<Longrightarrow>
                         \<guillemotleft>F\<^sub>a a b : Hom\<^sub>A a b \<rightarrow> Hom\<^sub>B (F\<^sub>o a) (F\<^sub>o b)\<guillemotright>"
  and preserves_Id: "a \<in> Obj\<^sub>A \<Longrightarrow> F\<^sub>a a a \<cdot> Id\<^sub>A a = Id\<^sub>B (F\<^sub>o a)"
  and preserves_Comp: "\<lbrakk>a \<in> Obj\<^sub>A; b \<in> Obj\<^sub>A; c \<in> Obj\<^sub>A\<rbrakk> \<Longrightarrow>
                          Comp\<^sub>B (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> T (F\<^sub>a b c, F\<^sub>a a b) =
                          F\<^sub>a a c \<cdot> Comp\<^sub>A a b c"

  locale fully_faithful_enriched_functor =
    enriched_functor +
  assumes locally_iso: "\<lbrakk>a \<in> Obj\<^sub>A; b \<in> Obj\<^sub>A\<rbrakk> \<Longrightarrow> iso (F\<^sub>a a b)"

  text\<open>
    A natural transformation from an an enriched functor \<open>F = (F\<^sub>o, F\<^sub>a)\<close> to an
    enriched functor \<open>G = (G\<^sub>o, G\<^sub>a)\<close> consists of a map \<open>\<tau>\<close> that assigns to each
    object \<open>a \<in> Obj\<^sub>A\<close> a ``component at \<open>a\<close>'', which is an arrow \<open>\<tau> a : \<I> \<rightarrow> Hom\<^sub>B (F\<^sub>o a) (G\<^sub>o a)\<close>,
    subject to an equation that expresses the naturality condition.
  \<close>

  locale enriched_natural_transformation =
    monoidal_category C T \<alpha> \<iota> +
    A: enriched_category C T \<alpha> \<iota> Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A +
    B: enriched_category C T \<alpha> \<iota> Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B +
    F: enriched_functor C T \<alpha> \<iota>
         Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B F\<^sub>o F\<^sub>a +
    G: enriched_functor C T \<alpha> \<iota>
         Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B G\<^sub>o G\<^sub>a
  for C :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"  (infixr \<open>\<cdot>\<close> 55)
  and T :: "'m \<times> 'm \<Rightarrow> 'm"
  and \<alpha> :: "'m \<times> 'm \<times> 'm \<Rightarrow> 'm"
  and \<iota> :: "'m"
  and Obj\<^sub>A :: "'a set"
  and Hom\<^sub>A :: "'a \<Rightarrow> 'a \<Rightarrow> 'm"
  and Id\<^sub>A :: "'a \<Rightarrow> 'm"
  and Comp\<^sub>A :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm"
  and Obj\<^sub>B :: "'b set"
  and Hom\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'm"
  and Id\<^sub>B :: "'b \<Rightarrow> 'm"
  and Comp\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'm"
  and F\<^sub>o :: "'a \<Rightarrow> 'b"
  and F\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'm"
  and G\<^sub>o :: "'a \<Rightarrow> 'b"
  and G\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'm"
  and \<tau> :: "'a \<Rightarrow> 'm" +
  assumes extensionality: "a \<notin> Obj\<^sub>A \<Longrightarrow> \<tau> a = null"
  and component_in_hom [intro]: "a \<in> Obj\<^sub>A \<Longrightarrow> \<guillemotleft>\<tau> a : \<I> \<rightarrow> Hom\<^sub>B (F\<^sub>o a) (G\<^sub>o a)\<guillemotright>"
  and naturality: "\<lbrakk>a \<in> Obj\<^sub>A; b \<in> Obj\<^sub>A\<rbrakk> \<Longrightarrow>
                     Comp\<^sub>B (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot> (\<tau> b \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] =
                     Comp\<^sub>B (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> \<tau> a) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"

  subsection "Self-Enrichment"

  context elementary_closed_monoidal_category
  begin

    text \<open>
      Every closed monoidal category \<open>M\<close> admits a structure of enriched category,
      where the exponentials in \<open>M\<close> itself serve as the ``hom-objects''
      (\emph{cf.}~\<^cite>\<open>"kelly-enriched-category"\<close> Section 1.6).
      Essentially all the work in proving this theorem has already been done in
      @{theory EnrichedCategoryBasics.ClosedMonoidalCategory}.
    \<close>

    interpretation closed_monoidal_category
      using is_closed_monoidal_category by blast

    interpretation EC: enriched_category C T \<alpha> \<iota> \<open>Collect ide\<close> exp Id Comp
      using Id_in_hom Comp_in_hom Comp_unit_right Comp_unit_left Comp_assoc\<^sub>E\<^sub>C\<^sub>M\<^sub>C(2)
      by unfold_locales auto

    theorem is_enriched_in_itself:
    shows "enriched_category C T \<alpha> \<iota> (Collect ide) exp Id Comp"
      ..

    text\<open>
      The following mappings define a bijection between \<open>hom a b\<close> and \<open>hom \<I> (exp a b)\<close>.
      These have functorial properties which are encountered repeatedly.
    \<close>

    definition UP  ("_\<^sup>\<up>" [100] 100)
    where "t\<^sup>\<up> \<equiv> if arr t then Curry[\<I>, dom t, cod t] (t \<cdot> \<l>[dom t]) else null"

    definition DN
    where "DN a b t  \<equiv> if arr t then Uncurry[a, b] t \<cdot> \<l>\<^sup>-\<^sup>1[a] else null"

    abbreviation DN'  ("_\<^sup>\<down>[_, _]" [100] 99)
    where "t\<^sup>\<down>[a, b] \<equiv> DN a b t"

    lemma UP_DN:
    shows [intro]: "arr t \<Longrightarrow> \<guillemotleft>t\<^sup>\<up> : \<I> \<rightarrow> exp (dom t) (cod t)\<guillemotright>"
    and [intro]: "\<lbrakk>ide a; ide b; \<guillemotleft>t : \<I> \<rightarrow> exp a b\<guillemotright>\<rbrakk> \<Longrightarrow> \<guillemotleft>t\<^sup>\<down>[a, b]: a \<rightarrow> b\<guillemotright>"
    and [simp]: "arr t \<Longrightarrow> (t\<^sup>\<up>)\<^sup>\<down>[dom t, cod t] = t"
    and [simp]: "\<lbrakk>ide a; ide b; \<guillemotleft>t : \<I> \<rightarrow> exp a b\<guillemotright>\<rbrakk> \<Longrightarrow> (t\<^sup>\<down>[a, b])\<^sup>\<up> = t"
      using UP_def DN_def Uncurry_Curry Curry_Uncurry [of \<I> a b t]
            comp_assoc comp_arr_dom
      by auto

    lemma UP_simps [simp]:
    assumes "arr t"
    shows "arr (t\<^sup>\<up>)" and "dom (t\<^sup>\<up>) = \<I>" and "cod (t\<^sup>\<up>) = exp (dom t) (cod t)"
      using assms UP_DN by auto

    lemma DN_simps [simp]:
    assumes "ide a" and "ide b" and "arr t" and "dom t = \<I>" and "cod t = exp a b"
    shows "arr (t\<^sup>\<down>[a, b])" and "dom (t\<^sup>\<down>[a, b]) = a" and "cod (t\<^sup>\<down>[a, b]) = b"
      using assms UP_DN DN_def by auto

    lemma UP_ide:
    assumes "ide a"
    shows "a\<^sup>\<up> = Id a"
      using assms Id_def comp_cod_arr UP_def by auto

    lemma DN_Id:
    assumes "ide a"
    shows "(Id a)\<^sup>\<down>[a, a] = a"
      using assms Uncurry_Curry lunit_in_hom Id_def DN_def by auto

    lemma UP_comp:
    assumes "seq t u"
    shows "(t \<cdot> u)\<^sup>\<up> = Comp (dom u) (cod u) (cod t) \<cdot> (t\<^sup>\<up> \<otimes> u\<^sup>\<up>) \<cdot> \<iota>\<^sup>-\<^sup>1"
    proof -
      have "Comp (dom u) (cod u) (cod t) \<cdot> (t\<^sup>\<up> \<otimes> u\<^sup>\<up>) \<cdot> \<iota>\<^sup>-\<^sup>1 =
            (Curry[exp (cod u) (cod t) \<otimes> exp (dom u) (cod u), dom u, cod t]
              (eval (cod u) (cod t) \<cdot>
                (exp (cod u) (cod t) \<otimes> eval (dom u) (cod u)) \<cdot>
                   \<a>[exp (cod u) (cod t), exp (dom u) (cod u), dom u]) \<cdot>
                     (t\<^sup>\<up> \<otimes> u\<^sup>\<up>)) \<cdot> \<iota>\<^sup>-\<^sup>1"
        unfolding Comp_def
        using assms comp_assoc by simp
      also have "... =
            (Curry[\<I> \<otimes> \<I>, dom u, cod t]
              ((eval (cod u) (cod t) \<cdot>
                  (exp (cod u) (cod t) \<otimes> eval (dom u) (cod u)) \<cdot>
                     \<a>[exp (cod u) (cod t), exp (dom u) (cod u), dom u]) \<cdot>
                       ((t\<^sup>\<up> \<otimes> u\<^sup>\<up>) \<otimes> dom u))) \<cdot> \<iota>\<^sup>-\<^sup>1"
        using assms
              comp_Curry_arr
                [of "dom u" "t\<^sup>\<up> \<otimes> u\<^sup>\<up>"
                    "\<I> \<otimes> \<I>" "exp (cod u) (cod t) \<otimes> exp (dom u) (cod u)"
                    "eval (cod u) (cod t) \<cdot>
                       (exp (cod u) (cod t) \<otimes> eval (dom u) (cod u)) \<cdot>
                         \<a>[exp (cod u) (cod t), exp (dom u) (cod u), dom u]"
                    "cod t"]
        by fastforce
      also have "... =
            Curry[\<I> \<otimes> \<I>, dom u, cod t]
              (eval (cod u) (cod t) \<cdot>
                 ((exp (cod u) (cod t) \<otimes> eval (dom u) (cod u)) \<cdot>
                    (t\<^sup>\<up> \<otimes> u\<^sup>\<up> \<otimes> dom u)) \<cdot> \<a>[\<I>, \<I>, dom u]) \<cdot> \<iota>\<^sup>-\<^sup>1"
        using assms assoc_naturality [of "t\<^sup>\<up>" "u\<^sup>\<up>" "dom u"] comp_assoc by auto
      also have "... =
            Curry[\<I> \<otimes> \<I>, dom u, cod t]
              (eval (cod u) (cod t) \<cdot>
                 (exp (cod u) (cod t) \<cdot> t\<^sup>\<up> \<otimes> Uncurry[dom u, cod u] (u\<^sup>\<up>)) \<cdot>
                    \<a>[\<I>, \<I>, dom u]) \<cdot> \<iota>\<^sup>-\<^sup>1"
        using assms comp_cod_arr UP_DN interchange by auto
      also have "... =
            Curry[\<I> \<otimes> \<I>, dom u, cod t]
              (eval (cod u) (cod t) \<cdot>
                 (exp (cod u) (cod t) \<cdot> t\<^sup>\<up> \<otimes> u \<cdot> \<l>[dom u]) \<cdot>
                    \<a>[\<I>, \<I>, dom u]) \<cdot> \<iota>\<^sup>-\<^sup>1"
        using assms Uncurry_Curry UP_def by auto
      also have "... =
            Curry[\<I> \<otimes> \<I>, dom u, cod t]
              (eval (cod u) (cod t) \<cdot>
                 (t\<^sup>\<up> \<otimes> u \<cdot> \<l>[dom u]) \<cdot> \<a>[\<I>, \<I>, dom u]) \<cdot> \<iota>\<^sup>-\<^sup>1"
        using assms comp_cod_arr by auto
      also have "... =
            Curry[\<I> \<otimes> \<I>, dom u, cod t]
              (eval (cod u) (cod t) \<cdot>
                ((t\<^sup>\<up> \<otimes> cod u) \<cdot> (\<I> \<otimes> u \<cdot> \<l>[dom u])) \<cdot>
                  \<a>[\<I>, \<I>, dom u]) \<cdot> \<iota>\<^sup>-\<^sup>1"
        using assms comp_arr_dom [of "t\<^sup>\<up>" \<I>] comp_cod_arr [of "u \<cdot> \<l>[dom u]" "cod u"]
              interchange [of "t\<^sup>\<up>"  \<I> "cod u" "u \<cdot> \<l>[dom u]"]
        by auto
      also have "... =
            Curry[\<I>, dom u, cod t]
              ((eval (cod u) (cod t) \<cdot>
                 ((t\<^sup>\<up> \<otimes> cod u) \<cdot> (\<I> \<otimes> u \<cdot> \<l>[dom u])) \<cdot>
                    \<a>[\<I>, \<I>, dom u]) \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> dom u))"
      proof -
        have "\<guillemotleft>\<iota>\<^sup>-\<^sup>1 : \<I> \<rightarrow> \<I> \<otimes> \<I>\<guillemotright>"
          using inv_in_hom unit_is_iso by blast
        thus ?thesis
          using assms comp_Curry_arr by fastforce
      qed
      also have "... =
            Curry[\<I>, dom u, cod t]
              ((Uncurry[cod u, cod t] (t\<^sup>\<up>)) \<cdot> (\<I> \<otimes> u \<cdot> \<l>[dom u]) \<cdot>
                  \<a>[\<I>, \<I>, dom u] \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> dom u))"
        using comp_assoc by simp
      also have "... = Curry[\<I>, dom u, cod t] (Uncurry[cod u, cod t] (t\<^sup>\<up>) \<cdot> (\<I> \<otimes> u))"
      proof -
        have "(\<I> \<otimes> u \<cdot> \<l>[dom u]) \<cdot> \<a>[\<I>, \<I>, dom u] \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> dom u) =
              ((\<I> \<otimes> u) \<cdot> (\<I> \<otimes> \<l>[dom u])) \<cdot> \<a>[\<I>, \<I>, dom u] \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> dom u)"
          using assms by auto
        also have "... = (\<I> \<otimes> u) \<cdot> (\<I> \<otimes> \<l>[dom u]) \<cdot> \<a>[\<I>, \<I>, dom u] \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> dom u)"
          using comp_assoc by simp
        also have "... = (\<I> \<otimes> u) \<cdot> (\<I> \<otimes> \<l>[dom u]) \<cdot> (\<I> \<otimes> \<l>\<^sup>-\<^sup>1[dom u])"
        proof -
          have "\<a>[\<I>, \<I>, dom u] \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> dom u) = \<I> \<otimes> \<l>\<^sup>-\<^sup>1[dom u]"
          proof -
            have "\<a>[\<I>, \<I>, dom u] \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> dom u) =
                  inv ((\<iota> \<otimes> dom u) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, dom u])"
              using assms inv_inv inv_comp [of "\<a>\<^sup>-\<^sup>1[\<I>, \<I>, dom u]" "\<iota> \<otimes> dom u"]
                   inv_tensor [of \<iota> "dom u"]
              by (metis ide_dom ide_is_iso ide_unity inv_ide iso_assoc iso_inv_iso
                  iso_is_arr lunit_char(2) seqE tensor_preserves_iso triangle
                  unit_is_iso unitor_coincidence(2))
            also have "... = inv (\<I> \<otimes> \<l>[dom u])"
              using assms lunit_char [of "dom u"] by auto
            also have "... = \<I> \<otimes> \<l>\<^sup>-\<^sup>1[dom u]"
              using assms inv_tensor by auto
            finally show ?thesis by blast
          qed
          thus ?thesis by simp
        qed
        also have "... = (\<I> \<otimes> u) \<cdot> (\<I> \<otimes> dom u)"
          using assms
          by (metis comp_ide_self comp_lunit_lunit'(1) dom_comp ideD(1)
              ide_dom ide_unity interchange)
        also have "... = \<I> \<otimes> u"
          using assms by blast
        finally have "(\<I> \<otimes> u \<cdot> \<l>[dom u]) \<cdot> \<a>[\<I>, \<I>, dom u] \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> dom u) = \<I> \<otimes> u"
          by blast
        thus ?thesis by argo
      qed
      also have "... = Curry[\<I>, dom u, cod t] ((t \<cdot> \<l>[cod u]) \<cdot> (\<I> \<otimes> u))"
        using assms Uncurry_Curry UP_def by auto
      also have "... = Curry[\<I>, dom u, cod t] (t \<cdot> u \<cdot> \<l>[dom u])"
        using assms comp_assoc lunit_naturality by auto
      also have "... = (t \<cdot> u)\<^sup>\<up>"
        using assms comp_assoc UP_def by simp
      finally show ?thesis by simp
    qed

  end

  section "Underlying Category, Functor, and Natural Transformation"

  subsection "Underlying Category"

  text\<open>
     The underlying category (\emph{cf.}~\<^cite>\<open>"kelly-enriched-category"\<close> Section 1.3)
     of an enriched category has as its arrows from \<open>a\<close> to \<open>b\<close> the arrows \<open>\<I> \<rightarrow> Hom a b\<close> of \<open>M\<close>
     (\emph{i.e.}~the points of \<open>Hom a b\<close>). The identity at \<open>a\<close> is \<open>Id a\<close>.  The composition of
     arrows \<open>f\<close> and \<open>g\<close> is given by the formula: \<open>Comp a b c \<cdot> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1\<close>.
  \<close>

  locale underlying_category =
    M: monoidal_category +
    A: enriched_category
  begin

    sublocale concrete_category Obj \<open>\<lambda>a b. M.hom \<I> (Hom a b)\<close> \<open>Id\<close>
                \<open>\<lambda>c b a g f. Comp a b c \<cdot> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1\<close>
    proof
      show "\<And>a. a \<in> Obj \<Longrightarrow> Id a \<in> M.hom \<I> (Hom a a)"
        using A.Id_in_hom by blast
      show 1: "\<And>a b c f g.
                 \<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj;
                  f \<in> M.hom \<I> (Hom a b); g \<in> M.hom \<I> (Hom b c)\<rbrakk>
                     \<Longrightarrow> Comp a b c \<cdot> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1 \<in> M.hom \<I> (Hom a c)"
        using A.Comp_in_hom M.inv_in_hom M.unit_is_iso M.comp_in_homI
              M.unit_in_hom
        apply auto[1]
        apply (intro M.comp_in_homI)
        by auto
      show "\<And>a b f. \<lbrakk>a \<in> Obj; b \<in> Obj; f \<in> M.hom \<I> (Hom a b)\<rbrakk>
                       \<Longrightarrow> Comp a a b \<cdot> (f \<otimes> Id a) \<cdot> \<iota>\<^sup>-\<^sup>1 = f"
      proof -
        fix a b f
        assume a: "a \<in> Obj" and b: "b \<in> Obj" and f: "f \<in> M.hom \<I> (Hom a b)"
        show "Comp a a b \<cdot> (f \<otimes> Id a) \<cdot> \<iota>\<^sup>-\<^sup>1 = f"
        proof -
          have "Comp a a b \<cdot> (f \<otimes> Id a) \<cdot> \<iota>\<^sup>-\<^sup>1 = (Comp a a b \<cdot> (f \<otimes> Id a)) \<cdot> \<iota>\<^sup>-\<^sup>1"
            using M.comp_assoc by simp
          also have "... = (Comp a a b \<cdot> (Hom a b \<otimes> Id a) \<cdot> (f \<otimes> \<I>)) \<cdot> \<iota>\<^sup>-\<^sup>1"
            using a f M.comp_arr_dom M.comp_cod_arr A.Id_in_hom
                  M.in_homE M.interchange mem_Collect_eq
            by metis
          also have "... = (\<r>[Hom a b] \<cdot> (f \<otimes> \<I>)) \<cdot> \<iota>\<^sup>-\<^sup>1"
            using a b f A.Comp_Hom_Id M.comp_assoc by metis
          also have "... = (f \<cdot> \<r>[\<I>]) \<cdot> \<iota>\<^sup>-\<^sup>1"
            using f M.runit_naturality by fastforce
          also have "... = f \<cdot> \<iota> \<cdot> \<iota>\<^sup>-\<^sup>1"
            by (simp add: M.unitor_coincidence(2) M.comp_assoc)
          also have "... = f"
            using f M.comp_arr_dom M.comp_arr_inv' M.unit_is_iso by auto
          finally show "Comp a a b \<cdot> (f \<otimes> Id a) \<cdot> \<iota>\<^sup>-\<^sup>1 = f" by blast
        qed
      qed
      show "\<And>a b f. \<lbrakk>a \<in> Obj; b \<in> Obj; f \<in> M.hom \<I> (Hom a b)\<rbrakk>
                       \<Longrightarrow> Comp a b b \<cdot> (Id b \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1 = f"
      proof -
        fix a b f
        assume a: "a \<in> Obj" and b: "b \<in> Obj" and f: "f \<in> M.hom \<I> (Hom a b)"
        show "Comp a b b \<cdot> (Id b \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1 = f"
        proof -
          have "Comp a b b \<cdot> (Id b \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1 = (Comp a b b \<cdot> (Id b \<otimes> f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
            using M.comp_assoc by simp
          also have "... = (Comp a b b \<cdot> (Id b \<otimes> Hom a b) \<cdot> (\<I> \<otimes> f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
            using a b f M.comp_arr_dom M.comp_cod_arr A.Id_in_hom
                  M.in_homE M.interchange mem_Collect_eq
            by metis
          also have "... = (\<l>[Hom a b] \<cdot> (\<I> \<otimes> f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
            using a b A.Comp_Id_Hom M.comp_assoc by metis
          also have "... = (f \<cdot> \<l>[\<I>]) \<cdot> \<iota>\<^sup>-\<^sup>1"
            using a b f M.lunit_naturality [of f] by auto
          also have "... = f \<cdot> \<iota> \<cdot> \<iota>\<^sup>-\<^sup>1"
            by (simp add: M.unitor_coincidence(1) M.comp_assoc)
          also have "... = f"
            using M.comp_arr_dom M.comp_arr_inv' M.unit_is_iso f by auto
          finally show "Comp a b b \<cdot> (Id b \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1 = f" by blast
        qed
      qed
      show "\<And>a b c d f g h.
                \<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj; d \<in> Obj;
                 f \<in> M.hom \<I> (Hom a b); g \<in> M.hom \<I> (Hom b c);
                 h \<in> M.hom \<I> (Hom c d)\<rbrakk>
                    \<Longrightarrow> Comp a c d \<cdot> (h \<otimes> Comp a b c \<cdot> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1) \<cdot> \<iota>\<^sup>-\<^sup>1 =
                        Comp a b d \<cdot> (Comp b c d \<cdot> (h \<otimes> g) \<cdot> \<iota>\<^sup>-\<^sup>1 \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1"
      proof -
        fix a b c d f g h
        assume a: "a \<in> Obj" and b: "b \<in> Obj" and c: "c \<in> Obj" and d: "d \<in> Obj"
        assume f: "f \<in> M.hom \<I> (Hom a b)" and g: "g \<in> M.hom \<I> (Hom b c)"
        and h: "h \<in> M.hom \<I> (Hom c d)"
        have "Comp a c d \<cdot> (h \<otimes> Comp a b c \<cdot> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1) \<cdot> \<iota>\<^sup>-\<^sup>1 =
              Comp a c d \<cdot>
                ((Hom c d \<otimes> Comp a b c) \<cdot> (h \<otimes> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1)) \<cdot> \<iota>\<^sup>-\<^sup>1"
          using a b c d f g h 1 M.interchange A.ide_Hom M.comp_ide_arr M.comp_cod_arr
                M.in_homE mem_Collect_eq
          by metis
        also have "... = Comp a c d \<cdot>
                           ((Hom c d \<otimes> Comp a b c) \<cdot>
                               (\<a>[Hom c d, Hom b c, Hom a b] \<cdot>
                                  \<a>\<^sup>-\<^sup>1[Hom c d, Hom b c, Hom a b])) \<cdot>
                                 (h \<otimes> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1) \<cdot> \<iota>\<^sup>-\<^sup>1"
        proof -
          have "(Hom c d \<otimes> Comp a b c) \<cdot>
                  (\<a>[Hom c d, Hom b c, Hom a b] \<cdot>
                     \<a>\<^sup>-\<^sup>1[Hom c d, Hom b c, Hom a b]) =
                Hom c d \<otimes> Comp a b c"
            using a b c d
            by (metis A.Comp_in_hom A.ide_Hom M.comp_arr_ide
                M.comp_assoc_assoc'(1) M.ide_in_hom M.interchange M.seqI'
                M.tensor_preserves_ide)
          thus ?thesis
            using M.comp_assoc by force
        qed
        also have "... = (Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                           \<a>[Hom c d, Hom b c, Hom a b]) \<cdot>
                             (\<a>\<^sup>-\<^sup>1[Hom c d, Hom b c, Hom a b] \<cdot>
                               (h \<otimes> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1)) \<cdot>
                                 \<iota>\<^sup>-\<^sup>1"
          using M.comp_assoc by auto
        also have "... = (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b)) \<cdot>
                           (\<a>\<^sup>-\<^sup>1[Hom c d, Hom b c, Hom a b] \<cdot> (h \<otimes> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1)) \<cdot> \<iota>\<^sup>-\<^sup>1"
          using a b c d A.Comp_assoc by auto
        also have "... = (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b)) \<cdot>
                           (\<a>\<^sup>-\<^sup>1[Hom c d, Hom b c, Hom a b] \<cdot> (h \<otimes> (g \<otimes> f))) \<cdot>
                             (\<I> \<otimes> \<iota>\<^sup>-\<^sup>1) \<cdot> \<iota>\<^sup>-\<^sup>1"
        proof -
          have "h \<otimes> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1 = (h \<otimes> (g \<otimes> f)) \<cdot> (\<I> \<otimes> \<iota>\<^sup>-\<^sup>1)"
          proof -
            have "M.seq h \<I>"
              using h by auto
            moreover have "M.seq (g \<otimes> f) \<iota>\<^sup>-\<^sup>1"
              using f g M.inv_in_hom M.unit_is_iso by blast
            ultimately show ?thesis
              using a b c d f g h M.interchange M.comp_arr_ide M.ide_unity by metis
          qed
          thus ?thesis
            using M.comp_assoc by simp
        qed
        also have "... = (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b)) \<cdot>
                           ((h \<otimes> g) \<otimes> f) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>] \<cdot> (\<I> \<otimes> \<iota>\<^sup>-\<^sup>1) \<cdot> \<iota>\<^sup>-\<^sup>1"
          using f g h M.assoc'_naturality
          by (metis M.comp_assoc M.in_homE mem_Collect_eq)
        also have "... = (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b)) \<cdot>
                           (((h \<otimes> g) \<otimes> f) \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> \<I>)) \<cdot> \<iota>\<^sup>-\<^sup>1"
        proof -
          have "\<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>] \<cdot> (\<I> \<otimes> \<iota>\<^sup>-\<^sup>1) \<cdot> \<iota>\<^sup>-\<^sup>1 = (\<iota>\<^sup>-\<^sup>1 \<otimes> \<I>) \<cdot> \<iota>\<^sup>-\<^sup>1"
            using M.unitor_coincidence
            by (metis (full_types) M.L.preserves_inv M.L.preserves_iso
                M.R.preserves_inv M.arrI M.arr_tensor M.comp_assoc M.ideD(1)
                M.ide_unity M.inv_comp M.iso_assoc M.unit_in_hom_ax
                M.unit_is_iso M.unit_triangle(1))
          thus ?thesis
            using M.comp_assoc by simp
        qed
        also have "... = Comp a b d \<cdot>
                           ((Comp b c d \<otimes> Hom a b) \<cdot> ((h \<otimes> g) \<cdot> \<iota>\<^sup>-\<^sup>1 \<otimes> f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
        proof -
          have "((h \<otimes> g) \<otimes> f) \<cdot> (\<iota>\<^sup>-\<^sup>1 \<otimes> \<I>) = (h \<otimes> g) \<cdot> \<iota>\<^sup>-\<^sup>1 \<otimes> f"
          proof -
            have "M.seq (h \<otimes> g) \<iota>\<^sup>-\<^sup>1"
              using g h M.inv_in_hom M.unit_is_iso by blast
            moreover have "M.seq f \<I>"
              using M.ide_in_hom M.ide_unity f by blast
            ultimately show ?thesis
              using f g h M.interchange M.comp_arr_ide M.ide_unity by metis
          qed
          thus ?thesis
            using M.comp_assoc by auto
        qed
        also have "... = Comp a b d \<cdot> (Comp b c d \<cdot> (h \<otimes> g) \<cdot> \<iota>\<^sup>-\<^sup>1 \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1"
           using b c d f g h 1 M.in_homE mem_Collect_eq M.comp_cod_arr
                 M.interchange A.ide_Hom M.comp_ide_arr
           by metis
        finally show "Comp a c d \<cdot> (h \<otimes> Comp a b c \<cdot> (g \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1) \<cdot> \<iota>\<^sup>-\<^sup>1 =
                      Comp a b d \<cdot> (Comp b c d \<cdot> (h \<otimes> g) \<cdot> \<iota>\<^sup>-\<^sup>1 \<otimes> f) \<cdot> \<iota>\<^sup>-\<^sup>1"
          by blast
      qed
    qed

    abbreviation comp  (infixr "\<cdot>\<^sub>0" 55)
    where "comp \<equiv> COMP"

    lemma hom_char:
    assumes "a \<in> Obj" and "b \<in> Obj"
    shows "hom (MkIde a) (MkIde b) = MkArr a b ` M.hom \<I> (Hom a b)"
    proof
      show "hom (MkIde a) (MkIde b) \<subseteq> MkArr a b ` M.hom \<I> (Hom a b)"
      proof
        fix t
        assume t: "t \<in> hom (MkIde a) (MkIde b)"
        have "t = MkArr a b (Map t)"
          using t MkArr_Map dom_char cod_char by fastforce
        moreover have "Map t \<in> M.hom \<I> (Hom a b)"
          using t arr_char dom_char cod_char by fastforce
        ultimately show "t \<in> MkArr a b ` M.hom \<I> (Hom a b)" by simp
      qed
      show "MkArr a b ` M.hom \<I> (Hom a b) \<subseteq> hom (MkIde a) (MkIde b)"
        using assms MkArr_in_hom by blast
    qed

  end

  subsection "Underlying Functor"

  text\<open>
     The underlying functor of an enriched functor \<open>F : A \<longrightarrow> B\<close>
     takes an arrow \<open>\<guillemotleft>f : a \<rightarrow> a'\<guillemotright>\<close> of the underlying category \<open>A\<^sub>0\<close>
     (\emph{i.e.}~an arrow \<open>\<guillemotleft>\<I> \<rightarrow> Hom a a'\<guillemotright>\<close> of \<open>M\<close>)
     to the arrow \<open>\<guillemotleft>F\<^sub>a a a' \<cdot> f : F\<^sub>o a \<rightarrow> F\<^sub>o a'\<guillemotright>\<close> of \<open>B\<^sub>0\<close>
     (\emph{i.e.} the arrow \<open>\<guillemotleft>F\<^sub>a a a' \<cdot> f : \<I> \<rightarrow> Hom (F\<^sub>o a) (F\<^sub>o a')\<guillemotright>\<close> of \<open>M\<close>).
  \<close>

  locale underlying_functor =
    enriched_functor
  begin

    sublocale A\<^sub>0: underlying_category C T \<alpha> \<iota> Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A ..
    sublocale B\<^sub>0: underlying_category C T \<alpha> \<iota> Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B ..

    notation A\<^sub>0.comp  (infixr "\<cdot>\<^sub>A\<^sub>0" 55)
    notation B\<^sub>0.comp  (infixr "\<cdot>\<^sub>B\<^sub>0" 55)

    definition map\<^sub>0
    where "map\<^sub>0 f = (if A\<^sub>0.arr f
                     then B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Cod f))
                            (F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f)
                     else B\<^sub>0.null)"

    sublocale "functor" A\<^sub>0.comp B\<^sub>0.comp map\<^sub>0
    proof
      fix f
      show "\<not> A\<^sub>0.arr f \<Longrightarrow> map\<^sub>0 f = B\<^sub>0.null"
        using map\<^sub>0_def by simp
      show 1: "\<And>f. A\<^sub>0.arr f \<Longrightarrow> B\<^sub>0.arr (map\<^sub>0 f)"
      proof -
        fix f
        assume f: "A\<^sub>0.arr f"
        have "B\<^sub>0.arr (B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Cod f))
                     (F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f))"
          using f preserves_Hom A\<^sub>0.Dom_in_Obj A\<^sub>0.Cod_in_Obj A\<^sub>0.arrE
          by (metis (mono_tags, lifting) B\<^sub>0.arr_MkArr comp_in_homI
              mem_Collect_eq preserves_Obj)
        thus "B\<^sub>0.arr (map\<^sub>0 f)"
          using f map\<^sub>0_def by simp
      qed
      show "A\<^sub>0.arr f \<Longrightarrow> B\<^sub>0.dom (map\<^sub>0 f) = map\<^sub>0 (A\<^sub>0.dom f)"
        using 1 A\<^sub>0.dom_char B\<^sub>0.dom_char preserves_Id A\<^sub>0.arr_dom_iff_arr
              map\<^sub>0_def A\<^sub>0.Dom_in_Obj
        by auto
      show "A\<^sub>0.arr f \<Longrightarrow> B\<^sub>0.cod (map\<^sub>0 f) = map\<^sub>0 (A\<^sub>0.cod f)"
        using 1 A\<^sub>0.cod_char B\<^sub>0.cod_char preserves_Id A\<^sub>0.arr_cod_iff_arr
              map\<^sub>0_def A\<^sub>0.Cod_in_Obj
        by auto
      fix g
      assume fg: "A\<^sub>0.seq g f"
      show "map\<^sub>0 (g \<cdot>\<^sub>A\<^sub>0 f) = map\<^sub>0 g \<cdot>\<^sub>B\<^sub>0 map\<^sub>0 f"
      proof -
        have "B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom (g \<cdot>\<^sub>A\<^sub>0 f))) (F\<^sub>o (B\<^sub>0.Cod (g \<cdot>\<^sub>A\<^sub>0 f)))
                       (F\<^sub>a (A\<^sub>0.Dom (g \<cdot>\<^sub>A\<^sub>0 f))
                       (B\<^sub>0.Cod (g \<cdot>\<^sub>A\<^sub>0 f)) \<cdot> B\<^sub>0.Map (g \<cdot>\<^sub>A\<^sub>0 f)) =
              B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom g)) (F\<^sub>o (B\<^sub>0.Cod g))
                       (F\<^sub>a (A\<^sub>0.Dom g) (B\<^sub>0.Cod g) \<cdot> B\<^sub>0.Map g) \<cdot>\<^sub>B\<^sub>0
                B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (B\<^sub>0.Cod f))
                         (F\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f) \<cdot> B\<^sub>0.Map f)"
        proof -
          have 2: "B\<^sub>0.arr (B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Dom g))
                          (F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f))"
            using fg 1 A\<^sub>0.seq_char map\<^sub>0_def by auto
          have 3: "B\<^sub>0.arr (B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom g)) (F\<^sub>o (A\<^sub>0.Cod g))
                          (F\<^sub>a (A\<^sub>0.Dom g) (A\<^sub>0.Cod g) \<cdot> A\<^sub>0.Map g))"
            using fg 1 A\<^sub>0.seq_char map\<^sub>0_def by metis
          have "B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom g)) (F\<^sub>o (B\<^sub>0.Cod g))
                         (F\<^sub>a (A\<^sub>0.Dom g) (B\<^sub>0.Cod g) \<cdot> B\<^sub>0.Map g) \<cdot>\<^sub>B\<^sub>0
                  B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (B\<^sub>0.Cod f))
                           (F\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f) \<cdot> B\<^sub>0.Map f) =
                B\<^sub>0.MkArr (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Cod g))
                         (Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Dom g)) (F\<^sub>o (A\<^sub>0.Cod g)) \<cdot>
                            (F\<^sub>a (A\<^sub>0.Dom g) (A\<^sub>0.Cod g) \<cdot> A\<^sub>0.Map g \<otimes>
                             F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f) \<cdot>
                               \<iota>\<^sup>-\<^sup>1)"
            using fg 2 3 A\<^sub>0.seq_char B\<^sub>0.comp_MkArr by simp
          moreover
          have "Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Dom g)) (F\<^sub>o (A\<^sub>0.Cod g)) \<cdot>
                      (F\<^sub>a (A\<^sub>0.Dom g) (A\<^sub>0.Cod g) \<cdot> A\<^sub>0.Map g \<otimes>
                       F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1 =
                F\<^sub>a (A\<^sub>0.Dom (g \<cdot>\<^sub>A\<^sub>0 f)) (B\<^sub>0.Cod (g \<cdot>\<^sub>A\<^sub>0 f)) \<cdot> B\<^sub>0.Map (g \<cdot>\<^sub>A\<^sub>0 f)"
          proof -
            have "Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Dom g)) (F\<^sub>o (A\<^sub>0.Cod g)) \<cdot>
                           (F\<^sub>a (A\<^sub>0.Dom g) (A\<^sub>0.Cod g) \<cdot> A\<^sub>0.Map g \<otimes>
                            F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1 =
                  Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Dom g)) (F\<^sub>o (A\<^sub>0.Cod g)) \<cdot>
                           ((F\<^sub>a (A\<^sub>0.Dom g) (A\<^sub>0.Cod g) \<otimes> F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f)) \<cdot>
                            (A\<^sub>0.Map g \<otimes> A\<^sub>0.Map f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
              using fg preserves_Hom
                    interchange [of "F\<^sub>a (A\<^sub>0.Dom g) (A\<^sub>0.Cod g)" "A\<^sub>0.Map g"
                                    "F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f)" "A\<^sub>0.Map f"]
              by (metis A\<^sub>0.arrE A\<^sub>0.seqE seqI' mem_Collect_eq)
            also have "... =
                  (Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Dom g)) (F\<^sub>o (A\<^sub>0.Cod g)) \<cdot>
                           (F\<^sub>a (A\<^sub>0.Dom g) (A\<^sub>0.Cod g) \<otimes> F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f))) \<cdot>
                    (A\<^sub>0.Map g \<otimes> A\<^sub>0.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1"
              using comp_assoc by auto
           also have "... = (F\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod g) \<cdot>
                               Comp\<^sub>A (A\<^sub>0.Dom f) (A\<^sub>0.Dom g) (B\<^sub>0.Cod g)) \<cdot>
                               (A\<^sub>0.Map g \<otimes> A\<^sub>0.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1"
              using fg A\<^sub>0.seq_char preserves_Comp A\<^sub>0.Dom_in_Obj A\<^sub>0.Cod_in_Obj
              by auto
           also have "... = F\<^sub>a (A\<^sub>0.Dom (g \<cdot>\<^sub>A\<^sub>0 f)) (B\<^sub>0.Cod (g \<cdot>\<^sub>A\<^sub>0 f)) \<cdot>
                              Comp\<^sub>A (A\<^sub>0.Dom f) (A\<^sub>0.Dom g) (B\<^sub>0.Cod g) \<cdot>
                                (A\<^sub>0.Map g \<otimes> A\<^sub>0.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1"
             using fg comp_assoc A\<^sub>0.seq_char by simp
           also have "... = F\<^sub>a (A\<^sub>0.Dom (g \<cdot>\<^sub>A\<^sub>0 f)) (B\<^sub>0.Cod (g \<cdot>\<^sub>A\<^sub>0 f)) \<cdot>
                              B\<^sub>0.Map (g \<cdot>\<^sub>A\<^sub>0 f)"
             using A\<^sub>0.Map_comp A\<^sub>0.seq_char fg by presburger
           finally show ?thesis by blast
          qed
          ultimately show ?thesis
            using A\<^sub>0.seq_char fg by auto
        qed
        thus ?thesis
          using fg map\<^sub>0_def B\<^sub>0.comp_MkArr by auto
      qed
    qed

    proposition is_functor:
    shows "functor A\<^sub>0.comp B\<^sub>0.comp map\<^sub>0"
      ..

  end

  subsection "Underlying Natural Transformation"

  text\<open>
    The natural transformation underlying an enriched natural transformation \<open>\<tau>\<close>
    has components that are essentially those of \<open>\<tau>\<close>, except that we have to bother
    ourselves about coercions between types.
  \<close>

  locale underlying_natural_transformation =
    enriched_natural_transformation
  begin

    sublocale A\<^sub>0: underlying_category C T \<alpha> \<iota> Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A ..
    sublocale B\<^sub>0: underlying_category C T \<alpha> \<iota> Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B ..
    sublocale F\<^sub>0: underlying_functor C T \<alpha> \<iota>
                    Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B F\<^sub>o F\<^sub>a ..
    sublocale G\<^sub>0: underlying_functor C T \<alpha> \<iota>
                    Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B G\<^sub>o G\<^sub>a ..

    definition map\<^sub>o\<^sub>b\<^sub>j
    where "map\<^sub>o\<^sub>b\<^sub>j a \<equiv>
           B\<^sub>0.MkArr (B\<^sub>0.Dom (F\<^sub>0.map\<^sub>0 a)) (B\<^sub>0.Dom (G\<^sub>0.map\<^sub>0 a))
             (\<tau> (A\<^sub>0.Dom a))"  

    sublocale \<tau>: NaturalTransformation.transformation_by_components
                   A\<^sub>0.comp B\<^sub>0.comp F\<^sub>0.map\<^sub>0 G\<^sub>0.map\<^sub>0 map\<^sub>o\<^sub>b\<^sub>j
    proof
      show "\<And>a. A\<^sub>0.ide a \<Longrightarrow> B\<^sub>0.in_hom (map\<^sub>o\<^sub>b\<^sub>j a) (F\<^sub>0.map\<^sub>0 a) (G\<^sub>0.map\<^sub>0 a)"
        unfolding map\<^sub>o\<^sub>b\<^sub>j_def
        using A\<^sub>0.Dom_in_Obj B\<^sub>0.ide_char\<^sub>C\<^sub>C F\<^sub>0.map\<^sub>0_def G\<^sub>0.map\<^sub>0_def
              F\<^sub>0.preserves_ide G\<^sub>0.preserves_ide component_in_hom
        by auto
      show "\<And>f. A\<^sub>0.arr f \<Longrightarrow>
                  map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.cod f) \<cdot>\<^sub>B\<^sub>0 F\<^sub>0.map\<^sub>0 f =
                  G\<^sub>0.map\<^sub>0 f \<cdot>\<^sub>B\<^sub>0 map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.dom f)"
      proof -
        fix f
        assume f: "A\<^sub>0.arr f"
        show "map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.cod f) \<cdot>\<^sub>B\<^sub>0 F\<^sub>0.map\<^sub>0 f =
              G\<^sub>0.map\<^sub>0 f \<cdot>\<^sub>B\<^sub>0 map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.dom f)"
        proof (intro B\<^sub>0.arr_eqI)
          show 1: "B\<^sub>0.seq (map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.cod f)) (F\<^sub>0.map\<^sub>0 f)"
            using A\<^sub>0.ide_cod
                  \<open>\<And>a. A\<^sub>0.ide a \<Longrightarrow>
                          B\<^sub>0.in_hom (map\<^sub>o\<^sub>b\<^sub>j a) (F\<^sub>0.map\<^sub>0 a) (G\<^sub>0.map\<^sub>0 a)\<close> f
            by blast
          show 2: "B\<^sub>0.seq (G\<^sub>0.map\<^sub>0 f) (map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.dom f))"
            using A\<^sub>0.ide_dom
                  \<open>\<And>a. A\<^sub>0.ide a \<Longrightarrow>
                          B\<^sub>0.in_hom (map\<^sub>o\<^sub>b\<^sub>j a) (F\<^sub>0.map\<^sub>0 a) (G\<^sub>0.map\<^sub>0 a)\<close> f
            by blast
          show "B\<^sub>0.Dom (map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.cod f) \<cdot>\<^sub>B\<^sub>0 F\<^sub>0.map\<^sub>0 f) =
                B\<^sub>0.Dom (G\<^sub>0.map\<^sub>0 f \<cdot>\<^sub>B\<^sub>0 map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.dom f))"
            using f 1 2 B\<^sub>0.comp_char [of "map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.cod f)" "F\<^sub>0.map\<^sub>0 f"]
                  B\<^sub>0.comp_char [of "G\<^sub>0.map\<^sub>0 f" "map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.dom f)"]
                  F\<^sub>0.map\<^sub>0_def G\<^sub>0.map\<^sub>0_def map\<^sub>o\<^sub>b\<^sub>j_def
            by simp
          show "B\<^sub>0.Cod (map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.cod f) \<cdot>\<^sub>B\<^sub>0 F\<^sub>0.map\<^sub>0 f) =
                B\<^sub>0.Cod (G\<^sub>0.map\<^sub>0 f \<cdot>\<^sub>B\<^sub>0 map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.dom f))"
            using f 1 2 B\<^sub>0.comp_char [of "map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.cod f)" "F\<^sub>0.map\<^sub>0 f"]
                  B\<^sub>0.comp_char [of "G\<^sub>0.map\<^sub>0 f" "map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.dom f)"]
                  F\<^sub>0.map\<^sub>0_def G\<^sub>0.map\<^sub>0_def map\<^sub>o\<^sub>b\<^sub>j_def
            by simp
          show "B\<^sub>0.Map (map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.cod f) \<cdot>\<^sub>B\<^sub>0 F\<^sub>0.map\<^sub>0 f) =
                B\<^sub>0.Map (G\<^sub>0.map\<^sub>0 f \<cdot>\<^sub>B\<^sub>0 map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.dom f))"
          proof -
            have "Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Cod f)) (G\<^sub>o (A\<^sub>0.Cod f)) \<cdot>
                    (\<tau> (A\<^sub>0.Cod f) \<otimes> F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1 =
                  Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (A\<^sub>0.Cod f)) \<cdot>
                    (G\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f \<otimes> \<tau> (A\<^sub>0.Dom f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
            proof -
              have "Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Cod f)) (G\<^sub>o (A\<^sub>0.Cod f)) \<cdot>
                      (\<tau> (A\<^sub>0.Cod f) \<otimes> F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1 =
                    Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Cod f)) (G\<^sub>o (A\<^sub>0.Cod f)) \<cdot>
                      ((\<tau> (A\<^sub>0.Cod f) \<otimes> F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f)) \<cdot> (\<I> \<otimes> A\<^sub>0.Map f)) \<cdot>
                         \<iota>\<^sup>-\<^sup>1"
              proof -
                have "\<tau> (A\<^sub>0.Cod f) \<otimes> F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f =
                      (\<tau> (A\<^sub>0.Cod f) \<otimes> F\<^sub>a (A\<^sub>0.Dom f) (A\<^sub>0.Cod f)) \<cdot> (\<I> \<otimes> A\<^sub>0.Map f)"
                proof -
                  have "seq (\<tau> (A\<^sub>0.Cod f)) \<I>"
                    using f seqI component_in_hom
                    by (metis (no_types, lifting) A\<^sub>0.Cod_in_Obj ide_char
                        ide_unity in_homE)
                  moreover have "seq (F\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)) (B\<^sub>0.Map f)"
                    using f A\<^sub>0.Map_in_Hom A\<^sub>0.Cod_in_Obj A\<^sub>0.Dom_in_Obj
                          F.preserves_Hom in_homE
                    by blast
                  ultimately show ?thesis
                    using f component_in_hom interchange comp_arr_dom by auto
                qed
                thus ?thesis by simp
              qed
              also have "... =
                    Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (A\<^sub>0.Cod f)) (G\<^sub>o (A\<^sub>0.Cod f)) \<cdot>
                      ((\<tau> (B\<^sub>0.Cod f) \<otimes> F\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)) \<cdot>
                         (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)] \<cdot>
                            \<l>[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)]) \<cdot>
                           (\<I> \<otimes> B\<^sub>0.Map f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
              proof -
                have "(\<l>\<^sup>-\<^sup>1[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)] \<cdot>
                         \<l>[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)]) \<cdot>
                        (\<I> \<otimes> B\<^sub>0.Map f) =
                      \<I> \<otimes> B\<^sub>0.Map f"
                  using f comp_lunit_lunit'(2)
                  by (metis (no_types, lifting) A.ide_Hom A\<^sub>0.arrE comp_cod_arr
                      comp_ide_self ideD(1) ide_unity interchange in_homE
                      mem_Collect_eq)
                thus ?thesis by simp
              qed
              also have "... =
                    (Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (F\<^sub>o (B\<^sub>0.Cod f)) (G\<^sub>o (B\<^sub>0.Cod f)) \<cdot>
                       (\<tau> (B\<^sub>0.Cod f) \<otimes> F\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)) \<cdot>
                          \<l>\<^sup>-\<^sup>1[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)]) \<cdot>
                      \<l>[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)] \<cdot> (\<I> \<otimes> B\<^sub>0.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1"
                using comp_assoc by simp
              also have "... =
                    Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (B\<^sub>0.Cod f)) \<cdot>
                      (G\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f) \<otimes> \<tau> (A\<^sub>0.Dom f)) \<cdot>
                         \<r>\<^sup>-\<^sup>1[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)] \<cdot>
                           (\<l>[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)] \<cdot> (\<I> \<otimes> B\<^sub>0.Map f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
                using f A\<^sub>0.Cod_in_Obj A\<^sub>0.Dom_in_Obj naturality comp_assoc by simp
              also have "... =
                    Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (B\<^sub>0.Cod f)) \<cdot>
                     (G\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f) \<otimes> \<tau> (A\<^sub>0.Dom f)) \<cdot>
                        \<r>\<^sup>-\<^sup>1[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)] \<cdot> (B\<^sub>0.Map f \<cdot> \<l>[\<I>]) \<cdot> \<iota>\<^sup>-\<^sup>1"
                using f lunit_naturality A\<^sub>0.Map_in_Hom by force
              also have "... =
                    Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (B\<^sub>0.Cod f)) \<cdot>
                      (G\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f) \<otimes> \<tau> (A\<^sub>0.Dom f)) \<cdot>
                        \<r>\<^sup>-\<^sup>1[Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)] \<cdot> B\<^sub>0.Map f"
              proof -
                have "\<iota> \<cdot> \<iota>\<^sup>-\<^sup>1 = \<I>"
                  using comp_arr_inv' unit_is_iso by blast
                moreover have "\<guillemotleft>B\<^sub>0.Map f : \<I> \<rightarrow> Hom\<^sub>A (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)\<guillemotright>"
                  using f A\<^sub>0.Map_in_Hom by blast
                ultimately show ?thesis
                  using f comp_arr_dom unitor_coincidence(1) comp_assoc by auto
              qed
              also have "... =
                    Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (B\<^sub>0.Cod f)) \<cdot>
                      (G\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f) \<otimes> \<tau> (A\<^sub>0.Dom f)) \<cdot>
                        (B\<^sub>0.Map f \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[\<I>]"
                using f runit'_naturality A\<^sub>0.Map_in_Hom by force
              also have "... =
                    Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (B\<^sub>0.Cod f)) \<cdot>
                      ((G\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f) \<otimes> \<tau> (A\<^sub>0.Dom f)) \<cdot>
                        (B\<^sub>0.Map f \<otimes> \<I>)) \<cdot> \<iota>\<^sup>-\<^sup>1"
                using unitor_coincidence comp_assoc by simp
              also have "... =
                    Comp\<^sub>B (F\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (A\<^sub>0.Dom f)) (G\<^sub>o (B\<^sub>0.Cod f)) \<cdot>
                      (G\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f) \<cdot> A\<^sub>0.Map f \<otimes> \<tau> (A\<^sub>0.Dom f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
              proof -
                have "seq (G\<^sub>a (A\<^sub>0.Dom f) (B\<^sub>0.Cod f)) (B\<^sub>0.Map f)"
                  using f A\<^sub>0.Map_in_Hom A\<^sub>0.Cod_in_Obj A\<^sub>0.Dom_in_Obj G.preserves_Hom
                  by fast
                moreover have "seq (\<tau> (A\<^sub>0.Dom f)) \<I>"
                  using f seqI component_in_hom
                  by (metis (no_types, lifting) A\<^sub>0.Dom_in_Obj ide_char
                      ide_unity in_homE)
                ultimately show ?thesis
                  using f comp_arr_dom interchange by auto
              qed
              finally show ?thesis by simp
            qed
            thus ?thesis
              using f 1 2 B\<^sub>0.comp_char [of "map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.cod f)" "F\<^sub>0.map\<^sub>0 f"]
                    B\<^sub>0.comp_char [of "G\<^sub>0.map\<^sub>0 f" "map\<^sub>o\<^sub>b\<^sub>j (A\<^sub>0.dom f)"]  
                    F\<^sub>0.map\<^sub>0_def G\<^sub>0.map\<^sub>0_def map\<^sub>o\<^sub>b\<^sub>j_def
              by simp
          qed
        qed
      qed
    qed

    proposition is_natural_transformation:
    shows "natural_transformation A\<^sub>0.comp B\<^sub>0.comp F\<^sub>0.map\<^sub>0 G\<^sub>0.map\<^sub>0 \<tau>.map"
      ..

  end

  subsection "Self-Enriched Case"

  text\<open>
    Here we show that a closed monoidal category \<open>C\<close>, regarded as a category enriched
    in itself, it is isomorphic to its own underlying category.  This is useful,
    because it is somewhat less cumbersome to work directly in the category \<open>C\<close>
    than in the higher-type version that results from the underlying category construction.
    Kelly often regards these two categories as identical.
  \<close>

  locale self_enriched_category =
    elementary_closed_monoidal_category +
    enriched_category C T \<alpha> \<iota> \<open>Collect ide\<close> exp Id Comp
  begin

    sublocale UC: underlying_category C T \<alpha> \<iota> \<open>Collect ide\<close> exp Id Comp ..

    abbreviation toUC
    where "toUC g \<equiv> if arr g
                     then UC.MkArr (dom g) (cod g) (g\<^sup>\<up>)
                     else UC.null"

    lemma toUC_simps [simp]:
    assumes "arr f"
    shows "UC.arr (toUC f)"
    and "UC.dom (toUC f) = toUC (dom f)"
    and "UC.cod (toUC f) = toUC (cod f)"
      using assms UC.arr_char UC.dom_char UC.cod_char UP_def
            comp_cod_arr Id_def
      by auto

    lemma toUC_in_hom [intro]:
    assumes "arr f"
    shows "UC.in_hom (toUC f) (UC.MkIde (dom f)) (UC.MkIde (cod f))"
      using assms toUC_simps by fastforce

    sublocale toUC: "functor" C UC.comp toUC
        using toUC_simps UP_comp UC.COMP_def
        by unfold_locales auto

    abbreviation frmUC
    where "frmUC g \<equiv> if UC.arr g
                       then (UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g]
                       else null"

    lemma frmUC_simps [simp]:
    assumes "UC.arr f"
    shows "arr (frmUC f)"
    and "dom (frmUC f) = frmUC (UC.dom f)"
    and "cod (frmUC f) = frmUC (UC.cod f)"
      using assms UC.arr_char UC.dom_char UC.cod_char Uncurry_Curry
            Id_def lunit_in_hom DN_def
      by auto

    lemma frmUC_in_hom [intro]:
    assumes "UC.in_hom f a b"
    shows "\<guillemotleft>frmUC f : frmUC a \<rightarrow> frmUC b\<guillemotright>"
      using assms frmUC_simps by blast

    lemma DN_Map_comp:
    assumes "UC.seq g f"
    shows "(UC.Map (UC.comp g f))\<^sup>\<down>[UC.Dom f, UC.Cod g] =
           (UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g] \<cdot>
             (UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f]"
    proof -
      have "(UC.Map (UC.comp g f))\<^sup>\<down>[UC.Dom f, UC.Cod g] =
            ((UC.Map (UC.comp g f))\<^sup>\<down>[UC.Dom f, UC.Cod g])\<^sup>\<up>
                         \<^sup>\<down>[UC.Dom f, UC.Cod g]"
        using assms UC.arr_char UC.seq_char [of g f] by fastforce
      also have "... = ((UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g] \<cdot>
                          (UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f])\<^sup>\<up>
                             \<^sup>\<down>[UC.Dom f, UC.Cod g]"
      proof -
        have "((UC.Map (UC.comp g f))\<^sup>\<down>[UC.Dom f, UC.Cod g])\<^sup>\<up> =
               UC.Map (UC.comp g f)"
          using assms UC.arr_char UC.seq_char [of g f] by fastforce
        also have "... = Comp (UC.Dom f) (UC.Dom g) (UC.Cod g) \<cdot>
                           (UC.Map g \<otimes> UC.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1"
          using assms UC.Map_comp UC.seq_char by blast
        also have "... = Comp (UC.Dom f) (UC.Dom g) (UC.Cod g) \<cdot>
                           (((UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g])\<^sup>\<up> \<otimes>
                                ((UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f])\<^sup>\<up>) \<cdot> \<iota>\<^sup>-\<^sup>1"
          using assms UC.seq_char UC.arr_char by auto
        also have "... = ((UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g] \<cdot>
                           (UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f])\<^sup>\<up>"
        proof -
          have "dom ((UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f]) = UC.Dom f"
            using assms DN_Id UC.Dom_in_Obj frmUC_simps(2) by auto
          moreover have "cod ((UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f]) = UC.Cod f"
            using assms DN_Id UC.Cod_in_Obj frmUC_simps(3) by auto
          moreover have "seq ((UC.Map g)\<^sup>\<down>[UC.Cod f, UC.Cod g])
                             ((UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f])"
            using assms frmUC_simps(1-3) UC.seq_char
            apply (intro seqI)
              apply auto[3]
            by metis+
          ultimately show ?thesis
            using assms UP_comp UP_DN(2) UC.arr_char UC.seq_char
                  in_homE seqI
            by auto
        qed
        finally show ?thesis by simp
      qed
      also have "... = (UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g] \<cdot>
                         (UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f]"
      proof -
        have 2: "seq ((UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g])
                     ((UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f])"
          using assms frmUC_simps(1-3) UC.seq_char
          apply (elim UC.seqE, intro seqI)
            apply auto[3]
          by metis+
        moreover have "dom ((UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g] \<cdot>
                              (UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f]) =
                       UC.Dom f"
          using assms 2 UC.Dom_comp UC.arr_char [of f] by auto
        moreover have "cod ((UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g] \<cdot>
                               (UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f]) =
                       UC.Cod g"
          using assms 2 UC.Cod_comp UC.arr_char [of g] by auto
        ultimately show ?thesis
          using assms
                UP_DN(3) [of "(UC.Map g)\<^sup>\<down>[UC.Dom g, UC.Cod g] \<cdot>
                                 (UC.Map f)\<^sup>\<down>[UC.Dom f, UC.Cod f]"]
          by simp
      qed
      finally show ?thesis by blast
    qed

    sublocale frmUC: "functor" UC.comp C frmUC
    proof
      show "\<And>f. \<not> UC.arr f \<Longrightarrow> frmUC f = null"
        by simp
      show "\<And>f. UC.arr f \<Longrightarrow> arr (frmUC f)"
        using UC.arr_char frmUC_simps(1) by blast
      show "\<And>f. UC.arr f \<Longrightarrow> dom (frmUC f) = frmUC (UC.dom f)"
        using frmUC_simps(2) by blast
      show "\<And>f. UC.arr f \<Longrightarrow> cod (frmUC f) = frmUC (UC.cod f)"
        using frmUC_simps(3) by blast
      fix f g
      assume fg: "UC.seq g f"
      show "frmUC (UC.comp g f) = frmUC g \<cdot> frmUC f"
        using fg UC.seq_char DN_Map_comp by auto
    qed

    sublocale inverse_functors UC.comp C toUC frmUC
    proof
      show "frmUC \<circ> toUC = map"
        using is_extensional comp_arr_dom comp_assoc Uncurry_Curry by auto
      interpret to_frm: composite_functor UC.comp C UC.comp frmUC toUC ..
      show "toUC \<circ> frmUC = UC.map"
      proof
        fix f
        show "(toUC \<circ> frmUC) f = UC.map f"
        proof (cases "UC.arr f")
          show "\<not> UC.arr f \<Longrightarrow> ?thesis"
            using UC.is_extensional by auto
          assume f: "UC.arr f"
          show ?thesis
          proof (intro UC.arr_eqI)
            show "UC.arr ((toUC \<circ> frmUC) f)"
              using f by blast
            show "UC.arr (UC.map f)"
              using f by blast
            show "UC.Dom ((toUC \<circ> frmUC) f) = UC.Dom (UC.map f)"
              using f UC.Dom_in_Obj frmUC.preserves_arr UC.arr_char [of f]
              by auto
            show "UC.Cod (to_frm.map f) = UC.Cod (UC.map f)"
              using f UC.arr_char [of f] by auto
            show "UC.Map (to_frm.map f) = UC.Map (UC.map f)"
              using f UP_DN UC.arr_char [of f] by auto
          qed
        qed
      qed
    qed

    lemma inverse_functors_toUC_frmUC:
    shows "inverse_functors UC.comp C toUC frmUC"
      ..

    corollary enriched_category_isomorphic_to_underlying_category:
    shows "isomorphic_categories UC.comp C"
      using inverse_functors_toUC_frmUC
      by unfold_locales blast

  end

  section "Opposite of an Enriched Category"

  text\<open>
    Construction of the opposite of an enriched category
    (\emph{cf.}~\<^cite>\<open>"kelly-enriched-category"\<close> (1.19)) requires that the underlying monoidal
    category be symmetric, in order to introduce the required ``twist'' in the definition
    of composition.
  \<close>

  locale opposite_enriched_category =
    symmetric_monoidal_category +
    EC: enriched_category
  begin

    interpretation elementary_symmetric_monoidal_category
                        C tensor unity lunit runit assoc sym
      using induces_elementary_symmetric_monoidal_category\<^sub>C\<^sub>M\<^sub>C by blast

    (* TODO: The names "Hom" and "Comp" are already in use as locale parameters. *)
    abbreviation (input) Hom\<^sub>o\<^sub>p
    where "Hom\<^sub>o\<^sub>p a b \<equiv> Hom b a"

    abbreviation Comp\<^sub>o\<^sub>p
    where "Comp\<^sub>o\<^sub>p a b c \<equiv> Comp c b a \<cdot> \<s>[Hom c b, Hom b a]"

    sublocale enriched_category C T \<alpha> \<iota> Obj Hom\<^sub>o\<^sub>p Id Comp\<^sub>o\<^sub>p
    proof
      show *: "\<And>a b. \<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow> ide (Hom b a)"
        using EC.ide_Hom by blast
      show "\<And>a. a \<in> Obj \<Longrightarrow> \<guillemotleft>Id a : \<I> \<rightarrow> Hom a a\<guillemotright>"
        using EC.Id_in_hom by blast
      show **: "\<And>a b c. \<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj\<rbrakk> \<Longrightarrow>
                          \<guillemotleft>Comp\<^sub>o\<^sub>p a b c : Hom c b \<otimes> Hom b a \<rightarrow> Hom c a\<guillemotright>"
        using sym_in_hom EC.ide_Hom EC.Comp_in_hom by auto
      show "\<And>a b. \<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow>
                     Comp\<^sub>o\<^sub>p a a b \<cdot> (Hom b a \<otimes> Id a) = \<r>[Hom b a]"
      proof -
        fix a b
        assume a: "a \<in> Obj" and b: "b \<in> Obj"
        have "Comp\<^sub>o\<^sub>p a a b \<cdot> (Hom b a \<otimes> Id a) =
              Comp b a a \<cdot> \<s>[Hom b a, Hom a a] \<cdot> (Hom b a \<otimes> Id a)"
          using comp_assoc by simp
        also have "... = Comp b a a \<cdot> (Id a \<otimes> Hom b a) \<cdot> \<s>[Hom b a, \<I>]"
          using a b sym_naturality [of "Hom b a" "Id a"] sym_in_hom
                EC.Id_in_hom EC.ide_Hom
          by fastforce
        also have "... = (Comp b a a \<cdot> (Id a \<otimes> Hom b a)) \<cdot> \<s>[Hom b a, \<I>]"
          using comp_assoc by simp
        also have "... = \<l>[Hom b a] \<cdot> \<s>[Hom b a, \<I>]"
          using a b EC.Comp_Id_Hom by simp
        also have "... = \<r>[Hom b a] "
          using a b unitor_coherence EC.ide_Hom by presburger
        finally show "Comp\<^sub>o\<^sub>p a a b \<cdot> (Hom b a \<otimes> Id a) = \<r>[Hom b a]"
          by blast
      qed
      show "\<And>a b. \<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow>
                     Comp\<^sub>o\<^sub>p a b b \<cdot> (Id b \<otimes> Hom b a) = \<l>[Hom b a]"
      proof -
        fix a b
        assume a: "a \<in> Obj" and b: "b \<in> Obj"
        have "Comp\<^sub>o\<^sub>p a b b \<cdot> (Id b \<otimes> Hom b a) =
              Comp b b a \<cdot> \<s>[Hom b b, Hom b a] \<cdot> (Id b \<otimes> Hom b a)"
          using comp_assoc by simp
        also have "... = Comp b b a \<cdot> (Hom b a \<otimes> Id b) \<cdot> \<s>[\<I>, Hom b a]"
          using a b sym_naturality [of "Id b" "Hom b a"] sym_in_hom
                EC.Id_in_hom EC.ide_Hom
          by force
        also have "... = (Comp b b a \<cdot> (Hom b a \<otimes> Id b)) \<cdot> \<s>[\<I>, Hom b a]"
          using comp_assoc by simp
        also have "... = \<r>[Hom b a] \<cdot> \<s>[\<I>, Hom b a]"
          using a b EC.Comp_Hom_Id by simp
        also have "... = \<l>[Hom b a]"
        proof -
          (* TODO: Should probably be a fact in elementary_symmetric_monoidal_category. *)
          have "\<r>[Hom b a] \<cdot> \<s>[\<I>, Hom b a] =
                (\<l>[Hom b a] \<cdot> \<s>[Hom b a, \<I>]) \<cdot> \<s>[\<I>, Hom b a]"
            using a b unitor_coherence EC.ide_Hom by simp
          also have "... = \<l>[Hom b a] \<cdot> \<s>[Hom b a, \<I>] \<cdot> \<s>[\<I>, Hom b a]"
            using comp_assoc by simp
          also have "... = \<l>[Hom b a]"
            using a b comp_arr_dom comp_arr_inv sym_inverse by simp
          finally show ?thesis by blast
        qed
        finally show "Comp\<^sub>o\<^sub>p a b b \<cdot> (Id b \<otimes> Hom b a) = \<l>[Hom b a]"
          by blast
      qed
      show "\<And>a b c d. \<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj; d \<in> Obj\<rbrakk> \<Longrightarrow>
                         Comp\<^sub>o\<^sub>p a b d \<cdot> (Comp\<^sub>o\<^sub>p b c d \<otimes> Hom b a) =
                         Comp\<^sub>o\<^sub>p a c d \<cdot> (Hom d c \<otimes> Comp\<^sub>o\<^sub>p a b c) \<cdot>
                           \<a>[Hom d c, Hom c b, Hom b a]"
      proof -
        fix a b c d
        assume a: "a \<in> Obj" and b: "b \<in> Obj" and c: "c \<in> Obj" and d: "d \<in> Obj"
        have "Comp\<^sub>o\<^sub>p a b d \<cdot> (Comp\<^sub>o\<^sub>p b c d \<otimes> Hom b a) =
              Comp\<^sub>o\<^sub>p a b d \<cdot> (Comp d c b \<otimes> Hom b a) \<cdot>
                (\<s>[Hom d c, Hom c b] \<otimes> Hom b a)"
          using a b c d ** interchange comp_ide_arr ide_in_hom seqI'
                EC.ide_Hom
          by metis
        also have "... = (Comp d b a \<cdot>
                            (\<s>[Hom d b, Hom b a] \<cdot> (Comp d c b \<otimes> Hom b a)) \<cdot>
                              (\<s>[Hom d c, Hom c b] \<otimes> Hom b a))"
          using comp_assoc by simp
        also have "... = (Comp d b a \<cdot>
                            ((Hom b a \<otimes> Comp d c b) \<cdot>
                                \<s>[Hom c b \<otimes> Hom d c, Hom b a]) \<cdot>
                              (\<s>[Hom d c, Hom c b] \<otimes> Hom b a))"
          using a b c d sym_naturality EC.Comp_in_hom ide_char
                in_homE EC.ide_Hom
          by metis
        also have "... = (Comp d b a \<cdot> (Hom b a \<otimes> Comp d c b)) \<cdot>
                           (\<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                              (\<s>[Hom d c, Hom c b] \<otimes> Hom b a))"
          using comp_assoc by simp
        also have "... = (Comp d c a \<cdot> (Comp c b a \<otimes> Hom d c) \<cdot>
                             \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c]) \<cdot>
                           (\<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                              (\<s>[Hom d c, Hom c b] \<otimes> Hom b a))"
        proof -
          have "Comp d b a \<cdot> (Hom b a \<otimes> Comp d c b) =
                (Comp d b a \<cdot> (Hom b a \<otimes> Comp d c b)) \<cdot>
                   (Hom b a \<otimes> Hom c b \<otimes> Hom d c)"
              using a b c d EC.Comp_in_hom arrI comp_in_homI ide_in_hom
                    tensor_in_hom EC.ide_Hom
          proof -
            have "seq (Comp d b a) (Hom b a \<otimes> Comp d c b)"
              using a b c d EC.Comp_in_hom arrI comp_in_homI ide_in_hom
                    tensor_in_hom EC.ide_Hom
              by meson
            moreover have "dom (Comp d b a \<cdot> (Hom b a \<otimes> Comp d c b)) =
                           (Hom b a \<otimes> Hom c b \<otimes> Hom d c)"
              using a b c d EC.Comp_in_hom dom_comp dom_tensor ideD(1-2)
                    in_homE calculation EC.ide_Hom
              by metis
            ultimately show ?thesis
              using a b c d EC.Comp_in_hom comp_arr_dom by metis
          qed
          also have "... =
                (Comp d b a \<cdot> (Hom b a \<otimes> Comp d c b)) \<cdot>
                   \<a>[Hom b a, Hom c b, Hom d c] \<cdot> \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c]"
            using a b c d comp_assoc_assoc'(1) EC.ide_Hom by simp
          also have "... = (Comp d b a \<cdot> (Hom b a \<otimes> Comp d c b) \<cdot>
                             \<a>[Hom b a, Hom c b, Hom d c]) \<cdot>
                               \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c]"
            using comp_assoc by simp
          also have "... = (Comp d c a \<cdot> (Comp c b a \<otimes> Hom d c)) \<cdot>
                              \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c]"
            using a b c d EC.Comp_assoc by simp
          also have "... = Comp d c a \<cdot> (Comp c b a \<otimes> Hom d c) \<cdot>
                             \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c]"
            using comp_assoc by simp
          finally have "Comp d b a \<cdot> (Hom b a \<otimes> Comp d c b) =
                        Comp d c a \<cdot> (Comp c b a \<otimes> Hom d c) \<cdot>
                          \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c]"
            by blast
          thus ?thesis by simp
        qed
        also have "... = (Comp d c a \<cdot> (Comp c b a \<otimes> Hom d c)) \<cdot>
                           (\<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                             \<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                               (\<s>[Hom d c, Hom c b] \<otimes> Hom b a))"
          using comp_assoc by simp
        finally have LHS: "(Comp d b a \<cdot> \<s>[Hom d b, Hom b a]) \<cdot>
                             (Comp d c b \<cdot> \<s>[Hom d c, Hom c b] \<otimes> Hom b a) =
                           (Comp d c a \<cdot> (Comp c b a \<otimes> Hom d c)) \<cdot>
                           (\<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                             \<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                               (\<s>[Hom d c, Hom c b] \<otimes> Hom b a))"
          by blast
        have "Comp\<^sub>o\<^sub>p a c d \<cdot> (Hom d c \<otimes> Comp\<^sub>o\<^sub>p a b c) \<cdot>
                \<a>[Hom d c, Hom c b, Hom b a] =
              Comp d c a \<cdot>
                (\<s>[Hom d c, Hom c a] \<cdot>
                  (Hom d c \<otimes> Comp c b a \<cdot> \<s>[Hom c b, Hom b a])) \<cdot>
                  \<a>[Hom d c, Hom c b, Hom b a]"
          using comp_assoc by simp
        also have "... =
              Comp d c a \<cdot>
                ((Comp c b a \<cdot> \<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                    \<s>[Hom d c, Hom c b \<otimes> Hom b a]) \<cdot>
                  \<a>[Hom d c, Hom c b, Hom b a]"
          using a b c d ** sym_naturality ide_char in_homE EC.ide_Hom
          by metis
        also have "... =
              Comp d c a \<cdot>
                (((Comp c b a \<otimes> Hom d c) \<cdot> (\<s>[Hom c b, Hom b a] \<otimes> Hom d c)) \<cdot>
                    \<s>[Hom d c, Hom c b \<otimes> Hom b a]) \<cdot>
                  \<a>[Hom d c, Hom c b, Hom b a]"
          using a b c d ** interchange comp_arr_dom ideD(1-2)
                in_homE EC.ide_Hom
          by metis
        also have "... = (Comp d c a \<cdot> (Comp c b a \<otimes> Hom d c)) \<cdot>
                           ((\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                             \<s>[Hom d c, Hom c b \<otimes> Hom b a] \<cdot>
                               \<a>[Hom d c, Hom c b, Hom b a])"
          using comp_assoc by simp
        also have "... = (Comp d c a \<cdot> (Comp c b a \<otimes> Hom d c)) \<cdot>
                           (\<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                              \<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                                (\<s>[Hom d c, Hom c b] \<otimes> Hom b a))"
        proof -
          have "(\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                  \<s>[Hom d c, Hom c b \<otimes> Hom b a] \<cdot>
                    \<a>[Hom d c, Hom c b, Hom b a] =
                \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                  \<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                    (\<s>[Hom d c, Hom c b] \<otimes> Hom b a)"
          proof -
            have 1: "\<s>[Hom d c, Hom c b \<otimes> Hom b a] \<cdot>
                       \<a>[Hom d c, Hom c b, Hom b a] =
                     \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                       (Hom c b \<otimes> \<s>[Hom d c, Hom b a]) \<cdot>
                         \<a>[Hom c b, Hom d c, Hom b a] \<cdot>
                           (\<s>[Hom d c, Hom c b] \<otimes> Hom b a)"
            proof -
              have "\<s>[Hom d c, Hom c b \<otimes> Hom b a] \<cdot>
                       \<a>[Hom d c, Hom c b, Hom b a] =
                    (\<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                       \<a>[Hom c b, Hom b a, Hom d c]) \<cdot>
                      \<s>[Hom d c, Hom c b \<otimes> Hom b a] \<cdot>
                        \<a>[Hom d c, Hom c b, Hom b a]"
                using a b c d comp_assoc_assoc'(2) comp_cod_arr by simp
              also have "... =
                    \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                      \<a>[Hom c b, Hom b a, Hom d c] \<cdot>
                        \<s>[Hom d c, Hom c b \<otimes> Hom b a] \<cdot>
                          \<a>[Hom d c, Hom c b, Hom b a]"
                using comp_assoc by simp
              also have "... =
                    \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                      (Hom c b \<otimes> \<s>[Hom d c, Hom b a]) \<cdot>
                        \<a>[Hom c b, Hom d c, Hom b a] \<cdot>
                          (\<s>[Hom d c, Hom c b] \<otimes> Hom b a)"
                using a b c d assoc_coherence EC.ide_Hom by auto
              finally show ?thesis by blast
            qed
            have 2: "(\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                       \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                         (Hom c b \<otimes> \<s>[Hom d c, Hom b a]) =
                     \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                       \<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                         inv \<a>[Hom c b, Hom d c, Hom b a]"
            proof -
              have "(\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                      \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                        (Hom c b \<otimes> \<s>[Hom d c, Hom b a]) =
                    inv ((Hom c b \<otimes> \<s>[Hom b a, Hom d c]) \<cdot>
                           \<a>[Hom c b, Hom b a, Hom d c] \<cdot>
                             (\<s>[Hom b a, Hom c b] \<otimes> Hom d c))"
              proof -
                have "inv ((Hom c b \<otimes> \<s>[Hom b a, Hom d c]) \<cdot>
                             \<a>[Hom c b, Hom b a, Hom d c] \<cdot>
                               (\<s>[Hom b a, Hom c b] \<otimes> Hom d c)) =
                      inv (\<a>[Hom c b, Hom b a, Hom d c] \<cdot>
                             (\<s>[Hom b a, Hom c b] \<otimes> Hom d c)) \<cdot>
                        inv (Hom c b \<otimes> \<s>[Hom b a, Hom d c])"
                  using a b c d EC.ide_Hom
                        inv_comp [of "\<a>[Hom c b, Hom b a, Hom d c] \<cdot>
                                          (\<s>[Hom b a, Hom c b] \<otimes> Hom d c)"
                                       "Hom c b \<otimes> \<s>[Hom b a, Hom d c]"]
                  by fastforce
                also have "... =
                      (inv (\<s>[Hom b a, Hom c b] \<otimes> Hom d c) \<cdot>
                         \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c]) \<cdot>
                        inv (Hom c b \<otimes> \<s>[Hom b a, Hom d c])"
                  using a b c d EC.ide_Hom inv_comp by simp
                also have "... =
                      ((\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                         \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c]) \<cdot>
                        (Hom c b \<otimes> \<s>[Hom d c, Hom b a])"
                  (* TODO: Need simps for inverse of sym. *)
                  using a b c d sym_inverse inverse_unique
                  apply auto[1]
                  by (metis *)
                finally show ?thesis
                  using comp_assoc by simp
              qed
              also have "... =
                    inv (\<a>[Hom c b, Hom d c, Hom b a] \<cdot>
                             \<s>[Hom b a, Hom c b \<otimes> Hom d c] \<cdot>
                               \<a>[Hom b a, Hom c b, Hom d c])"
                using a b c d assoc_coherence EC.ide_Hom by auto
              also have "... =
                    \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                      inv \<s>[Hom b a, Hom c b \<otimes> Hom d c] \<cdot>
                        \<a>\<^sup>-\<^sup>1[Hom c b, Hom d c, Hom b a]"
                using a b c d EC.ide_Hom inv_comp inv_tensor comp_assoc
                      isos_compose
                by auto
              also have "... =
                    \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                      \<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                        \<a>\<^sup>-\<^sup>1[Hom c b, Hom d c, Hom b a]"
                using a b c d sym_inverse inv_is_inverse inverse_unique
                by (metis tensor_preserves_ide EC.ide_Hom)
              finally show ?thesis by blast
            qed
            hence "(\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                     \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                       (Hom c b \<otimes> \<s>[Hom d c, Hom b a]) \<cdot>
                          \<a>[Hom c b, Hom d c, Hom b a] =
                   \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                     \<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                       inv \<a>[Hom c b, Hom d c, Hom b a] \<cdot>
                         \<a>[Hom c b, Hom d c, Hom b a]"
              by (metis comp_assoc)
            hence 3: "(\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                        \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                         (Hom c b \<otimes> \<s>[Hom d c, Hom b a]) \<cdot>
                           \<a>[Hom c b, Hom d c, Hom b a] =
                     \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                       \<s>[Hom c b \<otimes> Hom d c, Hom b a]"
              using a b c comp_arr_dom d by fastforce
            have "(\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                    \<s>[Hom d c, Hom c b \<otimes> Hom b a] \<cdot>
                      \<a>[Hom d c, Hom c b, Hom b a] =
                  (\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                     \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                       (Hom c b \<otimes> \<s>[Hom d c, Hom b a]) \<cdot>
                         \<a>[Hom c b, Hom d c, Hom b a] \<cdot>
                           (\<s>[Hom d c, Hom c b] \<otimes> Hom b a)"
              using 1 by simp
            also have "... =
                  ((\<s>[Hom c b, Hom b a] \<otimes> Hom d c) \<cdot>
                     \<a>\<^sup>-\<^sup>1[Hom c b, Hom b a, Hom d c] \<cdot>
                       (Hom c b \<otimes> \<s>[Hom d c, Hom b a]) \<cdot>
                         \<a>[Hom c b, Hom d c, Hom b a]) \<cdot>
                           (\<s>[Hom d c, Hom c b] \<otimes> Hom b a)"
              using comp_assoc by simp
            also have "... =
                  (\<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                     \<s>[Hom c b \<otimes> Hom d c, Hom b a]) \<cdot>
                        (\<s>[Hom d c, Hom c b] \<otimes> Hom b a)"
              using 3 by simp
            also have "... =
                  \<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                     \<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                        (\<s>[Hom d c, Hom c b] \<otimes> Hom b a)"
              using comp_assoc by simp
            finally show ?thesis by simp
          qed
          thus ?thesis by auto
        qed
        finally have RHS: "Comp\<^sub>o\<^sub>p a c d \<cdot>
                             (Hom d c \<otimes> Comp\<^sub>o\<^sub>p a b c) \<cdot>
                                \<a>[Hom d c, Hom c b, Hom b a] =
                           (Comp d c a \<cdot> (Comp c b a \<otimes> Hom d c)) \<cdot>
                             (\<a>\<^sup>-\<^sup>1[Hom b a, Hom c b, Hom d c] \<cdot>
                                \<s>[Hom c b \<otimes> Hom d c, Hom b a] \<cdot>
                                  (\<s>[Hom d c, Hom c b] \<otimes> Hom b a))"
          by blast
        show "Comp\<^sub>o\<^sub>p a b d \<cdot> (Comp\<^sub>o\<^sub>p b c d \<otimes> Hom b a) =
              Comp\<^sub>o\<^sub>p a c d \<cdot> (Hom d c \<otimes> Comp\<^sub>o\<^sub>p a b c) \<cdot>
                \<a>[Hom d c, Hom c b, Hom b a]"
          using LHS RHS by simp
      qed
    qed

  end

  subsection "Relation between \<open>(-\<^sup>o\<^sup>p)\<^sub>0\<close> and \<open>(-\<^sub>0)\<^sup>o\<^sup>p\<close>"

  text\<open>
    Kelly (comment before (1.22)) claims, for a category \<open>A\<close> enriched in a symmetric
    monoidal category, that we have \<open>(A\<^sup>o\<^sup>p)\<^sub>0 = (A\<^sub>0)\<^sup>o\<^sup>p\<close>.  This point becomes somewhat
    confusing, as it depends on the particular formalization one adopts for the
    notion of ``category''.

    \sloppypar
    As we can see from the next two facts (\<open>Op_UC_hom_char\<close> and \<open>UC_Op_hom_char\<close>),
    the hom-sets \<open>Op.UC.hom a b\<close> and \<open>UC.Op.hom a b\<close> are both obtained by using \<open>UC.MkArr\<close>
    to ``tag'' elements of \<open>hom \<I> (Hom (UC.Dom b) (UC.Dom a))\<close> with \<open>UC.Dom a\<close> and \<open>UC.Dom b\<close>.
    These two hom-sets are formally distinct if (as is the case for us), the arrows of a
    category are regarded as containing information about their domain and codomain,
    so that the hom-sets are disjoint.  On the other hand, if one regards a category
    as a collection of mappings that assign to each pair of objects \<open>a\<close> and \<open>b\<close>
    a corresponding set \<open>hom a b\<close>, then the hom-sets \<open>Op.UC.hom a b\<close> and \<open>UC.Op.hom a b\<close>
    could be arranged to be equal, as Kelly suggests.
  \<close>

  locale category_enriched_in_symmetric_monoidal_category =
    symmetric_monoidal_category +
    enriched_category
  begin

    interpretation elementary_symmetric_monoidal_category
                      C tensor unity lunit runit assoc sym
      using induces_elementary_symmetric_monoidal_category\<^sub>C\<^sub>M\<^sub>C by blast

    interpretation Op: opposite_enriched_category C T \<alpha> \<iota> \<sigma> Obj Hom Id Comp ..
    interpretation Op\<^sub>0: underlying_category C T \<alpha> \<iota> Obj Op.Hom\<^sub>o\<^sub>p Id Op.Comp\<^sub>o\<^sub>p
      ..

    interpretation UC: underlying_category C T \<alpha> \<iota> Obj Hom Id Comp ..
    interpretation UC.Op: dual_category UC.comp ..

    lemma Op_UC_hom_char:
    assumes "UC.ide a" and "UC.ide b"
    shows "Op\<^sub>0.hom a b =
           UC.MkArr (UC.Dom a) (UC.Dom b) `
             hom \<I> (Hom (UC.Dom b) (UC.Dom a))"
      using assms Op\<^sub>0.hom_char [of "UC.Dom a" "UC.Dom b"]
            UC.ide_char [of a] UC.ide_char [of b] UC.arr_char
      by force

    lemma UC_Op_hom_char:
    assumes "UC.ide a" and "UC.ide b"
    shows "UC.Op.hom a b =
           UC.MkArr (UC.Dom b) (UC.Dom a) `
             hom \<I> (Hom (UC.Dom b) (UC.Dom a))"
      using assms UC.Op.hom_char UC.hom_char [of "UC.Dom b" "UC.Dom a"]
            UC.ide_char\<^sub>C\<^sub>C
      by simp

    abbreviation toUCOp
    where "toUCOp f \<equiv> if Op\<^sub>0.arr f
                       then UC.MkArr (Op\<^sub>0.Cod f) (Op\<^sub>0.Dom f) (Op\<^sub>0.Map f)
                       else UC.Op.null"

    sublocale toUCOp: "functor" Op\<^sub>0.comp UC.Op.comp toUCOp
    proof
      show "\<And>f. \<not> Op\<^sub>0.arr f \<Longrightarrow> toUCOp f = UC.Op.null"
        by simp
      show 1: "\<And>f. Op\<^sub>0.arr f \<Longrightarrow> UC.Op.arr (toUCOp f)"
        using Op\<^sub>0.arr_char by auto
      show "\<And>f. Op\<^sub>0.arr f \<Longrightarrow> UC.Op.dom (toUCOp f) = toUCOp (Op\<^sub>0.dom f)"
        using 1 by simp
      show "\<And>f. Op\<^sub>0.arr f \<Longrightarrow> UC.Op.cod (toUCOp f) = toUCOp (Op\<^sub>0.cod f)"
        using 1 by simp
      show "\<And>g f. Op\<^sub>0.seq g f \<Longrightarrow>
                     toUCOp (Op\<^sub>0.comp g f) = UC.Op.comp (toUCOp g) (toUCOp f)"
      proof -
        fix f g
        assume fg: "Op\<^sub>0.seq g f"
        show "toUCOp (Op\<^sub>0.comp g f) = UC.Op.comp (toUCOp g) (toUCOp f)"
        proof (intro UC.arr_eqI)
          show "UC.arr (toUCOp (Op\<^sub>0.comp g f))"
            using 1 fg UC.Op.arr_char by blast
          show 2: "UC.arr (UC.Op.comp (toUCOp g) (toUCOp f))"
            using 1 Op\<^sub>0.seq_char UC.seq_char fg by force
          show "Op\<^sub>0.Dom (toUCOp (Op\<^sub>0.comp g f)) =
                Op\<^sub>0.Dom (UC.Op.comp (toUCOp g) (toUCOp f))"
            using 1 2 fg Op\<^sub>0.seq_char by fastforce
          show "Op\<^sub>0.Cod (toUCOp (Op\<^sub>0.comp g f)) =
                Op\<^sub>0.Cod (UC.Op.comp (toUCOp g) (toUCOp f))"
            using 1 2 fg Op\<^sub>0.seq_char by fastforce
          show "Op\<^sub>0.Map (toUCOp (Op\<^sub>0.comp g f)) =
                Op\<^sub>0.Map (UC.Op.comp (toUCOp g) (toUCOp f))"
          proof -
            have "Op\<^sub>0.Map (toUCOp (Op\<^sub>0.comp g f)) =
                  Op.Comp\<^sub>o\<^sub>p (UC.Dom f) (UC.Dom g) (UC.Cod g) \<cdot>
                    (UC.Map g \<otimes> UC.Map f) \<cdot> \<iota>\<^sup>-\<^sup>1"
              using 1 2 fg Op\<^sub>0.seq_char by auto
            also have "... = Comp (Op\<^sub>0.Cod g) (Op\<^sub>0.Dom g) (Op\<^sub>0.Dom f) \<cdot>
                             (\<s>[Hom (Op\<^sub>0.Cod g) (Op\<^sub>0.Dom g),
                                Hom (Op\<^sub>0.Dom g) (Op\<^sub>0.Dom f)] \<cdot>
                                (Op\<^sub>0.Map g \<otimes> Op\<^sub>0.Map f)) \<cdot> \<iota>\<^sup>-\<^sup>1"
              using comp_assoc by simp
            also have "... = Comp (Op\<^sub>0.Cod g) (Op\<^sub>0.Dom g) (Op\<^sub>0.Dom f) \<cdot>
                             ((Op\<^sub>0.Map f \<otimes> Op\<^sub>0.Map g) \<cdot> \<s>[\<I>, \<I>]) \<cdot> \<iota>\<^sup>-\<^sup>1"
              using fg Op\<^sub>0.seq_char Op\<^sub>0.arr_char sym_naturality
              by (metis (no_types, lifting) in_homE mem_Collect_eq)
            also have "... = Comp (Op\<^sub>0.Cod g) (Op\<^sub>0.Dom g) (Op\<^sub>0.Dom f) \<cdot>
                             (Op\<^sub>0.Map f \<otimes> Op\<^sub>0.Map g) \<cdot> \<s>[\<I>, \<I>] \<cdot> \<iota>\<^sup>-\<^sup>1"
              using comp_assoc by simp
            also have "... = Comp (Op\<^sub>0.Cod g) (Op\<^sub>0.Dom g) (Op\<^sub>0.Dom f) \<cdot>
                             (Op\<^sub>0.Map f \<otimes> Op\<^sub>0.Map g) \<cdot> \<iota>\<^sup>-\<^sup>1"
              using sym_inv_unit \<iota>_def monoidal_category_axioms
              by (simp add: monoidal_category.unitor_coincidence(1))
            finally have "Op\<^sub>0.Map (toUCOp (Op\<^sub>0.comp g f)) =
                        Comp (Op\<^sub>0.Cod g) (Op\<^sub>0.Dom g) (Op\<^sub>0.Dom f) \<cdot>
                             (Op\<^sub>0.Map f \<otimes> Op\<^sub>0.Map g) \<cdot> \<iota>\<^sup>-\<^sup>1"
              by blast
            also have "... = Op\<^sub>0.Map (UC.Op.comp (toUCOp g) (toUCOp f))"
              using fg 2 by auto
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    lemma functor_toUCOp:
    shows "functor Op\<^sub>0.comp UC.Op.comp toUCOp"
      ..

    abbreviation toOp\<^sub>0
      where "toOp\<^sub>0 f \<equiv> if UC.Op.arr f
                         then Op\<^sub>0.MkArr (UC.Cod f) (UC.Dom f) (UC.Map f)
                         else Op\<^sub>0.null"

    sublocale toOp\<^sub>0: "functor" UC.Op.comp Op\<^sub>0.comp toOp\<^sub>0
    proof
      show "\<And>f. \<not> UC.Op.arr f \<Longrightarrow> toOp\<^sub>0 f = Op\<^sub>0.null"
        by simp
      show 1: "\<And>f. UC.Op.arr f \<Longrightarrow> Op\<^sub>0.arr (toOp\<^sub>0 f)"
        using UC.arr_char by simp
      show "\<And>f. UC.Op.arr f \<Longrightarrow> Op\<^sub>0.dom (toOp\<^sub>0 f) = toOp\<^sub>0 (UC.Op.dom f)"
        using 1 by auto
      show "\<And>f. UC.Op.arr f \<Longrightarrow> Op\<^sub>0.cod (toOp\<^sub>0 f) = toOp\<^sub>0 (UC.Op.cod f)"
        using 1 by auto
      show "\<And>g f. UC.Op.seq g f \<Longrightarrow>
                     toOp\<^sub>0 (UC.Op.comp g f) = Op\<^sub>0.comp (toOp\<^sub>0 g) (toOp\<^sub>0 f)"
      proof -
        fix f g
        assume fg: "UC.Op.seq g f"
        show "toOp\<^sub>0 (UC.Op.comp g f) = Op\<^sub>0.comp (toOp\<^sub>0 g) (toOp\<^sub>0 f)"
        proof (intro Op\<^sub>0.arr_eqI)
          show "Op\<^sub>0.arr (toOp\<^sub>0 (UC.Op.comp g f))"
            using fg 1 by blast
          show 2: "Op\<^sub>0.seq (toOp\<^sub>0 g) (toOp\<^sub>0 f)"
            using fg 1 UC.seq_char UC.arr_char Op\<^sub>0.seq_char by fastforce
          show "Op\<^sub>0.Dom (toOp\<^sub>0 (UC.Op.comp g f)) =
                Op\<^sub>0.Dom (Op\<^sub>0.comp (toOp\<^sub>0 g) (toOp\<^sub>0 f))"
            using fg 1 2 Op\<^sub>0.dom_char Op\<^sub>0.cod_char UC.seq_char Op\<^sub>0.seq_char
            by auto
          show "Op\<^sub>0.Cod (toOp\<^sub>0 (UC.Op.comp g f)) =
                Op\<^sub>0.Cod (Op\<^sub>0.comp (toOp\<^sub>0 g) (toOp\<^sub>0 f))"
            using fg 1 2 Op\<^sub>0.dom_char Op\<^sub>0.cod_char UC.seq_char Op\<^sub>0.seq_char
            by auto
          show "Op\<^sub>0.Map (toOp\<^sub>0 (UC.Op.comp g f)) =
                Op\<^sub>0.Map (Op\<^sub>0.comp (toOp\<^sub>0 g) (toOp\<^sub>0 f))"
          proof -
            have "Op\<^sub>0.Map (Op\<^sub>0.comp (toOp\<^sub>0 g) (toOp\<^sub>0 f)) =
                  Op.Comp\<^sub>o\<^sub>p (Op\<^sub>0.Dom (toOp\<^sub>0 f)) (Op\<^sub>0.Dom (toOp\<^sub>0 g))
                    (Op\<^sub>0.Cod (toOp\<^sub>0 g)) \<cdot>
                    (Op\<^sub>0.Map (toOp\<^sub>0 g) \<otimes> Op\<^sub>0.Map (toOp\<^sub>0 f)) \<cdot> inv \<iota>"
              using fg 1 2 UC.seq_char by auto
            also have "... =
                       Comp (Op\<^sub>0.Dom g) (Op\<^sub>0.Cod g) (Op\<^sub>0.Cod f) \<cdot>
                         (\<s>[Hom (Op\<^sub>0.Dom g) (Op\<^sub>0.Cod g),
                            Hom (Op\<^sub>0.Cod g) (Op\<^sub>0.Cod f)] \<cdot>
                            (Op\<^sub>0.Map g \<otimes> Op\<^sub>0.Map f)) \<cdot> inv \<iota>"
              using fg comp_assoc by auto
            also have "... =
                       Comp (Op\<^sub>0.Dom g) (Op\<^sub>0.Cod g) (Op\<^sub>0.Cod f) \<cdot>
                         ((Op\<^sub>0.Map f \<otimes> Op\<^sub>0.Map g) \<cdot> \<s>[unity, unity]) \<cdot> inv \<iota>"
              using fg UC.seq_char UC.arr_char sym_naturality
              by (metis (no_types, lifting) in_homE UC.Op.arr_char
                  UC.Op.comp_def mem_Collect_eq)
            also have "... =
                       Comp (Op\<^sub>0.Dom g) (Op\<^sub>0.Cod g) (Op\<^sub>0.Cod f) \<cdot>
                         (Op\<^sub>0.Map f \<otimes> Op\<^sub>0.Map g) \<cdot> \<s>[unity, unity] \<cdot> inv \<iota>"
              using comp_assoc by simp
            also have "... =
                       Comp (Op\<^sub>0.Dom g) (Op\<^sub>0.Cod g) (Op\<^sub>0.Cod f) \<cdot>
                         (Op\<^sub>0.Map f \<otimes> Op\<^sub>0.Map g) \<cdot> inv \<iota>"
              using sym_inv_unit \<iota>_def monoidal_category_axioms
              by (simp add: monoidal_category.unitor_coincidence(1))
            also have "... = Op\<^sub>0.Map (toOp\<^sub>0 (UC.Op.comp g f))"
              using fg UC.seq_char by simp
            finally show ?thesis by argo
          qed
        qed
      qed
    qed

    lemma functor_toOp\<^sub>0:
    shows "functor UC.Op.comp Op\<^sub>0.comp toOp\<^sub>0"
      ..

    sublocale inverse_functors UC.Op.comp Op\<^sub>0.comp toUCOp toOp\<^sub>0
      using Op\<^sub>0.MkArr_Map toUCOp.preserves_reflects_arr Op\<^sub>0.is_extensional
            UC.MkArr_Map toOp\<^sub>0.preserves_reflects_arr UC.Op.is_extensional
      by unfold_locales auto

    lemma inverse_functors_toUCOp_toOp\<^sub>0:
    shows "inverse_functors UC.Op.comp Op\<^sub>0.comp toUCOp toOp\<^sub>0"
      ..

  end

  section "Enriched Hom Functors"

  text\<open>
    Here we exhibit covariant and contravariant hom functors as enriched functors,
    as in \<^cite>\<open>"kelly-enriched-category"\<close> Section 1.6.  We don't bother to exhibit
    them as partial functors of a single two-argument functor, as to do so would
    require us to define the tensor product of enriched categories; something that would
    require more technology for proving coherence conditions than we have developed
    at present.
  \<close>

  subsection "Covariant Case"

  locale covariant_Hom =
    monoidal_category +
    (* We need qualifier C here because otherwise there is a clash on Id and Comp. *)
    C: elementary_closed_monoidal_category +
    enriched_category +
  fixes x :: 'o
  assumes x: "x \<in> Obj"
  begin

    interpretation C: enriched_category C T \<alpha> \<iota> \<open>Collect ide\<close> exp C.Id C.Comp
      using C.is_enriched_in_itself by simp
    interpretation C: self_enriched_category C T \<alpha> \<iota> exp eval Curry ..

    abbreviation hom\<^sub>o
    where "hom\<^sub>o \<equiv> Hom x"

    abbreviation hom\<^sub>a
    where "hom\<^sub>a \<equiv> \<lambda>b c. if b \<in> Obj \<and> c \<in> Obj
                        then Curry[Hom b c, Hom x b, Hom x c] (Comp x b c)
                        else null"

    sublocale enriched_functor C T \<alpha> \<iota>
                Obj Hom Id Comp
                \<open>Collect ide\<close> exp C.Id C.Comp
                hom\<^sub>o hom\<^sub>a
    proof
      show "\<And>a b. a \<notin> Obj \<or> b \<notin> Obj \<Longrightarrow> hom\<^sub>a a b = null"
        by auto
      show "\<And>y. y \<in> Obj \<Longrightarrow> hom\<^sub>o y \<in> Collect ide"
        using x ide_Hom by auto
      show *: "\<And>a b. \<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow>
                        \<guillemotleft>hom\<^sub>a a b : Hom a b \<rightarrow> exp (hom\<^sub>o a) (hom\<^sub>o b)\<guillemotright>"
        using x by auto
      show "\<And>a. a \<in> Obj \<Longrightarrow> hom\<^sub>a a a \<cdot> Id a = C.Id (hom\<^sub>o a)"
        using x Comp_Id_Hom Comp_in_hom Id_in_hom C.Id_def C.comp_Curry_arr
        apply auto[1]
        by (metis ide_Hom)
      show "\<And>a b c. \<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj\<rbrakk> \<Longrightarrow>
                       C.Comp (hom\<^sub>o a) (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                         (hom\<^sub>a b c \<otimes> hom\<^sub>a a b) =
                       hom\<^sub>a a c \<cdot> Comp a b c"
      proof -
        fix a b c
        assume a: "a \<in> Obj" and b: "b \<in> Obj" and c: "c \<in> Obj"
        have "Uncurry[hom\<^sub>o a, hom\<^sub>o c]
                (C.Comp (hom\<^sub>o a) (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> (hom\<^sub>a b c \<otimes> hom\<^sub>a a b)) =
              Uncurry[hom\<^sub>o a, hom\<^sub>o c] (hom\<^sub>a a c \<cdot> Comp a b c)"
        proof -
          have "Uncurry[hom\<^sub>o a, hom\<^sub>o c]
                  (C.Comp (hom\<^sub>o a) (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> (hom\<^sub>a b c \<otimes> hom\<^sub>a a b)) =
                Uncurry[hom\<^sub>o a, hom\<^sub>o c]
                  (Curry[exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> exp (hom\<^sub>o a) (hom\<^sub>o b), hom\<^sub>o a,
                         hom\<^sub>o c]
                     (eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                        (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                          \<a>[exp (hom\<^sub>o b) (hom\<^sub>o c), exp (hom\<^sub>o a) (hom\<^sub>o b),
                            hom\<^sub>o a]) \<cdot>
                       (hom\<^sub>a b c \<otimes> hom\<^sub>a a b))"
            using C.Comp_def by simp
          also have "... =
                     Uncurry[hom\<^sub>o a, hom\<^sub>o c]
                       (Curry[Hom b c \<otimes> Hom a b, hom\<^sub>o a, hom\<^sub>o c]
                          ((eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                              (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                                 \<a>[exp (hom\<^sub>o b) (hom\<^sub>o c), exp (hom\<^sub>o a) (hom\<^sub>o b),
                                   hom\<^sub>o a]) \<cdot>
                            ((hom\<^sub>a b c \<otimes> hom\<^sub>a a b) \<otimes> hom\<^sub>o a)))"
          proof -
            have "\<guillemotleft>hom\<^sub>a b c \<otimes> hom\<^sub>a a b :
                    Hom b c \<otimes> Hom a b \<rightarrow>
                    exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> exp (hom\<^sub>o a) (hom\<^sub>o b)\<guillemotright>"
              using x a b c * by force
            moreover have "\<guillemotleft>eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                              (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                                \<a>[exp (hom\<^sub>o b) (hom\<^sub>o c), exp (hom\<^sub>o a) (hom\<^sub>o b), hom\<^sub>o a]
                              : (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> exp (hom\<^sub>o a) (hom\<^sub>o b))
                                   \<otimes> hom\<^sub>o a
                                     \<rightarrow> hom\<^sub>o c\<guillemotright>"
              using x a b c by simp
            ultimately show ?thesis
              using x a b c C.comp_Curry_arr by simp
          qed
          also have "... =
                     (eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                        (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                          \<a>[exp (hom\<^sub>o b) (hom\<^sub>o c), exp (hom\<^sub>o a) (hom\<^sub>o b), hom\<^sub>o a]) \<cdot>
                       ((hom\<^sub>a b c \<otimes> hom\<^sub>a a b) \<otimes> hom\<^sub>o a)"
            using x a b c
                  C.Uncurry_Curry
                     [of "Hom b c \<otimes> Hom a b" "hom\<^sub>o a" "hom\<^sub>o c"
                         "(eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                          (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                            \<a>[exp (hom\<^sub>o b) (hom\<^sub>o c), exp (hom\<^sub>o a) (hom\<^sub>o b), hom\<^sub>o a]) \<cdot>
                              ((Curry[Hom b c, hom\<^sub>o b, hom\<^sub>o c] (Comp x b c) \<otimes>
                                Curry[Hom a b, hom\<^sub>o a, hom\<^sub>o b] (Comp x a b))
                                  \<otimes> hom\<^sub>o a)"]
            by fastforce
          also have "... =
                     eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                       (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                         \<a>[exp (hom\<^sub>o b) (hom\<^sub>o c), exp (hom\<^sub>o a) (hom\<^sub>o b), hom\<^sub>o a] \<cdot>
                           ((hom\<^sub>a b c \<otimes> hom\<^sub>a a b) \<otimes> hom\<^sub>o a)"
            by (simp add: comp_assoc)
          also have "... =
                     eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                       ((exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                         (hom\<^sub>a b c \<otimes> hom\<^sub>a a b \<otimes> hom\<^sub>o a)) \<cdot>
                           \<a>[Hom b c, Hom a b, hom\<^sub>o a]"
             using x a b c Comp_in_hom
                   assoc_naturality
                     [of "Curry[Hom b c, hom\<^sub>o b, hom\<^sub>o c] (Comp x b c)"
                         "Curry[Hom a b, hom\<^sub>o a, hom\<^sub>o b] (Comp x a b)"
                         "hom\<^sub>o a"]
            using comp_assoc by auto
          also have "... =
                     eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                       (exp (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                          hom\<^sub>a b c \<otimes> Uncurry[hom\<^sub>o a, hom\<^sub>o b] (hom\<^sub>a a b)) \<cdot>
                            \<a>[Hom b c, Hom a b, hom\<^sub>o a]"
            using x a b c Comp_in_hom interchange by simp
          also have "... =
                     eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                       (exp (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> hom\<^sub>a b c \<otimes> Comp x a b) \<cdot>
                         \<a>[Hom b c, Hom a b, hom\<^sub>o a]"
            using x a b c C.Uncurry_Curry Comp_in_hom by auto
          also have "... =
                     eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> (hom\<^sub>a b c \<otimes> Comp x a b) \<cdot>
                       \<a>[Hom b c, Hom a b, hom\<^sub>o a]"
            using x a b c
            by (simp add: Comp_in_hom comp_ide_arr)
          also have "... =
                     eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                       ((hom\<^sub>a b c \<otimes> hom\<^sub>o b) \<cdot> (Hom b c \<otimes> Comp x a b)) \<cdot>
                         \<a>[Hom b c, Hom a b, hom\<^sub>o a]"
          proof -
            have "seq (hom\<^sub>a b c) (Hom b c)"
              using x a b c Comp_in_hom C.Curry_in_hom ide_Hom by simp
            moreover have "seq (hom\<^sub>o b) (Comp x a b)"
              using x a b c Comp_in_hom by fastforce
            ultimately show ?thesis
              using x a b c Comp_in_hom C.Curry_in_hom comp_arr_ide
                    comp_ide_arr ide_Hom interchange
              by metis
          qed
          also have "... =
                     Uncurry[hom\<^sub>o b, hom\<^sub>o c] (hom\<^sub>a b c) \<cdot>
                       (Hom b c \<otimes> Comp x a b) \<cdot>
                         \<a>[Hom b c, Hom a b, hom\<^sub>o a]"
            using comp_assoc by simp
          also have "... = Comp x a c \<cdot> (Comp a b c \<otimes> hom\<^sub>o a)"
            using x a b c C.Uncurry_Curry Comp_in_hom Comp_assoc by auto
          also have "... = Uncurry[hom\<^sub>o a, hom\<^sub>o c]
                             (Curry[Hom b c \<otimes> Hom a b, hom\<^sub>o a, hom\<^sub>o c]
                                (Comp x a c \<cdot> (Comp a b c \<otimes> hom\<^sub>o a)))"
            using x a b c Comp_in_hom comp_assoc
                  C.Uncurry_Curry
                    [of "Hom b c \<otimes> Hom a b" "hom\<^sub>o a" "hom\<^sub>o c"
                        "Comp x a c \<cdot> (Comp a b c \<otimes> hom\<^sub>o a)"]
            by fastforce
          also have "... = Uncurry[hom\<^sub>o a, hom\<^sub>o c] (hom\<^sub>a a c \<cdot> Comp a b c)"
            using x a b c Comp_in_hom
                  C.comp_Curry_arr 
                    [of "hom\<^sub>o a" "Comp a b c" "Hom b c \<otimes> Hom a b"
                        "Hom a c" "Comp x a c" "hom\<^sub>o c"]
            by auto
          finally show ?thesis by blast
        qed
        hence "Curry[Hom b c \<otimes> Hom a b, hom\<^sub>o a, hom\<^sub>o c]
                 (Uncurry[hom\<^sub>o a, hom\<^sub>o c]
                    (C.Comp (hom\<^sub>o a) (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                       (hom\<^sub>a b c \<otimes> hom\<^sub>a a b))) =
               Curry[Hom b c \<otimes> Hom a b, hom\<^sub>o a, hom\<^sub>o c]
                 (Uncurry[hom\<^sub>o a, hom\<^sub>o c] (hom\<^sub>a a c \<cdot> Comp a b c))"
          by simp
        thus "C.Comp (hom\<^sub>o a) (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> (hom\<^sub>a b c \<otimes> hom\<^sub>a a b) =
              hom\<^sub>a a c \<cdot> Comp a b c"
          using x a b c Comp_in_hom
                C.Curry_Uncurry
                  [of "Hom b c \<otimes> Hom a b" "hom\<^sub>o a" "hom\<^sub>o c" "hom\<^sub>a a c \<cdot> Comp a b c"]
                C.Curry_Uncurry
                  [of "Hom b c \<otimes> Hom a b" "hom\<^sub>o a" "hom\<^sub>o c"
                      "C.Comp (hom\<^sub>o a) (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> (hom\<^sub>a b c \<otimes> hom\<^sub>a a b)"]
          by auto
      qed
    qed

    lemma is_enriched_functor:
    shows "enriched_functor C T \<alpha> \<iota>
             Obj Hom Id Comp
             (Collect ide) exp C.Id C.Comp
             hom\<^sub>o hom\<^sub>a"
      ..

    sublocale C\<^sub>0: underlying_category C T \<alpha> \<iota> \<open>Collect ide\<close> exp C.Id C.Comp ..
    sublocale UC: underlying_category C T \<alpha> \<iota> Obj Hom Id Comp ..
    sublocale UF: underlying_functor C T \<alpha> \<iota>
                    Obj Hom Id Comp
                    \<open>Collect ide\<close> exp C.Id C.Comp
                    hom\<^sub>o hom\<^sub>a
      ..

    text\<open>
      The following is Kelly's formula (1.31), for the result of applying the ordinary
      functor underlying the covariant hom functor, to an arrow \<open>g : \<I> \<rightarrow> Hom b c\<close> of \<open>C\<^sub>0\<close>,
      resulting in an arrow \<open>Hom\<^sup>\<rightarrow> x g : Hom x b \<rightarrow> Hom x c\<close> of \<open>C\<close>.  The point of the result
      is that this can be expressed explicitly as \<open>Comp x b c \<cdot> (g \<otimes> hom\<^sub>o b) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]\<close>.
      This is all very confusing at first, because Kelly identifies \<open>C\<close> with the
      underlying category \<open>C\<^sub>0\<close> of \<open>C\<close> regarded as a self-enriched category, whereas here we
      cannot ignore the fact that they are merely isomorphic via \<open>C.frmUC: UC.comp \<rightarrow> C\<^sub>0.comp\<close>.
      There is also the bother that, for an arrow \<open>g : \<I> \<rightarrow> Hom b c\<close> of \<open>C\<close>,
      the corresponding arrow of the underlying category \<open>UC\<close> has to be formally
      constructed using \<open>UC.MkArr\<close>, \emph{i.e.}~as \<open>UC.MkArr b c g\<close>.
    \<close>

    lemma Kelly_1_31:
    assumes "b \<in> Obj" and "c \<in> Obj" and "\<guillemotleft>g : \<I> \<rightarrow> Hom b c\<guillemotright>"
    shows "C.frmUC (UF.map\<^sub>0 (UC.MkArr b c g)) =
           Comp x b c \<cdot> (g \<otimes> hom\<^sub>o b) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"
    proof -
      have "C.frmUC (UF.map\<^sub>0 (UC.MkArr b c g)) =
            (Curry[Hom b c, hom\<^sub>o b, hom\<^sub>o c] (Comp x b c) \<cdot> g) \<^sup>\<down>[hom\<^sub>o b, hom\<^sub>o c]"
        using assms x ide_Hom UF.map\<^sub>0_def
              C.UC.arr_MkArr
                [of "Hom x b" "Hom x c"
                    "Curry[Hom b c, Hom x b, Hom x c] (Comp x b c) \<cdot> g"]
        by fastforce
      also have "... = C.Uncurry (Hom x b) (Hom x c)
                         (Curry[\<I>, Hom x b, Hom x c]
                            (Comp x b c \<cdot> (g \<otimes> Hom x b))) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"
        using assms x C.comp_Curry_arr C.DN_def
        by (metis Comp_in_hom C.Curry_simps(1-2) in_homE seqI ide_Hom)
      also have "... = (Comp x b c \<cdot> (g \<otimes> Hom x b)) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"
        using assms x ide_Hom ide_unity
              C.Uncurry_Curry
                [of \<I> "Hom x b" "Hom x c" "Comp x b c \<cdot> (g \<otimes> Hom x b)"]
        by fastforce
      also have "... = Comp x b c \<cdot> (g \<otimes> Hom x b) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"
        using comp_assoc by simp
      finally show ?thesis by blast
    qed

    (*
     * TODO: Rationalize the naming between here and ClosedMonoidalCategory
     * to avoid clashes and be understandable.  I don't like having the generally
     * redundant subscript on "map\<^sub>0", but right now the unadorned name "map" clashes
     * with a value defined for the base category C.  The alternative is to qualify
     * all references to C, but that is worse.
     *)

    abbreviation map\<^sub>0
    where "map\<^sub>0 b c g \<equiv> Comp x b c \<cdot> (g \<otimes> Hom x b) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"    

  end

  context elementary_closed_monoidal_category
  begin

    lemma cov_Exp_DN:
    assumes "\<guillemotleft>g : \<I> \<rightarrow> exp a b\<guillemotright>"
    and "ide a" and "ide b" and "ide x"
    shows "Exp\<^sup>\<rightarrow> x (g \<^sup>\<down>[a, b]) =
           (Curry[exp a b, exp x a, exp x b] (Comp x a b) \<cdot> g) \<^sup>\<down>[exp x a, exp x b]"
    proof -
      have "(Curry[exp a b, exp x a, exp x b] (Comp x a b) \<cdot> g) \<^sup>\<down>[exp x a, exp x b] =
            Uncurry[exp x a, exp x b]
              (Curry[\<I>, exp x a, exp x b] (Comp x a b \<cdot> (g \<otimes> exp x a))) \<cdot> \<l>\<^sup>-\<^sup>1[exp x a]"
        using assms DN_def
              comp_Curry_arr
                [of "exp x a" g \<I> "exp a b" "Comp x a b" "exp x b"]
        by force
      also have "... = (Comp x a b \<cdot> (g \<otimes> exp x a)) \<cdot> \<l>\<^sup>-\<^sup>1[exp x a]"
        using assms Uncurry_Curry by auto
      also have "... = Curry[exp a b \<otimes> exp x a, x, b]
                         (eval a b \<cdot> (exp a b \<otimes> eval x a) \<cdot> \<a>[exp a b, exp x a, x]) \<cdot>
                           (g \<otimes> exp x a) \<cdot> \<l>\<^sup>-\<^sup>1[exp x a]"
        unfolding Comp_def
        using assms comp_assoc by auto
      also have "... = Curry[exp x a, x, b]
                         ((eval a b \<cdot> (exp a b \<otimes> eval x a) \<cdot> \<a>[exp a b, exp x a, x]) \<cdot>
                            ((g \<otimes> exp x a) \<cdot> \<l>\<^sup>-\<^sup>1[exp x a] \<otimes> x))"
        using assms comp_Curry_arr by auto
      also have "... = Curry[exp x a, x, b]
                         (eval a b \<cdot> (exp a b \<otimes> eval x a) \<cdot>
                            (\<a>[exp a b, exp x a, x] \<cdot> ((g \<otimes> exp x a) \<otimes> x)) \<cdot>
                               (\<l>\<^sup>-\<^sup>1[exp x a] \<otimes> x))"
        using assms comp_arr_dom comp_cod_arr interchange comp_assoc by fastforce
      also have "... = Curry[exp x a, x, b]
                         (eval a b \<cdot> (exp a b \<otimes> eval x a) \<cdot>
                            ((g \<otimes> exp x a \<otimes> x) \<cdot> \<a>[\<I>, exp x a, x]) \<cdot>
                               (\<l>\<^sup>-\<^sup>1[exp x a] \<otimes> x))"
        using assms assoc_naturality [of g "exp x a" x] by auto
      also have "... = Curry[exp x a, x, b]
                         (eval a b \<cdot> ((exp a b \<otimes> eval x a) \<cdot> (g \<otimes> exp x a \<otimes> x)) \<cdot>
                            \<a>[\<I>, exp x a, x] \<cdot> (\<l>\<^sup>-\<^sup>1[exp x a] \<otimes> x))"
        using assms comp_assoc by simp
      also have "... = Curry[exp x a, x, b]
                         (eval a b \<cdot> ((g \<otimes> a) \<cdot> (\<I> \<otimes> eval x a)) \<cdot>
                            \<a>[\<I>, exp x a, x] \<cdot> (\<l>\<^sup>-\<^sup>1[exp x a] \<otimes> x))"
        using assms comp_arr_dom comp_cod_arr interchange by auto
      also have "... = Curry[exp x a, x, b]
                         (Uncurry[a, b] g \<cdot> (\<I> \<otimes> eval x a) \<cdot> \<l>\<^sup>-\<^sup>1[exp x a \<otimes> x])"
        using assms lunit_tensor inv_comp comp_assoc by simp
      also have "... = Exp\<^sup>\<rightarrow> x (g \<^sup>\<down>[a, b])"
        using assms lunit'_naturality [of "eval x a"] comp_assoc DN_def by auto
      finally show ?thesis by simp
    qed

  end

  subsection "Contravariant Case"

  locale contravariant_Hom =
    symmetric_monoidal_category +
    C: elementary_closed_symmetric_monoidal_category +
    enriched_category +
  fixes y :: 'o
  assumes y: "y \<in> Obj"
  begin

    interpretation C: enriched_category C T \<alpha> \<iota> \<open>Collect ide\<close> exp C.Id C.Comp
      using C.is_enriched_in_itself by simp
    interpretation C: self_enriched_category C T \<alpha> \<iota> exp eval Curry ..

    sublocale Op: opposite_enriched_category C T \<alpha> \<iota> \<sigma> Obj Hom Id Comp ..

    abbreviation hom\<^sub>o
    where "hom\<^sub>o \<equiv> \<lambda>a. Hom a y"

    abbreviation hom\<^sub>a
    where "hom\<^sub>a \<equiv> \<lambda>b c. if b \<in> Obj \<and> c \<in> Obj
                        then Curry[Hom c b, Hom b y, Hom c y] (Op.Comp\<^sub>o\<^sub>p y b c)
                        else null"

    sublocale enriched_functor C T \<alpha> \<iota>
                Obj Op.Hom\<^sub>o\<^sub>p Id Op.Comp\<^sub>o\<^sub>p
                \<open>Collect ide\<close> exp C.Id C.Comp
                hom\<^sub>o hom\<^sub>a
    proof
      show "\<And>a b. a \<notin> Obj \<or> b \<notin> Obj \<Longrightarrow> hom\<^sub>a a b = null"
        by auto
      show "\<And>x. x \<in> Obj \<Longrightarrow> hom\<^sub>o x \<in> Collect ide"
        using y by auto
      show *: "\<And>a b. \<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow>
                        \<guillemotleft>hom\<^sub>a a b : Hom b a \<rightarrow> exp (hom\<^sub>o a) (hom\<^sub>o b)\<guillemotright>"
        using y C.cnt_Exp_ide C.Curry_in_hom Op.Comp_in_hom [of y] by simp
      show "\<And>a. a \<in> Obj \<Longrightarrow> hom\<^sub>a a a \<cdot> Id a = C.Id (hom\<^sub>o a)"
        using y Id_in_hom C.Id_def C.comp_Curry_arr Op.Comp_Id_Hom Op.Comp_in_hom
        by fastforce
      show "\<And>a b c. \<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj\<rbrakk> \<Longrightarrow>
                       C.Comp (hom\<^sub>o a) (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                         (hom\<^sub>a b c \<otimes> hom\<^sub>a a b) =
                       hom\<^sub>a a c \<cdot> Op.Comp\<^sub>o\<^sub>p a b c "
      proof -
        fix a b c
        assume a: "a \<in> Obj" and b: "b \<in> Obj" and c: "c \<in> Obj"
        have "C.Comp (hom\<^sub>o a) (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> (hom\<^sub>a b c \<otimes> hom\<^sub>a a b) =
              Curry[exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> exp (hom\<^sub>o a) (hom\<^sub>o b),
                    hom\<^sub>o a, hom\<^sub>o c]
                (eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                  (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                    \<a>[exp (hom\<^sub>o b) (hom\<^sub>o c), exp (hom\<^sub>o a) (hom\<^sub>o b), hom\<^sub>o a]) \<cdot>
                  (hom\<^sub>a b c \<otimes> hom\<^sub>a a b)"
          using y a b c comp_assoc C.Comp_def by simp
        also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           ((eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                              (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                                \<a>[exp (hom\<^sub>o b) (hom\<^sub>o c), exp (hom\<^sub>o a) (hom\<^sub>o b),
                                  hom\<^sub>o a]) \<cdot>
                              ((hom\<^sub>a b c \<otimes> hom\<^sub>a a b) \<otimes> hom\<^sub>o a))"
          using y a b c
                C.comp_Curry_arr
                  [of "Hom a y" "hom\<^sub>a b c \<otimes> hom\<^sub>a a b" "Hom c b \<otimes> Hom b a"
                       "exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> exp (hom\<^sub>o a) (hom\<^sub>o b)"
                       "eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                          (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                            \<a>[exp (hom\<^sub>o b) (hom\<^sub>o c), exp (hom\<^sub>o a) (hom\<^sub>o b), hom\<^sub>o a]"
                       "hom\<^sub>o c"]
          by fastforce
        also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           (eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                             (exp (hom\<^sub>o b) (hom\<^sub>o c) \<otimes> eval (hom\<^sub>o a) (hom\<^sub>o b)) \<cdot>
                               (hom\<^sub>a b c \<otimes> hom\<^sub>a a b \<otimes> hom\<^sub>o a) \<cdot>
                                 \<a>[Hom c b, Hom b a, hom\<^sub>o a])"
          using y a b c Op.Comp_in_hom comp_assoc
                C.assoc_naturality
                  [of "Curry[Hom c b, hom\<^sub>o b, hom\<^sub>o c] (Op.Comp\<^sub>o\<^sub>p y b c)"
                      "Curry[Hom b a, hom\<^sub>o a, hom\<^sub>o b] (Op.Comp\<^sub>o\<^sub>p y a b)"
                      "hom\<^sub>o a"]
          by auto
        also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           (eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                             (exp (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> hom\<^sub>a b c \<otimes>
                              Uncurry[hom\<^sub>o a, hom\<^sub>o b] (hom\<^sub>a a b)) \<cdot>
                               \<a>[Hom c b, Hom b a, hom\<^sub>o a])"
        proof -
          have "seq (exp (hom\<^sub>o b) (hom\<^sub>o c)) (hom\<^sub>a b c)"
            using y a b c by force
          moreover have "seq (eval (hom\<^sub>o a) (hom\<^sub>o b)) (hom\<^sub>a a b \<otimes> hom\<^sub>o a)"
            using y a b c by fastforce
          ultimately show ?thesis
            using y a b c comp_assoc
                  C.interchange
                    [of "exp (Hom b y) (Hom c y)" "hom\<^sub>a b c"
                        "eval (Hom a y) (Hom b y)" "hom\<^sub>a a b \<otimes> hom\<^sub>o a"]
            by metis
        qed
        also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           (eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                             (exp (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> hom\<^sub>a b c \<otimes> Op.Comp\<^sub>o\<^sub>p y a b) \<cdot>
                               \<a>[Hom c b, Hom b a, hom\<^sub>o a])"
          using y a b c C.Uncurry_Curry Op.Comp_in_hom by auto
        also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           (eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                              (hom\<^sub>a b c \<otimes> Op.Comp\<^sub>o\<^sub>p y a b) \<cdot>
                                \<a>[Hom c b, Hom b a, hom\<^sub>o a])"
          using y a b c
          by (simp add: comp_ide_arr Op.Comp_in_hom)
        also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           (eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                             (hom\<^sub>a b c \<cdot> Hom c b \<otimes> hom\<^sub>o b \<cdot> Op.Comp\<^sub>o\<^sub>p y a b) \<cdot>
                               \<a>[Hom c b, Hom b a, hom\<^sub>o a])"
          using y a b c *
          by (metis Op.Comp_in_hom comp_cod_arr comp_arr_dom in_homE)
         also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           (eval (hom\<^sub>o b) (hom\<^sub>o c) \<cdot>
                             ((hom\<^sub>a b c \<otimes> hom\<^sub>o b) \<cdot> (Hom c b \<otimes> Op.Comp\<^sub>o\<^sub>p y a b)) \<cdot>
                               \<a>[Hom c b, Hom b a, hom\<^sub>o a])"
          using y a b c *
                C.interchange [of "hom\<^sub>a b c" "Hom c b" "hom\<^sub>o b" "Op.Comp\<^sub>o\<^sub>p y a b"]
          by (metis Op.Comp_in_hom ide_Hom ide_char in_homE seqI)
        also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           (Uncurry[hom\<^sub>o b, hom\<^sub>o c] (hom\<^sub>a b c) \<cdot>
                              (Hom c b \<otimes> Op.Comp\<^sub>o\<^sub>p y a b) \<cdot>
                                \<a>[Hom c b, Hom b a, hom\<^sub>o a])"
          using comp_assoc by simp
        also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           (Op.Comp\<^sub>o\<^sub>p y b c \<cdot>
                             (Hom c b \<otimes> Op.Comp\<^sub>o\<^sub>p y a b) \<cdot>
                               \<a>[Hom c b, Hom b a, hom\<^sub>o a])"
          using y a b c C.Uncurry_Curry
          by (simp add: Op.Comp_in_hom)
        also have "... = Curry[Hom c b \<otimes> Hom b a, hom\<^sub>o a, hom\<^sub>o c]
                           (Op.Comp\<^sub>o\<^sub>p y a c \<cdot> (Op.Comp\<^sub>o\<^sub>p a b c \<otimes> hom\<^sub>o a))"
          using y a b c Op.Comp_assoc [of y a b c] by simp
        also have "... = hom\<^sub>a a c \<cdot> Op.Comp\<^sub>o\<^sub>p a b c"
          using y a b c C.comp_Curry_arr [of "Hom a y" "Op.Comp\<^sub>o\<^sub>p a b c"]
                ide_Hom Op.Comp_in_hom
          by fastforce
        finally
        show "C.Comp (hom\<^sub>o a) (hom\<^sub>o b) (hom\<^sub>o c) \<cdot> (hom\<^sub>a b c \<otimes> hom\<^sub>a a b) =
              hom\<^sub>a a c \<cdot> Op.Comp\<^sub>o\<^sub>p a b c"
          by blast
      qed
    qed

    lemma is_enriched_functor:
    shows "enriched_functor C T \<alpha> \<iota>
             Obj Op.Hom\<^sub>o\<^sub>p Id Op.Comp\<^sub>o\<^sub>p
             (Collect ide) exp C.Id C.Comp
             hom\<^sub>o hom\<^sub>a"
      ..

    sublocale C\<^sub>0: underlying_category C T \<alpha> \<iota> \<open>Collect ide\<close> exp C.Id C.Comp ..
    sublocale Op\<^sub>0: underlying_category C T \<alpha> \<iota> Obj Op.Hom\<^sub>o\<^sub>p Id Op.Comp\<^sub>o\<^sub>p ..
    sublocale UF: underlying_functor C T \<alpha> \<iota>
                    Obj Op.Hom\<^sub>o\<^sub>p Id Op.Comp\<^sub>o\<^sub>p
                    \<open>Collect ide\<close> exp C.Id C.Comp
                    hom\<^sub>o hom\<^sub>a
      ..

    text\<open>
      The following is Kelly's formula (1.32) for \<open>Hom\<^sup>\<leftarrow> f y : Hom b y \<rightarrow> Hom a y\<close>.
    \<close>

     lemma Kelly_1_32:
     assumes "a \<in> Obj" and "b \<in> Obj" and "\<guillemotleft>f : \<I> \<rightarrow> Hom a b\<guillemotright>"
     shows "C.frmUC (UF.map\<^sub>0 (Op\<^sub>0.MkArr b a f)) =
            Comp a b y \<cdot> (Hom b y \<otimes> f) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o b]"
     proof -
       have "C.frmUC (UF.map\<^sub>0 (Op\<^sub>0.MkArr b a f)) =
             (Curry[Hom a b, hom\<^sub>o b, hom\<^sub>o a] (Op.Comp\<^sub>o\<^sub>p y b a) \<cdot> f)
                \<^sup>\<down>[hom\<^sub>o b, hom\<^sub>o a]"
       proof -
         have "C.UC.arr (Op\<^sub>0.MkArr (Hom b y) (Hom a y)
                 (Curry[Hom a b, Hom b y, Hom a y] (Op.Comp\<^sub>o\<^sub>p y b a) \<cdot> f))"
           using assms y ide_Hom
           apply auto[1]
           using C.UC.arr_MkArr
                   [of "Hom b y" "Hom a y"
                       "Curry[Hom a b, hom\<^sub>o b, hom\<^sub>o a] (Op.Comp\<^sub>o\<^sub>p y b a) \<cdot> f"]
           by blast
         thus ?thesis
           using assms UF.map\<^sub>0_def Op\<^sub>0.arr_MkArr UF.preserves_arr by auto
       qed
       also have 1: "... = Curry[\<I>, hom\<^sub>o b, hom\<^sub>o a]
                             (Op.Comp\<^sub>o\<^sub>p y b a \<cdot> (f \<otimes> hom\<^sub>o b)) \<^sup>\<down>[hom\<^sub>o b, hom\<^sub>o a]"
       proof -
         have "Curry[Hom a b, Hom b y, Hom a y] (Op.Comp\<^sub>o\<^sub>p y b a) \<cdot> f =
               Curry[\<I>, Hom b y, Hom a y] (Op.Comp\<^sub>o\<^sub>p y b a \<cdot> (f \<otimes> Hom b y))"
           using assms y C.comp_Curry_arr by blast
         thus ?thesis by simp
       qed
       also have "... = (Op.Comp\<^sub>o\<^sub>p y b a \<cdot> (f \<otimes> Hom b y)) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"
       proof -
         have "arr (Curry[\<I>, Hom b y, Hom a y]
                      (Op.Comp\<^sub>o\<^sub>p y b a \<cdot> (f \<otimes> Hom b y)))"
           using assms y ide_Hom C.ide_unity
           by (metis 1 C.Curry_simps(1-3) C.DN_def C.DN_simps(1) cod_comp
               dom_comp in_homE not_arr_null seqI Op.Comp_in_hom)
         thus ?thesis
         unfolding C.DN_def
         using assms y ide_Hom C.ide_unity
               C.Uncurry_Curry
                 [of \<I> "Hom b y" "Hom a y" "Op.Comp\<^sub>o\<^sub>p y b a \<cdot> (f \<otimes> Hom b y)"]
         apply auto[1]
         by fastforce
       qed
       also have "... =
                  Comp a b y \<cdot> (\<s>[Hom a b, Hom b y] \<cdot> (f \<otimes> Hom b y)) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"
         using comp_assoc by simp
       also have "... = Comp a b y \<cdot> ((Hom b y \<otimes> f) \<cdot> \<s>[\<I>, Hom b y]) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"
         using assms y C.sym_naturality [of f "Hom b y"] by auto
       also have "... = Comp a b y \<cdot> (Hom b y \<otimes> f) \<cdot> \<s>[\<I>, Hom b y] \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"
         using comp_assoc by simp
       also have "... = Comp a b y \<cdot> (Hom b y \<otimes> f) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o b]"
       proof -
         have "\<r>\<^sup>-\<^sup>1[hom\<^sub>o b] = inv (\<l>[hom\<^sub>o b] \<cdot> \<s>[Hom b y, \<I>])"
            using assms y unitor_coherence by simp
         also have "... = \<s>[\<I>, Hom b y] \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o b]"
           using assms y
           by (metis C.ide_unity inv_comp_left(1) inverse_unique
               C.iso_lunit C.iso_runit C.sym_inverse C.unitor_coherence
               Op.ide_Hom)
         finally show ?thesis by simp
       qed
       finally show ?thesis by blast
     qed

     abbreviation map\<^sub>0
     where "map\<^sub>0 a b f \<equiv> Comp a b y \<cdot> (Hom b y \<otimes> f) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o b]"

  end

  context elementary_closed_symmetric_monoidal_category
  begin

    interpretation enriched_category C T \<alpha> \<iota> \<open>Collect ide\<close> exp Id Comp
      using is_enriched_in_itself by simp
    interpretation self_enriched_category C T \<alpha> \<iota> exp eval Curry ..

    sublocale Op: opposite_enriched_category C T \<alpha> \<iota> \<sigma> \<open>Collect ide\<close> exp Id Comp
      ..

    lemma cnt_Exp_DN:
    assumes "\<guillemotleft>f : \<I> \<rightarrow> exp a b\<guillemotright>"
    and "ide a" and "ide b" and "ide y"
    shows "Exp\<^sup>\<leftarrow> (f \<^sup>\<down>[a, b]) y =
           (Curry[exp a b, exp b y, exp a y] (Op.Comp\<^sub>o\<^sub>p y b a) \<cdot> f)
              \<^sup>\<down>[exp b y, exp a y]"
    proof -
      have "(Curry[exp a b, exp b y, exp a y] (Op.Comp\<^sub>o\<^sub>p y b a) \<cdot> f)
               \<^sup>\<down>[exp b y, exp a y] =
            Uncurry[exp b y, exp a y]
              (Curry[\<I>, exp b y, exp a y] (Op.Comp\<^sub>o\<^sub>p y b a \<cdot> (f \<otimes> exp b y))) \<cdot>
                 \<l>\<^sup>-\<^sup>1[exp b y]"
        using assms Op.Comp_in_hom DN_def comp_Curry_arr by force
      also have "... = (Op.Comp\<^sub>o\<^sub>p y b a \<cdot> (f \<otimes> exp b y)) \<cdot> \<l>\<^sup>-\<^sup>1[exp b y]"
        using assms Uncurry_Curry by auto
      also have "... = Comp a b y \<cdot> (\<s>[exp a b, exp b y] \<cdot> (f \<otimes> exp b y)) \<cdot>
                         \<l>\<^sup>-\<^sup>1[exp b y]"
        using comp_assoc by simp
      also have "... = Comp a b y \<cdot> ((exp b y \<otimes> f) \<cdot> \<s>[\<I>, exp b y]) \<cdot> \<l>\<^sup>-\<^sup>1[exp b y]"
        using assms sym_naturality [of f "exp b y"] by auto
      also have "... = Comp a b y \<cdot> (exp b y \<otimes> f) \<cdot> \<s>[\<I>, exp b y] \<cdot> \<l>\<^sup>-\<^sup>1[exp b y]"
        using comp_assoc by simp
      also have "... = Comp a b y \<cdot> (exp b y \<otimes> f) \<cdot> \<r>\<^sup>-\<^sup>1[exp b y]"
      proof -
        have "\<r>\<^sup>-\<^sup>1[exp b y] = inv (\<l>[exp b y] \<cdot> \<s>[exp b y, \<I>])"
          using assms unitor_coherence by auto
        also have "... = inv \<s>[exp b y, \<I>] \<cdot> \<l>\<^sup>-\<^sup>1[exp b y]"
          using assms inv_comp by simp
        also have "... = \<s>[\<I>, exp b y] \<cdot> \<l>\<^sup>-\<^sup>1[exp b y]"
          using assms
          by (metis ide_exp ide_unity inverse_unique sym_inverse)
        finally show ?thesis by simp
      qed
      also have "... = Curry[exp b y \<otimes> exp a b, a, y]
                         (eval b y \<cdot> (exp b y \<otimes> eval a b) \<cdot> \<a>[exp b y, exp a b, a]) \<cdot>
                            (exp b y \<otimes> f) \<cdot> \<r>\<^sup>-\<^sup>1[exp b y]"
        unfolding Comp_def by simp
      also have "... = Curry[exp b y, a, y]
                         ((eval b y \<cdot> (exp b y \<otimes> eval a b) \<cdot> \<a>[exp b y, exp a b, a]) \<cdot>
                            ((exp b y \<otimes> f) \<cdot> \<r>\<^sup>-\<^sup>1[exp b y] \<otimes> a))"
        using assms
              comp_Curry_arr
                [of a "(exp b y \<otimes> f) \<cdot> \<r>\<^sup>-\<^sup>1[exp b y]" "exp b y" "exp b y \<otimes> exp a b"
                    "eval b y \<cdot> (exp b y \<otimes> eval a b) \<cdot> \<a>[exp b y, exp a b, a]" y]
        by auto
      also have "... = Curry[exp b y, a, y]
                         ((eval b y \<cdot> (exp b y \<otimes> eval a b) \<cdot> \<a>[exp b y, exp a b, a]) \<cdot>
                            (((exp b y \<otimes> f) \<otimes> a) \<cdot> (\<r>\<^sup>-\<^sup>1[exp b y] \<otimes> a)))"
        using assms comp_arr_dom comp_cod_arr interchange by auto
      also have "... = Curry[exp b y, a, y]
                         (eval b y \<cdot> (exp b y \<otimes> eval a b) \<cdot>
                            (\<a>[exp b y, exp a b, a] \<cdot> ((exp b y \<otimes> f) \<otimes> a)) \<cdot>
                               (\<r>\<^sup>-\<^sup>1[exp b y] \<otimes> a))"
        using comp_assoc by simp
      also have "... = Curry[exp b y, a, y]
                         (eval b y \<cdot> (exp b y \<otimes> eval a b) \<cdot>
                            ((exp b y \<otimes> f \<otimes> a) \<cdot> \<a>[exp b y, \<I>, a]) \<cdot>
                               (\<r>\<^sup>-\<^sup>1[exp b y] \<otimes> a))"
        using assms assoc_naturality [of "exp b y" f a] by auto
      also have "... = Curry[exp b y, a, y]
                         (eval b y \<cdot>
                            ((exp b y \<otimes> eval a b) \<cdot> (exp b y \<otimes> f \<otimes> a)) \<cdot>
                               \<a>[exp b y, \<I>, a] \<cdot> (\<r>\<^sup>-\<^sup>1[exp b y] \<otimes> a))"
        using comp_assoc by simp
      also have "... = Curry[exp b y, a, y]
                         (eval b y \<cdot> (exp b y \<otimes> Uncurry[a, b] f) \<cdot>
                            \<a>[exp b y, \<I>, a] \<cdot> (\<r>\<^sup>-\<^sup>1[exp b y] \<otimes> a))"
        using assms comp_arr_dom comp_cod_arr interchange by simp
      also have "... = Curry[exp b y, a, y]
                         (eval b y \<cdot> (exp b y \<otimes> Uncurry[a, b] f) \<cdot> (exp b y \<otimes> \<l>\<^sup>-\<^sup>1[a]))"
      proof -
        have "exp b y \<otimes> \<l>\<^sup>-\<^sup>1[a] = inv ((\<r>[exp b y] \<otimes> a) \<cdot> \<a>\<^sup>-\<^sup>1[exp b y, \<I>, a])"
          using assms triangle' inv_inv iso_inv_iso
          by (metis ide_exp ide_is_iso inv_ide inv_tensor iso_lunit)
        also have "... = \<a>[exp b y, \<I>, a] \<cdot> (\<r>\<^sup>-\<^sup>1[exp b y] \<otimes> a)"
          using assms inv_comp by simp
        finally show ?thesis by simp
      qed
      also have "... = Curry[exp b y, a, y]
                         (eval b y \<cdot> (exp b y \<otimes> Uncurry[a, b] f \<cdot> \<l>\<^sup>-\<^sup>1[a]))"
        using assms comp_arr_dom comp_cod_arr interchange by fastforce
      also have "... = Exp\<^sup>\<leftarrow> (f \<^sup>\<down>[a, b]) y"
        using assms DN_def by auto
      finally show ?thesis by simp
    qed

  end

  section "Enriched Yoneda Lemma"

  text\<open>
    In this section we prove the (weak) Yoneda lemma for enriched categories,
    as in Kelly, Section 1.9.  The weakness is due to the fact that the lemma
    asserts only a bijection between sets, rather than an isomorphism of objects of
    the underlying base category.
  \<close>

  subsection "Preliminaries"

  text\<open>
    The following gives conditions under which \<open>\<tau>\<close> defined as \<open>\<tau> x = (\<T> x)\<^sup>\<up>\<close>
    yields an enriched natural transformation between enriched functors \<open>F\<close> and \<open>G\<close>
    to the self-enriched base category.
  \<close>

  context elementary_closed_monoidal_category
  begin

    lemma transformation_lam_UP:
    assumes "enriched_functor C T \<alpha> \<iota>
               Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A (Collect ide) exp Id Comp F\<^sub>o F\<^sub>a"
    assumes "enriched_functor C T \<alpha> \<iota>
               Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A (Collect ide) exp Id Comp G\<^sub>o G\<^sub>a"
    and "\<And>x. x \<notin> Obj\<^sub>A \<Longrightarrow> \<T> x = null"
    and "\<And>x. x \<in> Obj\<^sub>A \<Longrightarrow> \<guillemotleft>\<T> x : F\<^sub>o x \<rightarrow> G\<^sub>o x\<guillemotright>"
    and "\<And>a b. \<lbrakk>a \<in> Obj\<^sub>A; b \<in> Obj\<^sub>A\<rbrakk> \<Longrightarrow>
                  \<T> b \<cdot> Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b) =
                  eval (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> \<T> a)"
    shows "enriched_natural_transformation C T \<alpha> \<iota>
             Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A (Collect ide) exp Id Comp
             F\<^sub>o F\<^sub>a G\<^sub>o G\<^sub>a (\<lambda>x. (\<T> x)\<^sup>\<up>)"
    proof -
      interpret F: enriched_functor C T \<alpha> \<iota>
                     Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A \<open>Collect ide\<close> exp Id Comp F\<^sub>o F\<^sub>a
        using assms(1) by blast
      interpret G: enriched_functor C T \<alpha> \<iota>
                     Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A \<open>Collect ide\<close> exp Id Comp G\<^sub>o G\<^sub>a
        using assms(2) by blast
      show ?thesis
      proof
        show "\<And>x. x \<notin> Obj\<^sub>A \<Longrightarrow> (\<T> x)\<^sup>\<up> = null"
          unfolding UP_def
          using assms(3) by auto
        show "\<And>x. x \<in> Obj\<^sub>A \<Longrightarrow> \<guillemotleft>(\<T> x)\<^sup>\<up> : \<I> \<rightarrow> exp (F\<^sub>o x) (G\<^sub>o x)\<guillemotright>"
          unfolding UP_def
          using assms(4)
          apply auto[1]
          by force
        fix a b
        assume a: "a \<in> Obj\<^sub>A" and b: "b \<in> Obj\<^sub>A"
        have 1: "\<guillemotleft>((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]
                     : Hom\<^sub>A a b \<rightarrow> exp (F\<^sub>o b) (G\<^sub>o b) \<otimes> exp (F\<^sub>o a) (F\<^sub>o b)\<guillemotright>"
          using assms(4) [of b] a b UP_DN F.preserves_Hom
          apply (intro comp_in_homI tensor_in_homI)
              apply auto[5]
          by fastforce
        have 2: "\<guillemotleft>(G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]
                     : Hom\<^sub>A a b \<rightarrow> exp (G\<^sub>o a) (G\<^sub>o b) \<otimes> exp (F\<^sub>o a) (G\<^sub>o a)\<guillemotright>"
          using assms(4) [of a] a b UP_DN F.preserves_Obj G.preserves_Hom
          apply (intro comp_in_homI tensor_in_homI)
              apply auto[5]
          by fastforce
        have 3: "\<guillemotleft>Comp (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot> ((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]
                    : Hom\<^sub>A a b \<rightarrow> exp (F\<^sub>o a) (G\<^sub>o b)\<guillemotright>"
          using a b 1 F.preserves_Obj G.preserves_Obj by blast
        have 4: "\<guillemotleft>Comp (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]
                    : Hom\<^sub>A a b \<rightarrow> exp (F\<^sub>o a) (G\<^sub>o b)\<guillemotright>"
          using a b 2 F.preserves_Obj G.preserves_Obj by blast

        have "Uncurry[F\<^sub>o a, G\<^sub>o b]
                (Comp (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                   ((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]) =
              Uncurry[F\<^sub>o a, G\<^sub>o b]
                (Curry[exp (F\<^sub>o b) (G\<^sub>o b) \<otimes> exp (F\<^sub>o a) (F\<^sub>o b), F\<^sub>o a, G\<^sub>o b]
                  (eval (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                     (exp (F\<^sub>o b) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (F\<^sub>o b)) \<cdot>
                        \<a>[exp (F\<^sub>o b) (G\<^sub>o b), exp (F\<^sub>o a) (F\<^sub>o b), F\<^sub>o a]) \<cdot>
                    ((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b])"
          using a b Comp_def comp_assoc by auto
        also have "... =
              Uncurry[F\<^sub>o a, G\<^sub>o b]
                (Curry[Hom\<^sub>A a b, F\<^sub>o a, G\<^sub>o b]
                   ((eval (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                      (exp (F\<^sub>o b) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (F\<^sub>o b)) \<cdot>
                         \<a>[exp (F\<^sub>o b) (G\<^sub>o b), exp (F\<^sub>o a) (F\<^sub>o b), F\<^sub>o a]) \<cdot>
                           (((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)))"
          using a b 1 F.preserves_Obj G.preserves_Obj comp_Curry_arr by auto
        also have "... =
                   (eval (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                      (exp (F\<^sub>o b) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (F\<^sub>o b)) \<cdot>
                         \<a>[exp (F\<^sub>o b) (G\<^sub>o b), exp (F\<^sub>o a) (F\<^sub>o b), F\<^sub>o a]) \<cdot>
                           (((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using a b 1 F.preserves_Obj G.preserves_Obj Uncurry_Curry by auto
        also have "... =
                   (eval (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                      (exp (F\<^sub>o b) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (F\<^sub>o b)) \<cdot>
                         \<a>[exp (F\<^sub>o b) (G\<^sub>o b), exp (F\<^sub>o a) (F\<^sub>o b), F\<^sub>o a]) \<cdot>
                           ((((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<otimes> F\<^sub>o a) \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a))"
        proof -
          have "seq ((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
            using assms(4) a b 1 F.preserves_Hom [of a b] UP_DN
            apply (intro seqI)
              apply auto[2]
            by (metis F.A.ide_Hom arrI cod_inv dom_lunit iso_lunit seqE)
          thus ?thesis
            using assms(3) a b F.preserves_Obj F.preserves_Hom interchange
            by simp
        qed
        also have "... =
                   eval (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                      (exp (F\<^sub>o b) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (F\<^sub>o b)) \<cdot>
                         (\<a>[exp (F\<^sub>o b) (G\<^sub>o b), exp (F\<^sub>o a) (F\<^sub>o b), F\<^sub>o a] \<cdot>
                           (((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<otimes> F\<^sub>o a)) \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using comp_assoc by simp
        also have "... =
                   eval (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                      (exp (F\<^sub>o b) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (F\<^sub>o b)) \<cdot>
                         (((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b \<otimes> F\<^sub>o a) \<cdot>
                           \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a]) \<cdot>
                             (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using assms(4) a b F.preserves_Obj F.preserves_Hom
                assoc_naturality [of "(\<T> b)\<^sup>\<up>" "F\<^sub>a a b" "F\<^sub>o a"]
          by force
        also have "... =
                   eval (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                      ((exp (F\<^sub>o b) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (F\<^sub>o b)) \<cdot>
                         ((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b \<otimes> F\<^sub>o a)) \<cdot>
                           \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using comp_assoc by simp
        also have "... =
                   eval (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                      ((\<T> b)\<^sup>\<up> \<otimes> Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b)) \<cdot>
                           \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
        proof -
          have "seq (exp (F\<^sub>o b) (G\<^sub>o b)) (UP (\<T> b))"
            using assms(4) b F.preserves_Obj G.preserves_Obj by fastforce
          moreover have "seq (eval (F\<^sub>o a) (F\<^sub>o b)) (F\<^sub>a a b \<otimes> F\<^sub>o a)"
            using a b F.preserves_Obj F.preserves_Hom by force
          ultimately show ?thesis
            using assms(4) [of b] a b UP_DN(1) comp_cod_arr interchange by auto
        qed
        also have "... =
                   eval (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                      (((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>o b) \<cdot> (\<I> \<otimes> Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b))) \<cdot>
                           \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using assms(4) [of b] a b F.preserves_Obj F.preserves_Hom [of a b]
                comp_arr_dom comp_cod_arr [of "Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b)"]
                interchange [of "(\<T> b)\<^sup>\<up>" \<I> "F\<^sub>o b" "Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b)"]
          by auto
        also have "... =
                   Uncurry[F\<^sub>o b, G\<^sub>o b] ((\<T> b)\<^sup>\<up>) \<cdot>
                      (\<I> \<otimes> Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b)) \<cdot>
                         \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using comp_assoc by simp
        also have "... = (\<T> b \<cdot> \<l>[F\<^sub>o b]) \<cdot>
                           (\<I> \<otimes> Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b)) \<cdot>
                             \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
        proof -
          have "Uncurry[F\<^sub>o b, G\<^sub>o b] ((\<T> b)\<^sup>\<up>) = \<T> b \<cdot> \<l>[F\<^sub>o b]"
            unfolding UP_def
            using assms(4) a b Uncurry_Curry
            apply simp
            by (metis F.preserves_Obj arr_lunit cod_lunit comp_in_homI' dom_lunit
                ide_cod ide_unity in_homE mem_Collect_eq)
          thus ?thesis by simp
        qed
        also have "... = \<T> b \<cdot> (\<l>[F\<^sub>o b] \<cdot> (\<I> \<otimes> Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b))) \<cdot>
                             \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using comp_assoc by simp
        also have "... = \<T> b \<cdot> (Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b) \<cdot> \<l>[Hom\<^sub>A a b \<otimes> F\<^sub>o a]) \<cdot>
                             \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using a b lunit_naturality [of "Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b)"]
                F.preserves_Obj F.preserves_Hom [of a b]
          by auto
        also have "... = \<T> b \<cdot> Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b) \<cdot>
                           \<l>[Hom\<^sub>A a b \<otimes> F\<^sub>o a] \<cdot> \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot>
                             (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using comp_assoc by simp
        also have "... = \<T> b \<cdot> Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b)"
        proof -
          have "\<l>[Hom\<^sub>A a b \<otimes> F\<^sub>o a] \<cdot> \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot>
                  (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a) =
                Hom\<^sub>A a b \<otimes> F\<^sub>o a"
          proof -
            have "\<l>[Hom\<^sub>A a b \<otimes> F\<^sub>o a] \<cdot> \<a>[\<I>, Hom\<^sub>A a b, F\<^sub>o a] \<cdot>
                    (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a) =
                  (\<l>[Hom\<^sub>A a b] \<otimes> F\<^sub>o a) \<cdot> (\<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
              using a b lunit_tensor' [of "Hom\<^sub>A a b" "F\<^sub>o a"]
              by (metis F.A.ide_Hom F.preserves_Obj comp_assoc mem_Collect_eq)
            also have "... = \<l>[Hom\<^sub>A a b] \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a \<cdot> F\<^sub>o a"
              using a b interchange F.preserves_Obj by force
            also have "... = Hom\<^sub>A a b \<otimes> F\<^sub>o a"
              using a b F.preserves_Obj by auto
            finally show ?thesis by blast
          qed
          thus ?thesis
            using a b F.preserves_Obj F.preserves_Hom [of a b] comp_arr_dom
            by auto
        qed
        finally have LHS: "Uncurry[F\<^sub>o a, G\<^sub>o b]
                             (Comp (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot> ((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot>
                                \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]) =
                           \<T> b \<cdot> Uncurry[F\<^sub>o a, F\<^sub>o b] (F\<^sub>a a b)"
          by blast

        have "Uncurry[F\<^sub>o a, G\<^sub>o b] (Comp (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                (G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]) =
              Uncurry[F\<^sub>o a, G\<^sub>o b]
                (Curry[exp (G\<^sub>o a) (G\<^sub>o b) \<otimes> exp (F\<^sub>o a) (G\<^sub>o a), F\<^sub>o a, G\<^sub>o b]
                  (eval (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                    (exp (G\<^sub>o a) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (G\<^sub>o a)) \<cdot>
                      \<a>[exp (G\<^sub>o a) (G\<^sub>o b), exp (F\<^sub>o a) (G\<^sub>o a), F\<^sub>o a]) \<cdot>
                    (G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b])"
          using a b Comp_def comp_assoc by auto
        also have "... =
              Uncurry[F\<^sub>o a, G\<^sub>o b]
                (Curry[Hom\<^sub>A a b, F\<^sub>o a, G\<^sub>o b]
                  ((eval (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                     (exp (G\<^sub>o a) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (G\<^sub>o a)) \<cdot>
                       \<a>[exp (G\<^sub>o a) (G\<^sub>o b), exp (F\<^sub>o a) (G\<^sub>o a), F\<^sub>o a]) \<cdot>
                        ((G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)))"
          using assms(3) a b 2 F.preserves_Obj G.preserves_Obj comp_Curry_arr
          by auto
        also have "... =
                  (eval (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                     (exp (G\<^sub>o a) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (G\<^sub>o a)) \<cdot>
                       \<a>[exp (G\<^sub>o a) (G\<^sub>o b), exp (F\<^sub>o a) (G\<^sub>o a), F\<^sub>o a]) \<cdot>
                        ((G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using assms(3) a b 2 F.preserves_Obj G.preserves_Obj Uncurry_Curry
          by auto
        also have "... =
                  (eval (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                     (exp (G\<^sub>o a) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (G\<^sub>o a)) \<cdot>
                       \<a>[exp (G\<^sub>o a) (G\<^sub>o b), exp (F\<^sub>o a) (G\<^sub>o a), F\<^sub>o a]) \<cdot>
                        (((G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<otimes> F\<^sub>o a) \<cdot> (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a))"
          using assms(4) a b F.preserves_Obj G.preserves_Hom
                interchange [of "G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>" "\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]" "F\<^sub>o a" "F\<^sub>o a"]
          by fastforce
        also have "... =
                  eval (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                    (exp (G\<^sub>o a) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (G\<^sub>o a)) \<cdot>
                      (\<a>[exp (G\<^sub>o a) (G\<^sub>o b), exp (F\<^sub>o a) (G\<^sub>o a), F\<^sub>o a] \<cdot>
                         ((G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<otimes> F\<^sub>o a)) \<cdot> (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using comp_assoc by simp
        also have "... =
                  eval (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                    (exp (G\<^sub>o a) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (G\<^sub>o a)) \<cdot>
                      ((G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up> \<otimes> F\<^sub>o a) \<cdot>
                         \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a]) \<cdot>
                           (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using assms(4) a b F.preserves_Obj G.preserves_Hom
                assoc_naturality [of "G\<^sub>a a b" "(\<T> a)\<^sup>\<up>" "F\<^sub>o a"]
          by fastforce
        also have "... =
                  eval (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                    ((exp (G\<^sub>o a) (G\<^sub>o b) \<otimes> eval (F\<^sub>o a) (G\<^sub>o a)) \<cdot>
                       (G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up> \<otimes> F\<^sub>o a)) \<cdot>
                         \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a] \<cdot> (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using comp_assoc by simp
        also have "... =
                  eval (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                    (G\<^sub>a a b \<otimes> Uncurry[F\<^sub>o a, G\<^sub>o a] ((\<T> a)\<^sup>\<up>)) \<cdot>
                       \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a] \<cdot> (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using assms(4) a b F.preserves_Obj G.preserves_Obj
                G.preserves_Hom [of a b] comp_cod_arr interchange
          by fastforce
        also have "... =
                  eval (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                    ((G\<^sub>a a b \<otimes> G\<^sub>o a) \<cdot> (Hom\<^sub>A a b \<otimes> Uncurry[F\<^sub>o a, G\<^sub>o a] ((\<T> a)\<^sup>\<up>))) \<cdot>
                       \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a] \<cdot> (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
        proof -
          have "seq (G\<^sub>o a) (Uncurry[F\<^sub>o a, G\<^sub>o a] ((\<T> a)\<^sup>\<up>))"
            using assms(4) [of a] a b F.preserves_Obj G.preserves_Obj by auto
          moreover have "G\<^sub>o a \<cdot> Uncurry[F\<^sub>o a, G\<^sub>o a] ((\<T> a)\<^sup>\<up>) =
                         Uncurry[F\<^sub>o a, G\<^sub>o a] ((\<T> a)\<^sup>\<up>)"
            using a b F.preserves_Obj G.preserves_Obj calculation(1)
                  comp_ide_arr
            by blast
          ultimately show ?thesis
            using assms(3) a b G.preserves_Hom [of a b] interchange
                  comp_arr_dom
            by auto
        qed
        also have "... =
                  Uncurry[G\<^sub>o a, G\<^sub>o b] (G\<^sub>a a b) \<cdot>
                     (Hom\<^sub>A a b \<otimes> Uncurry[F\<^sub>o a, G\<^sub>o a] ((\<T> a)\<^sup>\<up>)) \<cdot>
                       \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a] \<cdot> (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using comp_assoc by simp
        also have "... =
                  Uncurry[G\<^sub>o a, G\<^sub>o b] (G\<^sub>a a b) \<cdot>
                     (Hom\<^sub>A a b \<otimes> \<T> a \<cdot> \<l>[F\<^sub>o a]) \<cdot>
                       \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a] \<cdot> (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using assms(4) [of a] a b F.preserves_Obj G.preserves_Obj UP_def
                Uncurry_Curry
          by auto
        also have "... =
                  Uncurry[G\<^sub>o a, G\<^sub>o b] (G\<^sub>a a b) \<cdot>
                     ((Hom\<^sub>A a b \<otimes> \<T> a) \<cdot> (Hom\<^sub>A a b \<otimes> \<l>[F\<^sub>o a])) \<cdot>
                       \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a] \<cdot> (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using assms(4) [of a] a b F.preserves_Obj G.preserves_Obj interchange
          by auto
        also have "... =
                  Uncurry[G\<^sub>o a, G\<^sub>o b] (G\<^sub>a a b) \<cdot> (Hom\<^sub>A a b \<otimes> \<T> a) \<cdot>
                    (Hom\<^sub>A a b \<otimes> \<l>[F\<^sub>o a]) \<cdot> \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a] \<cdot>
                       (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
          using comp_assoc by simp
        also have "... = Uncurry[G\<^sub>o a, G\<^sub>o b] (G\<^sub>a a b) \<cdot> (Hom\<^sub>A a b \<otimes> \<T> a)"
        proof -
          have "(Hom\<^sub>A a b \<otimes> \<l>[F\<^sub>o a]) \<cdot> \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a] \<cdot>
                   (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a) =
                Hom\<^sub>A a b \<otimes> F\<^sub>o a"
          proof -
            have "(Hom\<^sub>A a b \<otimes> \<l>[F\<^sub>o a]) \<cdot> \<a>[Hom\<^sub>A a b, \<I>, F\<^sub>o a] \<cdot>
                     (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a) =
                  (\<r>[Hom\<^sub>A a b] \<otimes> F\<^sub>o a) \<cdot> (\<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a)"
              using a b triangle [of "Hom\<^sub>A a b" "F\<^sub>o a"]
              by (metis F.A.ide_Hom F.preserves_Obj comp_assoc mem_Collect_eq)
            also have "... = \<r>[Hom\<^sub>A a b] \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b] \<otimes> F\<^sub>o a \<cdot> F\<^sub>o a"
              using a b interchange F.preserves_Obj by force
            also have "... = Hom\<^sub>A a b \<otimes> F\<^sub>o a"
              using a b F.preserves_Obj by auto
            finally show ?thesis by blast
          qed
          thus ?thesis
            using assms(4) [of a] a b comp_arr_dom by auto
        qed
        also have "... = eval (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> G\<^sub>o a) \<cdot> (Hom\<^sub>A a b \<otimes> \<T> a)"
          using comp_assoc by auto
        also have "... = eval (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> \<T> a)"
          using assms(4) a b G.preserves_Hom comp_arr_dom comp_cod_arr
                interchange
          by (metis in_homE)
        finally have RHS: "Uncurry[F\<^sub>o a, G\<^sub>o b]
                             (Comp (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot>
                                \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]) =
                           eval (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> \<T> a)"
          by blast

        have "Uncurry[F\<^sub>o a, G\<^sub>o b]
                (Comp (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot> ((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]) =
              Uncurry[F\<^sub>o a, G\<^sub>o b]
                (Comp (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b])"
          using a b assms(5) LHS RHS by simp
        moreover have "\<guillemotleft>Comp (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                          ((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]
                          : Hom\<^sub>A a b \<rightarrow> exp (F\<^sub>o a) (G\<^sub>o b)\<guillemotright>"
            using assms(4) a b 1 F.preserves_Obj G.preserves_Obj
                  F.preserves_Hom G.preserves_Hom
            apply (intro comp_in_homI' seqI)
                  apply auto[1]
            by fastforce+
        moreover have "\<guillemotleft>Comp (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                          (G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]
                          : Hom\<^sub>A a b \<rightarrow> exp (F\<^sub>o a) (G\<^sub>o b)\<guillemotright>"
            using assms(4) a b 2 UP_DN(1) F.preserves_Obj G.preserves_Obj
                  F.preserves_Hom G.preserves_Hom [of a b]
            apply (intro comp_in_homI' seqI)
                  apply auto[7]
            by fastforce
        ultimately show "Comp (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                           ((\<T> b)\<^sup>\<up> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b] =
                         Comp (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                           (G\<^sub>a a b \<otimes> (\<T> a)\<^sup>\<up>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
          using a b Curry_Uncurry F.A.ide_Hom F.preserves_Obj
                G.preserves_Obj mem_Collect_eq
          by metis
      qed
    qed

  end

  text\<open>
    Kelly (1.39) expresses enriched naturality in an alternate form, using the underlying
    functors of the covariant and contravariant enriched hom functors.
  \<close>

  locale Kelly_1_39 =
    symmetric_monoidal_category +
    elementary_closed_monoidal_category +
    enriched_natural_transformation
    for a :: 'a
    and b :: 'a +
    assumes a: "a \<in> Obj\<^sub>A"
    and b: "b \<in> Obj\<^sub>A"
  begin

    interpretation enriched_category C T \<alpha> \<iota> \<open>Collect ide\<close> exp Id Comp
      using is_enriched_in_itself by blast
    interpretation self_enriched_category C T \<alpha> \<iota> exp eval Curry
      ..

    sublocale cov_Hom: covariant_Hom C T \<alpha> \<iota>
                         exp eval Curry Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B \<open>F\<^sub>o a\<close>
      using a F.preserves_Obj by unfold_locales
    sublocale cnt_Hom: contravariant_Hom C T \<alpha> \<iota> \<sigma>
                         exp eval Curry Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B \<open>G\<^sub>o b\<close>
      using b G.preserves_Obj by unfold_locales

    lemma Kelly_1_39:
    shows "cov_Hom.map\<^sub>0 (F\<^sub>o b) (G\<^sub>o b) (\<tau> b) \<cdot> F\<^sub>a a b =
           cnt_Hom.map\<^sub>0 (F\<^sub>o a) (G\<^sub>o a) (\<tau> a) \<cdot> G\<^sub>a a b"
    proof -
      have "cov_Hom.map\<^sub>0 (F\<^sub>o b) (G\<^sub>o b) (\<tau> b) \<cdot> F\<^sub>a a b =
            Comp\<^sub>B (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot> (\<tau> b \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
      proof -
        have "cov_Hom.map\<^sub>0 (F\<^sub>o b) (G\<^sub>o b) (\<tau> b) \<cdot> F\<^sub>a a b =
              Comp\<^sub>B (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                (\<tau> b \<otimes> Hom\<^sub>B (F\<^sub>o a) (F\<^sub>o b)) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>B (F\<^sub>o a) (F\<^sub>o b)] \<cdot> F\<^sub>a a b"
          using comp_assoc by simp
        also have "... = Comp\<^sub>B (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                            (\<tau> b \<otimes> Hom\<^sub>B (F\<^sub>o a) (F\<^sub>o b)) \<cdot> (\<I> \<otimes> F\<^sub>a a b) \<cdot> \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
          using a b lunit'_naturality F.preserves_Hom [of a b] by fastforce
        also have "... = Comp\<^sub>B (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot>
                            ((\<tau> b \<otimes> Hom\<^sub>B (F\<^sub>o a) (F\<^sub>o b)) \<cdot> (\<I> \<otimes> F\<^sub>a a b)) \<cdot>
                               \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
          using comp_assoc by simp
        also have "... = Comp\<^sub>B (F\<^sub>o a) (F\<^sub>o b) (G\<^sub>o b) \<cdot> (\<tau> b \<otimes> F\<^sub>a a b) \<cdot>
                           \<l>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
          using a b component_in_hom [of b] F.preserves_Hom [of a b]
                comp_arr_dom comp_cod_arr [of "F\<^sub>a a b" "Hom\<^sub>B (F\<^sub>o a) (F\<^sub>o b)"]
                interchange
          by fastforce
        finally show ?thesis by blast
      qed
      moreover have "cnt_Hom.map\<^sub>0 (F\<^sub>o a) (G\<^sub>o a) (\<tau> a) \<cdot> G\<^sub>a a b =
                     Comp\<^sub>B (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> \<tau> a) \<cdot> \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
      proof -
        have "cnt_Hom.map\<^sub>0 (F\<^sub>o a) (G\<^sub>o a) (\<tau> a) \<cdot> G\<^sub>a a b =
              Comp\<^sub>B (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot> (Hom\<^sub>B (G\<^sub>o a) (G\<^sub>o b) \<otimes> \<tau> a) \<cdot>
                 \<r>\<^sup>-\<^sup>1[Hom\<^sub>B (G\<^sub>o a) (G\<^sub>o b)] \<cdot> G\<^sub>a a b"
          using comp_assoc by simp
        also have "... = Comp\<^sub>B (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                           (Hom\<^sub>B (G\<^sub>o a) (G\<^sub>o b) \<otimes> \<tau> a) \<cdot> (G\<^sub>a a b \<otimes> \<I>) \<cdot>
                              \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
          using a b runit'_naturality G.preserves_Hom [of a b] by fastforce
        also have "... = Comp\<^sub>B (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot>
                           ((Hom\<^sub>B (G\<^sub>o a) (G\<^sub>o b) \<otimes> \<tau> a) \<cdot> (G\<^sub>a a b \<otimes> \<I>)) \<cdot>
                               \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
          using comp_assoc by simp
        also have "... = Comp\<^sub>B (F\<^sub>o a) (G\<^sub>o a) (G\<^sub>o b) \<cdot> (G\<^sub>a a b \<otimes> \<tau> a) \<cdot>
                           \<r>\<^sup>-\<^sup>1[Hom\<^sub>A a b]"
          using a b interchange component_in_hom [of a] G.preserves_Hom [of a b]
                comp_arr_dom comp_cod_arr [of "G\<^sub>a a b" "Hom\<^sub>B (G\<^sub>o a) (G\<^sub>o b)"]
          by fastforce
        finally show ?thesis by blast
      qed
      ultimately show ?thesis
        using a b naturality by simp
    qed

  end

  subsection "Covariant Case"

  locale covariant_yoneda_lemma =
    symmetric_monoidal_category +
    C: closed_symmetric_monoidal_category +
    covariant_Hom +
    F: enriched_functor C T \<alpha> \<iota> Obj Hom Id Comp \<open>Collect ide\<close> exp C.Id C.Comp
  begin

    interpretation C: elementary_closed_symmetric_monoidal_category C T \<alpha> \<iota> \<sigma> exp eval Curry ..
    interpretation C: self_enriched_category C T \<alpha> \<iota> exp eval Curry ..
 
    text\<open>
      Every element \<open>e : \<I> \<rightarrow> F\<^sub>o x\<close> of \<open>F\<^sub>o x\<close> determines an enriched natural transformation
      \<open>\<tau>\<^sub>e: hom x - \<rightarrow> F\<close>.  The formula here is Kelly (1.47): \<open>\<tau>\<^sub>e y: hom x y \<rightarrow> F y\<close>
      is obtained as the composite:
      \[
        \<open>hom x y\<close> \labarrow{\<open>F\<^sub>a x y\<close>} \<open>exp (F x) (F y)\<close>
                  \labarrow{\<open>Exp\<^sup>\<leftarrow> e (F y)\<close>} \<open>exp \<I> (F y)\<close> \labarrow{} \<open>F y\<close>
      \]
      where the third component is a canonical isomorphism.
      This basically amounts to evaluating \<open>F\<^sub>a x y\<close> on element \<open>e\<close> of \<open>F\<^sub>o x\<close> to obtain
      an element of \<open>F\<^sub>o y\<close>.

      Note that the above composite gives an arrow \<open>\<tau>\<^sub>e y: hom x y \<rightarrow> F y\<close>, whereas the
      definition of enriched natural transformation formally requires
      \<open>\<tau>\<^sub>e y: \<I> \<rightarrow> exp (hom x y) (F y)\<close>.
      So we need to transform the composite to achieve that.
    \<close>

    abbreviation generated_transformation
    where "generated_transformation e \<equiv>
           \<lambda>y. (eval \<I> (F\<^sub>o y) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o y)] \<cdot> Exp\<^sup>\<leftarrow> e (F\<^sub>o y) \<cdot> F\<^sub>a x y)\<^sup>\<up>"

    lemma enriched_natural_transformation_generated_transformation:
    assumes "\<guillemotleft>e : \<I> \<rightarrow> F\<^sub>o x\<guillemotright>"
    shows "enriched_natural_transformation C T \<alpha> \<iota>
             Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
             hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a (generated_transformation e)"
    proof (intro C.transformation_lam_UP)
      show "\<And>y. y \<notin> Obj \<Longrightarrow>
                  eval \<I> (F\<^sub>o y) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o y)] \<cdot> Exp\<^sup>\<leftarrow> e (F\<^sub>o y) \<cdot> F\<^sub>a x y = null"
        by (simp add: F.extensionality)
      show "enriched_functor (\<cdot>) T \<alpha> \<iota> Obj Hom Id Comp
              (Collect ide) exp C.Id C.Comp hom\<^sub>o hom\<^sub>a"
        ..
      show "enriched_functor (\<cdot>) T \<alpha> \<iota> Obj Hom Id Comp
              (Collect ide) exp C.Id C.Comp F\<^sub>o F\<^sub>a"
        ..
      show *: "\<And>y. y \<in> Obj \<Longrightarrow>
                     \<guillemotleft>eval \<I> (F\<^sub>o y) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o y)] \<cdot> Exp\<^sup>\<leftarrow> e (F\<^sub>o y) \<cdot> F\<^sub>a x y
                        : hom\<^sub>o y \<rightarrow> F\<^sub>o y\<guillemotright>"
        using assms x F.preserves_Obj F.preserves_Hom
        apply (intro in_homI seqI)
                apply auto[6]
        by fastforce+
      show "\<And>a b. \<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow>
                    (eval \<I> (F\<^sub>o b) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o b)] \<cdot>
                       Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<cdot> F\<^sub>a x b) \<cdot>
                         Uncurry[hom\<^sub>o a, hom\<^sub>o b] (hom\<^sub>a a b) =
                    eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                      (F\<^sub>a a b \<otimes> eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                         Exp\<^sup>\<leftarrow> e (F\<^sub>o a) \<cdot> F\<^sub>a x a)"
      proof -
        fix a b
        assume a: "a \<in> Obj" and b: "b \<in> Obj"
        have "(eval \<I> (F\<^sub>o b) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o b)] \<cdot>
                 Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<cdot> F\<^sub>a x b) \<cdot> Uncurry[hom\<^sub>o a, hom\<^sub>o b] (hom\<^sub>a a b) =
              eval (F\<^sub>o x) (F\<^sub>o b) \<cdot> (F\<^sub>a x b \<cdot> Comp x a b \<otimes> e) \<cdot>
                \<r>\<^sup>-\<^sup>1[Hom a b \<otimes> hom\<^sub>o a]"
        proof -
          have "(eval \<I> (F\<^sub>o b) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o b)] \<cdot>
                   Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<cdot> F\<^sub>a x b) \<cdot> Uncurry[hom\<^sub>o a, hom\<^sub>o b] (hom\<^sub>a a b) =
                eval \<I> (F\<^sub>o b) \<cdot>
                   (\<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o b)] \<cdot> Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<cdot> F\<^sub>a x b) \<cdot>
                      Uncurry[hom\<^sub>o a, hom\<^sub>o b] (hom\<^sub>a a b)"
            using comp_assoc by simp
          also have "... = eval \<I> (F\<^sub>o b) \<cdot>
                             (\<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o b)] \<cdot> Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<cdot> F\<^sub>a x b) \<cdot>
                               Comp x a b"
            using a b x C.Uncurry_Curry [of _ "hom\<^sub>o a" "hom\<^sub>o b"] Comp_in_hom
            by auto
          also have "... = eval \<I> (F\<^sub>o b) \<cdot>
                             ((Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<cdot> F\<^sub>a x b \<otimes> \<I>) \<cdot>
                                 \<r>\<^sup>-\<^sup>1[hom\<^sub>o b]) \<cdot> Comp x a b"
          proof -
            have "\<guillemotleft>Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<cdot> F\<^sub>a x b : hom\<^sub>o b \<rightarrow> exp \<I> (F\<^sub>o b)\<guillemotright>"
              using assms a b x F.preserves_Obj F.preserves_Hom [of x b] by force
            thus ?thesis
              using a b F.preserves_Obj F.preserves_Hom
                    runit'_naturality [of "Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<cdot> F\<^sub>a x b"]
              by auto
          qed
          also have "... = eval \<I> (F\<^sub>o b) \<cdot>
                             (((Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<otimes> \<I>) \<cdot> (F\<^sub>a x b \<otimes> \<I>)) \<cdot>
                                  \<r>\<^sup>-\<^sup>1[hom\<^sub>o b]) \<cdot>
                               Comp x a b"
            using assms a b x F.preserves_Obj F.preserves_Hom [of x b]
                  interchange [of "Exp\<^sup>\<leftarrow> e (F\<^sub>o b)" "F\<^sub>a x b" \<I> \<I>]
            by fastforce
          also have "... = Uncurry[\<I>, F\<^sub>o b] (Exp\<^sup>\<leftarrow> e (F\<^sub>o b)) \<cdot> (F\<^sub>a x b \<otimes> \<I>) \<cdot>
                             \<r>\<^sup>-\<^sup>1[hom\<^sub>o b] \<cdot> Comp x a b"
            using comp_assoc by simp
          also have "... = (eval (F\<^sub>o x) (F\<^sub>o b) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o b) \<otimes> e)) \<cdot>
                              (F\<^sub>a x b \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o b] \<cdot> Comp x a b"
            using assms a b x F.preserves_Obj C.Uncurry_Curry by auto
          also have "... = eval (F\<^sub>o x) (F\<^sub>o b) \<cdot>
                             ((exp (F\<^sub>o x) (F\<^sub>o b) \<otimes> e) \<cdot> (F\<^sub>a x b \<otimes> \<I>)) \<cdot>
                               \<r>\<^sup>-\<^sup>1[hom\<^sub>o b] \<cdot> Comp x a b"
            using comp_assoc by simp
          also have "... = eval (F\<^sub>o x) (F\<^sub>o b) \<cdot> (F\<^sub>a x b \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o b] \<cdot>
                             Comp x a b"
            using assms a b x F.preserves_Hom [of x b]
                  comp_cod_arr [of "F\<^sub>a x b" "exp (F\<^sub>o x) (F\<^sub>o b)"] comp_arr_dom
                  interchange
            by fastforce
          also have "... = eval (F\<^sub>o x) (F\<^sub>o b) \<cdot> (F\<^sub>a x b \<otimes> e) \<cdot>
                             (Comp x a b \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[Hom a b \<otimes> hom\<^sub>o a]"
            using assms a b x runit'_naturality [of "Comp x a b"]
                  Comp_in_hom [of x a b]
            by auto
          also have "... = eval (F\<^sub>o x) (F\<^sub>o b) \<cdot> ((F\<^sub>a x b \<otimes> e) \<cdot> (Comp x a b \<otimes> \<I>)) \<cdot>
                             \<r>\<^sup>-\<^sup>1[Hom a b \<otimes> hom\<^sub>o a]"
            using comp_assoc by simp
          also have "... = eval (F\<^sub>o x) (F\<^sub>o b) \<cdot> (F\<^sub>a x b \<cdot> Comp x a b \<otimes> e) \<cdot>
                             \<r>\<^sup>-\<^sup>1[Hom a b \<otimes> hom\<^sub>o a]"
            using assms a b x F.preserves_Hom [of x b] Comp_in_hom comp_arr_dom
                  interchange [of "F\<^sub>a x b" "Comp x a b" e \<I>]
            by fastforce
          finally show ?thesis by blast
        qed
        also have "... = eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                           (F\<^sub>a a b \<otimes> eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                              Exp\<^sup>\<leftarrow> e (F\<^sub>o a) \<cdot> F\<^sub>a x a)"
        proof -
          have "eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                  (F\<^sub>a a b \<otimes> eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                     Exp\<^sup>\<leftarrow> e (F\<^sub>o a) \<cdot> F\<^sub>a x a) =
                eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                  (F\<^sub>a a b \<otimes> eval \<I> (F\<^sub>o a) \<cdot> (\<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                     Exp\<^sup>\<leftarrow> e (F\<^sub>o a)) \<cdot> F\<^sub>a x a)"
            using comp_assoc by simp
          also have "... =
                eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                  (F\<^sub>a a b \<otimes> eval \<I> (F\<^sub>o a) \<cdot>
                    ((Exp\<^sup>\<leftarrow> e (F\<^sub>o a) \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[exp (F\<^sub>o x) (F\<^sub>o a)]) \<cdot>
                       F\<^sub>a x a)"
            using assms a b x F.preserves_Obj F.preserves_Hom
                  runit'_naturality [of "Exp\<^sup>\<leftarrow> e (F\<^sub>o a)"]
            by auto
          also have "... =
                eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                  (F\<^sub>a a b \<otimes>
                     Uncurry[\<I>, F\<^sub>o a] (Exp\<^sup>\<leftarrow> e (F\<^sub>o a)) \<cdot> \<r>\<^sup>-\<^sup>1[exp (F\<^sub>o x) (F\<^sub>o a)] \<cdot>
                       F\<^sub>a x a)"
            using comp_assoc by simp
          also have "... =
                eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                  (F\<^sub>a a b \<otimes>
                     (eval (F\<^sub>o x) (F\<^sub>o a) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o a) \<otimes> e)) \<cdot>
                        \<r>\<^sup>-\<^sup>1[exp (F\<^sub>o x) (F\<^sub>o a)] \<cdot> F\<^sub>a x a)"
            using assms a b x F.preserves_Obj C.Uncurry_Curry by auto
          also have "... =
                eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                  (F\<^sub>a a b \<otimes>
                     (eval (F\<^sub>o x) (F\<^sub>o a) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o a) \<otimes> e)) \<cdot>
                        (F\<^sub>a x a \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using a b x F.preserves_Hom [of x a] runit'_naturality by fastforce
          also have "... =
                eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                  (F\<^sub>a a b \<otimes>
                     eval (F\<^sub>o x) (F\<^sub>o a) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o a) \<otimes> e) \<cdot>
                       (F\<^sub>a x a \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using comp_assoc by simp
          also have "... =
                eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                  (F\<^sub>a a b \<otimes> eval (F\<^sub>o x) (F\<^sub>o a) \<cdot> (F\<^sub>a x a \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using assms a b x F.preserves_Obj F.preserves_Hom F.preserves_Hom
                  comp_arr_dom [of e \<I>]
                  comp_cod_arr [of "F\<^sub>a x a" "exp (F\<^sub>o x) (F\<^sub>o a)"]
                  interchange [of "exp (F\<^sub>o x) (F\<^sub>o a)" "F\<^sub>a x a" e \<I>] comp_assoc
            by (metis in_homE)
          also have "... =
                eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                  (exp (F\<^sub>o a) (F\<^sub>o b) \<otimes> eval (F\<^sub>o x) (F\<^sub>o a)) \<cdot>
                    (F\<^sub>a a b \<otimes> (F\<^sub>a x a \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using assms a b x F.preserves_Obj F.preserves_Hom [of x a]
                  F.preserves_Hom [of a b]
                  comp_cod_arr [of "F\<^sub>a a b" "exp (F\<^sub>o a) (F\<^sub>o b)"]
                  interchange
                    [of "exp (F\<^sub>o a) (F\<^sub>o b)" "F\<^sub>a a b"
                        "eval (F\<^sub>o x) (F\<^sub>o a)" "(F\<^sub>a x a \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"]
            by fastforce
          also have "... = (eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                              (exp (F\<^sub>o a) (F\<^sub>o b) \<otimes> eval (F\<^sub>o x) (F\<^sub>o a))) \<cdot>
                             (F\<^sub>a a b \<otimes> (F\<^sub>a x a \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using comp_assoc by simp
          also have "... = (eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                              (exp (F\<^sub>o a) (F\<^sub>o b) \<otimes> eval (F\<^sub>o x) (F\<^sub>o a))) \<cdot>
                             (F\<^sub>a a b \<otimes> (F\<^sub>a x a \<otimes> e)) \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using assms a b x F.preserves_Obj F.preserves_Hom [of a b]
                  F.preserves_Hom [of x a] comp_arr_dom [of "F\<^sub>a a b" "Hom a b"]
                  interchange [of "F\<^sub>a a b" "Hom a b" "F\<^sub>a x a \<otimes> e" "\<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"]
            by fastforce
          also have "... = (eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                              (exp (F\<^sub>o a) (F\<^sub>o b) \<otimes> eval (F\<^sub>o x) (F\<^sub>o a))) \<cdot>
                             (exp (F\<^sub>o a) (F\<^sub>o b) \<otimes> exp (F\<^sub>o x) (F\<^sub>o a) \<otimes> F\<^sub>o x) \<cdot>
                             (F\<^sub>a a b \<otimes> F\<^sub>a x a \<otimes> e) \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using assms a b x F.preserves_Obj F.preserves_Hom [of a b]
                  F.preserves_Hom [of x a]
                  comp_cod_arr [of "(F\<^sub>a a b \<otimes> F\<^sub>a x a \<otimes> e) \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
                                   "exp (F\<^sub>o a) (F\<^sub>o b) \<otimes> exp (F\<^sub>o x) (F\<^sub>o a) \<otimes> F\<^sub>o x"]
            by fastforce
          also have "... = (eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                              (exp (F\<^sub>o a) (F\<^sub>o b) \<otimes> eval (F\<^sub>o x) (F\<^sub>o a))) \<cdot>
                             (\<a>[exp (F\<^sub>o a) (F\<^sub>o b), exp (F\<^sub>o x) (F\<^sub>o a), F\<^sub>o x] \<cdot>
                                \<a>\<^sup>-\<^sup>1[exp (F\<^sub>o a) (F\<^sub>o b), exp (F\<^sub>o x) (F\<^sub>o a), F\<^sub>o x]) \<cdot>
                             (F\<^sub>a a b \<otimes> (F\<^sub>a x a \<otimes> e)) \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using assms a b x F.preserves_Obj comp_assoc_assoc' by simp
          also have "... = (eval (F\<^sub>o a) (F\<^sub>o b) \<cdot>
                              (exp (F\<^sub>o a) (F\<^sub>o b) \<otimes> eval (F\<^sub>o x) (F\<^sub>o a)) \<cdot>
                              \<a>[exp (F\<^sub>o a) (F\<^sub>o b), exp (F\<^sub>o x) (F\<^sub>o a), F\<^sub>o x]) \<cdot>
                              (\<a>\<^sup>-\<^sup>1[exp (F\<^sub>o a) (F\<^sub>o b), exp (F\<^sub>o x) (F\<^sub>o a), F\<^sub>o x] \<cdot>
                                (F\<^sub>a a b \<otimes> F\<^sub>a x a \<otimes> e)) \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using comp_assoc by simp
          also have "... = Uncurry[F\<^sub>o x, F\<^sub>o b] (C.Comp (F\<^sub>o x) (F\<^sub>o a) (F\<^sub>o b)) \<cdot>
                              (\<a>\<^sup>-\<^sup>1[exp (F\<^sub>o a) (F\<^sub>o b), exp (F\<^sub>o x) (F\<^sub>o a), F\<^sub>o x] \<cdot>
                                (F\<^sub>a a b \<otimes> F\<^sub>a x a \<otimes> e)) \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using assms a b x F.preserves_Obj C.Uncurry_Curry C.Comp_def
            by auto
          also have "... = Uncurry[F\<^sub>o x, F\<^sub>o b] (C.Comp (F\<^sub>o x) (F\<^sub>o a) (F\<^sub>o b)) \<cdot>
                              (((F\<^sub>a a b \<otimes> F\<^sub>a x a) \<otimes> e) \<cdot> \<a>\<^sup>-\<^sup>1[Hom a b, hom\<^sub>o a, \<I>]) \<cdot>
                                (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using assms a b x F.preserves_Hom [of a b] F.preserves_Hom [of x a]
                  assoc'_naturality [of "F\<^sub>a a b" "F\<^sub>a x a" e]
            by fastforce
          also have "... = eval (F\<^sub>o x) (F\<^sub>o b) \<cdot>
                             ((C.Comp (F\<^sub>o x) (F\<^sub>o a) (F\<^sub>o b) \<otimes> F\<^sub>o x) \<cdot>
                                ((F\<^sub>a a b \<otimes> F\<^sub>a x a) \<otimes> e)) \<cdot>
                               \<a>\<^sup>-\<^sup>1[Hom a b, hom\<^sub>o a, \<I>] \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using comp_assoc by simp
          also have "... = eval (F\<^sub>o x) (F\<^sub>o b) \<cdot>
                             (C.Comp (F\<^sub>o x) (F\<^sub>o a) (F\<^sub>o b) \<cdot> (F\<^sub>a a b \<otimes> F\<^sub>a x a) \<otimes> e) \<cdot>
                               \<a>\<^sup>-\<^sup>1[Hom a b, hom\<^sub>o a, \<I>] \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using assms a b x F.preserves_Obj F.preserves_Hom [of a b]
                  F.preserves_Hom [of x a] comp_cod_arr [of e "F\<^sub>o x"]
                  interchange
                    [of "C.Comp (F\<^sub>o x) (F\<^sub>o a) (F\<^sub>o b)" "F\<^sub>a a b \<otimes> F\<^sub>a x a" "F\<^sub>o x" e]
            by fastforce
          also have "... = eval (F\<^sub>o x) (F\<^sub>o b) \<cdot> (F\<^sub>a x b \<cdot> Comp x a b \<otimes> e) \<cdot>
                               \<a>\<^sup>-\<^sup>1[Hom a b, hom\<^sub>o a, \<I>] \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a])"
            using assms a b x F.preserves_Obj F.preserves_Hom F.preserves_Comp
            by simp
          also have "... = eval (F\<^sub>o x) (F\<^sub>o b) \<cdot> (F\<^sub>a x b \<cdot> Comp x a b \<otimes> e) \<cdot>
                             \<r>\<^sup>-\<^sup>1[Hom a b \<otimes> hom\<^sub>o a]"
          proof -
            have "\<a>\<^sup>-\<^sup>1[Hom a b, hom\<^sub>o a, \<I>] \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]) =
                  \<r>\<^sup>-\<^sup>1[Hom a b \<otimes> hom\<^sub>o a]"
            proof -
              have "\<a>\<^sup>-\<^sup>1[Hom a b, hom\<^sub>o a, \<I>] \<cdot> (Hom a b \<otimes> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]) =
                    inv ((Hom a b \<otimes> \<r>[hom\<^sub>o a]) \<cdot> \<a>[Hom a b, hom\<^sub>o a, \<I>])"
                using assms a b x inv_comp by auto
              also have "... = \<r>\<^sup>-\<^sup>1[Hom a b \<otimes> hom\<^sub>o a]"
                using assms a b x runit_tensor by auto
              finally show ?thesis by blast
            qed
            thus ?thesis by simp
          qed
          finally show ?thesis by simp
        qed
        finally show "(eval \<I> (F\<^sub>o b) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o b)] \<cdot> Exp\<^sup>\<leftarrow> e (F\<^sub>o b) \<cdot> F\<^sub>a x b) \<cdot>
                         Uncurry[hom\<^sub>o a, hom\<^sub>o b] (hom\<^sub>a a b) =
                      eval (F\<^sub>o a) (F\<^sub>o b) \<cdot> (F\<^sub>a a b \<otimes> eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                         Exp\<^sup>\<leftarrow> e (F\<^sub>o a) \<cdot> F\<^sub>a x a)"
          by argo
      qed
    qed

    text\<open>
      If \<open>\<tau>: hom x - \<rightarrow> F\<close> is an enriched natural transformation, then there exists an
      element \<open>e\<^sub>\<tau> : \<I> \<rightarrow> F x\<close> that generates \<open>\<tau>\<close> via the preceding formula.
      The idea (Kelly 1.46) is to take:
      \[
          \<open>e\<^sub>\<tau>\<close> = \<open>\<I>\<close>\;\labarrow{\<open>Id x\<close>}\;\<open>hom\<^sub>o x\<close>\;\labarrow{\<open>\<tau> x\<close>}\; \<open>F x\<close>
      \]
      This amounts to the ``evaluation of \<open>\<tau> x\<close> at the identity on \<open>x\<close>''.

      However, note once again that, according to the formal definition of enriched
      natural transformation, we have \<open>\<tau> x : \<I> \<rightarrow> exp (hom\<^sub>o x) (F\<^sub>o x)\<close>, so it is
      necessary to transform this to an arrow: \<open>(\<tau> x) \<^sup>\<down>[hom\<^sub>o x, F\<^sub>o x]: hom\<^sub>o x \<rightarrow> F x\<close>.
    \<close>

    abbreviation generating_elem
    where "generating_elem \<tau> \<equiv> (\<tau> x) \<^sup>\<down>[hom\<^sub>o x, F\<^sub>o x] \<cdot> Id x"

    lemma generating_elem_in_hom:
    assumes "enriched_natural_transformation C T \<alpha> \<iota>
               Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
               hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>"
    shows "\<guillemotleft>generating_elem \<tau> : \<I> \<rightarrow> F\<^sub>o x\<guillemotright>"
    proof -
      interpret \<tau>: enriched_natural_transformation C T \<alpha> \<iota>
                     Obj Hom Id Comp \<open>Collect ide\<close> exp C.Id C.Comp
                     hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>
        using assms by blast
      show "\<guillemotleft>generating_elem \<tau> : \<I> \<rightarrow> F\<^sub>o x\<guillemotright>"
        using x Id_in_hom \<tau>.component_in_hom [of x] F.preserves_Obj C.DN_def
        by auto fastforce
    qed
    text\<open>
      Now we have to verify the elements of the diagram after Kelly (1.47):
$$\xymatrix{
 \<open>hom\<^sub>o a\<close>
   \xuppertwocell[rrrrr]{}^{\<open>hom\<^sub>o a\<close>}<15>{\omit{}}
   \ar[rr] _{\<open>hom\<^sub>a x a\<close>}
   \ar[d] _{\<open>F\<^sub>a a\<close>}
  &&
 \<open>[hom\<^sub>o x, hom\<^sub>o a]\<close>
   \ar[rr] _{\<open>[Id x, hom\<^sub>o a]\<close>}
   \ar[d] ^{\<open>[hom\<^sub>o x, \<tau> a]\<close>}
  &&
 \<open>[\<I>, hom\<^sub>o a]\<close>
   \ar[r] _{\textrm{iso}}
   \ar[d] ^{\<open>[\<I>, \<tau> a]\<close>}
  &
 \<open>hom\<^sub>o a\<close>
   \ar[d] ^{\<open>\<tau> a\<close>}
  \\
 \<open>[F\<^sub>o x, F\<^sub>o a]\<close>
   \ar[rr] ^{\<open>[\<tau>\<^sub>e x, F\<^sub>o a]\<close>}
   \xlowertwocell[rrrr]{}_{\<open>[\<tau>\<^sub>e x \<cdot> Id x, F\<^sub>o a]\<close>}<-15>{\omit{}}
  &&
 \<open>[hom\<^sub>o x, F\<^sub>o a]\<close>
   \ar[rr] ^{\<open>[Id x, F\<^sub>o a]\<close>}
  &&
 \<open>[\<I>, F\<^sub>o a]\<close>
   \ar[r] ^{\textrm{iso}}
  &
 \<open>F\<^sub>o a\<close>
}$$
    \<close>
    (*
                   hom\<^sub>a x a                    [Id x, hom\<^sub>o a]           iso
         hom\<^sub>o a ----------------> [hom\<^sub>o x, hom\<^sub>o a] -------> [\<I>, hom\<^sub>o a] -----> hom\<^sub>o a
           |                             |                     |               |
       F\<^sub>a  |                             | [hom\<^sub>o x, \<tau> a]        | [\<I>, \<tau> a ]     | \<tau> a
           v                             v                     v               v
         [F\<^sub>o x, F\<^sub>o a] ----------> [hom\<^sub>o x, F\<^sub>o a] ----------> [\<I>, F\<^sub>o a] -------> F\<^sub>o a
                     [\<tau>\<^sub>e x, F\<^sub>o a]                [Id x, F\<^sub>o a]             iso
                                      =
                                [\<tau>\<^sub>e x, F\<^sub>o a]
     *)
    text\<open>
      The left square is enriched naturality of \<open>\<tau>\<close> (Kelly (1.39)).
      The middle square commutes trivially.
      The right square commutes by the naturality of the canonical isomorphismm
      from \<open>[\<I>, hom\<^sub>o a]\<close> to \<open>hom\<^sub>o a\<close>.
      The top edge composes to \<open>hom\<^sub>o a\<close> (an identity).
      The commutativity of the entire diagram shows that \<open>\<tau> a\<close> is recovered from \<open>e\<^sub>\<tau>\<close>.
      Note that where \<open>\<tau> a\<close> appears, what is actually meant formally is \<open>(\<tau> a) \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a]\<close>.
    \<close>

    lemma center_square:
    assumes "enriched_natural_transformation C T \<alpha> \<iota>
               Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
               hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>"
    and "a \<in> Obj"
    shows "C.Exp \<I> (\<tau> a \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a]) \<cdot> C.Exp (Id x) (hom\<^sub>o a) =
           C.Exp (Id x) (F\<^sub>o a) \<cdot> C.Exp (hom\<^sub>o x) (\<tau> a \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a])"
    proof -
      interpret \<tau>: enriched_natural_transformation C T \<alpha> \<iota>
                     Obj Hom Id Comp \<open>Collect ide\<close> exp C.Id C.Comp
                     hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>
        using assms by blast
      let ?\<tau>\<^sub>a = "\<tau> a \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a]"
      show "C.Exp \<I> ?\<tau>\<^sub>a \<cdot> C.Exp (Id x) (hom\<^sub>o a) =
            C.Exp (Id x) (F\<^sub>o a) \<cdot> C.Exp (hom\<^sub>o x) ?\<tau>\<^sub>a"
        by (metis assms(2) x C.Exp_comp F.preserves_Obj Id_in_hom
            C.DN_simps(1-3) comp_arr_dom comp_cod_arr in_homE \<tau>.component_in_hom
            ide_Hom mem_Collect_eq)
    qed

    lemma right_square:
    assumes "enriched_natural_transformation C T \<alpha> \<iota>
               Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
               hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>"
    and "a \<in> Obj"
    shows "\<tau> a \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a] \<cdot> C.Dn (hom\<^sub>o a) =
           C.Dn (F\<^sub>o a) \<cdot> C.Exp \<I> (\<tau> a \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a])"
    proof -
      interpret \<tau>: enriched_natural_transformation C T \<alpha> \<iota>
                     Obj Hom Id Comp \<open>Collect ide\<close> exp C.Id C.Comp
                     hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>
        using assms by blast
      show ?thesis
        using assms(2) C.Up_Dn_naturality C.DN_simps \<tau>.component_in_hom
        apply auto[1]
        by (metis C.Exp_ide_y C.UP_DN(2) F.preserves_Obj ide_Hom ide_unity
            in_homE mem_Collect_eq x)
    qed

    lemma top_path:
    assumes "a \<in> Obj"
    shows "eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot> C.Exp (Id x) (hom\<^sub>o a) \<cdot>
             hom\<^sub>a x a =
           hom\<^sub>o a"
    proof -
      have "eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot> C.Exp (Id x) (hom\<^sub>o a) \<cdot>
              hom\<^sub>a x a =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              (Curry[exp \<I> (hom\<^sub>o a), \<I>, hom\<^sub>o a] (hom\<^sub>o a \<cdot> eval \<I> (hom\<^sub>o a)) \<cdot>
                 Curry[exp (hom\<^sub>o x) (hom\<^sub>o a), \<I>, hom\<^sub>o a]
                   (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (exp (hom\<^sub>o x) (hom\<^sub>o a) \<otimes> Id x))) \<cdot>
              hom\<^sub>a x a"
        using assms x C.Exp_def Id_in_hom [of x] by auto
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              Curry[exp \<I> (hom\<^sub>o a), \<I>, hom\<^sub>o a] (hom\<^sub>o a \<cdot> eval \<I> (hom\<^sub>o a)) \<cdot>
                Curry[exp (hom\<^sub>o x) (hom\<^sub>o a), \<I>, hom\<^sub>o a]
                  (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (exp (hom\<^sub>o x) (hom\<^sub>o a) \<otimes> Id x)) \<cdot>
                     hom\<^sub>a x a"
        using comp_assoc by simp
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              Curry[exp \<I> (hom\<^sub>o a), \<I>, hom\<^sub>o a] (hom\<^sub>o a \<cdot> eval \<I> (hom\<^sub>o a)) \<cdot>
                Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                  ((eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (exp (hom\<^sub>o x) (hom\<^sub>o a) \<otimes> Id x)) \<cdot>
                     (hom\<^sub>a x a \<otimes> \<I>))"
      proof -
        have "\<guillemotleft>eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (exp (hom\<^sub>o x) (hom\<^sub>o a) \<otimes> Id x)
                 : exp (hom\<^sub>o x) (hom\<^sub>o a) \<otimes> \<I> \<rightarrow> hom\<^sub>o a\<guillemotright>"
          using assms x
          by (meson Id_in_hom comp_in_homI C.eval_in_hom_ax C.ide_exp
              ide_in_hom tensor_in_hom ide_Hom)
        thus ?thesis
          using assms x preserves_Hom [of x a] C.comp_Curry_arr by simp
      qed
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              Curry[exp \<I> (hom\<^sub>o a), \<I>, hom\<^sub>o a] (hom\<^sub>o a \<cdot> eval \<I> (hom\<^sub>o a)) \<cdot>
                Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                  (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot>
                     (exp (hom\<^sub>o x) (hom\<^sub>o a) \<otimes> Id x) \<cdot> (hom\<^sub>a x a \<otimes> \<I>))"
        using comp_assoc by simp
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              Curry[exp \<I> (hom\<^sub>o a), \<I>, hom\<^sub>o a] (hom\<^sub>o a \<cdot> eval \<I> (hom\<^sub>o a)) \<cdot>
                Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                  (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (hom\<^sub>a x a \<otimes> Id x))"
      proof -
        have "seq (Id x) \<I> \<and> seq (hom\<^sub>o x) (Id x)"
          using x Id_in_hom ide_in_hom ide_unity by blast
        thus ?thesis
          using assms x preserves_Hom comp_arr_dom [of "Id x" \<I>]
                interchange [of "exp (hom\<^sub>o x) (hom\<^sub>o a)" "hom\<^sub>a x a" "Id x" \<I>]
          by (metis comp_cod_arr comp_ide_arr dom_eqI ide_unity
              in_homE ide_Hom)
      qed
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              Curry[exp \<I> (hom\<^sub>o a), \<I>, hom\<^sub>o a] (eval \<I> (hom\<^sub>o a)) \<cdot>
                Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                  (Uncurry[hom\<^sub>o x, hom\<^sub>o a] (hom\<^sub>a x a) \<cdot> (hom\<^sub>o a \<otimes> Id x))"
      proof -
        have "eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (hom\<^sub>a x a \<otimes> Id x) =
              eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (hom\<^sub>a x a \<cdot> hom\<^sub>o a \<otimes> hom\<^sub>o x \<cdot> Id x)"
          using assms x Id_in_hom comp_cod_arr comp_arr_dom Comp_in_hom
          by (metis in_homE preserves_Hom)
        also have "... = eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (hom\<^sub>a x a \<otimes> hom\<^sub>o x) \<cdot>
                           (hom\<^sub>o a \<otimes> Id x)"
            using assms x Id_in_hom Comp_in_hom
                  interchange [of "hom\<^sub>a x a" "hom\<^sub>o a" "hom\<^sub>o x" "Id x"]
            by (metis comp_arr_dom comp_cod_arr in_homE preserves_Hom)
        also have "... = Uncurry[hom\<^sub>o x, hom\<^sub>o a] (hom\<^sub>a x a) \<cdot> (hom\<^sub>o a \<otimes> Id x)"
          using comp_assoc by simp
        finally show ?thesis
          using assms x comp_cod_arr ide_Hom ide_unity C.eval_simps(1,3) by metis
      qed
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                (Uncurry[\<I>, hom\<^sub>o a]
                   (Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                      (Uncurry[hom\<^sub>o x, hom\<^sub>o a] (hom\<^sub>a x a) \<cdot> (hom\<^sub>o a \<otimes> Id x))))"
        using assms x
              C.comp_Curry_arr
                 [of \<I>
                     "Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                        (Uncurry[hom\<^sub>o x, hom\<^sub>o a] (hom\<^sub>a x a) \<cdot> (hom\<^sub>o a \<otimes> Id x))"
                     "hom\<^sub>o a" "exp \<I> (hom\<^sub>o a)"
                     "eval \<I> (hom\<^sub>o a)" "hom\<^sub>o a"]
        apply auto[1]
        by (metis Comp_Hom_Id Comp_in_hom C.Uncurry_Curry C.eval_in_hom_ax
            ide_unity C.isomorphic_exp_unity(1) ide_Hom)
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                (Uncurry[hom\<^sub>o x, hom\<^sub>o a] (hom\<^sub>a x a) \<cdot> (hom\<^sub>o a \<otimes> Id x))"
        using assms x C.Uncurry_Curry
        by (simp add: Comp_Hom_Id Comp_in_hom C.Curry_Uncurry
            C.isomorphic_exp_unity(1))
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (hom\<^sub>a x a \<otimes> hom\<^sub>o x) \<cdot> (hom\<^sub>o a \<otimes> Id x))"
        using comp_assoc by simp
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot>
              Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (hom\<^sub>a x a \<otimes> Id x))"
        using assms x comp_cod_arr [of "Id x" "hom\<^sub>o x"] comp_arr_dom
              interchange [of "hom\<^sub>a x a" "hom\<^sub>o a" "hom\<^sub>o x" "Id x"]
              preserves_Hom [of x a] Id_in_hom
        apply auto[1]
        by fastforce
      also have "... =
            eval \<I> (hom\<^sub>o a) \<cdot>
              (Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                 (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (hom\<^sub>a x a \<otimes> Id x)) \<otimes> \<I>) \<cdot>
                 \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"
      proof -
        have "\<guillemotleft>Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                 (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (hom\<^sub>a x a \<otimes> Id x))
                 : hom\<^sub>o a \<rightarrow> exp \<I> (hom\<^sub>o a)\<guillemotright>"
          using assms x preserves_Hom [of x a] Id_in_hom [of x] by force
        thus ?thesis
          using assms x runit'_naturality by fastforce
      qed
      also have "... =
             Uncurry[\<I>, hom\<^sub>o a]
               (Curry[hom\<^sub>o a, \<I>, hom\<^sub>o a]
                  (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot> (hom\<^sub>a x a \<otimes> Id x))) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"
        using comp_assoc by simp
      also have "... = (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot>
                         (Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a) \<otimes> Id x)) \<cdot>
                            \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"
        using assms x C.Uncurry_Curry preserves_Hom [of x a] Id_in_hom [of x]
        by fastforce
      also have "... = (eval (hom\<^sub>o x) (hom\<^sub>o a) \<cdot>
                         ((Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a) \<otimes> hom\<^sub>o x) \<cdot>
                            (hom\<^sub>o a \<otimes> Id x))) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"
        using assms x Id_in_hom [of x] Comp_in_hom comp_arr_dom comp_cod_arr
              interchange
        by auto
      also have "... = Uncurry[hom\<^sub>o x, hom\<^sub>o a]
                         (Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a)) \<cdot>
                         (hom\<^sub>o a \<otimes> Id x) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"
        using comp_assoc by simp
      also have "... = Comp x x a \<cdot> (hom\<^sub>o a \<otimes> Id x) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"
        using assms x C.Uncurry_Curry Comp_in_hom by simp
      also have "... = (Comp x x a \<cdot> (hom\<^sub>o a \<otimes> Id x)) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"
        using comp_assoc by simp
      also have "... = \<r>[hom\<^sub>o a] \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o a]"
        using assms x Comp_Hom_Id by auto
      also have "... = hom\<^sub>o a"
        using assms x comp_runit_runit' by blast
      finally show ?thesis by blast
    qed

    text\<open>
      The left square is an instance of Kelly (1.39), so we can get that by
      instantiating that result.  The confusing business is that the target
      enriched category is the base category C.
    \<close>

    lemma left_square:
    assumes "enriched_natural_transformation C T \<alpha> \<iota>
               Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
               hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>"
    and "a \<in> Obj"
    shows "Exp\<^sup>\<rightarrow> (hom\<^sub>o x) ((\<tau> a) \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a]) \<cdot> hom\<^sub>a x a =
           Exp\<^sup>\<leftarrow> ((\<tau> x) \<^sup>\<down>[hom\<^sub>o x, F\<^sub>o x]) (F\<^sub>o a) \<cdot> F\<^sub>a x a"
    proof -
      interpret \<tau>: enriched_natural_transformation C T \<alpha> \<iota>
                     Obj Hom Id Comp \<open>Collect ide\<close> exp C.Id C.Comp
                     hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>
        using assms(1) by blast

      interpret cov_Hom: covariant_Hom C T \<alpha> \<iota> exp eval Curry
                           \<open>Collect ide\<close> exp C.Id C.Comp \<open>hom\<^sub>o x\<close>
        using x by unfold_locales auto
      interpret cnt_Hom: contravariant_Hom C T \<alpha> \<iota> \<sigma> exp eval Curry
                           \<open>Collect ide\<close> exp C.Id C.Comp \<open>F\<^sub>o a\<close>
        using assms(2) F.preserves_Obj by unfold_locales
      interpret Kelly: Kelly_1_39 C T \<alpha> \<iota> \<sigma> exp eval Curry
                         Obj Hom Id Comp \<open>Collect ide\<close> exp C.Id C.Comp
                         hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau> x a
        using assms(2) x
        by unfold_locales

      text\<open>
        The following is the enriched naturality of \<open>\<tau>\<close>, expressed in the alternate form
        involving the underlying ordinary functors of the enriched hom functors.
      \<close>
      have 1: "cov_Hom.map\<^sub>0 (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a) \<cdot> hom\<^sub>a x a =
               cnt_Hom.map\<^sub>0 (hom\<^sub>o x) (F\<^sub>o x) (\<tau> x) \<cdot> F\<^sub>a x a"
        using Kelly.Kelly_1_39 by simp

      text\<open>
        Here we have the underlying ordinary functor of the enriched covariant hom,
        expressed in terms of the covariant endofunctor \<open>Exp\<^sup>\<rightarrow> (hom\<^sub>o x)\<close> on the base
        category.
      \<close>
      have 2: "cov_Hom.map\<^sub>0 (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a) =
               Exp\<^sup>\<rightarrow> (hom\<^sub>o x) ((\<tau> a) \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a])"
      proof -
        have "cov_Hom.map\<^sub>0 (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a) =
              (Curry[cnt_Hom.hom\<^sub>o (hom\<^sub>o a), cov_Hom.hom\<^sub>o (hom\<^sub>o a),
                     cnt_Hom.hom\<^sub>o (hom\<^sub>o x)]
                 (C.Comp (hom\<^sub>o x) (hom\<^sub>o a) (F\<^sub>o a)) \<cdot> \<tau> a)
                \<^sup>\<down>[cov_Hom.hom\<^sub>o (hom\<^sub>o a), cnt_Hom.hom\<^sub>o (hom\<^sub>o x)]"
        proof -
          have "cov_Hom.map\<^sub>0 (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a) =
                  cnt_Hom.Op\<^sub>0.Map
                    (cov_Hom.UF.map\<^sub>0 (cnt_Hom.Op\<^sub>0.MkArr (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a)))
                    \<^sup>\<down>[cnt_Hom.Op\<^sub>0.Dom
                        (cov_Hom.UF.map\<^sub>0
                           (cnt_Hom.Op\<^sub>0.MkArr (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a))),
                      cnt_Hom.Op\<^sub>0.Cod
                        (cov_Hom.UF.map\<^sub>0
                           (cnt_Hom.Op\<^sub>0.MkArr (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a)))]"
            using assms x preserves_Obj F.preserves_Obj \<tau>.component_in_hom
                  cov_Hom.Kelly_1_31 cov_Hom.UF.preserves_arr
            by force
          moreover
          have "cnt_Hom.Op\<^sub>0.Dom
                  (cov_Hom.UF.map\<^sub>0
                     (cnt_Hom.Op\<^sub>0.MkArr (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a))) =
                exp (hom\<^sub>o x) (hom\<^sub>o a)"
            using assms x cov_Hom.UF.map\<^sub>0_def
            apply auto[1]
            using cnt_Hom.y \<tau>.component_in_hom by force
          moreover
          have "cnt_Hom.Op\<^sub>0.Cod
                  (cov_Hom.UF.map\<^sub>0
                     (cnt_Hom.Op\<^sub>0.MkArr (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a))) =
                exp (hom\<^sub>o x) (F\<^sub>o a)"
            using assms x cov_Hom.UF.map\<^sub>0_def
            apply auto[1]
            using cnt_Hom.y \<tau>.component_in_hom by fastforce
          moreover
          have "cnt_Hom.Op\<^sub>0.Map
                  (cov_Hom.UF.map\<^sub>0
                     (cnt_Hom.Op\<^sub>0.MkArr (hom\<^sub>o a) (F\<^sub>o a) (\<tau> a))) =
                cov_Hom.hom\<^sub>a (hom\<^sub>o a) (F\<^sub>o a) \<cdot> \<tau> a"
            using assms x cov_Hom.UF.map\<^sub>0_def
            apply auto[1]
            using cnt_Hom.y \<tau>.component_in_hom by auto
          ultimately show ?thesis
            using assms x ide_Hom F.preserves_Obj by simp
        qed
        also have "... = Exp\<^sup>\<rightarrow> (hom\<^sub>o x) ((\<tau> a) \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a])"
          using assms(2) x C.cov_Exp_DN \<tau>.component_in_hom F.preserves_Obj
          by simp
        finally show ?thesis by blast
      qed

      text\<open>
        Here we have the underlying ordinary functor of the enriched contravariant hom,
        expressed in terms of the contravariant endofunctor \<open>\<lambda>f. Exp\<^sup>\<leftarrow> f (F\<^sub>o a)\<close> on the base
        category.
      \<close>
      have 3: "cnt_Hom.map\<^sub>0 (hom\<^sub>o x) (F\<^sub>o x) (\<tau> x) =
               Exp\<^sup>\<leftarrow> (\<tau> x \<^sup>\<down>[hom\<^sub>o x, F\<^sub>o x]) (F\<^sub>o a)"
      proof -
        have "cnt_Hom.map\<^sub>0 (hom\<^sub>o x) (F\<^sub>o x) (\<tau> x) =
              Uncurry[exp (F\<^sub>o x) (F\<^sub>o a), exp (hom\<^sub>o x) (F\<^sub>o a)]
                (cnt_Hom.hom\<^sub>a (F\<^sub>o x) (hom\<^sub>o x) \<cdot> \<tau> x) \<cdot>
                   \<l>\<^sup>-\<^sup>1[exp (F\<^sub>o x) (F\<^sub>o a)]"
        proof -
          have "cnt_Hom.map\<^sub>0 (hom\<^sub>o x) (F\<^sub>o x) (\<tau> x) =
                Uncurry[cnt_Hom.Op\<^sub>0.Dom
                          (cnt_Hom.UF.map\<^sub>0
                             (cnt_Hom.Op\<^sub>0.MkArr (F\<^sub>o x) (hom\<^sub>o x) (\<tau> x))),
                        cnt_Hom.Op\<^sub>0.Cod
                          (cnt_Hom.UF.map\<^sub>0
                             (cnt_Hom.Op\<^sub>0.MkArr (F\<^sub>o x) (hom\<^sub>o x) (\<tau> x)))]
                  (cnt_Hom.Op\<^sub>0.Map
                     (cnt_Hom.UF.map\<^sub>0
                        (cnt_Hom.Op\<^sub>0.MkArr (F\<^sub>o x) (Hom x x) (\<tau> x)))) \<cdot>
                     \<l>\<^sup>-\<^sup>1[cnt_Hom.Op\<^sub>0.Dom
                          (cnt_Hom.UF.map\<^sub>0
                             (cnt_Hom.Op\<^sub>0.MkArr (F\<^sub>o x) (hom\<^sub>o x) (\<tau> x)))]"
            using assms x 1 2 cnt_Hom.Kelly_1_32 [of "hom\<^sub>o x" "F\<^sub>o x" "\<tau> x"]
                  C.Curry_simps(1-3) C.DN_def C.UP_DN(2) C.eval_simps(1-3)
                  C.ide_exp Comp_in_hom F.preserves_Obj comp_in_homI'
                  not_arr_null preserves_Obj \<tau>.component_in_hom in_homE
                  mem_Collect_eq seqE
            by (smt (verit))
          moreover have "cnt_Hom.Op\<^sub>0.Dom
                           (cnt_Hom.UF.map\<^sub>0
                              (cnt_Hom.Op\<^sub>0.MkArr (F\<^sub>o x) (hom\<^sub>o x) (\<tau> x))) =
                         exp (F\<^sub>o x) (F\<^sub>o a)"
            using assms x cnt_Hom.UF.map\<^sub>0_def
            apply auto[1]
            using F.preserves_Obj cnt_Hom.Op\<^sub>0.arr_MkArr \<tau>.component_in_hom
            by blast
          moreover have "cnt_Hom.Op\<^sub>0.Cod
                           (cnt_Hom.UF.map\<^sub>0
                              (cnt_Hom.Op\<^sub>0.MkArr (F\<^sub>o x) (hom\<^sub>o x) (\<tau> x))) =
                         exp (hom\<^sub>o x) (F\<^sub>o a)"
            using assms x cnt_Hom.UF.map\<^sub>0_def
            apply auto[1]
            using F.preserves_Obj cnt_Hom.Op\<^sub>0.arr_MkArr \<tau>.component_in_hom
            by blast
          moreover have "cnt_Hom.Op\<^sub>0.Map
                           (cnt_Hom.UF.map\<^sub>0
                              (cnt_Hom.Op\<^sub>0.MkArr (F\<^sub>o x) (hom\<^sub>o x) (\<tau> x))) =
                         cnt_Hom.hom\<^sub>a (F\<^sub>o x) (hom\<^sub>o x) \<cdot> \<tau> x"
            using assms x cnt_Hom.UF.map\<^sub>0_def F.preserves_Obj
            by (simp add: \<tau>.component_in_hom)
          ultimately show ?thesis by argo
        qed
        also have "... = Exp\<^sup>\<leftarrow> (\<tau> x \<^sup>\<down>[hom\<^sub>o x, F\<^sub>o x]) (F\<^sub>o a)"
          using assms(2) x \<tau>.component_in_hom [of x] F.preserves_Obj
                C.DN_def C.cnt_Exp_DN
          by fastforce
        finally show ?thesis by simp
      qed
      show ?thesis
        using 1 2 3 by auto
    qed

    lemma transformation_generated_by_element:
    assumes "enriched_natural_transformation C T \<alpha> \<iota>
               Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
               hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>"
    and "a \<in> Obj"
    shows "\<tau> a = generated_transformation (generating_elem \<tau>) a"
    proof -
      interpret \<tau>: enriched_natural_transformation C T \<alpha> \<iota>
                     Obj Hom Id Comp \<open>Collect ide\<close> exp C.Id C.Comp
                     hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>
        using assms(1) by blast
      have "\<tau> a \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a] =
            \<tau> a \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a] \<cdot>
              eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)] \<cdot> C.Exp (Id x) (hom\<^sub>o a) \<cdot>
                Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a)"
        using assms(2) x top_path \<tau>.component_in_hom [of a] F.preserves_Obj
              comp_arr_dom C.UP_DN(2)
        by auto
      also have "... =
              (\<tau> a \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a] \<cdot> eval \<I> (hom\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (hom\<^sub>o a)]) \<cdot>
                C.Exp (Id x) (hom\<^sub>o a) \<cdot>
                  Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a)"
        using comp_assoc by simp
      also have "... =
              (eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                 C.Exp \<I> (Uncurry[hom\<^sub>o a, F\<^sub>o a] (\<tau> a) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o a])) \<cdot>
                 C.Exp (Id x) (hom\<^sub>o a) \<cdot>
                   Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a)"
        using assms right_square C.DN_def \<tau>.component_in_hom comp_assoc
        by auto blast
      also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                (C.Exp \<I> (Uncurry[hom\<^sub>o a, F\<^sub>o a] (\<tau> a) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o a]) \<cdot>
                   C.Exp (Id x) (hom\<^sub>o a)) \<cdot>
                  Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a)"
        using comp_assoc by simp
      also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                (C.Exp (Id x) (F\<^sub>o a) \<cdot>
                   C.Exp (hom\<^sub>o x) (Uncurry[hom\<^sub>o a, F\<^sub>o a] (\<tau> a) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o a])) \<cdot>
                  Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a)"
        using assms center_square C.DN_def
              enriched_natural_transformation.component_in_hom
        by fastforce
      also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot> C.Exp (Id x) (F\<^sub>o a) \<cdot>
                C.Exp (hom\<^sub>o x) (Uncurry[hom\<^sub>o a, F\<^sub>o a] (\<tau> a) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o a]) \<cdot>
                  Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a)"
        using comp_assoc by simp
      also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot> C.Exp (Id x) (F\<^sub>o a) \<cdot> 
                Exp\<^sup>\<leftarrow> (Uncurry[hom\<^sub>o x, F\<^sub>o x] (\<tau> x) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o x]) (F\<^sub>o a) \<cdot> F\<^sub>a x a"
      proof -
        have "eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot> C.Exp (Id x) (F\<^sub>o a) \<cdot>
                C.Exp (hom\<^sub>o x) (Uncurry[hom\<^sub>o a, F\<^sub>o a] (\<tau> a) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o a]) \<cdot>
                  Curry[hom\<^sub>o a, hom\<^sub>o x, hom\<^sub>o a] (Comp x x a) =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot> C.Exp (Id x) (F\<^sub>o a) \<cdot>
                C.Exp (hom\<^sub>o x) (Uncurry[hom\<^sub>o a, F\<^sub>o a] (\<tau> a) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o a]) \<cdot>
                  hom\<^sub>a x a"
          using assms(2) x by force
        also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot> C.Exp (Id x) (F\<^sub>o a) \<cdot>
                Exp\<^sup>\<rightarrow> (hom\<^sub>o x) (Uncurry[hom\<^sub>o a, F\<^sub>o a] (\<tau> a) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o a]) \<cdot>
                  hom\<^sub>a x a"
          using assms x C.Exp_def C.cnt_Exp_ide comp_arr_dom by auto
        also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot> C.Exp (Id x) (F\<^sub>o a) \<cdot>
                Exp\<^sup>\<rightarrow> (hom\<^sub>o x) (\<tau> a\<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a]) \<cdot> hom\<^sub>a x a"
          using assms x C.DN_def by fastforce
        also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot> C.Exp (Id x) (F\<^sub>o a) \<cdot>
                Exp\<^sup>\<leftarrow> (\<tau> x\<^sup>\<down>[hom\<^sub>o x, F\<^sub>o x]) (F\<^sub>o a) \<cdot> F\<^sub>a x a"
          using assms(2) left_square \<tau>.enriched_natural_transformation_axioms
          by fastforce
        also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot> C.Exp (Id x) (F\<^sub>o a) \<cdot>
                Exp\<^sup>\<leftarrow> (Uncurry[hom\<^sub>o x, F\<^sub>o x] (\<tau> x) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o x]) (F\<^sub>o a) \<cdot> F\<^sub>a x a"
          using C.DN_def by fastforce
        finally show ?thesis by blast
      qed
      also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                (C.Exp (Id x) (F\<^sub>o a) \<cdot>
                   Exp\<^sup>\<leftarrow> (Uncurry[hom\<^sub>o x, F\<^sub>o x] (\<tau> x) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o x]) (F\<^sub>o a)) \<cdot>
                   F\<^sub>a x a"
        using comp_assoc by simp
      also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                (Exp\<^sup>\<leftarrow> (Id x) (F\<^sub>o a) \<cdot>
                   Exp\<^sup>\<leftarrow> (Uncurry[hom\<^sub>o x, F\<^sub>o x] (\<tau> x) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o x]) (F\<^sub>o a)) \<cdot>
                   F\<^sub>a x a"
        using assms x F.preserves_Obj C.Exp_def C.cov_Exp_ide
                comp_cod_arr [of "Exp\<^sup>\<leftarrow> (Id x) (dom (F\<^sub>o a))"]
        by auto
      also have "... =
              eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                Exp\<^sup>\<leftarrow> ((Uncurry[hom\<^sub>o x, F\<^sub>o x] (\<tau> x) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o x]) \<cdot> Id x) (F\<^sub>o a) \<cdot>
                  F\<^sub>a x a"
      proof -
        have "seq (Uncurry[hom\<^sub>o x, F\<^sub>o x] (\<tau> x) \<cdot> \<l>\<^sup>-\<^sup>1[hom\<^sub>o x]) (Id x)"
          using assms x F.preserves_Obj Id_in_hom \<tau>.component_in_hom
          apply (intro seqI)
                apply auto[1]
          by force+
        thus ?thesis
          using assms x F.preserves_Obj C.cnt_Exp_comp by simp
      qed
      also have "... = eval \<I> (F\<^sub>o a) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o a)] \<cdot>
                         Exp\<^sup>\<leftarrow> (generating_elem \<tau>) (F\<^sub>o a) \<cdot> F\<^sub>a x a"
        using x C.DN_def comp_assoc \<tau>.component_in_hom by fastforce
      also have 1: "... =
                    (generated_transformation (generating_elem \<tau>) a) \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a]"
        using assms x F.preserves_Obj C.UP_DN(4) \<tau>.component_in_hom calculation
              ide_Hom
        by (metis (no_types, lifting) mem_Collect_eq)
      finally have *: "(\<tau> a) \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a] =
                       (generated_transformation (generating_elem \<tau>) a)
                          \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a]"
        by blast
      have "\<tau> a = ((\<tau> a) \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a])\<^sup>\<up>"
        using assms x \<tau>.component_in_hom ide_Hom F.preserves_Obj by auto
      also have "... = ((generated_transformation (generating_elem \<tau>) a)
                           \<^sup>\<down>[hom\<^sub>o a, F\<^sub>o a])\<^sup>\<up>"
        using * by argo
      also have "... = generated_transformation (generating_elem \<tau>) a"
        using assms x 1 ide_Hom by presburger
      finally show "\<tau> a = generated_transformation (generating_elem \<tau>) a" by blast
    qed

    lemma element_of_generated_transformation:
    assumes "e \<in> hom \<I> (F\<^sub>o x)"
    shows "generating_elem (generated_transformation e) = e"
    proof -
      have "generating_elem (generated_transformation e) =
            Uncurry[hom\<^sub>o x, F\<^sub>o x]
              ((eval \<I> (F\<^sub>o x) \<cdot> \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o x)] \<cdot>
                  Curry[exp (F\<^sub>o x) (F\<^sub>o x), \<I>, F\<^sub>o x]
                    (eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e)) \<cdot> F\<^sub>a x x)\<^sup>\<up>) \<cdot>
              \<l>\<^sup>-\<^sup>1[hom\<^sub>o x] \<cdot> Id x"
      proof -
        have "arr ((eval \<I> (F\<^sub>o x) \<cdot>
                      \<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o x)] \<cdot>
                        Curry[exp (F\<^sub>o x) (F\<^sub>o x), \<I>, F\<^sub>o x]
                          (eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e)) \<cdot> F\<^sub>a x x)\<^sup>\<up>)"
          using assms x F.preserves_Hom F.preserves_Obj
          apply (intro C.UP_simps seqI)
                apply auto[1]
          by fastforce+
        thus ?thesis
          using assms x C.DN_def comp_assoc by auto
      qed
      also have "... =
            Uncurry[hom\<^sub>o x, F\<^sub>o x]
              ((eval \<I> (F\<^sub>o x) \<cdot>
                  (\<r>\<^sup>-\<^sup>1[exp \<I> (F\<^sub>o x)] \<cdot>
                     Curry[exp (F\<^sub>o x) (F\<^sub>o x), \<I>, F\<^sub>o x]
                       (eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e))) \<cdot> F\<^sub>a x x)\<^sup>\<up>) \<cdot>
              \<l>\<^sup>-\<^sup>1[hom\<^sub>o x] \<cdot> Id x"
        using comp_assoc by simp
      also have "... =
            Uncurry[hom\<^sub>o x, F\<^sub>o x]
              ((eval \<I> (F\<^sub>o x) \<cdot>
                  ((Curry[exp (F\<^sub>o x) (F\<^sub>o x), \<I>, F\<^sub>o x]
                      (eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e)) \<otimes> \<I>) \<cdot>
                     \<r>\<^sup>-\<^sup>1[exp (F\<^sub>o x) (F\<^sub>o x)]) \<cdot>
                    F\<^sub>a x x)\<^sup>\<up>) \<cdot>
              \<l>\<^sup>-\<^sup>1[hom\<^sub>o x] \<cdot> Id x"
      proof -
        have "\<guillemotleft>Curry[exp (F\<^sub>o x) (F\<^sub>o x), \<I>, F\<^sub>o x]
                 (eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e))
                 : exp (F\<^sub>o x) (F\<^sub>o x) \<rightarrow> exp \<I> (F\<^sub>o x)\<guillemotright>"
          using assms x F.preserves_Obj C.ide_exp
          by (intro C.Curry_in_hom) auto
        thus ?thesis
          using assms
                runit'_naturality
                  [of "Curry[exp (F\<^sub>o x) (F\<^sub>o x), \<I>, F\<^sub>o x]
                         (eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e))"]
          by force
      qed
      also have "... =
            Uncurry[hom\<^sub>o x, F\<^sub>o x]
              ((Uncurry[\<I>, F\<^sub>o x]
                  (Curry[exp (F\<^sub>o x) (F\<^sub>o x), \<I>, F\<^sub>o x]
                     (eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e))) \<cdot>
                  \<r>\<^sup>-\<^sup>1[exp (F\<^sub>o x) (F\<^sub>o x)] \<cdot> F\<^sub>a x x)\<^sup>\<up>) \<cdot>
              \<l>\<^sup>-\<^sup>1[hom\<^sub>o x] \<cdot> Id x"
        using comp_assoc by simp
      also have "... =
            Uncurry[hom\<^sub>o x, F\<^sub>o x]
              (((eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e)) \<cdot>
                   \<r>\<^sup>-\<^sup>1[exp (F\<^sub>o x) (F\<^sub>o x)] \<cdot> F\<^sub>a x x)\<^sup>\<up>) \<cdot>
              \<l>\<^sup>-\<^sup>1[hom\<^sub>o x] \<cdot> Id x"
        using assms x F.preserves_Obj C.Uncurry_Curry by auto
      also have "... =
            Uncurry[hom\<^sub>o x, F\<^sub>o x]
              (((eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e)) \<cdot>
                   (F\<^sub>a x x \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o x])\<^sup>\<up>) \<cdot>
              \<l>\<^sup>-\<^sup>1[hom\<^sub>o x] \<cdot> Id x"
        using assms x runit'_naturality F.preserves_Hom [of x x] by fastforce
      also have "... =
            Uncurry[hom\<^sub>o x, F\<^sub>o x]
              (((eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (exp (F\<^sub>o x) (F\<^sub>o x) \<otimes> e) \<cdot> (F\<^sub>a x x \<otimes> \<I>)) \<cdot>
                  \<r>\<^sup>-\<^sup>1[hom\<^sub>o x])\<^sup>\<up>) \<cdot>
              \<l>\<^sup>-\<^sup>1[hom\<^sub>o x] \<cdot> Id x"
        using comp_assoc by simp
      also have "... =
            Uncurry[hom\<^sub>o x, F\<^sub>o x]
              (((eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (F\<^sub>a x x \<otimes> e)) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o x])\<^sup>\<up>) \<cdot>
              \<l>\<^sup>-\<^sup>1[hom\<^sub>o x] \<cdot> Id x"
        using assms x F.preserves_Hom [of x x] comp_arr_dom [of e \<I>] comp_cod_arr
             interchange
        by fastforce
      also have "... =
            Uncurry[hom\<^sub>o x, F\<^sub>o x]
              (Curry[\<I>, hom\<^sub>o x, F\<^sub>o x]
                 (((eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (F\<^sub>a x x \<otimes> e)) \<cdot> \<r>\<^sup>-\<^sup>1[hom\<^sub>o x]) \<cdot> \<l>[hom\<^sub>o x])) \<cdot>
              \<l>\<^sup>-\<^sup>1[hom\<^sub>o x] \<cdot> Id x"
      proof -
        have "seq (eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (F\<^sub>a x x \<otimes> e)) \<r>\<^sup>-\<^sup>1[Hom x x]"
          using assms x F.preserves_Obj F.preserves_Hom by blast
        thus ?thesis
          using assms x C.UP_def F.preserves_Obj by auto
      qed
      also have "... =
            (((eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (F\<^sub>a x x \<otimes> e)) \<cdot> \<r>\<^sup>-\<^sup>1[Hom x x]) \<cdot> \<l>[Hom x x]) \<cdot>
              \<l>\<^sup>-\<^sup>1[Hom x x] \<cdot> Id x"
        using assms x C.Uncurry_Curry F.preserves_Obj F.preserves_Hom by force
      also have "... =
            eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (F\<^sub>a x x \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[Hom x x] \<cdot>
              (\<l>[Hom x x] \<cdot> \<l>\<^sup>-\<^sup>1[Hom x x]) \<cdot> Id x"
        using comp_assoc by simp
      also have "... = eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (F\<^sub>a x x \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[Hom x x] \<cdot> Id x"
        using assms x ide_Hom Id_in_hom comp_lunit_lunit'(1) comp_cod_arr
        by fastforce
      also have "... = eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (F\<^sub>a x x \<otimes> e) \<cdot> (Id x \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[\<I>]"
        using x Id_in_hom runit'_naturality by fastforce
      also have "... = eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> ((F\<^sub>a x x \<otimes> e) \<cdot> (Id x \<otimes> \<I>)) \<cdot> \<r>\<^sup>-\<^sup>1[\<I>]"
        using comp_assoc by simp
      also have "... = eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (F\<^sub>a x x \<cdot> Id x \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[\<I>]"
        using assms x interchange [of "F\<^sub>a x x" "Id x" e \<I>] F.preserves_Hom
              comp_arr_dom Id_in_hom
        by fastforce
      also have "... = eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> (C.Id (F\<^sub>o x) \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[\<I>]"
        using x F.preserves_Id by auto
      also have "... =
                 eval (F\<^sub>o x) (F\<^sub>o x) \<cdot> ((C.Id (F\<^sub>o x) \<otimes> F\<^sub>o x) \<cdot> (\<I> \<otimes> e)) \<cdot> \<r>\<^sup>-\<^sup>1[\<I>]"
        using assms x interchange C.Id_in_hom F.preserves_Obj comp_arr_dom
              comp_cod_arr
        by (metis in_homE mem_Collect_eq)
      also have "... = Uncurry[F\<^sub>o x, F\<^sub>o x] (C.Id (F\<^sub>o x)) \<cdot> (\<I> \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[\<I>]"
        using comp_assoc by simp
      also have "... = \<l>[F\<^sub>o x] \<cdot> (\<I> \<otimes> e) \<cdot> \<r>\<^sup>-\<^sup>1[\<I>]"
        using x F.preserves_Obj C.Id_def C.Uncurry_Curry by fastforce
      also have "... = \<l>[F\<^sub>o x] \<cdot> (\<I> \<otimes> e) \<cdot> \<l>\<^sup>-\<^sup>1[\<I>]"
        using unitor_coincidence by simp
      also have "... = \<l>[F\<^sub>o x] \<cdot> \<l>\<^sup>-\<^sup>1[F\<^sub>o x] \<cdot> e"
        using assms lunit'_naturality by fastforce
      also have "... = (\<l>[F\<^sub>o x] \<cdot> \<l>\<^sup>-\<^sup>1[F\<^sub>o x]) \<cdot> e"
        using comp_assoc by simp
      also have "... = e"
        using assms x comp_lunit_lunit' F.preserves_Obj comp_cod_arr by auto
      finally show "generating_elem (generated_transformation e) = e"
        by blast
    qed

    text\<open>
      We can now state and prove the (weak) covariant Yoneda lemma (Kelly, Section 1.9)
      for enriched categories.
    \<close>

    theorem covariant_yoneda:
    shows "bij_betw generated_transformation
             (hom \<I> (F\<^sub>o x))
             (Collect (enriched_natural_transformation C T \<alpha> \<iota>
                         Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
                         hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a))"
    proof (intro bij_betwI)
      show "generated_transformation \<in>
              hom \<I> (F\<^sub>o x) \<rightarrow> Collect
                               (enriched_natural_transformation C T \<alpha> \<iota>
                                  Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
                                  hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a)"
        using enriched_natural_transformation_generated_transformation by blast
      show "generating_elem \<in>
              Collect (enriched_natural_transformation C T \<alpha> \<iota>
                         Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
                         hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a)
                \<rightarrow> hom \<I> (F\<^sub>o x)"
        using generating_elem_in_hom by blast
      show "\<And>e. e \<in> hom \<I> (F\<^sub>o x) \<Longrightarrow>
                   generating_elem (generated_transformation e) = e"
        using element_of_generated_transformation by blast
      show "\<And>\<tau>. \<tau> \<in> Collect (enriched_natural_transformation C T \<alpha> \<iota>
                               Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
                               hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a)
                  \<Longrightarrow> generated_transformation (generating_elem \<tau>) = \<tau>"
      proof -
        fix \<tau>
        assume \<tau>: "\<tau> \<in> Collect (enriched_natural_transformation C T \<alpha> \<iota>
                                  Obj Hom Id Comp (Collect ide) exp C.Id C.Comp
                                  hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a)"
        interpret \<tau>: enriched_natural_transformation C T \<alpha> \<iota>
                       Obj Hom Id Comp \<open>Collect ide\<close> exp C.Id C.Comp
                       hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a \<tau>
          using \<tau> by blast
        show "generated_transformation (generating_elem \<tau>) = \<tau>"
        proof
          fix a
          show "generated_transformation (generating_elem \<tau>) a = \<tau> a"
            using \<tau> transformation_generated_by_element \<tau>.extensionality
                  F.extensionality C.UP_def not_arr_null null_is_zero(2)
            by (cases "a \<in> Obj") auto
        qed
      qed
    qed

  end

  subsection "Contravariant Case"

  text\<open>
    The (weak) contravariant Yoneda lemma is obtained by just replacing the enriched category
    by its opposite in the covariant version.
  \<close>

  locale contravariant_yoneda_lemma =
    opposite_enriched_category C T \<alpha> \<iota> \<sigma> Obj Hom Id Comp +
    covariant_yoneda_lemma C T \<alpha> \<iota> \<sigma> exp eval Curry Obj Hom\<^sub>o\<^sub>p Id Comp\<^sub>o\<^sub>p y F\<^sub>o F\<^sub>a
  for C :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>\<cdot>\<close> 55)
  and T :: "'a \<times> 'a \<Rightarrow> 'a"
  and \<alpha> :: "'a \<times> 'a \<times> 'a \<Rightarrow> 'a"
  and \<iota> :: "'a"
  and \<sigma> :: "'a \<times> 'a \<Rightarrow> 'a"
  and exp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and eval :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and Curry :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and Obj :: "'b set"
  and Hom :: "'b \<Rightarrow> 'b \<Rightarrow> 'a"
  and Id :: "'b \<Rightarrow> 'a"
  and Comp :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'a"
  and y :: 'b
  and F\<^sub>o :: "'b \<Rightarrow> 'a"
  and F\<^sub>a :: "'b \<Rightarrow> 'b \<Rightarrow> 'a"
  begin

    corollary contravariant_yoneda:
    shows "bij_betw generated_transformation
             (hom \<I> (F\<^sub>o y))
             (Collect
                (enriched_natural_transformation
                   C T \<alpha> \<iota> Obj Hom\<^sub>o\<^sub>p Id Comp\<^sub>o\<^sub>p (Collect ide) exp C.Id C.Comp
                   hom\<^sub>o hom\<^sub>a F\<^sub>o F\<^sub>a))"
      using covariant_yoneda by blast

  end

end
