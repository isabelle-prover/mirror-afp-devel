(*  Title:       Category
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Category"

theory Category
imports Main "~~/src/HOL/Library/FuncSet"
begin

  text {*
    This theory develops an ``object-free'' definition of category loosely following
    \cite{AHS}, Sec. 3.52-3.53.
    We define the notion ``category'' in terms of axioms that concern a single
    partial binary operation on a type, some of whose elements are to be regarded
    as the ``arrows'' of the category.

    The nonstandard definition of category has some advantages and disadvantages.
    An advantage is that only one piece of data (the composition operation) is required
    to specify a category, so the use of records is not required to bundle up several
    separate objects.  A related advantage is the fact that functors and natural
    transformations can be defined simply to be functions that satisfy certain axioms,
    rather than more complex composite objects.
    One disadvantage is that the notions of ``object'' and ``identity arrow'' are
    conflated, though this is easy to get used to.  Perhaps a more significant disadvantage
    is that each arrow of a category must carry along the information about its domain
    and codomain. This implies, for example, that the arrows of a category of sets and
    functions cannot be directly identified with functions, but rather only with functions that
    have been equipped with their domain and codomain sets.

    To represent the partiality of the composition operation of a category, we assume that the
    composition for a category has a unique zero element, which we call @{text null},
    and we consider arrows to be ``composable'' if and only if their composite is non-null.
    Functors and natural transformations are required to map arrows to arrows and be
    ``extensional'' in the sense that they map non-arrows to null.  This is so that
    equality of functors and natural transformations coincides with their extensional equality
    as functions in HOL.
    The fact that we co-opt an element of the arrow type to serve as @{text null} means that
    it is not possible to define a category whose arrows exhaust the elements of a given type.
    This presents a disadvantage in some situations.  For example, we cannot construct a
    discrete category whose arrows are directly identified with the set of \emph{all}
    elements of a given type @{typ 'a}; instead, we must pass to a larger type
    (such as @{typ "'a option"}) so that there is an element available for use as @{text null}.
    The presence of @{text null}, however, is crucial to our being able to define a
    system of introduction and elimination rules that can be applied automatically to establish
    that a given expression denotes an arrow.  Without @{text null}, we would be able to
    define an introduction rule to infer, say, that the composition of composable arrows
    is composable, but not an elimination rule to infer that arrows are composable from
    the fact that their composite is an arrow.  Having the ability to do both is critical
    to the usability of the theory.
  *}

  section "Partial Magmas"

  text {*
    A \emph{partial magma} is a partial binary operation @{text C} defined on the set
    of elements at a type @{typ 'a}.  As discussed above,
    we assume the existence of a unique element @{text null} of type @{typ 'a}
    that is a zero for @{text C}, and we use @{text null} to represent ``undefined''.
    We think of the operation @{text C} as an operation of ``composition'', and
    we regard elements @{text f} and @{text g} of type @{typ 'a} as \emph{composable}
    if @{text "C g f \<noteq> null"}.
  *}

  type_synonym 'a comp = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  locale partial_magma =
  fixes C :: "'a comp"
  assumes ex_un_null: "\<exists>!n. \<forall>f. C n f = n \<and> C f n = n"
  begin

    definition null :: 'a
    where "null = (THE n. \<forall>f. C n f = n \<and> C f n = n)"

    lemma nullI:
    assumes "\<And>f. C n f = n \<and> C f n = n"
    shows "n = null"
      using assms null_def ex_un_null the1_equality [of "\<lambda>n. \<forall>f. C n f = n \<and> C f n = n"]
      by auto
    
    lemma comp_null:
    shows "C null f = null" and "C f null = null"
      using null_def ex_un_null theI' [of "\<lambda>n. \<forall>f. C n f = n \<and> C f n = n"]
      by auto

    text {*
      A \emph{unit} is an element @{text a} such that composition of any other element
      @{text f} with @{text a} on either the left or the right results in @{text f}
      whenever the composition is defined.
    *}

    definition unit :: "'a \<Rightarrow> bool"
    where "unit a \<equiv> (\<forall>f. (C a f \<noteq> null \<longrightarrow> C a f = f) \<and> (C f a \<noteq> null \<longrightarrow> C f a = f))"

    lemma unitI:
    assumes "\<And>f. C a f \<noteq> null \<Longrightarrow> C a f = f"
    and "\<And>f. C f a \<noteq> null \<Longrightarrow> C f a = f"
    shows "unit a"
      using assms unit_def by auto

    text {*
      A \emph{domain} of an element @{text f} is a unit @{text a} for which composition of
      @{text f} with @{text a} on the right is defined.  We say that @{text f} \emph{has a domain}
      if a domain @{text a} for @{text f} exists.  The notions of \emph{codomain} and
      \emph{has a codomain} are defined similarly, using composition on the left.
      Note that, although these definitions are completely dual, the choice of terminology
      implies that we will think of composition as being written in traditional order,
      as opposed to diagram order.  It is pretty much essential to do it this way, to maintain
      compatibility with the notation for function application once we start working with
      functors and natural transformations.
    *}

    definition has_dom
    where "has_dom f \<equiv> (\<exists>a. unit a \<and> C f a \<noteq> null)"

    definition has_cod
    where "has_cod f \<equiv> (\<exists>b. unit b \<and> C b f \<noteq> null)"

    lemma has_domI:
    assumes "unit a \<and> C f a \<noteq> null"
    shows "has_dom f"
      using assms has_dom_def by blast

    lemma has_codI:
    assumes "unit b \<and> C b f \<noteq> null"
    shows "has_cod f"
      using assms has_cod_def by blast

    text {*
      An element @{text f} is an \emph{arrow} if either it has a domain or it has a codomain.
      In an arbitrary partial magma it is possible for @{text f} to have one but not the other,
      but the @{text category} locale will include assumptions to rule this out.
    *}

    definition arr :: "'a \<Rightarrow> bool"
    where "arr f \<equiv> has_dom f \<or> has_cod f"

    lemma arrI:
    assumes "has_dom f \<or> has_cod f"
    shows "arr f"
      using assms arr_def by simp

    lemma not_arr_null:
    shows "\<not>arr null"
      by (simp add: arr_def has_dom_def comp_null(1) comp_null(2) has_cod_def)

  end

  section "Categories"

  text{*
    A \emph{category} is defined to be a partial magma whose composition satisfies an
    associativity condition and in which every arrow has both a domain and a codomain.
    The associativity condition involves four ``matching conditions''
    (@{text "match_1"}, @{text "match_2"}, @{text "match_3"}, and @{text "match_4"})
    which constrain the domain of definition of the composition, and a fifth condition
    (@{text "comp_assoc'"}) which states that the results of the two ways of composing
    three elements are equal.  In the presence of the @{text "comp_assoc'"} axiom
    @{text "match_4"} can be derived from @{text "match_3"} and vice versa,
    however we retain all four conditions so that the set of axioms is self-dual,
    which is sometimes useful.  The name @{text comp_assoc'} is primed because we
    later introduce a variant form @{text comp_assoc} which is more convenient to use
    in practice but less convenient when establishing interpretations.
  *}

  locale category = partial_magma C
  for C :: "'a comp" +
  assumes match_1: "\<lbrakk> C h g \<noteq> null; C (C h g) f \<noteq> null \<rbrakk> \<Longrightarrow> C g f \<noteq> null"
  and match_2: "\<lbrakk> C h (C g f) \<noteq> null; C g f \<noteq> null \<rbrakk> \<Longrightarrow> C h g \<noteq> null"
  and match_3: "\<lbrakk> C g f \<noteq> null; C h g \<noteq> null \<rbrakk> \<Longrightarrow> C (C h g) f \<noteq> null"
  and match_4: "\<lbrakk> C g f \<noteq> null; C h g \<noteq> null \<rbrakk> \<Longrightarrow> C h (C g f) \<noteq> null"
  and comp_assoc': "\<lbrakk> C g f \<noteq> null; C h g \<noteq> null \<rbrakk> \<Longrightarrow> C h (C g f) = C (C h g) f"
  and has_dom_iff_has_cod: "has_dom f \<longleftrightarrow> has_cod f"
  begin

    lemma dom_unique:
    assumes "unit a" and "C f a \<noteq> null" and "unit a'" and "C f a' \<noteq> null"
    shows "a = a'"
      using assms unit_def match_1 by metis

    lemma cod_unique:
    assumes "unit b" and "C b f \<noteq> null" and "unit b'" and "C b' f \<noteq> null"
    shows "b = b'"
      using assms unit_def match_2 by metis

    definition dom
    where "dom f = (if has_dom f then (SOME a. unit a \<and> C f a \<noteq> null) else null)"

    definition cod
    where "cod f = (if has_cod f then (SOME b. unit b \<and> C b f \<noteq> null) else null)"

    lemma has_domD:
    assumes "has_dom f"
    shows "arr f" and "unit (dom f)" and "C f (dom f) = f"
    proof -
      from assms obtain a where A: "unit a \<and> C f a \<noteq> null" using has_dom_def by blast
      have F: "unit (dom f) \<and> C f (dom f) \<noteq> null"
        using assms dom_def has_dom_def someI_ex [of "\<lambda>a. unit a \<and> C f a \<noteq> null"] by auto
      show "arr f" using A by (simp add: arr_def assms)
      show "unit (dom f)" using A F by simp
      show "C f (dom f) = f" using A F unit_def by blast
    qed

    lemma has_codD:
    assumes "has_cod f"
    shows "arr f" and "unit (cod f)" and "C (cod f) f = f"
    proof -
      from assms obtain b where B: "unit b \<and> C b f \<noteq> null" using has_cod_def by blast
      have F: "unit (cod f) \<and> C (cod f) f \<noteq> null"
        using assms cod_def has_cod_def someI_ex [of "\<lambda>b. unit b \<and> C b f \<noteq> null"] by auto
      show "arr f" using B by (simp add: arr_def assms)
      show "unit (cod f)" using B F by simp
      show "C (cod f) f = f" using B F unit_def by blast
    qed

    lemma dom_simp:
    assumes "unit a" and "C f a \<noteq> null"
    shows "dom f = a"
    proof -
      have 1: "arr f" using assms by (simp add: has_domD(1) has_domI)
      hence "unit (dom f) \<and> C f(dom f) \<noteq> null"
        by (metis assms(1) assms(2) has_domI has_domD(2) has_domD(3) unit_def)
      thus ?thesis using assms dom_unique by blast
    qed

    lemma cod_simp:
    assumes "unit b" and "C b f \<noteq> null"
    shows "cod f = b"
    proof -
      have 1: "arr f" using assms by (simp add: has_codD(1) has_codI)
      hence "unit (cod f) \<and> C (cod f) f \<noteq> null"
        by (metis assms(1) assms(2) has_codI has_codD(2) has_codD(3) unit_def)
      thus ?thesis using assms cod_unique by blast
    qed

    text{*
      An \emph{identity} is an arrow @{text a} that is its own domain and codomain.
      We will also refer to identities as \emph{objects}.
    *}

    definition ide :: "'a \<Rightarrow> bool"
    where "ide a \<equiv> (has_dom a \<or> has_cod a) \<and> dom a = a \<and> cod a = a"

    (* Removing simp here breaks stuff, even though it is later declared as simp in "lemmas". *)
    lemma ideD [simp]:
    assumes "ide a"
    shows "arr a" and "dom a = a" and "cod a = a"
      using assms arr_def ide_def by auto

    lemma ideI_dom:
    assumes "arr a" and "dom a = a"
    shows "ide a"
      using assms
      by (metis (no_types, lifting) has_dom_iff_has_cod cod_unique ide_def has_codD(2) has_codD(3)
          has_domD(2) has_domD(3) dom_def not_arr_null)

    lemma ideI_cod:
    assumes "arr a" and "cod a = a"
    shows "ide a"
      using assms
      by (metis (no_types, lifting) has_dom_iff_has_cod dom_unique ideI_dom cod_def has_codD(2)
          has_codD(3) has_domD(2) has_domD(3) not_arr_null)

    (* Removing simp here breaks stuff, even though it is later declared as simp in "lemmas". *)
    lemma ide_dom [simp]:
    assumes "arr f"
    shows "ide (dom f)"
      using assms
      by (metis (no_types, lifting) cod_simp has_domD(2) has_domI arr_def has_domD(3)
          has_dom_iff_has_cod ideI_cod match_1 not_arr_null)
        
    (* Removing simp here breaks stuff, even though it is later declared as simp in "lemmas". *)
    lemma ide_cod [simp]:
    assumes "arr f"
    shows "ide (cod f)"
      using assms
      by (metis (no_types, lifting) arr_def cod_simp has_codD(2) has_codI has_codD(3)
          has_dom_iff_has_cod ideI_cod match_2 not_arr_null)

    text{*
      To obtain the ``only if'' direction in the next two results and in similar results later
      for composition and the application of functors and natural transformations,
      is the reason for assuming the existence of @{term null} as a special element of the
      arrow type, as opposed to, say, using option types to represent partiality.
      The presence of @{term null} allows us not only to make the ``upward'' inference that
      the domain of an arrow is again an arrow, but also to make the ``downward'' inference
      that if @{text "dom f"} is an arrow then so is @{text f}.  Similarly, we will be able
      to infer not only that if @{text f} and @{text g} are composable arrows then
      @{text "C g f"} is an arrow, but also that if @{text "C g f"} is an arrow then
      @{text f} and @{text g} are composable arrows.  These inferences allow most necessary
      facts about what terms denote arrows to be deduced automatically from minimal
      assumptions.  Typically all that is required is to assume or establish that certain
      terms denote arrows in particular hom-sets at the point where those terms are first
      introduced, and then similar facts about related terms can be derived automatically.
      Without this feature, nearly every proof would involve many tedious additional steps
      to establish that each of the terms appearing in the proof (including all its subterms)
      in fact denote arrows.
    *}

    lemma arr_dom_iff_arr:
    shows "arr (dom f) \<longleftrightarrow> arr f"
      using arrI ide_dom dom_def not_arr_null ideD by force

    lemma arr_cod_iff_arr:
    shows "arr (cod f) \<longleftrightarrow> arr f"
      using arrI ide_cod cod_def not_arr_null ideD by force

    lemma comp_arr_dom [simp]:
    assumes "arr f"
    shows "C f (dom f) = f"
      using assms by (metis arr_dom_iff_arr has_domD(3) dom_def not_arr_null)

    lemma comp_cod_arr [simp]:
    assumes "arr f"
    shows "C (cod f) f = f"
      using assms by (metis arr_cod_iff_arr cod_def has_codD(3) not_arr_null)

    lemma comp_arr_ide [simp]:
    assumes "ide a" and "dom f = a"
    shows "C f a = f"
      using assms has_domD(3) ideD(1) dom_def not_arr_null by auto

    lemma comp_ide_arr [simp]:
    assumes "ide b" and "cod f = b"
    shows "C b f = f"
      using assms cod_def has_codD(3) ideD(1) not_arr_null by auto

    lemma dom_dom:
    assumes "arr f"
    shows "dom (dom f) = dom f"
      using assms ide_dom ideD by blast

    lemma cod_cod:
    assumes "arr f"
    shows "cod (cod f) = cod f"
      using assms ide_cod ideD by blast

    lemma dom_cod:
    assumes "arr f"
    shows "dom (cod f) = cod f"
      using assms ide_cod ideD by blast

    lemma cod_dom:
    assumes "arr f"
    shows "cod (dom f) = dom f"
      using assms ide_dom ideD by blast

    lemma arr_comp [simp]:
    assumes "arr f" and "arr g" and "cod f = dom g"
    shows "arr (C g f)"
      using assms match_3
      by (metis (no_types, hide_lams) arrI comp_cod_arr comp_arr_dom comp_null(2) ex_un_null
          has_dom_def local.dom_def)

    text{*
      The following is another example of a crucial ``downward'' rule that would not be possible
      without a reserved @{term null} value.
    *}

    lemma arr_compD:
    assumes "arr (C g f)"
    shows "arr f" and "arr g" and "cod f = dom g"
    proof -
      show "arr f"
        using assms match_1 arr_def has_dom_iff_has_cod has_dom_def not_arr_null by metis
      show "arr g"
        using assms match_2 arr_def has_dom_iff_has_cod has_cod_def not_arr_null by metis
      show "cod f = dom g"
        using assms \<open>arr f\<close> \<open>arr g\<close> match_1 match_2 dom_simp cod_simp not_arr_null
        by (metis (no_types, lifting) comp_cod_arr has_dom_iff_has_cod arr_def has_codD(2))
    qed

    lemma dom_comp [simp]:
    assumes "arr f" and "arr g" and "cod f = dom g"
    shows "dom (C g f) = dom f"
    proof -
      have 0: "arr (C g f)" using assms by auto
      have 1: "arr (C f (dom f))" using assms comp_arr_dom by simp
      have "unit (dom (C g f)) \<and> C (C g f) (dom (C g f)) \<noteq> null"
        using 0 has_dom_iff_has_cod has_domD
        by (metis (no_types, lifting) arr_dom_iff_arr dom_def not_arr_null)
      moreover have "unit (dom f) \<and> C (C g f) (dom f) \<noteq> null"
      proof
        show "unit (dom f)"
          using assms(1) has_domD has_dom_iff_has_cod
          by (metis ideD(1) ide_dom dom_def not_arr_null)
        show "C (C g f) (dom f) \<noteq> null"
        proof -
          have "C g f = C g (C f (dom f))"
            using 0 comp_arr_dom by (simp add: assms(1))
          also have "... = C (C g f) (dom f)"
            using 0 1 comp_assoc' not_arr_null by metis
          finally show ?thesis using 0 not_arr_null by auto
        qed
      qed
      ultimately show ?thesis using dom_unique by blast
    qed

    lemma cod_comp [simp]:
    assumes "arr f" and "arr g" and "cod f = dom g"
    shows "cod (C g f) = cod g"
    proof -
      have 0: "arr (C g f)" using assms arr_comp by blast
      have 1: "arr (C (cod g) g)" using assms comp_cod_arr by simp
      have "unit (cod (C g f)) \<and> C (cod (C g f)) (C g f) \<noteq> null"
        using 0 has_dom_iff_has_cod has_codD
        by (metis (no_types, lifting) arr_cod_iff_arr cod_def not_arr_null)
      moreover have "unit (cod g) \<and> C (cod g) (C g f) \<noteq> null"
      proof
        show "unit (cod g)"
          using assms(2) has_codD has_dom_iff_has_cod
          by (metis cod_def ideD(1) ide_cod not_arr_null)
        show "C (cod g) (C g f) \<noteq> null"
        proof -
          have "C g f = C (C (cod g) g) f"
            using 0 comp_cod_arr by (simp add: assms(2))
          also have "... = C (cod g) (C g f)"
            using 0 1 comp_assoc' not_arr_null by metis
          finally show ?thesis using 0 not_arr_null by auto
        qed
      qed
      ultimately show ?thesis using cod_unique by blast
    qed

    lemma ide_comp_simp:
    assumes "ide (C g f)"
    shows "C g f = dom f"
      using assms
      by (metis arr_compD(1) arr_compD(2) arr_compD(3) dom_comp ideD(1) ideD(2))

    text{*
      Here we define some common configurations of arrows.
      These are all defined as abbreviations, because we want all ``diagrammatic'' assumptions
      in a theorem to reduce readily to a conjunction of assertions of the form @{text "arr f"},
      @{text "dom f = X"}, or @{text "cod f = Y"}.
    *}

    abbreviation seq
    where "seq g f \<equiv> arr f \<and> arr g \<and> cod f = dom g"

    abbreviation endo
    where "endo f \<equiv> arr f \<and> dom f = cod f"
     
    abbreviation par
    where "par f g \<equiv> arr f \<and> arr g \<and> dom f = dom g \<and> cod f = cod g"

    abbreviation antipar
    where "antipar f g \<equiv> arr f \<and> arr g \<and> dom f = cod g \<and> cod f = dom g"

    abbreviation span
    where "span f g \<equiv> arr f \<and> arr g \<and> dom f = dom g"

    abbreviation cospan
    where "cospan f g \<equiv> arr f \<and> arr g \<and> cod f = cod g"
   
    text{*
      The following form of associativity seems to work better in practical proofs
      than the version in the category locale assumptions, however it is inconvenient
      to establish when proving an interpretation, because of the presence of
      @{text dom} and @{term cod} in the hypotheses.
    *}

    lemma comp_assoc [iff]:
    assumes "seq g f" and "seq h g"
    shows "C (C h g) f = C h (C g f)"
    proof -
      have "arr (C g f) \<and> arr (C h g) \<longleftrightarrow> arr f \<and> arr g \<and> arr h \<and> cod f = dom g \<and> cod g = dom h"
        using assms(1) assms(2) by simp
      thus ?thesis
        using assms comp_assoc' not_arr_null by metis
    qed

    text{*
      Diagrammatic assumptions required in proofs are often conveniently stated
      in terms of ``hom-sets''.  Note that @{text "f \<in> hom (dom f) (cod f)"} is
      equivalent to @{term "arr f"}, and that we can also use @{text "f \<in> hom a (cod f)"}
      or @{text "f \<in> hom (dom f) b"} when we don't have any other name for the codomain or
      domain of @{text f}.
    *}

    abbreviation hom
    where "hom a b \<equiv> {f. arr f \<and> dom f = a \<and> cod f = b}"

    text{*
      The intention below was to develop the basic results above without having
      any facts implicitly applied, and only then to set annotations for some of
      the facts.  However, I found that if I did not annotate some
      of the facts as they were introduced, they did not get used automatically later on.
      This can be verified and/or debugged by removing the annotations above and seeing
      what breaks in theories that depend on this one.  This behavior is mysterious and
      I don't know the reason for it.
    *}

    lemmas dom_dom cod_cod dom_cod cod_dom dom_comp cod_comp arr_comp comp_assoc
           ide_dom ide_cod comp_arr_dom comp_cod_arr comp_ide_arr comp_arr_ide
           ideD not_arr_null comp_null [simp]
    lemmas ide_dom ide_cod ideD [elim]
    lemmas has_domI has_codI ideI_dom [intro]

  end

  section "Classical Categories"

  text{*
    In this section we define a secondary axiomatization of categories, @{text classical_category},
    which is a more traditional one, except that in view of the totality of functions in HOL
    we need to introduce predicates @{text Obj} and @{text Arr} that characterize the bona fide
    objects and arrows among the elements of their respective types.
    A category defined this way is not ``extensional'', in the sense that there
    will in general be categories with the same sets of objects and arrows,
    such that @{text Dom}, @{text Cod}, @{text Id}, and @{text Comp} agree on these
    objects and arrows, but they do not necessarily agree on other values of the corresponding
    types.

    We show below that an interpretation of the @{text category} induces an interpretation
    of the @{text classical_category} locale.
    Conversely, we show that if @{text Obj}, @{text Arr}, @{text Dom}, @{text Cod},
    @{text Id}, and @{text Comp} comprise an interpretation of @{text classical_category},
    then we can define from them a partial composition that interprets the @{text category} locale.
    Moreover, the predicate derived @{text arr} derived from this partial composition agrees
    with the originally given predicate @{text Arr}, the notions @{text dom}, @{text cod},
    and @{text comp} derived from the partial composition agree with the originally given
    @{text Dom}, @{text Cod}, and @{text Comp} on arguments that satisfy @{text arr},
    and the identities derived from the partial composition are in bijective correspondence with
    the elements that satisfy the originally given predicate @{text Obj}.

    In some cases, rather than defining a construction on categories directly
    in terms of the partial-composition-based axioms, it can be simpler to
    define the construction in classical terms in a convenient way, and then
    extract a partial composition via the construction given here.
  *}

  locale classical_category =
  fixes Obj :: "'obj \<Rightarrow> bool"
  and Arr :: "'arr \<Rightarrow> bool"
  and Dom :: "'arr \<Rightarrow> 'obj"
  and Cod :: "'arr \<Rightarrow> 'obj"
  and Id :: "'obj \<Rightarrow> 'arr"
  and Comp :: "'arr \<Rightarrow> 'arr \<Rightarrow> 'arr"
  assumes Obj_Dom: "Arr f \<Longrightarrow> Obj (Dom f)"
  and Obj_Cod: "Arr f \<Longrightarrow> Obj (Cod f)"
  and Arr_Id [simp]: "Obj a \<Longrightarrow> Arr (Id a)"
  and Dom_Id [simp]: "Obj a \<Longrightarrow> Dom (Id a) = a"
  and Cod_Id [simp]: "Obj a \<Longrightarrow> Cod (Id a) = a"
  and Arr_Comp [simp]: "\<lbrakk> Arr f; Arr g; Cod f = Dom g \<rbrakk> \<Longrightarrow> Arr (Comp g f)"
  and Comp_assoc [simp]: "\<lbrakk> Arr f; Arr g; Arr h; Cod f = Dom g; Cod g = Dom h \<rbrakk>
                                              \<Longrightarrow> Comp (Comp h g) f = Comp h (Comp g f)"
  and Dom_Comp [simp]: "\<lbrakk> Arr f; Arr g; Cod f = Dom g \<rbrakk> \<Longrightarrow> Dom (Comp g f) = Dom f"
  and Cod_Comp [simp]: "\<lbrakk> Arr f; Arr g; Cod f = Dom g \<rbrakk> \<Longrightarrow> Cod (Comp g f) = Cod g"
  and Comp_Arr_Id_Dom [simp]: "Arr f \<Longrightarrow> Comp f (Id (Dom f)) = f"
  and Comp_Id_Cod_Arr [simp]: "Arr f \<Longrightarrow> Comp (Id (Cod f)) f = f"
  begin

    abbreviation Seq
    where "Seq g f \<equiv> (Arr f \<and> Arr g \<and> Cod f = Dom g)"

    text{*
      Because @{term Arr} might be the universal predicate for type @{typ 'arr},
      it is necessary to pass to type @{typ "'arr option"} in order to have a value
      available to serve as @{text null}.
    *}

    definition comp :: "'arr option \<Rightarrow> 'arr option \<Rightarrow> 'arr option"
    where "comp g f = (if f \<noteq> None \<and> g \<noteq> None \<and> Seq (the g) (the f)
                       then Some (Comp (the g) (the f)) else None)"

    interpretation C: partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. comp n f = n \<and> comp f n = n"
      proof
        show "\<forall>f. comp None f = None \<and> comp f None = None"
          using comp_def by auto
        show "\<And>n. \<forall>f. comp n f = n \<and> comp f n = n \<Longrightarrow> n = None"
          by (metis comp_def)
      qed
    qed

    lemma null_char:
    shows "C.null = None"
    proof -
      let ?P = "\<lambda>n. \<forall>f. comp n f = n \<and> comp f n = n"
      have "?P None" using comp_def by auto
      hence "(THE n. ?P n) = None"
        using C.ex_un_null the1_equality [of ?P] by simp
      thus ?thesis using C.null_def by auto
    qed

    text{*
      It is typically not necessary to exactly characterize the units for a
      partial composition in order to establish that it defines a category;
      often it is sufficient simply to show that there are ``enough units''.
      That is the case here.
    *}

    lemma unit_Some_Id:
    assumes "Obj A"
    shows "C.unit (Some (Id A))"
    proof -
      have "\<And>f. comp f (Some (Id A)) \<noteq> C.null \<Longrightarrow> comp f (Some (Id A)) = f"
      proof -
        fix f
        assume f: "comp f (Some (Id A)) \<noteq> C.null"
        hence 1: "f = Some (the f) \<and> Seq (the f) (Id A)"
          using null_char comp_def by (metis option.collapse option.sel)
        hence "Comp (the f) (Id A) = the f" by (simp add: assms)
        thus "comp f (Some (Id A)) = f" using f 1 comp_def by simp
      qed
      moreover have "\<And>f. comp (Some (Id A)) f \<noteq> C.null \<Longrightarrow> comp (Some (Id A)) f = f"
      proof -
        fix f
        assume f: "comp (Some (Id A)) f \<noteq> C.null"
        hence 1: "f = Some (the f) \<and> Seq (Id A) (the f)"
          using null_char comp_def by (metis option.collapse option.sel)
        hence "Comp (Id A) (the f) = the f" using assms by auto
        thus "comp (Some (Id A)) f = f" using f 1 comp_def by simp
      qed
      ultimately show ?thesis using C.unit_def null_char by auto
    qed

    lemma arr_char:
    shows "C.arr f \<longleftrightarrow> f \<noteq> None \<and> Arr (the f)"     
    proof
      assume f: "C.arr f"
      have 1: "f \<noteq> None"
        using f null_char
        by (metis C.arr_def C.has_cod_def C.has_dom_def comp_def)
      then have "Arr (the f)"
        using f 
        by (metis C.arr_def C.has_cod_def C.has_dom_def local.comp_def null_char)
      with 1 show "f \<noteq> None \<and> Arr (the f)" by auto
    next
      assume f: "f \<noteq> None \<and> Arr (the f)"
      have "Seq (the f) (Id (Dom (the f)))" using f Obj_Dom by simp
      hence "comp f (Some (Id (Dom (the f)))) \<noteq> None" using f comp_def by auto
      moreover have "C.unit (Some (Id (Dom (the f))))"
        using f unit_Some_Id by (simp add: Obj_Dom)
      ultimately have "C.has_dom f" using C.has_dom_def null_char by auto
      thus "C.arr f" by (simp add: C.arr_def)
    qed

    lemma comp_simp:
    assumes "comp g f \<noteq> C.null"
    shows "comp g f = Some (Comp (the g) (the f))"
    proof -
      have "f \<noteq> None \<and> g \<noteq> None \<and> Seq (the g) (the f)"
        using assms null_char comp_def by metis
      thus "comp g f = Some (Comp (the g) (the f))" using comp_def by auto
    qed

    interpretation C: category comp
    proof
      fix f g h
      assume gf: "comp g f \<noteq> C.null" and hgf: "comp h (comp g f) \<noteq> C.null"
      show "comp h g \<noteq> C.null"
        using gf hgf Cod_Comp comp_simp comp_def null_char
        by (metis option.distinct(1) option.sel)
      next
      fix f g h
      assume hgf: "comp (comp h g) f \<noteq> C.null" and hg: "comp h g \<noteq> C.null"
      show "comp g f \<noteq> C.null"
        using hgf hg Dom_Comp comp_simp comp_def null_char
        by (metis option.distinct(1) option.sel)
      next
      fix f g h
      assume gf: "comp g f \<noteq> C.null" and hg: "comp h g \<noteq> C.null"
      show "comp h (comp g f) \<noteq> C.null"
        using gf hg comp_simp comp_def null_char Arr_Comp Cod_Comp
        by (metis option.distinct(1) option.sel)
      show "comp (comp h g) f \<noteq> C.null"
        using gf hg comp_simp comp_def null_char Arr_Comp Dom_Comp
        by (metis option.distinct(1) option.sel)
      next
      fix f
      show "C.has_dom f \<longleftrightarrow> C.has_cod f"
        unfolding C.has_dom_def C.has_cod_def
        using arr_char null_char Arr_Id Dom_Id Cod_Id Obj_Dom Obj_Cod unit_Some_Id comp_def
        by (metis option.distinct(1) option.sel)
      next
      fix f g h
      assume gf: "comp g f \<noteq> C.null" and hg: "comp h g \<noteq> C.null"
      show "comp h (comp g f) = comp (comp h g) f"
      proof -
        have 1: "f = Some (the f) \<and> g = Some (the g) \<and> Seq (the g) (the f)
                \<and> comp g f = Some (Comp (the g) (the f))"
          using gf comp_simp arr_char null_char comp_def by (metis option.collapse)
        have 2: "h = Some (the h) \<and> Seq (the h) (the g) \<and> comp h g = Some (Comp (the h) (the g))"
          using 1 hg comp_simp arr_char null_char comp_def by (metis option.collapse)
        show ?thesis
          using 1 2 Comp_assoc null_char comp_def Arr_Comp Cod_Comp Dom_Comp by simp
      qed
    qed

    theorem induces_category:
    shows "category comp" ..

    text{*
      The arrows of the classical category are in bijective correspondence with the
      arrows of the category defined by @{term comp}, and the originally given
      @{term Dom}, @{term Cod}, and @{term Comp} coincide along this bijection with
      @{term C.dom}, @{term C.cod}, and @{term comp}.
    *}

    lemma bij_betw_Arr_arr:
    shows "bij_betw Some (Collect Arr) (Collect C.arr)"
    proof (intro bij_betwI)
      show "Some \<in> Collect Arr \<rightarrow> Collect C.arr" using arr_char by auto
      show "the \<in> Collect C.arr \<rightarrow> Collect Arr" using arr_char by auto
      show "\<And>x. x \<in> Collect Arr \<Longrightarrow> the (Some x) = x" by auto
      show "\<And>y. y \<in> Collect C.arr \<Longrightarrow> Some (the y) = y" using arr_char by auto
    qed

    lemma dom_char:
    shows "C.dom f = (if C.arr f then Some (Id (Dom (the f))) else None)"
    proof (cases "C.arr f")
      assume f: "C.arr f"
      hence "C.dom f = Some (Id (Dom (the f)))"
        using unit_Some_Id
        by (simp add: Obj_Dom arr_char comp_def null_char C.dom_simp)
      thus ?thesis using f by auto
      next
      assume "\<not>C.arr f"
      thus ?thesis using C.dom_def null_char C.arrI by auto
    qed

    lemma cod_char:
    shows "C.cod f = (if C.arr f then Some (Id (Cod (the f))) else None)"
    proof (cases "C.arr f")
      assume f: "C.arr f"
      hence "C.cod f = Some (Id (Cod (the f)))"
        by (metis C.comp_cod_arr C.dom_cod arr_char comp_def dom_char)
      thus ?thesis using f by auto
      next
      assume "\<not>C.arr f"
      thus ?thesis using C.cod_def null_char C.arrI by auto
    qed

    lemma comp_char:
    shows "comp g f = (if f \<noteq> None \<and> g \<noteq> None \<and> Seq (the g) (the f)
                       then Some (Comp (the g) (the f)) else None)"
      using comp_def by simp

    text{*
      The objects of the classical category are in bijective correspondence with
      the identities of the category defined by comp.
    *}

    lemma ide_char:
    shows "C.ide a \<longleftrightarrow> Arr (the a) \<and> a = Some (Id (Dom (the a)))"
    proof
      assume a: "C.ide a"
      have 1: "C.arr a" using a C.ideD by blast
      hence "a \<noteq> None \<and> Arr (the a)" using arr_char by auto
      moreover have "a = Some (Id (Dom (the a)))"
        using a 1 dom_char using C.ideD(2) by auto
      ultimately show "Arr (the a) \<and> a = Some (Id (Dom (the a)))" by auto
      next
      assume a: "Arr (the a) \<and> a = Some (Id (Dom (the a)))"
      show "C.ide a"
        using a arr_char dom_char C.ideI_dom by force
    qed

    lemma bij_betw_Obj_ide:
    shows "bij_betw (Some o Id) (Collect Obj) (Collect C.ide)"
    proof (intro bij_betwI)
      show "Some o Id \<in> Collect Obj \<rightarrow> Collect C.ide"
        by (simp add: ide_char)
      show "Dom o the \<in> Collect C.ide \<rightarrow> Collect Obj"
        by (simp add: Obj_Dom ide_char)
      fix x
      assume x: "x \<in> Collect Obj"
      show "(Dom o the) ((Some o Id) x) = x"
        using x by simp
      next
      fix y
      assume y: "y \<in> Collect C.ide"
      show "(Some o Id) ((Dom o the) y) = y"
        using y using C.ideD(1) C.ideD(2) dom_char by auto
    qed

  end

  sublocale classical_category \<subseteq> category comp
    using induces_category by auto

  text{*
    A category defined using the nonstandard, partial-composition-based axiomatization
    admits an interpretation of the classical axioms, and the composition derived
    from this interpretation coincides with the originally given one.
  *}

  context category
  begin

    theorem is_classical_category:
    shows "classical_category ide arr dom cod dom C"
      apply unfold_locales by auto

    interpretation CC: classical_category ide arr dom cod dom C
      using is_classical_category by auto

    text{*
      In the next result we do not achieve exact agreement, because @{term C} might give
      non-@{term null}, non-arrow results for uncomposable arguments, whereas @{term CC.comp}
      by definition always returns @{term null} in such cases.
      This could be avoided by adding to the category locale the assumption
      @{term "\<not>seq f g \<Longrightarrow> C f g = null"}, but there seems to be little point in doing so,
      as it would add an additional proof obligation every time a category is constructed.
    *}

    lemma C_equals_CC_comp:
    assumes "seq g f"
    shows "C g f = the (CC.comp (Some g) (Some f))"
      using assms CC.comp_def by auto

  end

end
