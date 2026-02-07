(*  Title:       SetsCat
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2026
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "The Category of Small Sets"

theory SetsCat
imports Category3.SetCat Category3.CategoryWithPullbacks Category3.CartesianClosedCategory
        Category3.EquivalenceOfCategories Category3.Colimit Universe
begin

  text\<open>
    In this section we consider the category of small sets and functions between
    them as an exemplifying instance of the pattern we propose for working with large categories
    in HOL.  We define a locale \<open>sets_cat\<close>, which axiomatizes a category with terminal object,
    such that each object determines a ``small'' set (the set of its global elements),
    there is an object corresponding to any externally given small set, and such that
    the hom-sets between objects are in bijection with the small extensional functions
    between sets of global elements.  We show that this locale characterizes the category
    of small sets and functions, in the sense that, for a fixed notion of smallness,
    any two interpretations of the \<open>sets_cat\<close> locale are equivalent as categories.
    We then proceed to derive various familiar properties of a category of sets; assuming
    in each case that the notion of ``smallness'' satisfies suitable conditions as defined
    in the theory \<open>Smallness\<close>, and that the collection of all arrows of the
    category satisfies suitable closure conditions as defined in the theory
    \<open>Universe\<close>.  In particular, we show if the collection of arrows
    forms a ``universe'', then the category is well-pointed, small-complete and small co-complete,
    cartesian closed, has a subobject classifier and a natural numbers object,
    and splits all epimorphisms.
  \<close>

  section "Basic Definitions and Properties"

  text\<open>
    We will describe the category of small sets and functions as a certain kind of category
    with terminal object, which has been equipped with a notion of ``smallness'' that
    specifies what sets will correspond to objects in the category.
  \<close>

  locale sets_cat_base =
    smallness sml +
    category_with_terminal_object C
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    sublocale embedding \<open>Collect arr\<close> .

    text\<open>
      Every object in the category determines a set: its set of global elements
      (we make an arbitrary choice of terminal object).
    \<close>

    abbreviation Set
    where "Set \<equiv> hom \<one>\<^sup>?"

    text\<open>
      Every arrow in the category determines an extensional function between
      sets of global elements.
    \<close>

    definition Fun
    where "Fun f x \<equiv> if x \<in> Set (dom f) then f \<cdot> x else null"

    abbreviation Hom
    where "Hom a b \<equiv> (Set a \<rightarrow> Set b) \<inter> {F. \<forall>x. x \<notin> Set a \<longrightarrow> F x = null}"

    lemma Fun_in_Hom:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "Fun f \<in> Hom a b"
      using assms Fun_def by auto

    lemma Set_some_terminal:
    shows "Set some_terminal = {some_terminal}"
      using ide_in_hom terminal_def terminal_some_terminal by auto

    lemma Fun_some_terminator:
    assumes "ide a"
    shows "Fun \<t>\<^sup>?[a] = (\<lambda>x. if x \<in> Set a then \<one>\<^sup>? else null)"
      unfolding Fun_def
      using assms elementary_category_with_terminal_object.trm_naturality
            elementary_category_with_terminal_object.trm_one
            extends_to_elementary_category_with_terminal_object
      by fastforce

    text\<open>
      The following function will allow us to obtain an object corresponding to an
      externally given set.  The set of global elements of the object is to be
      equipollent with the given set.  We give the definition here, but of course
      it will be necessary to prove that this function actually does produce such
      an object under suitable conditions.
    \<close>

    definition mkide :: "'a set \<Rightarrow> 'U"
    where "mkide A \<equiv> SOME a. ide a \<and> Set a \<approx> A"

  end

  text\<open>
    The following locale states our axioms for the category of small sets and functions.
    The axioms assert: (1) that the set of global elements of every object is small;
    (2) that the mapping from hom-sets to extensional functions between small sets
    of global elements is injective and surjective; and (3) that the category is ``replete''
    in the sense that for every small set of arrows of the category there exists an object
    whose set of elements is equipollent with it.
  \<close>

  locale sets_cat =
    sets_cat_base sml C
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55) +
  assumes small_Set: "ide a \<Longrightarrow> small (Set a)"
  and inj_Fun: "\<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> inj_on Fun (hom a b)"
  and surj_Fun: "\<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> Hom a b \<subseteq> Fun ` (hom a b)"
  and repleteness_ax: "\<lbrakk>small A; A \<subseteq> Collect arr\<rbrakk> \<Longrightarrow> \<exists>a. ide a \<and> Set a \<approx> A"
  begin

    text\<open>
      It is convenient to extend the repleteness property to apply to any small set,
      at any type, which happens to have an embedding into the collection of arrows of
      the category.
    \<close>

    lemma repleteness:
    assumes "small A" and "embeds A"
    shows "\<exists>a. ide a \<and> Set a \<approx> A"
      by (metis assms(1,2) eqpoll_trans inj_on_image_eqpoll_self repleteness_ax small_image_iff)

    text\<open>
      We obtain a pair of inverse comparison maps between an externally given small set \<open>A\<close>
      and the set of global elements of the object \<open>mkide a\<close> corresponding to it.
      The map \<open>IN\<close> encodes each element of \<open>A\<close> as a global element of \<open>mkide A\<close>.
      The inverse map \<open>OUT\<close> decodes global elements of \<open>mkide A\<close> to the corresponding
      elements of \<open>A\<close>.
      We will need to pay attention to these comparison maps when relating notions internal
      to the category to notions external to it.  However, when working completely internally
      to the category these maps do not appear at all.
    \<close>

    definition OUT :: "'a set \<Rightarrow> 'U \<Rightarrow> 'a"
    where "OUT A \<equiv> SOME F. bij_betw F (Set (mkide A)) A"

    abbreviation IN :: "'a set \<Rightarrow> 'a \<Rightarrow> 'U"
    where "IN A \<equiv> inv_into (Set (mkide A)) (OUT A)"

    text\<open>
      The following is the main fact that allows us to produce objects of the category.
      It states that, given any small set \<open>A\<close> for which there is some embedding into the
      collection of arrows of the category, there exists a corresponding object \<open>mkide A\<close>
      whose set of global elements is equipollent to \<open>A\<close>.
    \<close>

    lemma ide_mkide:
    assumes "small A" and "embeds A"
    shows [intro]: "ide (mkide A)"
    and "Set (mkide A) \<approx> A"
    proof -
      have "ide (mkide A) \<and> Set (mkide A) \<approx> A"
        using assms repleteness mkide_def someI_ex
        by (metis (lifting) HOL.ext)
      thus "ide (mkide A)" and "Set (mkide A) \<approx> A"
        using assms by auto
    qed

    lemma bij_OUT:
    assumes "small A" and "embeds A"
    shows "bij_betw (OUT A) (Set (mkide A)) A"
      unfolding OUT_def
      using assms ide_mkide(2) someI_ex [of "\<lambda>F. bij_betw F (Set (mkide A)) A"] eqpoll_def
      by blast

    lemma bij_IN:
    assumes "small A" and "embeds A"
    shows "bij_betw (IN A) A (Set (mkide A))"
      using assms bij_OUT bij_betw_inv_into by blast

    lemma OUT_elem_of:
    assumes "small A" and "embeds A" and "\<guillemotleft>x : \<one>\<^sup>? \<rightarrow> mkide A\<guillemotright>"
    shows "OUT A x \<in> A"
      by (metis CollectI assms(1,2,3) bij_betw_apply bij_OUT)

    lemma IN_in_hom:
    assumes "small A" and "embeds A" and "x \<in> A" and "a = mkide A"
    shows "\<guillemotleft>IN A x : \<one>\<^sup>? \<rightarrow> a\<guillemotright>"
      by (metis (mono_tags, lifting) Ball_Collect assms(1,2,3,4) bij_betw_def bij_OUT
          inv_into_into set_eq_subset)

    lemma IN_OUT:
    assumes "small A" and "embeds A"
    shows "x \<in> Set (mkide A) \<Longrightarrow> IN A (OUT A x) = x"
      using assms bij_OUT(1)
      by (metis bij_betw_inv_into_left)

    lemma OUT_IN:
    assumes "small A" and "embeds A"
    shows "x \<in> A \<Longrightarrow> OUT A (IN A x) = x"
      using assms bij_OUT(1)
      by (metis bij_betw_inv_into_right)

    lemma Fun_IN:
    assumes "small A" and "embeds A" and "y \<in> A"
    shows "Fun (IN A y) = (\<lambda>x. if x = \<one>\<^sup>? then IN A y else null)"
    proof
      fix x
      show "Fun (IN A y) x = (if x = \<one>\<^sup>? then IN A y else null)"
      proof (cases "x \<in> Set \<one>\<^sup>?")
        case False
        show ?thesis
          using False Fun_def
          by (metis IN_in_hom Set_some_terminal assms(1,2,3) in_homE singleton_iff)
        next
        case True
        have x: "x = \<one>\<^sup>?"
          using True Set_some_terminal by blast
        have "Fun (IN A y) x = IN A y \<cdot> \<one>\<^sup>?"
          using Fun_def dom_eqI ide_some_terminal ext x by auto
        also have "... = (if x = \<one>\<^sup>? then IN A y else null)"
          by (metis (lifting) HOL.ext IN_in_hom assms(1,2,3) comp_arr_dom in_homE x)
        finally show ?thesis by blast
      qed
    qed

    text\<open>
      The following function enables us to obtain an arrow of the category by specifying
      an extensional function between sets of global objects.
    \<close>

    definition mkarr :: "'U \<Rightarrow> 'U \<Rightarrow> ('U \<Rightarrow> 'U) \<Rightarrow> 'U"
    where "mkarr a b F \<equiv> if ide a \<and> ide b \<and> F \<in> Hom a b
                          then SOME f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> Fun f = F
                          else null"

    lemma mkarr_in_hom [intro]:
    assumes "ide a" and "ide b" and "F \<in> Hom a b"
    shows "\<guillemotleft>mkarr a b F : a \<rightarrow> b\<guillemotright>"
    proof -
      have "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> Fun f = F"
        using assms surj_Fun [of a b] by blast
      thus ?thesis
        unfolding mkarr_def
        using assms someI_ex [of "\<lambda>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> Fun f = F"] by auto
    qed

    lemma arr_mkarr [intro, simp]:
    assumes "ide a" and "ide b" and "F \<in> Hom a b"
    shows "arr (mkarr a b F)"
      using assms mkarr_in_hom by blast

    lemma arr_mkarrD [dest]:
    assumes "arr (mkarr a b F)"
    shows "ide a" and "ide b" and "F \<in> Hom a b"
      by (metis (lifting) assms mkarr_def not_arr_null)+

    lemma arr_mkarrE [elim]:
    assumes "arr (mkarr a b F)"
    and "\<lbrakk>ide a; ide b; F \<in> Hom a b\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms by auto

    lemma dom_mkarr [simp]:
    assumes "arr (mkarr a b F)"
    shows "dom (mkarr a b F) = a"
      by (meson arr_mkarrE assms in_homE mkarr_in_hom)

    lemma cod_mkarr [simp]:
    assumes "arr (mkarr a b F)"
    shows "cod (mkarr a b F) = b"
      by (meson arr_mkarrE assms in_homE mkarr_in_hom)

    lemma Fun_mkarr [simp]:
    assumes "arr (mkarr a b F)"
    shows "Fun (mkarr a b F) = F"
    proof -
      have "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> Fun f = F"
        using assms surj_Fun [of a b] by blast
      thus ?thesis
        unfolding mkarr_def
        using assms someI_ex [of "\<lambda>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> Fun f = F"] by auto
    qed

    lemma mkarr_Fun:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "mkarr a b (Fun f) = f"
    proof -
      have "\<guillemotleft>mkarr a b (Fun f) : a \<rightarrow> b\<guillemotright> \<and> Fun (mkarr a b (Fun f)) = Fun f"
        by (metis (lifting) Fun_in_Hom Fun_mkarr assms ide_cod ide_dom in_homE mkarr_in_hom)
      thus ?thesis
        using assms inj_Fun inj_onD [of Fun "hom a b" "mkarr a b (Fun f)" f]
        by blast
    qed

    text\<open>
      The locale assumptions ensure that, for any two objects \<open>a\<close> and \<open>b\<close>,
      there is a bijection between the hom-set \<open>hom a b\<close> and the set \<open>Hom a b\<close>
      of extensional functions from \<open>Set a\<close> to \<open>Set b\<close>.
    \<close>

    lemma bij_Fun:
    assumes "ide a" and "ide b"
    shows "bij_betw Fun (hom a b) (Hom a b)"
    and "bij_betw (mkarr a b) (Hom a b) (hom a b)"
    proof -
      have 1: "Fun \<in> hom a b \<rightarrow> Hom a b"
        using Fun_in_Hom by blast
      have 2: "mkarr a b \<in> Hom a b \<rightarrow> hom a b"
        using assms mkarr_in_hom by auto
      have 3: "\<And>F. F \<in> Hom a b \<Longrightarrow> Fun (mkarr a b F) = F"
        using Fun_mkarr assms(1,2) mkarr_in_hom by auto
      have 4: "\<And>f. f \<in> hom a b \<Longrightarrow> mkarr a b (Fun f) = f"
        using assms mkarr_Fun by auto
      show "bij_betw Fun (hom a b) (Hom a b)"
        using 1 2 3 4
        by (intro bij_betwI) auto
      show "bij_betw (mkarr a b) (Hom a b) (hom a b)"
        using 1 2 3 4
        by (intro bij_betwI) auto
    qed

    lemma arr_eqI:
    assumes "par t u" and "Fun t = Fun u"
    shows "t = u"
      using assms by (metis (lifting) arr_iff_in_hom mkarr_Fun)

    lemma arr_eqI':
    assumes "in_hom f a b" and "in_hom g a b"
    and "\<And>x. in_hom x \<one>\<^sup>? a \<Longrightarrow> f \<cdot> x = g \<cdot> x"
    shows "f = g"
      using assms arr_eqI [of f g] in_homE Fun_def by fastforce

    lemma Fun_arr:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "Fun f = (\<lambda>x. if x \<in> Set a then f \<cdot> x else null)"
      using assms Fun_def by auto

    lemma Fun_ide:
    assumes "ide a"
    shows "Fun a = (\<lambda>x. if x \<in> Set a then x else null)"
      by (metis (lifting) CollectD CollectI assms comp_cod_arr in_homE ide_char Fun_def)

    lemma Fun_comp:
    assumes "seq t u"
    shows "Fun (t \<cdot> u) = Fun t \<circ> Fun u"
      unfolding Fun_def
      using assms comp_assoc by force

    lemma mkarr_comp:
    assumes "seq g f"
    shows "mkarr (dom f) (cod g) (Fun g \<circ> Fun f) = g \<cdot> f"
      by (metis (lifting) Fun_comp assms cod_comp dom_comp in_homI mkarr_Fun)

    lemma comp_mkarr:
    assumes "arr (mkarr a b F)" and "arr (mkarr b c G)"
    shows "mkarr b c G \<cdot> mkarr a b F = mkarr a c (G \<circ> F)"
      using assms Fun_mkarr mkarr_comp [of "mkarr b c G" "mkarr a b F"] by simp

    lemma app_mkarr:
    assumes "in_hom (mkarr a b F) a b" and "in_hom x \<one>\<^sup>? a"
    shows "mkarr a b F \<cdot> x = F x"
      using assms Fun_mkarr
      by (metis Fun_def in_homE mem_Collect_eq)

    lemma ide_as_mkarr:
    assumes "ide a"
    shows "mkarr a a (\<lambda>x. if x \<in> Set a then x else null) = a"
      using assms Fun_ide Fun_mkarr
      by (intro arr_eqI) auto

    text\<open>
      An object \<open>a\<close> is terminal if and only if its set of global elements \<open>Set a\<close>
      is a singleton set.
    \<close>

    lemma terminal_char:
    shows "terminal a \<longleftrightarrow> ide a \<and> (\<exists>!x. x \<in> Set a)"
    proof
      show "terminal a \<Longrightarrow> ide a \<and> (\<exists>!x. x \<in> Set a)"
        using terminal_def terminal_some_terminal by auto
      assume a: "ide a \<and> (\<exists>!x. x \<in> Set a)"
      show "terminal a"
      proof
        show "ide a"
          using a by blast
        show "\<And>b. ide b \<Longrightarrow> \<exists>!f. \<guillemotleft>f : b \<rightarrow> a\<guillemotright>"
        proof -
          fix b
          assume b: "ide b"
          have "\<guillemotleft>mkarr b a (\<lambda>x. if x \<in> Set b then THE y. y \<in> Set a else null) : b \<rightarrow> a\<guillemotright>"
            using a b theI [of "\<lambda>y. y \<in> Set a"]
            by (intro mkarr_in_hom) fastforce+
          moreover have "\<And>t u. \<lbrakk>\<guillemotleft>t : b \<rightarrow> a\<guillemotright>; \<guillemotleft>u : b \<rightarrow> a\<guillemotright>\<rbrakk> \<Longrightarrow> t = u"
            using a Fun_def by (intro arr_eqI) fastforce+
          ultimately show "\<exists>!f. \<guillemotleft>f : b \<rightarrow> a\<guillemotright>" by blast
        qed
      qed
    qed

    text\<open>
      An object \<open>a\<close> is initial if and only if its set of global elements \<open>Set a\<close>
      is the empty set, except in the degenerate situation in which every object
      is both an initial and a terminal object.
    \<close>

    lemma initial_char:
    shows "initial a \<longleftrightarrow> ide a \<and> (Set a = {} \<or> (\<forall>b. ide b \<longrightarrow> terminal b))"
    proof -
      have "\<forall>b. ide b \<longrightarrow> terminal b \<Longrightarrow> \<forall>b. ide b \<longrightarrow> initial b"
        by (simp add: initialI terminal_def)
      moreover have "\<exists>b. ide b \<and> \<not> terminal b \<Longrightarrow> \<forall>a. initial a \<longleftrightarrow> ide a \<and> Set a = {}"
      proof -
        assume 1: "\<exists>b. ide b \<and> \<not> terminal b"
        obtain b where b: "ide b \<and> \<not> terminal b"
          using 1 by blast
        show "\<forall>a. initial a \<longleftrightarrow> ide a \<and> Set a = {}"
        proof (intro allI iffI conjI)
          fix a
          assume a: "initial a"
          show "ide a"
            using a initial_def by blast
          show "Set a = {}"
          proof (cases "Set b = {}")
            case True
            show ?thesis
              using a b True by blast
            next
            case False
            have "Set a \<noteq> {} \<Longrightarrow> \<not> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>)"
            proof -
              assume 2: "Set a \<noteq> {}"
              obtain x y where 3: "x \<in> Set b \<and> y \<in> Set b \<and> x \<noteq> y"
                using b False terminal_char by auto
              show ?thesis
              proof -
                have "\<guillemotleft>mkarr a b (\<lambda>z. if z \<in> Set a then x else null) : a \<rightarrow> b\<guillemotright>"
                  using \<open>ide a\<close> b 3 by auto
                moreover have "\<guillemotleft>mkarr a b (\<lambda>z. if z \<in> Set a then y else null) : a \<rightarrow> b\<guillemotright>"
                  using \<open>ide a\<close> b 3 by auto
                moreover have "mkarr a b (\<lambda>z. if z \<in> Set a then x else null) \<noteq>
                               mkarr a b (\<lambda>z. if z \<in> Set a then y else null)"
                  by (metis (full_types, lifting) 2 3 Fun_mkarr arrI calculation(2) ex_in_conv)
                ultimately show ?thesis by auto
              qed
            qed
            thus ?thesis
              using a b initial_def by auto
          qed
          next
          fix a
          assume a: "ide a \<and> Set a = {}"
          show "initial a"
          proof -
            have "\<And>b. ide b \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
            proof -
              fix b
              assume b: "ide b"
              have "\<guillemotleft>mkarr a b (\<lambda>_. null) : a \<rightarrow> b\<guillemotright>"
                by (simp add: a b mkarr_in_hom)
              moreover have "\<And>f g. \<lbrakk>\<guillemotleft>f : a \<rightarrow> b\<guillemotright>; \<guillemotleft>g : a \<rightarrow> b\<guillemotright>\<rbrakk> \<Longrightarrow> f = g"
                using a arr_eqI' by fastforce
              ultimately show "\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>" by blast
            qed
            thus ?thesis
              using a initial_def by blast
          qed
        qed
      qed
      ultimately show ?thesis
        by (metis initial_def)
    qed

    text\<open>
      An arrow is a monomorphism if and only if the corresponding function is injective.
    \<close>

    lemma mono_char:
    shows "mono f \<longleftrightarrow> arr f \<and> inj_on (Fun f) (Set (dom f))"
    proof
      assume f: "mono f"
      have "arr f"
        using f mono_implies_arr by simp
      moreover have "inj_on (Fun f) (Set (dom f))"
        by (intro inj_onI)
           (metis Fun_def calculation f in_homE mem_Collect_eq mono_cancel seqI)
      ultimately show "arr f \<and> inj_on (Fun f) (Set (dom f))" by blast
      next
      assume f: "arr f \<and> inj_on (Fun f) (Set (dom f))"
      show "mono f"
      proof
        show "arr f"
          using f by blast
        fix g h
        assume seq: "seq f g" and eq: "f \<cdot> g = f \<cdot> h"
        show "g = h"
        proof (intro arr_eqI)
          show par: "par g h"
            by (metis dom_comp eq seq seqE)
          show "Fun g = Fun h"
          proof -
            have "\<And>x. x \<in> Set (dom g) \<Longrightarrow> Fun g x = Fun h x"
            proof -
              fix x
              assume x: "x \<in> Set (dom g)"
              have "f \<cdot> (g \<cdot> x) = f \<cdot> (h \<cdot> x)"
                using eq by (metis comp_assoc)
              moreover have "g \<cdot> x \<in> Set (dom f) \<and> h \<cdot> x \<in> Set (dom f)"
                by (metis seq par comp_in_homI in_homI mem_Collect_eq seq seqE x)
              ultimately have "g \<cdot> x = h \<cdot> x"
                using f inj_on_def [of "Fun f" "Set (dom f)"] Fun_def by auto
              thus "Fun g x = Fun h x"
                using par Fun_def by presburger
            qed
            thus ?thesis
              using par Fun_def by force
          qed
        qed
      qed
    qed

    text\<open>
      An arrow is a retraction if and only if the corresponding function is surjective.
    \<close>

    lemma retraction_char:
    shows "retraction f \<longleftrightarrow> arr f \<and> Fun f ` Set (dom f) = Set (cod f)"
    proof (intro iffI conjI)
      assume f: "retraction f"
      show 1: "arr f"
        using f by blast
      obtain g where g: "f \<cdot> g = cod f"
        using f by blast
      show "Fun f ` Set (dom f) = Set (cod f)"
      proof
        show "Fun f ` Set (dom f) \<subseteq> Set (cod f)"
          using \<open>arr f\<close> Fun_def by auto
        show "Set (cod f) \<subseteq> Fun f ` Set (dom f)"
        proof -
          have "Set (cod f) \<subseteq> Fun f ` Fun g ` Set (cod f)"
          proof -
            have "Set (cod f) \<subseteq> Fun (cod f) ` Set (cod f)"
              using 1 Fun_ide by auto
            also have "... = (Fun f \<circ> Fun g) ` Set (cod f)"
              using 1 g Fun_comp
              by (metis (no_types, lifting) arr_cod)
            also have "... = Fun f ` Fun g ` Set (cod f)"
              by (metis image_comp)
            finally show ?thesis by blast
          qed
          also have "... \<subseteq> Fun f ` Set (dom f)"
          proof -
            have "\<guillemotleft>g : cod f \<rightarrow> dom f\<guillemotright>"
              using g
              by (metis 1 arr_iff_in_hom ide_cod ide_compE seqE)
            thus ?thesis
              using Fun_def by auto
          qed
          finally show ?thesis by blast
        qed
      qed
      next
      assume f: "arr f \<and> Fun f ` Set (dom f) = Set (cod f)"
      let ?G = "\<lambda>y. if y \<in> Set (cod f) then inv_into (Set (dom f)) (Fun f) y else null"
      let ?g = "mkarr (cod f) (dom f) ?G"
      have "f \<cdot> ?g = cod f"
      proof (intro arr_eqI)
        have seq: "seq f ?g"
        proof
          show "\<guillemotleft>f : dom f \<rightarrow> cod f\<guillemotright>"
            using f by blast
          show "\<guillemotleft>?g : cod f \<rightarrow> dom f\<guillemotright>"
          proof (intro mkarr_in_hom)
            show "ide (cod f)" and "ide (dom f)"
              using f by auto
            show "?G \<in> (Set (cod f) \<rightarrow> Set (dom f)) \<inter> {F. \<forall>x. x \<notin> Set (cod f) \<longrightarrow> F x = null}"
            proof
              show "?G \<in> Set (cod f) \<rightarrow> Set (dom f)"
              proof
                fix x
                assume x: "x \<in> Set (cod f)"
                show "?G x \<in> Set (dom f)"
                  by (metis f inv_into_into x)
              qed
              show "?G \<in> {F. \<forall>x. x \<notin> Set (cod f) \<longrightarrow> F x = null}"
                using f by auto
            qed
          qed
        qed
        thus par: "par (f \<cdot> ?g) (cod f)" by auto
        show "Fun (f \<cdot> ?g) = Fun (cod f)"
        proof -
          have "Fun (f \<cdot> ?g) = Fun f \<circ> ?G"
            using par Fun_comp Fun_mkarr by fastforce
          also have "... = Fun (cod f)"
          proof
            fix y
            show "(Fun f \<circ> ?G) y = Fun (cod f) y"
            proof (cases "y \<in> Set (cod f)")
              case False
              show ?thesis
                using False Fun_def dom_cod by auto
              next
              case True
              show ?thesis
              proof -
                have "Fun f (inv_into (Set (dom f)) (Fun f) y) = y"
                  by (metis (no_types) True f f_inv_into_f)
                thus ?thesis
                  using Fun_ide True f by force
              qed
            qed
          qed
          finally show ?thesis by blast
        qed
      qed
      thus "retraction f"
        by (metis (lifting) f ide_cod retraction_def)
    qed

    text\<open>
      An arrow is a isomorphism if and only if the corresponding function is a bijection.
    \<close>

    lemma iso_char:
    shows "iso f \<longleftrightarrow> arr f \<and> bij_betw (Fun f) (Set (dom f)) (Set (cod f))"
      using retraction_char mono_char bij_betw_def
      by (metis (no_types, lifting) iso_iff_mono_and_retraction)

    lemma isomorphic_char:
    shows "isomorphic a b \<longleftrightarrow> ide a \<and> ide b \<and> Set a \<approx> Set b"
    proof
      assume 1: "isomorphic a b"
      show "ide a \<and> ide b \<and> Set a \<approx> Set b"
        using 1 isomorphic_def iso_char eqpoll_def [of "Set a" "Set b"] by auto
      next
      assume 1: "ide a \<and> ide b \<and> Set a \<approx> Set b"
      obtain F where F: "bij_betw F (Set a) (Set b)"
        using 1 eqpoll_def by blast
      let ?F' = "\<lambda>x. if x \<in> Set a then F x else null"
      let ?f = "mkarr a b (\<lambda>x. if x \<in> Set a then F x else null)"
      have f: "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright>"
      proof
        show "ide a" and "ide b"
          using 1 by auto
        show "(\<lambda>x. if x \<in> Set a then F x else null) \<in> Hom a b"
          using F Pi_mem bij_betw_imp_funcset by fastforce
      qed
      moreover have "bij_betw (Fun ?f) (Set a) (Set b)"
        using F Fun_mkarr arrI bij_betw_cong f
        apply (unfold bij_betw_def)
        by (auto simp add: inj_on_def)
      ultimately have "iso ?f \<and> dom ?f = a \<and> cod ?f = b"
        using iso_char Fun_mkarr by auto
      thus "isomorphic a b"
        using isomorphicI by force
    qed

  end

  section "Categoricity"

  text\<open>
    The following is a kind of ``categoricity in power'' result which states that,
    for a fixed notion of smallness, if \<open>C\<close> and \<open>D\<close> are ``sets categories'' whose collections
    of arrows are equipollent, then in fact \<open>C\<close> and \<open>D\<close> are equivalent categories.
  \<close>

  lemma categoricity:
  assumes "sets_cat sml C" and "sets_cat sml D"
  and "Collect (partial_composition.arr C) \<approx> Collect (partial_composition.arr D)"
  shows "equivalent_categories C D"
  proof
    interpret smallness sml
      using assms(1) sets_cat_def sets_cat_base_def by blast
    interpret C: sets_cat sml C
      using assms(1) by blast
    interpret D: sets_cat sml D
      using assms(2) by blast
    have D_embeds_C_Set: "\<And>a. C.ide a \<Longrightarrow> D.embeds (C.Set a)"
      using assms(3) D.embeds_subset [of "Collect C.arr"]
      by (metis (no_types, lifting) Collect_mono bij_betw_def C.in_homE eqpoll_def)
    let ?F\<^sub>o = "\<lambda>a. D.mkide (C.Set a)"
    have F\<^sub>o: "\<And>a. C.ide a \<Longrightarrow> D.ide (?F\<^sub>o a)"
      by (simp add: C.small_Set D.ide_mkide(1) D_embeds_C_Set)
    have bij_OUT: "\<And>a. C.ide a \<Longrightarrow> bij_betw (D.OUT (C.Set a)) (D.Set (?F\<^sub>o a)) (C.Set a)"
      by (simp add: C.small_Set D.bij_OUT(1) D_embeds_C_Set)
    let ?F\<^sub>F\<^sub>u\<^sub>n = "\<lambda>f. \<lambda>x. if x \<in> D.Set (?F\<^sub>o (C.dom f))
                          then (D.IN (C.Set (C.cod f)) \<circ> C.Fun f \<circ> D.OUT (C.Set (C.dom f))) x
                          else D.null"
    have F\<^sub>F\<^sub>u\<^sub>n: "\<And>f. C.arr f \<Longrightarrow> ?F\<^sub>F\<^sub>u\<^sub>n f \<in> D.Hom (?F\<^sub>o (C.dom f)) (?F\<^sub>o (C.cod f))"
    proof
      fix f
      assume f: "C.arr f"
      show "?F\<^sub>F\<^sub>u\<^sub>n f \<in> {F. \<forall>x. x \<notin> D.Set (?F\<^sub>o (C.dom f)) \<longrightarrow> F x = D.null}"
        by simp
      show "?F\<^sub>F\<^sub>u\<^sub>n f \<in> D.Set (?F\<^sub>o (C.dom f)) \<rightarrow> D.Set (?F\<^sub>o (C.cod f))"
      proof
        fix x
        assume x: "x \<in> D.Set (?F\<^sub>o (C.dom f))"
        show "?F\<^sub>F\<^sub>u\<^sub>n f x \<in> D.Set (D.mkide (C.Set (C.cod f)))"
        proof -
          have "D.in_hom (D.IN (C.Set (C.cod f)) (C f (D.OUT (C.Set (C.dom f)) x)))
                  D.some_terminal (D.mkide (C.Set (C.cod f)))"
          proof -
            have "\<guillemotleft>C f (D.OUT (C.Set (C.dom f)) x) : \<one>\<^sup>? \<rightarrow> C.cod f\<guillemotright>"
              using x f C.ide_dom bij_betwE bij_OUT by blast
            moreover have "small (C.Set (C.cod f))"
              using C.small_Set f by force
            moreover have "D.embeds (C.Set (C.cod f))"
              by (simp add: D_embeds_C_Set f)
            ultimately show ?thesis
              using x f D.bij_IN [of "C.Set (C.cod f)"] bij_betwE by auto
          qed
          moreover have "\<guillemotleft>D.OUT (C.Set (C.dom f)) x : \<one>\<^sup>? \<rightarrow> C.dom f\<guillemotright>"
            using x f C.ide_dom bij_betwE bij_OUT by blast
          ultimately show ?thesis
            using x f C.Fun_def by force
        qed
      qed
    qed
    let ?F = "\<lambda>f. if C.arr f then D.mkarr (?F\<^sub>o (C.dom f)) (?F\<^sub>o (C.cod f)) (?F\<^sub>F\<^sub>u\<^sub>n f) else D.null"
    interpret "functor" C D ?F
    proof
      show "\<And>f. \<not> C.arr f \<Longrightarrow> ?F f = D.null"
        by simp
      show arrF: "\<And>f. C.arr f \<Longrightarrow> D.arr (?F f)"
        using F\<^sub>o F\<^sub>F\<^sub>u\<^sub>n by auto
      show domF: "\<And>f. C.arr f \<Longrightarrow> D.dom (?F f) = ?F (C.dom f)"
      proof -
        fix f
        assume f: "C.arr f"
        have "D.dom (?F f) = D.mkide (C.Set (C.dom f))"
          using f arrF by auto
        also have "... = ?F (C.dom f)"
        proof -
          have "?F\<^sub>F\<^sub>u\<^sub>n (C.dom f) =
                (\<lambda>x. if x \<in> D.Set (D.mkide (C.Set (C.dom f))) then x else D.null)"
          proof
            fix x
            have "x \<in> D.Set (D.mkide (C.Set (C.dom f))) \<Longrightarrow>
                    \<guillemotleft>D.OUT (C.Set (C.dom f)) x : \<one>\<^sup>? \<rightarrow> C.dom f\<guillemotright>"
              using f C.ide_dom bij_betwE bij_OUT by blast
            thus "?F\<^sub>F\<^sub>u\<^sub>n (C.dom f) x =
                  (if x \<in> D.Set (D.mkide (C.Set (C.dom f))) then x else D.null)"
              using f C.ide_dom bij_betwE bij_OUT arrF F\<^sub>o C.Fun_ide
                    D.IN_OUT [of "C.Set (C.dom f)" x]
              by (auto simp add: C.small_Set D_embeds_C_Set)
          qed
          moreover have "D.mkide (C.Set (C.dom f)) =
                         D.mkarr (D.mkide (C.Set (C.dom f))) (D.mkide (C.Set (C.dom f)))
                             (\<lambda>x. if D.in_hom x D.some_terminal (D.mkide (C.Set (C.dom f)))
                                  then x else D.null)"
            using f arrF F\<^sub>o D.ide_as_mkarr by auto
          ultimately show ?thesis
            using f by auto
        qed
        finally show "D.dom (?F f) = ?F (C.dom f)" by blast
      qed
      show codF: "\<And>f. C.arr f \<Longrightarrow> D.cod (?F f) = ?F (C.cod f)"
      proof -
        fix f
        assume f: "C.arr f"
        have "D.cod (?F f) = D.mkide (C.Set (C.cod f))"
          using f arrF by auto
        also have "... = ?F (C.cod f)"
        proof -
          have "?F\<^sub>F\<^sub>u\<^sub>n (C.cod f) =
                (\<lambda>x. if x \<in> D.Set (D.mkide (C.Set (C.cod f))) then x else D.null)"
          proof
            fix x
            have "x \<in> D.Set (D.mkide (C.Set (C.cod f))) \<Longrightarrow>
                    \<guillemotleft>D.OUT (C.Set (C.cod f)) x : \<one>\<^sup>? \<rightarrow> C.cod f\<guillemotright>"
              using f C.ide_cod bij_betwE bij_OUT by blast
            thus "?F\<^sub>F\<^sub>u\<^sub>n (C.cod f) x =
                  (if x \<in> D.Set (D.mkide (C.Set (C.cod f))) then x else D.null)"
              using f C.ide_cod bij_betwE bij_OUT arrF F\<^sub>o C.Fun_ide
                    D.IN_OUT [of "C.Set (C.cod f)" x]
              by (auto simp add: C.small_Set D_embeds_C_Set)
          qed
          moreover have "D.mkide (C.Set (C.cod f)) =
                         D.mkarr (D.mkide (C.Set (C.cod f))) (D.mkide (C.Set (C.cod f)))
                             (\<lambda>x. if D.in_hom x D.some_terminal (D.mkide (C.Set (C.cod f)))
                                  then x else D.null)"
            using f arrF F\<^sub>o D.ide_as_mkarr [of "D.mkide (C.Set (C.cod f))"] by auto
          ultimately show ?thesis
            using f by auto
        qed
        finally show "D.cod (?F f) = ?F (C.cod f)" by blast
      qed
      fix f g
      assume seq: "C.seq g f"
      have f: "C.arr f" and g: "C.arr g"
        using seq by auto
      show "?F (C g f) = D (?F g) (?F f)"
      proof (intro D.arr_eqI [of "?F (C g f)"])
        show par: "D.par (?F (C g f)) (D (?F g) (?F f))"
        proof (intro conjI)
          show 1: "D.arr (?F (C g f))"
            using seq arrF [of "C g f"] by fastforce
          show 2: "D.arr (D (?F g) (?F f))"
            using seq arrF domF codF by (intro D.seqI) auto
          show "D.dom (?F (C g f)) = D.dom (D (?F g) (?F f))"
            using 1 2 by fastforce
          show "D.cod (?F (C g f)) = D.cod (D (?F g) (?F f))"
            using 1 2 by fastforce
        qed
        show "D.Fun (?F (C g f)) = D.Fun (D (?F g) (?F f))"
        proof -
          have "D.Fun (D (?F g) (?F f)) = D.Fun (?F g) \<circ> D.Fun (?F f)"
            using seq par D.Fun_comp [of "?F g" "?F f"] by fastforce
          also have "... = ?F\<^sub>F\<^sub>u\<^sub>n g \<circ> ?F\<^sub>F\<^sub>u\<^sub>n f"
            using f g arrF D.Fun_mkarr by auto
          also have "... = D.Fun (?F (C g f))"
          proof
            fix x
            show "(?F\<^sub>F\<^sub>u\<^sub>n g \<circ> ?F\<^sub>F\<^sub>u\<^sub>n f) x = D.Fun (?F (C g f)) x"
            proof (cases "x \<in> D.Set (D.mkide (C.Set (C.dom f)))")
              case False
              show ?thesis
                using False f par by auto
              next
              case True
              have 1: "\<guillemotleft>D.OUT (C.Set (C.dom f)) x : \<one>\<^sup>? \<rightarrow> C.dom f\<guillemotright>"
                using True D.OUT_elem_of [of "C.Set (C.dom f)" x]
                      C.ide_dom C.small_Set D_embeds_C_Set f
                by blast
              have "(?F\<^sub>F\<^sub>u\<^sub>n g \<circ> ?F\<^sub>F\<^sub>u\<^sub>n f) x =
                    D.IN (C.Set (C.cod g))
                      (C.Fun g
                         (D.OUT (C.Set (C.dom g))
                            (D.IN (C.Set (C.cod f))
                               (C.Fun f
                                  (D.OUT (C.Set (C.dom f)) x)))))"
              proof -
                have "D.in_hom (D.IN (C.Set (C.cod f)) (C f (D.OUT (C.Set (C.dom f)) x)))
                                 D.some_terminal (D.mkide (C.Set (C.dom g)))"
                  using True f seq 1 C.ide_cod C.small_Set D_embeds_C_Set
                  by (intro D.IN_in_hom) auto
                thus ?thesis
                  using True 1 C.Fun_def by auto
              qed
              also have "... =
                    D.IN (C.Set (C.cod g))
                      (C.Fun g
                         (C.Fun f
                            (D.OUT (C.Set (C.dom f)) x)))"
                using True 1 seq f g C.small_Set D_embeds_C_Set C.Fun_def D.Fun_def
                      D.OUT_IN [of "C.Set (C.dom g)" "C f (D.OUT (C.Set (C.dom f)) x)"]
                by auto[1] (metis C.comp_in_homI' C.in_homE C.seqE)
              also have "... = ?F\<^sub>F\<^sub>u\<^sub>n (C g f) x"
                using True seq 1 C.comp_assoc C.Fun_def D.Fun_def
                by auto[1] fastforce
              also have "... = D.Fun (?F (C g f)) x"
                using True par seq D.Fun_mkarr D.app_mkarr D.in_homI by force
              finally show ?thesis by blast
            qed
          qed
          finally show ?thesis by simp
        qed
      qed
    qed
    interpret F: fully_faithful_and_essentially_surjective_functor C D ?F
    proof
      show "\<And>f f'. \<lbrakk>C.par f f'; ?F f = ?F f'\<rbrakk> \<Longrightarrow> f = f'"
      proof -
        fix f f'
        assume par: "C.par f f'"
        assume eq: "?F f = ?F f'"
        show "f = f'"
        proof (intro C.arr_eqI' [of f])
          show f: "\<guillemotleft>f : C.dom f \<rightarrow> C.cod f\<guillemotright>"
            using par by blast
          show f': "\<guillemotleft>f' : C.dom f \<rightarrow> C.cod f\<guillemotright>"
            using par by auto
          show "\<And>x. \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> C.dom f\<guillemotright> \<Longrightarrow> C f x = C f' x"
          proof -
            fix x
            assume x: "\<guillemotleft>x : \<one>\<^sup>? \<rightarrow> C.dom f\<guillemotright>"
            have fx: "\<guillemotleft>C f x : \<one>\<^sup>? \<rightarrow> C.cod f\<guillemotright> \<and> C.ide (C.dom f) \<and> C.ide (C.cod f)"
              by (metis (no_types) C.arrI C.comp_in_homI C.ide_cod C.seqE f x)
            have f'x: "\<guillemotleft>C f' x : \<one>\<^sup>? \<rightarrow> C.cod f'\<guillemotright> \<and> C.ide (C.dom f') \<and> C.ide (C.cod f')"
                by (metis (no_types) C.arrI C.comp_in_homI C.ide_cod C.seqE f' x par)
            have 1: "D.in_hom (D.IN (C.Set (C.dom f)) x)
                       D.some_terminal (D.mkide (C.Set (C.dom f)))"
              by (metis C.ide_dom C.small_Set D.IN_in_hom D_embeds_C_Set mem_Collect_eq
                  par x)
            have "C f x = C.Fun f x"
              using C.Fun_def x by auto
            also have "... = D.OUT (C.Set (C.cod f))
                               (D.IN (C.Set (C.cod f))
                                  (C.Fun f
                                     (D.OUT (C.Set (C.dom f))
                                        (D.IN (C.Set (C.dom f)) x))))"
              by (simp add: fx C.small_Set D.OUT_IN D_embeds_C_Set x C.Fun_def)
            also have "... = D.OUT (C.Set (C.cod f)) (?F\<^sub>F\<^sub>u\<^sub>n f (D.IN (C.Set (C.dom f)) x))"
              using par 1 by auto
            also have "... =
                       D.OUT (C.Set (C.cod f)) (D.Fun (?F f) (D.IN (C.Set (C.dom f)) x))"
            proof -
              have "D.arr (?F f)"
                using f by blast
              thus ?thesis
                using x f par by auto
            qed
            also have "... =
                       D.OUT (C.Set (C.cod f)) (D.Fun (?F f') (D.IN (C.Set (C.dom f)) x))"
              using eq by simp
            also have "... = D.OUT (C.Set (C.cod f)) (?F\<^sub>F\<^sub>u\<^sub>n f' (D.IN (C.Set (C.dom f)) x))"
            proof -
              have "D.arr (?F f')"
                using f' by blast
              thus ?thesis
                using x f par by auto
            qed
            also have "... = D.OUT (C.Set (C.cod f'))
                               (D.IN (C.Set (C.cod f'))
                                  (C.Fun f'
                                     (D.OUT (C.Set (C.dom f'))
                                        (D.IN (C.Set (C.dom f')) x))))"
              using par 1 by auto
            also have "... = C.Fun f' x"
              by (metis f'x C.small_Set D.OUT_IN D_embeds_C_Set mem_Collect_eq par x C.Fun_def)
            also have "... = C f' x"
              using C.Fun_def x par by auto
            finally show "C f x = C f' x" by blast
          qed
        qed
      qed
      have *: "\<And>a. C.ide a \<Longrightarrow> ?F a = ?F\<^sub>o a"
      proof - 
        fix a
        assume a: "C.ide a"
        show "?F a = ?F\<^sub>o a"
        proof -
          have "(\<lambda>x. if D.in_hom x D.some_terminal (D.mkide (C.Set a))
                     then (D.IN (C.Set (C.cod a)) \<circ> C.Fun a \<circ> D.OUT (C.Set (C.dom a))) x
                     else D.null) =
                (\<lambda>x. if D.in_hom x D.some_terminal (D.mkide (C.Set a)) then x else D.null)"
          proof
            fix x
            show "(if D.in_hom x D.some_terminal (D.mkide (C.Set a))
                   then (D.IN (C.Set (C.cod a)) \<circ> C.Fun a \<circ> D.OUT (C.Set (C.dom a))) x
                   else D.null) =
                  (if D.in_hom x D.some_terminal (D.mkide (C.Set a)) then x else D.null)"
            using a C.Fun_ide D.IN_OUT [of "C.Set a"] C.small_Set D_embeds_C_Set
            apply auto[1]
            by (metis (lifting) D.OUT_elem_of mem_Collect_eq)
          qed
          thus ?thesis
            using a D.ide_as_mkarr F\<^sub>o by auto
        qed
      qed
      show "\<And>a b g. \<lbrakk>C.ide a; C.ide b; D.in_hom g (?F a) (?F b)\<rbrakk>
                       \<Longrightarrow> \<exists>h. \<guillemotleft>h : a \<rightarrow> b\<guillemotright> \<and> ?F h = g"
      proof -
        fix a b g
        assume a: "C.ide a" and b: "C.ide b" and g: "D.in_hom g (?F a) (?F b)"
        have "?F a = ?F\<^sub>o a"
          using a * by blast
        have dom_g: "D.dom g = ?F\<^sub>o a"
          using a g * by auto
        have cod_g: "D.cod g = ?F\<^sub>o b"
          using b g * by auto
        have Fun_g: "D.Fun g \<in> D.Hom (?F\<^sub>o a) (?F\<^sub>o b)"
          using g D.Fun_in_Hom dom_g cod_g by blast
        let ?H = "\<lambda>x. if x \<in> C.Set a
                      then (D.OUT (C.Set b) \<circ> D.Fun g \<circ> D.IN (C.Set a)) x
                      else C.null"
        have H: "?H \<in> C.Hom a b"
        proof
          show "?H \<in> C.Set a \<rightarrow> C.Set b"
          proof
            fix x
            assume x: "x \<in> C.Set a"
            show "?H x \<in> C.Set b"
            proof -
              have "?H x = D.OUT (C.Set b) (D.Fun g (D.IN (C.Set a) x))"
                using x by simp
              moreover have "... \<in> C.Set b"
              proof -
                have "D.IN (C.Set a) x \<in> D.Set (?F\<^sub>o a)"
                  by (metis (lifting) a bij_betw_iff_bijections bij_betw_inv_into bij_OUT x)
                hence "D.Fun g (D.IN (C.Set a) x) \<in> D.Set (?F\<^sub>o b)"
                  using Fun_g by blast
                thus ?thesis
                  using b C.small_Set D_embeds_C_Set bij_OUT bij_betw_apply D.Fun_def
                  by fastforce
              qed
              ultimately show ?thesis by auto
            qed
          qed
          show "?H \<in> {F. \<forall>x. x \<notin> C.Set a \<longrightarrow> F x = C.null}" by simp
        qed
        let ?h = "C.mkarr a b ?H"
        have h: "\<guillemotleft>?h : a \<rightarrow> b\<guillemotright>"
          using a b H by blast
        moreover have "?F ?h = g"
        proof (intro D.arr_eqI)
          have Fh: "D.in_hom (?F ?h) (?F\<^sub>o a) (?F\<^sub>o b)"
          proof -
            have "D.in_hom (?F ?h) (?F a) (?F b)"
              using h preserves_hom by blast
            moreover have "?F a = ?F\<^sub>o a \<and> ?F b = ?F\<^sub>o b"
              using a b * by auto
            ultimately show ?thesis by simp
          qed
          show par: "D.par (?F ?h) g"
            using Fh h g cod_g dom_g D.in_homE by auto
          show "D.Fun (?F ?h) = D.Fun g"
          proof
            fix x
            show "D.Fun (?F ?h) x = D.Fun g x"
            proof (cases "x \<in> D.Set (?F\<^sub>o a)")
              case False
              show ?thesis
                using False par D.Fun_def by auto
              next
              case True
              have "D.Fun (?F ?h) x = ?F\<^sub>F\<^sub>u\<^sub>n ?h x"
                using True h Fh D.Fun_def D.app_mkarr by auto
              also have "... = (if x \<in> D.Set (?F\<^sub>o a)
                                then (D.IN (C.Set b) \<circ> C.Fun ?h \<circ> D.OUT (C.Set a)) x
                                else D.null)"
                using h by auto
              also have "... = D.IN (C.Set b) (?H (D.OUT (C.Set a) x))"
                using True h C.app_mkarr by auto
              also have "... = D.IN (C.Set b)
                                 (D.OUT (C.Set b)
                                    (D.Fun g
                                       (D.IN (C.Set a)
                                          (D.OUT (C.Set a) x))))"
              proof -
                have "D.OUT (C.Set a) x \<in> C.Set a"
                  using True a bij_betw_apply bij_OUT by force
                thus ?thesis by simp
              qed
              also have "... = D.Fun g x"
                using True a b g D.IN_OUT [of "C.Set a" x] D.IN_OUT [of "C.Set b" "D.Fun g x"]
                      C.small_Set D_embeds_C_Set dom_g cod_g D.Fun_def
                by auto
              finally show ?thesis by blast
            qed
          qed
        qed
        ultimately show "\<exists>h. \<guillemotleft>h : a \<rightarrow> b\<guillemotright> \<and> ?F h = g" by blast
      qed
      show "\<And>b. D.ide b \<Longrightarrow> \<exists>a. C.ide a \<and> D.isomorphic (?F a) b"
      proof -
        fix b
        assume b: "D.ide b"
        let ?a = "C.mkide (D.Set b)"
        have 1: "C.ide ?a \<and> C.Set ?a \<approx> D.Set b"
        proof -
          have "\<exists>\<iota>. C.is_embedding_of \<iota> (D.Set b)"
            by (metis (no_types, lifting) D.in_homE Set.basic_monos(6) assms(3)
                bij_betw_def bij_betw_inv_into eqpoll_def image_mono inj_on_subset)
          thus ?thesis
            using b C.ide_mkide [of "D.Set b"] D.small_Set by force
        qed
        have "D.Set (?F ?a) \<approx> D.Set b"
        proof -
          have "\<And>a. C.ide a \<Longrightarrow> D.Set (?F a) \<approx> C.Set a"
            using * C.small_Set D_embeds_C_Set D.ide_mkide(2) by fastforce
          thus ?thesis
            using 1 eqpoll_trans by blast
        qed
        moreover have "\<And>a. C.ide a \<Longrightarrow> D.isomorphic (?F a) b \<longleftrightarrow> D.Set (?F a) \<approx> D.Set b"
          using D.isomorphic_char b preserves_ide by force
        ultimately show "\<exists>a. C.ide a \<and> D.isomorphic (?F a) b"
          using 1 by blast
      qed
    qed
    show "equivalence_functor C D ?F"
      using F.is_equivalence_functor by blast
  qed

  section "Well-Pointedness"

  context sets_cat
  begin

    lemma is_well_pointed:
    assumes "par f g" and "\<And>x. x \<in> Set (dom f) \<Longrightarrow> f \<cdot> x = g \<cdot> x"
    shows "f = g"
      by (metis CollectI arr_eqI' assms(1,2) in_homI)

  end

  section "Epis Split"

  text\<open>
    In this section we assume that smallness encompasses sets of arbitrary finite cardinality,
    and that the category has at least two arrows, so that we can show the existence of an
    object with two global elements.
    If this fails to be the case, then the situation is somewhat pathological and not very
    interesting.
  \<close>

  locale sets_cat_with_bool =
    sets_cat sml C +
    small_finite sml
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55) +
  assumes embeds_bool_ax: "embeds (UNIV :: bool set)"
  begin

    definition two  ("\<^bold>\<two>")
    where "two \<equiv> mkide {True, False}"

    lemma ide_two [intro, simp]:
    shows "ide two"
    and "bij_betw (IN {True, False}) UNIV (Set two)"
    and "bij_betw (OUT {True, False}) (Set two) UNIV"
      using two_def ide_mkide embeds_bool_ax small_finite UNIV_bool
            finite.simps insert_commute infinite_imp_nonempty finite.emptyI
            bij_IN [of "{True, False}"] bij_OUT [of "{True, False}"]
      by metis+

    definition tt
    where "tt \<equiv> IN {True, False} True"

    definition ff
    where "ff \<equiv> IN {True, False} False"

    lemma tt_in_hom [intro]:
    shows "\<guillemotleft>tt : \<one>\<^sup>? \<rightarrow> \<^bold>\<two>\<guillemotright>"
      using bij_betwE tt_def by force

    lemma ff_in_hom [intro]:
    shows "\<guillemotleft>ff : \<one>\<^sup>? \<rightarrow> \<^bold>\<two>\<guillemotright>"
      using bij_betwE ff_def by force

    lemma tt_simps [simp]:
    shows "arr tt" and "dom tt = \<one>\<^sup>?" and "cod tt = \<^bold>\<two>"
      using tt_in_hom by blast+

    lemma ff_simps [simp]:
    shows "arr ff" and "dom ff = \<one>\<^sup>?" and "cod ff = \<^bold>\<two>"
      using ff_in_hom by blast+

    lemma Fun_tt:
    shows "Fun tt = (\<lambda>x. if x \<in> Set \<one>\<^sup>? then tt else null)"
      unfolding Fun_def
      using tt_def
      by (metis Set_some_terminal comp_arr_dom emptyE insertE tt_simps(1,2))

    lemma Fun_ff:
    shows "Fun ff = (\<lambda>x. if x \<in> Set \<one>\<^sup>? then ff else null)"
      unfolding Fun_def
      using ff_def
      by (metis Set_some_terminal comp_arr_dom emptyE insertE ff_simps(1,2))

    lemma mono_tt:
    shows "mono tt"
      using Fun_tt mono_char
      by (metis point_is_mono terminal_some_terminal tt_simps(1,2))

    lemma mono_ff:
    shows "mono ff"
      using Fun_ff mono_char
      by (metis point_is_mono terminal_some_terminal ff_simps(1,2))

    lemma tt_ne_ff:
    shows "tt \<noteq> ff"
      using tt_def ff_def two_def
      by (metis bij_betw_inv_into_right ide_two(3) iso_tuple_UNIV_I)

    lemma Set_two:
    shows "Set \<^bold>\<two> = {tt, ff}"
    proof -
      have "Set \<^bold>\<two> = IN {True, False} ` UNIV"
        using bij_betw_imp_surj_on by blast
      thus ?thesis
        using tt_def ff_def
        by (simp add: UNIV_bool insert_commute)
    qed

    text\<open>
      In the present context, an arrow is epi if and only if the corresponding function
      is surjective.  It follows that every epimorphism splits.
    \<close>

    lemma epi_char\<^sub>S\<^sub>C\<^sub>B:
    shows "epi f \<longleftrightarrow> arr f \<and> Fun f ` Set (dom f) = Set (cod f)"
    proof
      show "arr f \<and> Fun f ` Set (dom f) = Set (cod f) \<Longrightarrow> epi f"
        using retraction_char retraction_is_epi by presburger
      assume f: "epi f"
      show "arr f \<and> Fun f ` Set (dom f) = Set (cod f)"
      proof (intro conjI)
        show "arr f"
          using epi_implies_arr f by blast
        show "Fun f ` Set (dom f) = Set (cod f)"
        proof
          show "Fun f ` Set (dom f) \<subseteq> Set (cod f)"
            using \<open>arr f\<close> Fun_def by auto
          show "Set (cod f) \<subseteq> Fun f ` Set (dom f)"
          proof
            fix y
            assume y: "y \<in> Set (cod f)"
            have "y \<notin> Fun f ` Set (dom f) \<Longrightarrow> False"
            proof -
              assume 1: "y \<notin> Fun f ` Set (dom f)"
              let ?G = "\<lambda>z. if z \<in> Set (cod f) then if z = y then tt else ff else null"
              let ?G' = "\<lambda>z. if z \<in> Set (cod f) then ff else null"
              let ?g = "mkarr (cod f) \<^bold>\<two> ?G"
              let ?g' = "mkarr (cod f) \<^bold>\<two> ?G'"
              have g: "\<guillemotleft>?g : cod f \<rightarrow> \<^bold>\<two>\<guillemotright>"
                using f epi_implies_arr ide_two
                by (intro mkarr_in_hom) auto
              have g': "\<guillemotleft>?g' : cod f \<rightarrow> \<^bold>\<two>\<guillemotright>"
                using f epi_implies_arr ide_two
                by (intro mkarr_in_hom) auto
              have "?g \<noteq> ?g'"
              proof -
                have "?g \<cdot> y \<noteq> ?g' \<cdot> y"
                  using app_mkarr g g' tt_ne_ff y by auto
                thus ?thesis by auto
              qed
              moreover have "?g \<cdot> f = ?g' \<cdot> f"
              proof -
                have "?G \<circ> Fun f = ?G' \<circ> Fun f"
                proof
                  fix x
                  show "(?G \<circ> Fun f) x = (?G' \<circ> Fun f) x"
                    using 1 tt_ne_ff Fun_def by auto
                qed
                thus ?thesis
                  using f g g' Fun_mkarr \<open>arr f\<close> in_homI Fun_comp
                  by (intro arr_eqI) auto
              qed
              ultimately show False
                using f g g' \<open>arr f\<close> epi_cancel by blast
            qed
            thus "y \<in> Fun f ` Set (dom f)" by blast
          qed
        qed
      qed
    qed

    corollary epis_split:
    assumes "epi e"
    shows "\<exists>m. e \<cdot> m = cod e"
      using assms epi_char\<^sub>S\<^sub>C\<^sub>B retraction_char
      by (meson ide_compE retraction_def)

  end

  section "Equalizers"

  text\<open>
    In this section we show that the category of small sets and functions has equalizers
    of parallel pairs of arrows.  This is our first example of a general pattern that we
    will apply repeatedly in the sequel to other categorical constructions.
    Given a parallel pair \<open>f\<close>, \<open>g\<close> of arrows in a category of sets, we know that the
    global elements of the domain of the equalizer will be in bijection with the set \<open>E\<close>
    of global elements \<open>x\<close> of \<open>dom f\<close> such that \<open>f \<cdot> x = g \<cdot> x\<close>.  So, we obtain this set,
    which in this case happens already to be a small subset of the set of arrows of the
    category, and we obtain the corresponding object \<open>mkide E\<close>, which will be the domain
    of the equalizer.  This part of the proof uses the smallness of \<open>E\<close> and the fact that
    it embeds in (actually, is a subset of) the set of arrows of the category.
    Once we have shown the existence of the object \<open>mkide E\<close>, we can apply \<open>mkarr\<close> to the
    inclusion of \<open>Set (mkide e)\<close> in \<open>Set (dom f)\<close> to obtain the equalizing arrow itself.
    Showing that this arrow has the necessary universal property requires reasoning about
    the comparison maps between \<open>E\<close> and \<open>Set (mkide e)\<close>, but once that has been accomplished
    we are left simply with a universal property that does not mention these maps.

    The construction and proofs here are simpler than for the other constructions we will
    consider, because the set \<open>E\<close> to which we apply \<open>mkide\<close> is already a subset of the
    collection of arrows of the category -- in particular it is at the same type.
    This means that the smallness and embedding property required for the application
    of \<open>mkide\<close> holds automatically, without any further assumptions.
    In general, though, a set to which we wish to apply \<open>mkide\<close> will not be a subset of
    the set of arrows, nor will it even be at the same type, so it will be necessary
    to reason about an encoding that embeds the elements of this set into the set of
    arrows of the category.
  \<close>

  locale equalizers_in_sets_cat =
    sets_cat
  begin

    abbreviation Dom_equ
    where "Dom_equ f g \<equiv> {x. x \<in> Set (dom f) \<and> f \<cdot> x = g \<cdot> x}"

    definition dom_equ
    where "dom_equ f g \<equiv> mkide (Dom_equ f g)"

    abbreviation Equ
    where "Equ f g \<equiv> \<lambda>x. if x \<in> Set (dom_equ f g) then OUT (Dom_equ f g) x else null"

    definition equ
    where "equ f g \<equiv> mkarr (dom_equ f g) (dom f) (Equ f g)"

    text\<open>
      It is useful to include convenience facts about \<open>OUT\<close> and \<open>IN\<close> in the following,
      so that we can avoid having to deal with the smallness and embedding conditions
      elsewhere.
    \<close>

    lemma ide_dom_equ:
    assumes "par f g"
    shows "ide (dom_equ f g)"
    and "bij_betw (OUT (Dom_equ f g)) (Set (dom_equ f g)) (Dom_equ f g)"
    and "bij_betw (IN (Dom_equ f g)) (Dom_equ f g) (Set (dom_equ f g))"
    and "\<And>x. x \<in> Set (dom_equ f g) \<Longrightarrow> OUT (Dom_equ f g) x \<in> Set (dom f)"
    and "\<And>y. y \<in> Dom_equ f g \<Longrightarrow> IN (Dom_equ f g) y \<in> Set (dom_equ f g)"
    and "\<And>x. x \<in> Set (dom_equ f g) \<Longrightarrow> IN (Dom_equ f g) (OUT (Dom_equ f g) x) = x"
    and "\<And>y. y \<in> Dom_equ f g \<Longrightarrow> OUT (Dom_equ f g) (IN (Dom_equ f g) y) = y"
    proof -
      have 1: "small (Dom_equ f g)"
        by (metis (full_types) assms ide_dom small_Collect small_Set)
      have 2: "embeds (Dom_equ f g)"
        by (metis (no_types, lifting) Collect_mono arrI image_ident mem_Collect_eq
            subset_image_inj)
      show "ide (dom_equ f g)"
        by (unfold dom_equ_def, intro ide_mkide) fact+
      show 3: "bij_betw (OUT (Dom_equ f g)) (Set (dom_equ f g)) (Dom_equ f g)"
        unfolding dom_equ_def
        using assms ide_mkide bij_OUT 1 2 by auto
      show 4: "bij_betw (IN (Dom_equ f g)) (Dom_equ f g) (Set (dom_equ f g))"
        unfolding dom_equ_def
        using assms ide_mkide bij_OUT bij_IN 1 2 by fastforce
      show "\<And>x. x \<in> Set (dom_equ f g) \<Longrightarrow> OUT (Dom_equ f g) x \<in> Set (dom f)"
        by (metis (no_types, lifting) 3 CollectD bij_betw_apply)
      show "\<And>y. y \<in> Dom_equ f g \<Longrightarrow> IN (Dom_equ f g) y \<in> Set (dom_equ f g)"
        by (metis (no_types, lifting) 4 bij_betw_apply)
      show "\<And>x. x \<in> Set (dom_equ f g) \<Longrightarrow> IN (Dom_equ f g) (OUT (Dom_equ f g) x) = x"
        using 1 2 IN_OUT dom_equ_def by auto
      show "\<And>y. y \<in> Dom_equ f g \<Longrightarrow> OUT (Dom_equ f g) (IN (Dom_equ f g) y) = y"
        using 1 2 OUT_IN by force
    qed

    lemma Equ_in_Hom [intro]:
    assumes "par f g"
    shows "Equ f g \<in> Hom (dom_equ f g) (dom f)"
    proof
      show "Equ f g \<in> Set (dom_equ f g) \<rightarrow> Set (dom f)"
        using assms ide_dom_equ(4) by auto
      show "Equ f g \<in> {F. \<forall>x. x \<notin> Set (dom_equ f g) \<longrightarrow> F x = null}"
        by simp
    qed

    lemma equ_in_hom [intro, simp]:
    assumes "par f g"
    shows "\<guillemotleft>equ f g : dom_equ f g \<rightarrow> dom f\<guillemotright>"
      using assms ide_dom_equ Equ_in_Hom
      unfolding equ_def
      by (intro mkarr_in_hom) auto

    lemma equ_simps [simp]:
    assumes "par f g"
    shows "arr (equ f g)" and "dom (equ f g) = dom_equ f g" and "cod (equ f g) = dom f"
      using assms equ_in_hom by blast+

    lemma Fun_equ:
    assumes "par f g"
    shows "Fun (equ f g) = Equ f g"
    proof -
      have "arr (equ f g)"
        using assms by auto
      thus ?thesis
        unfolding equ_def
        using assms Fun_mkarr by auto
    qed

    lemma equ_equalizes:
    assumes "par f g"
    shows "f \<cdot> equ f g = g \<cdot> equ f g"
    proof (intro arr_eqI [of "f \<cdot> equ f g"])
      show par: "par (f \<cdot> equ f g) (g \<cdot> equ f g)"
        using assms by auto
      show "Fun (f \<cdot> equ f g) = Fun (g \<cdot> equ f g)"
      proof
        fix x
        show "Fun (f \<cdot> equ f g) x = Fun (g \<cdot> equ f g) x"
        proof (cases "x \<in> Set (dom_equ f g)")
          case False
          show ?thesis
            using assms False Fun_equ Fun_def by simp
          next
          case True 
          show ?thesis
          proof -
            have "Fun (f \<cdot> equ f g) x = Fun f (Fun (equ f g) x)"
              using assms Fun_comp comp_in_homI equ_in_hom comp_assoc by auto
            also have "... = Fun f (OUT (Dom_equ f g) x)"
              using assms True Fun_equ by simp
            also have "... = f \<cdot> (OUT (Dom_equ f g) x)"
              using Fun_def True assms ide_dom_equ(4) by simp
            also have "... = g \<cdot> (OUT (Dom_equ f g) x)"
              using assms True ide_dom_equ(2) [of f g] bij_betw_apply by force
            also have "... = Fun g (Fun (equ f g) x)"
              using assms True Fun_def Fun_equ ide_dom_equ by simp
            also have "... = Fun (g \<cdot> equ f g) x"
              using assms Fun_comp comp_in_homI equ_in_hom comp_assoc by auto
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    lemma equ_is_equalizer:
    assumes "par f g"
    shows "has_as_equalizer f g (equ f g)"
    proof
      show "par f g" by fact
      show 0: "seq f (equ f g)"
        using assms by auto
      show "f \<cdot> equ f g = g \<cdot> equ f g"
        using assms equ_equalizes by blast
      show "\<And>e'. \<lbrakk>seq f e'; f \<cdot> e' = g \<cdot> e'\<rbrakk> \<Longrightarrow> \<exists>!h. equ f g \<cdot> h = e'"
      proof -
        fix e'
        assume seq: "seq f e'" and eq: "f \<cdot> e' = g \<cdot> e'"
        let ?H = "\<lambda>x. if x \<in> Set (dom e') then IN (Dom_equ f g) (e' \<cdot> x) else null"
        have H: "?H \<in> Hom (dom e') (dom_equ f g)"
        proof
          show "?H \<in> {F. \<forall>x. x \<notin> Set (dom e') \<longrightarrow> F x = null}" by simp
          show "?H \<in> Set (dom e') \<rightarrow> Set (dom_equ f g)"
          proof
            fix x
            assume x: "x \<in> Set (dom e')"
            have "?H x = IN (Dom_equ f g) (e' \<cdot> x)"
              using x by simp
            moreover have "... \<in> Set (dom_equ f g)"
              using assms seq x ide_dom_equ(5)
              by (metis (mono_tags, lifting) CollectD CollectI arr_iff_in_hom
                  comp_in_homI eq local.comp_assoc seqE)
            ultimately show "?H x \<in> Set (dom_equ f g)" by auto
          qed
        qed
        let ?h = "mkarr (dom e') (dom_equ f g) ?H"
        have h: "\<guillemotleft>?h : dom e' \<rightarrow> dom_equ f g\<guillemotright>"
          using assms H seq ide_dom_equ
          by (intro mkarr_in_hom) auto
        have *: "equ f g \<cdot> ?h = e'"
        proof (intro arr_eqI' [of "equ f g \<cdot> ?h"])
          show 1: "\<guillemotleft>equ f g \<cdot> ?h : dom e' \<rightarrow> dom f\<guillemotright>"
            using assms h by blast
          show e': "\<guillemotleft>e' : dom e' \<rightarrow> dom f\<guillemotright>"
            by (metis arr_iff_in_hom seq seqE)
          show "\<And>x. \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> dom e'\<guillemotright> \<Longrightarrow> (equ f g \<cdot> ?h) \<cdot> x = e' \<cdot> x"
          proof -
            fix x 
            assume x: "\<guillemotleft>x : \<one>\<^sup>? \<rightarrow> dom e'\<guillemotright>"
            have "(equ f g \<cdot> ?h) \<cdot> x = equ f g \<cdot> ?h \<cdot> x"
              using comp_assoc by blast
            also have "... = equ f g \<cdot> ?H x"
              using app_mkarr h x by presburger
            also have "... = OUT (Dom_equ f g) (IN (Dom_equ f g) (e' \<cdot> x))"
            proof -
              have "?H x \<in> Set (dom_equ f g)"
                using 1 x by blast
              thus ?thesis
                using assms x equ_in_hom app_mkarr
                by (simp add: assms equ_def)
            qed
            also have "... = e' \<cdot> x"
            proof -
              have "e' \<cdot> x \<in> Dom_equ f g"
                by (metis (mono_tags, lifting) e' comp_in_homI eq comp_assoc
                    mem_Collect_eq x)
              thus ?thesis
                using assms ide_dom_equ(7) [of f g "e' \<cdot> x"] by blast
            qed
            finally show "(equ f g \<cdot> ?h) \<cdot> x = e' \<cdot> x" by blast
          qed
        qed
        moreover have "\<And>h'. equ f g \<cdot> h' = e' \<Longrightarrow> h' = ?h"
        proof -
          fix h'
          assume h': "equ f g \<cdot> h' = e'"
          show "h' = ?h"
          proof (intro arr_eqI' [of h' _ _ ?h])
            show 1: "\<guillemotleft>h' : dom e' \<rightarrow> dom_equ f g\<guillemotright>"
              by (metis arr_iff_in_hom assms comp_in_homE equ_simps(2) h' in_homE seq)
            show "\<guillemotleft>?h : dom e' \<rightarrow> dom_equ f g\<guillemotright>"
              using h by blast
            show "\<And>x. \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> dom e'\<guillemotright> \<Longrightarrow> h' \<cdot> x = ?h \<cdot> x"
            proof -
              fix x
              assume x: "\<guillemotleft>x : \<one>\<^sup>? \<rightarrow> dom e'\<guillemotright>"
              have 3: "h' \<cdot> x = IN (Dom_equ f g) (Equ f g (h' \<cdot> x))"
                using assms h' x 1 seq eq ide_dom_equ(6) comp_in_homI in_homI
                by auto
              also have 4: "... = IN (Dom_equ f g) (Fun (equ f g) (h' \<cdot> x))"
                using assms Fun_equ [of f g]
                by (metis (lifting))
              also have 5: "... = IN (Dom_equ f g) (equ f g \<cdot> (h' \<cdot> x))"
                using Fun_def
                by (metis (no_types, lifting) x CollectI comp_in_homI
                    dom_comp h' in_homI seq seqE)
              also have "... = IN (Dom_equ f g) ((equ f g \<cdot> h') \<cdot> x)"
                using comp_assoc by simp
              also have "... = IN (Dom_equ f g) ((equ f g \<cdot> ?h) \<cdot> x)"
                using h h' eq "*" by argo
              also have "... = IN (Dom_equ f g) (equ f g \<cdot> (?h \<cdot> x))"
                using comp_assoc by simp
              also have "... = IN (Dom_equ f g) (Fun (equ f g) (?h \<cdot> x))"
                  using x Fun_def app_mkarr h h' comp_assoc 3 4 5 by auto
              also have "... = IN (Dom_equ f g) (Equ f g (?h \<cdot> x))"
                using assms Fun_equ by (metis (lifting))
              also have "... = ?h \<cdot> x"
                using assms x ide_dom_equ(6) h by auto
              finally show "h' \<cdot> x = ?h \<cdot> x" by blast
            qed
          qed
        qed
        ultimately show "\<exists>!h. equ f g \<cdot> h = e'" by auto
      qed
    qed

    lemma has_equalizers:
    assumes "par f g"
    shows "\<exists>e. has_as_equalizer f g e"
     using assms equ_is_equalizer by blast

  end

  subsection "Exported Notions"

  text\<open>
    As we don't want to clutter the @{locale sets_cat} locale with auxiliary definitions and
    facts that no longer need to be used once we have completed the equalizer construction,
    we have carried out the construction in a separate locale and we now transfer
    to the  @{locale sets_cat} locale only those definitions and facts that we would like to export.
    In general, we will need to export the objects and arrows mentioned by the
    universal property together with the associated infrastructure for establishing the
    types of expressions that use them.
    We will also need to export facts that allow us to externalize these arrows
    as functions between sets of global elements, and we will need facts that give
    the types and inverse relationship between the comparison maps.
  \<close>

  context sets_cat
  begin

    interpretation Equ: equalizers_in_sets_cat sml C ..

    abbreviation equ
    where "equ \<equiv> Equ.equ"

    abbreviation Equ
    where "Equ f g \<equiv> {x. x \<in> Set (dom f) \<and> f \<cdot> x = g \<cdot> x}"

    lemma equalizer_comparison_map_props:
    assumes "par f g"
    shows "bij_betw (OUT (Equ f g)) (Set (dom (equ f g))) (Equ f g)"
    and "bij_betw (IN (Equ f g)) (Equ f g) (Set (dom (equ f g)))"
    and "\<And>x. x \<in> Set (dom (equ f g)) \<Longrightarrow> OUT (Equ f g) x \<in> Set (dom f)"
    and "\<And>y. y \<in> Equ f g \<Longrightarrow> IN (Equ f g) y \<in> Set (dom (equ f g))"
    and "\<And>x. x \<in> Set (dom (equ f g)) \<Longrightarrow> IN (Equ f g) (OUT (Equ f g) x) = x"
    and "\<And>y. y \<in> Equ f g \<Longrightarrow> OUT (Equ f g) (IN (Equ f g) y) = y"
      using assms Equ.ide_dom_equ [of f g] Equ.equ_simps(2) [of f g] by auto

    lemma equ_is_equalizer:
    assumes "par f g"
    shows "has_as_equalizer f g (equ f g)"
      using assms Equ.equ_is_equalizer by blast

    lemma Fun_equ:
    assumes "par f g"
    shows "Fun (equ f g) = (\<lambda>x. if x \<in> Set (dom (equ f g))
                                then OUT {x. x \<in> Set (dom f) \<and> f \<cdot> x = g \<cdot> x} x
                                else null)"
      using assms Equ.Fun_equ by auto

    lemma has_equalizers:
    assumes "par f g"
    shows "\<exists>e. has_as_equalizer f g e"
      using assms Equ.has_equalizers by blast

  end

  section "Binary Products"

  text\<open>
    In this section we show that the category of small sets and functions has binary products.
    We follow the same pattern as for equalizers, except that now the set to which we would
    like to apply \<open>mkide\<close> to obtain a product object will consist of pairs of arrows,
    rather than individual arrows.  This means that we will need to assume the existence of
    a pairing function that embeds the set of pairs of arrows of the category back into the
    original set of arrows.  Once again, in showing that the construction makes sense we will
    need to reason about comparison maps, but once this is done we will be left simply with a
    universal property which does not mention these maps.  After that, we only have to work
    with the comparison maps when relating notions internal to the category to notions
    external to it.
  \<close>

  text\<open>
    The following locale specializes @{locale sets_cat} by adding the assumption that there exists
    a suitable pairing function.  In addition, we need to assume that the smallness notion
    being used is respected by pairing.
  \<close>

  locale sets_cat_with_pairing =
    sets_cat sml C +
    small_product sml +
    pairing \<open>Collect arr\<close>
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)

  text\<open>
    As previously, we carry out the details of the construction in an auxiliary locale
    and later transfer to the @{locale sets_cat} locale only those things that we want to export.
  \<close>

  locale products_in_sets_cat =
    sets_cat_with_pairing sml C
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    lemma small_product_set:
    assumes "ide a" and "ide b"
    shows "small (Set a \<times> Set b)"
      using assms small_Set by fastforce

    lemma embeds_product_sets:
    assumes "ide a" and "ide b"
    shows "embeds (Set a \<times> Set b)"
    proof -
      have "Set a \<times> Set b \<subseteq> Collect arr \<times> Collect arr"
        using assms small_Set by auto
      thus ?thesis
        using assms embeds_pairs
        by (meson image_mono inj_on_subset subset_trans)
    qed

    text\<open>
      We define the product of two objects as the object determined by the cartesian
      product of their sets of elements.
    \<close>

    definition prod\<^sub>o
    where "prod\<^sub>o a b \<equiv> mkide (Set a \<times> Set b)"

    lemma ide_prod\<^sub>o:
    assumes "ide a" and "ide b"
    shows "ide (prod\<^sub>o a b)"
    and "bij_betw (OUT (Set a \<times> Set b)) (Set (prod\<^sub>o a b)) (Set a \<times> Set b)"
    and "bij_betw (IN (Set a \<times> Set b)) (Set a \<times> Set b) (Set (prod\<^sub>o a b))"
    and "\<And>x. x \<in> Set (prod\<^sub>o a b) \<Longrightarrow> OUT (Set a \<times> Set b) x \<in> Set a \<times> Set b"
    and "\<And>y. y \<in> Set a \<times> Set b \<Longrightarrow> IN (Set a \<times> Set b) y \<in> Set (prod\<^sub>o a b)"
    and "\<And>x. x \<in> Set (prod\<^sub>o a b) \<Longrightarrow> IN (Set a \<times> Set b) (OUT (Set a \<times> Set b) x) = x"
    and "\<And>y. y \<in> Set a \<times> Set b \<Longrightarrow> OUT (Set a \<times> Set b) (IN (Set a \<times> Set b) y) = y"
    proof -
      have 1: "small (Set a \<times> Set b)"
        using assms ide_char small_Set small_product by metis
      moreover have 2: "is_embedding_of some_pairing (Set a \<times> Set b)"
      proof -
        have "Set a \<times> Set b \<subseteq> Collect arr \<times> Collect arr"
          using assms ide_char small_Set by blast
        thus ?thesis
          using assms some_pairing_is_embedding
          by (meson image_mono inj_on_subset subset_trans)
      qed
      ultimately show "ide (prod\<^sub>o a b)"
      and 3: "bij_betw (OUT (Set a \<times> Set b)) (Set (prod\<^sub>o a b)) (Set a \<times> Set b)"
        unfolding prod\<^sub>o_def
        using assms ide_mkide bij_OUT by blast+
      show 4: "bij_betw (IN (Set a \<times> Set b)) (Set a \<times> Set b) (Set (prod\<^sub>o a b))"
        using \<open>bij_betw (OUT (Set a \<times> Set b)) (Set (prod\<^sub>o a b)) (Set a \<times> Set b)\<close>
              bij_betw_inv_into prod\<^sub>o_def
        by auto
      show "\<And>x. x \<in> Set (prod\<^sub>o a b) \<Longrightarrow> OUT (Set a \<times> Set b) x \<in> Set a \<times> Set b"
        using 3 bij_betwE by blast
      show "\<And>y. y \<in> Set a \<times> Set b \<Longrightarrow> IN (Set a \<times> Set b) y \<in> Set (prod\<^sub>o a b)"
        using 4 bij_betwE by blast
      show "\<And>x. x \<in> Set (prod\<^sub>o a b) \<Longrightarrow> IN (Set a \<times> Set b) (OUT (Set a \<times> Set b) x) = x"
        using 1 2 IN_OUT prod\<^sub>o_def by auto
      show "\<And>y. y \<in> Set a \<times> Set b \<Longrightarrow> OUT (Set a \<times> Set b) (IN (Set a \<times> Set b) y) = y"
        by (metis "1" "2" OUT_IN)
    qed

    text\<open>
      We next define the projection arrows from a product object in terms of the projection
      functions on the underlying cartesian product of sets.
    \<close>

    abbreviation P\<^sub>0 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "P\<^sub>0 a b \<equiv> \<lambda>x. if x \<in> Set (prod\<^sub>o a b) then snd (OUT (Set a \<times> Set b) x) else null"

    abbreviation P\<^sub>1 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "P\<^sub>1 a b \<equiv> \<lambda>x. if x \<in> Set (prod\<^sub>o a b) then fst (OUT (Set a \<times> Set b) x) else null"

    lemma P\<^sub>0_in_Hom:
    assumes "ide a" and "ide b"
    shows "P\<^sub>0 a b \<in> Hom (prod\<^sub>o a b) b"
    proof
      show "P\<^sub>0 a b \<in> Set (prod\<^sub>o a b) \<rightarrow> Set b"
      proof
        fix x
        assume x: "x \<in> Set (prod\<^sub>o a b)"
        have "OUT (Set a \<times> Set b) x \<in> Set a \<times> Set b"
          using assms x bij_betwE ide_prod\<^sub>o(2) by blast
        thus "P\<^sub>0 a b x \<in> Set b"
          using assms x by force
      qed
      show "P\<^sub>0 a b \<in> {F. \<forall>x. x \<notin> Set (prod\<^sub>o a b) \<longrightarrow> F x = null}"
        by simp
    qed

    lemma P\<^sub>1_in_Hom:
    assumes "ide a" and "ide b"
    shows "P\<^sub>1 a b \<in> Hom (prod\<^sub>o a b) a"
    proof
      show "P\<^sub>1 a b \<in> Set (prod\<^sub>o a b) \<rightarrow> Set a"
      proof
        fix x
        assume x: "x \<in> Set (prod\<^sub>o a b)"
        have "OUT (Set a \<times> Set b) x \<in> Set a \<times> Set b"
          using assms x bij_betwE ide_prod\<^sub>o(2) by blast
        thus "P\<^sub>1 a b x \<in> Set a"
          using assms x by force
      qed
      show "P\<^sub>1 a b \<in> {F. \<forall>x. x \<notin> Set (prod\<^sub>o a b) \<longrightarrow> F x = null}"
        by simp
    qed

    definition pr\<^sub>0 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "pr\<^sub>0 a b \<equiv> mkarr (prod\<^sub>o a b) b (P\<^sub>0 a b)"

    definition pr\<^sub>1 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "pr\<^sub>1 a b \<equiv> mkarr (prod\<^sub>o a b) a (P\<^sub>1 a b)"

    lemma pr_in_hom [intro]:
    assumes "ide a" and "ide b"
    shows "in_hom (pr\<^sub>1 a b) (prod\<^sub>o a b) a"
    and "in_hom (pr\<^sub>0 a b) (prod\<^sub>o a b) b"
      using assms pr\<^sub>0_def pr\<^sub>1_def mkarr_in_hom ide_prod\<^sub>o P\<^sub>0_in_Hom P\<^sub>1_in_Hom by auto

    lemma pr_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr (pr\<^sub>0 a b)" and "dom (pr\<^sub>0 a b) = prod\<^sub>o a b" and "cod (pr\<^sub>0 a b) = b"
    and "arr (pr\<^sub>1 a b)" and "dom (pr\<^sub>1 a b) = prod\<^sub>o a b" and "cod (pr\<^sub>1 a b) = a"
      using assms pr_in_hom by blast+

    lemma Fun_pr:
    assumes "ide a" and "ide b"
    shows "Fun (pr\<^sub>1 a b) = P\<^sub>1 a b"
    and "Fun (pr\<^sub>0 a b) = P\<^sub>0 a b"
      using assms Fun_mkarr pr\<^sub>0_def pr\<^sub>1_def pr_simps(1,4) by presburger+

    text\<open>
      Tupling of arrows is also defined in terms of the underlying cartesian product.
    \<close>
    definition Tuple :: "'U \<Rightarrow> 'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "Tuple f g \<equiv> (\<lambda>x. if x \<in> Set (dom f)
                             then IN (Set (cod f) \<times> Set (cod g)) (Fun f x, Fun g x)
                             else null)"

    definition tuple :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "tuple f g \<equiv> mkarr (dom f) (prod\<^sub>o (cod f) (cod g)) (Tuple f g)"

    lemma tuple_in_hom [intro]:
    assumes "\<guillemotleft>f : c \<rightarrow> a\<guillemotright>" and "\<guillemotleft>g : c \<rightarrow> b\<guillemotright>"
    shows "\<guillemotleft>tuple f g : c \<rightarrow> prod\<^sub>o a b\<guillemotright>"
    proof -
      have "Tuple f g \<in> Set c \<rightarrow> Set (prod\<^sub>o a b)"
      proof
        fix x
        assume x: "x \<in> Set c"
        have "bij_betw (IN (Set a \<times> Set b)) (Set a \<times> Set b) (Set (mkide (Set a \<times> Set b)))"
          using assms embeds_pairs ide_prod\<^sub>o(2) prod\<^sub>o_def
          by (metis ide_cod ide_prod\<^sub>o(3) in_homE)
        thus "Tuple f g x \<in> Set (prod\<^sub>o a b)"
          unfolding Tuple_def prod\<^sub>o_def Fun_def
          using assms x bij_betw_apply in_homE small_Set
          by auto fastforce
      qed
      moreover have "\<And>x. x \<notin> Set c \<Longrightarrow> Tuple f g x = null"
        unfolding Tuple_def
        using assms by auto
      ultimately show ?thesis
        unfolding tuple_def
        using assms mkarr_in_hom ide_prod\<^sub>o(1) by fastforce
    qed

    lemma tuple_simps [simp]:
    assumes "span f g"
    shows "arr (tuple f g)"
    and "dom (tuple f g) = dom f"
    and "cod (tuple f g) = prod\<^sub>o (cod f) (cod g)"
      using assms
      by (metis assms in_homE in_homI tuple_in_hom)+

    text\<open>
      In verifying the equations required for a categorical product, we unfortunately
      do have to fuss with the comparison maps.
    \<close>

    lemma comp_pr_tuple:
    assumes "span f g"
    shows "pr\<^sub>1 (cod f) (cod g) \<cdot> tuple f g = f"
    and "pr\<^sub>0 (cod f) (cod g) \<cdot> tuple f g = g"
    proof -
      let ?c = "dom f" and ?a = "cod f" and ?b = "cod g"
      show "pr\<^sub>1 ?a ?b \<cdot> tuple f g = f"
      proof -
        have "pr\<^sub>1 ?a ?b \<cdot> tuple f g =
              mkarr (prod\<^sub>o ?a ?b) ?a (P\<^sub>1 ?a ?b) \<cdot> mkarr ?c (prod\<^sub>o ?a ?b) (Tuple f g)"
          unfolding pr\<^sub>1_def tuple_def Tuple_def
          using assms by auto
        also have "... = mkarr ?c ?a (P\<^sub>1 ?a ?b \<circ> Tuple f g)"
          using assms comp_mkarr
          by (metis (lifting) calculation ide_cod pr_simps(4,5) seqE seqI tuple_simps(1,3))
        also have "... = mkarr ?c ?a
                          (\<lambda>x. if x \<in> Set ?c
                               then fst (OUT (Set ?a \<times> Set ?b)
                                           (IN (Set ?a \<times> Set ?b) (Fun f x, Fun g x)))
                               else null)"
        proof -
          have "(P\<^sub>1 ?a ?b \<circ> Tuple f g) =
                (\<lambda>x. if \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> ?c\<guillemotright>
                     then fst (OUT (Set ?a \<times> Set ?b)
                                 (IN (Set ?a \<times> Set ?b) (Fun f x, Fun g x)))
                     else null)"
            using assms ide_prod\<^sub>o(3) [of ?a ?b] bij_betw_apply Tuple_def Fun_def by fastforce
          thus ?thesis by simp
        qed
        also have "... = mkarr ?c ?a (\<lambda>x. if x \<in> Set ?c then fst (Fun f x, Fun g x) else null)"
        proof -
          have "\<And>x. x \<in> Set ?c \<Longrightarrow>
                       OUT (Set ?a \<times> Set ?b) (IN (Set ?a \<times> Set ?b) (Fun f x, Fun g x)) =
                       (Fun f x, Fun g x)"
            using assms OUT_IN [of "Set ?a \<times> Set ?b"] small_product_set embeds_product_sets
                  Fun_def
            by auto
          thus ?thesis
            by (metis (lifting))
        qed
        also have "... = mkarr ?c ?a (\<lambda>x. if x \<in> Set ?c then Fun f x else null)"
          using assms by (metis (lifting) fst_eqD)
        also have "... = f"
        proof -
          have "Fun f = (\<lambda>x. if x \<in> Set ?c then Fun f x else null)"
            unfolding Fun_def by meson
          thus ?thesis
            by (metis (no_types, lifting) arr_iff_in_hom assms mkarr_Fun)
        qed
        finally show ?thesis by simp
      qed
      show "pr\<^sub>0 ?a ?b \<cdot> tuple f g = g"
      proof -
        have "pr\<^sub>0 ?a ?b \<cdot> tuple f g =
              mkarr (prod\<^sub>o ?a ?b) ?b (P\<^sub>0 ?a ?b) \<cdot> mkarr ?c (prod\<^sub>o ?a ?b) (Tuple f g)"
          unfolding pr\<^sub>0_def tuple_def Tuple_def
          using assms comp_mkarr by auto
        also have "... = mkarr ?c ?b (P\<^sub>0 ?a ?b \<circ> Tuple f g)"
          using assms comp_mkarr
          by (metis (lifting) calculation ide_cod seqE seqI pr_simps(1,2) tuple_simps(1,3))
        also have "... = mkarr ?c ?b
                           (\<lambda>x. if x \<in> Set ?c
                                then snd (OUT (Set ?a \<times> Set ?b)
                                            (IN (Set ?a \<times> Set ?b) (Fun f x, Fun g x)))
                                else null)"
        proof -
          have "(P\<^sub>0 ?a ?b \<circ> Tuple f g) =
                (\<lambda>x. if x \<in> Set ?c
                     then snd (OUT (Set ?a \<times> Set ?b)
                                 (IN (Set ?a \<times> Set ?b) (Fun f x, Fun g x)))
                     else null)"
            using assms ide_prod\<^sub>o(3) [of ?a ?b] bij_betw_apply Tuple_def Fun_def by fastforce
          thus ?thesis by simp
        qed
        also have "... = mkarr ?c ?b (\<lambda>x. if x \<in> Set ?c then snd (Fun f x, Fun g x) else null)"
        proof -
          have "\<And>x. x \<in> Set ?c \<Longrightarrow>
                       OUT (Set ?a \<times> Set ?b) (IN (Set ?a \<times> Set ?b) (Fun f x, Fun g x)) =
                       (Fun f x, Fun g x)"
            using assms OUT_IN [of "Set ?a \<times> Set ?b"] small_product_set embeds_product_sets
                  Fun_def
            by auto
          thus ?thesis
            by (metis (lifting))
        qed
        also have "... = mkarr ?c ?b (\<lambda>x. if x \<in> Set ?c then Fun g x else null)"
          using assms by (metis (lifting) snd_eqD)
        also have "... = g"
        proof -
          have "Fun g = (\<lambda>x. if x \<in> Set ?c then Fun g x else null)"
            unfolding Fun_def by (metis assms)
          thus ?thesis
            by (metis (no_types, lifting) arr_iff_in_hom assms mkarr_Fun)
        qed
        finally show ?thesis by simp
      qed
    qed

    lemma Fun_tuple:
    assumes "span f g"
    shows "Fun (tuple f g) =
           (\<lambda>x. if x \<in> Set (dom f)
                then IN (Set (cod f) \<times> Set (cod g)) (Fun f x, Fun g x)
                else null)"
      using tuple_def Tuple_def Fun_mkarr assms tuple_simps(1) by presburger

    lemma binary_product_pr:
    assumes "ide a" and "ide b"
    shows "binary_product C a b (pr\<^sub>1 a b) (pr\<^sub>0 a b)"
    proof
      show "has_as_binary_product a b (pr\<^sub>1 a b) (pr\<^sub>0 a b)"
      proof
        show 1: "span (pr\<^sub>1 a b) (pr\<^sub>0 a b)"
          using assms by auto
        show "cod (pr\<^sub>1 a b) = a"
          using assms by auto
        show "cod (pr\<^sub>0 a b) = b"
          using assms by auto
        fix x f g
        assume f: "\<guillemotleft>f : x \<rightarrow> a\<guillemotright>" and g: "\<guillemotleft>g : x \<rightarrow> b\<guillemotright>"
        let ?H = "\<lambda>z. if z \<in> Set x then IN (Set a \<times> Set b) (Fun f z, Fun g z) else null"
        let ?h = "mkarr x (prod\<^sub>o a b) ?H"
        have h: "\<guillemotleft>?h : x \<rightarrow> dom (pr\<^sub>1 a b)\<guillemotright> \<and> C (pr\<^sub>1 a b) ?h = f \<and> C (pr\<^sub>0 a b) ?h = g"
          using assms f g tuple_in_hom [of f x a g b] comp_pr_tuple [of f g]
          unfolding tuple_def Tuple_def by auto
        moreover have "\<And>h'. \<guillemotleft>h' : x \<rightarrow> dom (pr\<^sub>1 a b)\<guillemotright> \<and> C (pr\<^sub>1 a b) h' = f \<and>
                            C (pr\<^sub>0 a b) h' = g
                               \<Longrightarrow> h' = ?h"
        proof -
          fix h'
          assume h': "\<guillemotleft>h' : x \<rightarrow> dom (pr\<^sub>1 a b)\<guillemotright> \<and> C (pr\<^sub>1 a b) h' = f \<and> C (pr\<^sub>0 a b) h' = g"
          show "h' = ?h"
          proof (intro arr_eqI' [of h'])
            show "\<guillemotleft>h' : x \<rightarrow> dom (prod\<^sub>o a b)\<guillemotright>"
              using assms h' ide_prod\<^sub>o(1) by auto
            show "\<guillemotleft>?h : x \<rightarrow> dom (prod\<^sub>o a b)\<guillemotright>"
              using assms h ide_prod\<^sub>o(1) by auto
            show "\<And>z. \<guillemotleft>z : \<one>\<^sup>? \<rightarrow> x\<guillemotright> \<Longrightarrow> h' \<cdot> z = ?h \<cdot> z"
            proof -
              fix z
              assume z: "\<guillemotleft>z : \<one>\<^sup>? \<rightarrow> x\<guillemotright>"
              have "h' \<cdot> z = Fun h' z"
                using h' z Fun_def by auto
              also have "... = IN (Set a \<times> Set b) (Fun f z, Fun g z)"
              proof -
                have "fst (OUT (Set a \<times> Set b) (Fun h' z)) = Fun f z"
                proof -
                  have "Fun f z = Fun (pr\<^sub>1 a b \<cdot> h') z"
                    using h' by force
                  also have "... = (P\<^sub>1 a b \<circ> Fun h') z"
                    using assms(1-2) f h' Fun_pr(1) Fun_comp arrI by auto
                  also have "... = fst (OUT (Set a \<times> Set b) (Fun h' z))"
                    using assms(1,2) h' z Fun_def by auto
                  finally show ?thesis by simp
                qed
                moreover have "snd (OUT (Set a \<times> Set b) (Fun h' z)) = Fun g z"
                proof -
                  have "Fun g z = Fun (pr\<^sub>0 a b \<cdot> h') z"
                    using h' by force
                  also have "... = (P\<^sub>0 a b \<circ> Fun h') z"
                    using assms(1-2) g h' Fun_pr(2) Fun_comp arrI by auto
                  also have "... = snd (OUT (Set a \<times> Set b) (Fun h' z))"
                    using assms(1,2) h' z Fun_def by auto
                 finally show ?thesis by simp
                qed
                ultimately have "IN (Set a \<times> Set b) (Fun f z, Fun g z) =
                                 IN (Set a \<times> Set b) (OUT (Set a \<times> Set b) (Fun h' z))"
                  by (metis split_pairs2)
                also have "... = Fun h' z"
                  using assms h' z IN_OUT \<open>C h' z = Fun h' z\<close> prod\<^sub>o_def Fun_def
                    small_product_set [of a b] embeds_product_sets [of a b]
                  by auto
                finally show ?thesis by simp  
              qed
              also have "... = C ?h z"
                using app_mkarr assms(1,2) h z by auto
              finally show "C h' z = C ?h z" by blast
            qed
          qed
        qed
        ultimately show "\<exists>!h. \<guillemotleft>h : x \<rightarrow> dom (pr\<^sub>1 a b)\<guillemotright> \<and> C (pr\<^sub>1 a b) h = f \<and>
                              C (pr\<^sub>0 a b) h = g"
          by auto
      qed
    qed

    lemma has_binary_products:
    shows has_binary_products
      using binary_product_pr
      by (meson binary_product.has_as_binary_product has_binary_products_def)

  end

  subsection "Exported Notions"

  text\<open>
    We now transfer to the @{locale sets_cat_with_pairing} locale just the things we want to export.
    The projections are the main thing; most of the rest is inherited from the
    @{locale elementary_category_with_binary_products} locale.  We also need to include some
    infrastucture for moving in and out of the category and working with the comparison maps.
  \<close>

  context sets_cat_with_pairing
  begin

    interpretation Products: products_in_sets_cat ..

    abbreviation pr\<^sub>0 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "pr\<^sub>0 \<equiv> Products.pr\<^sub>0"

    abbreviation pr\<^sub>1 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "pr\<^sub>1 \<equiv> Products.pr\<^sub>1"

    sublocale elementary_category_with_binary_products C pr\<^sub>0 pr\<^sub>1
    proof
      show "\<And>f g. span f g \<Longrightarrow> \<exists>!l. C (pr\<^sub>1 (cod f) (cod g)) l = f \<and> C (pr\<^sub>0 (cod f) (cod g)) l = g"
      proof -
        fix f g
        assume fg: "span f g"
        interpret binary_product C \<open>cod f\<close> \<open>cod g\<close> \<open>pr\<^sub>1 (cod f) (cod g)\<close> \<open>pr\<^sub>0 (cod f) (cod g)\<close>
          using fg Products.binary_product_pr ide_cod by blast
        show "\<exists>!l. C (pr\<^sub>1 (cod f) (cod g)) l = f \<and> C (pr\<^sub>0 (cod f) (cod g)) l = g"
          by (metis (full_types) fg tuple_props(4,5,6))
      qed
    qed auto

    lemma bin_prod_comparison_map_props:
    assumes "ide a" and "ide b"
    shows "OUT (Set a \<times> Set b) \<in> Set (prod a b) \<rightarrow> Set a \<times> Set b"
    and "IN (Set a \<times> Set b) \<in> Set a \<times> Set b \<rightarrow> Set (prod a b)"
    and "\<And>x. x \<in> Set (prod a b) \<Longrightarrow> IN (Set a \<times> Set b) (OUT (Set a \<times> Set b) x) = x"
    and "\<And>y. y \<in> Set a \<times> Set b \<Longrightarrow> OUT (Set a \<times> Set b) (IN (Set a \<times> Set b) y) = y"
    and "bij_betw (OUT (Set a \<times> Set b)) (Set (prod a b)) (Set a \<times> Set b)"
    and "bij_betw (IN (Set a \<times> Set b)) (Set a \<times> Set b) (Set (prod a b))"
      using assms Products.ide_prod\<^sub>o [of a b] pr_simps(5) by auto

    lemma Fun_pr\<^sub>0:
    assumes "ide a" and "ide b"
    shows "Fun (pr\<^sub>0 a b) = Products.P\<^sub>0 a b"
      using assms Products.Fun_pr(2) by auto[1]

    lemma Fun_pr\<^sub>1:
    assumes "ide a" and "ide b"
    shows "Fun (pr\<^sub>1 a b) = Products.P\<^sub>1 a b"
      using assms Products.Fun_pr(1) by auto[1]

    lemma Fun_prod:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : c \<rightarrow> d\<guillemotright>"
    shows "Fun (prod f g) = (\<lambda>x. if x \<in> Set (prod a c)
                                 then tuple (Fun f (C (pr\<^sub>1 a c) x)) (Fun g (C (pr\<^sub>0 a c) x))
                                 else null)"
    proof
      fix x
      show "Fun (prod f g) x = (if x \<in> Set (prod a c)
                                then tuple (Fun f (C (pr\<^sub>1 a c) x)) (Fun g (C (pr\<^sub>0 a c) x))
                                else null)"
      proof (cases "x \<in> Set (prod a c)")
        case False
        show ?thesis
          using False
          by (metis assms(1,2) in_homE prod_simps(2) Fun_def)
        next
        case True
        show ?thesis
        proof -
          have "\<guillemotleft>x : \<one>\<^sup>? \<rightarrow> dom (prod f g)\<guillemotright>"
            using True assms(1,2) by fastforce
          moreover have "\<guillemotleft>pr\<^sub>1 a c \<cdot> x : \<one>\<^sup>? \<rightarrow> dom f\<guillemotright> \<and> \<guillemotleft>pr\<^sub>0 a c \<cdot> x : \<one>\<^sup>? \<rightarrow> dom g\<guillemotright>"
            using assms True
            by (intro conjI comp_in_homI) fastforce+
          moreover have "prod f g \<cdot> x = tuple (f \<cdot> pr\<^sub>1 a c \<cdot> x) (g \<cdot> pr\<^sub>0 a c \<cdot> x)"
            using assms True prod_tuple tuple_pr_arr
            by (metis calculation(2) ide_dom in_homE seqI)
          ultimately show ?thesis
            using assms True Fun_def by auto
        qed
      qed
    qed

    lemma prod_ide_eq:
    assumes "ide a" and "ide b"
    shows "prod a b = mkide (Set a \<times> Set b)"
      using assms(1,2) pr_simps(2) Products.prod\<^sub>o_def by force

    lemma tuple_eq:
    assumes "\<guillemotleft>f : x \<rightarrow> a\<guillemotright>" and "\<guillemotleft>g : x \<rightarrow> b\<guillemotright>"
    shows "tuple f g = mkarr x (prod a b)
                         (\<lambda>z. if z \<in> Set x
                              then IN (Set a \<times> Set b) (Fun f z, Fun g z)
                              else null)"
    proof -
      have "tuple f g = Products.tuple f g"
        by (metis Products.comp_pr_tuple(1,2) assms(1,2) in_homE pr_tuple(1,2) universal)
      thus ?thesis
        unfolding Products.tuple_def Products.Tuple_def
        using assms Products.prod\<^sub>o_def prod_ide_eq by fastforce
    qed

    lemma tuple_point_eq:
    assumes "\<guillemotleft>x : \<one>\<^sup>? \<rightarrow> a\<guillemotright>" and "\<guillemotleft>y : \<one>\<^sup>? \<rightarrow> b\<guillemotright>"
    shows "tuple x y = IN (Set a \<times> Set b) (x, y)"
    proof -
      have 1: "tuple x y = mkarr \<one>\<^sup>? (prod a b)
                             (\<lambda>z. if z \<in> Set \<one>\<^sup>? then IN (Set a \<times> Set b) (x, y) else null)"
      proof -
        have "\<And>z. z \<in> Set \<one>\<^sup>? \<Longrightarrow> Fun x z = x \<and> Fun y z = y"
          unfolding Fun_def
          by (metis assms CollectD comp_arr_dom ide_dom ide_in_hom in_homE some_trm_eqI)
        hence "(\<lambda>z. if z \<in> Set \<one>\<^sup>? then IN (Set a \<times> Set b) (Fun x z, Fun y z) else null) =
               (\<lambda>z. if z \<in> Set \<one>\<^sup>? then IN (Set a \<times> Set b) (x, y) else null)"
          by fastforce
        thus ?thesis
          using assms tuple_eq by simp
      qed
      also have "... = IN (Set a \<times> Set b) (x, y)"
      proof -
        have "mkarr \<one>\<^sup>? (prod a b)
                (\<lambda>z. if z \<in> Set \<one>\<^sup>? then IN (Set a \<times> Set b) (x, y) else null) =
              mkarr \<one>\<^sup>? (prod a b)
                (\<lambda>z. if z \<in> Set \<one>\<^sup>? then IN (Set a \<times> Set b) (x, y) else null) \<cdot> \<one>\<^sup>?"
          by (metis (lifting) assms(1,2) calculation comp_arr_dom dom_mkarr in_homE
              tuple_simps(1))
        also have "... = IN (Set a \<times> Set b) (x, y)"
          using app_mkarr [of "\<one>\<^sup>?" "prod a b" _ "\<one>\<^sup>?"]
          by (metis (full_types, lifting) CollectI
              assms(1,2) 1 ide_in_hom ide_some_terminal tuple_in_hom)
        finally show ?thesis by blast
      qed
      finally show ?thesis by blast
    qed

    lemma Fun_tuple:
    assumes "span f g"
    shows "Fun (tuple f g) =
           (\<lambda>x. if x \<in> Set (dom f)
                then IN (Set (cod f) \<times> Set (cod g)) (Fun f x, Fun g x)
                else null)"
      using assms Fun_mkarr tuple_eq [of f "dom f" "cod f" g "cod g"]
      by (metis (lifting) in_homI tuple_simps(1))

  end

  section "Binary Coproducts"

  text\<open>
    In this section we prove the existence of binary coproducts, following the
    same approach as for binary products.  The required assumptions are slightly
    different, because here we need smallness to be preserved by union.
  \<close>

  locale sets_cat_with_cotupling =
    sets_cat_with_bool sml C +
    small_sum sml +
    pairing \<open>Collect arr\<close>
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)

  locale coproducts_in_sets_cat =
    sets_cat_with_cotupling sml C
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    abbreviation Coprod
    where "Coprod a b \<equiv> ({tt} \<times> Set a) \<union> ({ff} \<times> Set b)"

    lemma small_Coprod:
    assumes "ide a" and "ide b"
    shows "small (Coprod a b)"
      using assms small_product
      by (metis Set_two ide_two(1) small_Set small_insert_iff small_union)

    lemma embeds_Coprod:
    assumes "ide a" and "ide b"
    shows "embeds (Coprod a b)"
    proof -
      have "Coprod a b \<subseteq> Collect arr \<times> Collect arr"
        using ff_simps(1) tt_simps(1) by blast
      thus ?thesis
        using embeds_pairs
        by (simp add: embeds_subset)
    qed

    definition coprod\<^sub>o
    where "coprod\<^sub>o a b \<equiv> mkide (Coprod a b)"

    lemma ide_coprod\<^sub>o:
    assumes "ide a" and "ide b"
    shows "ide (coprod\<^sub>o a b)"
    and "bij_betw (OUT (Coprod a b)) (Set (coprod\<^sub>o a b)) (Coprod a b)"
    and "bij_betw (IN (Coprod a b)) (Coprod a b) (Set (coprod\<^sub>o a b))"
    and "\<And>x. x \<in> Set (coprod\<^sub>o a b) \<Longrightarrow> OUT (Coprod a b) x \<in> Coprod a b"
    and "\<And>y. y \<in> Coprod a b \<Longrightarrow> IN (Coprod a b) y \<in> Set (coprod\<^sub>o a b)"
    and "\<And>x. x \<in> Set (coprod\<^sub>o a b) \<Longrightarrow> IN (Coprod a b) (OUT (Coprod a b) x) = x"
    and "\<And>y. y \<in> Coprod a b \<Longrightarrow> OUT (Coprod a b) (IN (Coprod a b) y) = y"
    proof -
      show "ide (coprod\<^sub>o a b)"
      and 1: "bij_betw (OUT (Coprod a b)) (Set (coprod\<^sub>o a b)) (Coprod a b)"
        unfolding coprod\<^sub>o_def
        using assms ide_mkide(1) bij_OUT small_Coprod embeds_Coprod by metis+
      show 2: "bij_betw (IN (Coprod a b)) (Coprod a b) (Set (coprod\<^sub>o a b))"
        using 1 bij_betw_inv_into coprod\<^sub>o_def by auto
      show "\<And>x. x \<in> Set (coprod\<^sub>o a b) \<Longrightarrow> OUT (Coprod a b) x \<in> Coprod a b"
        using 1 bij_betwE by blast
      show "\<And>y. y \<in> Coprod a b \<Longrightarrow> IN (Coprod a b) y \<in> Set (coprod\<^sub>o a b)"
        using 2 bij_betwE by blast
      show "\<And>x. x \<in> Set (coprod\<^sub>o a b) \<Longrightarrow> IN (Coprod a b) (OUT (Coprod a b) x) = x"
        using assms small_Coprod embeds_Coprod IN_OUT coprod\<^sub>o_def by metis
      show "\<And>y. y \<in> Coprod a b \<Longrightarrow> OUT (Coprod a b) (IN (Coprod a b) y) = y"
        using assms small_Coprod embeds_Coprod coprod\<^sub>o_def 1
              bij_betw_inv_into_right
                [of "OUT (Coprod a b)" "Set (coprod\<^sub>o a b)" "Coprod a b"]
        by presburger
    qed

    abbreviation In\<^sub>0 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "In\<^sub>0 a b \<equiv> \<lambda>x. if x \<in> Set b then IN (Coprod a b) (ff, x) else null"

    abbreviation In\<^sub>1 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "In\<^sub>1 a b \<equiv> \<lambda>x. if x \<in> Set a then IN (Coprod a b) (tt, x) else null"

    lemma In\<^sub>0_in_Hom:
    assumes "ide a" and "ide b"
    shows "In\<^sub>0 a b \<in> Hom b (coprod\<^sub>o a b)"
    proof
      show "In\<^sub>0 a b \<in> {F. \<forall>x. x \<notin> Set b \<longrightarrow> F x = null}" by simp
      show "In\<^sub>0 a b \<in> Set b \<rightarrow> Set (coprod\<^sub>o a b)"
      proof
        fix x
        assume x: "x \<in> Set b"
        have "(ff, x) \<in> Coprod a b"
          using assms x by blast
        thus "In\<^sub>0 a b x \<in> Set (coprod\<^sub>o a b)"
          using assms x ide_coprod\<^sub>o(3) bij_betwE ide_coprod\<^sub>o(5) by presburger
      qed
    qed

    lemma In\<^sub>1_in_Hom:
    assumes "ide a" and "ide b"
    shows "In\<^sub>1 a b \<in> Hom a (coprod\<^sub>o a b)"
    proof
      show "In\<^sub>1 a b \<in> {F. \<forall>x. x \<notin> Set a \<longrightarrow> F x = null}" by simp
      show "In\<^sub>1 a b \<in> Set a \<rightarrow> Set (coprod\<^sub>o a b)"
      proof
        fix x
        assume x: "x \<in> Set a"
        have "(tt, x) \<in> Coprod a b"
          using assms x by blast
        thus "In\<^sub>1 a b x \<in> Set (coprod\<^sub>o a b)"
          using assms x ide_coprod\<^sub>o(3) bij_betwE ide_coprod\<^sub>o(5) by presburger
      qed
    qed

    definition in\<^sub>0 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "in\<^sub>0 a b \<equiv> mkarr b (coprod\<^sub>o a b) (In\<^sub>0 a b)"

    definition in\<^sub>1 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "in\<^sub>1 a b \<equiv> mkarr a (coprod\<^sub>o a b) (In\<^sub>1 a b)"

    lemma in_in_hom [intro, simp]:
    assumes "ide a" and "ide b"
    shows "in_hom (in\<^sub>1 a b) a (coprod\<^sub>o a b)"
    and "in_hom (in\<^sub>0 a b) b (coprod\<^sub>o a b)"
      using assms in\<^sub>0_def in\<^sub>1_def mkarr_in_hom ide_coprod\<^sub>o In\<^sub>0_in_Hom In\<^sub>1_in_Hom by auto

    lemma in_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr (in\<^sub>0 a b)" and "dom (in\<^sub>0 a b) = b" and "cod (in\<^sub>0 a b) = coprod\<^sub>o a b"
    and "arr (in\<^sub>1 a b)" and "dom (in\<^sub>1 a b) = a" and "cod (in\<^sub>1 a b) = coprod\<^sub>o a b"
      using assms in_in_hom by blast+

    lemma Fun_in:
    assumes "ide a" and "ide b"
    shows "Fun (in\<^sub>1 a b) = In\<^sub>1 a b"
    and "Fun (in\<^sub>0 a b) = In\<^sub>0 a b"
      using assms Fun_mkarr in\<^sub>0_def in\<^sub>1_def in_simps(1,4) by presburger+

    definition Cotuple :: "'U \<Rightarrow> 'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "Cotuple f g \<equiv> (\<lambda>x. if x \<in> Set (coprod\<^sub>o (dom f) (dom g))
                              then if fst (OUT (Coprod (dom f) (dom g)) x) = tt
                                   then Fun f (snd (OUT (Coprod (dom f) (dom g)) x))
                                   else if fst (OUT (Coprod (dom f) (dom g)) x) = ff
                                        then Fun g (snd (OUT (Coprod (dom f) (dom g)) x))
                                        else null
                              else null)"

    definition cotuple :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "cotuple f g \<equiv> mkarr (coprod\<^sub>o (dom f) (dom g)) (cod f) (Cotuple f g)"

    lemma cotuple_in_hom [intro, simp]:
    assumes "\<guillemotleft>f : a \<rightarrow> c\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>cotuple f g : coprod\<^sub>o a b \<rightarrow> c\<guillemotright>"
    proof -
      have bij: "bij_betw (OUT (Coprod a b)) (Set (coprod\<^sub>o a b)) (Coprod a b)"
        using assms ide_coprod\<^sub>o(2) ide_dom by blast
      have "Cotuple f g \<in> Set (coprod\<^sub>o a b) \<rightarrow> Set c"
      proof
        fix x
        assume x: "x \<in> Set (coprod\<^sub>o a b)"
        have 1: "OUT (Coprod a b) x \<in> Coprod a b"
          using x bij bij_betwE by blast
        have "fst (OUT (Coprod a b) x) = tt \<or> fst (OUT (Coprod a b) x) = ff"
          using 1 by fastforce
        moreover have "fst (OUT (Coprod a b) x) = tt \<Longrightarrow> Cotuple f g x \<in> Set c"
        proof -
          assume 2: "fst (OUT (Coprod a b) x) = tt"
          have "snd (OUT (Coprod a b) x) \<in> Set a"
            using 1 2 tt_ne_ff by auto
          thus ?thesis
            unfolding Cotuple_def
            using assms x 2 Fun_in_Hom [of f a c] tt_ne_ff
            by auto fastforce
        qed
        moreover have "fst (OUT (Coprod a b) x) = ff \<Longrightarrow> Cotuple f g x \<in> Set c"
        proof -
          assume 2: "fst (OUT (Coprod a b) x) = ff"
          have "snd (OUT (Coprod a b) x) \<in> Set b"
            using 1 2 tt_ne_ff by auto
          thus ?thesis
            unfolding Cotuple_def
            using assms x 2 Fun_in_Hom [of g b c] tt_ne_ff by auto
        qed
        ultimately show "Cotuple f g x \<in> Set c" by blast
      qed
      moreover have "\<And>x. x \<notin> Set (coprod\<^sub>o a b) \<Longrightarrow> Cotuple f g x = null"
        unfolding Cotuple_def
        using assms by auto
      ultimately show ?thesis
        unfolding cotuple_def
        using assms mkarr_in_hom ide_coprod\<^sub>o(1) by fastforce
    qed

    lemma cotuple_simps [simp]:
    assumes "cospan f g"
    shows "arr (cotuple f g)"
    and "dom (cotuple f g) = coprod\<^sub>o (dom f) (dom g)"
    and "cod (cotuple f g) = cod f"
      using assms
      by (metis assms in_homE in_homI cotuple_in_hom)+

    lemma comp_cotuple_in:
    assumes "cospan f g"
    shows "cotuple f g \<cdot> in\<^sub>1 (dom f) (dom g) = f"
    and "cotuple f g \<cdot> in\<^sub>0 (dom f) (dom g) = g"
    proof -
      let ?a = "dom f" and ?b = "dom g" and ?c = "cod f"
      show "cotuple f g \<cdot> in\<^sub>1 (dom f) (dom g) = f"
      proof -
        have "cotuple f g \<cdot> in\<^sub>1 (dom f) (dom g) =
              mkarr (coprod\<^sub>o ?a ?b) ?c (Cotuple f g) \<cdot> mkarr ?a (coprod\<^sub>o ?a ?b) (In\<^sub>1 ?a ?b)"
          unfolding in\<^sub>1_def cotuple_def
          using assms by auto
        also have "... = mkarr ?a ?c (Cotuple f g \<circ> In\<^sub>1 ?a ?b)"
          using assms comp_mkarr cotuple_def cotuple_simps(1) ide_dom in\<^sub>1_def in_simps(4)
          by presburger
        also have "... = mkarr ?a ?c
                           (\<lambda>x. if x \<in> Set ?a
                                then Fun f (snd (OUT (Coprod ?a ?b) (IN (Coprod ?a ?b) (tt, x))))
                                else null)"
        proof -
          have "\<And>x. x \<in> Set ?a \<Longrightarrow>
                      (Cotuple f g \<circ> In\<^sub>1 ?a ?b) x =
                      Fun f (snd (OUT (Coprod ?a ?b) (IN (Coprod ?a ?b) (tt, x))))"
            unfolding Cotuple_def tt_ne_ff
            using assms tt_ne_ff ide_coprod\<^sub>o by auto
          hence "Cotuple f g \<circ> In\<^sub>1 ?a ?b =
                (\<lambda>x. if x \<in> Set ?a
                     then Fun f (snd (OUT (Coprod ?a ?b) (IN (Coprod ?a ?b) (tt, x))))
                     else null)"
            unfolding Cotuple_def
            by fastforce
          thus ?thesis by simp
        qed
        also have "... = mkarr ?a ?c (\<lambda>x. if x \<in> Set ?a then Fun f x else null)"
        proof -
          have "\<And>x. x \<in> Set ?a \<Longrightarrow>
                          Fun f (snd (OUT (Coprod ?a ?b) (IN (Coprod ?a ?b) (tt, x)))) = Fun f x"
            using assms ide_coprod\<^sub>o(7) by auto
          thus ?thesis
            by meson
        qed
        also have "... = f"
        proof -
          have "Fun f = (\<lambda>x. if x \<in> Set ?a then Fun f x else null)"
            unfolding Fun_def by meson
          thus ?thesis
            by (metis (no_types, lifting) arr_iff_in_hom assms mkarr_Fun)
        qed
        finally show ?thesis by blast
      qed
      show "cotuple f g \<cdot> in\<^sub>0 (dom f) (dom g) = g"
      proof -
        have "cotuple f g \<cdot> in\<^sub>0 (dom f) (dom g) =
              mkarr (coprod\<^sub>o ?a ?b) ?c (Cotuple f g) \<cdot> mkarr ?b (coprod\<^sub>o ?a ?b) (In\<^sub>0 ?a ?b)"
          unfolding in\<^sub>0_def cotuple_def
          using assms by auto
        also have "... = mkarr ?b ?c (Cotuple f g \<circ> In\<^sub>0 ?a ?b)"
          using assms comp_mkarr cotuple_def cotuple_simps(1) ide_dom in\<^sub>0_def in_simps(1)
          by presburger
        also have "... = mkarr ?b ?c
                           (\<lambda>x. if x \<in> Set ?b
                                then Fun g (snd (OUT (Coprod ?a ?b) (IN (Coprod ?a ?b) (ff, x))))
                                else null)"
        proof -
          have "\<And>x. x \<in> Set ?b \<Longrightarrow>
                      (Cotuple f g \<circ> In\<^sub>0 ?a ?b) x =
                      Fun g (snd (OUT (Coprod ?a ?b) (IN (Coprod ?a ?b) (ff, x))))"
            unfolding Cotuple_def tt_ne_ff
            using assms tt_ne_ff ide_coprod\<^sub>o by auto
          hence "Cotuple f g \<circ> In\<^sub>0 ?a ?b =
                (\<lambda>x. if x \<in> Set ?b
                     then Fun g (snd (OUT (Coprod ?a ?b) (IN (Coprod ?a ?b) (ff, x))))
                     else null)"
            unfolding Cotuple_def
            by fastforce
          thus ?thesis by simp
        qed
        also have "... = mkarr ?b ?c (\<lambda>x. if x \<in> Set ?b then Fun g x else null)"
        proof -
          have "\<And>x. x \<in> Set ?b \<Longrightarrow>
                          Fun g (snd (OUT (Coprod ?a ?b) (IN (Coprod ?a ?b) (ff, x)))) = Fun g x"
            using assms ide_coprod\<^sub>o(7) by auto
          thus ?thesis
            by meson
        qed
        also have "... = g"
        proof -
          have "Fun g = (\<lambda>x. if x \<in> Set ?b then Fun g x else null)"
            unfolding Fun_def by meson
          thus ?thesis
            by (metis (no_types, lifting) arr_iff_in_hom assms mkarr_Fun)
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma Fun_cotuple:
    assumes "cospan f g"
    shows "Fun (cotuple f g) =
           (\<lambda>x. if x \<in> Set (coprod\<^sub>o (dom f) (dom g))
                              then if fst (OUT (Coprod (dom f) (dom g)) x) = tt
                                   then Fun f (snd (OUT (Coprod (dom f) (dom g)) x))
                                   else if fst (OUT (Coprod (dom f) (dom g)) x) = ff
                                        then Fun g (snd (OUT (Coprod (dom f) (dom g)) x))
                                        else null
                              else null)"
      using cotuple_def Cotuple_def Fun_mkarr assms cotuple_simps(1) by presburger

    lemma binary_coproduct_in:
    assumes "ide a" and "ide b"
    shows "binary_product (dual_category.comp C) a b (in\<^sub>1 a b) (in\<^sub>0 a b)"
    proof -
      have bij: "bij_betw (OUT (Coprod a b)) (Set (coprod\<^sub>o a b)) (Coprod a b)"
        using assms ide_coprod\<^sub>o(2) ide_dom by blast
      interpret Cop: dual_category C ..
      show ?thesis
      proof
        show "Cop.has_as_binary_product a b (in\<^sub>1 a b) (in\<^sub>0 a b)"
        proof
          show "Cop.span (in\<^sub>1 a b) (in\<^sub>0 a b)"
            using assms(1,2) by force
          show "Cop.cod (in\<^sub>1 a b) = a"
            using assms(1,2) by fastforce
          show "Cop.cod (in\<^sub>0 a b) = b"
            using assms(1,2) by fastforce
          fix c f g
          assume f: "Cop.in_hom f c a" and g: "Cop.in_hom g c b"
          show "\<exists>!h. Cop.in_hom h c (Cop.dom (in\<^sub>1 a b)) \<and> in\<^sub>1 a b \<cdot>\<^sup>o\<^sup>p h = f \<and> in\<^sub>0 a b \<cdot>\<^sup>o\<^sup>p h = g"
          proof
            show "Cop.in_hom (cotuple f g) c (Cop.dom (in\<^sub>1 a b)) \<and>
                    in\<^sub>1 a b \<cdot>\<^sup>o\<^sup>p (cotuple f g) = f \<and> in\<^sub>0 a b \<cdot>\<^sup>o\<^sup>p (cotuple f g) = g"
            proof (intro conjI)
              show "Cop.in_hom (cotuple f g) c (Cop.dom (in\<^sub>1 a b))"
                using assms(1,2) f g by force
              show "in\<^sub>1 a b \<cdot>\<^sup>o\<^sup>p cotuple f g = f"
                using assms(1,2) f g comp_cotuple_in by auto
              show "in\<^sub>0 a b \<cdot>\<^sup>o\<^sup>p cotuple f g = g"
                using assms(1,2) f g comp_cotuple_in
                by (metis Cop.comp_def Cop.hom_char in_homE)
            qed
            show "\<And>h. Cop.in_hom h c (Cop.dom (in\<^sub>1 a b)) \<and> in\<^sub>1 a b \<cdot>\<^sup>o\<^sup>p h = f \<and> in\<^sub>0 a b \<cdot>\<^sup>o\<^sup>p h = g
                         \<Longrightarrow> h = cotuple f g"
            proof -
              fix h
              assume h: "Cop.in_hom h c (Cop.dom (in\<^sub>1 a b)) \<and>
                           in\<^sub>1 a b \<cdot>\<^sup>o\<^sup>p h = f \<and> in\<^sub>0 a b \<cdot>\<^sup>o\<^sup>p h = g"
              show "h = cotuple f g"
              proof (intro arr_eqI [of h])
                show par: "par h (cotuple f g)"
                  using assms(1,2) h by force
                show "Fun h = Fun (cotuple f g)"
                proof
                  fix x
                  show "Fun h x = Fun (cotuple f g) x"
                  proof (cases "x \<in> Set (coprod\<^sub>o a b)")
                    case False
                    show ?thesis
                      using False assms(1,2) h par Fun_cotuple [of f g] Fun_def
                      by (metis (lifting) Cop.cod_char Cop.dom_char Cop.in_homE
                          in_simps(6) mem_Collect_eq)
                    next
                    case True
                    show ?thesis
                    proof -
                      have 2: "OUT (Coprod a b) x \<in> Coprod a b"
                        using True bij bij_betwE by blast
                      hence "fst (OUT (Coprod a b) x) = tt \<or> fst (OUT (Coprod a b) x) = ff"
                        using True bij bij_betwE
                        unfolding coprod\<^sub>o_def
                        by auto
                      moreover have "fst (OUT (Coprod a b) x) = tt \<Longrightarrow> ?thesis"
                      proof -
                        assume 3: "fst (OUT (Coprod a b) x) = tt"
                        have 4: "snd (OUT (Coprod a b) x) \<in> Set a"
                          using True 2 3 tt_ne_ff by fastforce
                        have "Fun (cotuple f g) x = Fun f (snd (OUT (Coprod a b) x))"
                          using assms 2 3 4 coprod\<^sub>o_def
                          apply simp
                          by (metis (lifting) HOL.ext Cop.cod_char Cop.dom_char Cop.in_homE True
                               Fun_cotuple [of f g] arr_dom_iff_arr f g ide_char)
                        also have "... = Fun (h \<cdot> in\<^sub>1 a b) (snd (OUT (Coprod a b) x))"
                          using h by auto
                        also have "... = Fun h (Fun (in\<^sub>1 a b) (snd (OUT (Coprod a b) x)))"
                          using Cop.arrI Fun_comp f h by force
                        also have "... = Fun h (IN (Coprod a b) (tt, snd (OUT (Coprod a b) x)))"
                          using assms 4 Fun_in(1) [of a b] by auto
                        also have "... = Fun h (IN (Coprod a b) (OUT (Coprod a b) x))"
                          by (metis "3" surjective_pairing)
                        also have "... = Fun h x"
                          using assms True ide_coprod\<^sub>o(6) by presburger
                        finally show ?thesis by simp
                      qed
                      moreover have "fst (OUT (Coprod a b) x) = ff \<Longrightarrow> ?thesis"
                      proof -
                        assume 3: "fst (OUT (Coprod a b) x) = ff"
                        have 4: "snd (OUT (Coprod a b) x) \<in> Set b"
                          using True 2 3 tt_ne_ff by fastforce
                        have "Fun (cotuple f g) x = Fun g (snd (OUT (Coprod a b) x))"
                          using True assms f g 2 3 4 tt_ne_ff coprod\<^sub>o_def Fun_cotuple [of f g]
                          apply auto[1]
                          by (metis (lifting) HOL.ext fst_conv in_homE snd_conv)
                        also have "... = Fun (h \<cdot> in\<^sub>0 a b) (snd (OUT (Coprod a b) x))"
                          using h by auto
                        also have "... = Fun h (Fun (in\<^sub>0 a b) (snd (OUT (Coprod a b) x)))"
                          using Cop.arrI Fun_comp g h by force
                        also have "... = Fun h (IN (Coprod a b) (ff, snd (OUT (Coprod a b) x)))"
                          using assms 4 Fun_in(2) [of a b] by auto
                        also have "... = Fun h (IN (Coprod a b) (OUT (Coprod a b) x))"
                          by (metis "3" surjective_pairing)
                        also have "... = Fun h x"
                          using assms True ide_coprod\<^sub>o(6) by presburger
                        finally show ?thesis by simp
                      qed
                      ultimately show ?thesis by blast
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed

    lemma has_binary_coproducts:
    shows "category.has_binary_products (dual_category.comp C)"
    proof -
      interpret Cop: dual_category C ..
      show "Cop.has_binary_products"
      proof (unfold Cop.has_binary_products_def, intro allI impI, elim conjE)
        fix a b
        assume a: "Cop.ide a" and b: "Cop.ide b"
        interpret binary_product Cop.comp a b \<open>in\<^sub>1 a b\<close> \<open>in\<^sub>0 a b\<close>
          using a b binary_coproduct_in [of a b] Cop.ide_char by blast
        show "\<exists>p. Ex (Cop.has_as_binary_product a b p)"
          using has_as_binary_product by blast
      qed
    qed

  end

  subsection "Exported Notions"

  context sets_cat_with_cotupling
  begin

    interpretation Coproducts: coproducts_in_sets_cat ..

    abbreviation in\<^sub>0 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "in\<^sub>0 \<equiv> Coproducts.in\<^sub>0"

    abbreviation in\<^sub>1 :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "in\<^sub>1 \<equiv> Coproducts.in\<^sub>1"

    abbreviation Coprod :: "'U \<Rightarrow> 'U \<Rightarrow> ('U \<times> 'U) set"
    where "Coprod \<equiv> Coproducts.Coprod"

    abbreviation coprod\<^sub>o :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "coprod\<^sub>o \<equiv> Coproducts.coprod\<^sub>o"

    lemma ide_coprod\<^sub>o:
    assumes "ide a" and "ide b"
    shows "ide (coprod\<^sub>o a b)"
      using assms Coproducts.ide_coprod\<^sub>o by blast

    lemma in\<^sub>1_in_hom [intro, simp]:
    assumes "ide a" and "ide b"
    shows "in_hom (in\<^sub>1 a b) a (coprod\<^sub>o a b)"
      using assms Coproducts.in_in_hom by blast

    lemma in\<^sub>0_in_hom [intro, simp]:
    assumes "ide a" and "ide b"
    shows "in_hom (in\<^sub>0 a b) b (coprod\<^sub>o a b)"
      using assms Coproducts.in_in_hom by blast

    lemma in\<^sub>1_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr (in\<^sub>1 a b)" and "dom (in\<^sub>1 a b) = a" and "cod (in\<^sub>1 a b) = coprod\<^sub>o a b"
      using assms Coproducts.in_simps by auto

    lemma in\<^sub>0_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr (in\<^sub>0 a b)" and "dom (in\<^sub>0 a b) = b" and "cod (in\<^sub>0 a b) = coprod\<^sub>o a b"
      using assms Coproducts.in_simps by auto

    lemma bin_coprod_comparison_map_props:
    assumes "ide a" and "ide b"
    shows "bij_betw (OUT (Coprod a b)) (Set (coprod\<^sub>o a b)) (Coprod a b)"
    and "bij_betw (IN (Coprod a b)) (Coprod a b) (Set (coprod\<^sub>o a b))"
    and "\<And>x. x \<in> Set (coprod\<^sub>o a b) \<Longrightarrow> OUT (Coprod a b) x \<in> Coprod a b"
    and "\<And>y. y \<in> Coprod a b \<Longrightarrow> IN (Coprod a b) y \<in> Set (coprod\<^sub>o a b)"
    and "\<And>x. x \<in> Set (coprod\<^sub>o a b) \<Longrightarrow> IN (Coprod a b) (OUT (Coprod a b) x) = x"
    and "\<And>y. y \<in> Coprod a b \<Longrightarrow> OUT (Coprod a b) (IN (Coprod a b) y) = y"
      using assms Coproducts.ide_coprod\<^sub>o by auto

    lemma Fun_in\<^sub>1:
    assumes "ide a" and "ide b"
    shows "Fun (in\<^sub>1 a b) = Coproducts.In\<^sub>1 a b"
      using assms Coproducts.Fun_in(1) by auto[1]

    lemma Fun_in\<^sub>0:
    assumes "ide a" and "ide b"
    shows "Fun (in\<^sub>0 a b) = Coproducts.In\<^sub>0 a b"
      using assms Coproducts.Fun_in(2) by auto[1]

    abbreviation cotuple
    where "cotuple \<equiv> Coproducts.cotuple"

    lemma cotuple_in_hom [intro, simp]:
    assumes "\<guillemotleft>f : a \<rightarrow> c\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>cotuple f g : coprod\<^sub>o a b \<rightarrow> c\<guillemotright>"
      using assms Coproducts.cotuple_in_hom by blast

    lemma cotuple_simps [simp]:
    assumes "cospan f g"
    shows "arr (cotuple f g)"
    and "dom (cotuple f g) = coprod\<^sub>o (dom f) (dom g)"
    and "cod (cotuple f g) = cod f"
      using assms Coproducts.cotuple_simps by auto

    abbreviation Cotuple
    where "Cotuple f g \<equiv> (\<lambda>x. if x \<in> Set (coprod\<^sub>o (dom f) (dom g))
                              then if fst (OUT (Coprod (dom f) (dom g)) x) = tt
                                   then Fun f (snd (OUT (Coprod (dom f) (dom g)) x))
                                   else if fst (OUT (Coprod (dom f) (dom g)) x) = ff
                                        then Fun g (snd (OUT (Coprod (dom f) (dom g)) x))
                                        else null
                              else null)"

    lemma cotuple_eq:
    assumes "\<guillemotleft>f : a \<rightarrow> c\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> c\<guillemotright>"
    shows "cotuple f g = mkarr (coprod\<^sub>o a b) c (Cotuple f g)"
      unfolding Coproducts.cotuple_def Coproducts.Cotuple_def
      using assms by auto

    lemma Fun_cotuple:
    assumes "cospan f g"
    shows "Fun (cotuple f g) = Cotuple f g"
      using assms Coproducts.Fun_cotuple by blast

    lemma binary_coproduct_in:
    assumes "ide a" and "ide b"
    shows "binary_product (dual_category.comp C) a b (in\<^sub>1 a b) (in\<^sub>0 a b)"
      using assms Coproducts.binary_coproduct_in by blast

    lemma has_binary_coproducts:
    shows "category.has_binary_products (dual_category.comp C)"
      using Coproducts.has_binary_coproducts by blast

  end

  section "Small Products"

  text\<open>
    In this section we show that the category of small sets and functions has small products.
    For this we need to assume that smallness is preserved by the formation of function
    spaces.
  \<close>

  locale sets_cat_with_tupling =
    sets_cat sml C +
    tupling sml \<open>Collect arr\<close> null
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    sublocale sets_cat_with_bool
      using embeds_bool
      by unfold_locales auto
    sublocale sets_cat_with_pairing sml C ..
    sublocale sets_cat_with_cotupling ..

  end

  locale small_products_in_sets_cat =
    sets_cat_with_tupling sml C
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    text\<open>
      A product diagram is specified by an extensional function \<open>A\<close> from small index set \<open>I\<close>
      to @{term \<open>Collect ide\<close>}, using @{term null} as the default value.  An element of the product
      is given by an extensional function \<open>F\<close> from \<open>I\<close> to @{term \<open>Collect arr\<close>}, such that
      \<open>F i \<in> Set (A i)\<close> for each \<open>i \<in> I\<close>.
    \<close>

    abbreviation ProdX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> ('a \<Rightarrow> 'U) set"
    where "ProdX I A \<equiv> {F. \<forall>i. i \<in> I \<longrightarrow> F i \<in> Set (A i)} \<inter> {F. \<forall>i. i \<notin> I \<longrightarrow> F i = null}"

    lemma ProdX_empty:
    shows "ProdX {} A = {\<lambda>x. null}"
      by auto

    definition prodX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'U"
    where "prodX I A \<equiv> mkide (ProdX I A)"

    lemma small_function_tuple:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "F \<in> ProdX I A"
    shows "small_function F" and "range F \<subseteq> (\<Union>i\<in>I. Set (A i)) \<union> {null}"
    proof -
      have 1: "small ((\<Union>i\<in>I. Set (A i)) \<union> {null})"
        using assms small_Set by auto
      have 2: "\<And>F v. \<lbrakk>F \<in> ProdX I A; popular_value F v\<rbrakk> \<Longrightarrow> v = null"
      proof -
        fix F v
        assume F: "F \<in> ProdX I A"
        assume v: "popular_value F v"
        have "(\<exists>i. i \<in> I \<and> v \<in> Set (A i)) \<or> v = null"
          using v F popular_value_in_range [of F v] by blast
        hence "v \<noteq> null \<Longrightarrow> {i. F i = v} \<subseteq> I"
          using F by blast
        hence "v \<noteq> null \<Longrightarrow> \<not> popular_value F v"
          using assms(1) smaller_than_small by blast
        thus "v = null"
          using v by blast
      qed
      show 3: "range F \<subseteq> (\<Union>i\<in>I. Set (A i)) \<union> {null}"
        using assms(4) by auto
      show "small_function F"
      proof
        show "small (range F)"
          using 1 3 smaller_than_small by blast
        show "at_most_one_popular_value F"
          using assms(4) 2 Uniq_def
          by (metis (mono_tags, lifting))
      qed
    qed

    lemma small_ProdX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    shows "small (ProdX I A)"
    proof (cases "small (UNIV :: 'U set)")
      case True
      show ?thesis
        using True small_function_tuple smaller_than_small
        by (metis large_univ subset_UNIV)
      next
      case False
      have "\<And>F. F \<in> ProdX I A \<Longrightarrow> SF_Dom F \<subseteq> I"
      proof -
        fix F
        assume F: "F \<in> ProdX I A"
        have "popular_value F null"
        proof -
          have "\<not> small (UNIV - I)"
            using assms False small_union by fastforce
          moreover have "UNIV - I \<subseteq> {i. F i = null}"
            using F by blast
          ultimately show ?thesis
            using smaller_than_small by blast
        qed
        thus "SF_Dom F \<subseteq> I"
          using F by auto
      qed
      hence "ProdX I A \<subseteq> {f. small_function f \<and> SF_Dom f \<subseteq> I \<and>
                             range f \<subseteq> (\<Union>i\<in>I. Set (A i)) \<union> {null}}"
        using assms small_function_tuple by blast
      moreover have 1: "small ((\<Union>i\<in>I. Set (A i)) \<union> {null})"
        using assms small_Set by auto
      ultimately show ?thesis
        using assms(1) small_Set small_funcset [of I "(\<Union>i\<in>I. Set (A i)) \<union> {null}"]
              smaller_than_small
        by blast
    qed

    lemma embeds_ProdX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    shows "embeds (ProdX I A)"
    proof -
      obtain \<iota> where \<iota>: "is_embedding_of \<iota> SEF"
        using embeds_SEF by blast
      have "ProdX I A \<subseteq> SEF"
        using assms EF_def small_function_tuple by auto
      hence "is_embedding_of \<iota> (ProdX I A)"
        using \<iota> by (meson dual_order.trans image_mono inj_on_subset)
      thus ?thesis by blast
    qed

    lemma ide_prodX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    shows "ide (prodX I A)"
    and "bij_betw (OUT (ProdX I A)) (Set (prodX I A)) (ProdX I A)"
    and "bij_betw (IN (ProdX I A)) (ProdX I A) (Set (prodX I A))"
    and "\<And>x. x \<in> Set (prodX I A) \<Longrightarrow> OUT (ProdX I A) x \<in> ProdX I A"
    and "\<And>y. y \<in> ProdX I A \<Longrightarrow> IN (ProdX I A) y \<in> Set (prodX I A)"
    and "\<And>x. x \<in> Set (prodX I A) \<Longrightarrow> IN (ProdX I A) (OUT (ProdX I A) x) = x"
    and "\<And>y. y \<in> ProdX I A \<Longrightarrow> OUT (ProdX I A) (IN (ProdX I A) y) = y"
    proof -
      have 2: "small ((\<Union>i\<in>I. Set (A i)) \<union> {null})"
        using assms(1-2) small_Set by auto
      have *: "\<And>F. F \<in> ProdX I A \<Longrightarrow> small_function F \<and> range F \<subseteq> (\<Union>i\<in>I. Set (A i)) \<union> {null}"
        using assms small_function_tuple by blast
      show "ide (prodX I A)"
        unfolding prodX_def
        using assms small_ProdX embeds_ProdX by auto
      show 1: "bij_betw (OUT (ProdX I A)) (Set (prodX I A)) (ProdX I A)"
        unfolding prodX_def
        using assms small_ProdX embeds_ProdX bij_OUT [of "ProdX I A"] by fastforce
      show 2: "bij_betw (IN (ProdX I A)) (ProdX I A) (Set (prodX I A))"
        unfolding prodX_def
        using assms small_ProdX embeds_ProdX bij_IN [of "ProdX I A"] by fastforce
      show "\<And>x. x \<in> Set (prodX I A) \<Longrightarrow> OUT (ProdX I A) x \<in> ProdX I A"
        using 1 bij_betwE by blast
      show "\<And>y. y \<in> ProdX I A \<Longrightarrow> IN (ProdX I A) y \<in> Set (prodX I A)"
        using 2 bij_betwE by blast
      show "\<And>x. x \<in> Set (prodX I A) \<Longrightarrow> IN (ProdX I A) (OUT (ProdX I A) x) = x"
      proof -
        fix x
        assume x: "x \<in> Set (prodX I A)"
        show "IN (ProdX I A) (OUT (ProdX I A) x) = x"
        proof -
          have "x = inv_into (Set (prodX I A)) (OUT (ProdX I A)) (OUT (ProdX I A) x)"
            using x 1
                  bij_betw_inv_into_left
                    [of "OUT (ProdX I A)" "Set (prodX I A)" "ProdX I A"]
            by auto
          thus ?thesis
            by (simp add: prodX_def)
        qed
      qed
      show "\<And>y. y \<in> ProdX I A \<Longrightarrow> OUT (ProdX I A) (IN (ProdX I A) y) = y"
      proof -
        fix y
        assume y: "y \<in> ProdX I A"
        show "OUT (ProdX I A) (IN (ProdX I A) y) = y"
          using assms(1,2,3) y OUT_IN [of "ProdX I A" y] small_ProdX embeds_ProdX [of I A]
          by blast
      qed
    qed

    lemma terminal_prodX_empty:
    shows "terminal (prodX {} (A :: 'U \<Rightarrow> 'U))"
    proof -
      let ?I = "{} :: 'U set"
      have 1: "{F. \<forall>i. i \<notin> ?I \<longrightarrow> F i = null} = {\<lambda>i. null}"
         by auto
      have "\<exists>!x. x \<in> Set (prodX ?I A)"
      proof -
        have "eqpoll (Set (prodX ?I A)) {F. \<forall>i. i \<notin> ?I \<longrightarrow> F i = null}"
        proof -
          have "small {F. \<forall>i. i \<notin> ?I \<longrightarrow> F i = null}"
            using 1 small_finite by force
          moreover have "\<exists>\<iota>. is_embedding_of \<iota> {F. \<forall>i :: 'U. F i = null}"
          proof -
            have "is_embedding_of (\<lambda>_. \<one>\<^sup>?) {\<lambda>i. null}"
              using ide_char ide_some_terminal by blast
            thus ?thesis
              using 1 by auto
          qed
          ultimately show ?thesis
            unfolding prodX_def
            using 1 bij_OUT [of "{F. \<forall>i. i \<notin> ?I \<longrightarrow> F i = null}"] eqpoll_def
            by auto blast
        qed
        moreover have "\<exists>!x. x \<in> {F. \<forall>i. i \<notin> ?I \<longrightarrow> F i = null}"
          using 1 by auto
        ultimately show ?thesis
          by (metis (no_types, lifting) eqpoll_iff_bijections)
      qed
      thus ?thesis
        using terminal_char ide_prodX(1)
        by (metis Pi_I empty_subsetI ex_in_conv small_Set smaller_than_small
          terminal_some_terminal)
    qed

    abbreviation PrX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'a \<Rightarrow> 'U \<Rightarrow> 'U"
    where "PrX I A i \<equiv> \<lambda>x. if x \<in> Set (prodX I A) then OUT (ProdX I A) x i else null"

    definition prX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'a \<Rightarrow> 'U"
    where "prX I A i \<equiv> mkarr (prodX I A) (A i) (PrX I A i)"

    lemma prX_in_hom [intro, simp]:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "i \<in> I"
    shows "in_hom (prX I A i) (prodX I A) (A i)"
    proof (unfold prX_def, intro mkarr_in_hom)
      show "ide (prodX I A)"
        using assms ide_prodX by blast
      show "ide (A i)"
        using assms by blast
      show "PrX I A i \<in> Hom (prodX I A) (A i)"
      proof
        show "PrX I A i \<in> Set (prodX I A) \<rightarrow> Set (A i)"
        proof
          fix x
          assume x: "x \<in> Set (prodX I A)"
          have "OUT (ProdX I A) x \<in> ProdX I A"
            using assms(1,2,3) x ide_prodX(2)
              bij_betwE [of "OUT (ProdX I A)" "Set (prodX I A)" "ProdX I A"]
            by blast
          thus "PrX I A i x \<in> Set (A i)"
            using assms x by force
        qed
        show "PrX I A i \<in> {F. \<forall>x. x \<notin> Set (prodX I A) \<longrightarrow> F x = null}"
          by simp
      qed
    qed

    lemma prX_simps [simp]:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "i \<in> I"
    shows "arr (prX I A i)" and "dom (prX I A i) = prodX I A" and "cod (prX I A i) = A i"
      using assms prX_in_hom by blast+
 
    lemma Fun_prX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "i \<in> I"
    shows "Fun (prX I A i) = PrX I A i"
    proof -
      have "arr (prX I A i)"
        using assms by auto
      thus ?thesis
        using assms Fun_mkarr [of "prodX I A" "A i" "PrX I A i"] prX_def by metis
    qed

    definition TupleX :: "'a set \<Rightarrow> 'U \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'U \<Rightarrow> 'U"
    where "TupleX I c A F \<equiv> (\<lambda>x. if x \<in> Set c then IN (ProdX I A) (\<lambda>i. Fun (F i) x) else null)"

    lemma TupleX_in_Hom:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : c \<rightarrow> A i\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null"
    shows "TupleX I c A F \<in> Hom c (prodX I A)"
    proof
      show "TupleX I c A F \<in> {F. \<forall>x. x \<notin> Set c \<longrightarrow> F x = null}"
        unfolding TupleX_def
        using assms by auto
      show "TupleX I c A F \<in> Set c \<rightarrow> Set (prodX I A)"
      proof (cases "I = {}")
        case False
        show ?thesis
        proof
          fix x
          assume x: "x \<in> Set c"
          have "\<forall>i. i \<in> I \<longrightarrow> x \<in> Set (dom (F i))"
            using False assms x by blast
          moreover have "(\<lambda>i. Fun (F i) x) \<in> ProdX I A"
            using False assms x Fun_def by auto
          ultimately show "TupleX I c A F x \<in> Set (prodX I A)"
            unfolding TupleX_def
            using False assms x ide_prodX(3) [of I A] bij_betw_apply
            by (metis (mono_tags, lifting))
        qed
        next
        case True
        show ?thesis
          unfolding TupleX_def
          using True assms ide_prodX(3) bij_betw_apply Fun_def
          by auto[1] fastforce
      qed
    qed

    definition tupleX :: "'a set \<Rightarrow> 'U \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'U"
    where "tupleX I c A F \<equiv> mkarr c (prodX I A) (TupleX I c A F)"

    lemma tupleX_in_hom [intro, simp]:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : c \<rightarrow> A i\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null" and "ide c"
    shows "\<guillemotleft>tupleX I c A F : c \<rightarrow> prodX I A\<guillemotright>"
      unfolding tupleX_def
      using assms ide_prodX TupleX_in_Hom
      by (intro mkarr_in_hom) auto

    lemma tupleX_simps [simp]:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : c \<rightarrow> A i\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null" and "ide c"
    shows "arr (tupleX I c A F)"
    and "dom (tupleX I c A F) = c"
    and "cod (tupleX I c A F) = prodX I A"
      using assms in_homE tupleX_in_hom by metis+

    lemma comp_prX_tupleX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : c \<rightarrow> A i\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null"
    shows "i \<in> I \<Longrightarrow> C (prX I A i) (tupleX I c A F) = F i"
    proof -
      assume i: "i \<in> I"
      have I: "I \<noteq> {}"
        using i by blast
      hence c: "ide c"
        using assms(4) ide_dom by blast
      show "C (prX I A i) (tupleX I c A F) = F i"
      proof -
        have "C (prX I A i) (tupleX I c A F) =
              mkarr (prodX I A) (A i) (PrX I A i) \<cdot> mkarr c (prodX I A) (TupleX I c A F)"
          unfolding prX_def tupleX_def TupleX_def
          using assms i I comp_mkarr by simp
        also have "... = mkarr c (A i) (PrX I A i \<circ> TupleX I c A F)"
        proof -
          have "\<guillemotleft>mkarr c (prodX I A) (TupleX I c A F) : c \<rightarrow> prodX I A\<guillemotright>"
            by (metis assms c tupleX_def tupleX_in_hom)
          moreover have "\<guillemotleft>mkarr (prodX I A) (A i) (PrX I A i) : prodX I A \<rightarrow> A i\<guillemotright>"
          proof -
            have "\<guillemotleft>prX I A i : prodX I A \<rightarrow> A i\<guillemotright>"
              using assms(1-3) i by blast
            thus ?thesis
              by (simp add: prX_def)
          qed
          ultimately show ?thesis
            using assms i comp_mkarr [of c "prodX I A" "TupleX I c A F" "A i" "PrX I A i"]
            by auto
        qed
        also have "... = mkarr c (A i)
                           (\<lambda>x. if TupleX I c A F x \<in> Set (prodX I A)
                                then OUT (ProdX I A) (TupleX I c A F x) i
                                else null)"
          using I by (simp add: comp_def)
        also have "... = mkarr c (A i)
                           (\<lambda>x. if x \<in> Set c then OUT (ProdX I A) (TupleX I c A F x) i else null)"
        proof -
          have "(\<lambda>x. if TupleX I c A F x \<in> Set (prodX I A)
                     then OUT (ProdX I A) (TupleX I c A F x) i
                     else null) =
                (\<lambda>x. if x \<in> Set c then OUT (ProdX I A) (TupleX I c A F x) i else null)"
          proof
            fix x
            show "(if TupleX I c A F x \<in> Set (prodX I A)
                   then OUT (ProdX I A) (TupleX I c A F x) i 
                   else null) =
                  (if x \<in> Set c then OUT (ProdX I A) (TupleX I c A F x) i else null)"
              using assms TupleX_in_Hom
              by auto blast
          qed
          thus ?thesis by simp
        qed
        also have "... = mkarr c (A i)
                           (\<lambda>x. if x \<in> Set c
                                then OUT (ProdX I A) (IN (ProdX I A) (\<lambda>i. Fun (F i) x)) i
                                else null)"
        proof -
          have "(\<lambda>x. if x \<in> Set c then OUT (ProdX I A) (TupleX I c A F x) i else null) =
                (\<lambda>x. if x \<in> Set c
                     then OUT (ProdX I A) (IN (ProdX I A) (\<lambda>i. Fun (F i) x)) i
                     else null)"
          proof
            fix x
            show "(if x \<in> Set c then OUT (ProdX I A) (TupleX I c A F x) i else null) =
                  (if x \<in> Set c
                   then OUT (ProdX I A) (IN (ProdX I A) (\<lambda>i. Fun (F i) x)) i
                   else null)"
              unfolding TupleX_def by argo
          qed
          thus ?thesis by simp
        qed
        also have "... = mkarr c (A i) (\<lambda>x. if x \<in> Set c then Fun (F i) x else null)"
        proof -
          have "(\<lambda>x. if x \<in> Set c
                     then OUT (ProdX I A) (IN (ProdX I A) (\<lambda>i. Fun (F i) x)) i
                     else null) =
                (\<lambda>x. if x \<in> Set c then Fun (F i) x else null)"
          proof
            fix x
            show "(if x \<in> Set c
                   then OUT (ProdX I A) (IN (ProdX I A) (\<lambda>i. Fun (F i) x)) i
                   else null) =
                  (if x \<in> Set c then Fun (F i) x else null)"
            proof (cases "x \<in> Set c")
              case False
              show ?thesis
                using False by simp
              next
              case True
              show ?thesis
              proof -
                have "(\<lambda>i. Fun (F i) x) \<in> ProdX I A"
                  using assms(4-5) True Fun_def by auto
                hence "OUT (ProdX I A) (IN (ProdX I A) (\<lambda>i. Fun (F i) x)) i = Fun (F i) x"
                  using assms OUT_IN [of "ProdX I A" "\<lambda>i. Fun (F i) x"]
                        small_ProdX embeds_ProdX
                  by presburger
                thus ?thesis by simp
              qed
            qed
          qed
          thus ?thesis by simp
        qed
        also have "... = F i"
        proof -
          have "Fun (F i) = (\<lambda>x. if x \<in> Set c then Fun (F i) x else null)"
            using assms(4) i Fun_def by fastforce
          thus ?thesis
            using assms(4) i mkarr_Fun by force
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma Fun_tupleX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : c \<rightarrow> A i\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null" and "ide c"
    shows "Fun (tupleX I c A F) =
           (\<lambda>x. if x \<in> Set c then IN (ProdX I A) (\<lambda>i. Fun (F i) x) else null)"
    proof -
      have "Fun (tupleX I c A F) =
            (\<lambda>x. if x \<in> Set c then mkarr c (prodX I A) (TupleX I c A F) \<cdot> x else null)"
        unfolding tupleX_def Fun_def
        apply simp
        by (metis ext mem_Collect_eq dom_mkarr seqE)
      also have "... = (\<lambda>x. if x \<in> Set c then TupleX I c A F x else null)"
        using assms app_mkarr
        by (metis (no_types, lifting) CollectD tupleX_def tupleX_in_hom)
      also have "... = (\<lambda>x. if x \<in> Set c then IN (ProdX I A) (\<lambda>i. Fun (F i) x) else null)"
        unfolding TupleX_def by auto
      finally show ?thesis by blast
    qed

    lemma product_cone_prodX:
    assumes "discrete_diagram J C D" and "Collect (partial_composition.arr J) = I"
    and "small I" and "I \<subseteq> Collect arr"
    shows "has_as_product J D (prodX I D)"
    and "product_cone J C D (prodX I D) (prX I D)"
    proof -
      interpret J: category J
        using assms(1) discrete_diagram_def by blast
      interpret D: discrete_diagram J C D
        using assms(1) by blast
      let ?\<pi> = "prX I D"
      let ?a = "prodX I D"
      interpret A: constant_functor J C ?a
        using assms ide_prodX
        apply unfold_locales
        using D.is_discrete by auto
      interpret \<pi>: natural_transformation J C A.map D ?\<pi>
      proof
        fix j
        show "\<not> J.arr j \<Longrightarrow> prX I D j = null"
          by (metis (no_types, lifting) D.as_nat_trans.extensionality ideD(1) mkarr_def
              not_arr_null prX_def)
        assume j: "J.arr j"
        show 1: "arr (prX I D j)"
          using D.is_discrete assms j by force
        show "D j \<cdot> prX I D (J.dom j) = prX I D j"
          by (metis (lifting) 1 D.is_discrete J.ideD(2) comp_cod_arr cod_mkarr j prX_def)
        show "prX I D (J.cod j) \<cdot> A.map j = prX I D j"
          by (metis (lifting) 1 A.map_simp D.is_discrete J.ide_char comp_arr_dom j
              dom_mkarr prX_def)
      qed
      show "product_cone J C D ?a ?\<pi>"
      proof
        fix a' \<chi>'
        assume \<chi>': "D.cone a' \<chi>'"
        interpret \<chi>': cone J C D a' \<chi>'
          using \<chi>' by blast
        show "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> prodX I D\<guillemotright> \<and> D.cones_map f (prX I D) = \<chi>'"
        proof -
          let ?f = "tupleX I a' D \<chi>'"
          have f: "\<guillemotleft>?f : a' \<rightarrow> prodX I D\<guillemotright>"
            using assms tupleX_in_hom
            by (metis D.is_discrete D.preserves_ide J.ide_char Pi_I'
              \<chi>'.component_in_hom \<chi>'.extensionality \<chi>'.ide_apex mem_Collect_eq)
          moreover have "D.cones_map ?f (prX I D) = \<chi>'"
          proof
            fix i
            show "D.cones_map ?f (prX I D) i = \<chi>' i"
            proof -
              have "J.arr i \<Longrightarrow> prX I D i \<cdot> ?f = \<chi>' i"
                using assms comp_prX_tupleX [of I D \<chi>' a' i]
                by (metis D.is_discrete D.preserves_ide J.ide_char Pi_I'
                   \<chi>'.component_in_hom \<chi>'.extensionality mem_Collect_eq)
              moreover have "\<not> J.arr i \<Longrightarrow> null = \<chi>' i"
                using \<chi>'.extensionality by auto
              moreover have "D.cone (cod ?f) (prX I D)"
              proof -
                have "D.cone (prodX I D) (prX I D)" ..
                moreover have "cod ?f = prodX I D"
                  using f by blast
                ultimately show ?thesis by auto
              qed
              ultimately show ?thesis
                using assms \<chi>'.cone_axioms by auto
            qed
          qed
          moreover have "\<And>f'. \<lbrakk>\<guillemotleft>f' : a' \<rightarrow> prodX I D\<guillemotright>; D.cones_map f' (prX I D) = \<chi>'\<rbrakk>
                                 \<Longrightarrow> f' = ?f"
          proof -
            fix f'
            assume f': "\<guillemotleft>f' : a' \<rightarrow> prodX I D\<guillemotright>"
            assume 1: "D.cones_map f' (prX I D) = \<chi>'"
            show "f' = ?f"
            proof (intro arr_eqI [of f'])
              show par: "par f' ?f"
                using f f' by fastforce
              show "Fun f' = Fun (tupleX I a' D \<chi>')"
              proof
                fix x
                show "Fun f' x = Fun (tupleX I a' D \<chi>') x"
                proof (cases "x \<in> Set a'")
                  case False
                  show ?thesis
                    using False par f' Fun_def by auto
                  next
                  case True
                  have 2: "D.cone (cod f') (prX I D)"
                  by (metis A.constant_functor_axioms Limit.cone_def
                    \<pi>.natural_transformation_axioms \<chi>' f' in_homE)
                  have "Fun (tupleX I a' D \<chi>') x = IN (ProdX I D) (\<lambda>i. Fun (\<chi>' i) x)"
                  proof -
                    have "dom (tupleX I a' D \<chi>') = a'"
                      using f by auto
                    have *: "(\<lambda>x. if \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> a'\<guillemotright> then tupleX I a' D \<chi>' \<cdot> x else null) =
                             (\<lambda>x. if \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> a'\<guillemotright> then IN (ProdX I D) (\<lambda>i. Fun (\<chi>' i) x) else null)"
                    proof -
                      have "D \<in> I \<rightarrow> Collect ide"
                        using assms(2) D.is_discrete by force
                      moreover have "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>\<chi>' i : a' \<rightarrow> D i\<guillemotright>"
                        using assms(2) D.is_discrete \<chi>'.component_in_hom by fastforce
                      moreover have "\<And>i. i \<notin> I \<Longrightarrow> \<chi>' i = null"
                        using assms(2) \<chi>'.extensionality by blast
                      moreover have "ide a'"
                        using \<chi>'.ide_apex by auto
                      ultimately show ?thesis
                        using assms f Fun_tupleX [of I D \<chi>' a'] Fun_arr by force
                    qed
                    have "Fun (tupleX I a' D \<chi>') x = tupleX I a' D \<chi>' \<cdot> x"
                      using True \<open>dom (tupleX I a' D \<chi>') = a'\<close> Fun_def by presburger
                    also have "... = (\<lambda>x. if \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> a'\<guillemotright> then tupleX I a' D \<chi>' \<cdot> x else null) x"
                      using True by simp
                    also have "... = (\<lambda>x. if \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> a'\<guillemotright>
                                          then IN (ProdX I D) (\<lambda>i. Fun (\<chi>' i) x)
                                          else null) x"
                      using * by meson  (* TODO: Is \<beta>-reduction preventing an easy proof here? *)
                    also have "... = IN (ProdX I D) (\<lambda>i. Fun (\<chi>' i) x)"
                      using True by simp
                    finally show ?thesis by blast
                  qed
                  also have "... = IN (ProdX I D) (\<lambda>i. \<chi>' i \<cdot> x)"
                    unfolding Fun_def
                    by (metis J.dom_cod True \<chi>'.A.map_simp \<chi>'.cod_determines_component
                      \<chi>'.preserves_dom \<chi>'.preserves_reflects_arr local.ext seqE)
                  also have "... = IN (ProdX I D) (\<lambda>i. D.cones_map f' (prX I D) i \<cdot> x)"
                    using 1 by simp
                  also have "... = IN (ProdX I D) (\<lambda>i. (if J.arr i then prX I D i \<cdot> f' else null) \<cdot> x)"
                    using 2 by simp
                  also have "... = IN (ProdX I D) (\<lambda>i. if J.arr i then prX I D i \<cdot> (f' \<cdot> x) else null)"
                  proof -
                    have "(\<lambda>i. (if J.arr i then prX I D i \<cdot> f' else null) \<cdot> x) =
                          (\<lambda>i. if J.arr i then prX I D i \<cdot> (f' \<cdot> x) else null)"
                    proof
                      fix i
                      show "(if J.arr i then prX I D i \<cdot> f' else null) \<cdot> x =
                            (if J.arr i then prX I D i \<cdot> (f' \<cdot> x) else null)"
                        using comp_assoc by auto
                    qed
                    thus ?thesis by simp
                  qed
                  also have "... = IN (ProdX I D)
                                     (\<lambda>i. if J.arr i then prX I D i \<cdot> (Fun f' x) else null)"
                    unfolding Fun_def
                    using True f' by auto
                  also have "... = IN (ProdX I D)
                                     (\<lambda>i. if J.arr i then Fun (prX I D i) (Fun f' x) else null)"
                  proof -
                    have "(\<lambda>i. if J.arr i then prX I D i \<cdot> (Fun f' x) else null) =
                          (\<lambda>i. if J.arr i then Fun (prX I D i) (Fun f' x) else null)"
                    proof
                      fix i
                      show "(if J.arr i then prX I D i \<cdot> (Fun f' x) else null) =
                            (if J.arr i then Fun (prX I D i) (Fun f' x) else null)"
                        using f' Fun_def by fastforce
                    qed
                    thus ?thesis by simp
                  qed
                  also have "... = IN (ProdX I D)
                                     (\<lambda>i. if J.arr i
                                          then (if Fun f' x \<in> Set (prodX I D)
                                                then OUT (ProdX I D) (Fun f' x) i else null)
                                          else null)"
                  proof -
                    have "\<And>i. J.arr i \<Longrightarrow> Fun (prX I D i) =
                                           (\<lambda>x. if x \<in> Set (prodX I D)
                                                then OUT (ProdX I D) x i else null)"
                      using assms Fun_prX D.is_discrete by force
                    hence "(\<lambda>i. if J.arr i then Fun (prX I D i) (Fun f' x) else null) =
                          (\<lambda>i. if J.arr i
                               then (\<lambda>x. if x \<in> Set (prodX I D)
                                         then OUT (ProdX I D) x i else null)
                                    (Fun f' x)
                               else null)"
                      by auto
                    thus ?thesis by simp
                  qed
                  also have "... = IN (ProdX I D)
                                     (\<lambda>i. if J.arr i then OUT (ProdX I D) (Fun f' x) i else null)"
                  proof -
                    have "(\<lambda>i. if J.arr i
                               then (\<lambda>x. if x \<in> Set (prodX I D)
                                         then OUT (ProdX I D) x i else null)
                                    (Fun f' x)
                               else null) =
                          (\<lambda>i. if J.arr i then OUT (ProdX I D) (Fun f' x) i else null)"
                      using True f' Fun_def Fun_arr comp_in_homI by auto
                    thus ?thesis by simp
                  qed
                  also have "... = IN (ProdX I D) (OUT (ProdX I D) (Fun f' x))"
                  proof -
                    have "(\<lambda>i. if J.arr i then OUT (ProdX I D) (Fun f' x) i else null) =
                          OUT (ProdX I D) (Fun f' x)"
                    proof
                      fix i
                      show "(if J.arr i then OUT (ProdX I D) (Fun f' x) i else null) =
                            OUT (ProdX I D) (Fun f' x) i"
                      proof (cases "J.arr i")
                        case True
                        show ?thesis
                          using True by simp
                        next
                        case False
                        have 1: "Fun f' x \<in> Set (prodX I D)"
                          using True f' Fun_def by auto
                        moreover have "small (ProdX I D)" and "embeds (ProdX I D)"
                          using assms small_ProdX [of I D] embeds_ProdX [of I D]
                                D.is_discrete D.preserves_ide
                          by auto
                        moreover have "\<guillemotleft>Fun f' x : \<one>\<^sup>? \<rightarrow> mkide (ProdX I D)\<guillemotright>"
                          using True f'
                          by (metis 1 prodX_def mem_Collect_eq)
                        ultimately have "OUT (ProdX I D) (Fun f' x) \<in> ProdX I D"
                          using OUT_elem_of [of "ProdX I D" "Fun f' x"] Fun_in_Hom
                          by fastforce
                        thus ?thesis
                          using False assms(2) by fastforce
                      qed
                    qed
                    thus ?thesis by simp
                  qed
                  also have "... = Fun f' x"
                  proof -
                    have "small (ProdX I D)"
                      using assms small_ProdX D.is_discrete by fastforce
                    moreover have "\<exists>\<iota>. is_embedding_of \<iota> (ProdX I D)"
                      using assms embeds_ProdX [of I D] D.is_discrete by auto
                    moreover have "Fun f' x \<in> Set (mkide (ProdX I D))"
                    proof -
                      have "Fun f' x \<in> Set (prodX I D)"
                        using Fun_in_Hom True f' by blast
                      thus ?thesis
                        by (simp add: prodX_def)
                    qed
                    ultimately show ?thesis
                      using assms IN_OUT [of "ProdX I D" "Fun f' x"] by blast
                  qed
                  finally show ?thesis by simp
                qed
              qed
            qed
          qed
          ultimately show ?thesis by blast
        qed
      qed
      thus "has_as_product J D (prodX I D)"
        using has_as_product_def by blast
    qed

    lemma has_small_products:
    assumes "small I" and "I \<subseteq> Collect arr"
    shows "has_products I"
    proof (unfold has_products_def, intro conjI)
      show "I \<noteq> UNIV"
        using assms not_arr_null by blast
      show "\<forall>J D. discrete_diagram J (\<cdot>) D \<and> Collect (partial_composition.arr J) = I
                    \<longrightarrow> (\<exists>a. has_as_product J D a)"
        using assms product_cone_prodX by blast
    qed

  end

  subsection "Exported Notions"

  context sets_cat_with_tupling
  begin

    interpretation Products: small_products_in_sets_cat ..

    abbreviation ProdX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> ('a \<Rightarrow> 'U) set"
    where "ProdX \<equiv> Products.ProdX"

    abbreviation prodX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'U"
    where "prodX \<equiv> Products.prodX"

    abbreviation prX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'a \<Rightarrow> 'U"
    where "prX \<equiv> Products.prX"

    abbreviation tupleX :: "'a set \<Rightarrow> 'U \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'U"
    where "tupleX \<equiv> Products.tupleX"

    lemma small_prod_comparison_map_props:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    shows "OUT (ProdX I A) \<in> Set (prodX I A) \<rightarrow> ProdX I A"
    and "IN (ProdX I A) \<in> ProdX I A \<rightarrow> Set (prodX I A)"
    and "\<And>x. x \<in> Set (prodX I A) \<Longrightarrow> IN (ProdX I A) (OUT (ProdX I A) x) = x"
    and "\<And>y. y \<in> ProdX I A \<Longrightarrow> OUT (ProdX I A) (IN (ProdX I A) y) = y"
    and "bij_betw (OUT (ProdX I A)) (Set (prodX I A)) (ProdX I A)"
    and "bij_betw (IN (ProdX I A)) (ProdX I A) (Set (prodX I A))"
    proof -
      show "OUT (ProdX I A) \<in> Set (prodX I A) \<rightarrow> ProdX I A"
      proof -
        have "bij_betw
                (OUT ({f. \<forall>a. a \<in> I \<longrightarrow> f a \<in> Set (A a)} \<inter> {f. \<forall>a. a \<notin> I \<longrightarrow> f a = null}))
                (Set (prodX I A))
                ({f. \<forall>a. a \<in> I \<longrightarrow> f a \<in> Set (A a)} \<inter> {f. \<forall>a. a \<notin> I \<longrightarrow> f a = null})"
          using Products.ide_prodX(2) assms(1-3) by blast
        then show ?thesis
          by (simp add: bij_betw_imp_funcset)
      qed
      show "IN (ProdX I A) \<in> ProdX I A \<rightarrow> Set (prodX I A)"
      proof -
        have "bij_betw
                (OUT ({f. \<forall>a. a \<in> I \<longrightarrow> f a \<in> Set (A a)} \<inter> {f. \<forall>a. a \<notin> I \<longrightarrow> f a = null}))
                (Set (prodX I A))
                ({f. \<forall>a. a \<in> I \<longrightarrow> f a \<in> Set (A a)} \<inter> {f. \<forall>a. a \<notin> I \<longrightarrow> f a = null})"
          using Products.ide_prodX(2) assms(1-3) by blast
        then show ?thesis
          by (simp add: Products.prodX_def bij_betw_imp_funcset bij_betw_inv_into)
      qed
      show "\<And>x. x \<in> Set (prodX I A) \<Longrightarrow> IN (ProdX I A) (OUT (ProdX I A) x) = x"
        using assms IN_OUT [of "ProdX I A"] Products.small_ProdX Products.embeds_ProdX
        by (simp add: Products.prodX_def)
      show "\<And>y. y \<in> ProdX I A \<Longrightarrow> OUT (ProdX I A) (IN (ProdX I A) y) = y"
        using assms OUT_IN [of "ProdX I A"] Products.small_ProdX Products.embeds_ProdX
        by (simp add: Products.prodX_def)
      show "bij_betw (OUT (ProdX I A)) (Set (prodX I A)) (ProdX I A)"
        using assms Products.ide_prodX by fastforce
      show "bij_betw (IN (ProdX I A)) (ProdX I A) (Set (prodX I A))"
        using assms Products.ide_prodX by fastforce
    qed

    lemma Fun_prX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "i \<in> I"
    shows "Fun (prX I A i) = Products.PrX I A i"
      using assms Products.Fun_prX by auto

    lemma Fun_tupleX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : c \<rightarrow> A i\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null" and "ide c"
    shows "Fun (tupleX I c A F) =
           (\<lambda>x. if x \<in> Set c then IN (Products.ProdX I A) (\<lambda>i. Fun (F i) x) else null)"
      using assms Products.Fun_tupleX by auto

    lemma product_cone:
    assumes "discrete_diagram J C D" and "Collect (partial_composition.arr J) = I"
    and "small I" and "I \<subseteq> Collect arr"
    shows "has_as_product J D (prodX I D)"
    and "product_cone J C D (prodX I D) (prX I D)"
      using assms Products.product_cone_prodX by auto

    lemma has_small_products:
    assumes "small I" and "I \<subseteq> Collect arr"
    shows "has_products I"
      using assms Products.has_small_products by blast

    text\<open>
      Clearly it is not required that the index set \<open>I\<close> be actually a subset of
      @{term \<open>Collect arr\<close>} but rather only that it be embedded in it.  So we are free to form
      products indexed by small sets at arbitrary types, as long as @{term \<open>Collect arr\<close>}
      is large enough to embed them.  We do have to satisfy the technical requirement that the
      index set \<open>I\<close> not exhaust the elements at its type, which we introduced in the
      definition of @{term has_products} as a convenience to avoid the use of coercion maps.
    \<close>

    lemma has_small_products':
    assumes "small I" and "embeds I" and "I \<noteq> UNIV"
    shows "has_products I"
    proof -
      obtain I' where I': "I' \<subseteq> Collect arr \<and> I \<approx> I'"
        using assms inj_on_image_eqpoll_1 by auto
      have "has_products I'"
        using assms I'
        by (meson eqpoll_sym eqpoll_trans has_small_products small_def)
      thus ?thesis
        using assms(3) I' has_products_preserved_by_bijection
        by (metis eqpoll_def eqpoll_sym)
    qed

  end

  section "Small Coproducts"

  text\<open>
    In this section we show that the category of small sets and functions has small coproducts.
    For this we need to assume the existence of a pairing function and also that the notion
    of smallness is respected by small sums.
  \<close>

  locale small_coproducts_in_sets_cat =
    sets_cat_with_cotupling sml C
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    text\<open>
      The global elements of a coproduct \<open>CoprodX I A\<close> are in bijection with
      \<open>\<Union>i\<in>I. {i} \<times> Set (A i)\<close>.
    \<close>

    abbreviation CoprodX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> ('a \<times> 'U) set"
    where "CoprodX I A \<equiv> \<Union>i\<in>I. {i} \<times> Set (A i)"

    definition coprodX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'U"
    where "coprodX I A \<equiv> mkide (CoprodX I A)"

    lemma small_CoprodX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    shows "small (CoprodX I A)"
      using assms small_Set small_Union
      by (simp add: Pi_iff smaller_than_small)

    lemma embeds_CoprodX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    shows "embeds (CoprodX I A)"
    proof
      let ?\<iota> = "(\<lambda>x. pair (fst x) (snd x))"
      show "is_embedding_of ?\<iota> (CoprodX I A)"
      proof
        show "?\<iota> ` CoprodX I A \<subseteq> Collect arr"
          using arrI assms(3) some_pairing_in_univ by auto
        show "inj_on ?\<iota> (CoprodX I A)"
        proof -
          have "inj_on ?\<iota> (Collect arr \<times> Collect arr)"
            using some_pairing_is_embedding by auto
          moreover have "CoprodX I A \<subseteq> Collect arr \<times> Collect arr"
            using arrI assms(3) by auto
          ultimately show ?thesis
            by (meson inj_on_subset)
        qed
      qed
    qed

    lemma ide_coprodX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    shows "ide (coprodX I A)"
    and "bij_betw (OUT (CoprodX I A)) (Set (coprodX I A)) (CoprodX I A)"
    and "bij_betw (IN (CoprodX I A)) (CoprodX I A) (Set (coprodX I A))"
    and "\<And>x. x \<in> Set (coprodX I A) \<Longrightarrow> OUT (CoprodX I A) x \<in> CoprodX I A"
    and "\<And>y. y \<in> CoprodX I A \<Longrightarrow> IN (CoprodX I A) y \<in> Set (coprodX I A)"
    and "\<And>x. x \<in> Set (coprodX I A) \<Longrightarrow> IN (CoprodX I A) (OUT (CoprodX I A) x) = x"
    and "\<And>y. y \<in> CoprodX I A \<Longrightarrow> OUT (CoprodX I A) (IN (CoprodX I A) y) = y"
    proof -
      show "ide (coprodX I A)"
        unfolding coprodX_def
        by (simp add: assms(1,2,3) small_CoprodX embeds_CoprodX ide_mkide(1))
      show 1: "bij_betw (OUT (CoprodX I A)) (Set (coprodX I A)) (CoprodX I A)"
        unfolding coprodX_def
        using assms small_CoprodX embeds_CoprodX bij_OUT [of "CoprodX I A"] by fastforce
      show 2: "bij_betw (IN (CoprodX I A)) (CoprodX I A) (Set (coprodX I A))"
        unfolding coprodX_def
        using assms small_CoprodX embeds_CoprodX bij_IN [of "CoprodX I A"] by fastforce
      show "\<And>x. x \<in> Set (coprodX I A) \<Longrightarrow> OUT (CoprodX I A) x \<in> CoprodX I A"
        using 1 bij_betwE by blast
      show "\<And>y. y \<in> CoprodX I A \<Longrightarrow> IN (CoprodX I A) y \<in> Set (coprodX I A)"
        using 2 bij_betwE by blast
      show "\<And>x. x \<in> Set (coprodX I A) \<Longrightarrow> IN (CoprodX I A) (OUT (CoprodX I A) x) = x"
        using 1 bij_betw_inv_into_left
                    [of "OUT (CoprodX I A)" "Set (coprodX I A)" "CoprodX I A"]
        by (auto simp add: coprodX_def)
      show "\<And>y. y \<in> CoprodX I A \<Longrightarrow> OUT (CoprodX I A) (IN (CoprodX I A) y) = y"
        by (simp add: OUT_IN assms(1,2,3) small_CoprodX embeds_CoprodX)
    qed

    abbreviation InX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'a \<Rightarrow> 'U \<Rightarrow> 'U"
    where "InX I A i \<equiv> \<lambda>x. if x \<in> Set (A i) then IN (CoprodX I A) (i, x) else null"

    definition inX
    where "inX I A i \<equiv> mkarr (A i) (coprodX I A) (InX I A i)"

    lemma InX_in_Hom:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "i \<in> I"
    shows "InX I A i \<in> Hom (A i) (coprodX I A)"
      using assms ide_coprodX(2-3,5) by auto

    lemma inX_in_hom [intro, simp]:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "i \<in> I"
    shows "in_hom (inX I A i) (A i) (coprodX I A)"
      using assms ide_coprodX InX_in_Hom
      by (unfold inX_def, intro mkarr_in_hom) auto

    lemma inX_simps [simp]:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "i \<in> I"
    shows "arr (inX I A i)" and "dom (inX I A i) = A i" and "cod (inX I A i) = coprodX I A"
      using assms inX_in_hom by blast+
 
    lemma Fun_inX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "i \<in> I"
    shows "Fun (inX I A i) = InX I A i"
    proof -
      have "arr (inX I A i)"
        by (simp add: assms)
      thus ?thesis
        by (simp add: inX_def)
    qed

    definition CotupleX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'U \<Rightarrow> 'U"
    where "CotupleX I A F \<equiv>
           (\<lambda>x. if x \<in> Set (coprodX I A)
                then Fun (F (fst (OUT (CoprodX I A) x))) (snd (OUT (CoprodX I A) x))
                else null)"

    lemma CotupleX_in_Hom:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : A i \<rightarrow> c\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null"
    shows "CotupleX I A F \<in> Hom (coprodX I A) c"
    proof
      show "CotupleX I A F \<in> {F. \<forall>x. x \<notin> Set (coprodX I A) \<longrightarrow> F x = null}"
        by (cases "I = {}") (auto simp add: CotupleX_def)
      show "CotupleX I A F \<in> Set (coprodX I A) \<rightarrow> Set c"
      proof (cases "I = {}")
        case False
        show ?thesis
        proof
          fix x
          assume x: "x \<in> Set (coprodX I A)"
          have "OUT (CoprodX I A) x \<in> CoprodX I A"
            using assms x ide_coprodX
            by (meson bij_betwE)
          hence "\<And>i. i = fst (OUT (CoprodX I A) x) \<Longrightarrow>
                        \<guillemotleft>F i : A i \<rightarrow> c\<guillemotright> \<and> snd (OUT (CoprodX I A) x) \<in> Set (A i)"
            using assms(4) by force
          thus "CotupleX I A F x \<in> Set c"
            using x CotupleX_def [of I A F] Fun_def by auto
        qed
        next
        case True
        show ?thesis
          by (metis (no_types, lifting) Pi_I' True True True True UN_E all_not_in_conv
              assms(1,3) bij_betwE ide_coprodX(2))
      qed
    qed

    definition cotupleX
    where "cotupleX I c A F \<equiv> mkarr (coprodX I A) c (CotupleX I A F)"

    lemma cotupleX_in_hom [intro, simp]:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : A i \<rightarrow> c\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null" and "ide c"
    shows "\<guillemotleft>cotupleX I c A F : coprodX I A \<rightarrow> c\<guillemotright>"
      using assms ide_coprodX CotupleX_in_Hom
      unfolding cotupleX_def CotupleX_def
      by (intro mkarr_in_hom) auto

    lemma cotupleX_simps [simp]:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : A i \<rightarrow> c\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null" and "ide c"
    shows "arr (cotupleX I c A F)"
    and "dom (cotupleX I c A F) = coprodX I A"
    and "cod (cotupleX I c A F) = c"
      using assms cotupleX_in_hom in_homE by blast+

    lemma comp_cotupleX_inX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : A i \<rightarrow> c\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null" and "ide c"
    shows "i \<in> I \<Longrightarrow> cotupleX I c A F \<cdot> inX I A i = F i"
    proof -
      assume i: "i \<in> I"
      have I: "I \<noteq> {}"
        using i by blast
      show "cotupleX I c A F \<cdot> inX I A i = F i"
      proof -
        have 1: "cotupleX I c A F \<cdot> inX I A i =
              mkarr (coprodX I A) c (CotupleX I A F) \<cdot> mkarr (A i) (coprodX I A) (InX I A i)"
          unfolding inX_def cotupleX_def CotupleX_def
          using assms i I comp_mkarr by simp
        also have "... = mkarr (A i) c (CotupleX I A F \<circ> InX I A i)"
          using assms i comp_mkarr
          by (metis (no_types, lifting) 1 seqI cotupleX_def cotupleX_simps(1)
              dom_mkarr inX_simps(1,3) seqE)
        also have "... = mkarr (A i) c
                           (\<lambda>x. if x \<in> Set (A i)
                                then CotupleX I A F (IN (CoprodX I A) (i, x))
                                else null)"
        proof -
          have "CotupleX I A F \<circ> InX I A i =
                (\<lambda>x. if x \<in> Set (A i) then CotupleX I A F (IN (CoprodX I A) (i, x)) else null)"
          proof
            fix x
            show "(CotupleX I A F \<circ> InX I A i) x =
                  (if x \<in> Set (A i) then CotupleX I A F (IN (CoprodX I A) (i, x)) else null)"
              unfolding CotupleX_def by auto
          qed
          thus ?thesis by simp  
        qed
        also have "... = mkarr (A i) c
                           (\<lambda>x. if x \<in> Set (A i)
                                then Fun (F (fst (OUT (CoprodX I A) (IN (CoprodX I A) (i, x)))))
                                            (snd (OUT (CoprodX I A) (IN (CoprodX I A) (i, x))))
                                else null)"
        proof -
          have "\<And>x. x \<in> Set (A i) \<Longrightarrow> IN (CoprodX I A) (i, x) \<in> Set (coprodX I A)"
            using assms(1,2,3) i bij_betwE ide_coprodX(3) by blast
          hence "(\<lambda>x. if x \<in> Set (A i)
                      then CotupleX I A F (IN (CoprodX I A) (i, x))
                      else null) =
                 (\<lambda>x. if x \<in> Set (A i)
                      then Fun (F (fst (OUT (CoprodX I A) (IN (CoprodX I A) (i, x)))))
                                  (snd (OUT (CoprodX I A) (IN (CoprodX I A) (i, x))))
                      else null)"
            unfolding CotupleX_def by force
          thus ?thesis by simp
        qed
        also have "... = mkarr (A i) c (\<lambda>x. if x \<in> Set (A i) then Fun (F i) x else null)"
        proof -
          have "\<And>x. x \<in> Set (A i) \<Longrightarrow> OUT (CoprodX I A) (IN (CoprodX I A) (i, x)) = (i, x)"
            using assms i ide_coprodX by auto
          hence "(\<lambda>x. if \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> A i\<guillemotright>
                      then Fun (F (fst (OUT (CoprodX I A) (IN (CoprodX I A) (i, x)))))
                                  (snd (OUT (CoprodX I A) (IN (CoprodX I A) (i, x))))
                      else null) =
                 (\<lambda>x. if \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> A i\<guillemotright> then Fun (F i) x else null)"
            by force
          thus ?thesis by simp
        qed
        also have "... = mkarr (A i) c (Fun (F i))"
          by (metis (lifting) Fun_def assms(4) category.in_homE category_axioms
              i mem_Collect_eq)
        also have "... = F i"
          using assms(4) i mkarr_Fun by blast
        finally show ?thesis by blast
      qed
    qed

    lemma Fun_cotupleX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : A i \<rightarrow> c\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null" and "ide c"
    shows "Fun (cotupleX I c A F) =
           (\<lambda>x. if x \<in> Set (coprodX I A)
                then Fun (F (fst (OUT (CoprodX I A) x))) (snd (OUT (CoprodX I A) x))
                else null)"
      using assms Fun_mkarr CotupleX_in_Hom CotupleX_def [of I A F] cotupleX_def cotupleX_simps(1)
      by (metis (lifting))

    lemma coproduct_cocone_coprodX:
    assumes "discrete_diagram J C D" and "Collect (partial_composition.arr J) = I"
    and "small I" and "I \<subseteq> Collect arr"
    shows "has_as_coproduct J D (coprodX I D)"
    and "coproduct_cocone J C D (coprodX I D) (inX I D)"
    proof -
      interpret J: category J
        using assms(1) discrete_diagram_def by blast
      interpret D: discrete_diagram J C D
        using assms(1) by blast
      let ?\<pi> = "inX I D"
      let ?a = "coprodX I D"
      interpret A: constant_functor J C ?a
        using assms ide_coprodX
        using D.is_discrete by unfold_locales auto
      interpret \<pi>: natural_transformation J C D A.map ?\<pi>
      proof
        fix j
        show "\<not> J.arr j \<Longrightarrow> inX I D j = null"
          by (metis (no_types, lifting) D.as_nat_trans.extensionality ideD(1)
              mkarr_def not_arr_null inX_def)
        assume j: "J.arr j"
        show 1: "arr (inX I D j)"
          using D.is_discrete assms j by force
        show "inX I D (J.cod j) \<cdot> D j = inX I D j"
          by (metis (lifting) 1 D.is_discrete D.preserves_ide D.preserves_reflects_arr
              J.ideD(3) comp_arr_ide dom_mkarr ideD(3) j inX_def seqI)
        show "A.map j \<cdot> inX I D (J.dom j) = inX I D j"
          by (metis (lifting) 1 A.map_simp D.is_discrete J.ide_char comp_cod_arr j
              cod_mkarr inX_def)
      qed
      show "coproduct_cocone J C D ?a ?\<pi>"
      proof
        fix a' \<chi>'
        assume \<chi>': "D.cocone a' \<chi>'"
        interpret \<chi>': cocone J C D a' \<chi>'
          using \<chi>' by blast
        show "\<exists>!f. \<guillemotleft>f : coprodX I D \<rightarrow> a'\<guillemotright> \<and> D.cocones_map f (inX I D) = \<chi>'"
        proof -
          let ?f = "cotupleX I a' D \<chi>'"
          have f: "\<guillemotleft>?f : coprodX I D \<rightarrow> a'\<guillemotright>"
            using assms cotupleX_in_hom
            by (metis D.is_discrete D.preserves_ide J.ide_char Pi_I'
              \<chi>'.component_in_hom \<chi>'.extensionality \<chi>'.ide_apex mem_Collect_eq)
          moreover have "D.cocones_map ?f (inX I D) = \<chi>'"
          proof
            fix i
            show "D.cocones_map ?f (inX I D) i = \<chi>' i"
            proof -
              have "J.arr i \<Longrightarrow> ?f \<cdot> inX I D i = \<chi>' i"
                using assms comp_cotupleX_inX
                by (metis D.is_discrete D.preserves_ide J.ide_char Pi_I'
                   \<chi>'.component_in_hom \<chi>'.extensionality \<chi>'.ide_apex mem_Collect_eq)
              moreover have "\<not> J.arr i \<Longrightarrow> null = \<chi>' i"
                using \<chi>'.extensionality by auto
              moreover have "D.cocone (dom ?f) (inX I D)"
                by (metis A.constant_functor_axioms D.diagram_axioms
                    \<pi>.natural_transformation_axioms cocone_def diagram_def f in_homE)
              ultimately show ?thesis
                using assms \<chi>'.cocone_axioms by auto
            qed
          qed
          moreover have "\<And>f'. \<lbrakk>\<guillemotleft>f' : coprodX I D \<rightarrow> a'\<guillemotright>; D.cocones_map f' (inX I D) = \<chi>'\<rbrakk>
                                 \<Longrightarrow> f' = ?f"
          proof -
            fix f'
            assume f': "\<guillemotleft>f' : coprodX I D \<rightarrow> a'\<guillemotright>"
            assume 1: "D.cocones_map f' (inX I D) = \<chi>'"
            show "f' = ?f"
            proof (intro arr_eqI [of f'])
              show par: "par f' ?f"
                using f f' by fastforce
              show "Fun f' = Fun (cotupleX I a' D \<chi>')"
              proof
                fix x
                show "Fun f' x = Fun (cotupleX I a' D \<chi>') x"
                proof (cases "x \<in> Set (coprodX I D)")
                  case False
                  show ?thesis
                    using False par f' Fun_def by auto
                  next
                  case True
                  have 2: "D.cocone (dom f') (inX I D)"
                    by (metis A.constant_functor_axioms cocone_def
                        \<pi>.natural_transformation_axioms \<chi>' f' in_homE)
                  have "Fun (cotupleX I a' D \<chi>') x =
                        Fun (\<chi>' (fst (OUT (CoprodX I D) x))) (snd (OUT (CoprodX I D) x))"
                  proof -
                    have "Fun (cotupleX I a' D \<chi>') x = cotupleX I a' D \<chi>' \<cdot> x"
                      using True f Fun_def by auto
                    also have "... = (\<lambda>x. if \<guillemotleft>x : \<one>\<^sup>? \<rightarrow> coprodX I D\<guillemotright>
                                          then cotupleX I a' D \<chi>' \<cdot> x else null) x"
                      using True by simp
                    also have "... =
                               Fun (\<chi>' (fst (OUT (CoprodX I D) x))) (snd (OUT (CoprodX I D) x))"
                      using assms f True cotupleX_def [of I a' D \<chi>'] CotupleX_def [of I D \<chi>']
                            app_mkarr cotupleX_in_hom
                      by auto
                    finally show ?thesis by blast
                  qed
                  also have "... = Fun f' x"
                  proof (cases "OUT (CoprodX I D) x")
                    case (Pair i x')
                    have ix': "(i, x') \<in> CoprodX I D"
                      using assms True Pair ide_coprodX(2) [of I D]
                      by (metis (no_types, lifting) D.is_discrete D.preserves_ide Pi_I'
                          bij_betwE mem_Collect_eq)
                    have "Fun (\<chi>' (fst (OUT (CoprodX I D) x))) (snd (OUT (CoprodX I D) x)) =
                          Fun (\<chi>' i) x'"
                      by (simp add: Pair)
                    also have "... = Fun (D.cocones_map f' (inX I D) i) x'"
                      using 1 by simp
                    also have "... = (f' \<cdot> inX I D i) \<cdot> x'"
                      using assms 2 f' ix' inX_in_hom Fun_def D.extensionality D.is_discrete
                        \<pi>.extensionality
                      by auto
                    also have "... = f' \<cdot> (inX I D i \<cdot> x')"
                      using comp_assoc by simp
                    also have "... = f' \<cdot> IN (CoprodX I D) (i, x')"
                    proof -
                      have "\<guillemotleft>inX I D i : D i \<rightarrow> coprodX I D\<guillemotright>"
                        using assms inX_in_hom D.is_discrete ix' by fastforce
                      hence "\<guillemotleft>mkarr (D i) (coprodX I D) (InX I D i) : D i \<rightarrow> coprodX I D\<guillemotright>"
                        unfolding inX_def by simp
                      thus ?thesis
                        unfolding inX_def
                        using assms ix' app_mkarr by auto
                    qed
                    also have "... = f' \<cdot> x"
                    proof - 
                      have "IN (CoprodX I D) (i, x') = IN (CoprodX I D) (OUT (CoprodX I D) x)"
                        using Pair by simp
                      also have "... = x"
                      proof -
                        have "small (CoprodX I D)"
                          using assms small_CoprodX D.is_discrete by fastforce
                        thus ?thesis
                          using assms True ide_coprodX(6) D.is_discrete D.preserves_ide
                            Pi_I' coprodX_def
                          by force
                      qed
                      finally show ?thesis by simp
                    qed
                    finally show ?thesis
                      using True f' Fun_def by force
                  qed
                  finally show ?thesis by simp
                qed
              qed
            qed
          qed
          ultimately show ?thesis by blast
        qed
      qed
      thus "has_as_coproduct J D (coprodX I D)"
        using has_as_coproduct_def by blast
    qed

    lemma has_small_coproducts:
    assumes "small I" and "I \<subseteq> Collect arr"
    shows "has_coproducts I"
    proof (unfold has_coproducts_def, intro conjI)
      show "I \<noteq> UNIV"
        using assms not_arr_null by blast
      show "\<forall>J D. discrete_diagram J (\<cdot>) D \<and> Collect (partial_composition.arr J) = I
                    \<longrightarrow> (\<exists>a. has_as_coproduct J D a)"
        using assms coproduct_cocone_coprodX by blast
    qed

  end

  subsection "Exported Notions"

  context sets_cat_with_cotupling
  begin

    interpretation Coproducts: small_coproducts_in_sets_cat ..

    abbreviation CoprodX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> ('a \<times> 'U) set"
    where "CoprodX \<equiv> Coproducts.CoprodX"

    abbreviation coprodX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'U"
    where "coprodX \<equiv> Coproducts.coprodX"

    abbreviation inX :: "'a set \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'a \<Rightarrow> 'U"
    where "inX \<equiv> Coproducts.inX"

    abbreviation cotupleX :: "'a set \<Rightarrow> 'U \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> ('a \<Rightarrow> 'U) \<Rightarrow> 'U"
    where "cotupleX \<equiv> Coproducts.cotupleX"

    lemma coprod_comparison_map_props:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    shows "OUT (CoprodX I A) \<in> Set (coprodX I A) \<rightarrow> CoprodX I A"
    and "IN (CoprodX I A) \<in> CoprodX I A \<rightarrow> Set (coprodX I A)"
    and "\<And>x. x \<in> Set (coprodX I A) \<Longrightarrow> IN (CoprodX I A) (OUT (CoprodX I A) x) = x"
    and "\<And>y. y \<in> CoprodX I A \<Longrightarrow> OUT (CoprodX I A) (IN (CoprodX I A) y) = y"
    and "bij_betw (OUT (CoprodX I A)) (Set (coprodX I A)) (CoprodX I A)"
    and "bij_betw (IN (CoprodX I A)) (CoprodX I A) (Set (coprodX I A))"
      using assms Coproducts.ide_coprodX by auto

    lemma Fun_inX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "i \<in> I"
    shows "Fun (inX I A i) = Coproducts.InX I A i"
      using assms Coproducts.Fun_inX by auto

    lemma Fun_cotupleX:
    assumes "small I" and "A \<in> I \<rightarrow> Collect ide" and "I \<subseteq> Collect arr"
    and "\<And>i. i \<in> I \<Longrightarrow> \<guillemotleft>F i : A i \<rightarrow> c\<guillemotright>" and "\<And>i. i \<notin> I \<Longrightarrow> F i = null" and "ide c"
    shows "Fun (cotupleX I c A F) =
           (\<lambda>x. if x \<in> Set (coprodX I A)
                then Fun (F (fst (OUT (\<Union>i\<in>I. {i} \<times> Set (A i)) x)))
                       (snd (OUT (\<Union>i\<in>I. {i} \<times> Set (A i)) x))
               else null)"
      using assms Coproducts.Fun_cotupleX app_mkarr Coproducts.cotupleX_def by auto

    lemma coproduct_cocone_coprodX:
    assumes "discrete_diagram J C D" and "Collect (partial_composition.arr J) = I"
    and "small I" and "I \<subseteq> Collect arr"
    shows "has_as_coproduct J D (coprodX I D)"
    and "coproduct_cocone J C D (coprodX I D) (inX I D)"
      using assms Coproducts.coproduct_cocone_coprodX by auto

    lemma has_small_coproducts:
    assumes "small I" and "I \<subseteq> Collect arr"
    shows "has_coproducts I"
      using assms Coproducts.has_small_coproducts by blast

  end

  section "Coequalizers"

  text\<open>
    In this section we show that a sets category has coequalizers of parallel pairs
    of arrows.  For this, we need to assume that the set of arrows of the category
    embeds the set of all its small subsets.  The reason we need this assumption is to
    make it possible to obtain an object corresponding to the set of equivalence classes
    that results from the quotient construction.
  \<close>

  locale sets_cat_with_powering =
    sets_cat sml C +
    powering sml \<open>Collect arr\<close>
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)

  sublocale sets_cat_with_tupling \<subseteq> sets_cat_with_powering ..

  locale coequalizers_in_sets_cat =
    sets_cat_with_powering sml C
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    text\<open>
      The following defines the ``equivalence closure'' of a binary relation \<open>r\<close>
      on a set \<open>A\<close>, and proves the characterization of it as the least equivalence relation
      on \<open>A\<close> that contains \<open>r\<close>.  For some reason I could not find such a thing in the
      Isabelle distribution, though I did find a predicate version @{term equivclp}.
    \<close>

    definition equivcl
    where "equivcl A r \<equiv> SOME r'. r \<subseteq> r' \<and> equiv A r' \<and> (\<forall>s'. r \<subseteq> s' \<and> equiv A s' \<longrightarrow> r' \<subseteq> s')"

    lemma equivcl_props:
    assumes "r \<subseteq> A \<times> A"
    shows "\<exists>r'. r \<subseteq> r' \<and> equiv A r' \<and> (\<forall>s'. r \<subseteq> s' \<and> equiv A s' \<longrightarrow> r' \<subseteq> s')"
    and "r \<subseteq> equivcl A r" and "equiv A (equivcl A r)"
    and "\<And>s'. r \<subseteq> s' \<and> equiv A s' \<Longrightarrow> equivcl A r \<subseteq> s'"
    proof -
      have 1: "equiv A (A \<times> A)"
        using refl_on_def trans_on_def
        by (intro equivI symI) auto
      show 2: "\<exists>r'. r \<subseteq> r' \<and> equiv A r' \<and> (\<forall>s'. r \<subseteq> s' \<and> equiv A s' \<longrightarrow> r' \<subseteq> s')"
      proof -
        let ?r' = "\<Inter> {s. equiv A s \<and> r \<subseteq> s}"
        have "r \<subseteq> ?r'"
          by blast
        moreover have "\<forall>s'. r \<subseteq> s' \<and> equiv A s' \<longrightarrow> ?r' \<subseteq> s'"
          by blast
        moreover have "equiv A ?r'"
          using assms 1
          apply (intro equivI symI transI refl_onI)
             apply auto[4]
            apply (simp add: equiv_def refl_on_def)
           apply (meson equiv_def symD)
          by (meson equivE transE)
        ultimately show ?thesis by blast
      qed
      have "r \<subseteq> equivcl A r \<and> equiv A (equivcl A r) \<and>
              (\<forall>s'. r \<subseteq> s' \<and> equiv A s' \<longrightarrow> equivcl A r \<subseteq> s')"
        unfolding equivcl_def
        using 2 someI_ex [of "\<lambda>r'. r \<subseteq> r' \<and> equiv A r' \<and> (\<forall>s'. r \<subseteq> s' \<and> equiv A s' \<longrightarrow> r' \<subseteq> s')"]
        by fastforce
      thus "r \<subseteq> equivcl A r" and "equiv A (equivcl A r)"
      and "\<And>s'. r \<subseteq> s' \<and> equiv A s' \<Longrightarrow> equivcl A r \<subseteq> s'"
        by auto
    qed

    text\<open>
      The elements of the codomain of the coequalizer of \<open>f\<close> and \<open>g\<close> are the equivalence
      classes of the least equivalence relation on \<open>Set (cod f)\<close> that relates \<open>f \<cdot> x\<close>
      and \<open>g \<cdot> x\<close> whenever \<open>x \<in> Set (dom f)\<close>.
    \<close>

    abbreviation Cod_coeq :: "'U \<Rightarrow> 'U \<Rightarrow> 'U set set"
    where "Cod_coeq f g \<equiv> (\<lambda>y. (equivcl (Set (cod f))
                                  ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) `` {y})) ` Set (cod f)"

    lemma small_Cod_coeq:
    assumes "par f g"
    shows "small (Cod_coeq f g)"
      using assms ide_cod small_Set by blast

    lemma embeds_Cod_coeq:
    assumes "par f g"
    shows "embeds (Cod_coeq f g)"
    and "Cod_coeq f g \<subseteq> Pow (Set (cod f))"
    proof -
      show 1: "Cod_coeq f g \<subseteq> Pow (Set (cod f))"
      proof -
        let ?r = "(\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)"
        have "?r \<subseteq> Set (cod f) \<times> Set (cod f)"
          using assms by auto
        hence "equivcl (Set (cod f)) ?r \<subseteq> Set (cod f) \<times> Set (cod f)"
          using equivcl_props(3)
          by (metis (no_types, lifting) Sigma_cong equiv_type)
        thus ?thesis by blast
      qed
      show "embeds (Cod_coeq f g)"
      proof -
        have "Cod_coeq f g \<subseteq> {X. X \<subseteq> Collect arr \<and> small X}"
        proof -
          have "Cod_coeq f g \<subseteq> {X. X \<subseteq> Collect arr}"
            using 1 by blast
          moreover have "Cod_coeq f g \<subseteq> {X. small X}"
            using assms 1 small_Set smaller_than_small
            by (metis (no_types, lifting) HOL.ext Collect_mono Pow_def
                ide_cod subset_trans)
          ultimately show ?thesis by blast
        qed
        thus ?thesis
          using embeds_small_sets
          by (meson image_mono inj_on_subset subset_trans)
      qed
    qed

    definition cod_coeq
    where "cod_coeq f g \<equiv> mkide (Cod_coeq f g)"

    lemma ide_cod_coeq:
    assumes "par f g"
    shows "ide (cod_coeq f g)"
    and "bij_betw (OUT (Cod_coeq f g)) (Set (cod_coeq f g)) (Cod_coeq f g)"
    and "bij_betw (IN (Cod_coeq f g)) (Cod_coeq f g) (Set (cod_coeq f g))"
    and "\<And>x. x \<in> Set (cod_coeq f g) \<Longrightarrow> OUT (Cod_coeq f g) x \<in> Cod_coeq f g"
    and "\<And>y. y \<in> Cod_coeq f g \<Longrightarrow> IN (Cod_coeq f g) y \<in> Set (cod_coeq f g)"
    and "\<And>x. x \<in> Set (cod_coeq f g) \<Longrightarrow> IN (Cod_coeq f g) (OUT (Cod_coeq f g) x) = x"
    and "\<And>y. y \<in> Cod_coeq f g \<Longrightarrow> OUT (Cod_coeq f g) (IN (Cod_coeq f g) y) = y"
    proof -
      have "(\<lambda>x. {f \<cdot> x, g \<cdot> x}) ` Set (dom f) \<subseteq> Pow (Set (cod f))"
        using assms by auto
      show "ide (cod_coeq f g)"
        using small_Cod_coeq embeds_Cod_coeq assms cod_coeq_def by auto
      show 1: "bij_betw (OUT (Cod_coeq f g)) (Set (cod_coeq f g)) (Cod_coeq f g)"
        unfolding cod_coeq_def
        using assms ide_mkide bij_OUT small_Cod_coeq [of f g] embeds_Cod_coeq [of f g]
        by auto
      show 2: "bij_betw (IN (Cod_coeq f g)) (Cod_coeq f g) (Set (cod_coeq f g))"
        unfolding cod_coeq_def
        using assms ide_mkide bij_OUT bij_IN small_Cod_coeq [of f g] embeds_Cod_coeq
        by fastforce
      show "\<And>x. x \<in> Set (cod_coeq f g) \<Longrightarrow> OUT (Cod_coeq f g) x \<in> Cod_coeq f g"
        using 1 bij_betwE by blast
      show "\<And>y. y \<in> Cod_coeq f g \<Longrightarrow> IN (Cod_coeq f g) y \<in> Set (cod_coeq f g)"
        using 2 bij_betwE by blast
      show "\<And>x. x \<in> Set (cod_coeq f g) \<Longrightarrow> IN (Cod_coeq f g) (OUT (Cod_coeq f g) x) = x"
        by (metis (no_types, lifting) HOL.ext "1" bij_betw_inv_into_left cod_coeq_def)
      show "\<And>y. y \<in> Cod_coeq f g \<Longrightarrow> OUT (Cod_coeq f g) (IN (Cod_coeq f g) y) = y"
        by (metis (no_types, lifting) HOL.ext "1" bij_betw_inv_into_right cod_coeq_def)
    qed

    definition Coeq
    where "Coeq f g \<equiv> \<lambda>y. if y \<in> Set (cod f)
                           then IN (Cod_coeq f g)
                                  (equivcl (Set (cod f))
                                     ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) `` {y})
                           else null"

    lemma Coeq_in_Hom [intro]:
    assumes "par f g"
    shows "Coeq f g \<in> Hom (cod f) (cod_coeq f g)"
    proof
      show "Coeq f g \<in> Set (cod f) \<rightarrow> Set (cod_coeq f g)"
      proof
        fix y
        assume y: "y \<in> Set (cod f)"
        have "Coeq f g y = IN (Cod_coeq f g)
                                  (equivcl (Set (cod f))
                                     ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) `` {y})"
          unfolding Coeq_def
          using y by simp
        moreover have "... \<in> Set (cod_coeq f g)"
          using assms ide_cod_coeq(5) y by blast
        ultimately show "Coeq f g y \<in> Set (cod_coeq f g)" by simp
      qed
      show "Coeq f g \<in> {F. \<forall>x. x \<notin> Set (cod f) \<longrightarrow> F x = null}"
        unfolding Coeq_def by simp
    qed

    definition coeq
    where "coeq f g \<equiv> mkarr (cod f) (cod_coeq f g) (Coeq f g)"

    lemma coeq_in_hom [intro, simp]:
    assumes "par f g"
    shows "\<guillemotleft>coeq f g : cod f \<rightarrow> cod_coeq f g\<guillemotright>"
      using assms ide_cod_coeq(1) Coeq_in_Hom
      by (unfold coeq_def, intro mkarr_in_hom) auto

    lemma coeq_simps [simp]:
    assumes "par f g"
    shows "arr (coeq f g)" and "dom (coeq f g) = cod f" and "cod (coeq f g) = cod_coeq f g"
      using assms coeq_in_hom by blast+

    lemma Fun_coeq:
    assumes "par f g"
    shows "Fun (coeq f g) = Coeq f g"
      using assms Fun_mkarr coeq_def coeq_simps(1) by presburger

    lemma coeq_coequalizes:
    assumes "par f g"
    shows "coeq f g \<cdot> f = coeq f g \<cdot> g"
    proof (intro arr_eqI)
      show par: "par (coeq f g \<cdot> f) (coeq f g \<cdot> g)"
        using assms by auto
      show "Fun (coeq f g \<cdot> f) = Fun (coeq f g \<cdot> g)"
      proof
        fix x
        show "Fun (coeq f g \<cdot> f) x = Fun (coeq f g \<cdot> g) x"
        proof (cases "x \<in> Set (dom f)")
          case False
          show ?thesis
            using assms False Fun_coeq Fun_def by simp
          next
          case True 
          show ?thesis
          proof -
            have "Fun (coeq f g \<cdot> f) x = Fun (coeq f g) (Fun f x)"
              using assms Fun_comp comp_in_homI coeq_in_hom comp_assoc by auto
            also have "... = Coeq f g (Fun f x)"
              using assms True Fun_coeq
              by (metis (full_types, lifting))
            also have "... = IN (Cod_coeq f g)
                               (equivcl (Set (cod f))
                                  ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) `` {f \<cdot> x})"
              unfolding Coeq_def
              using True assms Fun_def by auto
            also have "... = IN (Cod_coeq f g)
                               (equivcl (Set (cod f))
                                  ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) `` {g \<cdot> x})"
            proof -
              have "equivcl (Set (cod f)) ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) `` {f \<cdot> x} =
                    equivcl (Set (cod f)) ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) `` {g \<cdot> x}"
                using assms True
                      equivcl_props(2-3) [of "(\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)" "Set (cod f)"]
                      equiv_class_eq_iff
                        [of "Set (cod f)"
                            "equivcl (Set (cod f)) ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f))"
                            "f \<cdot> x" "g \<cdot> x"]
                by auto
              thus ?thesis by simp
            qed
            also have "... = Coeq f g (Fun g x)"
              unfolding Coeq_def
              using True assms Fun_def by auto
            also have "... = Fun (coeq f g) (Fun g x)"
              using assms True Fun_coeq
              by (metis (full_types, lifting))
            also have "... = Fun (coeq f g \<cdot> g) x"
              using assms Fun_comp comp_in_homI coeq_in_hom comp_assoc by auto
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    lemma Coeq_surj:
    assumes "par f g" and "Set (cod f) \<noteq> {}" and "y \<in> Set (cod_coeq f g)"
    shows "\<exists>x. x \<in> Set (cod f) \<and> Coeq f g x = y"
    proof -
      have 1: "(\<Union>x\<in>Set (dom f). {f \<cdot> x, g \<cdot> x}) \<subseteq> Set (cod f)"
        using assms by auto
      have y: "OUT (Cod_coeq f g) y \<in> Cod_coeq f g"
        using assms ide_cod_coeq(2) [of f g] bij_betwE by blast
      obtain x where x: "x \<in> Set (cod f) \<and>
                         OUT (Cod_coeq f g) y =
                         equivcl (Set (cod f)) ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) ``{x}"
        using assms y by blast
      hence 2: "x \<in> OUT (Cod_coeq f g) y"
      proof -
        have "(\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f) \<subseteq> Set (cod f) \<times> Set (cod f)"
          using assms by auto
        hence "x \<in> equivcl (Set (cod f)) ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) ``{x}"
          using assms x equivcl_props(3) [of "(\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)" "Set (cod f)"]
                equiv_class_self
          by (metis (lifting))
        thus ?thesis
          using x by argo
      qed
      have "Coeq f g x = y"
      proof -
        have "OUT (Cod_coeq f g) (Coeq f g x) =
              OUT (Cod_coeq f g)
                (IN (Cod_coeq f g)
                   (equivcl (Set (cod f)) ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) ``{x}))"
          unfolding Coeq_def
          using x by presburger
        also have "... = equivcl (Set (cod f)) ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) ``{x}"
          using assms x y ide_cod_coeq(7) by (metis (lifting))
        also have "... = OUT (Cod_coeq f g) y"
        proof -
          have "OUT (Cod_coeq f g) y \<in> Cod_coeq f g"
            using assms x by force
          (*
           * x \<in> OUT (Cod_coeq f g) y, which is a class of the coequalizing equivalence.
           * Therefore the class of x in that equivalence is the same class.
           *)
          thus ?thesis
            using assms x 1 2 by blast
        qed
        finally have "IN (Cod_coeq f g) (OUT (Cod_coeq f g) (Coeq f g x)) =
                      IN (Cod_coeq f g) (OUT (Cod_coeq f g) y)"
          by simp
        thus ?thesis
          using assms x y ide_cod_coeq(6) cod_coeq_def Coeq_def
          by (metis (lifting))
      qed
      thus "\<exists>x. x \<in> Set (cod f) \<and> Coeq f g x = y"
        using x by blast
    qed

    lemma coeq_is_coequalizer:
    assumes "par f g" and "Set (cod f) \<noteq> {}"
    shows "has_as_coequalizer f g (coeq f g)"
    proof
      show "par f g" by fact
      show "seq (coeq f g) f"
        using assms by auto
      show "coeq f g \<cdot> f = coeq f g \<cdot> g"
        using assms coeq_coequalizes by blast
      show "\<And>q'. \<lbrakk>seq q' f; q' \<cdot> f = q' \<cdot> g\<rbrakk> \<Longrightarrow> \<exists>!h. h \<cdot> coeq f g = q'"
      proof -
        fix q'
        assume seq: "seq q' f" and eq: "q' \<cdot> f = q' \<cdot> g"
        let ?H = "\<lambda>y. if y \<in> Set (cod_coeq f g)
                      then q' \<cdot> (SOME x. x \<in> Set (cod f) \<and> Coeq f g x = y)
                      else null"
        have H: "?H \<in> Hom (cod_coeq f g) (cod q')"
        proof
          show "?H \<in> Set (cod_coeq f g) \<rightarrow> Set (cod q')"
          proof
            fix y
            assume y: "y \<in> Set (cod_coeq f g)"
            have "?H y = q' \<cdot> (SOME x. x \<in> Set (cod f) \<and> Coeq f g x = y)"
              using y by simp
            moreover have "... \<in> Set (cod q')"
              using assms y someI_ex [of "\<lambda>x.  x \<in> Set (cod f) \<and> Coeq f g x = y"]
                    Coeq_surj seq in_homI
              by blast
            ultimately show "?H y \<in> Set (cod q')" by simp
          qed
          show "?H \<in> {F. \<forall>x. x \<notin> Set (cod_coeq f g) \<longrightarrow> F x = null}"
            by simp
        qed
        let ?h = "mkarr (cod_coeq f g) (cod q') ?H"
        have h: "\<guillemotleft>?h : cod_coeq f g \<rightarrow> cod q'\<guillemotright>"
          using assms H ide_cod_coeq seq
          by (intro mkarr_in_hom) auto
        have *: "?h \<cdot> coeq f g = q'"
        proof (intro arr_eqI)
          show par: "par (?h \<cdot> coeq f g) q'"
            using assms h seq by fastforce
          show "Fun (?h \<cdot> coeq f g) = Fun q'"
          proof -
            have "Fun (?h \<cdot> coeq f g) = Fun ?h \<circ> Fun (coeq f g)"
              using Fun_comp par by blast
            also have "... = ?H \<circ> Coeq f g"
              using assms h Fun_coeq Fun_mkarr arrI by auto
            also have "... = Fun q'"
            proof
              fix y
              show "(?H \<circ> Coeq f g) y = Fun q' y"
              proof (cases "y \<in> Set (cod f)")
                case False
                show ?thesis
                  unfolding Coeq_def
                  using False seq Fun_def by auto
                next
                case True
                have "(?H \<circ> Coeq f g) y =
                      q' \<cdot> (SOME x'. x' \<in> Set (cod f) \<and> Coeq f g x' = Coeq f g y)"
                  using Coeq_in_Hom True assms(1) by auto
                also have "... = q' \<cdot> y"
                proof -
                  let ?e = "(\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)"
                  have e: "?e \<subseteq> Set (cod f) \<times> Set (cod f)"
                    using assms by auto
                  let ?\<E> = "equivcl (Set (cod f)) ?e"
                  let ?\<E>' = "{p \<in> Set (cod f) \<times> Set (cod f). q' \<cdot> fst p = q' \<cdot> snd p}"
                  have "?\<E> \<subseteq> ?\<E>'"
                  proof -
                    have "equiv (Set (cod f)) ?\<E>'"
                      by (intro equivI symI) (auto simp add: refl_on_def trans_on_def)
                    moreover have "(\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f) \<subseteq> ?\<E>'"
                    proof -
                      have "\<And>x. x \<in> Set (dom f) \<Longrightarrow> (f \<cdot> x, g \<cdot> x) \<in> ?\<E>'"
                      proof -
                        fix x
                        assume x: "x \<in> Set (dom f)"
                        have "(f \<cdot> x, g \<cdot> x) \<in> Set (cod f) \<times> Set (cod f)"
                          using assms x by auto
                        moreover have "q' \<cdot> f \<cdot> x = q' \<cdot> g \<cdot> x"
                          using eq comp_assoc by metis
                        ultimately show "(f \<cdot> x, g \<cdot> x) \<in> ?\<E>'" by fastforce
                      qed
                      thus ?thesis
                        by (meson image_subsetI)
                    qed
                    ultimately show ?thesis
                      by (meson equiv_type equivcl_props(4) subset_trans)
                  qed
                  moreover have "\<And>y'. y' \<in> Set (cod f) \<and> Coeq f g y' = Coeq f g y
                                         \<Longrightarrow> (y', y) \<in> ?\<E>"
                  proof -
                    fix y'
                    assume y': "y' \<in> Set (cod f) \<and> Coeq f g y' = Coeq f g y"
                    have eq: "equivcl (Set (cod f)) ?e `` {y'} =
                              equivcl (Set (cod f)) ?e `` {y}"
                      using assms(1) True y' ide_cod_coeq(7) [of f g]
                      unfolding Coeq_def
                      by (metis (mono_tags, lifting) image_eqI)
                    moreover have "y' \<in> equivcl (Set (cod f)) ?e `` {y'} \<and>
                                   y \<in> equivcl (Set (cod f)) ?e `` {y}"
                    proof
                      have 1: "equiv (Set (cod f)) (equivcl (Set (cod f)) ?e)"
                        by (simp add: e equivcl_props(3))
                      show "y' \<in> equivcl (Set (cod f)) ?e `` {y'}"
                        by (metis (lifting) 1 equiv_class_self y')
                      show "y \<in> equivcl (Set (cod f)) ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) `` {y}"
                        by (metis (no_types, lifting) 1 True equiv_class_self)
                    qed
                    ultimately show "(y', y) \<in> ?\<E>" by blast
                  qed
                  ultimately have "\<And>y'. y' \<in> Set (cod f) \<and> Coeq f g y' = Coeq f g y
                                           \<Longrightarrow> (y', y) \<in> ?\<E>'"
                    by (meson subsetD)
                  thus ?thesis
                    using True someI_ex [of "\<lambda>y'. y' \<in> Set (cod f) \<and> Coeq f g y' = Coeq f g y"]
                    by (metis (mono_tags, lifting) fst_conv mem_Collect_eq snd_conv)
                qed
                also have "... = Fun q' y"
                  using True seq Fun_def by auto
                finally show ?thesis by blast
              qed
            qed
            finally show ?thesis by blast
          qed
        qed
        moreover have "\<And>h'. h' \<cdot> coeq f g = q' \<Longrightarrow> h' = ?h"
        proof -
          fix h'
          assume h': "h' \<cdot> coeq f g = q'"
          show "h' = ?h"
          proof (intro arr_eqI [of h'])
            show par: "par h' ?h"
              using h h' seq
              by (metis (lifting) calculation cod_comp seqE)
            show "Fun h' = Fun ?h"
            proof -
              have 1: "Fun h' \<circ> Coeq f g = Fun ?h \<circ> Coeq f g"
                using assms h' * Fun_coeq Fun_comp seq seqE
                by (metis (lifting))
              show ?thesis
              proof
                fix z
                show "Fun h' z = Fun ?h z"
                proof (cases "z \<in> Set (cod_coeq f g)")
                  case False
                  show ?thesis
                    using assms False h' par Fun_def by auto
                  next
                  case True
                  obtain x where x: "x \<in> Set (cod f) \<and> Coeq f g x = z"
                    using assms True Coeq_surj by blast
                  show ?thesis
                    using True x h' 1 * Fun_comp comp_apply
                    by (metis (lifting))
                qed
              qed
            qed
          qed
        qed
        ultimately show "\<exists>!h. h \<cdot> coeq f g = q'" by auto
      qed
    qed

    lemma has_coequalizers:
    assumes "par f g"
    shows "\<exists>e. has_as_coequalizer f g e"
    proof (cases "Set (cod f) = {}")
      case False
      show ?thesis
        using assms False coeq_is_coequalizer by blast
      next
      case True
      have "f = g"
        using assms True
        by (metis arr_eqI' comp_in_homI empty_Collect_eq in_homI)
      hence "has_as_coequalizer f g (cod f)"
        using assms comp_arr_dom comp_cod_arr seqE
        by (intro has_as_coequalizerI) metis+
      thus ?thesis by blast
    qed

  end

  subsection "Exported Notions"

  context sets_cat_with_powering
  begin

    interpretation Coeq: coequalizers_in_sets_cat sml C ..

    abbreviation Cod_coeq
    where "Cod_coeq \<equiv> Coeq.Cod_coeq"

    abbreviation coeq
    where "coeq \<equiv> Coeq.coeq"

    lemma coequalizer_comparison_map_props:
    assumes "par f g"
    shows "bij_betw (OUT (Cod_coeq f g)) (Set (cod (coeq f g))) (Cod_coeq f g)"
    and "bij_betw (IN (Cod_coeq f g)) (Cod_coeq f g) (Set (cod (coeq f g)))"
    and "\<And>x. x \<in> Set (cod (coeq f g)) \<Longrightarrow> OUT (Cod_coeq f g) x \<in> Cod_coeq f g"
    and "\<And>y. y \<in> Cod_coeq f g \<Longrightarrow> IN (Cod_coeq f g) y \<in> Set (cod (coeq f g))"
    and "\<And>x. x \<in> Set (cod (coeq f g)) \<Longrightarrow> IN (Cod_coeq f g) (OUT (Cod_coeq f g) x) = x"
    and "\<And>y. y \<in> Cod_coeq f g \<Longrightarrow> OUT (Cod_coeq f g) (IN (Cod_coeq f g) y) = y"
      using assms Coeq.ide_cod_coeq by auto

    lemma coeq_is_coequalizer:
    assumes "par f g" and "Set (cod f) \<noteq> {}"
    shows "has_as_coequalizer f g (coeq f g)"
      using assms Coeq.coeq_is_coequalizer by blast

    text\<open>
      Since the fact \<open>Fun_coeq\<close> below is not very useful without the notions used in
      stating it, the function \<open>equivcl\<close> and characteristic fact \<open>equivcl_props\<close> are
      also exported here.  It would be better if \<open>Fun_coeq\<close> could be expressed completely
      in terms of existing notions from the library.
    \<close>

    definition equivcl
    where "equivcl \<equiv> Coeq.equivcl"

    lemma equivcl_props:
    assumes "r \<subseteq> A \<times> A"
    shows "\<exists>r'. r \<subseteq> r' \<and> equiv A r' \<and> (\<forall>s'. r \<subseteq> s' \<and> equiv A s' \<longrightarrow> r' \<subseteq> s')"
    and "r \<subseteq> equivcl A r" and "equiv A (equivcl A r)"
    and "\<And>s'. r \<subseteq> s' \<and> equiv A s' \<Longrightarrow> equivcl A r \<subseteq> s'"
      using assms Coeq.equivcl_props [of r A]
      unfolding equivcl_def by auto

    lemma Fun_coeq:
    assumes "par f g"
    shows "Fun (coeq f g) = (\<lambda>y. if y \<in> Set (cod f)
                                 then IN (Cod_coeq f g)
                                        (equivcl (Set (cod f))
                                           ((\<lambda>x. (f \<cdot> x, g \<cdot> x)) ` Set (dom f)) `` {y})
                           else null)"
      using assms Coeq.Fun_coeq Coeq.Coeq_def
      unfolding equivcl_def by auto

    lemma has_coequalizers:
    assumes "par f g"
    shows "\<exists>e. has_as_coequalizer f g e"
     using assms Coeq.has_coequalizers by blast

  end

  section "Exponentials"

  text\<open>
    In this section we show that the category is cartesian closed.
  \<close>
  locale exponentials_in_sets_cat =
    sets_cat_with_tupling sml C
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    abbreviation app :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "app f \<equiv> inv_into SEF some_embedding_of_small_functions f"

    abbreviation Exp :: "'U \<Rightarrow> 'U \<Rightarrow> ('U \<Rightarrow> 'U) set"
    where "Exp a b \<equiv> {F. F \<in> Set a \<rightarrow> Set b \<and> (\<forall>x. x \<notin> Set a \<longrightarrow> F x = null)}"

    definition exp :: "'U \<Rightarrow> 'U \<Rightarrow> 'U"
    where "exp a b \<equiv> mkide (Exp a b)"

    lemma memb_Exp_popular_value:
    assumes "ide a" and "ide b" and "F \<in> Exp a b"
    and "popular_value F y"
    shows "y = null"
    proof -
      (* TODO: This is similar to argument in small_function_tuple. *)
      have "y \<in> Set b \<or> y = null"
        using assms popular_value_in_range [of F y] by blast
      hence "y \<noteq> null \<Longrightarrow> {x. F x = y} \<subseteq> Set a"
        using assms by blast
      thus "y = null"
        using assms smaller_than_small small_Set by auto
    qed

    lemma memb_Exp_imp_small_function:
    assumes "ide a" and "ide b" and "F \<in> Exp a b"
    shows "small_function F"
    proof
      show "small (range F)"
      proof -
        have "range F \<subseteq> Set b \<union> {null}"
          using assms by blast
        moreover have "small ..."
          using assms small_Set by auto
        ultimately show ?thesis
          using smaller_than_small by blast
      qed
      show "at_most_one_popular_value F"
        using assms memb_Exp_popular_value Uniq_def
        by (metis (no_types, lifting))
    qed

    lemma small_Exp:
    assumes "ide a" and "ide b"
    shows "small (Exp a b)"
    proof -
      show ?thesis
      proof (cases "small (UNIV :: 'U set)")
        case False
        have "Exp a b \<subseteq> {F. small_function F \<and> SF_Dom F \<subseteq> Set a \<and> range F \<subseteq> Set b \<union> {null}}"
        proof
          fix F
          assume F: "F \<in> Exp a b"
          have "small_function F"
            using assms F memb_Exp_imp_small_function [of a b F] by blast
          moreover have "SF_Dom F \<subseteq> Set a"
          proof -
            have "popular_value F null"
            proof -
              (* TODO: Why doesn't this follow by blast or simp? *)
              have "\<And>F y. F \<in> Exp a b \<Longrightarrow> popular_value F y \<Longrightarrow> y = null"
                using assms memb_Exp_popular_value by meson
              moreover have "\<exists>y. popular_value F y"
                by (metis (no_types, lifting) HOL.ext False assms(1,2) ex_popular_value_iff
                    F memb_Exp_imp_small_function)
              ultimately show ?thesis
                using F by blast
            qed
            thus ?thesis
              using F by auto
          qed
          moreover have "range F \<subseteq> Set b \<union> {null}"
            using F by blast
          ultimately
          show "F \<in> {F. small_function F \<and> SF_Dom F \<subseteq> Set a \<and> range F \<subseteq> Set b \<union> {null}}"
            by blast
        qed
        thus ?thesis
          using False small_funcset [of "Set a" "Set b \<union> {null}"]
                small_Set assms(1,2) smaller_than_small
          by fastforce
        next
        case True
        have "Exp a b \<subseteq> {F. small_function F \<and> SF_Dom F \<subseteq> UNIV \<and> range F \<subseteq> Set b \<union> {null}}"
          using assms memb_Exp_imp_small_function by auto
        thus ?thesis
          using True small_funcset [of UNIV "Set b \<union> {null}"]
                small_Set assms(1,2) smaller_than_small
          by (metis (mono_tags, lifting) subset_UNIV)
      qed
    qed

    lemma embeds_Exp:
    assumes "ide a" and "ide b"
    shows "embeds (Exp a b)"
    proof -
      have "is_embedding_of some_embedding_of_small_functions (Exp a b)"
      proof -
        have "Exp a b \<subseteq> SEF"
          unfolding EF_def
          using assms memb_Exp_imp_small_function by blast
        thus ?thesis
          using assms some_embedding_of_small_functions_is_embedding memb_Exp_popular_value
          by (meson image_mono inj_on_subset subset_trans)
      qed
      thus ?thesis by blast
    qed

    lemma ide_exp:
    assumes "ide a" and "ide b"
    shows "ide (exp a b)"
    and "bij_betw (OUT (Exp a b)) (Set (exp a b)) (Exp a b)"
    and "bij_betw (IN (Exp a b)) (Exp a b) (Set (exp a b))"
    proof -
      have "small (Exp a b)"
        using assms small_Exp by blast
      moreover have "embeds (Exp a b)"
        using assms embeds_Exp by blast
      ultimately show "ide (exp a b)" and "bij_betw (OUT (Exp a b)) (Set (exp a b)) (Exp a b)"
        unfolding exp_def
        using assms ide_mkide bij_OUT by blast+
      thus "bij_betw (IN (Exp a b)) (Exp a b) (Set (exp a b))"
        using bij_betw_inv_into exp_def by fastforce
    qed

    abbreviation Eval
    where "Eval b c \<equiv> (\<lambda>fx. if fx \<in> Set (prod (exp b c) b)
                             then OUT (Exp b c)
                                    (Fun (pr\<^sub>1 (exp b c) b) fx)
                                    (Fun (pr\<^sub>0 (exp b c) b) fx)
                             else null)"

    definition eval
    where "eval b c \<equiv> mkarr (prod (exp b c) b) c (Eval b c)"

    lemma eval_in_hom [intro, simp]:
    assumes "ide b" and "ide c"
    shows "\<guillemotleft>eval b c : prod (exp b c) b \<rightarrow> c\<guillemotright>"
    proof (unfold eval_def, intro mkarr_in_hom)
      show "ide c" by fact
      show "ide (prod (exp b c) b)"
        using assms ide_exp ide_prod by auto
      show "Eval b c \<in> Hom (prod (exp b c) b) c"
      proof
        show "Eval b c \<in> Set (prod (exp b c) b) \<rightarrow> Set c"
        proof
          fix fx
          assume fx: "fx \<in> Set (prod (exp b c) b)"
          have "Eval b c fx = OUT (Exp b c) (Fun (pr\<^sub>1 (exp b c) b) fx)
                                (Fun (pr\<^sub>0 (exp b c) b) fx)"
            using fx by simp
          moreover have "... \<in> Set c"
          proof -
            have "OUT (Exp b c) (Fun (pr\<^sub>1 (exp b c) b) fx) \<in> Exp b c"
            proof -
              have "Fun (pr\<^sub>1 (exp b c) b) fx \<in> Set (exp b c)"
                using assms fx Fun_def
                by (simp add: comp_in_homI ide_exp(1))
              thus ?thesis
                using assms(1,2) bij_betwE ide_exp(2) by blast
            qed
            moreover have "Fun (pr\<^sub>0 (exp b c) b) fx \<in> Set b"
              using assms(1,2) fx ide_exp(1) Fun_def by auto
            ultimately show ?thesis by blast
          qed
          ultimately show "Eval b c fx \<in> Set c" by auto
        qed
        show "Eval b c \<in> {F. \<forall>x. x \<notin> Set (prod (exp b c) b) \<longrightarrow> F x = null}"
          by simp
      qed
    qed

    lemma eval_simps [simp]:
    assumes "ide b" and "ide c"
    shows "arr (eval b c)" and "dom (eval b c) = prod (exp b c) b" and "cod (eval b c) = c"
      using assms eval_in_hom by blast+

    lemma Fun_eval:
    assumes "ide b" and "ide c"
    shows "Fun (eval b c) = Eval b c"
      using assms eval_def Fun_mkarr [of "prod (exp b c) b" c "Eval b c"]
      by (metis arrI eval_in_hom)

    definition Curry
    where "Curry a b c \<equiv> \<lambda>f. if \<guillemotleft>f : prod a b \<rightarrow> c\<guillemotright>
                             then mkarr a (exp b c)
                                    (\<lambda>x. if x \<in> Set a
                                         then IN (Exp b c)
                                                (\<lambda>y. if y \<in> Set b
                                                     then C f (tuple x y)
                                                     else null)
                                         else null)
                             else null"

    lemma Curry_in_hom [intro]:
    assumes "ide a" and "ide b" and "ide c"
    and "\<guillemotleft>f : prod a b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>Curry a b c f : a \<rightarrow> exp b c\<guillemotright>"
    and "Fun (Curry a b c f) =
             (\<lambda>x. if x \<in> Set a
                  then IN (Exp b c) (\<lambda>y. if y \<in> Set b then C f (tuple x y) else null)
                  else null)"
    proof -
      have "\<And>x. x \<in> Set a \<Longrightarrow>
                  IN (Exp b c) (\<lambda>y. if y \<in> Set b then C f (tuple x y) else null)
                    \<in> Set (exp b c)"
      proof -
        fix x
        assume x: "x \<in> Set a"
        have "(\<lambda>y. if y \<in> Set b then C f (tuple x y) else null) \<in> Exp b c"
        proof -
          have "\<And>y. y \<in> Set b \<Longrightarrow> C f (tuple x y) \<in> Set c"
            using assms x by auto
          thus ?thesis by simp
        qed
        thus "IN (Exp b c) (\<lambda>y. if y \<in> Set b then C f (tuple x y) else null)
                \<in> Set (exp b c)"
          using assms bij_betwE ide_exp
          by (metis (no_types, lifting))
      qed
      thus "\<guillemotleft>Curry a b c f : a \<rightarrow> exp b c\<guillemotright>"
        unfolding Curry_def
        using assms ide_exp
        by (simp, intro mkarr_in_hom, auto)
      show "Fun (Curry a b c f) =
             (\<lambda>x. if x \<in> Set a
                  then IN (Exp b c) (\<lambda>y. if y \<in> Set b then C f (tuple x y) else null)
                  else null)"
        using \<open>\<guillemotleft>Curry a b c f : a \<rightarrow> exp b c\<guillemotright>\<close> arrI assms(4) Curry_def app_mkarr
        by auto
    qed

    lemma Curry_simps [simp]:
    assumes "ide a" and "ide b" and "ide c"
    and "\<guillemotleft>f : prod a b \<rightarrow> c\<guillemotright>"
    shows "arr (Curry a b c f)" and "dom (Curry a b c f) = a" and "cod (Curry a b c f) = exp b c"
      using assms Curry_in_hom by blast+

    lemma Fun_Curry:
    assumes "ide a" and "ide b" and "ide c"
    and "\<guillemotleft>f : prod a b \<rightarrow> c\<guillemotright>"
    shows "Fun (Curry a b c f) =
             (\<lambda>x. if x \<in> Set a
                  then IN (Exp b c) (\<lambda>y. if y \<in> Set b then C f (tuple x y) else null)
                  else null)"
      using assms Curry_in_hom(2) by blast

    interpretation elementary_category_with_terminal_object C \<open>\<one>\<^sup>?\<close> some_terminator
      using extends_to_elementary_category_with_terminal_object by blast

    lemma is_category_with_terminal_object:
    shows "elementary_category_with_terminal_object C \<one>\<^sup>? some_terminator"
    and "category_with_terminal_object C"
      ..

    interpretation elementary_cartesian_closed_category
                     C pr\<^sub>0 pr\<^sub>1 \<open>\<one>\<^sup>?\<close> some_terminator exp eval Curry
    proof
      show "\<And>b c. \<lbrakk>ide b; ide c\<rbrakk> \<Longrightarrow> \<guillemotleft>eval b c : prod (exp b c) b \<rightarrow> c\<guillemotright>"
        using eval_in_hom by blast
      show "\<And>b c. \<lbrakk>ide b; ide c\<rbrakk> \<Longrightarrow> ide (exp b c)"
        using ide_exp by blast
      show "\<And>a b c g. \<lbrakk>ide a; ide b; ide c; \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright>\<rbrakk>
               \<Longrightarrow> \<guillemotleft>Curry a b c g : a \<rightarrow> exp b c\<guillemotright>"
        using Curry_in_hom by simp
      show "\<And>a b c g. \<lbrakk>ide a; ide b; ide c; \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright>\<rbrakk>
              \<Longrightarrow> C (eval b c) (prod (Curry a b c g) b) = g"
      proof -
        fix a b c g
        assume a: "ide a" and b: "ide b" and c: "ide c" and g: "\<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright>"
        show "eval b c \<cdot> prod (Curry a b c g) b = g"
        proof (intro arr_eqI [of _ g])
          show par: "par (C (eval b c) (prod (Curry a b c g) b)) g"
            using a b c g by auto
          show "Fun (eval b c \<cdot> prod (Curry a b c g) b) = Fun g"
          proof
            fix x
            show "Fun (eval b c \<cdot> prod (Curry a b c g) b) x = Fun g x"
            proof (cases "x \<in> Set (prod a b)")
              case False
              show ?thesis
                using False Fun_def
                by (metis g in_homE par)
              next
              case True
              have "Fun (C (eval b c) (prod (Curry a b c g) b)) x =
                    Fun (eval b c) (Fun (prod (Curry a b c g) b) x)"
                using True a b c g Fun_comp par comp_assoc by auto
              also have "... =  (\<lambda>fx. if fx \<in> Set (prod (exp b c) b)
                                      then OUT (Exp b c) (Fun (pr\<^sub>1 (exp b c) b) fx)
                                             (Fun (pr\<^sub>0 (exp b c) b) fx)
                                      else null)
                                  ((if x \<in> Set (prod a b)
                                    then tuple
                                           (Fun (Curry a b c g) (pr\<^sub>1 a b \<cdot> x))
                                           (Fun b (pr\<^sub>0 a b \<cdot> x))
                                    else null))"
              proof -
                have "Fun (eval b c) = (\<lambda>fx. if fx \<in> Set (prod (exp b c) b)
                                             then OUT (Exp b c) (Fun (pr\<^sub>1 (exp b c) b) fx)
                                                    (Fun (pr\<^sub>0 (exp b c) b) fx)
                                             else null)"
                  using b c Fun_eval by simp
                moreover have "Fun (prod (Curry a b c g) b) =
                               (\<lambda>x. if x \<in> Set (prod a b)
                                    then tuple
                                           (Fun (Curry a b c g) (pr\<^sub>1 a b \<cdot> x))
                                           (Fun b (pr\<^sub>0 a b \<cdot> x))
                                    else null)"
                  using a b c g Fun_prod [of "Curry a b c g" a "exp b c" b b b] Curry_in_hom
                  by (meson ide_in_hom)
                ultimately show ?thesis by simp
              qed
              also have "... = OUT (Exp b c)
                                 (Fun (pr\<^sub>1 (exp b c) b)
                                    (tuple
                                       (Fun (Curry a b c g) (C (pr\<^sub>1 a b) x))
                                       (Fun b (C (pr\<^sub>0 a b) x))))
                                 (Fun (pr\<^sub>0 (exp b c) b)
                                    (tuple
                                       (Fun (Curry a b c g) (C (pr\<^sub>1 a b) x))
                                       (Fun b (C (pr\<^sub>0 a b) x))))"
               proof -
                 have "tuple
                         (Fun (Curry a b c g) (C (pr\<^sub>1 a b) x))
                         (Fun b (C (pr\<^sub>0 a b) x))
                            \<in> Set (prod (exp b c) b)"
                   using a b c g True Fun_def by auto
                 thus ?thesis
                   using True by presburger
               qed
              also have "... = OUT (Exp b c)
                                 (pr\<^sub>1 (exp b c) b \<cdot>
                                    tuple
                                      (Fun (Curry a b c g) (C (pr\<^sub>1 a b) x))
                                      (Fun b (C (pr\<^sub>0 a b) x)))
                                 (pr\<^sub>0 (exp b c) b \<cdot>
                                    tuple
                                      (Fun (Curry a b c g) (C (pr\<^sub>1 a b) x))
                                      (Fun b (C (pr\<^sub>0 a b) x)))"
              proof -
                have "tuple
                        (Fun (Curry a b c g) (C (pr\<^sub>1 a b) x))
                        (Fun b (C (pr\<^sub>0 a b) x))
                           \<in> Set (prod (exp b c) b)"
                  using a b c g True Fun_def by auto
                moreover have "Set (prod (exp b c) b) = Set (dom (pr\<^sub>1 (exp b c) b))"
                  using b c
                  by (simp add: ide_exp(1))
                moreover have "Set (prod (exp b c) b) = Set (dom (pr\<^sub>0 (exp b c) b))"
                  using b c
                  by (simp add: ide_exp(1))
                ultimately show ?thesis
                  unfolding Fun_def
                  using a b c g True by auto
              qed
              also have "... = OUT (Exp b c)
                                 (Fun (Curry a b c g) (C (pr\<^sub>1 a b) x))
                                 (Fun b (C (pr\<^sub>0 a b) x))"
                unfolding Fun_def
                using True a b c g by auto
              also have "... = OUT (Exp b c)
                                  (Fun (Curry a b c g) (C (pr\<^sub>1 a b) x))
                                  (C (pr\<^sub>0 a b) x)"
              proof -
                have "C (pr\<^sub>0 a b) x \<in> Set b"
                  using True a b by blast
                thus ?thesis
                  using b Fun_ide [of b]
                  by presburger
              qed
              also have "... = OUT (Exp b c)
                                 ((\<lambda>x. if x \<in> Set a
                                       then IN (Exp b c)
                                          (\<lambda>y. if y \<in> Set b then g \<cdot> tuple x y else null)
                                       else null)
                                     (C (pr\<^sub>1 a b) x))
                                 (C (pr\<^sub>0 a b) x)"
                using a b c g Fun_Curry [of a b c g] by simp
              also have "... = OUT (Exp b c)
                                 (IN (Exp b c)
                                    (\<lambda>y. if y \<in> Set b then g \<cdot> tuple (pr\<^sub>1 a b \<cdot> x) y else null))
                                    (pr\<^sub>0 a b \<cdot> x)"
                using True a b c g by auto
              also have "... = (\<lambda>y. if y \<in> Set b then g \<cdot> tuple (pr\<^sub>1 a b \<cdot> x) y else null)
                                  (pr\<^sub>0 a b \<cdot> x)"
              proof -
                have "(\<lambda>y. if y \<in> Set b then g \<cdot> tuple (pr\<^sub>1 a b \<cdot> x) y else null) \<in> Hom b c"
                proof
                  show "(\<lambda>y. if y \<in> Set b then g \<cdot> tuple (pr\<^sub>1 a b \<cdot> x) y else null) \<in> Set b \<rightarrow> Set c"
                  proof
                    fix y
                    assume y: "y \<in> Set b"
                    show "(if y \<in> Set b then g \<cdot> tuple (pr\<^sub>1 a b \<cdot> x) y else null) \<in> Set c"
                      using True a b c g y by auto
                  qed
                  show "(\<lambda>y. if y \<in> Set b then g \<cdot> tuple (pr\<^sub>1 a b \<cdot> x) y else null)
                           \<in> {F. \<forall>x. x \<notin> Set b \<longrightarrow> F x = null}"
                    by auto
                qed
                thus ?thesis
                  using a b c g small_Exp [of b c] embeds_Exp [of b c] ide_exp(1) [of b c]
                        OUT_IN
                          [of "Exp b c"
                              "\<lambda>y. if y \<in> Set b then g \<cdot> tuple (pr\<^sub>1 a b \<cdot> x) y else null"]
                  by auto
              qed
              also have "... = g \<cdot> tuple (pr\<^sub>1 a b \<cdot> x) (pr\<^sub>0 a b \<cdot> x)"
                using True a b c g by auto
              also have "... = g \<cdot> tuple (pr\<^sub>1 a b) (pr\<^sub>0 a b) \<cdot> x"
                using True a b c g comp_tuple_arr
                by (metis CollectD in_homE pr_simps(2) span_pr)
              also have "... = g \<cdot> x"
                using True a b tuple_pr comp_cod_arr by fastforce
              also have "... = Fun g x"
                using True g Fun_def by auto
              finally show ?thesis by blast
            qed
          qed
        qed
      qed
      show "\<And>a b c h. \<lbrakk>ide a; ide b; ide c; \<guillemotleft>h : a \<rightarrow> exp b c\<guillemotright>\<rbrakk>
                \<Longrightarrow> Curry a b c (C (eval b c) (prod h b)) = h"
      proof -
        fix a b c h
        assume a: "ide a" and b: "ide b" and c: "ide c" and h: "\<guillemotleft>h : a \<rightarrow> exp b c\<guillemotright>"
        show "Curry a b c (C (eval b c) (prod h b)) = h"
        proof (intro arr_eqI [of _ h])
          show par: "par (Curry a b c (C (eval b c) (prod h b))) h"
            using a b c h Curry_def Curry_simps(1) by auto
          show "Fun (Curry a b c (C (eval b c) (prod h b))) = Fun h"
          proof
            fix x
            show "Fun (Curry a b c (C (eval b c) (prod h b))) x = Fun h x"
            proof (cases "x \<in> Set a")
              case False
              show ?thesis
                using False a b c h
                by (metis Fun_def in_homE par)
              next
              case True
              have "OUT (Exp b c) (Fun (Curry a b c (C (eval b c) (prod h b))) x) =
                    OUT (Exp b c) 
                      (IN (Exp b c)
                         (\<lambda>y. if y \<in> Set b then (eval b c \<cdot> prod h b) \<cdot> tuple x y else null))"
                using True a b c h Fun_Curry [of a b c "C (eval b c) (prod h b)"]
                      eval_in_hom [of b c]
                by auto
              also have "... = (\<lambda>y. if y \<in> Set b then (eval b c \<cdot> prod h b) \<cdot> tuple x y else null)"
              proof -
                have "(\<lambda>y. if y \<in> Set b then (eval b c \<cdot> prod h b) \<cdot> tuple x y else null) \<in> Hom b c"
                proof
                  show "(\<lambda>y. if y \<in> Set b then (eval b c \<cdot> prod h b) \<cdot> tuple x y else null)
                           \<in> Set b \<rightarrow> Set c"
                  proof
                    fix y
                    assume y: "y \<in> Set b"
                    show "(if y \<in> Set b then (eval b c \<cdot> prod h b) \<cdot> tuple x y else null) \<in> Set c"
                      using True a b c h y ide_in_hom by auto
                  qed
                  show "(\<lambda>y. if y \<in> Set b then (eval b c \<cdot> prod h b) \<cdot> tuple x y else null)
                           \<in> {F. \<forall>x. x \<notin> Set b \<longrightarrow> F x = null}"
                    by simp
                qed
                thus ?thesis
                  using True a b c h small_Exp  [of b c] embeds_Exp ide_exp [of b c]
                        OUT_IN
                          [of "Exp b c"
                              "\<lambda>y. if y \<in> Set b then (eval b c \<cdot> prod h b) \<cdot> tuple x y else null"]
                  by auto
              qed
              also have "... = OUT (Exp b c) (Fun h x)"
              proof
                fix y
                show "... y = OUT (Exp b c) (Fun h x) y"
                proof (cases "y \<in> Set b")
                  assume y: "y \<notin> Set b"
                  have "\<guillemotleft>Fun h x : \<one>\<^sup>? \<rightarrow> mkide (Exp b c)\<guillemotright>"
                    using True b c h
                    by (metis Fun_arr[of h a "cod h"] arr_iff_in_hom[of "h \<cdot> x"]
                        dom_comp[of h x] cod_comp[of h x] exp_def[of b c]
                        in_homE[of h a "exp b c"] in_homE[of x "\<one>\<^sup>?" a]
                        mem_Collect_eq[of x "\<lambda>uub. \<guillemotleft>uub : \<one>\<^sup>? \<rightarrow> a\<guillemotright>"] seqI[of x h])
                  thus ?thesis
                    using True b c h y OUT_elem_of [of "Exp b c" "Fun h x"] small_Exp [of b c]
                          embeds_Exp [of b c] ide_exp [of b c]
                    by auto
                  next
                  assume y: "y \<in> Set b"
                  have "(\<lambda>y. if y \<in> Set b then (eval b c \<cdot> prod h b) \<cdot> tuple x y else null) y =
                        (eval b c \<cdot> prod h b) \<cdot> tuple x y"
                    using y by simp
                  also have "... = eval b c \<cdot> (prod h b \<cdot> tuple x y)"
                    using comp_assoc by simp
                  also have "... = eval b c \<cdot> tuple (h \<cdot> x) (b \<cdot> y)"
                    using True b c h y prod_tuple
                    by (metis comp_cod_arr in_homE mem_Collect_eq seqI)
                  also have "... = eval b c \<cdot> tuple (h \<cdot> x) y"
                    using b y
                    by (metis comp_cod_arr in_homE mem_Collect_eq)
                  also have "... = Fun (eval b c) (tuple (h \<cdot> x) y)"
                    using True b c h y Fun_def [of "eval b c" "tuple (h \<cdot> x) y"] by auto
                  also have "... = (\<lambda>fx. if fx \<in> Set (prod (exp b c) b)
                                         then OUT (Exp b c) (Fun (pr\<^sub>1 (exp b c) b) fx)
                                                (Fun (pr\<^sub>0 (exp b c) b) fx)
                                         else null)
                                      (tuple (h \<cdot> x) y)"
                    using b c Fun_eval [of b c] by presburger
                  also have "... = OUT (Exp b c) (Fun (pr\<^sub>1 (exp b c) b) (tuple (h \<cdot> x) y))
                                     (Fun (pr\<^sub>0 (exp b c) b) (tuple (h \<cdot> x) y))"
                    using True b c h y
                    by (simp add: comp_in_homI tuple_in_hom)
                  also have "... = OUT (Exp b c) (pr\<^sub>1 (exp b c) b \<cdot> tuple (h \<cdot> x) y)
                                     (pr\<^sub>0 (exp b c) b \<cdot> tuple (h \<cdot> x) y)"
                    using True b c h y Fun_def ide_exp(1) span_pr by auto
                  also have "... = OUT (Exp b c) (h \<cdot> x) y"
                    using True b c h y
                    apply auto
                    by fastforce
                  also have "... = OUT (Exp b c) (Fun h x) y"
                    using True h Fun_def by auto
                  finally show "(if y \<in> Set b then (eval b c \<cdot> prod h b) \<cdot> tuple x y else null) =
                                OUT (Exp b c) (Fun h x) y"
                    by blast
                qed
              qed
              finally have *: "OUT (Exp b c) (Fun (Curry a b c (C (eval b c) (prod h b))) x) =
                               OUT (Exp b c) (Fun h x)"
                by simp
              show "Fun (Curry a b c (C (eval b c) (prod h b))) x = Fun h x"
              proof -
                have "Fun (Curry a b c (C (eval b c) (prod h b))) x =
                      IN (Exp b c) (OUT (Exp b c) (Fun (Curry a b c (C (eval b c) (prod h b))) x))"
                proof -
                  have "Fun (Curry a b c (eval b c \<cdot> prod h b)) x \<in> Set (mkide (Exp b c))"
                  proof -
                    have "\<guillemotleft>Curry a b c (eval b c \<cdot> prod h b) : a \<rightarrow> exp b c\<guillemotright>"
                      using a b c h par
                            Curry_in_hom [of a b c "C (eval b c) (prod h b)"]
                      by (metis arr_iff_in_hom in_homE)
                    hence "Fun (Curry a b c (eval b c \<cdot> prod h b)) \<in> Set a \<rightarrow> Set (exp b c)"
                      using Fun_in_Hom [of "Curry a b c (eval b c \<cdot> prod h b)" a "exp b c"]
                      by blast
                    thus ?thesis
                      using True exp_def by auto
                  qed
                  thus ?thesis
                    using True a b c h small_Exp embeds_Exp
                          IN_OUT [of "Exp b c" "Fun (Curry a b c (C (eval b c) (prod h b))) x"]
                    by presburger
                qed
                also have "... = IN (Exp b c) (OUT (Exp b c) (Fun h x))"
                  using * by simp
                also have "... = Fun h x"
                proof -
                  have "Fun h x \<in> Set (mkide (Exp b c))"
                    using True b c h Fun_def exp_def by auto
                  thus ?thesis
                    using True b c h small_Exp embeds_Exp
                          IN_OUT [of "Exp b c" "Fun h x"]
                    by presburger
                qed
                finally show ?thesis by blast
              qed
            qed
          qed
        qed
      qed
    qed

    lemma is_elementary_cartesian_closed_category:
    shows "elementary_cartesian_closed_category C pr\<^sub>0 pr\<^sub>1 \<one>\<^sup>? some_terminator exp eval Curry"
      ..

    lemma is_cartesian_closed_category:
    shows "cartesian_closed_category C"
      ..

  end

  subsection "Exported Notions"

  context sets_cat_with_tupling
  begin

    sublocale sets_cat_with_pairing ..

    interpretation Expos: exponentials_in_sets_cat sml C ..

    abbreviation Exp
    where "Exp \<equiv> Expos.Exp"

    abbreviation exp
    where "exp \<equiv> Expos.exp"

    lemma ide_exp:
    assumes "ide a" and "ide b"
    shows "ide (exp a b)"
      using assms Expos.ide_exp by blast

    lemma exp_comparison_map_props:
    assumes "ide a" and "ide b"
    shows "OUT (Exp a b) \<in> Set (exp a b) \<rightarrow> Exp a b"
    and "IN (Exp a b) \<in> Exp a b \<rightarrow> Set (exp a b)"
    and "\<And>x. x \<in> Set (exp a b) \<Longrightarrow> IN (Exp a b) (OUT (Exp a b) x) = x"
    and "\<And>y. y \<in> Exp a b \<Longrightarrow> OUT (Exp a b) (IN (Exp a b) y) = y"
    and "bij_betw (OUT (Exp a b)) (Set (exp a b)) (Exp a b)"
    and "bij_betw (IN (Exp a b)) (Exp a b) (Set (exp a b))"
    proof -
      show "OUT (Exp a b) \<in> Set (exp a b) \<rightarrow> Exp a b"
        using assms Expos.ide_exp(2) [of a b] bij_betw_def bij_betw_imp_funcset
        by simp
      thus "IN (Exp a b) \<in> Exp a b \<rightarrow> Set (exp a b)"
        using assms Expos.exp_def
        by (metis (no_types, lifting) HOL.ext Expos.ide_exp(2) bij_betw_imp_funcset bij_betw_inv_into)
      show "\<And>x. x \<in> Set (exp a b) \<Longrightarrow> IN (Exp a b) (OUT (Exp a b) x) = x"
        using assms
        by (metis (no_types, lifting) HOL.ext Expos.exp_def Expos.ide_exp(2) bij_betw_inv_into_left)
      show "\<And>y. y \<in> Exp a b \<Longrightarrow> OUT (Exp a b) (IN (Exp a b) y) = y"
        using assms
        by (metis (no_types, lifting) HOL.ext Expos.exp_def Expos.ide_exp(2) bij_betw_inv_into_right)
      show "bij_betw (OUT (Exp a b)) (Set (exp a b)) (Exp a b)"
        using assms Expos.exponentials_in_sets_cat_axioms exponentials_in_sets_cat.ide_exp(2)
        by fastforce
      show "bij_betw (IN (Exp a b)) (Exp a b) (Set (exp a b))"
        using assms Expos.exponentials_in_sets_cat_axioms exponentials_in_sets_cat.ide_exp(3)
        by fastforce
    qed

    abbreviation Eval
    where "Eval \<equiv> Expos.Eval"

    abbreviation eval
    where "eval \<equiv> Expos.eval"

    lemma eval_in_hom [intro, simp]:
    assumes "ide b" and "ide c"
    shows "\<guillemotleft>eval b c : prod (exp b c) b \<rightarrow> c\<guillemotright>"
      using assms Expos.eval_in_hom by blast

    lemma eval_simps [simp]:
    assumes "ide b" and "ide c"
    shows "arr (eval b c)" and "dom (eval b c) = prod (exp b c) b" and "cod (eval b c) = c"
      using assms Expos.eval_simps by auto

    lemma Fun_eval:
    assumes "ide b" and "ide c"
    shows "Fun (eval b c) = Eval b c"
      unfolding eval_def
      using assms Expos.Fun_eval [of b c] by simp

    abbreviation Curry
    where "Curry \<equiv> Expos.Curry"

    lemma Curry_in_hom [intro, simp]:
    assumes "ide a" and "ide b" and "ide c"
    and "\<guillemotleft>f : prod a b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>Curry a b c f : a \<rightarrow> exp b c\<guillemotright>"
      using assms Expos.Curry_in_hom by auto

    lemma Curry_simps [simp]:
    assumes "ide a" and "ide b" and "ide c"
    and "\<guillemotleft>f : prod a b \<rightarrow> c\<guillemotright>"
    shows "arr (Curry a b c f)"
    and "dom (Curry a b c f) = a" and "cod (Curry a b c f) = exp b c"
      using assms Expos.Curry_simps by auto

    lemma Fun_Curry:
    assumes "ide a" and "ide b" and "ide c"
    and "\<guillemotleft>f : prod a b \<rightarrow> c\<guillemotright>"
    shows "Fun (Curry a b c f) =
           (\<lambda>x. if x \<in> Set a
                then IN (Exp b c) (\<lambda>y. if y \<in> Set b then C f (tuple x y) else null)
                else null)"
      using assms Expos.Fun_Curry by blast

    theorem is_cartesian_closed:
    shows "elementary_cartesian_closed_category C pr\<^sub>0 pr\<^sub>1 \<one>\<^sup>? some_terminator exp eval Curry"
    and "cartesian_closed_category C"
      using Expos.is_elementary_cartesian_closed_category Expos.is_cartesian_closed_category
      by auto

  end

  section "Subobject Classifier"

  text\<open>
    In this section we show that a sets category has a subobject classifier,
    which is a categorical formulation of set comprehension.  We give here a formal
    definition of subobject classifier, because we have not done that elsewhere
    to date, but ultimately this definition would perhaps be better placed with
    a development of the theory of elementary topoi, which are cartesian closed
    categories with subobject classifier.
  \<close>

  context category
  begin

    text\<open>
      A subobject classifier is a monomorphism \<open>tt\<close> from a terminal object into
      an object \<open>\<Omega>\<close>, which we may regard as an ``object of truth values'',
      such that for every monomorphism \<open>m\<close> there exists a unique arrow \<open>\<chi> : cod m \<rightarrow> \<Omega>\<close>,
      such that \<open>m\<close> is given by the pullback of \<open>tt\<close> along \<open>\<chi>\<close>.
    \<close>

    definition subobject_classifier
    where "subobject_classifier tt \<equiv>
             mono tt \<and> terminal (dom tt) \<and>
               (\<forall>m. mono m \<longrightarrow>
                      (\<exists>!\<chi>. \<guillemotleft>\<chi> : cod m \<rightarrow> cod tt\<guillemotright> \<and>
                            has_as_pullback tt \<chi> (THE f. \<guillemotleft>f : dom m \<rightarrow> dom tt\<guillemotright>) m))"

    lemma subobject_classifierI [intro]:
    assumes "\<guillemotleft>tt : one \<rightarrow> \<Omega>\<guillemotright>" and "terminal one" and "mono tt"
    and "\<And>m. mono m \<Longrightarrow> \<exists>!\<chi>. \<guillemotleft>\<chi> : cod m \<rightarrow> \<Omega>\<guillemotright> \<and>
                               has_as_pullback tt \<chi> (THE f. \<guillemotleft>f : dom m \<rightarrow> one\<guillemotright>) m"
    shows "subobject_classifier tt"
      using assms subobject_classifier_def by blast

    lemma subobject_classifierE [elim]:
    assumes "subobject_classifier tt"
    and "\<lbrakk>mono tt; terminal (dom tt);
          \<And>m. mono m \<Longrightarrow> \<exists>!\<chi>. \<guillemotleft>\<chi> : cod m \<rightarrow> cod tt\<guillemotright> \<and>
                                has_as_pullback tt \<chi> (THE f. \<guillemotleft>f : dom m \<rightarrow> dom tt\<guillemotright>) m\<rbrakk>
             \<Longrightarrow> T"
    shows T
      using assms subobject_classifier_def by force

  end

  locale category_with_subobject_classifier =
    category +
  assumes has_subobject_classifier_ax: "\<exists>tt. subobject_classifier tt"
  begin

    sublocale category_with_terminal_object
      using category_axioms category_with_terminal_object.intro
            category_with_terminal_object_axioms_def has_subobject_classifier_ax
      by force

  end

  context sets_cat_with_bool
  begin

    text\<open>
      For a sets category, the two-point object \<open>\<^bold>\<two>\<close> (which exists in the current context
      @{locale sets_cat_with_bool}) serves as the object of truth values.
      The subobject classifier will be the arrow \<open>tt : \<one>\<^sup>? \<rightarrow> \<^bold>\<two>\<close>.

      Here we define a mapping \<open>\<chi>\<close> that takes a monomorphism \<open>m\<close> to a corresponding
      ``predicate'' \<open>\<chi> m : cod m \<rightarrow> \<^bold>\<two>\<close>.
    \<close>

    abbreviation Chi
    where "Chi m \<equiv> \<lambda>y. if y \<in> Set (cod m)
                       then
                         if y \<in> Fun m ` Set (dom m) then tt else ff
                       else null"

    definition \<chi> :: "'U \<Rightarrow> 'U"
    where "\<chi> m \<equiv> mkarr (cod m) \<^bold>\<two> (Chi m)"

    lemma \<chi>_in_hom [intro, simp]:
    assumes "\<guillemotleft>m : b \<rightarrow> a\<guillemotright>" and "mono m"
    shows "\<guillemotleft>\<chi> m : a \<rightarrow> \<^bold>\<two>\<guillemotright>"
      using assms ide_two ff_in_hom tt_in_hom \<chi>_def mkarr_in_hom by auto

    lemma \<chi>_simps [simp]:
    assumes "\<guillemotleft>m : b \<rightarrow> a\<guillemotright>" and "mono m"
    shows "arr (\<chi> m)" and "dom (\<chi> m) = a" and "cod (\<chi> m) = \<^bold>\<two>"
      using assms \<chi>_in_hom by blast+

    lemma Fun_\<chi>:
    assumes "\<guillemotleft>m : b \<rightarrow> a\<guillemotright>" and "mono m"
    shows "Fun (\<chi> m) = Chi m"
      unfolding \<chi>_def
      using assms Fun_mkarr
      by (metis (no_types, lifting) \<chi>_def \<chi>_in_hom arrI)

    lemma bij_Fun_mono:
    assumes "\<guillemotleft>m : b \<rightarrow> a\<guillemotright>" and "mono m"
    shows "bij_betw (Fun m) (Set b) {y. y \<in> Set a \<and> \<chi> m \<cdot> y = tt}"
    proof -
      have "{y. y \<in> Set a \<and> \<chi> m \<cdot> y = tt} = {y. y \<in> Set a \<and> Chi m y = tt}"
      proof -
        have "\<And>y. y \<in> Set a \<Longrightarrow> \<chi> m \<cdot> y = tt \<longleftrightarrow> Chi m y = tt"
          by (metis Fun_\<chi> Fun_arr \<chi>_in_hom assms(1,2))
        thus ?thesis by blast
      qed
      moreover have "bij_betw (Fun m) (Set b) {y. y \<in> Set a \<and> Chi m y = tt}"
        unfolding bij_betw_def
        using assms mono_char tt_def ff_def tt_ne_ff Fun_def by auto
      ultimately show ?thesis by simp
    qed

    lemma has_subobject_classifier:
    shows "subobject_classifier tt"
    proof
      show "\<guillemotleft>tt : \<one>\<^sup>? \<rightarrow> \<^bold>\<two>\<guillemotright>"
        using tt_in_hom by blast
      show "terminal \<one>\<^sup>?"
        using terminal_some_terminal by blast
      show "mono tt"
        using mono_tt by blast
      fix m
      assume m: "mono m"
      define b where b_def: "b = dom m"
      define a where a_def: "a = cod m"
      have m: "\<guillemotleft>m : b \<rightarrow> a\<guillemotright> \<and> mono m"
        using m a_def b_def mono_implies_arr by blast
      have bij_Fun_m: "bij_betw (Fun m) (Set b) {y \<in> Set a. \<chi> m \<cdot> y = tt}"
        using m bij_Fun_mono by presburger
      have "\<exists>!\<chi>. \<guillemotleft>\<chi> : a \<rightarrow> \<^bold>\<two>\<guillemotright> \<and> has_as_pullback tt \<chi> \<t>\<^sup>?[b] m"
      proof -
        have 1: "\<guillemotleft>\<chi> m : a \<rightarrow> \<^bold>\<two>\<guillemotright>"
          using m \<chi>_in_hom by blast
        moreover have 2: "has_as_pullback tt (\<chi> m) \<t>\<^sup>?[b] m"
        proof
          show cs: "commutative_square tt (\<chi> m) \<t>\<^sup>?[b] m"
          proof
            show "cospan tt (\<chi> m)"
              by (metis (lifting) \<chi>_in_hom arr_iff_in_hom m in_homE mono_char tt_simps(1,3))
            show span: "span \<t>\<^sup>?[b] m"
              using m by auto
            show "dom tt = cod \<t>\<^sup>?[b]"
              using m by auto
            show "tt \<cdot> \<t>\<^sup>?[b] = \<chi> m \<cdot> m"
            proof (intro arr_eqI)
              show par: "par (tt \<cdot> \<t>\<^sup>?[b]) (\<chi> m \<cdot> m)"
                using m \<open>span \<t>\<^sup>?[b] m\<close> a_def b_def by auto
              show "Fun (tt \<cdot> \<t>\<^sup>?[b]) = Fun (\<chi> m \<cdot> m)"
              proof
                fix x
                show "Fun (tt \<cdot> \<t>\<^sup>?[b]) x = Fun (\<chi> m \<cdot> m) x"
                proof (cases "x \<in> Set b")
                  case False
                  show ?thesis
                    using False par m Fun_def by auto
                  next
                  case True
                  have "Fun (tt \<cdot> \<t>\<^sup>?[b]) x = Fun tt (Fun \<t>\<^sup>?[b] x)"
                    using Fun_comp par by auto
                  also have "... = (\<lambda>x. if x \<in> Set \<one>\<^sup>? then tt else null)
                                      (if x \<in> Set b then \<one>\<^sup>? else null)"
                    using Fun_some_terminator Fun_tt span b_def ide_dom by auto
                  also have "... = tt"
                    using True ide_in_hom ide_some_terminal by auto
                  also have "... = (\<lambda>x. if x \<in> Set a then tt else null) (Fun m x)"
                    using m True Fun_def
                    by (metis CollectD CollectI in_homE comp_in_homI)
                  also have "... = Chi m (Fun m x)"
                    using app_mkarr m Fun_def by auto
                  also have "... = Fun (\<chi> m) (Fun m x)"
                    using m Fun_\<chi> [of m b a] by simp
                  also have "... = Fun (\<chi> m \<cdot> m) x"
                    by (metis comp_eq_dest_lhs par Fun_comp)
                  finally show ?thesis by blast
                qed
              qed
            qed
          qed
          show "\<And>h k. commutative_square tt (\<chi> m) h k \<Longrightarrow> \<exists>!l. \<t>\<^sup>?[b] \<cdot> l = h \<and> m \<cdot> l = k"
          proof -
            fix h k
            assume hk: "commutative_square tt (\<chi> m) h k"
            have inj_m: "inj_on (Fun m) (Set b)"
              using m mono_char by blast
            have kx: "\<And>x. x \<in> Set (dom h) \<Longrightarrow> k \<cdot> x \<in> {y \<in> Set a. \<chi> m \<cdot> y = tt}"
            proof -
              fix x
              assume x: "x \<in> Set (dom h)"
              have "\<chi> m \<cdot> k \<cdot> x  = tt \<cdot> h \<cdot> x"
                using hk comp_assoc
                by (metis (no_types, lifting) commutative_squareE)
              hence "\<chi> m \<cdot> k \<cdot> x  = tt"
                by (metis (lifting) IntI Int_Collect comp_arr_dom comp_in_homI' in_homE
                    commutative_squareE hk ide_some_terminal ide_in_hom some_trm_eqI
                    tt_simps(2) x)
              thus "k \<cdot> x \<in> {y \<in> Set a. \<chi> m \<cdot> y = tt}"
                using hk comp_assoc
                by (metis (mono_tags, lifting) "1" dom_comp in_homE in_homI mem_Collect_eq
                    seqE tt_simps(1,2))
            qed
            let ?l = "mkarr (dom h) b
                        (\<lambda>x. if x \<in> Set (dom h) then inv_into (Set b) (Fun m) (k \<cdot> x) else null)"
            have l: "\<guillemotleft>?l : dom h \<rightarrow> b\<guillemotright>"
            proof (intro mkarr_in_hom)
              show "ide (dom h)"
                using hk ide_dom by blast
              show "ide b"
                using m by auto
              show "(\<lambda>x. if x \<in> Set (dom h) then inv_into (Set b) (Fun m) (k \<cdot> x) else null)
                       \<in> Hom (dom h) b"
              proof
                show "(\<lambda>x. if x \<in> Set (dom h) then inv_into (Set b) (Fun m) (k \<cdot> x) else null)
                         \<in> Set (dom h) \<rightarrow> Set b"
                proof
                  fix x
                  assume x: "x \<in> Set (dom h)"
                  have "inv_into (Set b) (Fun m) (k \<cdot> x) \<in> Set b \<and>
                                   Fun m (inv_into (Set b) (Fun m) (k \<cdot> x)) = k \<cdot> x"
                    using x bij_Fun_m kx
                    by (meson bij_betw_apply bij_betw_inv_into bij_betw_inv_into_right)
                  thus "(if x \<in> Set (dom h) then inv_into (Set b) (Fun m) (k \<cdot> x) else null)
                           \<in> Set b"
                    using x by presburger
                qed
                show "(\<lambda>x. if x \<in> Set (dom h) then inv_into (Set b) (Fun m) (k \<cdot> x) else null)
                         \<in> {F. \<forall>x. x \<notin> Set (dom h) \<longrightarrow> F x = null}"
                  by auto
              qed
            qed
            have "\<t>\<^sup>?[b] \<cdot> ?l = h"
              by (metis (lifting) commutative_square_def comp_cod_arr
                  elementary_category_with_terminal_object.trm_naturality
                  elementary_category_with_terminal_object.trm_one
                  extends_to_elementary_category_with_terminal_object hk in_homE l
                  tt_simps(2))
            moreover have "m \<cdot> ?l = k"
            proof (intro arr_eqI)
              show par: "par (m \<cdot> ?l) k"
                by (metis (no_types, lifting) HOL.ext \<chi>_simps(2) m cod_comp dom_comp seqI'
                    commutative_squareE hk in_homE l)
              show "Fun (m \<cdot> ?l) = Fun k"
              proof
                fix x
                show "Fun (m \<cdot> ?l) x = Fun k x"
                proof (cases "x \<in> Set (dom h)")
                  case False
                  show ?thesis
                    using False par commutative_square_def Fun_def by auto
                  next
                  case True
                  have "Fun (m \<cdot> ?l) x = Fun m (Fun ?l x)"
                    using True Fun_comp CollectI m comp_in_homI in_homE l comp_assoc par
                    by fastforce
                  also have "... = Fun m (inv_into (Set b) (Fun m) (k \<cdot> x))"
                    using True m app_mkarr l by auto
                  also have "... = k \<cdot> x"
                    using True bij_Fun_m bij_betw_inv_into_right kx by force
                  also have "... = Fun k x"
                    using True hk Fun_def by fastforce
                  finally show ?thesis by blast
                qed
              qed
            qed
            ultimately have 1: "\<t>\<^sup>?[b] \<cdot> ?l = h \<and> m \<cdot> ?l = k" by blast
            moreover have "\<And>l'. \<t>\<^sup>?[b] \<cdot> l' = h \<and> m \<cdot> l' = k \<Longrightarrow> l' = ?l"
              using m l
              by (metis (lifting) \<open>m \<cdot> ?l = k\<close> seqI' mono_cancel)
            ultimately show "\<exists>!l. \<t>\<^sup>?[b] \<cdot> l = h \<and> m \<cdot> l = k" by auto
          qed
        qed
        moreover have "\<And>\<chi>'. \<guillemotleft>\<chi>' : a \<rightarrow> \<^bold>\<two>\<guillemotright> \<and> has_as_pullback tt \<chi>' \<t>\<^sup>?[b] m \<Longrightarrow> \<chi>' = \<chi> m"
        proof -
          fix \<chi>'
          assume \<chi>': "\<guillemotleft>\<chi>' : a \<rightarrow> \<^bold>\<two>\<guillemotright> \<and> has_as_pullback tt \<chi>' \<t>\<^sup>?[b] m"
          show "\<chi>' = \<chi> m"
          proof (intro arr_eqI' [of \<chi>'])
            show "\<guillemotleft>\<chi>' : a \<rightarrow> \<^bold>\<two>\<guillemotright>"
              using \<chi>' by simp
            show "\<guillemotleft>\<chi> m : a \<rightarrow> \<^bold>\<two>\<guillemotright>"
              using "1" by force
            show "\<And>y. \<guillemotleft>y : \<one>\<^sup>? \<rightarrow> a\<guillemotright> \<Longrightarrow> \<chi>' \<cdot> y = \<chi> m \<cdot> y"
            proof -
              fix y
              assume y: "\<guillemotleft>y : \<one>\<^sup>? \<rightarrow> a\<guillemotright>"
              show "\<chi>' \<cdot> y = \<chi> m \<cdot> y"
              proof (cases "y \<in> Set a")
                case False  
                show ?thesis
                 using False y by blast
                next
                case True
                show ?thesis
                proof (cases "y \<in> Fun m ` Set b")
                  case True
                  obtain x where x: "x \<in> Set b \<and> y = Fun m x"
                    using True by blast
                  have "\<chi>' \<cdot> y = \<chi>' \<cdot> m \<cdot> x"
                    using x y Fun_def by auto
                  also have "... = tt \<cdot> \<one>\<^sup>?"
                    using \<chi>' x Fun_def
                    by (metis (no_types, lifting) HOL.ext Fun_some_terminator m 
                        commutative_square_def has_as_pullbackE ide_dom in_homE comp_assoc)
                  also have "... = \<chi> m \<cdot> m \<cdot> x"
                    using 1 2 x \<chi>_def app_mkarr m comp_arr_dom y Fun_def by auto
                  also have "... = \<chi> m \<cdot> y"
                    using x y Fun_def by auto
                  finally show ?thesis by blast
                  next
                  case False
                  have "\<chi>' \<cdot> y = ff"
                  proof -
                    have "\<chi>' \<cdot> y = tt \<Longrightarrow> False"
                    proof -
                      assume 3: "\<chi>' \<cdot> y = tt"
                      hence "commutative_square tt \<chi>' \<one>\<^sup>? y"
                        by (metis \<open>\<guillemotleft>\<chi>' : a \<rightarrow> \<^bold>\<two>\<guillemotright>\<close> commutative_squareI comp_arr_dom ideD(1,2,3)
                            ide_some_terminal in_homE tt_simps(1,2,3) y)
                      hence "\<exists>x. x \<in> Set b \<and> m \<cdot> x = y \<and> \<t>\<^sup>?[b] \<cdot> x = \<one>\<^sup>?"
                        using \<chi>' has_as_pullbackE [of tt \<chi>' "\<t>\<^sup>?[b]" m]
                        by (metis arr_iff_in_hom m dom_comp in_homE mem_Collect_eq seqE y)
                      thus False
                        using False \<chi>' m Fun_def by auto
                    qed
                    thus ?thesis
                      using Set_two \<chi>' y by blast
                  qed
                  also have "... = \<chi> m \<cdot> y"
                    using "1" False app_mkarr m y \<chi>_def by auto
                  finally show ?thesis by blast
                qed
              qed
            qed
          qed
        qed
        ultimately show "\<exists>!\<chi>. \<guillemotleft>\<chi> : a \<rightarrow> \<^bold>\<two>\<guillemotright> \<and> has_as_pullback tt \<chi> \<t>\<^sup>?[b] m"
          by blast
      qed
      moreover have "\<t>\<^sup>?[b] = (THE t. \<guillemotleft>t : dom m \<rightarrow> \<one>\<^sup>?\<guillemotright>)"
        using terminal_some_terminal the1_equality [of "\<lambda>t. \<guillemotleft>t : dom m \<rightarrow> \<one>\<^sup>?\<guillemotright>"]
        by (simp add: b_def m mono_implies_arr some_terminator_def)
      ultimately show "\<exists>!\<chi>. \<guillemotleft>\<chi> : cod m \<rightarrow> \<^bold>\<two>\<guillemotright> \<and>
                            has_as_pullback tt \<chi> (THE t. \<guillemotleft>t : dom m \<rightarrow> \<one>\<^sup>?\<guillemotright>) m"
        using m by auto
    qed

    sublocale category_with_subobject_classifier
      using has_subobject_classifier
      by unfold_locales auto

    lemma is_category_with_subobject_classifier:
    shows "category_with_subobject_classifier C"
      ..

  end

  section "Natural Numbers Object"

  text\<open>
    In this section we show that a sets category has a natural numbers object,
    assuming that the smallness notion is such that the set of natural numbers is small,
    and assuming that that the collection of arrows admits lifting, so that the category
    has infinitely many arrows.
  \<close>

  locale sets_cat_with_infinity =
    sets_cat sml C +
    small_nat sml +
    lifting \<open>Collect arr\<close>
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    abbreviation nat  ("\<^bold>N")
    where "nat \<equiv> mkide (UNIV :: nat set)"

    lemma ide_nat:
    shows "ide \<^bold>N"
    and "bij_betw (OUT (UNIV :: nat set)) (Set \<^bold>N) (UNIV :: nat set)"
    and "bij_betw (IN (UNIV :: nat set)) (UNIV :: nat set) (Set \<^bold>N)"
      using small_nat embeds_nat bij_OUT bij_IN by auto

    abbreviation Zero
    where "Zero \<equiv> \<lambda>x. if x \<in> Set \<one>\<^sup>? then IN (UNIV :: nat set) 0 else null"

    lemma Zero_in_Hom:
    shows "Zero \<in> Hom \<one>\<^sup>? \<^bold>N"
      using Pi_I' bij_betwE ide_nat(3) by fastforce

    definition zero
    where "zero \<equiv> mkarr \<one>\<^sup>? \<^bold>N Zero"

    lemma zero_in_hom [intro, simp]:
    shows "\<guillemotleft>zero : \<one>\<^sup>? \<rightarrow> \<^bold>N\<guillemotright>"
      using mkarr_in_hom [of "\<one>\<^sup>?" "\<^bold>N"] Zero_in_Hom ide_nat(1) ide_some_terminal zero_def
      by presburger

    lemma zero_simps [simp]:
    shows "arr zero" and "dom zero = \<one>\<^sup>?" and "cod zero = \<^bold>N"
      using zero_in_hom by blast+

    lemma Fun_zero:
    shows "Fun zero = Zero"
      using zero_def app_mkarr zero_in_hom zero_simps(2) by auto

    abbreviation Succ
    where "Succ \<equiv> \<lambda>x. if x \<in> Set \<^bold>N then IN (UNIV :: nat set) (Suc (OUT UNIV x)) else null"

    lemma Succ_in_Hom:
    shows "Succ \<in> Hom \<^bold>N \<^bold>N"
      using Pi_I' bij_betwE ide_nat(3) by fastforce

    definition succ
    where "succ \<equiv> mkarr \<^bold>N \<^bold>N Succ"

    lemma succ_in_hom [intro]:
    shows "\<guillemotleft>succ : \<^bold>N \<rightarrow> \<^bold>N\<guillemotright>"
      using Succ_in_Hom ide_nat(1) succ_def by auto

    lemma succ_simps [simp]:
    shows "arr succ" and "dom succ = \<^bold>N" and "cod succ = \<^bold>N"
      using succ_in_hom by blast+

    lemma Fun_succ:
    shows "Fun succ = Succ"
      using succ_def app_mkarr succ_in_hom succ_simps(2) by auto

    lemma nat_universality:
    assumes "\<guillemotleft>Z : \<one>\<^sup>? \<rightarrow> a\<guillemotright>" and "\<guillemotleft>S : a \<rightarrow> a\<guillemotright>"
    shows "\<exists>!f. \<guillemotleft>f : \<^bold>N \<rightarrow> a\<guillemotright> \<and> f \<cdot> zero = Z \<and> f \<cdot> succ = S \<cdot> f"
    proof -
      let ?F = "\<lambda>n. if n \<in> Set \<^bold>N then ((\<cdot>) S ^^ OUT (UNIV :: nat set) n) Z else null"
      have F: "?F \<in> Hom \<^bold>N a"
      proof
        show "?F \<in> {F. \<forall>x. x \<notin> Set (mkide (UNIV :: nat set)) \<longrightarrow> F x = null}" by simp
        show "?F \<in> Set \<^bold>N \<rightarrow> Set a"
        proof
          have 1: "\<And>k. ((\<cdot>) S ^^ k) Z \<in> Set a"
          proof -
            fix k
            show "((\<cdot>) S ^^ k) Z \<in> Set a"
              using assms by (induct k) auto
          qed
          fix n
          assume n: "n \<in> Set \<^bold>N"
          show "?F n \<in> Set a"
            using n 1 by auto
        qed
      qed
      let ?f = "mkarr \<^bold>N a ?F"
      have f: "\<guillemotleft>?f : \<^bold>N \<rightarrow> a\<guillemotright>"
        using mkarr_in_hom F assms(2) ide_nat(1) by auto
      have "\<guillemotleft>?f : \<^bold>N \<rightarrow> a\<guillemotright> \<and> ?f \<cdot> zero = Z \<and> ?f \<cdot> succ = S \<cdot> ?f"
      proof (intro conjI)
        show "\<guillemotleft>?f : \<^bold>N \<rightarrow> a\<guillemotright>" by fact
        show "?f \<cdot> zero = Z"
        proof (intro arr_eqI)
          show par: "par (?f \<cdot> zero) Z"
            using assms(1) f by fastforce
          show "Fun (?f \<cdot> zero) = Fun Z"
          proof -
            have "Fun (?f \<cdot> zero) = Fun ?f \<circ> Fun zero"
              using Fun_comp par by blast
            also have "... = ?F \<circ> Zero"
              using Fun_mkarr Fun_zero par by fastforce
            also have "... = Fun Z"
            proof
              fix x
              show "(?F \<circ> Zero) x = Fun Z x"
              proof (cases "x \<in> Set \<one>\<^sup>?")
                case False
                show ?thesis
                  using False par Fun_def by auto
                next
                case True
                have "(?F \<circ> Zero) x =
                      ((\<cdot>) S ^^ OUT (UNIV :: nat set) (IN (UNIV :: nat set) 0)) Z"
                  using True bij_betw_imp_surj_on ide_nat(3) by fastforce
                also have "... = ((\<cdot>) S ^^ 0) Z"
                  using OUT_IN [of "UNIV :: nat set" "0 :: nat"] small_nat embeds_nat
                  by simp
                also have "... = Fun Z x"
                  using True Fun_def
                  by (metis assms(1) comp_arr_dom funpow_0 ide_in_hom ide_some_terminal
                      in_homE mem_Collect_eq some_trm_eqI)
                finally show ?thesis by blast
              qed
            qed
            finally show ?thesis by blast
          qed
        qed
        show "?f \<cdot> succ = S \<cdot> ?f"
        proof (intro arr_eqI)
          show par: "par (?f \<cdot> succ) (S \<cdot> ?f)"
            using assms(2) f by fastforce
          show "Fun (?f \<cdot> succ) = Fun (S \<cdot> ?f)"
          proof -
            have "Fun (?f \<cdot> succ) = Fun ?f \<circ> Fun succ"
              using Fun_comp par by blast
            also have "... = Fun S \<circ> Fun ?f"
            proof
              fix x
              show "(Fun ?f \<circ> Fun succ) x = (Fun S \<circ> Fun ?f) x"
              proof (cases "x \<in> Set \<^bold>N")
                case False
                show ?thesis
                  using False f Fun_def by auto
                next
                case True
                have "(Fun ?f \<circ> Fun succ) x = ?F (succ \<cdot> x)"
                  using True f app_mkarr [of "\<^bold>N" a _ "succ \<cdot> x"] Fun_def by auto
                also have "... = ((\<cdot>) S ^^ OUT UNIV (succ \<cdot> x)) Z"
                  using True f by auto
                also have "... = ((\<cdot>) S ^^ Suc (OUT UNIV x)) Z"
                  by (metis (no_types, lifting) Fun_def Fun_succ True UNIV_I bij_betw_def
                      bij_betw_inv_into_left ide_nat(2,3) mem_Collect_eq rangeI succ_simps(2))
                also have "... = S \<cdot> ((\<cdot>) S ^^ OUT UNIV x) Z"
                  by auto
                also have "... = S \<cdot> ?F x"
                  using True by auto
                also have "... = S \<cdot> Fun ?f x"
                  using f by auto
                also have "... = Fun S (Fun ?f x)"
                  by (metis (no_types, lifting) CollectD CollectI Fun_def dom_comp in_homE
                      in_homI ext null_is_zero(2) seqE)
                also have "... = (Fun S \<circ> Fun ?f) x"
                  by simp
                finally show ?thesis by blast
              qed
            qed
            also have "... = Fun (S \<cdot> ?f)"
              using Fun_comp par by presburger
            finally show ?thesis by blast
          qed
        qed
      qed
      moreover have "\<And>f'. \<guillemotleft>f' : \<^bold>N \<rightarrow> a\<guillemotright> \<and> f' \<cdot> zero = Z \<and> f' \<cdot> succ = S \<cdot> f' \<longrightarrow> f' = ?f"
      proof (intro impI arr_eqI)
        fix f'
        assume f': "\<guillemotleft>f' : \<^bold>N \<rightarrow> a\<guillemotright> \<and> f' \<cdot> zero = Z \<and> f' \<cdot> succ = S \<cdot> f'"
        show par: "par f' ?f"
          using f f' by fastforce
        have *: "\<And>k. ((\<cdot>) S ^^ k) Z = Fun f' (IN UNIV k)"
        proof -
          fix k
          show "((\<cdot>) S ^^ k) Z = Fun f' (IN UNIV k)"
          proof (induct k)
            show "((\<cdot>) S ^^ 0) Z = Fun f' (IN (UNIV :: nat set) 0)"
              using f' app_mkarr
              unfolding zero_def
              by (metis (no_types, lifting) CollectI Fun_zero comp_arr_dom f' funpow_0
                  ide_in_hom ide_some_terminal in_homE zero_in_hom Fun_def)
            fix k
            assume ind: "((\<cdot>) S ^^ k) Z = Fun f' (IN UNIV k)"
            have "Fun f' (IN UNIV (Suc k)) = Fun f' (succ \<cdot> IN UNIV k)"
            proof -
              have "\<And>n. OUT UNIV (IN UNIV (n::nat)) = n"
                by (metis (no_types) bij_betw_inv_into_right ide_nat(2) iso_tuple_UNIV_I)
              thus ?thesis
                by (metis (no_types) Fun_def Fun_succ bij_betwE ide_nat(3) iso_tuple_UNIV_I
                    succ_simps(2))
            qed
            also have "... = f' \<cdot> succ \<cdot> IN UNIV k"
              using bij_betwE f' ide_nat(3) Fun_def by fastforce
            also have "... = (f' \<cdot> succ) \<cdot> IN UNIV k"
              using comp_assoc by simp
            also have "... = S \<cdot> Fun f' (IN UNIV k)"
              using f' bij_betw_apply ide_nat(3) comp_assoc Fun_def by fastforce
            also have "... = S \<cdot> ((\<cdot>) S ^^ k) Z"
              using ind by simp
            also have "... = ((\<cdot>) S ^^ Suc k) Z"
              by auto
            finally show "((\<cdot>) S ^^ Suc k) Z = Fun f' (IN UNIV (Suc k))"
              by simp
          qed
        qed
        show "Fun f' = Fun ?f"
        proof
          fix x
          show "Fun f' x = Fun ?f x"
          proof (cases "x \<in> Set \<^bold>N")
            case False
            show ?thesis
              using False par Fun_def by auto
            next
            case True
            have "Fun ?f x = ((\<cdot>) S ^^ OUT UNIV x) Z"
              using True app_mkarr f par by force
            also have "... = Fun f' (IN (UNIV :: nat set) (OUT UNIV x))"
              using * by simp
            also have "... = Fun f' x"
              using True IN_OUT small_nat embeds_nat by metis
            finally show ?thesis by simp
          qed
        qed
      qed
      ultimately show ?thesis by auto
    qed

    lemma has_natural_numbers_object:
    shows "\<exists>a z s. \<guillemotleft>z : \<one>\<^sup>? \<rightarrow> a\<guillemotright> \<and> \<guillemotleft>s : a \<rightarrow> a\<guillemotright> \<and>
                   (\<forall>a' z' s'. \<guillemotleft>z' : \<one>\<^sup>? \<rightarrow> a'\<guillemotright> \<and> \<guillemotleft>s' : a' \<rightarrow> a'\<guillemotright> \<longrightarrow>
                                (\<exists>!f. \<guillemotleft>f : a \<rightarrow> a'\<guillemotright> \<and> f \<cdot> z = z' \<and> f \<cdot> s = s' \<cdot> f))"
    proof -
      have "\<guillemotleft>zero : \<one>\<^sup>? \<rightarrow> nat\<guillemotright> \<and> \<guillemotleft>succ : nat \<rightarrow> nat\<guillemotright> \<and>
            (\<forall>a' z' s'. \<guillemotleft>z' : \<one>\<^sup>? \<rightarrow> a'\<guillemotright> \<and> \<guillemotleft>s' : a' \<rightarrow> a'\<guillemotright> \<longrightarrow>
                          (\<exists>!f. \<guillemotleft>f : nat \<rightarrow> a'\<guillemotright> \<and> f \<cdot> zero = z' \<and> f \<cdot> succ = s' \<cdot> f))"
        using nat_universality by auto
      thus ?thesis by auto
    qed

  end

  section "Sets Category with Tupling and Infinity"

  text\<open>
    Finally, if the collection of arrows of a sets category admits embeddings of all the
    usual set-theoretic constructions, then the category supports all of the constructions
    considered; in particular it is small-complete and small-cocomplete, is cartesian closed,
    has a subobject classifier (so that it is an elementary topos), and validates an
    axiom of infinity in the form of the existence of a natural numbers object.
  \<close>

  context sets_cat_with_tupling
  begin

    lemmas is_well_pointed epis_split has_binary_products has_binary_coproducts
            has_small_products has_small_coproducts has_equalizers has_coequalizers
            is_cartesian_closed has_subobject_classifier

  end

  locale sets_cat_with_tupling_and_infinity =
    sets_cat_with_tupling sml C +
    sets_cat_with_infinity sml C
  for sml :: "'V set \<Rightarrow> bool"
  and C :: "'U comp"  (infixr \<open>\<cdot>\<close> 55)
  begin

    sublocale universe sml \<open>Collect arr\<close> null ..

    lemmas has_natural_numbers_object

  end

end
