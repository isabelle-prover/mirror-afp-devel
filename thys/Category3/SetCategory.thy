(*  Title:       SetCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter SetCategory

theory SetCategory
imports Category Functor
begin

  text{*
    This theory defines a locale @{text set_category} that axiomatizes the notion
    ``category of all @{typ 'a}-sets and functions between them'' in the context of HOL.
    A primary reason for doing this is to make it possible to prove results
    (such as the Yoneda Lemma) that use such categories without having to commit to a
    particular element type @{typ 'a} and without having the results depend on the
    concrete details of a particular construction.
    The axiomatization given here is categorical, in the sense that if categories
    @{term S} and @{term S'} each interpret the @{text set_category} locale,
    then a bijection between the sets of terminal objects of @{term S} and @{term S'}
    extends to an isomorphism of @{term S} and @{term S'} as categories.

    The axiomatization is based on the following idea: if, for some type @{typ 'a},
    category @{term S} is the category of all @{typ 'a}-sets and functions between
    them, then the elements of type @{typ 'a} are in bijective correspondence with
    the terminal objects of category @{term S}.  In addition, if @{term unity}
    is an arbitrarily chosen terminal object of @{term S}, then for each object @{term a},
    the hom-set @{term "hom unity a"} (\emph{i.e.} the set of ``points'' or
    ``global elements'' of @{term a}) is in bijective correspondence with a subset
    of the terminal objects of @{term S}.  By making a specific, but arbitrary,
    choice of such a correspondence, we can then associate with each object @{term a}
    of @{term S} a set @{term "set a"} that consists of all terminal objects @{term t}
    that correspond to some point @{term x} of @{term a}.  Each arrow @{term f}
    then induces a function @{text "Fun f \<in> set (dom f) \<rightarrow> set (cod f)"},
    defined on terminal objects of @{term S} by passing to points of @{term "dom f"},
    composing with @{term f}, then passing back from points of @{term "cod f"}
    to terminal objects.  Once we can associate a set with each object of @{term S}
    and a function with each arrow, we can force @{term S} to be isomorphic to the
    category of @{typ 'a}-sets by imposing suitable extensionality and completeness axioms.
  *}
 
  section "Some Lemmas about Restriction"

    text{*
      The development of the @{text set_category} locale makes heavy use of the
      theory @{theory FuncSet}.  However, in some cases, I found that @{theory FuncSet}
      did not provide results about restriction in the form that was most useful to me.
      I used the following additional results in various places.
    *}

  (* This variant of FuncSet.restrict_ext is sometimes useful. *)

  lemma restr_eqI:
  assumes "A = A'" and "\<And>x. x \<in> A \<Longrightarrow> F x = F' x"
  shows "restrict F A = restrict F' A'"
    using assms by force

  (* This rule avoided a long proof in at least one instance
     where FuncSet.restrict_apply did not work.
   *)
  lemma restr_eqE [elim]:
  assumes "restrict F A = restrict F' A" and "x \<in> A"
  shows "F x = F' x"
    using assms restrict_def by metis

  (* This seems more useful than compose_eq in FuncSet. *)
  lemma compose_eq' [iff]:
  shows "compose A G F = restrict (G o F) A"
    unfolding compose_def restrict_def by auto

  section "Set Categories"

  text{*
    We first define the locale @{text set_category_data}, which sets out the basic
    data and definitions for the @{text set_category} locale, without imposing any conditions
    other than that @{term S} is a category and that @{term img} is a function defined
    on the arrow type of @{term S}.  The function @{term img} should be thought of
    as a mapping that takes a point @{term "x \<in> hom unity a"} to a corresponding
    terminal object @{term "img x"}.  Eventually, assumptions will be introduced so
    that this is in fact the case.
  *}

  locale set_category_data = category S
  for S :: "'s comp"
  and img :: "'s \<Rightarrow> 's"
  begin

    text{*
      Call the set of all terminal objects of S the ``universe''.
    *}
    abbreviation Univ :: "'s set"
    where "Univ \<equiv> Collect terminal"
  
    text{*
      Choose an arbitrary element of the universe and call it @{term unity}.
    *}
    definition unity :: 's
    where "unity = (SOME t. terminal t)"
    
    text{*
      Each object @{term a} determines a subset @{term "set a"} of the universe,
      consisting of all those terminal objects @{term t} such that @{term "t = img x"}
      for some @{term "x \<in> hom unity a"}.
    *}
    definition set :: "'s \<Rightarrow> 's set"
    where "set a = img ` hom unity a"

    text{*
      The inverse of the map @{term set} is a map @{term mkIde} that takes each subset
      of the universe to an identity of @{term S}.
    *}
    definition mkIde :: "'s set \<Rightarrow> 's"
    where "mkIde A = (if A \<subseteq> Univ then inv_into (Collect ide) set A else null)"

  end

  text{*
    Next, we define a locale @{text set_category_given_img} that augments the
    @{text set_category_data} locale with assumptions that serve to define
    the notion of a set category with a chosen correspondence between points
    and terminal objects.  The assumptions require that the universe be nonempty
    (so that the definition of @{term unity} makes sense), that the map
    @{term img} is a locally injective map taking points to terminal objects,
    that each terminal object @{term t} belongs to @{term "set t"},
    that two objects of @{term S} are equal if they determine the same set,
    that two parallel arrows of @{term S} are equal if they determine the same
    function, that there is an object corresponding to each subset of the universe,
    and for any objects @{term a} and @{term b} and function
    @{term "F \<in> hom unity a \<rightarrow> hom unity b"} there is an arrow @{term "f \<in> hom a b"}
    whose action under the composition of @{term S} coincides with the function @{term F}.
  *}
    
  locale set_category_given_img = set_category_data S img
  for S :: "'s comp"
  and img :: "'s \<Rightarrow> 's" +
  assumes nonempty_Univ: "Univ \<noteq> {}"
  and img_mapsto: "ide a \<Longrightarrow> img \<in> hom unity a \<rightarrow> Univ"
  and inj_img: "ide a \<Longrightarrow> inj_on img (hom unity a)"
  and stable_img: "terminal t \<Longrightarrow> t \<in> img ` hom unity t"
  and extensional_set: "\<lbrakk> ide a; ide b; set a = set b \<rbrakk> \<Longrightarrow> a = b"
  and extensional_arr: "\<lbrakk> par f f'; \<And>x. x \<in> hom unity (dom f) \<Longrightarrow> S f x = S f' x \<rbrakk> \<Longrightarrow> f = f'"
  and set_complete: "A \<subseteq> Univ \<Longrightarrow> \<exists>a. ide a \<and> set a = A"
  and fun_complete1: "\<lbrakk> ide a; ide b; F \<in> hom unity a \<rightarrow> hom unity b \<rbrakk>
                          \<Longrightarrow> \<exists>f. f \<in> hom a b \<and> (\<forall>x. x \<in> hom unity a \<longrightarrow> S f x = F x)"
  begin
  
    text{*
      Each arrow @{term "f \<in> hom a b"} determines a function @{term "Fun f \<in> Univ \<rightarrow> Univ"},
      by passing from @{term Univ} to @{term "hom a unity"}, composing with @{term f},
      then passing back to @{term Univ}.
    *}

    definition Fun :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    where "Fun f = restrict (img o S f o inv_into (hom unity (dom f)) img) (set (dom f))"

    lemma comp_arr_point:
    assumes "arr f" and "x \<in> hom unity (dom f)"
    shows "S f x = inv_into (hom unity (cod f)) img (Fun f (img x))"
      using assms Fun_def set_def inj_img by simp
      
    text{*
      Parallel arrows that determine the same function are equal.
    *}

    lemma arr_eqI:
    assumes "par f f'" and "Fun f = Fun f'"
    shows "f = f'"
    proof -
      have "\<And>x. x \<in> hom unity (dom f) \<Longrightarrow> S f x = S f' x"
        using assms comp_arr_point by auto
      thus ?thesis using assms extensional_arr by blast
    qed

    lemma terminal_unity:
    shows "terminal unity"
      using unity_def nonempty_Univ someI_ex
      by (metis Collect_cong empty_def)

    lemma ide_unity [simp]:
    shows "ide unity"
      using terminal_unity terminal_def by blast

    lemma set_subset_Univ [simp]:
    assumes "ide a"
    shows "set a \<subseteq> Univ"
      using assms set_def img_mapsto by auto
  
    lemma inj_on_set:
    shows "inj_on set (Collect ide)"
    proof (intro inj_onI)
      fix a a'
      assume a: "a \<in> Collect ide" and a': "a' \<in> Collect ide" and aa': "set a = set a'"
      thus "a = a'" using extensional_set [of a a'] by blast
    qed
      
    text{*
      The mapping @{term mkIde}, which takes subsets of the universe to identities,
      and @{term set}, which takes identities to subsets of the universe, are inverses.
    *}

    lemma mkIde_set [simp]:
    assumes "ide a"
    shows "mkIde (set a) = a"
      using assms mkIde_def inj_on_set inv_into_f_f [of set "Collect ide" a] by simp

    lemma set_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "set (mkIde A) = A"
      using assms mkIde_def set_complete inv_into_def
            someI_ex [of "\<lambda>a. a \<in> Collect ide \<and> set a = A"]
            f_inv_into_f [of A set "Collect ide"]
      by fastforce
      
    lemma ide_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "ide (mkIde A)"
    proof -
      have "A \<subseteq> Univ" using assms by auto
      thus ?thesis using mkIde_def by (metis mkIde_set set_complete)
    qed
      
    lemma arr_mkIde [iff]:
    shows "arr (mkIde A) \<longleftrightarrow> A \<subseteq> Univ"
    proof
      assume A: "arr (mkIde A)"
      hence "mkIde A \<noteq> null" using not_arr_null by fastforce
      thus "A \<subseteq> Univ" using mkIde_def by metis
      next
      assume A: "A \<subseteq> Univ"
      thus "arr (mkIde A)" by simp
    qed
    
    lemma dom_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "dom (mkIde A) = mkIde A"
      using assms by simp
    
    lemma cod_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "cod (mkIde A) = mkIde A"
      using assms by simp
      
    text{*
      Each arrow @{term f} determines an extensional function from
      @{term "set (dom f)"} to @{term "set (cod f)"}.
    *}

    lemma Fun_mapsto:
    assumes "arr f"
    shows "Fun f \<in> extensional (set (dom f)) \<inter> (set (dom f) \<rightarrow> set (cod f))"
    proof
      show "Fun f \<in> extensional (set (dom f))" using Fun_def by fastforce
      show "Fun f \<in> set (dom f) \<rightarrow> set (cod f)"
      proof
        fix t
        assume t: "t \<in> set (dom f)"
        have "Fun f t = img (S f (inv_into (hom unity (dom f)) img t))"
          using assms t Fun_def restrict_apply comp_def by simp
        moreover have "img (S f (inv_into (hom unity (dom f)) img t)) \<in> set (cod f)"
        proof -
          have "inv_into (hom unity (dom f)) img t \<in> hom unity (dom f)"
            using assms t set_def img_mapsto inv_into_into
            by (metis (no_types, lifting) Collect_cong)
          hence "S f (inv_into (hom unity (dom f)) img t) \<in> hom unity (cod f)"
            using assms by force
          thus ?thesis
            using set_def by blast
        qed
        ultimately show "Fun f t \<in> set (cod f)" by auto
      qed
    qed
    
    text{*
      Identities of @{term S} correspond to restrictions of the identity function.
    *}

    lemma Fun_ide [simp]:
    assumes "ide a"
    shows "Fun a = restrict (\<lambda>x. x) (set a)"
    proof (unfold Fun_def)
      show "restrict (img o S a o (inv_into (hom unity (dom a)) img)) (set (dom a))
              = restrict (\<lambda>x. x) (set a)"
        using assms inj_img set_def by force
    qed
    
    lemma Fun_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "Fun (mkIde A) = restrict (\<lambda>x. x) A"
      using assms by simp
    
    text{*
      Composition in @{term S} corresponds to extensional function composition.
    *}

    lemma Fun_comp [simp]:
    assumes "seq g f"
    shows "Fun (S g f) = restrict (Fun g o Fun f) (set (dom f))"
    proof -
      have "restrict (img o S (S g f) o (inv_into (hom unity (dom (S g f))) img))
                     (set (dom (S g f)))
              = restrict (Fun g o Fun f) (set (dom f))"
      proof -
        have 1: "set (dom (S g f)) = set (dom f)" using assms by auto
        have 2: "\<And>t. t \<in> set (dom (S g f)) \<Longrightarrow>
                    (img o S (S g f) o (inv_into (hom unity (dom (S g f))) img)) t
                      = (Fun g o Fun f) t"
        proof -
          fix t
          assume "t \<in> set (dom (S g f))"
          hence t: "t \<in> set (dom f)" by (simp add: 1)
          let ?img' = "\<lambda>a. \<lambda>t. inv_into (hom unity a) img t"
          have 1: "\<And>a x. x \<in> hom unity a \<Longrightarrow> ?img' a (img x) = x"
            using assms img_mapsto inj_img ide_cod inv_into_f_eq by auto
          have 2: "?img' (dom f) t \<in> hom unity (dom f)"
            using assms t inv_into_into [of t img "hom unity (dom f)"] set_def [of "dom f"]
            by simp
          have "(img o S (S g f) o (inv_into (hom unity (dom (S g f))) img)) t
                   = img (S (S g f) (?img' (dom f) t))"
            using assms by simp
          also have "... = img (S g (S f (?img' (dom f) t)))"
            using assms 2 by simp
          also have "... = img (S g (?img' (dom g) (Fun f t)))"
            using assms t 1 Fun_def set_def inv_into_into by auto
          also have "... = Fun g (Fun f t)"
          proof -
            have "Fun f t \<in> img ` hom unity (cod f)"
              using assms t Fun_mapsto set_def by blast
            thus ?thesis using assms t by (auto simp add: set_def Fun_def)
          qed
          finally show "(img o S (S g f) o (inv_into (hom unity (dom (S g f))) img)) t
                          = (Fun g o Fun f) t"
            by auto
        qed
        show ?thesis using 1 2 by auto
      qed
      thus ?thesis using Fun_def by auto
    qed

    text{*
      The constructor @{term mkArr} is used to obtain an arrow given subsets
      @{term A} and @{term B} of the universe and a function @{term "F \<in> A \<rightarrow> B"}.
    *}
    
    definition mkArr :: "'s set \<Rightarrow> 's set \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> 's"
    where "mkArr A B F = (if A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B
                          then (THE f. f \<in> hom (mkIde A) (mkIde B) \<and> Fun f = restrict F A)
                          else null)"

    text{*
      Each function @{term "F \<in> set a \<rightarrow> set b"} determines a unique arrow @{term "f \<in> hom a b"},
      such that @{term "Fun f"} is the restriction of @{term F} to @{term "set a"}.
    *}

    lemma fun_complete:
    assumes "ide a" and "ide b" and "F \<in> set a \<rightarrow> set b"
    shows "\<exists>!f. f \<in> hom a b \<and> Fun f = restrict F (set a)"
    proof -
      let ?P = "\<lambda>f. f \<in> hom a b \<and> Fun f = restrict F (set a)"
      show "\<exists>!f. ?P f"
      proof
        have "\<exists>f. ?P f"
        proof -
          let ?F' = "\<lambda>x. inv_into (hom unity b) img (F (img x))"
          have "?F' \<in> hom unity a \<rightarrow> hom unity b"
          proof
            fix x
            assume x: "x \<in> hom unity a"
            have "F (img x) \<in> set b" using assms(3) x set_def by auto
            thus "inv_into (hom unity b) img (F (img x)) \<in> hom unity b"
              using assms img_mapsto inj_img set_def by auto
          qed
          hence "\<exists>f. f \<in> hom a b \<and> (\<forall>x. x \<in> hom unity a \<longrightarrow> S f x = ?F' x)"
            using assms fun_complete1 by presburger
          from this obtain f where f: "f \<in> hom a b \<and> (\<forall>x. x \<in> hom unity a \<longrightarrow> S f x = ?F' x)"
            by blast
          have "Fun f = restrict F (set a)"
            unfolding Fun_def apply (intro restr_eqI)
          proof -
            show "set (dom f) = set a" using f by auto
            show "\<And>t. t \<in> set (dom f) \<Longrightarrow> (img \<circ> S f \<circ> inv_into (hom unity (dom f)) img) t = F t"
            proof -
              fix t
              assume t: "t \<in> set (dom f)"
              have "(img \<circ> S f \<circ> inv_into (hom unity (dom f)) img) t =
                      img (S f (inv_into (hom unity (dom f)) img t))"
                by simp
              also have "... = img (?F' (inv_into (hom unity (dom f)) img t))"
              proof -
                have "inv_into (hom unity (dom f)) img t \<in> hom unity (dom f)"
                  using t set_def [of "dom f"] inv_into_into
                  by (metis (mono_tags, lifting))
                thus ?thesis using f by simp
              qed
              also have "... = img (inv_into (hom unity (cod f)) img (F t))"
                using f t set_def inj_img by auto
              also have "... = F t"
              proof -
                have "F t \<in> set (cod f)"
                  using assms f t by auto
                thus ?thesis
                  using f t set_def inj_img by auto
              qed
              finally show "(img \<circ> S f \<circ> inv_into (hom unity (dom f)) img) t = F t" by auto
            qed
          qed
          thus ?thesis using f by blast
        qed
        thus F: "?P (SOME f. ?P f)" using someI_ex [of ?P] by fast
        show "\<And>f'. ?P f' \<Longrightarrow> f' = (SOME f. ?P f)"
        proof -
          fix f'
          assume F': "?P f'"
          show "f' = (SOME f. ?P f)"
            using F F' arr_eqI [of f' "SOME f. ?P f"] by simp
        qed
      qed
    qed
                          
    lemma mkArr_in_hom:
    assumes "A \<subseteq> Univ" and "B \<subseteq> Univ" and "F \<in> A \<rightarrow> B"
    shows "mkArr A B F \<in> hom (mkIde A) (mkIde B)"
      using assms mkArr_def fun_complete [of "mkIde A" "mkIde B" F]
            theI' [of "\<lambda>f. f \<in> hom (mkIde A) (mkIde B) \<and> Fun f = restrict F A"]
      by simp

    text{*
      The ``only if'' direction of the next lemma can be achieved only if there exists a
      non-arrow element of type @{typ 's}, which can be used as the value of @{term "mkArr A B F"}
      in cases where @{term "F \<notin> A \<rightarrow> B"}.  Nevertheless, it is essential to have this,
      because without the ``only if'' direction, we can't derive any useful
      consequences from an assumption of the form @{term "arr (mkArr A B F)"};
      instead we have to obtain @{term "F \<in> A \<rightarrow> B"} some other way.
      This is is usually highly inconvenient and it makes the theory very weak and almost
      unusable in practice.  The observation that having a non-arrow value of type @{typ 's}
      solves this problem is ultimately what led me to incorporate @{term null} first into the
      definition of the @{text set_category} locale and then, ultimately, into the definition
      of the @{text category} locale.  I believe this idea is critical to the usability of the
      entire development.
    *}

    (* TODO: This gets used as an introduction rule, but the conjunction on the right-hand side
       is not very convenient. *)
    lemma arr_mkArr [iff]:
    shows "arr (mkArr A B F) \<longleftrightarrow> A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B"
    proof -
      have "\<not>A \<subseteq> Univ \<or> \<not>B \<subseteq> Univ \<or> F \<notin> A \<rightarrow> B \<Longrightarrow> \<not>arr (mkArr A B F)"
        using mkArr_def not_arr_null ex_un_null someI_ex [of "\<lambda>f. \<not>arr f"] by metis
      moreover have "A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B \<Longrightarrow> arr (mkArr A B F)"
        using mkArr_in_hom by force
      ultimately show ?thesis by auto
    qed
    
    lemma Fun_mkArr':
    assumes "arr (mkArr A B F)"
    shows "Fun (mkArr A B F) = restrict F A \<and> dom (mkArr A B F) = mkIde A \<and>
           cod (mkArr A B F) = mkIde B"
    proof -
      have 1: "A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B" using assms by fast
      moreover have "mkArr A B F \<in> hom (mkIde A) (mkIde B)
                       \<and> Fun (mkArr A B F) = restrict F (set (mkIde A))"
      proof -
        have "\<exists>!f. f \<in> hom (mkIde A) (mkIde B) \<and> Fun f = restrict F (set (mkIde A))"
        proof -
          have "set (mkIde A) \<subseteq> Univ \<and> set (mkIde B) \<subseteq> Univ" using 1 by simp
          moreover have "ide (mkIde A) \<and> ide (mkIde B) \<and> F \<in> set (mkIde A) \<rightarrow> set (mkIde B)"
            using 1 by simp
          ultimately show ?thesis
            using fun_complete [of "mkIde A" "mkIde B" F] by fast
        qed
        thus ?thesis
          using 1 mkArr_def theI' [of "\<lambda>f. f \<in> hom (mkIde A) (mkIde B)
                                            \<and> Fun f = restrict F (set (mkIde A))"]
          by simp
      qed
      ultimately show ?thesis by auto
    qed

    lemma mkArr_Fun [simp]:
    assumes "arr f"
    shows "mkArr (set (dom f)) (set (cod f)) (Fun f) = f"
    proof -
      have 1: "set (dom f) \<subseteq> Univ \<and> set (cod f) \<subseteq> Univ
                \<and> ide (dom f) \<and> ide (cod f)
                \<and> Fun f \<in> extensional (set (dom f)) \<inter> (set (dom f) \<rightarrow> set (cod f))"
        using assms Fun_mapsto by force
      hence "\<exists>!f'. f' \<in> hom (dom f) (cod f) \<and> Fun f' = restrict (Fun f) (set (dom f))"
        using fun_complete by force
      moreover have "f \<in> hom (dom f) (cod f) \<and> Fun f = restrict (Fun f) (set (dom f))"
      proof -
        have "restrict (Fun f) (set (dom f)) = Fun f"
          using 1 by (meson IntD1 extensional_restrict)
        thus ?thesis using assms by fastforce
      qed
      ultimately have "f = (THE f'. f' \<in> hom (dom f) (cod f)
                                      \<and> Fun f' = restrict (Fun f) (set (dom f)))"
        using theI' [of "\<lambda>f'. f' \<in> hom (dom f) (cod f) \<and> Fun f' = restrict (Fun f) (set (dom f))"]
        by blast
      also have "... = mkArr (set (dom f)) (set (cod f)) (Fun f)"
        using assms 1 mkArr_def by simp
      finally show ?thesis by auto
    qed
    
    lemma dom_mkArr [simp]:
    assumes "arr (mkArr A B F)"
    shows "dom (mkArr A B F) = mkIde A"
      using assms Fun_mkArr' by auto
        
    lemma cod_mkArr [simp]:
    assumes "arr (mkArr A B F)"
    shows "cod (mkArr A B F) = mkIde B"
      using assms Fun_mkArr' by auto
     
    lemma Fun_mkArr [simp]:
    assumes "arr (mkArr A B F)"
    shows "Fun (mkArr A B F) = restrict F A"
      using assms Fun_mkArr' by auto

    text{*
      The following provides the basic technique for showing that arrows
      constructed using @{term mkArr} are equal.
    *}

    lemma mkArr_eqI [intro]:
    assumes "arr (mkArr A B F)"
    and "A = A'" and "B = B'" and "\<And>x. x \<in> A \<Longrightarrow> F x = F' x"
    shows "mkArr A B F = mkArr A' B' F'"
    proof (intro arr_eqI)
      have 1: "arr (mkArr A B F) \<and> arr (mkArr A' B' F')"
        using assms arr_mkArr by (auto simp add: Pi_iff)
      show "par (mkArr A B F) (mkArr A' B' F')"
        using 1 assms(2) assms(3) by simp
      show "Fun (mkArr A B F) = Fun (mkArr A' B' F')"
        using assms 1 Fun_mkArr by auto
    qed

    text{*
      This version avoids trivial proof obligations when the domain and codomain
      sets are identical from the context.
    *}
    
    lemma mkArr_eqI' [intro]:
    assumes "arr (mkArr A B F)" and "\<And>x. x \<in> A \<Longrightarrow> F x = F' x"
    shows "mkArr A B F = mkArr A B F'"
      using assms mkArr_eqI by blast
    
    lemma mkArr_restrict_eq [simp]:
    assumes "arr (mkArr A B F)"
    shows "mkArr A B (restrict F A) = mkArr A B F"
    proof (intro mkArr_eqI')
      have 1: "A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B" using assms by auto
      show "arr (mkArr A B (restrict F A))" using 1 by fast
      show "\<And>x. x \<in> A \<Longrightarrow> restrict F A x = F x" by fastforce
    qed
      
    lemma mkArr_restrict_eq':
    assumes "arr (mkArr A B (restrict F A))"
    shows "mkArr A B (restrict F A) = mkArr A B F"
    proof (intro mkArr_eqI')
      have 1: "A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B"
      proof -
        have "F \<in> A \<rightarrow> B \<longleftrightarrow> restrict F A \<in> A \<rightarrow> B" by force
        thus ?thesis using assms by auto
      qed
      show "arr (mkArr A B (restrict F A))" using 1 by fast
      show "\<And>x. x \<in> A \<Longrightarrow> restrict F A x = F x" by fastforce
    qed
      
    lemma mkIde_as_mkArr [simp]:
    assumes "A \<subseteq> Univ"
    shows "mkArr A A (\<lambda>x. x) = mkIde A"
    proof (intro arr_eqI)
      show "par (mkArr A A (\<lambda>x. x)) (mkIde A)" using assms by simp
      show "Fun (mkArr A A (\<lambda>x. x)) = Fun (mkIde A)" using assms by simp
    qed

    lemma comp_mkArr [simp]:
    assumes "arr (mkArr A B F)" and "arr (mkArr B C G)"
    shows "S (mkArr B C G) (mkArr A B F) = mkArr A C (G o F)"
    proof (intro arr_eqI)
      have 1: "seq (mkArr B C G) (mkArr A B F)" using assms by force
      have 2: "G o F \<in> A \<rightarrow> C" using assms by auto
      show "par (S (mkArr B C G) (mkArr A B F)) (mkArr A C (G o F))"
        using 1 2 by auto
      show "Fun (S (mkArr B C G) (mkArr A B F)) = Fun (mkArr A C (G o F))"
        using 1 2 by fastforce
    qed
    
    text{*
      The locale assumption @{prop stable_img} forces @{term "t \<in> set t"} in case
      @{term t} is a terminal object.  This is very convenient, as it results in the
      characterization of terminal objects as identities @{term t} for which
      @{term "set t = {t}"}.  However, it is not absolutely necessary to have this.
      The following weaker characterization of terminal objects can be proved without
      the @{prop stable_img} assumption.
    *}

    lemma terminal_char1:
    shows "terminal t \<longleftrightarrow> ide t \<and> (\<exists>!x. x \<in> set t)"
    proof -
      have "terminal t \<Longrightarrow> ide t \<and> (\<exists>!x. x \<in> set t)"
      proof -
        assume t: "terminal t"
        have "ide t" using t terminal_def by auto
        moreover have "\<exists>!x. x \<in> set t"
        proof -
          have "\<exists>!x. x \<in> hom unity t"
            using t terminal_unity terminal_def by auto
          thus ?thesis using set_def by auto
        qed
        ultimately show "ide t \<and> (\<exists>!x. x \<in> set t)" by auto
      qed
      moreover have "ide t \<and> (\<exists>!x. x \<in> set t) \<Longrightarrow> terminal t"
      proof -
        assume t: "ide t \<and> (\<exists>!x. x \<in> set t)"
        from this obtain t' where "set t = {t'}" by blast
        hence t': "{t'} \<subseteq> Univ \<and> t = mkIde {t'}"
          using t set_subset_Univ mkIde_set by metis
        show "terminal t"
        proof
          show "ide t" using t by simp
          show "\<And>a. ide a \<Longrightarrow> \<exists>!f. f \<in> hom a t"
          proof -
            fix a
            assume a: "ide a"
            show "\<exists>!f. f \<in> hom a t"
            proof
              show 1: "mkArr (set a) {t'} (\<lambda>x. t') \<in> hom a t"
                using a t' mkArr_in_hom by force
              show "\<And>f. f \<in> hom a t \<Longrightarrow> f = mkArr (set a) {t'} (\<lambda>x. t')"
              proof -
                fix f
                assume f: "f \<in> hom a t"
                show "f = mkArr (set a) {t'} (\<lambda>x. t')"
                proof (intro arr_eqI)
                  show 1: "par f (mkArr (set a) {t'} (\<lambda>x. t'))" using 1 f by auto
                  show "Fun f = Fun (mkArr (set a) {t'} (\<lambda>x. t'))"
                    using 1 f t Fun_mapsto extensional_arb unity_def Fun_mkArr by fastforce
                qed
              qed
            qed
          qed
        qed
      qed
      ultimately show ?thesis by blast
    qed
    
    text{*
      As stated above, in the presence of the @{prop stable_img} assumption we have
      the following stronger characterization of terminal objects.
    *}

    lemma terminal_char2:
    shows "terminal t \<longleftrightarrow> ide t \<and> set t = {t}"
    proof
      assume T: "terminal t"
      show "ide t \<and> set t = {t}"
      proof
        show "ide t" using T terminal_char1 by auto
        show "set t = {t}"
        proof -
          have "\<exists>!x. x \<in> hom unity t" using T terminal_def terminal_unity by force
          moreover have "t \<in> img ` hom unity t" using T stable_img set_def by simp
          ultimately show ?thesis using set_def by auto
        qed
      qed
      next
      assume "ide t \<and> set t = {t}"
      thus "terminal t" using terminal_char1 by force
    qed

  end

  text{*
    At last, we define the @{text set_category} locale by existentially quantifying
    out the choice of a particular @{term img} map.  We need to know that such a map
    exists, but it does not matter which one we choose.
  *}

  locale set_category = category S
  for S :: "'s comp" +
  assumes ex_img: "\<exists>img. set_category_given_img S img"
  begin
  
    definition some_img
    where "some_img = (SOME img. set_category_given_img S img)"
   
  end
  
  sublocale set_category \<subseteq> set_category_given_img S some_img
  proof -
    have "\<exists>img. set_category_given_img S img" using ex_img by auto
    thus "set_category_given_img S some_img" 
      using someI_ex [of "\<lambda>img. set_category_given_img S img"] some_img_def
      by metis
  qed

  context set_category
  begin

    text{*
      The arbitrary choice of @{term img} induces a system of inclusions,
      which are arrows corresponding to inclusions of subsets.
    *}

    definition incl :: "'s \<Rightarrow> bool"
    where "incl f = (arr f \<and> set (dom f) \<subseteq> set (cod f) \<and>
                     f = mkArr (set (dom f)) (set (cod f)) (\<lambda>x. x))"

    lemma Fun_incl:
    assumes "incl f"
    shows "Fun f = (\<lambda>x \<in> set (dom f). x)"
      using assms incl_def by (metis Fun_mkArr)

    lemma ex_incl_iff_subset:
    assumes "ide a" and "ide b"
    shows "(\<exists>f. f \<in> hom a b \<and> incl f) \<longleftrightarrow> set a \<subseteq> set b"
    proof
      show "\<exists>f. f \<in> hom a b \<and> incl f \<Longrightarrow> set a \<subseteq> set b"
        using incl_def by auto
      show "set a \<subseteq> set b \<Longrightarrow> \<exists>f. f \<in> hom a b \<and> incl f"
      proof
        assume 1: "set a \<subseteq> set b"
        show "mkArr (set a) (set b) (\<lambda>x. x) \<in> hom a b \<and> incl (mkArr (set a) (set b) (\<lambda>x. x))"
        proof
          show "mkArr (set a) (set b) (\<lambda>x. x) \<in> hom a b"
          proof -
            have "(\<lambda>x. x) \<in> set a \<rightarrow> set b" using 1 by auto
            thus ?thesis using assms mkArr_in_hom set_subset_Univ by auto
          qed
          thus "incl (mkArr (set a) (set b) (\<lambda>x. x))"
            using 1 incl_def by simp
        qed
      qed
    qed

  end

  section "Categoricity"

  text{*
    In this section we show that the @{text set_category} locale completely characterizes
    the structure of its interpretations as categories, in the sense that for any two
    interpretations @{term S} and @{term S'}, a bijection between the universe of @{term S}
    and the universe of @{term S'} extends to an isomorphism of @{term S} and @{term S'}.
  *}
  
  locale two_set_categories_bij_betw_Univ =
    S: set_category S +
    S': set_category S'
    for S :: "'s comp"
    and S' :: "'t comp"
    and \<phi> :: "'s \<Rightarrow> 't" +
    assumes bij_\<phi>: "bij_betw \<phi> S.Univ S'.Univ"
  begin
  
    abbreviation \<psi>
    where "\<psi> \<equiv> inv_into S.Univ \<phi>"

    lemma \<psi>_\<phi>:
    assumes "t \<in> S.Univ"
    shows "\<psi> (\<phi> t) = t"
      using assms bij_\<phi> bij_betw_inv_into_left by metis

    lemma \<phi>_\<psi>:
    assumes "t' \<in> S'.Univ"
    shows "\<phi> (\<psi> t') = t'"
      using assms bij_\<phi> bij_betw_inv_into_right by metis
    
    lemma \<psi>_img_\<phi>_img:
    assumes "A \<subseteq> S.Univ"
    shows "\<psi> ` \<phi> ` A = A"
      using assms bij_\<phi> by (simp add: bij_betw_def)
      
    lemma \<phi>_img_\<psi>_img:
    assumes "A' \<subseteq> S'.Univ"
    shows "\<phi> ` \<psi> ` A' = A'"
      using assms bij_\<phi> by (simp add: bij_betw_def image_inv_into_cancel)
  
    text{*
      The object map @{term \<Phi>o} of a functor from @{term S} to @{term S'}.
    *}

    definition \<Phi>o
    where "\<Phi>o = (\<lambda>a \<in> Collect S.ide. S'.mkIde (\<phi> ` S.set a))"

    lemma set_\<Phi>o:
    assumes "S.ide a"
    shows "S'.set (\<Phi>o a) = \<phi> ` S.set a"
    proof -
      from assms have "S.set a \<subseteq> S.Univ" by simp
      then show ?thesis
      using S'.set_mkIde \<Phi>o_def assms bij_\<phi> bij_betw_def image_mono mem_Collect_eq restrict_def
      by (metis (no_types, lifting))
    qed

    lemma \<Phi>o_preserves_ide:
    assumes "S.ide a"
    shows "S'.ide (\<Phi>o a)"
      using assms \<Phi>o_def S.set_subset_Univ bij_\<phi> bij_betw_def image_mono S'.ide_mkIde
            restrict_apply' CollectI
      by (metis (no_types, lifting))
      
    text{*
      The map @{term \<Phi>a} assigns to each arrow @{term f} of @{term S} the function on
      the universe of @{term S'} that is the same as the function induced by @{term f}
      on the universe of @{term S}, up to the bijection @{term \<phi>} between the two
      universes.
    *}

    definition \<Phi>a
    where "\<Phi>a = (\<lambda>f. \<lambda>x' \<in> \<phi> ` S.set (S.dom f). \<phi> (S.Fun f (\<psi> x')))"
    
    lemma \<Phi>a_mapsto:
    assumes "S.arr f"
    shows "\<Phi>a f \<in> S'.set (\<Phi>o (S.dom f)) \<rightarrow> S'.set (\<Phi>o (S.cod f))"
    proof -
      have "\<Phi>a f \<in> \<phi> ` S.set (S.dom f) \<rightarrow> \<phi> ` S.set (S.cod f)"
      proof
        fix x
        assume x: "x \<in> \<phi> ` S.set (S.dom f)"
        have "\<psi> x \<in> S.set (S.dom f)"
          using assms x \<psi>_img_\<phi>_img [of "S.set (S.dom f)"] S.set_subset_Univ by auto
        hence "S.Fun f (\<psi> x) \<in> S.set (S.cod f)" using assms S.Fun_mapsto by auto
        hence "\<phi> (S.Fun f (\<psi> x)) \<in> \<phi> ` S.set (S.cod f)" by simp
        thus "\<Phi>a f x \<in> \<phi> ` S.set (S.cod f)" using x \<Phi>a_def by auto
      qed
      thus ?thesis using assms set_\<Phi>o \<Phi>o_preserves_ide by auto
    qed
    
    text{*
      The map @{term \<Phi>a} takes composition of arrows to extensional
      composition of functions.
    *}

    lemma \<Phi>a_comp:
    assumes gf: "S.seq g f"
    shows "\<Phi>a (S g f) = restrict (\<Phi>a g o \<Phi>a f) (S'.set (\<Phi>o (S.dom f)))"
    proof -
      have "\<Phi>a (S g f) = (\<lambda>x' \<in> \<phi> ` S.set (S.dom f). \<phi> (S.Fun (S g f) (\<psi> x')))"
        using gf \<Phi>a_def by auto
      also have "... = (\<lambda>x' \<in> \<phi> ` S.set (S.dom f).
                           \<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x')))"
        using gf set_\<Phi>o S.Fun_comp by simp
      also have "... = restrict (\<Phi>a g o \<Phi>a f) (S'.set (\<Phi>o (S.dom f)))"
      proof -
        have "\<And>x'. x' \<in> \<phi> ` S.set (S.dom f)
                 \<Longrightarrow> \<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x')) = \<Phi>a g (\<Phi>a f x')"
        proof -
          fix x'
          assume X': "x' \<in> \<phi> ` S.set (S.dom f)"
          hence 1: "\<psi> x' \<in> S.set (S.dom f)"
            using gf \<psi>_img_\<phi>_img [of "S.set (S.dom f)"] S.set_subset_Univ by auto
          hence "\<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x'))
                   = \<phi> (S.Fun g (S.Fun f (\<psi> x')))"
            using restrict_apply by auto
          also have "... = \<phi> (S.Fun g (\<psi> (\<phi> (S.Fun f (\<psi> x')))))"
          proof -
            have "S.Fun f (\<psi> x') \<in> S.set (S.cod f)"
              using gf 1 S.Fun_mapsto by fast
            hence "\<psi> (\<phi> (S.Fun f (\<psi> x'))) = S.Fun f (\<psi> x')"
              using bij_\<phi> S.set_subset_Univ bij_betw_def inv_into_f_f subsetCE S.ide_cod assms
              by metis
            thus ?thesis by auto
          qed
          also have "... = \<Phi>a g (\<Phi>a f x')"
          proof -
            have "\<Phi>a f x' \<in> \<phi> ` S.set (S.cod f)"
              using gf S.ide_dom S.ide_cod X' \<Phi>a_mapsto [of f] set_\<Phi>o [of "S.dom f"]
                    set_\<Phi>o [of "S.cod f"]
              by blast
            thus ?thesis by (simp add: X' \<Phi>a_def gf)
          qed
          finally show "\<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x')) = \<Phi>a g (\<Phi>a f x')"
            by auto
        qed
        thus ?thesis using assms set_\<Phi>o by fastforce
      qed
      finally show ?thesis by auto
    qed
    
    text{*
      Finally, we use @{term \<Phi>o} and @{term \<Phi>a} to define a functor @{term \<Phi>}.
    *}

    definition \<Phi>
    where "\<Phi> f = (if f \<in> Collect S.arr then
                     S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod f))) (\<Phi>a f)
                   else S'.null)"
    
    lemma \<Phi>_in_hom:
    assumes "S.arr f"
    shows "\<Phi> f \<in> S'.hom (\<Phi>o (S.dom f)) (\<Phi>o (S.cod f))"
      using assms \<Phi>_def \<Phi>a_mapsto restrict_apply \<Phi>o_preserves_ide S'.set_subset_Univ by simp
    
    lemma \<Phi>_ide [simp]:
    assumes "S.ide a"
    shows "\<Phi> a = \<Phi>o a"
    proof -
      have "\<Phi> a = S'.mkArr (S'.set (\<Phi>o a)) (S'.set (\<Phi>o a)) (\<lambda>x'. x')"
      proof -
        have "\<Phi> a \<in> S'.hom (\<Phi>o a) (\<Phi>o a)" using assms \<Phi>_in_hom by simp
        moreover have "\<Phi>a a = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a))"
        proof -
          have "\<Phi>a a = (\<lambda>x' \<in> \<phi> ` S.set a. \<phi> (S.Fun a (\<psi> x')))"
            using assms \<Phi>a_def restrict_apply by simp
          also have "... = (\<lambda>x' \<in> \<phi> ` S.set a. \<phi> (\<psi> x'))"
          proof -
            have "S.Fun a = (\<lambda>x \<in> S.set a. x)" using assms S.Fun_ide by simp
            moreover have "\<And>x'. x' \<in> \<phi> ` S.set a \<Longrightarrow> \<psi> x' \<in> S.set a"
              using assms bij_\<phi> S.set_subset_Univ image_iff by (metis \<psi>_img_\<phi>_img)
            ultimately show ?thesis by auto
          qed
          also have "... = (\<lambda>x' \<in> S'.set (\<Phi>o a). \<phi> (\<psi> x'))"
          proof -
            have "\<phi> ` S.set a = S'.set (\<Phi>o a)"
              using assms set_\<Phi>o [of a] by simp
            thus ?thesis by auto
          qed
          also have "... = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a))"
          proof
            fix x'
            have "x' \<notin> S'.set (\<Phi>o a) \<Longrightarrow>
                   (\<lambda>x' \<in> S'.set (\<Phi>o a). \<phi> (\<psi> x')) x' = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a)) x'"
              by simp
            moreover have "x' \<in> S'.set (\<Phi>o a) \<Longrightarrow>
                   (\<lambda>x' \<in> S'.set (\<Phi>o a). \<phi> (\<psi> x')) x' = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a)) x'"
            proof -
              assume x': "x' \<in> S'.set (\<Phi>o a)"
              show "(\<lambda>x' \<in> S'.set (\<Phi>o a). \<phi> (\<psi> x')) x' = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a)) x'"
              proof -
                have "(\<lambda>x' \<in> S'.set (\<Phi>o a). \<phi> (\<psi> x')) x' = \<phi> (\<psi> x')" using assms x' by simp
                also have "... = x'"
                  using assms x' S'.set_subset_Univ [of "\<Phi>o a"] \<Phi>o_preserves_ide [of a] \<phi>_\<psi>
                  by blast
                also have "... = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a)) x'"
                  using x' restrict_apply by simp
                finally show ?thesis by auto
              qed
            qed
            ultimately show "(\<lambda>x' \<in> S'.set (\<Phi>o a). \<phi> (\<psi> x')) x'
                                = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a)) x'"
              by blast
          qed
          ultimately show ?thesis by auto
        qed
        ultimately show ?thesis using assms \<Phi>_def by auto
      qed
      thus ?thesis
        using assms S'.mkIde_as_mkArr \<Phi>o_preserves_ide \<Phi>_in_hom S'.set_subset_Univ by simp
    qed
    
    lemma set_dom_\<Phi>:
    assumes F: "S.arr f"
    shows "S'.set (S'.dom (\<Phi> f)) = \<phi> ` (S.set (S.dom f))"
      using assms S.ide_dom \<Phi>_in_hom \<Phi>_ide set_\<Phi>o by simp
    
    lemma \<Phi>_comp:
    assumes "S.seq g f"
    shows "\<Phi> (S g f) = S' (\<Phi> g) (\<Phi> f)"
    proof -
      have "\<Phi> (S g f) = S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a (S g f))"
        using \<Phi>_def assms by simp
      also have "... = S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g)))
                                (restrict (\<Phi>a g o \<Phi>a f) (S'.set (\<Phi>o (S.dom f))))"
        using assms \<Phi>a_comp set_\<Phi>o by fastforce
      also have "... = S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a g o \<Phi>a f)"
      proof -
        have "S'.arr (S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a g o \<Phi>a f))"
        proof -
          have "\<Phi>a g o \<Phi>a f \<in> S'.set (\<Phi>o (S.dom f)) \<rightarrow> S'.set (\<Phi>o (S.cod g))"
            using assms \<Phi>a_mapsto [of f] \<Phi>a_mapsto [of g] by auto
          thus ?thesis
            using assms S.ide_dom S.ide_cod \<Phi>o_preserves_ide S'.arr_mkArr S'.set_subset_Univ
            by simp
        qed
        thus ?thesis
          using assms S'.mkArr_restrict_eq by auto
      qed
      also have "... = S' (S'.mkArr (S'.set (\<Phi>o (S.dom g))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a g))
                          (S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod f))) (\<Phi>a f))"
      proof -
        have "S'.arr (S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod f))) (\<Phi>a f))"
          using assms \<Phi>a_mapsto set_\<Phi>o S.ide_dom S.ide_cod \<Phi>o_preserves_ide S'.arr_mkArr
                S'.set_subset_Univ
          by meson
        moreover have "S'.arr (S'.mkArr (S'.set (\<Phi>o (S.dom g))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a g))"
          using assms \<Phi>a_mapsto set_\<Phi>o S.ide_dom S.ide_cod \<Phi>o_preserves_ide S'.arr_mkArr
                S'.set_subset_Univ
          by meson
        moreover have "S'.set (\<Phi>o (S.cod f)) = S'.set (\<Phi>o (S.dom g))"
          using assms by auto
        ultimately show ?thesis using assms S'.comp_mkArr by simp
      qed
      also have "... = S' (\<Phi> g) (\<Phi> f)" using assms \<Phi>_def by simp
      finally show ?thesis by fast
    qed
      
    interpretation \<Phi>: "functor" S S' \<Phi>
      using \<Phi>_def \<Phi>_in_hom \<Phi>_comp \<Phi>_ide
      apply unfold_locales
      (* 5 *) apply simp
      (* 4 *) apply simp
      (* 3 *) apply fastforce
      (* 2 *) apply fastforce
      (* 1 *) by force

    lemma \<Phi>_is_functor:
    shows "functor S S' \<Phi>" ..
      
    lemma Fun_\<Phi>:
    assumes "S.arr f" and "x \<in> S.set (S.dom f)"
    shows "S'.Fun (\<Phi> f) (\<phi> x) = \<Phi>a f (\<phi> x)"
      using \<Phi>_def assms restrict_apply S'.Fun_mkArr \<Phi>.preserves_ide \<Phi>.preserves_hom set_\<Phi>o
      by fastforce
      
    lemma \<Phi>_acts_elementwise:
    assumes "S.ide a"
    shows "S'.set (\<Phi> a) = \<Phi> ` S.set a"
    proof
      have 0: "S'.set (\<Phi> a) = \<phi> ` S.set a"
        using assms \<Phi>_ide set_\<Phi>o by simp
      have 1: "\<And>x. x \<in> S.set a \<Longrightarrow> \<Phi> x = \<phi> x"
      proof -
        fix x
        assume x: "x \<in> S.set a"
        have 1: "S.terminal x" using assms x S.set_subset_Univ by blast
        hence 2: "S'.terminal (\<phi> x)"
          using bij_\<phi> bij_betw_def bij_betw_inv_into f_inv_into_f inv_into_into
          by (metis (no_types, lifting) CollectD CollectI)
        have "\<Phi> x = \<Phi>o x"
          using assms x \<Phi>_ide S.set_subset_Univ S.terminal_def by blast
        also have "\<Phi>o x = \<phi> x"
        proof -
          have "\<Phi>o x = S'.mkIde (\<phi> ` S.set x)"
            using assms 1 x \<Phi>o_def restrict_apply S.set_subset_Univ S.terminal_def by auto
          moreover have "S'.mkIde (\<phi> ` S.set x) = \<phi> x"
          proof -
            have "\<phi> ` S.set x = {\<phi> x}" using assms 1 S.terminal_char2 by simp
            thus ?thesis
              using assms x 1 2 bij_\<phi> S'.mkIde_set S'.terminal_char2 by metis
          qed
          ultimately show ?thesis by auto
        qed
        finally show "\<Phi> x = \<phi> x" by auto
      qed
      have "\<And>x. x \<in> S.set a \<Longrightarrow> \<phi> x \<in> \<Phi> ` S.set a" using 1 by force
      thus "S'.set (\<Phi> a) \<subseteq> \<Phi> ` S.set a" using 0 by auto
      have "\<And>x'. x' \<in> \<Phi> ` S.set a \<Longrightarrow> x' \<in> S'.set (\<Phi> a)"
        using assms 0 1 set_dom_\<Phi> by blast
      thus "\<Phi> ` S.set a \<subseteq> S'.set (\<Phi> a)" by auto
    qed

    lemma \<Phi>_preserves_incl:
    assumes "S.incl m"
    shows "S'.incl (\<Phi> m)"
    proof -
      have 1: "S.arr m \<and> S.set (S.dom m) \<subseteq> S.set (S.cod m)
                \<and> m = S.mkArr (S.set (S.dom m)) (S.set (S.cod m)) (\<lambda>x. x)"
        using assms S.incl_def by blast
      have "S'.arr (\<Phi> m)" using 1 by simp
      moreover have 2: "S'.set (S'.dom (\<Phi> m)) \<subseteq> S'.set (S'.cod (\<Phi> m))"
        using 1 \<Phi>.preserves_dom \<Phi>.preserves_cod \<Phi>_acts_elementwise
        by (metis (full_types) S.ide_cod S.ide_dom image_mono)
      moreover have "\<Phi> m = S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<lambda>x'. x')"
      proof -
        have "\<Phi> m = S'.mkArr (S'.set (\<Phi>o (S.dom m))) (S'.set (\<Phi>o (S.cod m))) (\<Phi>a m)"
          using 1 \<Phi>_def restrict_apply by simp
        also have "... = S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<Phi>a m)"
          using 1 \<Phi>.preserves_dom \<Phi>.preserves_cod \<Phi>_ide by auto
        finally have 3: "\<Phi> m = S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<Phi>a m)"
          by auto
        also have "... = S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<lambda>x'. x')"
        proof -
          have 4: "S.Fun m = restrict (\<lambda>x. x) (S.set (S.dom m))"
            using assms S.incl_def [of m] by (metis (full_types) S.Fun_mkArr)
          hence "\<Phi>a m = restrict (\<lambda>x'. x') (\<phi> ` (S.set (S.dom m)))"
          proof -
            have 5: "\<And>x'. x' \<in> \<phi> ` S.set (S.dom m) \<Longrightarrow> \<phi> (\<psi> x') = x'"
              using 1 bij_\<phi> bij_betw_def S'.set_subset_Univ S.ide_dom \<Phi>o_preserves_ide
                    f_inv_into_f set_\<Phi>o
              by (metis subsetCE)
            have "\<Phi>a m = restrict (\<lambda>x'. \<phi> (S.Fun m (\<psi> x'))) (\<phi> ` S.set (S.dom m))"
              using \<Phi>a_def by simp
            also have "... = restrict (\<lambda>x'. x') (\<phi> ` S.set (S.dom m))"
            proof -
              have "\<And>x. x \<in> \<phi> ` (S.set (S.dom m)) \<Longrightarrow> \<phi> (S.Fun m (\<psi> x)) = x"
              proof -
                fix x
                assume x: "x \<in> \<phi> ` (S.set (S.dom m))"
                hence "\<psi> x \<in> S.set (S.dom m)"
                  using 1 S.ide_dom S.set_subset_Univ \<psi>_img_\<phi>_img image_eqI by metis
                thus "\<phi> (S.Fun m (\<psi> x)) = x" using 1 4 5 x restrict_apply' by simp
              qed
              thus ?thesis by auto
            qed
            finally show ?thesis by auto
          qed
          hence "\<Phi>a m = restrict (\<lambda>x'. x') (S'.set (S'.dom (\<Phi> m)))"
            using 1 set_dom_\<Phi> by auto
          thus ?thesis
            using 2 3 `S'.arr (\<Phi> m)` S'.mkArr_restrict_eq S'.ide_cod S'.ide_dom S'.incl_def
            by (metis S'.arr_mkArr image_restrict_eq image_subset_iff_funcset)
        qed
        finally show ?thesis by auto
      qed
      ultimately show ?thesis using S'.incl_def by blast
    qed

    text{*
      Interchange the role of @{term \<phi>} and @{term \<psi>} to obtain a functor @{text \<Psi>}
      from @{term S'} to @{term S}.
    *}

    interpretation INV: two_set_categories_bij_betw_Univ S' S \<psi>
      apply unfold_locales by (simp add: bij_\<phi> bij_betw_inv_into)

    abbreviation \<Psi>o
    where "\<Psi>o \<equiv> INV.\<Phi>o"

    abbreviation \<Psi>a
    where "\<Psi>a \<equiv> INV.\<Phi>a"

    abbreviation \<Psi>
    where "\<Psi> \<equiv> INV.\<Phi>"

    interpretation \<Psi>: "functor" S' S \<Psi>
      using INV.\<Phi>_is_functor by auto

    text{*
      The functors @{term \<Phi>} and @{term \<Psi>} are inverses.
    *}

    lemma Fun_\<Psi>:
    assumes "S'.arr f'" and "x' \<in> S'.set (S'.dom f')"
    shows "S.Fun (\<Psi> f') (\<psi> x') = \<Psi>a f' (\<psi> x')"
      using assms INV.Fun_\<Phi> by blast
          
    lemma \<Psi>o_\<Phi>o:
    assumes "S.ide a"
    shows "\<Psi>o (\<Phi>o a) = a"
      using assms \<Phi>o_def INV.\<Phi>o_def \<psi>_img_\<phi>_img \<Phi>o_preserves_ide set_\<Phi>o by force
     
    lemma \<Phi>\<Psi>:
    assumes "S.arr f"
    shows "\<Psi> (\<Phi> f) = f"
    proof (intro S.arr_eqI)
      show par: "S.par (\<Psi> (\<Phi> f)) f"
        using assms \<Phi>.preserves_ide \<Psi>.preserves_ide \<Phi>_ide INV.\<Phi>_ide \<Psi>o_\<Phi>o by auto
      show "S.Fun (\<Psi> (\<Phi> f)) = S.Fun f"
      proof -
        have "S.arr (\<Psi> (\<Phi> f))" using assms by auto
        moreover have "\<Psi> (\<Phi> f) = S.mkArr (S.set (S.dom f)) (S.set (S.cod f)) (\<Psi>a (\<Phi> f))"
          using assms INV.\<Phi>_def \<Phi>_in_hom \<Psi>o_\<Phi>o by simp
        moreover have "\<Psi>a (\<Phi> f) = (\<lambda>x \<in> S.set (S.dom f). \<psi> (S'.Fun (\<Phi> f) (\<phi> x)))"
        proof -
          have "\<Psi>a (\<Phi> f) = (\<lambda>x \<in> \<psi> ` S'.set (S'.dom (\<Phi> f)). \<psi> (S'.Fun (\<Phi> f) (\<phi> x)))"
          proof -
            have "\<And>x. x \<in> \<psi> ` S'.set (S'.dom (\<Phi> f)) \<Longrightarrow> INV.\<psi> x = \<phi> x"
              using assms S.ide_dom S.set_subset_Univ \<Psi>.reflects_arr par bij_\<phi>
                    inv_into_inv_into_eq subsetCE INV.set_dom_\<Phi>
              by (metis (no_types, lifting) )
            thus ?thesis
              using INV.\<Phi>a_def by auto
          qed
          moreover have "\<psi> ` S'.set (S'.dom (\<Phi> f)) = S.set (S.dom f)"
            using assms by (metis \<Psi>.reflects_arr \<open>S.par (\<Psi> (\<Phi> f)) f\<close> INV.set_dom_\<Phi>)
          ultimately show ?thesis by auto
        qed
        ultimately have 1: "S.Fun (\<Psi> (\<Phi> f)) = (\<lambda>x \<in> S.set (S.dom f). \<psi> (S'.Fun (\<Phi> f) (\<phi> x)))"
          using S'.Fun_mkArr by simp
        show ?thesis
        proof
          fix x
          have "x \<notin> S.set (S.dom f) \<Longrightarrow> S.Fun (\<Psi> (\<Phi> f)) x = S.Fun f x"
            using 1 assms extensional_def S.Fun_mapsto S.Fun_def by auto
          moreover have "x \<in> S.set (S.dom f) \<Longrightarrow> S.Fun (\<Psi> (\<Phi> f)) x = S.Fun f x"
          proof -
            assume x: "x \<in> S.set (S.dom f)"
            have "S.Fun (\<Psi> (\<Phi> f)) x = \<psi> (S'.Fun (\<Phi> f) (\<phi> x))"
              using x 1 restrict_apply by auto
            also have "... = \<psi> (\<Phi>a f (\<phi> x))"
              using Fun_\<Phi> x assms S.set_subset_Univ bij_\<phi> by presburger
            also have "... = \<psi> (\<phi> (S.Fun f (\<psi> (\<phi> x))))"
              using x \<Phi>a_def bij_\<phi> by auto
            also have "... = S.Fun f x"
            proof -
              have 2: "\<And>x. x \<in> S.Univ \<Longrightarrow> \<psi> (\<phi> x) = x"
                using bij_\<phi> bij_betw_inv_into_left by fast
              have "S.Fun f (\<psi> (\<phi> x)) = S.Fun f x"
              proof -
                have "x \<in> S.Univ" using x assms S.set_subset_Univ [of "S.dom f"] by fastforce
                thus ?thesis using 2 by presburger
              qed
              moreover have "S.Fun f x \<in> S.Univ"
                using x assms S.Fun_mapsto [of f] S.set_subset_Univ [of "S.cod f"] by fastforce
              ultimately show ?thesis using 2 by auto
            qed
            finally show ?thesis by auto
          qed
          ultimately show "S.Fun (\<Psi> (\<Phi> f)) x = S.Fun f x" by auto
        qed
      qed
    qed

    lemma \<Phi>o_\<Psi>o:
    assumes "S'.ide a'"
    shows "\<Phi>o (\<Psi>o a') = a'"
      using assms \<Phi>o_def INV.\<Phi>o_def \<phi>_img_\<psi>_img INV.\<Phi>o_preserves_ide \<psi>_\<phi> INV.set_\<Phi>o by force

    lemma \<Psi>\<Phi>:
    assumes "S'.arr f'"
    shows "\<Phi> (\<Psi> f') = f'"
    proof (intro S'.arr_eqI)
      show "S'.par (\<Phi> (\<Psi> f')) f'"
        using assms \<Phi>.preserves_ide \<Psi>.preserves_ide \<Phi>_ide INV.\<Phi>_ide \<Phi>o_\<Psi>o by auto
      show "S'.Fun (\<Phi> (\<Psi> f')) = S'.Fun f'"
      proof -
        have "S'.arr (\<Phi> (\<Psi> f'))" using assms \<Phi>.preserves_hom \<Psi>.preserves_hom by blast
        moreover have "\<Phi> (\<Psi> f') = S'.mkArr (S'.set (S'.dom f')) (S'.set (S'.cod f')) (\<Phi>a (\<Psi> f'))"
          using assms \<Phi>_def INV.\<Phi>_in_hom \<Phi>o_\<Psi>o by simp
        moreover have "\<Phi>a (\<Psi> f') = (\<lambda>x' \<in> S'.set (S'.dom f'). \<phi> (S.Fun (\<Psi> f') (\<psi> x')))"
        proof -
          have "\<Phi>a (\<Psi> f') = (\<lambda>x' \<in> \<phi> ` S.set (S.dom (\<Psi> f')). \<phi> (S.Fun (\<Psi> f') (\<psi> x')))"
            using \<Phi>a_def by simp
          moreover have "\<phi> ` S.set (S.dom (\<Psi> f')) = S'.set (S'.dom f')"
            using assms by (metis \<Psi>.preserves_arr \<open>S'.par (\<Phi> (\<Psi> f')) f'\<close> set_dom_\<Phi>)
          ultimately show ?thesis by auto
        qed
        ultimately have 1: "S'.Fun (\<Phi> (\<Psi> f')) = (\<lambda>x' \<in> S'.set (S'.dom f'). \<phi> (S.Fun (\<Psi> f') (\<psi> x')))"
          using S'.Fun_mkArr by simp
        show ?thesis
        proof
          fix x'
          have "x' \<notin> S'.set (S'.dom f') \<Longrightarrow> S'.Fun (\<Phi> (\<Psi> f')) x' = S'.Fun f' x'"
            using 1 assms S'.Fun_mapsto [of f'] extensional_def [of "S'.set (S'.dom f')"]
            by (simp add: S'.Fun_def)
          moreover have "x' \<in> S'.set (S'.dom f') \<Longrightarrow> S'.Fun (\<Phi> (\<Psi> f')) x' = S'.Fun f' x'"
          proof -
            assume x': "x' \<in> S'.set (S'.dom f')"
            have "S'.Fun (\<Phi> (\<Psi> f')) x' = \<phi> (S.Fun (\<Psi> f') (\<psi> x'))"
              using x' 1 restrict_apply by auto
            also have "... = \<phi> (\<Psi>a f' (\<psi> x'))"
              using Fun_\<Psi> x' assms S'.set_subset_Univ bij_\<phi> by presburger
            also have "... = \<phi> (\<psi> (S'.Fun f' (\<phi> (\<psi> x'))))"
            proof -
              have "\<phi> (\<Psi>a f' (\<psi> x')) = \<phi> (\<psi> (S'.Fun f' x'))"
              proof -
                have "x' \<in> S'.Univ"
                  by (meson S'.ide_dom S'.set_subset_Univ assms subsetCE x')
                then show ?thesis
                  by (simp add: INV.\<Phi>a_def INV.\<psi>_\<phi> x')
              qed
              also have "... = \<phi> (\<psi> (S'.Fun f' (\<phi> (\<psi> x'))))"
                using assms x' \<phi>_\<psi> [of x'] S'.set_subset_Univ [of "S'.dom f'"] by fastforce
              finally show ?thesis by auto
            qed
            also have "... = S'.Fun f' x'"
            proof -
              have 2: "\<And>x'. x' \<in> S'.Univ \<Longrightarrow> \<phi> (\<psi> x') = x'"
                using bij_\<phi> bij_betw_inv_into_right by fast
              have "S'.Fun f' (\<phi> (\<psi> x')) = S'.Fun f' x'"
              proof -
                have "x' \<in> S'.Univ" using x' assms S'.set_subset_Univ [of "S'.dom f'"] by fastforce
                thus ?thesis using 2 by presburger
              qed
              moreover have "S'.Fun f' x' \<in> S'.Univ"
                using x' assms S'.Fun_mapsto [of f'] S'.set_subset_Univ [of "S'.cod f'"] by fastforce
              ultimately show ?thesis using 2 by auto
            qed
            finally show ?thesis by auto
          qed
          ultimately show "S'.Fun (\<Phi> (\<Psi> f')) x' = S'.Fun f' x'" by auto
        qed
      qed
    qed
          
    lemma inverse_functors_\<Phi>_\<Psi>:
    shows "inverse_functors S S' \<Phi> \<Psi>"
    proof -
      interpret \<Phi>\<Psi>: composite_functor S S' S \<Phi> \<Psi> ..
      interpret I: identity_functor S ..
      have inv: "\<Psi> o \<Phi> = I.map"
        using \<Phi>\<Psi> I.map_def \<Phi>\<Psi>.is_extensional by auto
    
      interpret \<Psi>\<Phi>: composite_functor S' S S' \<Psi> \<Phi> ..
      interpret I': identity_functor S' ..
      have inv': "\<Phi> o \<Psi> = I'.map"
        using \<Psi>\<Phi> I'.map_def \<Psi>\<Phi>.is_extensional by auto
    
      show ?thesis
        apply (unfold_locales) using inv inv' apply auto done
    qed
      
    lemma are_isomorphic:
    shows "\<exists>\<Phi>. invertible_functor S S' \<Phi> \<and> (\<forall>m. S.incl m \<longrightarrow> S'.incl (\<Phi> m))"
    proof -
      interpret inverse_functors S S' \<Phi> \<Psi>
        using inverse_functors_\<Phi>_\<Psi> by auto
      have 1: "inverse_functors S S' \<Phi> \<Psi>" ..
      interpret invertible_functor S S' \<Phi>
        apply unfold_locales using 1 by auto
      have "invertible_functor S S' \<Phi>" ..
      thus ?thesis using \<Phi>_preserves_incl by auto
    qed
    
  end
  
  (*
   * The main result: set_category is categorical, in the following (logical) sense:
   * If S and S' are two "set categories", and if the sets of terminal objects of S and S'
   * are in bijective correspondence, then S and S' are isomorphic as categories,
   * via a functor that preserves inclusion maps, hence the inclusion relation between sets.
   *)
  theorem set_category_is_categorical:
  assumes "set_category S" and "set_category S'"
  and "bij_betw \<phi> (set_category_data.Univ S) (set_category_data.Univ S')"
  shows "\<exists>\<Phi>. invertible_functor S S' \<Phi>
              \<and> (\<forall>m. set_category.incl S m \<longrightarrow> set_category.incl S' (\<Phi> m))"
  proof -
    interpret S: set_category S using assms(1) by auto
    interpret S': set_category S' using assms(2) by auto
    interpret two_set_categories_bij_betw_Univ S S' \<phi>
      apply (unfold_locales) using assms(3) by auto
    show ?thesis using are_isomorphic by auto
  qed
  
  section "Further Properties of Set Categories"

  text{*
    In this section we further develop the consequences of the @{text set_category}
    axioms, and establish characterizations of a number of standard category-theoretic
    notions for a @{text set_category}.
  *}

  context set_category
  begin
  
    abbreviation Dom
    where "Dom f \<equiv> set (dom f)"
    
    abbreviation Cod
    where "Cod f \<equiv> set (cod f)"

    subsection "Initial Object"

    text{*
      The object corresponding to the empty set is an initial object.
    *}

    definition empty
    where "empty = mkIde {}"

    lemma initial_empty:
    shows "initial empty"
    proof
      show "ide empty" using empty_def by auto
      show "\<And>b. ide b \<Longrightarrow> \<exists>!f. f \<in> hom empty b"
      proof -
        fix b
        assume b: "ide b"
        show "\<exists>!f. f \<in> hom empty b"
        proof
          show 1: "mkArr {} (set b) (\<lambda>x. x) \<in> hom empty b"
            using b empty_def by simp
          show "\<And>f. f \<in> hom empty b \<Longrightarrow> f = mkArr {} (set b) (\<lambda>x. x)"
          proof -
            fix f
            assume f: "f \<in> hom empty b"
            show "f = mkArr {} (set b) (\<lambda>x. x)"
            proof (intro arr_eqI)
              show 1: "par f (mkArr {} (set b) (\<lambda>x. x))" using 1 f by auto
              show "Fun f = Fun (mkArr {} (set b) (\<lambda>x. x))"
                using empty_def 1 f Fun_mapsto by fastforce
            qed
          qed
        qed
      qed
    qed

    subsection "Identity Arrows"
    
    text{*
      Identity arrows correspond to restrictions of the identity function.
    *}

    lemma ide_char:
    assumes "arr f"
    shows "ide f \<longleftrightarrow> Dom f = Cod f \<and> Fun f = (\<lambda>x \<in> Dom f. x)"
    proof
      assume "ide f"
      thus "Dom f = Cod f \<and> Fun f = (\<lambda>x \<in> Dom f. x)"
        using Fun_ide by simp
      next
      assume f: "Dom f = Cod f \<and> Fun f = (\<lambda>x \<in> Dom f. x)"
      show "ide f"
      proof -
        have 2: "f = mkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. x)"
          using assms f mkArr_Fun [of f] by metis
        also have "... = mkIde (Dom f)"
          using assms 2 f mkIde_as_mkArr
          by (metis arr_cod_iff_arr arr_mkArr cod_mkArr dom_mkArr Fun_mkIde arr_eqI)
        finally have "f = mkIde (Dom f)" by auto
        thus "ide f" using assms ide_mkIde by auto
      qed
    qed

    lemma ideI:
    assumes "arr f" and "Dom f = Cod f" and "\<And>x. x \<in> Dom f \<Longrightarrow> Fun f x = x"
    shows "ide f"
    proof -
      have "Fun f = (\<lambda>x \<in> Dom f. x)"
      proof
        fix x
        have "x \<notin> Dom f \<Longrightarrow> Fun f x = (\<lambda>x \<in> Dom f. x) x" by (simp add: Fun_def)
        moreover have "x \<in> Dom f \<Longrightarrow> Fun f x = (\<lambda>x \<in> Dom f. x) x"
          using assms by simp
        ultimately show "Fun f x = (\<lambda>x \<in> Dom f. x) x" by auto
      qed
      thus ?thesis using assms ide_char by blast
    qed

    subsection "Inclusions"
    
    lemma ide_implies_incl:
    assumes "ide a"
    shows "incl a"
    proof -
      have "arr a \<and> Dom a \<subseteq> Cod a" using assms by simp
      moreover have "a = mkArr (Dom a) (Cod a) (\<lambda>x. x)"
        apply (intro arr_eqI) using assms by auto
      ultimately show ?thesis using incl_def by simp
    qed
    
    definition incl_in :: "'s \<Rightarrow> 's \<Rightarrow> bool"
    where "incl_in a b = (ide a \<and> ide b \<and> set a \<subseteq> set b)"
    
    abbreviation incl_of
    where "incl_of a b \<equiv> mkArr (set a) (set b) (\<lambda>x. x)"

    lemma elem_set_implies_set_eq_singleton:
    assumes "a \<in> set b"
    shows "set a = {a}"
    proof -
      have "ide b" using assms set_def by auto
      thus ?thesis using assms set_subset_Univ terminal_char2 by blast
    qed

    lemma elem_set_implies_incl_in:
    assumes "a \<in> set b"
    shows "incl_in a b"
    proof -
      have b: "ide b" using assms set_def by auto
      hence "set b \<subseteq> Univ" by simp
      hence "a \<in> Univ \<and> set a \<subseteq> set b"
        using assms elem_set_implies_set_eq_singleton by auto
      hence "ide a \<and> set a \<subseteq> set b"
        using b terminal_char1 by simp
      thus ?thesis using b incl_in_def by simp
    qed
    
    lemma incl_incl_of [simp]:
    assumes "incl_in a b"
    shows "incl (incl_of a b)"
    and "incl_of a b \<in> hom a b"
    proof -
      have "set a \<subseteq> set b \<and> set b \<subseteq> Univ"
        using assms incl_in_def by simp
      moreover from this have "(\<lambda>x. x) \<in> set a \<rightarrow> set b" by auto
      ultimately show "incl_of a b \<in> hom a b"
        using assms incl_in_def mkArr_in_hom by force
      thus "incl (incl_of a b)" using incl_def by fastforce
    qed
    
    text{*
      There is at most one inclusion between any pair of objects.
    *}

    lemma incls_coherent:
    assumes "par f f'" and "incl f" and "incl f'"
    shows "f = f'"
      using assms incl_def fun_complete by auto

    text{*
      The set of inclusions is closed under composition.
    *}

    lemma incl_comp [simp]:
    assumes "incl f" and "incl g" and "cod f = dom g"
    shows "incl (S g f)"
    proof -
      have 1: "seq g f" using assms incl_def by blast
      hence 2: "arr (S g f)" by auto
      moreover have "Dom (S g f) \<subseteq> Cod (S g f)"
        using assms 1 incl_def by auto
      moreover have "S g f = mkArr (Dom f) (Cod g) (restrict (\<lambda>x. x) (Dom f))"
      proof -
        have "Fun (S g f) = restrict (\<lambda>x. x) (Dom f)"
        proof -
          have "Fun (S g f) = restrict (Fun g o Fun f) (Dom f)"
            using 1 Fun_comp by blast
          also have "... = restrict (\<lambda>x. x) (Dom f)"
          proof -
            have "Dom f \<subseteq> Dom g" using assms incl_def by metis
            hence "restrict (restrict (\<lambda>x. x) (Dom g) o restrict (\<lambda>x. x) (Dom f)) (Dom f)
                     = restrict (\<lambda>x. x) (Dom f)"
              by fastforce
            moreover have "Fun f = restrict (\<lambda>x. x) (Dom f) \<and> Fun g = restrict (\<lambda>x. x) (Dom g)"
              using assms incl_def Fun_mkArr by metis
            ultimately show ?thesis by simp
          qed
          finally show ?thesis by auto
        qed
        thus ?thesis using 1 2 mkArr_Fun by (metis cod_comp dom_comp)
      qed
      ultimately show ?thesis using incl_def [of "S g f"] by force
    qed

    subsection "Image Factorization"

    text{*
      The image of an arrow is the object that corresponds to the set-theoretic
      image of the domain set under the function induced by the arrow.
    *}

    abbreviation Img
    where "Img f \<equiv> Fun f ` Dom f"

    definition img
    where "img f = mkIde (Img f)"

    lemma ide_img [simp]:
    assumes "arr f"
    shows "ide (img f)"
    proof -
      have "Fun f ` Dom f \<subseteq> Cod f" using assms Fun_mapsto by blast
      moreover have "Cod f \<subseteq> Univ" using assms by simp
      ultimately show ?thesis using img_def by simp
    qed
    
    lemma set_img [simp]:
    assumes "arr f"
    shows "set (img f) = Img f"
    proof -
      have "Fun f ` set (dom f) \<subseteq> set (cod f) \<and> set (cod f) \<subseteq> Univ"
        using assms Fun_mapsto by auto
      hence "Fun f ` set (dom f) \<subseteq> Univ" by auto
      thus ?thesis using assms img_def set_mkIde by presburger
    qed

    lemma img_point_in_Univ:
    assumes "x \<in> hom unity a"
    shows "img x \<in> Univ"
    proof -
      have "set (img x) = {Fun x unity}"
        using assms img_def terminal_unity terminal_char2
              image_empty image_insert mem_Collect_eq set_img
        by force
      thus "img x \<in> Univ" using assms terminal_char1 by simp
    qed

    lemma incl_in_img_cod:
    assumes "arr f"
    shows "incl_in (img f) (cod f)"
    proof (unfold img_def)
      have 1: "Img f \<subseteq> Cod f \<and> Cod f \<subseteq> Univ"
        using assms Fun_mapsto by auto
      hence 2: "ide (mkIde (Img f))" by fastforce
      moreover have "ide (cod f)" using assms by auto
      moreover have "set (mkIde (Img f)) \<subseteq> Cod f"
        using 1 2 by force
      ultimately show "incl_in (mkIde (Img f)) (cod f)"
        using incl_in_def by blast
    qed

    lemma img_point_elem_set:
    assumes "x \<in> hom unity a"
    shows "img x \<in> set a"
    proof -
      have "incl_in (img x) a"
        using assms incl_in_img_cod by auto
      hence "set (img x) \<subseteq> set a"
        using incl_in_def by blast
      moreover have "img x \<in> set (img x)"
        using assms img_point_in_Univ terminal_char2 by blast
      ultimately show ?thesis by auto
    qed

    text{*
      The corestriction of an arrow @{term f} is the arrow
      @{term "corestr f \<in> hom (dom f) (img f)"} that induces the same function
      on the universe as @{term f}.
    *}

    definition corestr
    where "corestr f = mkArr (Dom f) (Img f) (Fun f)"
    
    lemma corestr_in_hom:
    assumes "arr f"
    shows "corestr f \<in> hom (dom f) (img f)"
    proof -
      have "Fun f \<in> Dom f \<rightarrow> Fun f ` Dom f \<and> Dom f \<subseteq> Univ"
        using assms by auto
      moreover have "Fun f ` Dom f \<subseteq> Univ"
      proof -
        have "Fun f ` Dom f \<subseteq> Cod f \<and> Cod f \<subseteq> Univ"
          using assms Fun_mapsto by auto
        thus ?thesis by blast
      qed
      ultimately have "mkArr (Dom f) (Fun f ` Dom f) (Fun f) \<in> hom (dom f) (img f)"
        using assms img_def mkArr_in_hom by force
      thus ?thesis using corestr_def by presburger
    qed
    
    text{*
      Every arrow factors as a corestriction followed by an inclusion.
    *}

    lemma img_fact:
    assumes "arr f"
    shows "S (incl_of (img f) (cod f)) (corestr f) = f"
    proof (intro arr_eqI)
      have 1: "corestr f \<in> hom (dom f) (img f)"
        using assms corestr_in_hom by blast
      moreover have 2: "incl_of (img f) (cod f) \<in> hom (img f) (cod f)"
        using assms incl_in_img_cod incl_incl_of by presburger
      ultimately show P: "par (S (incl_of (img f) (cod f)) (corestr f)) f"
        using assms by auto
      show "Fun (S (incl_of (img f) (cod f)) (corestr f)) = Fun f"
      proof -
        have "Fun (S (incl_of (img f) (cod f)) (corestr f))
                 = restrict (Fun (incl_of (img f) (cod f)) o Fun (corestr f)) (Dom f)"
          using Fun_comp 1 2 by force
        also have
           "... = restrict (restrict (\<lambda>x. x) (Img f) o restrict (Fun f) (Dom f)) (Dom f)"
        proof -
          have "Fun (corestr f) = restrict (Fun f) (Dom f)"
            using assms corestr_def [of f] Fun_mkArr [of "Dom f" "Img f" "Fun f"] corestr_in_hom
            by force
          moreover have "Fun (incl_of (img f) (cod f)) = restrict (\<lambda>x. x) (Img f)"
          proof -
            have "incl_in (img f) (cod f)" using assms incl_in_img_cod by blast
            hence "arr (incl_of (img f) (cod f))" using incl_incl_of by force
            moreover have "incl_of (img f) (cod f) = mkArr (Img f) (Cod f) (\<lambda>x. x)"
              using assms by fastforce
            moreover have "mkIde (Img f) = img f"
              using assms img_def by presburger
            ultimately show ?thesis using assms Fun_mkArr by metis
          qed
          ultimately show ?thesis by presburger
        qed
        also have "... = Fun f"
        proof
          fix x
          have "x \<notin> Dom f \<Longrightarrow>
                  restrict (restrict (\<lambda>x. x) (Img f) o restrict (Fun f) (Dom f)) (Dom f) x = Fun f x"
            using assms extensional_restrict Fun_mapsto [of f] extensional_arb [of "Fun f" "Dom f" x]
            by simp
          moreover have
               "x \<in> Dom f \<Longrightarrow>
                  restrict (restrict (\<lambda>x. x) (Img f) o restrict (Fun f) (Dom f)) (Dom f) x = Fun f x"
            by simp
          ultimately show
              "restrict (restrict (\<lambda>x. x) (Img f) o restrict (Fun f) (Dom f)) (Dom f) x = Fun f x"
            by auto
        qed
        finally show ?thesis by auto
      qed
    qed

    lemma Fun_corestr:
    assumes "arr f"
    shows "Fun (corestr f) = Fun f"
    proof -
      have 1: "f = S (incl_of (img f) (cod f)) (corestr f)"
        using assms img_fact by presburger
      hence 2: "Fun f = restrict (Fun (incl_of (img f) (cod f)) o Fun (corestr f)) (Dom f)"
        using assms Fun_comp [of "corestr f" "incl_of (img f) (cod f)"] 
        by (metis (full_types) arr_compD(1) arr_compD(2) arr_compD(3) dom_comp)
      also have "... = restrict (Fun (corestr f)) (Dom f)"
        using assms incl_incl_of [of "img f" "cod f"] Fun_incl [of f] incl_in_img_cod [of f]
              corestr_def [of f] corestr_in_hom [of f] Fun_mkArr [of "Dom f" "Img f" "Fun f"]
        by auto
      also have "... = Fun (corestr f)"
        using assms Fun_mapsto [of "corestr f"] corestr_in_hom [of f] extensional_restrict by auto
      finally show ?thesis by auto
    qed
    
    subsection "Points and Terminal Objects"

    text{*
      To each element @{term t} of @{term "set a"} is associated a point
      @{term "mkPoint a t \<in> hom unity a"}.  The function induced by such
      a point is the constant-@{term t} function on the set @{term "{unity}"}.
    *}

    definition mkPoint
    where "mkPoint a t \<equiv> mkArr {unity} (set a) (\<lambda>_. t)"

    lemma mkPoint_in_hom:
    assumes "ide a" and "t \<in> set a"
    shows "mkPoint a t \<in> hom unity a"
      using assms mkArr_in_hom [of "{unity}" "set a" "\<lambda>_. t"]
      by (metis (no_types, lifting) Pi_I mem_Collect_eq mkIde_set set_subset_Univ
          terminal_char2 terminal_unity mkPoint_def)

    lemma Fun_mkPoint:
    assumes "ide a" and "t \<in> set a"
    shows "Fun (mkPoint a t) = (\<lambda>_ \<in> {unity}. t)"
      using assms mkPoint_def terminal_unity by force

    text{*
      For each object @{term a} the function @{term "mkPoint a"} has as its inverse
      the restriction of the function @{term img} to @{term "hom unity a"}
    *}

    lemma mkPoint_img:
    shows "img \<in> hom unity a \<rightarrow> set a"
    and "\<And>x. x \<in> hom unity a \<Longrightarrow> mkPoint a (img x) = x"
    proof -
      show "img \<in> hom unity a \<rightarrow> set a"
      proof
        fix x
        assume x: "x \<in> hom unity a"
        show "img x \<in> set a"
        proof -
          have "incl_in (img x) (cod x)"
            using x incl_in_img_cod mem_Collect_eq by blast
          hence "set (img x) \<subseteq> set a"
            using x incl_in_def by blast
          moreover have "img x \<in> set (img x)"
            using x img_point_in_Univ terminal_char2 by blast
          ultimately show ?thesis by auto
        qed
      qed
      show "\<And>x. x \<in> hom unity a \<Longrightarrow> mkPoint a (img x) = x"
      proof -
        fix x
        assume x: "x \<in> hom unity a"
        show "mkPoint a (img x) = x"
        proof (intro arr_eqI)
          have 0: "img x \<in> set a"
          proof -
            have "set (img x) = Fun x ` {unity}"
              using x img_def terminal_unity terminal_char2 mem_Collect_eq set_img by force
            moreover from this have "... \<subseteq> set a"
              using x Fun_mapsto
              by (metis (mono_tags, lifting) mem_Collect_eq incl_in_img_cod incl_in_def)
            ultimately show ?thesis
              by (metis elem_set_implies_incl_in elem_set_implies_set_eq_singleton extensional_set 
                        image_insert image_is_empty image_subset_iff incl_in_def singleton_iff)
          qed
          hence 1: "mkPoint a (img x) \<in> hom unity a"
            using x mkPoint_in_hom by force
          thus "par (mkPoint a (img x)) x"
            using x by auto
          have "Fun (mkPoint a (img x)) = (\<lambda>_ \<in> {unity}. img x)"
            using 1 mkPoint_def by simp
          also have "... = Fun x"
          proof
            fix z
            have "z \<noteq> unity \<Longrightarrow> (\<lambda>_ \<in> {unity}. img x) z = Fun x z"
              using x Fun_mapsto Fun_def restrict_apply singletonD terminal_char2 terminal_unity
             by auto
            moreover have "(\<lambda>_ \<in> {unity}. img x) unity = Fun x unity"
            proof -
              have "(\<lambda>_ \<in> {unity}. img x) ` {unity} = Fun x ` {unity}"
              proof -
                have "(\<lambda>_ \<in> {unity}. img x) ` {unity} = {img x}" by simp
                also have "... = set (img x)"
                  using 0 elem_set_implies_set_eq_singleton by blast
                also have "... = Fun x ` {unity}"
                  using x mem_Collect_eq set_img terminal_char2 terminal_unity by auto
                finally show ?thesis by auto
              qed
              thus ?thesis by simp
            qed
            ultimately show "(\<lambda>_ \<in> {unity}. img x) z = Fun x z" by auto
          qed
          finally show "Fun (mkPoint a (img x)) = Fun x" by auto
        qed
      qed
    qed

    lemma img_mkPoint:
    assumes "ide a"
    shows "mkPoint a \<in> set a \<rightarrow> hom unity a"
    and "\<And>t. t \<in> set a \<Longrightarrow> img (mkPoint a t) = t"
    proof -
      show "mkPoint a \<in> set a \<rightarrow> hom unity a"
      proof
        fix t
        assume t: "t \<in> set a"
        show "mkPoint a t \<in> hom unity a"
          using assms(1) t mkPoint_in_hom by presburger
      qed
      show "\<And>t. t \<in> set a \<Longrightarrow> img (mkPoint a t) = t"
        proof -
        fix t
        assume t: "t \<in> set a"
        show "img (mkPoint a t) = t"
        proof -
          have 1: "arr (mkPoint a t)"
            using assms t mkPoint_in_hom by simp
          have "Fun (mkPoint a t) ` {unity} = {t}"
            using 1 mkPoint_def by simp
          thus ?thesis
            by (metis 1 t elem_set_implies_incl_in elem_set_implies_set_eq_singleton img_def
                      incl_in_def dom_mkArr mkIde_set terminal_char2 terminal_unity mkPoint_def)
        qed
      qed
    qed

    text{*
      For each object @{term a} the elements of @{term "hom unity a"} are therefore in
      bijective correspondence with @{term "set a"}.
    *}

    lemma bij_betw_points_and_set:
    assumes "ide a"
    shows "bij_betw img (hom unity a) (set a)"
    proof (intro bij_betwI)
      show "img \<in> hom unity a \<rightarrow> set a"
        using assms mkPoint_img by auto
      show "mkPoint a \<in> set a \<rightarrow> hom unity a"
        using assms img_mkPoint by auto
      show "\<And>x. x \<in> hom unity a \<Longrightarrow> mkPoint a (img x) = x"
        using assms mkPoint_img by auto
      show "\<And>t. t \<in> set a \<Longrightarrow> img (mkPoint a t) = t"
        using assms img_mkPoint by auto
    qed

    text{*
      The function on the universe induced by an arrow @{term f} agrees, under the bijection
      between @{term "hom unity (dom f)"} and @{term "Dom f"}, with the action of @{term f}
      by composition on @{term "hom unity (dom f)"}.
    *}

    lemma Fun_point:
    assumes "x \<in> hom unity a"
    shows "Fun x = (\<lambda>_ \<in> {unity}. img x)"
    proof -
      have "x = mkPoint a (img x)"
        using assms mkPoint_img img_mkPoint by auto
      thus ?thesis
        using assms Fun_mkPoint [of a "img x"] img_point_elem_set by force
    qed

    lemma comp_arr_mkPoint:
    assumes "arr f" and "t \<in> Dom f"
    shows "S f (mkPoint (dom f) t) = mkPoint (cod f) (Fun f t)"
    proof (intro arr_eqI)
      have 0: "seq f (mkPoint (dom f) t)"
        using assms mkPoint_in_hom [of "dom f" t] by simp
      have 1: "S f (mkPoint (dom f) t) \<in> hom unity (cod f)"
        using assms mkPoint_in_hom [of "dom f" t] by simp
      show "par (S f (mkPoint (dom f) t)) (mkPoint (cod f) (Fun f t))"
      proof -
        have "mkPoint (cod f) (Fun f t) \<in> hom unity (cod f)"
          using assms Fun_mapsto [of f] mkPoint_in_hom [of "cod f" "Fun f t"] by auto
        thus ?thesis using 1 by auto
      qed
      show "Fun (S f (mkPoint (dom f) t)) = Fun (mkPoint (cod f) (Fun f t))"
      proof -
        have "Fun (S f (mkPoint (dom f) t)) = restrict (Fun f o Fun (mkPoint (dom f) t)) {unity}"
          using assms 0 1 Fun_comp [of "mkPoint (dom f) t" f] terminal_char2 terminal_unity
          by auto
        also have "... = restrict (Fun f o (\<lambda>_ \<in> {unity}. t)) {unity}"
          using assms Fun_mkPoint by simp
        also have "... = (\<lambda>_ \<in> {unity}. Fun f t)"
          by auto
        also have "... = Fun (mkPoint (cod f) (Fun f t))"
          using assms Fun_mkPoint [of "cod f" "Fun f t"] Fun_mapsto [of f] by fastforce
        finally show ?thesis by auto
      qed
    qed

    lemma comp_arr_point:
    assumes "arr f" and "x \<in> hom unity (dom f)"
    shows "S f x = mkPoint (cod f) (Fun f (img x))"
    proof -
      have "x = mkPoint (dom f) (img x)" using assms mkPoint_img by simp
      thus ?thesis using assms comp_arr_mkPoint [of f "img x"]
        by (simp add: img_point_elem_set)
    qed

    text{*
      This agreement allows us to express @{term "Fun f"} in terms of composition.
    *}

    lemma Fun_in_terms_of_comp:
    assumes "arr f"
    shows "Fun f = restrict (img o S f o mkPoint (dom f)) (Dom f)"
    proof
      fix t
      have "t \<notin> Dom f \<Longrightarrow> Fun f t = restrict (img o S f o mkPoint (dom f)) (Dom f) t"
        using assms by (simp add: Fun_def)
      moreover have "t \<in> Dom f \<Longrightarrow> Fun f t = restrict (img o S f o mkPoint (dom f)) (Dom f) t"
      proof -
        assume t: "t \<in> Dom f"
        have 1: "S f (mkPoint (dom f) t) = mkPoint (cod f) (Fun f t)"
          using assms t comp_arr_mkPoint by simp
        hence "img (S f (mkPoint (dom f) t)) = img (mkPoint (cod f) (Fun f t))" by simp
        thus ?thesis
        proof -
          have "Fun f t \<in> Cod f" using assms t Fun_mapsto by auto
          thus ?thesis
            using assms t 1 img_mkPoint by auto
        qed
      qed
      ultimately show "Fun f t = restrict (img o S f o mkPoint (dom f)) (Dom f) t" by auto
    qed

    text{*
      We therefore obtain a rule for proving parallel arrows equal by showing
      that they have the same action by composition on points.
    *}

    (*
     * TODO: Find out why attempts to use this as the main rule for a proof loop
     * unless the specific instance is given.
     *)
    lemma arr_eqI':
    assumes "par f f'" and "\<And>x. x \<in> hom unity (dom f) \<Longrightarrow> S f x = S f' x"
    shows "f = f'"
    proof (intro arr_eqI)
      show "par f f'" using assms by auto
      show "Fun f = Fun f'"
      proof -
        have "Fun f = (\<lambda>t \<in> Dom f. img (S f (mkPoint (dom f) t)))"
          using assms Fun_in_terms_of_comp by fastforce
        also have "... = (\<lambda>t \<in> Dom f. img (S f' (mkPoint (dom f) t)))"
        proof -
          have 1: "Dom f = Dom f" by auto
          have 2: "\<And>t. t \<in> Dom f \<Longrightarrow>
                     img (S f (mkPoint (dom f) t)) = img (S f' (mkPoint (dom f) t))"
          proof -
            fix t
            assume t: "t \<in> Dom f"
            have "mkPoint (dom f) t \<in> hom unity (dom f)"
              using assms t mkPoint_in_hom by auto
            thus "img (S f (mkPoint (dom f) t)) = img (S f' (mkPoint (dom f) t))"
              using assms by simp
          qed
          show ?thesis using 1 2 by auto
        qed
        also have "... = Fun f'"
          using assms Fun_in_terms_of_comp by fastforce
        finally show ?thesis by auto
      qed
    qed

    text{*
      An arrow can therefore be specified by giving its action by composition on points.
      In many situations, this is more natural than specifying it as a function on the universe.
    *}

    definition mkArr'
    where "mkArr' a b F = mkArr (set a) (set b) (img o F o mkPoint a)"

    lemma mkArr'_in_hom:
    assumes "ide a" and "ide b" and "F \<in> hom unity a \<rightarrow> hom unity b"
    shows "mkArr' a b F \<in> hom a b"
    proof -
      have "img o F o mkPoint a \<in> set a \<rightarrow> set b"
      proof
        fix t
        assume t: "t \<in> set a"
        thus "(img o F o mkPoint a) t \<in> set b"
          using assms mkPoint_in_hom [of a t] img_point_elem_set [of "F (mkPoint a t)" b]
          by auto
      qed
      thus "mkArr' a b F \<in> hom a b" using assms mkArr'_def by simp
    qed

    lemma comp_point_mkArr':
    assumes "ide a" and "ide b" and "F \<in> hom unity a \<rightarrow> hom unity b"
    shows "\<And>x. x \<in> hom unity a \<Longrightarrow> S (mkArr' a b F) x = F x"
    proof -
      fix x
      assume x: "x \<in> hom unity a"
      have "Fun (mkArr' a b F) (img x) = img (F x)"
        using assms x mkArr'_def mkArr'_in_hom Fun_mkArr img_point_elem_set mkPoint_img
          by simp
      hence "S (mkArr' a b F) x = mkPoint b (img (F x))"
        using assms x mkArr'_in_hom [of a b F] comp_arr_point [of "mkArr' a b F" x]
        by auto
      thus "S (mkArr' a b F) x = F x"
        using assms x mkPoint_img(2) [of "F x" b] by auto
    qed

    text{*
      A third characterization of terminal objects is as those objects whose set of
      points is a singleton.
    *}

    lemma terminal_char3:
    assumes "\<exists>!x. x \<in> hom unity a"
    shows "terminal a"
    proof -
      have a: "ide a"
        using assms ide_cod mem_Collect_eq by blast
      hence 1: "bij_betw img (hom unity a) (set a)"
        using assms bij_betw_points_and_set by auto
      hence "img ` (hom unity a) = set a"
        by (simp add: bij_betw_def)
      moreover have "hom unity a = {THE x. x \<in> hom unity a}"
        using assms theI' [of "\<lambda>x. x \<in> hom unity a"] by auto
      ultimately have "set a = {img (THE x. x \<in> hom unity a)}"
        by force
      thus ?thesis using a terminal_char1 by simp
    qed

    text{*
      The following is an alternative formulation of functional completeness, which says that
      any function on points uniquely determines an arrow.
    *}

    lemma fun_complete':
    assumes "ide a" and "ide b" and "F \<in> hom unity a \<rightarrow> hom unity b"
    shows "\<exists>!f. f \<in> hom a b \<and> (\<forall>x. x \<in> hom unity a \<longrightarrow> S f x = F x)"
    proof
      have 1: "mkArr' a b F \<in> hom a b" using assms mkArr'_in_hom by auto
      moreover have 2: "\<And>x. x \<in> hom unity a \<Longrightarrow> S (mkArr' a b F) x = F x"
        using assms comp_point_mkArr' by auto
      ultimately show "mkArr' a b F \<in> hom a b
                        \<and> (\<forall>x. x \<in> hom unity a \<longrightarrow> S (mkArr' a b F) x = F x)" by blast    
      fix f
      assume f: "f \<in> hom a b \<and> (\<forall>x. x \<in> hom unity a \<longrightarrow> S f x = F x)"
      show "f = mkArr' a b F"
        using f 1 2 apply (intro arr_eqI' [of f "mkArr' a b F"]) by auto
    qed

    subsection "The `Determines Same Function' Relation on Arrows"

    text{*
      An important part of understanding the structure of a category of sets and functions
      is to characterize when it is that two arrows ``determine the same function''.
      The following result provides one answer to this: two arrows with a common domain
      determine the same function if and only if they can be rendered equal by composing with
      a cospan of inclusions.
    *}

    lemma eq_Fun_iff_incl_joinable:
    assumes "span f f'"
    shows "Fun f = Fun f' \<longleftrightarrow> (\<exists>m m'. incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> S m f = S m' f')"
    proof
      assume ff': "Fun f = Fun f'"
      let ?b = "mkIde (Cod f \<union> Cod f')"
      let ?m = "incl_of (cod f) ?b"
      let ?m' = "incl_of (cod f') ?b"
      have "incl ?m"
        using assms incl_incl_of [of "cod f" ?b] incl_in_def [of "cod f" ?b] by simp
      have "incl ?m'"
        using assms incl_incl_of [of "cod f'" ?b] incl_in_def [of "cod f'" ?b] by simp
      have M: "?m = mkArr (Cod f) (Cod f \<union> Cod f') (\<lambda>x. x)"
        by (simp add: assms)
      have M': "?m' = mkArr (Cod f') (Cod f \<union> Cod f') (\<lambda>x. x)"
        by (simp add: assms)
      have par: "par (S ?m f) (S ?m' f')" using assms M M' by simp
      have seq: "seq ?m f \<and> seq ?m' f'" using assms M M' by simp
      have "S ?m f = S ?m' f'"
      proof (intro arr_eqI)
        show "par (S ?m f) (S ?m' f')" using assms by simp
        show "Fun (S ?m f) = Fun (S ?m' f')"
        proof -
          have "Fun (S ?m f) = restrict (\<lambda>x. Fun ?m (Fun f x)) (Dom f)"
            using seq Fun_comp [of ?m f] by auto
          also have "... = restrict (\<lambda>x. Fun ?m' (Fun f' x)) (Dom f')"
            using assms ff' Fun_mapsto by fastforce
          also have "... = Fun (S ?m' f')" using seq Fun_comp by auto
          finally show ?thesis by auto
        qed
      qed
      hence "incl ?m \<and> incl ?m' \<and> seq ?m f \<and> seq ?m' f' \<and> S ?m f = S ?m' f'"
        using seq `incl ?m` `incl ?m'` by simp
      thus "\<exists>m m'. incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> S m f = S m' f'" by blast
      next
      assume ff': "\<exists>m m'. incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> S m f = S m' f'"
      show "Fun f = Fun f'"
      proof -
        from ff' obtain m m' where mm': "incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> S m f = S m' f'"
          by blast
        show ?thesis
          using ff' mm' Fun_incl
          by (metis arr_cod_iff_arr comp_cod_arr dom_cod ide_dom Fun_comp Fun_ide)
      qed
    qed

    text{*
      Another answer to the same question: two arrows with a common domain determine the
      same function if and only if their corestrictions are equal.
    *}

    lemma eq_Fun_iff_eq_corestr:
    assumes "span f f'"
    shows "Fun f = Fun f' \<longleftrightarrow> corestr f = corestr f'"
    proof
      assume ff': "Fun f = Fun f'"
      show "corestr f = corestr f'"
        using assms ff' corestr_def by simp
      next
      assume ff': "corestr f = corestr f'"
      show "Fun f = Fun f'"
        using assms ff' Fun_corestr by metis
    qed

    subsection "Retractions, Sections, and Isomorphisms"

    text{*
      An arrow is a retraction if and only if its image coincides with its codomain.
    *}

    lemma retraction_if_Img_eq_Cod:
    assumes "arr g" and "Img g = Cod g"
    shows "section_retraction (mkArr (Cod g) (Dom g) (Hilbert_Choice.inv_into (Dom g) (Fun g))) g"
    proof -
      let ?F = "Hilbert_Choice.inv_into (Dom g) (Fun g)"
      let ?f = "mkArr (Cod g) (Dom g) ?F"
      have f: "arr ?f"
      proof
        have "Cod g \<subseteq> Univ \<and> Dom g \<subseteq> Univ" using assms by auto
        moreover have "?F \<in> Cod g \<rightarrow> Dom g"
        proof
          fix y
          assume y: "y \<in> Cod g"
          let ?P = "\<lambda>x. x \<in> Dom g \<and> Fun g x = y"
          have "\<exists>x. ?P x" using y assms by force
          hence "?P (SOME x. ?P x)" using someI_ex [of ?P] by fast
          hence "?P (?F y)" using Hilbert_Choice.inv_into_def by metis
          thus "?F y \<in> Dom g" by auto
        qed
        ultimately show "Cod g \<subseteq> Univ \<and> Dom g \<subseteq> Univ \<and> ?F \<in> Cod g \<rightarrow> Dom g" by auto
      qed
      show "section_retraction ?f g"
      proof
        show 1: "antipar ?f g" using f assms by simp
        show "ide (S g ?f)"
        proof -
          have "g = mkArr (Dom g) (Cod g) (Fun g)" using assms by auto
          hence "S g ?f = mkArr (Cod g) (Cod g) (Fun g o ?F)"
            using 1 comp_mkArr by metis
          moreover have "mkArr (Cod g) (Cod g) (\<lambda>y. y) = ..."
          proof (intro mkArr_eqI')
            show "arr (mkArr (Cod g) (Cod g) (\<lambda>y. y))" using assms by auto
            show "\<And>y. y \<in> Cod g \<Longrightarrow> y = (Fun g o ?F) y"
              using assms by (simp add: f_inv_into_f)
          qed
          ultimately show ?thesis using assms f by auto
        qed
      qed
    qed

    lemma retraction_char:
    shows "retraction g \<longleftrightarrow> arr g \<and> Img g = Cod g"
    proof
      assume G: "retraction g"
      show "arr g \<and> Img g = Cod g"
      proof
        show "arr g" using G section_retraction_def by blast
        show "Img g = Cod g"
        proof -
          from G obtain f where f: "section_retraction f g" by blast
          have "Fun (S g f) = restrict (Fun g o Fun f) (Cod g)"
            using f section_retraction_def [of f g] Fun_comp [of f g] by auto
          moreover have "Fun (S g f) = restrict (\<lambda>x. x) (Cod g)"
            using f Fun_ide ide_comp_simp section_retractionD(4) section_retractionD(5) by auto
          ultimately have 1: "restrict (Fun g o Fun f) (Cod g) = restrict (\<lambda>x. x) (Cod g)"
            by simp
          hence "Fun g ` Fun f ` Cod g = Cod g"
            by (metis image_comp image_ident image_restrict_eq)
          moreover have "Fun f ` Cod g \<subseteq> Dom g"
            using f Fun_mapsto
            by (metis arr_mkArr funcset_image mkArr_Fun section_retractionD(1)
                      section_retractionD(3) section_retractionD(4))
          moreover have "Img g \<subseteq> Cod g"
            using f section_retraction_def Fun_mapsto by blast
          ultimately show ?thesis by blast
        qed
      qed
      next
      assume "arr g \<and> Img g = Cod g"
      thus "retraction g" using retraction_if_Img_eq_Cod by blast
    qed

    text{*
      Every corestriction is a retraction.
    *}

    lemma retraction_corestr:
    assumes "arr f"
    shows "retraction (corestr f)"
      using assms retraction_char Fun_corestr corestr_in_hom by simp

    text{*
      An arrow is a section if and only if it induces an injective function on its
      domain, except in the special case that it has an empty domain set and a
      nonempty codomain set.
    *}

    lemma section_if_inj:
    assumes "arr f" and "inj_on (Fun f) (Dom f)" and "Dom f = {} \<longrightarrow> Cod f = {}"
    shows "section_retraction f (mkArr (Cod f) (Dom f)
                                       (\<lambda>y. if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                                            else SOME x. x \<in> Dom f))"
    proof -
      let ?P= "\<lambda>y. \<lambda>x. x \<in> Dom f \<and> Fun f x = y"
      let ?G = "\<lambda>y. if y \<in> Img f then SOME x. ?P y x else SOME x. x \<in> Dom f"
      let ?g = "mkArr (Cod f) (Dom f) ?G"
      have g: "arr ?g"
      proof -
        have 1: "Cod f \<subseteq> Univ" using assms by simp
        have 2: "Dom f \<subseteq> Univ" using assms by simp
        have 3: "?G \<in> Cod f \<rightarrow> Dom f"
        proof
          fix y
          assume Y: "y \<in> Cod f"
          show "?G y \<in> Dom f"
          proof (cases "y \<in> Img f")
            assume "y \<in> Img f"
            hence "(\<exists>x. ?P y x) \<and> ?G y = (SOME x. ?P y x)" using Y by auto
            hence "?P y (?G y)" using someI_ex [of "?P y"] by presburger
            thus "?G y \<in> Dom f" by auto
            next
            assume "y \<notin> Img f"
            hence "(\<exists>x. x \<in> Dom f) \<and> ?G y = (SOME x. x \<in> Dom f)" using assms Y by auto
            thus "?G y \<in> Dom f" using someI_ex [of "\<lambda>x. x \<in> Dom f"] by presburger
          qed
        qed
        show ?thesis using 1 2 3 by simp
      qed
      show "section_retraction f ?g"
      proof
        show 1: "antipar f ?g" using assms g by simp
        show "ide (S ?g f)"
        proof -
          have "f = mkArr (Dom f) (Cod f) (Fun f)" using assms by auto
          hence "S ?g f = mkArr (Dom f) (Dom f) (?G o Fun f)"
            using 1 comp_mkArr [of "Dom f" "Cod f" "Fun f" "Dom f" ?G] by presburger
          moreover have "mkArr (Dom f) (Dom f) (\<lambda>x. x) = ..."
          proof (intro mkArr_eqI')
            show "arr (mkArr (Dom f) (Dom f) (\<lambda>x. x))" using assms by auto
            show "\<And>x. x \<in> Dom f \<Longrightarrow> x = (?G o Fun f) x"
            proof -
              fix x
              assume x: "x \<in> Dom f"
              have "Fun f x \<in> Img f" using x by blast
              hence "(\<exists>x'. ?P (Fun f x) x') \<and> ?G (Fun f x) = (SOME x'. ?P (Fun f x) x')"
                by auto
              moreover from this have "?P (Fun f x) (?G (Fun f x))"
                using someI_ex [of "?P (Fun f x)"] by presburger
              ultimately have "x = ?G (Fun f x)"
                using assms x inj_on_def [of "Fun f" "Dom f"] by simp
              thus "x = (?G o Fun f) x" by simp
            qed
          qed
          ultimately show ?thesis using assms by auto
        qed
      qed
    qed

    lemma section_char:
    shows "section f \<longleftrightarrow> arr f \<and> (Dom f = {} \<longrightarrow> Cod f = {}) \<and> inj_on (Fun f) (Dom f)"
    proof
      assume f: "section f"
      from f obtain g where g: "section_retraction f g" using section_def by blast
      show "arr f \<and> (Dom f = {} \<longrightarrow> Cod f = {}) \<and> inj_on (Fun f) (Dom f)"
      proof -
        have "arr f" using f section_retraction_def by blast
        moreover have "Dom f = {} \<longrightarrow> Cod f = {}"
        proof -
          have "Cod f \<noteq> {} \<longrightarrow> Dom f \<noteq> {}"
          proof
            assume "Cod f \<noteq> {}"
            from this obtain y where "y \<in> Cod f" by blast
            hence "Fun g y \<in> Dom f"
              using g Fun_mapsto [of g] by fastforce
            thus "Dom f \<noteq> {}" by blast
          qed
          thus ?thesis by auto
        qed
        moreover have "inj_on (Fun f) (Dom f)"
        proof -
          have "restrict (Fun g o Fun f) (Dom f) = Fun (S g f)"
            using g Fun_comp [of f g]
            by (simp add: calculation(1) section_retractionD(2) section_retractionD(3))
          also have "... = restrict (\<lambda>x. x) (Dom f)"
            using g Fun_ide ide_comp_simp section_retractionD(5) by auto
          finally have "restrict (Fun g o Fun f) (Dom f) = restrict (\<lambda>x. x) (Dom f)" by auto
          thus ?thesis using inj_onI inj_on_imageI2 inj_on_restrict_eq by metis
        qed
        ultimately show ?thesis by auto
      qed
      next
      assume F: "arr f \<and> (Dom f = {} \<longrightarrow> Cod f = {}) \<and> inj_on (Fun f) (Dom f)"
      thus "section f" using section_if_inj by auto
    qed

    text{*
      Section-retraction pairs can also be characterized by an inverse relationship
      between the functions they induce.
    *}

    lemma section_retraction_char:
    shows "section_retraction f g \<longleftrightarrow>
             antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)"
    proof
      show "section_retraction f g \<Longrightarrow>
             antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)"
      proof -
        assume fg: "section_retraction f g"
        have 1: "antipar f g" using fg by auto
        moreover have "compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)"
        proof
          fix x
          have "x \<notin> Dom f \<Longrightarrow> compose (Dom f) (Fun g) (Fun f) x = (\<lambda>x \<in> Dom f. x) x"
            by (simp add: compose_def)
          moreover have "x \<in> Dom f \<Longrightarrow> compose (Dom f) (Fun g) (Fun f) x = (\<lambda>x \<in> Dom f. x) x"
          proof -
            assume x: "x \<in> Dom f"
            have "compose (Dom f) (Fun g) (Fun f) x = restrict (Fun g o Fun f) (Dom f) x"
              using compose_def [of "Dom f" "Fun g" "Fun f"] by simp
            also have "... = Fun (S g f) x"
              using 1 Fun_comp [of f g] by simp
            also have "... = Fun (dom f) x"
              using fg ide_comp_simp by auto
            also have "... = (\<lambda>x \<in> Dom f. x) x"
              using x 1 by simp
            finally show ?thesis by auto
          qed
          ultimately show "compose (Dom f) (Fun g) (Fun f) x = (\<lambda>x \<in> Dom f. x) x" by auto
        qed
        ultimately show ?thesis by auto
      qed
      show "antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)
               \<Longrightarrow> section_retraction f g"
      proof -
        assume fg: "antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)"
        show "section_retraction f g"
        proof
          show 1: "antipar f g" using fg by auto
          show "ide (S g f)"
          proof -
            have "arr (S g f)" using 1 by simp
            moreover have "Dom (S g f) = Cod (S g f)" using 1 by simp
            moreover have "Fun (S g f) = (\<lambda>x \<in> Dom (S g f). x)"
            proof -
              have "Fun (S g f) = restrict (Fun g o Fun f) (Dom f)" using 1 by simp
              also have "... = compose (Dom f) (Fun g) (Fun f)" by simp
              also have "... = (\<lambda>x \<in> Dom (S g f). x)" using fg by auto
              finally show ?thesis by auto
            qed
            ultimately show ?thesis using 1 ide_char [of "S g f"] by blast
          qed
        qed
      qed
    qed

    text{*
      Antiparallel arrows @{term f} and @{term g} are inverses if the functions
      they induce are inverses.
    *}

    lemma inverse_arrows_char:
    shows "inverse_arrows f g \<longleftrightarrow>
             antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)
                         \<and> compose (Dom g) (Fun f) (Fun g) = (\<lambda>y \<in> Dom g. y)"
    proof -
      have "inverse_arrows f g \<longleftrightarrow> section_retraction f g \<and> section_retraction g f"
        by fastforce
      thus ?thesis using section_retraction_char by auto
    qed

    text{*
      An arrow is an isomorphism if and only if the function it induces is a bijection.
    *}

    lemma iso_char:
    shows "iso f \<longleftrightarrow> arr f \<and> bij_betw (Fun f) (Dom f) (Cod f)"
    proof -
      have "iso f \<longleftrightarrow> section f \<and> retraction f"
        using iso_iff_section_and_retraction by auto
      also have "... \<longleftrightarrow> arr f \<and> inj_on (Fun f) (Dom f) \<and> Img f = Cod f"
        using section_char retraction_char by force
      also have "... \<longleftrightarrow> arr f \<and> bij_betw (Fun f) (Dom f) (Cod f)"
        using inj_on_def [of "Fun f" "Dom f"] bij_betw_def [of "Fun f" "Dom f" "Cod f"]
        by meson
      finally show ?thesis by auto
    qed

    text{*
      The inverse of an isomorphism is constructed by inverting the induced function.
    *}

    lemma inv_char:
    assumes "iso f"
    shows "inv f = mkArr (Cod f) (Dom f) (inv_into (Dom f) (Fun f))"
    proof -
      let ?g = "mkArr (Cod f) (Dom f) (inv_into (Dom f) (Fun f))"
      have "section_retraction ?g f"
        using assms iso_is_retraction retraction_char retraction_if_Img_eq_Cod by simp
      moreover have "section_retraction f ?g"
      proof -
        let ?g' = "mkArr (Cod f) (Dom f) (\<lambda>y. if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                                              else SOME x. x \<in> Dom f)"
        have 1: "section_retraction f ?g'"
          using assms iso_is_section section_char section_if_inj by simp
        moreover have "?g' = ?g"
        proof
          show "arr ?g'" using 1 section_retraction_def by meson
          show "\<And>y. y \<in> Cod f \<Longrightarrow> (if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                                                  else SOME x. x \<in> Dom f)
                                     = inv_into (Dom f) (Fun f) y"
          proof -
            fix y
            assume "y \<in> Cod f"
            hence "y \<in> Img f" using assms iso_is_retraction retraction_char by metis
            thus "(if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                   else SOME x. x \<in> Dom f)
                     = inv_into (Dom f) (Fun f) y"
              using inv_into_def by metis
          qed
        qed
        ultimately show ?thesis by auto
      qed
      ultimately have "inverse_arrows f ?g" using section_retraction_def by auto
      thus ?thesis using inverse_unique by blast
    qed

    subsection "Monomorphisms and Epimorphisms"

    text{*
      An arrow is a monomorphism if and only if the function it induces is injective.
    *}

    lemma mono_char:
    shows "mono f \<longleftrightarrow> arr f \<and> inj_on (Fun f) (Dom f)"
    proof
      assume f: "mono f"
      hence "arr f" using mono_def by auto
      moreover have "inj_on (Fun f) (Dom f)"
      proof (intro inj_onI)
        have 0: "inj_on (S f) (hom unity (dom f))"
        proof -
          have 1: "hom unity (dom f) \<subseteq> {g. seq f g}"
            using f mono_def by auto
          show ?thesis
          proof -
            have "inj_on (S f) {s. seq f s}"
              using f mono_def by blast
            hence "\<exists>A. hom unity (dom f) \<subseteq> A \<and> inj_on (S f) A"
              using 1 by blast
            thus ?thesis
              by (meson subset_inj_on)
          qed
        qed
        fix x x'
        assume x: "x \<in> Dom f" and x': "x' \<in> Dom f" and xx': "Fun f x = Fun f x'"
        have 1: "mkPoint (dom f) x \<in> hom unity (dom f) \<and> mkPoint (dom f) x' \<in> hom unity (dom f)"
          using x x' `arr f` mkPoint_in_hom by simp
        hence 2: "S f (mkPoint (dom f) x) \<in> hom unity (cod f) \<and>
                  S f (mkPoint (dom f) x') \<in> hom unity (cod f)"
          using `arr f` by simp
        have "S f (mkPoint (dom f) x) = S f (mkPoint (dom f) x')"
          using `arr f` x x' xx' comp_arr_mkPoint by simp
        hence "mkPoint (dom f) x = mkPoint (dom f) x'"
          using 0 1 inj_onD [of "S f" "hom unity (dom f)" "mkPoint (dom f) x"] by simp
        thus "x = x'"
          using `arr f` x x' img_mkPoint(2) [of "dom f" x] img_mkPoint(2) [of "dom f" x'] ide_dom
          by presburger
      qed
      ultimately show "arr f \<and> inj_on (Fun f) (Dom f)" by auto
      next
      assume f: "arr f \<and> inj_on (Fun f) (Dom f)"
      show "mono f"
      proof
        show "arr f" using f by auto
        show "\<And>g g'. \<lbrakk> seq f g; seq f g'; S f g = S f g' \<rbrakk> \<Longrightarrow> g = g'"
        proof -
          fix g g'
          assume g: "seq f g" and g': "seq f g'" and gg': "S f g = S f g'"
          show "g = g'"
          proof (intro arr_eqI)
            show par: "par g g'"
              using g g' gg' dom_comp by metis
            show "Fun g = Fun g'"
            proof
              fix x
              have "x \<notin> Dom g \<Longrightarrow> Fun g x = Fun g' x"
                using g g' by (simp add: par Fun_def)
              moreover have "x \<in> Dom g \<Longrightarrow> Fun g x = Fun g' x"
              proof -
                assume x: "x \<in> Dom g"
                have "Fun f (Fun g x) = Fun (S f g) x"
                  using g x by auto
                also have "... = Fun (S f g') x"
                  using gg' by auto
                also have "... = Fun f (Fun g' x)"
                  using par g' x by auto
                finally have "Fun f (Fun g x) = Fun f (Fun g' x)" by auto
                moreover have "Fun g x \<in> Dom f \<and> Fun g' x \<in> Dom f"
                  using par g g' x Fun_mapsto by fastforce
                ultimately show "Fun g x = Fun g' x"
                  using f gg' inj_onD [of "Fun f" "Dom f" "Fun g x" "Fun g' x"]
                  by simp
              qed
              ultimately show "Fun g x = Fun g' x" by auto
            qed
          qed
        qed
      qed
    qed

    text{*
      Inclusions are monomorphisms.
    *}

    lemma mono_imp_incl:
    assumes "incl f"
    shows "mono f"
    proof -
      have "arr f" using assms incl_def by auto
      moreover have "Fun f = (\<lambda>x \<in> Dom f. x)"
        using assms Fun_incl by auto
      moreover have "inj_on (\<lambda>x \<in> Dom f. x) (Dom f)" by auto
      ultimately show ?thesis using mono_char by auto
    qed

    text{*
      A monomorphism is a section, except in case it has an empty domain set and
      a nonempty codomain set.
    *}

    lemma mono_imp_section:
    assumes "mono f" and "Dom f = {} \<longrightarrow> Cod f = {}"
    shows "section f"
      using assms mono_char section_char by auto

    text{*
      An arrow is an epimorphism if and only if either its image coincides with its
      codomain, or else the universe has only a single element (in which case all arrows
      are epimorphisms).
    *}
  
    lemma epi_char:
    shows "epi f \<longleftrightarrow> arr f \<and> (Img f = Cod f \<or> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t'))"
    proof
      assume epi: "epi f"
      show "arr f \<and> (Img f = Cod f \<or> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t'))"
      proof -
        have f: "arr f" using epi epi_implies_arr by auto
        moreover have "\<not>(\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t') \<Longrightarrow> Img f = Cod f"
        proof -
          assume "\<not>(\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t')"
          from this obtain tt and ff
            where B: "tt \<in> Univ \<and> ff \<in> Univ \<and> tt \<noteq> ff" by blast
          show "Img f = Cod f"
          proof
            show "Img f \<subseteq> Cod f" using f Fun_mapsto by auto
            show "Cod f \<subseteq> Img f"
            proof
              let ?g = "mkArr (Cod f) {ff, tt} (\<lambda>y. tt)"
              let ?g' = "mkArr (Cod f) {ff, tt} (\<lambda>y. if \<exists>x. x \<in> Dom f \<and> Fun f x = y
                                                     then tt else ff)"
              let ?b = "mkIde {ff, tt}"
              have g: "?g \<in> hom (cod f) ?b \<and> Fun ?g = (\<lambda>y \<in> Cod f. tt)"
                using f B `arr f` by auto
              have g': "?g' \<in> hom (cod f) ?b \<and>
                        Fun ?g' = (\<lambda>y \<in> Cod f. if \<exists>x. x \<in> Dom f \<and> Fun f x = y then tt else ff)"
                using `arr f` B by simp
              have "S ?g f = S ?g' f"
                using f g g' apply (intro arr_eqI)
                (* 2 *) using restr_eqI apply force
                (* 1 *) by fastforce
              hence gg': "?g = ?g'"
                using epi f g g' epiE [of f ?g ?g'] by simp
              fix y
              assume y: "y \<in> Cod f"
              have "Fun ?g' y = tt" using gg' g y restrict_apply by simp
              hence "(if \<exists>x. x \<in> Dom f \<and> Fun f x = y then tt else ff) = tt"
                using g y by simp
              hence "\<exists>x. x \<in> Dom f \<and> Fun f x = y"
                using B by presburger
              thus "y \<in> Img f" by blast
            qed
          qed
        qed
        ultimately show "arr f \<and> (Img f = Cod f \<or> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t'))"
          by fast
      qed
      next
      show "arr f \<and> (Img f = Cod f \<or> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t')) \<Longrightarrow> epi f"
      proof -
        have "arr f \<and> Img f = Cod f \<Longrightarrow> epi f"
        proof -
          assume f: "arr f \<and> Img f = Cod f"
          show "epi f"
            using f arr_eqI' epiE retractionI retraction_if_Img_eq_Cod retraction_is_epi
            by meson
        qed
        moreover have "arr f \<and> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t') \<Longrightarrow> epi f"
        proof -
          assume f: "arr f \<and> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t')"
          have "\<And>f f'. par f f' \<Longrightarrow> f = f'"
          proof -
            fix f f'
            assume ff': "par f f'"
            show "f = f'"
            proof (intro arr_eqI)
              show "par f f'" using ff' by simp
              have 1: "\<And>t t'. t \<in> Cod f \<and> t' \<in> Cod f \<Longrightarrow> t = t'"
                using f ff' set_subset_Univ ide_cod set_mp by blast
              show "Fun f = Fun f'"
                using 1 ff' Fun_mapsto [of f] Fun_mapsto [of f']
                      extensional_arb [of "Fun f" "Dom f"] extensional_arb [of "Fun f'" "Dom f"]
                by fastforce
            qed
          qed
          thus "epi f" using f by (metis cod_comp epiI)
        qed
        ultimately show "arr f \<and> (Img f = Cod f \<or> 
                                  (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t')) \<Longrightarrow> epi f"
          by auto
      qed
    qed

    text{*
      An epimorphism is a retraction, except in the case of a degenerate universe with only
      a single element.
    *}

    lemma epi_imp_retraction:
    assumes "epi f" and "\<exists>t t'. t \<in> Univ \<and> t' \<in> Univ \<and> t \<noteq> t'"
    shows "retraction f"
      using assms epi_char retraction_char by auto

    text{*
      Retraction/inclusion factorization is unique (not just up to isomorphism -- remember
      that the notion of inclusion is not categorical but depends on the arbitrarily chosen
      @{term img}).
    *}

    lemma unique_retr_incl_fact:
    assumes "seq m e" and "seq m' e'" and "S m e = S m' e'"
    and "incl m" and "incl m'" and "retraction e" and "retraction e'"
    shows "m = m'" and "e = e'"
    proof -
      have "arr e" using assms(1) by auto
      have "arr e'" using assms(2) by auto
      have "cod m = cod m'"
      proof -
        have "cod m = cod (S m e)" using assms(1) by simp
        also have "... = cod (S m' e')" using assms(1) assms(2) assms(3) by auto
        also have "... = cod m'" using assms(2) by simp
        finally show ?thesis by auto
      qed
      have "dom e = dom e'"
      proof -
        (* It struggles with this if I give too many assumptions at once -- not sure why. *)
        have "dom e = dom (S m e)" using assms(1) by simp
        also have "... = dom (S m' e')" using assms(1) assms(2) assms(3) by auto
        also have "... = dom e'" using assms(2) by simp
        finally show ?thesis by auto
      qed
      hence "span e e'" using assms(1) assms(2) by blast
      moreover have "seq m e \<and> seq m' e' \<and> S m e = S m' e' \<and> incl m \<and> incl m'"
        using assms by blast
      ultimately have "Fun e = Fun e'" using assms eq_Fun_iff_incl_joinable by auto
      hence "img e = img e'" using `arr e` `arr e'` `dom e = dom e'` img_def by auto
      moreover have "img e = cod e \<and> img e' = cod e'"
        using assms(6) assms(7) retraction_char img_def by simp
      ultimately have "par e e'" using `span e e'` by simp
      thus "e = e'" using `Fun e = Fun e'` arr_eqI by blast
      hence "par m m'" using assms(1) assms(2) `cod m = cod m'` by presburger
      thus "m = m'" using assms(4) assms(5) incls_coherent by blast
    qed

  end

  section "Concrete Set Categories"

  text{*
    The @{text set_category} locale is useful for stating results that depend on a
    category of @{typ 'a}-sets and functions, without having to commit to a particular
    element type @{typ 'a}.  However, in applications we often need to work with a
    category of sets and functions that is guaranteed to contain sets corresponding
    to the subsets of some extrinsically given type @{typ 'a}.
    A \emph{concrete set category} is a set category @{text S} that is equipped
    with an injective function @{term \<iota>} from type @{typ 'a} to @{text "S.Univ"}.
    The following locale serves to facilitate some of the technical aspects of passing
    back and forth between elements of type @{typ 'a} and the elements of @{text "S.Univ"}.
  *}

  locale concrete_set_category =
    set_category S
    for S :: "'s comp"
    and U :: "'a set"
    and \<iota> :: "'a \<Rightarrow> 's" +
    assumes \<iota>_mapsto: "\<iota> \<in> U \<rightarrow> Univ"
    and inj_\<iota>: "inj_on \<iota> U"
  begin

    abbreviation \<o>
    where "\<o> \<equiv> Hilbert_Choice.inv_into U \<iota>"

    lemma \<o>_mapsto:
    shows "\<o> \<in> \<iota> ` U \<rightarrow> U"
      by (simp add: inv_into_into)

    lemma \<o>_\<iota> [simp]:
    assumes "x \<in> U"
    shows "\<o> (\<iota> x) = x"
      using assms inj_\<iota> inv_into_f_f by simp
      
    lemma \<iota>_\<o> [simp]:
    assumes "t \<in> \<iota> ` U"
    shows "\<iota> (\<o> t) = t"
      using assms o_def inj_\<iota> by auto

  end

end
