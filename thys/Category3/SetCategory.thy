(*  Title:       SetCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter SetCategory

theory SetCategory
imports Category Functor Subcategory
begin

  text\<open>
    This theory defines a locale \<open>set_category\<close> that axiomatizes the notion
    ``category of @{typ 'a}-sets and functions between them'' in the context of HOL.
    A primary reason for doing this is to make it possible to prove results
    (such as the Yoneda Lemma) that use such categories without having to commit to a
    particular element type @{typ 'a} and without having the results depend on the
    concrete details of a particular construction.
    The axiomatization given here is categorical, in the sense that if categories
    @{term S} and @{term S'} each interpret the \<open>set_category\<close> locale,
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
    then induces a function \<open>Fun f \<in> set (dom f) \<rightarrow> set (cod f)\<close>,
    defined on terminal objects of @{term S} by passing to points of @{term "dom f"},
    composing with @{term f}, then passing back from points of @{term "cod f"}
    to terminal objects.  Once we can associate a set with each object of @{term S}
    and a function with each arrow, we can force @{term S} to be isomorphic to the
    category of @{typ 'a}-sets by imposing suitable extensionality and completeness axioms.
\<close>
 
  section "Some Lemmas about Restriction"

    text\<open>
      \sloppypar
      The development of the \<open>set_category\<close> locale makes heavy use of the
      theory @{theory "HOL-Library.FuncSet"}.  However, in some cases, I found that
      that theory did not provide results about restriction in the form that was
      most useful to me. I used the following additional results in various places.
\<close>

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
  lemma compose_eq' [simp]:
  shows "compose A G F = restrict (G o F) A"
    unfolding compose_def restrict_def by auto

  section "Set Categories"

  text\<open>
    We first define the locale \<open>set_category_data\<close>, which sets out the basic
    data and definitions for the \<open>set_category\<close> locale, without imposing any conditions
    other than that @{term S} is a category and that @{term img} is a function defined
    on the arrow type of @{term S}.  The function @{term img} should be thought of
    as a mapping that takes a point @{term "x \<in> hom unity a"} to a corresponding
    terminal object @{term "img x"}.  Eventually, assumptions will be introduced so
    that this is in fact the case.  The set of terminal objects of the category will
    serve as abstract ``elements'' of sets; we will refer to the set of \emph{all}
    terminal objects as the \emph{universe}.
\<close>

  locale set_category_data = category S
  for S :: "'s comp"      (infixr "\<cdot>" 55)
  and img :: "'s \<Rightarrow> 's"
  begin

    notation in_hom       ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    text\<open>
      Call the set of all terminal objects of S the ``universe''.
\<close>
    abbreviation Univ :: "'s set"
    where "Univ \<equiv> Collect terminal"
  
    text\<open>
      Choose an arbitrary element of the universe and call it @{term unity}.
\<close>
    definition unity :: 's
    where "unity = (SOME t. terminal t)"
    
    text\<open>
      Each object @{term a} determines a subset @{term "set a"} of the universe,
      consisting of all those terminal objects @{term t} such that @{term "t = img x"}
      for some @{term "x \<in> hom unity a"}.
\<close>
    definition set :: "'s \<Rightarrow> 's set"
    where "set a = img ` hom unity a"

  end

  text\<open>
    Next, we define a locale \<open>set_category_given_img\<close> that augments the
    \<open>set_category_data\<close> locale with assumptions that serve to define
    the notion of a set category with a chosen correspondence between points
    and terminal objects.  The assumptions require that the universe be nonempty
    (so that the definition of @{term unity} makes sense), that the map
    @{term img} is a locally injective map taking points to terminal objects,
    that each terminal object @{term t} belongs to @{term "set t"},
    that two objects of @{term S} are equal if they determine the same set,
    that two parallel arrows of @{term S} are equal if they determine the same
    function, and that for any objects @{term a} and @{term b} and function
    @{term "F \<in> hom unity a \<rightarrow> hom unity b"} there is an arrow @{term "f \<in> hom a b"}
    whose action under the composition of @{term S} coincides with the function @{term F}.

    The parameter @{term setp} is a predicate that determines which subsets of the
    universe are to be regarded as defining objects of the category.  This parameter
    has been introduced because most of the characteristic properties of a category
    of sets and functions do not depend on there being an object corresponding to
    \emph{every} subset of the universe, and we intend to consider in particular the
    cases in which only finite subsets or only ``small'' subsets of the universe
    determine objects.  Accordingly, we assume that there is an object corresponding
    to each subset of the universe that satisfies @{term setp}.
    It is also necessary to assume some basic regularity properties of the predicate
    @{term setp}; namely, that it holds for all subsets of the universe corresponding
    to objects of @{term S}, and that it respects subset and union.
\<close>
    
  locale set_category_given_img = set_category_data S img
  for S :: "'s comp"      (infixr "\<cdot>" 55)
  and img :: "'s \<Rightarrow> 's"
  and setp :: "'s set \<Rightarrow> bool" +
  assumes setp_imp_subset_Univ: "setp A \<Longrightarrow> A \<subseteq> Univ"
  and setp_set_ide: "ide a \<Longrightarrow> setp (set a)"
  and setp_respects_subset: "A' \<subseteq> A \<Longrightarrow> setp A \<Longrightarrow> setp A'"
  and setp_respects_union: "\<lbrakk> setp A; setp B \<rbrakk> \<Longrightarrow> setp (A \<union> B)"
  and nonempty_Univ: "Univ \<noteq> {}"
  and inj_img: "ide a \<Longrightarrow> inj_on img (hom unity a)"
  and stable_img: "terminal t \<Longrightarrow> t \<in> img ` hom unity t"
  and extensional_set: "\<lbrakk> ide a; ide b; set a = set b \<rbrakk> \<Longrightarrow> a = b"
  and extensional_arr: "\<lbrakk> par f f'; \<And>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<Longrightarrow> f \<cdot> x = f' \<cdot> x \<rbrakk> \<Longrightarrow> f = f'"
  and set_complete: "setp A \<Longrightarrow> \<exists>a. ide a \<and> set a = A"
  and fun_complete_ax: "\<lbrakk> ide a; ide b; F \<in> hom unity a \<rightarrow> hom unity b \<rbrakk>
                            \<Longrightarrow> \<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
  begin

    lemma setp_singleton:
    assumes "terminal a"
    shows "setp {a}"
      using assms
      by (metis setp_set_ide Set.set_insert Un_upper1 insert_is_Un set_def
          setp_respects_subset stable_img terminal_def)

    lemma setp_empty:
    shows "setp {}"
      using setp_singleton setp_respects_subset nonempty_Univ by blast

    lemma finite_imp_setp:
    assumes "A \<subseteq> Univ" and "finite A"
    shows "setp A"
      using setp_empty setp_singleton setp_respects_union
      by (metis assms(1-2) finite_subset_induct insert_is_Un mem_Collect_eq)

    text\<open>
      Each arrow @{term "f \<in> hom a b"} determines a function @{term "Fun f \<in> Univ \<rightarrow> Univ"},
      by passing from @{term Univ} to @{term "hom a unity"}, composing with @{term f},
      then passing back to @{term Univ}.
\<close>

    definition Fun :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    where "Fun f = restrict (img o S f o inv_into (hom unity (dom f)) img) (set (dom f))"

    lemma comp_arr_point\<^sub>S\<^sub>C:
    assumes "arr f" and "\<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright>"
    shows "f \<cdot> x = inv_into (hom unity (cod f)) img (Fun f (img x))"
    proof -
      have "\<guillemotleft>f \<cdot> x : unity \<rightarrow> cod f\<guillemotright>"
        using assms by blast
      thus ?thesis
        using assms Fun_def inj_img set_def by simp
    qed
      
    text\<open>
      Parallel arrows that determine the same function are equal.
\<close>

    lemma arr_eqI\<^sub>S\<^sub>C:
    assumes "par f f'" and "Fun f = Fun f'"
    shows "f = f'"
      using assms comp_arr_point\<^sub>S\<^sub>C extensional_arr by metis

    lemma terminal_unity\<^sub>S\<^sub>C:
    shows "terminal unity"
      using unity_def nonempty_Univ by (simp add: someI_ex)

    lemma ide_unity [simp]:
    shows "ide unity"
      using terminal_unity\<^sub>S\<^sub>C terminal_def by blast

    lemma setp_set' [simp]:
    assumes "ide a"
    shows "setp (set a)"
      using assms setp_set_ide by auto
  
    lemma inj_on_set:
    shows "inj_on set (Collect ide)"
      using extensional_set by (intro inj_onI, auto)
      
    text\<open>
      The inverse of the map @{term set} is a map @{term mkIde} that takes each subset
      of the universe to an identity of @{term[source=true] S}.
\<close>
    definition mkIde :: "'s set \<Rightarrow> 's"
    where "mkIde A = (if setp A then inv_into (Collect ide) set A else null)"

    lemma mkIde_set [simp]:
    assumes "ide a"
    shows "mkIde (set a) = a"
      by (simp add: assms inj_on_set mkIde_def)

    lemma set_mkIde [simp]:
    assumes "setp A"
    shows "set (mkIde A) = A"
      using assms mkIde_def set_complete someI_ex [of "\<lambda>a. a \<in> Collect ide \<and> set a = A"]
            mkIde_set
      by metis
      
    lemma ide_mkIde [simp]:
    assumes "setp A"
    shows "ide (mkIde A)"
      using assms mkIde_def mkIde_set set_complete by metis

    lemma arr_mkIde [iff]:
    shows "arr (mkIde A) \<longleftrightarrow> setp A"
      using not_arr_null mkIde_def ide_mkIde by auto
    
    lemma dom_mkIde [simp]:
    assumes "setp A"
    shows "dom (mkIde A) = mkIde A"
      using assms ide_mkIde by simp
    
    lemma cod_mkIde [simp]:
    assumes "setp A"
    shows "cod (mkIde A) = mkIde A"
      using assms ide_mkIde by simp
      
    text\<open>
      Each arrow @{term f} determines an extensional function from
      @{term "set (dom f)"} to @{term "set (cod f)"}.
\<close>

    lemma Fun_mapsto:
    assumes "arr f"
    shows "Fun f \<in> extensional (set (dom f)) \<inter> (set (dom f) \<rightarrow> set (cod f))"
    proof
      show "Fun f \<in> extensional (set (dom f))" using Fun_def by fastforce
      show "Fun f \<in> set (dom f) \<rightarrow> set (cod f)"
      proof
        fix t
        assume t: "t \<in> set (dom f)"
        have "Fun f t = img (f \<cdot> inv_into (hom unity (dom f)) img t)"
          using assms t Fun_def comp_def by simp
        moreover have "... \<in> set (cod f)"
          using assms t set_def inv_into_into [of t img "hom unity (dom f)"] by blast
        ultimately show "Fun f t \<in> set (cod f)" by auto
      qed
    qed
    
    text\<open>
      Identities of @{term[source=true] S} correspond to restrictions of the identity function.
\<close>

    lemma Fun_ide:
    assumes "ide a"
    shows "Fun a = restrict (\<lambda>x. x) (set a)"
      using assms Fun_def inj_img set_def comp_cod_arr by fastforce
    
    lemma Fun_mkIde [simp]:
    assumes "setp A"
    shows "Fun (mkIde A) = restrict (\<lambda>x. x) A"
      using assms ide_mkIde set_mkIde Fun_ide by simp
    
    text\<open>
      Composition in @{term S} corresponds to extensional function composition.
\<close>

    lemma Fun_comp [simp]:
    assumes "seq g f"
    shows "Fun (g \<cdot> f) = restrict (Fun g o Fun f) (set (dom f))"
    proof -
      have "restrict (img o S (g \<cdot> f) o (inv_into (hom unity (dom (g \<cdot> f))) img))
                     (set (dom (g \<cdot> f)))
              = restrict (Fun g o Fun f) (set (dom f))"
      proof -
        let ?img' = "\<lambda>a. \<lambda>t. inv_into (hom unity a) img t"
        have 1: "set (dom (g \<cdot> f)) = set (dom f)"
          using assms by auto
        moreover have "\<And>t. t \<in> set (dom (g \<cdot> f)) \<Longrightarrow>
                           (img o S (g \<cdot> f) o ?img' (dom (g \<cdot> f))) t = (Fun g o Fun f) t"
        proof -
          fix t
          assume "t \<in> set (dom (g \<cdot> f))"
          hence t: "t \<in> set (dom f)" by (simp add: 1)
          have "(img o S (g \<cdot> f) o ?img' (dom (g \<cdot> f))) t = img (g \<cdot> f \<cdot> ?img' (dom f) t)"
            using assms dom_comp comp_assoc by simp
          also have "... = img (g \<cdot> ?img' (dom g) (Fun f t))"
          proof -
            have "\<And>a x. x \<in> hom unity a \<Longrightarrow> ?img' a (img x) = x"
              using assms inj_img ide_cod inv_into_f_eq
              by (metis arrI in_homE mem_Collect_eq)
            thus ?thesis
              using assms t Fun_def set_def comp_arr_point\<^sub>S\<^sub>C by auto
          qed
          also have "... = Fun g (Fun f t)"
          proof -
            have "Fun f t \<in> img ` hom unity (cod f)"
              using assms t Fun_mapsto set_def by fast
            thus ?thesis
              using assms by (auto simp add: set_def Fun_def)
          qed
          finally show "(img o S (g \<cdot> f) o ?img' (dom (g \<cdot> f))) t = (Fun g o Fun f) t"
            by auto
        qed
        ultimately show ?thesis by auto
      qed
      thus ?thesis using Fun_def by auto
    qed

    text\<open>
      The constructor @{term mkArr} is used to obtain an arrow given subsets
      @{term A} and @{term B} of the universe and a function @{term "F \<in> A \<rightarrow> B"}.
\<close>
    
    definition mkArr :: "'s set \<Rightarrow> 's set \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> 's"
    where "mkArr A B F = (if setp A \<and> setp B \<and> F \<in> A \<rightarrow> B
                          then (THE f. f \<in> hom (mkIde A) (mkIde B) \<and> Fun f = restrict F A)
                          else null)"

    text\<open>
      Each function @{term "F \<in> set a \<rightarrow> set b"} determines a unique arrow @{term "f \<in> hom a b"},
      such that @{term "Fun f"} is the restriction of @{term F} to @{term "set a"}.
\<close>

    lemma fun_complete:
    assumes "ide a" and "ide b" and "F \<in> set a \<rightarrow> set b"
    shows "\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> Fun f = restrict F (set a)"
    proof -
      let ?P = "\<lambda>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> Fun f = restrict F (set a)"
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
              using assms setp_set_ide inj_img set_def by auto
          qed
          hence "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> f \<cdot> x = ?F' x)"
            using assms fun_complete_ax [of a b] by force
          from this obtain f where f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> f \<cdot> x = ?F' x)"
            by blast
          let ?img' = "\<lambda>a. \<lambda>t. inv_into (hom unity a) img t"
          have "Fun f = restrict F (set a)"
          proof (unfold Fun_def, intro restr_eqI)
            show "set (dom f) = set a" using f by auto
            show "\<And>t. t \<in> set (dom f) \<Longrightarrow> (img \<circ> S f \<circ> ?img' (dom f)) t = F t"
            proof -
              fix t
              assume t: "t \<in> set (dom f)"
              have "(img \<circ> S f \<circ> ?img' (dom f)) t = img (f \<cdot> ?img' (dom f) t)"
                by simp
              also have "... = img (?F' (?img' (dom f) t))"
                by (metis f in_homE inv_into_into set_def mem_Collect_eq t)
              also have "... = img (?img' (cod f) (F t))"
                using f t set_def inj_img by auto
              also have "... = F t"
              proof -
                have "F t \<in> set (cod f)"
                  using assms f t by auto
                thus ?thesis
                  using f t set_def inj_img by auto
              qed
              finally show "(img \<circ> S f \<circ> ?img' (dom f)) t = F t" by auto
            qed
          qed
          thus ?thesis using f by blast
        qed
        thus F: "?P (SOME f. ?P f)" using someI_ex [of ?P] by fast
        show "\<And>f'. ?P f' \<Longrightarrow> f' = (SOME f. ?P f)"
          using F arr_eqI\<^sub>S\<^sub>C
          by (metis (no_types, lifting) in_homE)
      qed
    qed
                          
    lemma mkArr_in_hom:
    assumes "setp A" and "setp B" and "F \<in> A \<rightarrow> B"
    shows "\<guillemotleft>mkArr A B F : mkIde A \<rightarrow> mkIde B\<guillemotright>"
      using assms mkArr_def fun_complete [of "mkIde A" "mkIde B" F] ide_mkIde set_mkIde
            theI' [of "\<lambda>f. f \<in> hom (mkIde A) (mkIde B) \<and> Fun f = restrict F A"]
            setp_imp_subset_Univ
      by simp

    text\<open>
      The ``only if'' direction of the next lemma can be achieved only if there exists a
      non-arrow element of type @{typ 's}, which can be used as the value of @{term "mkArr A B F"}
      in cases where @{term "F \<notin> A \<rightarrow> B"}.  Nevertheless, it is essential to have this,
      because without the ``only if'' direction, we can't derive any useful
      consequences from an assumption of the form @{term "arr (mkArr A B F)"};
      instead we have to obtain @{term "F \<in> A \<rightarrow> B"} some other way.
      This is is usually highly inconvenient and it makes the theory very weak and almost
      unusable in practice.  The observation that having a non-arrow value of type @{typ 's}
      solves this problem is ultimately what led me to incorporate @{term null} first into the
      definition of the \<open>set_category\<close> locale and then, ultimately, into the definition
      of the \<open>category\<close> locale.  I believe this idea is critical to the usability of the
      entire development.
\<close>

    lemma arr_mkArr [iff]:
    shows "arr (mkArr A B F) \<longleftrightarrow> setp A \<and> setp B \<and> F \<in> A \<rightarrow> B"
    proof
      show "arr (mkArr A B F) \<Longrightarrow> setp A \<and> setp B \<and> F \<in> A \<rightarrow> B"
        using mkArr_def not_arr_null ex_un_null someI_ex [of "\<lambda>f. \<not>arr f"] setp_imp_subset_Univ
        by metis
      show "setp A \<and> setp B \<and> F \<in> A \<rightarrow> B \<Longrightarrow> arr (mkArr A B F)"
        using mkArr_in_hom by auto
    qed
    
    lemma arr_mkArrI [intro]:
    assumes "setp A" and "setp B" and "F \<in> A \<rightarrow> B"
    shows "arr (mkArr A B F)"
      using assms arr_mkArr by blast

    lemma Fun_mkArr':
    assumes "arr (mkArr A B F)"
    shows "\<guillemotleft>mkArr A B F : mkIde A \<rightarrow> mkIde B\<guillemotright>"
    and "Fun (mkArr A B F) = restrict F A"
    proof -
      have 1: "setp A \<and> setp B \<and> F \<in> A \<rightarrow> B" using assms by fast
      have 2: "mkArr A B F \<in> hom (mkIde A) (mkIde B) \<and>
                     Fun (mkArr A B F) = restrict F (set (mkIde A))"
      proof -
        have "\<exists>!f. f \<in> hom (mkIde A) (mkIde B) \<and> Fun f = restrict F (set (mkIde A))"
          using 1 fun_complete [of "mkIde A" "mkIde B" F] ide_mkIde set_mkIde by simp
        thus ?thesis using 1 mkArr_def theI' set_mkIde by simp
      qed
      show "\<guillemotleft>mkArr A B F : mkIde A \<rightarrow> mkIde B\<guillemotright>" using 1 2 by auto
      show "Fun (mkArr A B F) = restrict F A" using 1 2 set_mkIde by auto
    qed

    lemma mkArr_Fun:
    assumes "arr f"
    shows "mkArr (set (dom f)) (set (cod f)) (Fun f) = f"
    proof -
      have 1: "setp (set (dom f)) \<and> setp (set (cod f)) \<and> ide (dom f) \<and> ide (cod f) \<and>
               Fun f \<in> extensional (set (dom f)) \<inter> (set (dom f) \<rightarrow> set (cod f))"
        using Fun_mapsto assms ide_cod ide_dom setp_set' by presburger
      hence "\<exists>!f'. f' \<in> hom (dom f) (cod f) \<and> Fun f' = restrict (Fun f) (set (dom f))"
        using fun_complete by force
      moreover have "f \<in> hom (dom f) (cod f) \<and> Fun f = restrict (Fun f) (set (dom f))"
        using assms 1 extensional_restrict by force
      ultimately have "f = (THE f'. f' \<in> hom (dom f) (cod f) \<and>
                                    Fun f' = restrict (Fun f) (set (dom f)))"
        using theI' [of "\<lambda>f'. f' \<in> hom (dom f) (cod f) \<and> Fun f' = restrict (Fun f) (set (dom f))"]
        by blast
      also have "... = mkArr (set (dom f)) (set (cod f)) (Fun f)"
        using assms 1 mkArr_def mkIde_set by simp
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

    text\<open>
      The following provides the basic technique for showing that arrows
      constructed using @{term mkArr} are equal.
\<close>

    lemma mkArr_eqI [intro]:
    assumes "arr (mkArr A B F)"
    and "A = A'" and "B = B'" and "\<And>x. x \<in> A \<Longrightarrow> F x = F' x"
    shows "mkArr A B F = mkArr A' B' F'"
      using assms Fun_mkArr
      by (intro arr_eqI\<^sub>S\<^sub>C, auto simp add: Pi_iff)

    text\<open>
      This version avoids trivial proof obligations when the domain and codomain
      sets are identical from the context.
\<close>
    
    lemma mkArr_eqI' [intro]:
    assumes "arr (mkArr A B F)" and "\<And>x. x \<in> A \<Longrightarrow> F x = F' x"
    shows "mkArr A B F = mkArr A B F'"
      using assms mkArr_eqI by simp
    
    lemma mkArr_restrict_eq:
    assumes "arr (mkArr A B F)"
    shows "mkArr A B (restrict F A) = mkArr A B F"
      using assms by (intro mkArr_eqI', auto)
      
    lemma mkArr_restrict_eq':
    assumes "arr (mkArr A B (restrict F A))"
    shows "mkArr A B (restrict F A) = mkArr A B F"
      using assms by (intro mkArr_eqI', auto)
      
    lemma mkIde_as_mkArr [simp]:
    assumes "setp A"
    shows "mkArr A A (\<lambda>x. x) = mkIde A"
      using assms arr_mkIde dom_mkIde cod_mkIde Fun_mkIde
      by (intro arr_eqI\<^sub>S\<^sub>C, auto)

    lemma comp_mkArr:
    assumes "arr (mkArr A B F)" and "arr (mkArr B C G)"
    shows "mkArr B C G \<cdot> mkArr A B F = mkArr A C (G \<circ> F)"
    proof (intro arr_eqI\<^sub>S\<^sub>C)
      have 1: "seq (mkArr B C G) (mkArr A B F)" using assms by force
      have 2: "G o F \<in> A \<rightarrow> C" using assms by auto
      show "par (mkArr B C G \<cdot> mkArr A B F) (mkArr A C (G \<circ> F))"
        using assms 1 2
        by (intro conjI) simp_all
      show "Fun (mkArr B C G \<cdot> mkArr A B F) = Fun (mkArr A C (G \<circ> F))"
        using 1 2 by fastforce
    qed
    
    text\<open>
      The locale assumption @{prop stable_img} forces @{term "t \<in> set t"} in case
      @{term t} is a terminal object.  This is very convenient, as it results in the
      characterization of terminal objects as identities @{term t} for which
      @{term "set t = {t}"}.  However, it is not absolutely necessary to have this.
      The following weaker characterization of terminal objects can be proved without
      the @{prop stable_img} assumption.
\<close>

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
            using t terminal_unity\<^sub>S\<^sub>C terminal_def by auto
          thus ?thesis using set_def by auto
        qed
        ultimately show "ide t \<and> (\<exists>!x. x \<in> set t)" by auto
      qed
      moreover have "ide t \<and> (\<exists>!x. x \<in> set t) \<Longrightarrow> terminal t"
      proof -
        assume t: "ide t \<and> (\<exists>!x. x \<in> set t)"
        from this obtain t' where "set t = {t'}" by blast
        hence t': "set t = {t'} \<and> setp {t'} \<and> t = mkIde {t'}"
          using t setp_set_ide mkIde_set by metis
        show "terminal t"
        proof
          show "ide t" using t by simp
          show "\<And>a. ide a \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> t\<guillemotright>"
          proof -
            fix a
            assume a: "ide a"
            show "\<exists>!f. \<guillemotleft>f : a \<rightarrow> t\<guillemotright>"
            proof
              show 1: "\<guillemotleft>mkArr (set a) {t'} (\<lambda>x. t') : a \<rightarrow> t\<guillemotright>"
                using a t t' mkArr_in_hom
                by (metis Pi_I' mkIde_set setp_set_ide singletonD)
              show "\<And>f. \<guillemotleft>f : a \<rightarrow> t\<guillemotright> \<Longrightarrow> f = mkArr (set a) {t'} (\<lambda>x. t')"
              proof -
                fix f
                assume f: "\<guillemotleft>f : a \<rightarrow> t\<guillemotright>"
                show "f = mkArr (set a) {t'} (\<lambda>x. t')"
                proof (intro arr_eqI\<^sub>S\<^sub>C)
                  show 1: "par f (mkArr (set a) {t'} (\<lambda>x. t'))" using 1 f in_homE by metis
                  show "Fun f = Fun (mkArr (set a) {t'} (\<lambda>x. t'))"
                  proof -
                    have "Fun (mkArr (set a) {t'} (\<lambda>x. t')) = (\<lambda>x\<in>set a. t')"
                      using 1 Fun_mkArr by simp
                    also have "... = Fun f"
                    proof -
                      have "\<And>x. x \<in> set a \<Longrightarrow> Fun f x = t'"
                        using f t' Fun_def mkArr_Fun arr_mkArr
                        by (metis PiE in_homE singletonD)
                      moreover have "\<And>x. x \<notin> set a \<Longrightarrow> Fun f x = undefined"
                        using f Fun_def by auto
                      ultimately show ?thesis by auto
                    qed
                    finally show ?thesis by force
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      ultimately show ?thesis by blast
    qed
    
    text\<open>
      As stated above, in the presence of the @{prop stable_img} assumption we have
      the following stronger characterization of terminal objects.
\<close>

    lemma terminal_char2:
    shows "terminal t \<longleftrightarrow> ide t \<and> set t = {t}"
    proof
      assume t: "terminal t"
      show "ide t \<and> set t = {t}"
      proof
        show "ide t" using t terminal_char1 by auto
        show "set t = {t}"
        proof -
          have "\<exists>!x. x \<in> hom unity t" using t terminal_def terminal_unity\<^sub>S\<^sub>C by force
          moreover have "t \<in> img ` hom unity t" using t stable_img set_def by simp
          ultimately show ?thesis using set_def by auto
        qed
      qed
      next
      assume "ide t \<and> set t = {t}"
      thus "terminal t" using terminal_char1 by force
    qed

  end

  text\<open>
    At last, we define the \<open>set_category\<close> locale by existentially quantifying
    out the choice of a particular @{term img} map.  We need to know that such a map
    exists, but it does not matter which one we choose.
\<close>

  locale set_category = category S
  for S :: "'s comp"      (infixr "\<cdot>" 55)
  and setp :: "'s set \<Rightarrow> bool" +
  assumes ex_img: "\<exists>img. set_category_given_img S img setp"
  begin

    notation in_hom ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
  
    definition some_img
    where "some_img = (SOME img. set_category_given_img S img setp)"
   
    sublocale set_category_given_img S some_img setp
    proof -
      have "\<exists>img. set_category_given_img S img setp" using ex_img by auto
      thus "set_category_given_img S some_img setp"
        using someI_ex [of "\<lambda>img. set_category_given_img S img setp"] some_img_def
        by metis
    qed

  end
  
  text\<open>We call a set category \emph{replete} if there is an object corresponding to
    every subset of the universe.
\<close>

  locale replete_set_category =
    category S +
    set_category S \<open>\<lambda>A. A \<subseteq> Collect terminal\<close>
  for S :: "'s comp"      (infixr "\<cdot>" 55)
  begin

    abbreviation setp
    where "setp \<equiv> \<lambda>A. A \<subseteq> Univ"

    lemma is_set_category:
    shows "set_category S (\<lambda>A. A \<subseteq> Collect terminal)"
      ..

  end

  context set_category
  begin

    text\<open>
      The arbitrary choice of @{term img} induces a system of arrows corresponding
      to inclusions of subsets.
\<close>

    definition incl :: "'s \<Rightarrow> bool"
    where "incl f = (arr f \<and> set (dom f) \<subseteq> set (cod f) \<and>
                     f = mkArr (set (dom f)) (set (cod f)) (\<lambda>x. x))"

    lemma Fun_incl:
    assumes "incl f"
    shows "Fun f = (\<lambda>x \<in> set (dom f). x)"
      using assms incl_def by (metis Fun_mkArr)

    lemma ex_incl_iff_subset:
    assumes "ide a" and "ide b"
    shows "(\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> incl f) \<longleftrightarrow> set a \<subseteq> set b"
    proof
      show "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> incl f \<Longrightarrow> set a \<subseteq> set b"
        using incl_def by auto
      show "set a \<subseteq> set b \<Longrightarrow> \<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> incl f"
      proof
        assume 1: "set a \<subseteq> set b"
        show "\<guillemotleft>mkArr (set a) (set b) (\<lambda>x. x) : a \<rightarrow> b\<guillemotright> \<and> incl (mkArr (set a) (set b) (\<lambda>x. x))"
        proof
          show "\<guillemotleft>mkArr (set a) (set b) (\<lambda>x. x) : a \<rightarrow> b\<guillemotright>"
            by (metis 1 assms image_ident image_subset_iff_funcset mkIde_set
                mkArr_in_hom setp_set_ide)
          thus "incl (mkArr (set a) (set b) (\<lambda>x. x))"
            using 1 incl_def by force
        qed
      qed
    qed

  end

  section "Categoricity"

  text\<open>
    In this section we show that the \<open>set_category\<close> locale completely characterizes
    the structure of its interpretations as categories, in the sense that for any two
    interpretations @{term S} and @{term S'}, a @{term setp}-respecting bijection
    between the universe of @{term S} and the universe of @{term S'} extends
    to an isomorphism of @{term S} and @{term S'}.
\<close>
  
  locale two_set_categories_bij_betw_Univ =
    S: set_category S setp +
    S': set_category S' setp'
  for S :: "'s comp"      (infixr "\<cdot>" 55)
  and setp :: "'s set \<Rightarrow> bool"
  and S' :: "'t comp"     (infixr "\<cdot>\<acute>" 55)
  and setp' :: "'t set \<Rightarrow> bool"
  and \<phi> :: "'s \<Rightarrow> 't" +
  assumes bij_\<phi>: "bij_betw \<phi> S.Univ S'.Univ"
  and \<phi>_respects_setp: "A \<subseteq> S.Univ \<Longrightarrow> setp' (\<phi> ` A) \<longleftrightarrow> setp A"
  begin

    notation S.in_hom     ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation S'.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>'' _\<guillemotright>")

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
  
    text\<open>
      We define the object map @{term \<Phi>o} of a functor from @{term[source=true] S}
      to @{term[source=true] S'}.
\<close>

    definition \<Phi>o
    where "\<Phi>o = (\<lambda>a \<in> Collect S.ide. S'.mkIde (\<phi> ` S.set a))"

    lemma set_\<Phi>o:
    assumes "S.ide a"
    shows "S'.set (\<Phi>o a) = \<phi> ` S.set a"
      by (simp add: S.setp_imp_subset_Univ \<Phi>o_def \<phi>_respects_setp assms)

    lemma \<Phi>o_preserves_ide:
    assumes "S.ide a"
    shows "S'.ide (\<Phi>o a)"
      using assms S'.ide_mkIde bij_\<phi> bij_betw_def image_mono restrict_apply' S.setp_set'
            \<phi>_respects_setp S.setp_imp_subset_Univ
      unfolding \<Phi>o_def
      by simp
      
    text\<open>
      The map @{term \<Phi>a} assigns to each arrow @{term f} of @{term[source=true] S} the function on
      the universe of @{term[source=true] S'} that is the same as the function induced by @{term f}
      on the universe of @{term[source=true] S}, up to the bijection @{term \<phi>} between the two
      universes.
\<close>

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
          using assms x \<psi>_img_\<phi>_img [of "S.set (S.dom f)"] S.setp_imp_subset_Univ by auto
        hence "S.Fun f (\<psi> x) \<in> S.set (S.cod f)" using assms S.Fun_mapsto by auto
        hence "\<phi> (S.Fun f (\<psi> x)) \<in> \<phi> ` S.set (S.cod f)" by simp
        thus "\<Phi>a f x \<in> \<phi> ` S.set (S.cod f)" using x \<Phi>a_def by auto
      qed
      thus ?thesis using assms set_\<Phi>o \<Phi>o_preserves_ide by auto
    qed
    
    text\<open>
      The map @{term \<Phi>a} takes composition of arrows to extensional
      composition of functions.
\<close>

    lemma \<Phi>a_comp:
    assumes gf: "S.seq g f"
    shows "\<Phi>a (g \<cdot> f) = restrict (\<Phi>a g o \<Phi>a f) (S'.set (\<Phi>o (S.dom f)))"
    proof -
      have "\<Phi>a (g \<cdot> f) = (\<lambda>x' \<in> \<phi> ` S.set (S.dom f). \<phi> (S.Fun (S g f) (\<psi> x')))"
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
            using gf \<psi>_img_\<phi>_img S.setp_imp_subset_Univ S.ide_dom S.setp_set_ide
            by blast
          hence "\<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x'))
                   = \<phi> (S.Fun g (S.Fun f (\<psi> x')))"
            using restrict_apply by auto
          also have "... = \<phi> (S.Fun g (\<psi> (\<phi> (S.Fun f (\<psi> x')))))"
          proof -
            have "S.Fun f (\<psi> x') \<in> S.set (S.cod f)"
              using gf 1 S.Fun_mapsto by fast
            hence "\<psi> (\<phi> (S.Fun f (\<psi> x'))) = S.Fun f (\<psi> x')"
              using assms bij_\<phi> S.setp_imp_subset_Univ bij_betw_def inv_into_f_f subsetCE
                    S.ide_cod S.setp_set_ide
              by (metis S.seqE)
            thus ?thesis by auto
          qed
          also have "... = \<Phi>a g (\<Phi>a f x')"
          proof -
            have "\<Phi>a f x' \<in> \<phi> ` S.set (S.cod f)"
              using gf S.ide_dom S.ide_cod X' \<Phi>a_mapsto [of f] set_\<Phi>o [of "S.dom f"]
                    set_\<Phi>o [of "S.cod f"]
              by blast
            thus ?thesis using gf X' \<Phi>a_def by auto
          qed
          finally show "\<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x')) =
                        \<Phi>a g (\<Phi>a f x')"
            by auto
        qed
        thus ?thesis using assms set_\<Phi>o by fastforce
      qed
      finally show ?thesis by auto
    qed
    
    text\<open>
      Finally, we use @{term \<Phi>o} and @{term \<Phi>a} to define a functor @{term \<Phi>}.
\<close>

    definition \<Phi>
    where "\<Phi> f = (if S.arr f then
                     S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod f))) (\<Phi>a f)
                   else S'.null)"
    
    lemma \<Phi>_in_hom:
    assumes "S.arr f"
    shows "\<Phi> f \<in> S'.hom (\<Phi>o (S.dom f)) (\<Phi>o (S.cod f))"
    proof -
      have "\<guillemotleft>\<Phi> f : S'.dom (\<Phi> f) \<rightarrow>' S'.cod (\<Phi> f)\<guillemotright>"
        using assms \<Phi>_def \<Phi>a_mapsto \<Phi>o_preserves_ide
        by (intro S'.in_homI) auto
      thus ?thesis
        using assms \<Phi>_def \<Phi>a_mapsto \<Phi>o_preserves_ide by auto
    qed

    lemma \<Phi>_ide [simp]:
    assumes "S.ide a"
    shows "\<Phi> a = \<Phi>o a"
    proof -
      have "\<Phi> a = S'.mkArr (S'.set (\<Phi>o a)) (S'.set (\<Phi>o a)) (\<lambda>x'. x')"
      proof -
        have "\<guillemotleft>\<Phi> a : \<Phi>o a \<rightarrow>' \<Phi>o a\<guillemotright>"
          using assms \<Phi>_in_hom S.ide_in_hom by fastforce
        moreover have "\<Phi>a a = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a))"
        proof -
          have "\<Phi>a a = (\<lambda>x' \<in> \<phi> ` S.set a. \<phi> (S.Fun a (\<psi> x')))"
            using assms \<Phi>a_def restrict_apply by auto
          also have "... = (\<lambda>x' \<in> S'.set (\<Phi>o a). \<phi> (\<psi> x'))"
          proof -
            have "S.Fun a = (\<lambda>x \<in> S.set a. x)"
              using assms S.Fun_ide by auto
            moreover have "\<And>x'. x' \<in> \<phi> ` S.set a \<Longrightarrow> \<psi> x' \<in> S.set a"
              using assms bij_\<phi> S.setp_imp_subset_Univ image_iff S.setp_set_ide
              by (metis \<psi>_img_\<phi>_img)
            ultimately show ?thesis
              using assms set_\<Phi>o by auto
          qed
          also have "... = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a))"
            using assms S'.setp_imp_subset_Univ S'.setp_set_ide \<Phi>o_preserves_ide \<phi>_\<psi>
            by (meson restr_eqI subsetCE)
          ultimately show ?thesis by auto
        qed
        ultimately show ?thesis
          using assms \<Phi>_def \<Phi>o_preserves_ide S'.mkArr_restrict_eq'
          by (metis S'.arrI S.ide_char)
      qed
      thus ?thesis
        using assms S'.mkIde_as_mkArr \<Phi>o_preserves_ide \<Phi>_in_hom S'.mkIde_set
        by simp
    qed
    
    lemma set_dom_\<Phi>:
    assumes "S.arr f"
    shows "S'.set (S'.dom (\<Phi> f)) = \<phi> ` (S.set (S.dom f))"
      using assms S.ide_dom \<Phi>_in_hom \<Phi>_ide set_\<Phi>o by fastforce
    
    lemma \<Phi>_comp:
    assumes "S.seq g f"
    shows "\<Phi> (g \<cdot> f) = \<Phi> g \<cdot>\<acute> \<Phi> f"
    proof -
      have "\<Phi> (g \<cdot> f) = S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a (S g f))"
        using \<Phi>_def assms by auto
      also have "... = S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g)))
                                (restrict (\<Phi>a g o \<Phi>a f) (S'.set (\<Phi>o (S.dom f))))"
        using assms \<Phi>a_comp set_\<Phi>o by force
      also have "... = S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a g o \<Phi>a f)"
        by (metis S'.mkArr_restrict_eq' \<Phi>_in_hom assms calculation S'.in_homE mem_Collect_eq)
      also have "... = S' (S'.mkArr (S'.set (\<Phi>o (S.dom g))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a g))
                          (S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod f))) (\<Phi>a f))"
      proof -
        have "S'.arr (S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod f))) (\<Phi>a f))"
          using assms \<Phi>a_mapsto set_\<Phi>o S.ide_dom S.ide_cod \<Phi>o_preserves_ide
                S'.arr_mkArr S'.setp_imp_subset_Univ S'.setp_set_ide S.seqE
          by metis
        moreover have "S'.arr (S'.mkArr (S'.set (\<Phi>o (S.dom g))) (S'.set (\<Phi>o (S.cod g)))
                              (\<Phi>a g))"
          using assms \<Phi>a_mapsto set_\<Phi>o S.ide_dom S.ide_cod \<Phi>o_preserves_ide S'.arr_mkArr
                S'.setp_imp_subset_Univ S'.setp_set_ide S.seqE
          by metis
        ultimately show ?thesis using assms S'.comp_mkArr by auto
      qed
      also have "... = \<Phi> g \<cdot>\<acute> \<Phi> f" using assms \<Phi>_def by force
      finally show ?thesis by fast
    qed
      
    interpretation \<Phi>: "functor" S S' \<Phi>
      apply unfold_locales
      using \<Phi>_def
          apply simp
      using \<Phi>_in_hom \<Phi>_comp
      by auto

    lemma \<Phi>_is_functor:
    shows "functor S S' \<Phi>" ..
      
    lemma Fun_\<Phi>:
    assumes "S.arr f" and "x \<in> S.set (S.dom f)"
    shows "S'.Fun (\<Phi> f) (\<phi> x) = \<Phi>a f (\<phi> x)"
      using assms \<Phi>_def \<Phi>.preserves_arr set_\<Phi>o by auto
      
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
        have 1: "S.terminal x" using assms x S.setp_imp_subset_Univ S.setp_set_ide by blast
        hence 2: "S'.terminal (\<phi> x)"
          by (metis CollectD CollectI bij_\<phi> bij_betw_def image_iff)
        have "\<Phi> x = \<Phi>o x"
          using assms x 1 \<Phi>_ide S.terminal_def by auto
        also have "... = \<phi> x"
        proof -
          have "\<Phi>o x = S'.mkIde (\<phi> ` S.set x)"
            using assms 1 x \<Phi>o_def S.terminal_def by auto
          moreover have "S'.mkIde (\<phi> ` S.set x) = \<phi> x"
            using assms x 1 2 S.terminal_char2 S'.terminal_char2 S'.mkIde_set bij_\<phi>
            by (metis (no_types, lifting) empty_is_image image_insert)
          ultimately show ?thesis by auto
        qed
        finally show "\<Phi> x = \<phi> x" by auto
      qed
      show "S'.set (\<Phi> a) \<subseteq> \<Phi> ` S.set a" using 0 1 by force
      show "\<Phi> ` S.set a \<subseteq> S'.set (\<Phi> a)" using 0 1 by force
    qed

    lemma \<Phi>_preserves_incl:
    assumes "S.incl m"
    shows "S'.incl (\<Phi> m)"
    proof -
      have 1: "S.arr m \<and> S.set (S.dom m) \<subseteq> S.set (S.cod m) \<and>
               m = S.mkArr (S.set (S.dom m)) (S.set (S.cod m)) (\<lambda>x. x)"
        using assms S.incl_def by blast
      have "S'.arr (\<Phi> m)" using 1 by auto
      moreover have 2: "S'.set (S'.dom (\<Phi> m)) \<subseteq> S'.set (S'.cod (\<Phi> m))"
        using 1 \<Phi>.preserves_dom \<Phi>.preserves_cod \<Phi>_acts_elementwise by auto
      moreover have "\<Phi> m =
                     S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<lambda>x'. x')"
      proof -
        have "\<Phi> m = S'.mkArr (S'.set (\<Phi>o (S.dom m))) (S'.set (\<Phi>o (S.cod m))) (\<Phi>a m)"
          using 1 \<Phi>_def by simp
        also have "... = S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<Phi>a m)"
          using 1 \<Phi>_ide by auto
        finally have 3: "\<Phi> m =
                         S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<Phi>a m)"
          by auto
        also have "... = S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<lambda>x'. x')"
        proof -
          have 4: "S.Fun m = restrict (\<lambda>x. x) (S.set (S.dom m))"
            using assms S.incl_def by (metis (full_types) S.Fun_mkArr)
          hence "\<Phi>a m = restrict (\<lambda>x'. x') (\<phi> ` (S.set (S.dom m)))"
          proof -
            have 5: "\<And>x'. x' \<in> \<phi> ` S.set (S.dom m) \<Longrightarrow> \<phi> (\<psi> x') = x'"
              by (meson 1 S.ide_dom S.setp_imp_subset_Univ S.setp_set' f_inv_into_f
                        image_mono subset_eq)
            have "\<Phi>a m = restrict (\<lambda>x'. \<phi> (S.Fun m (\<psi> x'))) (\<phi> ` S.set (S.dom m))"
              using \<Phi>a_def by simp
            also have "... = restrict (\<lambda>x'. x') (\<phi> ` S.set (S.dom m))"
            proof -
              have "\<And>x. x \<in> \<phi> ` (S.set (S.dom m)) \<Longrightarrow> \<phi> (S.Fun m (\<psi> x)) = x"
              proof -
                fix x
                assume x: "x \<in> \<phi> ` (S.set (S.dom m))"
                hence "\<psi> x \<in> S.set (S.dom m)"
                  using 1 S.ide_dom S.setp_imp_subset_Univ S.setp_set_ide \<psi>_img_\<phi>_img image_eqI
                  by metis
                thus "\<phi> (S.Fun m (\<psi> x)) = x" using 1 4 5 x by simp
              qed
              thus ?thesis by auto
            qed
            finally show ?thesis by auto
          qed
          hence "\<Phi>a m = restrict (\<lambda>x'. x') (S'.set (S'.dom (\<Phi> m)))"
            using 1 set_dom_\<Phi> by auto
          thus ?thesis
            using 2 3 \<open>S'.arr (\<Phi> m)\<close> S'.mkArr_restrict_eq S'.ide_cod S'.ide_dom S'.incl_def
            by (metis S'.arr_mkArr image_restrict_eq image_subset_iff_funcset)
        qed
        finally show ?thesis by auto
      qed
      ultimately show ?thesis using S'.incl_def by blast
    qed

    lemma \<psi>_respects_sets:
    assumes "A' \<subseteq> S'.Univ"
    shows "setp (\<psi> ` A') \<longleftrightarrow> setp' A'"
      using assms \<phi>_respects_setp \<phi>_img_\<psi>_img bij_\<phi>
      by (metis \<psi>_img_\<phi>_img bij_betw_def image_mono order_refl)

    text\<open>
      Interchange the role of @{term \<phi>} and @{term \<psi>} to obtain a functor \<open>\<Psi>\<close>
      from @{term[source=true] S'} to @{term[source=true] S}.
\<close>

    interpretation INV: two_set_categories_bij_betw_Univ S' setp' S setp \<psi>
      using \<psi>_respects_sets bij_\<phi> bij_betw_inv_into
      by unfold_locales auto

    abbreviation \<Psi>o
    where "\<Psi>o \<equiv> INV.\<Phi>o"

    abbreviation \<Psi>a
    where "\<Psi>a \<equiv> INV.\<Phi>a"

    abbreviation \<Psi>
    where "\<Psi> \<equiv> INV.\<Phi>"

    interpretation \<Psi>: "functor" S' S \<Psi>
      using INV.\<Phi>_is_functor by auto

    text\<open>
      The functors @{term \<Phi>} and @{term \<Psi>} are inverses.
\<close>

    lemma Fun_\<Psi>:
    assumes "S'.arr f'" and "x' \<in> S'.set (S'.dom f')"
    shows "S.Fun (\<Psi> f') (\<psi> x') = \<Psi>a f' (\<psi> x')"
      using assms INV.Fun_\<Phi> by blast
          
    lemma \<Psi>o_\<Phi>o:
    assumes "S.ide a"
    shows "\<Psi>o (\<Phi>o a) = a"
      using assms \<Phi>o_def INV.\<Phi>o_def \<psi>_img_\<phi>_img \<Phi>o_preserves_ide set_\<Phi>o S.mkIde_set
      by (simp add: S.setp_imp_subset_Univ)
     
    lemma \<Phi>\<Psi>:
    assumes "S.arr f"
    shows "\<Psi> (\<Phi> f) = f"
    proof (intro S.arr_eqI\<^sub>S\<^sub>C)
      show par: "S.par (\<Psi> (\<Phi> f)) f"
        using assms \<Phi>o_preserves_ide \<Psi>o_\<Phi>o by auto
      show "S.Fun (\<Psi> (\<Phi> f)) = S.Fun f"
      proof -
        have "S.arr (\<Psi> (\<Phi> f))" using assms by auto
        moreover have "\<Psi> (\<Phi> f) = S.mkArr (S.set (S.dom f)) (S.set (S.cod f)) (\<Psi>a (\<Phi> f))"
          using assms INV.\<Phi>_def \<Phi>_in_hom \<Psi>o_\<Phi>o by auto
        moreover have "\<Psi>a (\<Phi> f) = (\<lambda>x \<in> S.set (S.dom f). \<psi> (S'.Fun (\<Phi> f) (\<phi> x)))"
        proof -
          have "\<Psi>a (\<Phi> f) = (\<lambda>x \<in> \<psi> ` S'.set (S'.dom (\<Phi> f)). \<psi> (S'.Fun (\<Phi> f) (\<phi> x)))"
          proof -
            have "\<And>x. x \<in> \<psi> ` S'.set (S'.dom (\<Phi> f)) \<Longrightarrow> INV.\<psi> x = \<phi> x"
              using assms S.ide_dom S.setp_imp_subset_Univ \<Psi>.preserves_reflects_arr par bij_\<phi>
                    inv_into_inv_into_eq subsetCE INV.set_dom_\<Phi>
              by (metis (no_types) S.setp_set')
            thus ?thesis
              using INV.\<Phi>a_def by auto
          qed
          moreover have "\<psi> ` S'.set (S'.dom (\<Phi> f)) = S.set (S.dom f)"
            using assms by (metis par \<Psi>.preserves_reflects_arr INV.set_dom_\<Phi>)
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
            have "S.Fun (\<Psi> (\<Phi> f)) x = \<psi> (\<phi> (S.Fun f (\<psi> (\<phi> x))))"
              using assms x 1 Fun_\<Phi> bij_\<phi> \<Phi>a_def by auto
            also have "... = S.Fun f x"
            proof -
              have 2: "\<And>x. x \<in> S.Univ \<Longrightarrow> \<psi> (\<phi> x) = x"
                using bij_\<phi> bij_betw_inv_into_left by fast
              have "S.Fun f (\<psi> (\<phi> x)) = S.Fun f x"
                using assms x 2 S.ide_dom S.setp_imp_subset_Univ
                by (metis S.setp_set' subsetD)
              moreover have "S.Fun f x \<in> S.Univ"
                using x assms S.Fun_mapsto S.setp_imp_subset_Univ S.setp_set' S.ide_cod
                by blast
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
      using assms \<Phi>o_def INV.\<Phi>o_def \<phi>_img_\<psi>_img INV.\<Phi>o_preserves_ide \<psi>_\<phi> INV.set_\<Phi>o
            S'.mkIde_set S'.setp_imp_subset_Univ
      by force

    lemma \<Psi>\<Phi>:
    assumes "S'.arr f'"
    shows "\<Phi> (\<Psi> f') = f'"
    proof (intro S'.arr_eqI\<^sub>S\<^sub>C)
      show par: "S'.par (\<Phi> (\<Psi> f')) f'"
        using assms \<Phi>.preserves_ide \<Psi>.preserves_ide \<Phi>_ide INV.\<Phi>_ide \<Phi>o_\<Psi>o by auto
      show "S'.Fun (\<Phi> (\<Psi> f')) = S'.Fun f'"
      proof -
        have "S'.arr (\<Phi> (\<Psi> f'))" using assms by blast
        moreover have "\<Phi> (\<Psi> f') =
                       S'.mkArr (S'.set (S'.dom f')) (S'.set (S'.cod f')) (\<Phi>a (\<Psi> f'))"
          using assms \<Phi>_def INV.\<Phi>_in_hom \<Phi>o_\<Psi>o by simp
        moreover have "\<Phi>a (\<Psi> f') = (\<lambda>x' \<in> S'.set (S'.dom f'). \<phi> (S.Fun (\<Psi> f') (\<psi> x')))"
          unfolding \<Phi>a_def
          using assms par \<Psi>.preserves_arr set_dom_\<Phi> by metis
        ultimately have 1: "S'.Fun (\<Phi> (\<Psi> f')) =
                            (\<lambda>x' \<in> S'.set (S'.dom f'). \<phi> (S.Fun (\<Psi> f') (\<psi> x')))"
          using S'.Fun_mkArr by simp
        show ?thesis
        proof
          fix x'
          have "x' \<notin> S'.set (S'.dom f') \<Longrightarrow> S'.Fun (\<Phi> (\<Psi> f')) x' = S'.Fun f' x'"
            using 1 assms S'.Fun_mapsto extensional_def by (simp add: S'.Fun_def)
          moreover have "x' \<in> S'.set (S'.dom f') \<Longrightarrow> S'.Fun (\<Phi> (\<Psi> f')) x' = S'.Fun f' x'"
          proof -
            assume x': "x' \<in> S'.set (S'.dom f')"
            have "S'.Fun (\<Phi> (\<Psi> f')) x' = \<phi> (S.Fun (\<Psi> f') (\<psi> x'))"
              using x' 1 by auto
            also have "... = \<phi> (\<Psi>a f' (\<psi> x'))"
              using Fun_\<Psi> x' assms S'.setp_imp_subset_Univ bij_\<phi> by metis
            also have "... = \<phi> (\<psi> (S'.Fun f' (\<phi> (\<psi> x'))))"
            proof -
              have "\<phi> (\<Psi>a f' (\<psi> x')) = \<phi> (\<psi> (S'.Fun f' x'))"
              proof -
                have "x' \<in> S'.Univ"
                  by (meson S'.ide_dom S'.setp_imp_subset_Univ S'.setp_set_ide assms subsetCE x')
                thus ?thesis
                  by (simp add: INV.\<Phi>a_def INV.\<psi>_\<phi> x')
              qed
              also have "... = \<phi> (\<psi> (S'.Fun f' (\<phi> (\<psi> x'))))"
                using assms x' \<phi>_\<psi> S'.setp_imp_subset_Univ S'.setp_set_ide S'.ide_dom
                by (metis subsetCE)
              finally show ?thesis by auto
            qed
            also have "... = S'.Fun f' x'"
            proof -
              have 2: "\<And>x'. x' \<in> S'.Univ \<Longrightarrow> \<phi> (\<psi> x') = x'"
                using bij_\<phi> bij_betw_inv_into_right by fast
              have "S'.Fun f' (\<phi> (\<psi> x')) = S'.Fun f' x'"
                using assms x' 2 S'.setp_imp_subset_Univ S'.setp_set_ide S'.ide_dom
                by (metis subsetCE)
              moreover have "S'.Fun f' x' \<in> S'.Univ"
                using x' assms S'.Fun_mapsto S'.setp_imp_subset_Univ S'.setp_set_ide S'.ide_cod
                by blast
              ultimately show ?thesis using 2 by auto
            qed
            finally show ?thesis by auto
          qed
          ultimately show "S'.Fun (\<Phi> (\<Psi> f')) x' = S'.Fun f' x'" by auto
        qed
      qed
    qed
          
    lemma inverse_functors_\<Phi>_\<Psi>:
    shows "inverse_functors S S' \<Psi> \<Phi>"
    proof -
      interpret \<Phi>\<Psi>: composite_functor S S' S \<Phi> \<Psi> ..
      have inv: "\<Psi> o \<Phi> = S.map"
        using \<Phi>\<Psi> S.map_def \<Phi>\<Psi>.is_extensional by auto
    
      interpret \<Psi>\<Phi>: composite_functor S' S S' \<Psi> \<Phi> ..
      have inv': "\<Phi> o \<Psi> = S'.map"
        using \<Psi>\<Phi> S'.map_def \<Psi>\<Phi>.is_extensional by auto
    
      show ?thesis
        using inv inv' by (unfold_locales, auto)
    qed
      
    lemma are_isomorphic:
    shows "\<exists>\<Phi>. invertible_functor S S' \<Phi> \<and> (\<forall>m. S.incl m \<longrightarrow> S'.incl (\<Phi> m))"
    proof -
      interpret inverse_functors S S' \<Psi> \<Phi>
        using inverse_functors_\<Phi>_\<Psi> by auto
      have 1: "inverse_functors S S' \<Psi> \<Phi>" ..
      interpret invertible_functor S S' \<Phi>
        apply unfold_locales using 1 by auto
      have "invertible_functor S S' \<Phi>" ..
      thus ?thesis using \<Phi>_preserves_incl by auto
    qed
    
  end
  
  text\<open>
    The main result: @{locale set_category} is categorical, in the following (logical) sense:
    If \<open>S\<close> and \<open>S'\<close> are two "set categories", and if the sets of terminal objects of \<open>S\<close> and \<open>S'\<close>
    are in correspondence via a @{term setp}-preserving bijection, then \<open>S\<close> and \<open>S'\<close> are
    isomorphic as categories, via a functor that preserves inclusion maps, hence also the
    inclusion relation between sets.
\<close>

  theorem set_category_is_categorical:
  assumes "set_category S setp" and "set_category S' setp'"
  and "bij_betw \<phi> (set_category_data.Univ S) (set_category_data.Univ S')"
  and "\<And>A. A \<subseteq> set_category_data.Univ S \<Longrightarrow> setp' (\<phi> ` A) \<longleftrightarrow> setp A"
  shows "\<exists>\<Phi>. invertible_functor S S' \<Phi> \<and>
             (\<forall>m. set_category.incl S setp m \<longrightarrow> set_category.incl S' setp' (\<Phi> m))"
  proof -
    interpret S: set_category S setp using assms(1) by auto
    interpret S': set_category S' setp' using assms(2) by auto
    interpret two_set_categories_bij_betw_Univ S setp S' setp' \<phi>
      apply (unfold_locales) using assms(3-4) by auto
    show ?thesis using are_isomorphic by auto
  qed
  
  section "Further Properties of Set Categories"

  text\<open>
    In this section we further develop the consequences of the \<open>set_category\<close>
    axioms, and establish characterizations of a number of standard category-theoretic
    notions for a \<open>set_category\<close>.
\<close>

  context set_category
  begin
  
    abbreviation Dom
    where "Dom f \<equiv> set (dom f)"
    
    abbreviation Cod
    where "Cod f \<equiv> set (cod f)"

    subsection "Initial Object"

    text\<open>
      The object corresponding to the empty set is an initial object.
\<close>

    definition empty
    where "empty = mkIde {}"

    lemma initial_empty:
    shows "initial empty"
    proof
      show 0: "ide empty"
        using empty_def by (simp add: setp_empty)
      show "\<And>b. ide b \<Longrightarrow> \<exists>!f. \<guillemotleft>f : empty \<rightarrow> b\<guillemotright>"
      proof -
        fix b
        assume b: "ide b"
        show "\<exists>!f. \<guillemotleft>f : empty \<rightarrow> b\<guillemotright>"
        proof
          show 1: "\<guillemotleft>mkArr {} (set b) (\<lambda>x. x) : empty \<rightarrow> b\<guillemotright>"
            using 0 b empty_def mkArr_in_hom mkIde_set setp_imp_subset_Univ arr_mkIde
            by (metis Pi_I empty_iff ide_def mkIde_def)
          show "\<And>f. \<guillemotleft>f : empty \<rightarrow> b\<guillemotright> \<Longrightarrow> f = mkArr {} (set b) (\<lambda>x. x)"
            by (metis "1" arr_mkArr empty_iff in_homE empty_def mkArr_Fun mkArr_eqI set_mkIde)
        qed
      qed
    qed

    subsection "Identity Arrows"
    
    text\<open>
      Identity arrows correspond to restrictions of the identity function.
\<close>

    lemma ide_char\<^sub>S\<^sub>C:
    assumes "arr f"
    shows "ide f \<longleftrightarrow> Dom f = Cod f \<and> Fun f = (\<lambda>x \<in> Dom f. x)"
      using assms mkIde_as_mkArr mkArr_Fun Fun_ide in_homE ide_cod mkArr_Fun mkIde_set
      by (metis ide_char)

    lemma ideI:
    assumes "arr f" and "Dom f = Cod f" and "\<And>x. x \<in> Dom f \<Longrightarrow> Fun f x = x"
    shows "ide f"
    proof -
      have "Fun f = (\<lambda>x \<in> Dom f. x)"
        using assms Fun_def by auto
      thus ?thesis using assms ide_char\<^sub>S\<^sub>C by blast
    qed

    subsection "Inclusions"
    
    lemma ide_implies_incl:
    assumes "ide a"
    shows "incl a"
      by (simp add: assms incl_def)
    
    definition incl_in :: "'s \<Rightarrow> 's \<Rightarrow> bool"
    where "incl_in a b = (ide a \<and> ide b \<and> set a \<subseteq> set b)"
    
    abbreviation incl_of
    where "incl_of a b \<equiv> mkArr (set a) (set b) (\<lambda>x. x)"

    lemma elem_set_implies_set_eq_singleton:
    assumes "a \<in> set b"
    shows "set a = {a}"
    proof -
      have "ide b" using assms set_def by auto
      thus ?thesis using assms setp_imp_subset_Univ terminal_char2
        by (metis setp_set' insert_subset mem_Collect_eq mk_disjoint_insert)
    qed

    lemma elem_set_implies_incl_in:
    assumes "a \<in> set b"
    shows "incl_in a b"
    proof -
      have b: "ide b" using assms set_def by auto
      hence "setp (set b)" by simp
      hence "a \<in> Univ \<and> set a \<subseteq> set b"
        using setp_imp_subset_Univ assms elem_set_implies_set_eq_singleton by auto
      hence "ide a \<and> set a \<subseteq> set b"
        using b terminal_char1 by simp
      thus ?thesis using b incl_in_def by simp
    qed
    
    lemma incl_incl_of [simp]:
    assumes "incl_in a b"
    shows "incl (incl_of a b)"
    and "\<guillemotleft>incl_of a b : a \<rightarrow> b\<guillemotright>"
    proof -
      show "\<guillemotleft>incl_of a b : a \<rightarrow> b\<guillemotright>"
        using assms incl_in_def mkArr_in_hom
        by (metis image_ident image_subset_iff_funcset mkIde_set setp_set_ide)
      thus "incl (incl_of a b)"
        using assms incl_def incl_in_def by fastforce
    qed
    
    text\<open>
      There is at most one inclusion between any pair of objects.
\<close>

    lemma incls_coherent:
    assumes "par f f'" and "incl f" and "incl f'"
    shows "f = f'"
      using assms incl_def fun_complete by auto

    text\<open>
      The set of inclusions is closed under composition.
\<close>

    lemma incl_comp [simp]:
    assumes "incl f" and "incl g" and "cod f = dom g"
    shows "incl (g \<cdot> f)"
    proof -
      have 1: "seq g f" using assms incl_def by auto
      moreover have 2: "Dom (g \<cdot> f) \<subseteq> Cod (g \<cdot> f)"
        using assms 1 incl_def by auto
      moreover have "g \<cdot> f = mkArr (Dom f) (Cod g) (restrict (\<lambda>x. x) (Dom f))"
      proof (intro arr_eqI\<^sub>S\<^sub>C)
        have 3: "arr (mkArr (Dom f) (Cod g) (\<lambda>x\<in>Dom f. x))"
          by (metis 1 2 cod_comp dom_comp ide_cod ide_dom incl_def incl_in_def
              incl_incl_of(1) mkArr_restrict_eq)
        show 4: "par (g \<cdot> f) (mkArr (Dom f) (Cod g) (\<lambda>x\<in>Dom f. x))"
          using assms 1 3 mkIde_set by auto
        show "Fun (g \<cdot> f) = Fun (mkArr (Dom f) (Cod g) (\<lambda>x\<in>Dom f. x))"
          using assms 3 4 Fun_comp Fun_mkArr
          by (metis comp_cod_arr dom_cod ide_cod ide_implies_incl incl_def mkArr_restrict_eq')
      qed
      ultimately show ?thesis using incl_def by force
    qed

    subsection "Image Factorization"

    text\<open>
      The image of an arrow is the object that corresponds to the set-theoretic
      image of the domain set under the function induced by the arrow.
\<close>

    abbreviation Img
    where "Img f \<equiv> Fun f ` Dom f"

    definition img
    where "img f = mkIde (Img f)"

    lemma ide_img [simp]:
    assumes "arr f"
    shows "ide (img f)"
    proof -
      have "Fun f ` Dom f \<subseteq> Cod f" using assms Fun_mapsto by blast
      moreover have "setp (Cod f)" using assms by simp
      ultimately show ?thesis using img_def setp_respects_subset by auto
    qed
    
    lemma set_img [simp]:
    assumes "arr f"
    shows "set (img f) = Img f"
    proof -
      have 1: "Img f \<subseteq> Cod f \<and> setp (set (cod f))"
        using assms Fun_mapsto by auto
      hence "Fun f ` set (dom f) \<subseteq> Univ"
        using setp_imp_subset_Univ by blast
      thus ?thesis
        using assms 1 img_def set_mkIde setp_respects_subset by auto
    qed

    lemma img_point_in_Univ:
    assumes "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
    shows "img x \<in> Univ"
    proof -
      have "set (img x) = {Fun x unity}"
        using assms terminal_char2 terminal_unity\<^sub>S\<^sub>C by auto
      thus "img x \<in> Univ" using assms terminal_char1 by auto
    qed

    lemma incl_in_img_cod:
    assumes "arr f"
    shows "incl_in (img f) (cod f)"
    proof (unfold img_def)
      have 1: "Img f \<subseteq> Cod f \<and> setp (Cod f)"
        using assms Fun_mapsto by auto
      hence 2: "ide (mkIde (Img f))"
        using setp_respects_subset by auto
      moreover have "ide (cod f)" using assms by auto
      moreover have "set (mkIde (Img f)) \<subseteq> Cod f"
        using 1 2 using setp_respects_subset by force
      ultimately show "incl_in (mkIde (Img f)) (cod f)"
        using assms incl_in_def ide_cod by blast
    qed

    lemma img_point_elem_set:
    assumes "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
    shows "img x \<in> set a"
      by (metis assms img_point_in_Univ in_homE incl_in_img_cod insert_subset
          mem_Collect_eq incl_in_def terminal_char2)

    text\<open>
      The corestriction of an arrow @{term f} is the arrow
      @{term "corestr f \<in> hom (dom f) (img f)"} that induces the same function
      on the universe as @{term f}.
\<close>

    definition corestr
    where "corestr f = mkArr (Dom f) (Img f) (Fun f)"
    
    lemma corestr_in_hom:
    assumes "arr f"
    shows "\<guillemotleft>corestr f : dom f \<rightarrow> img f\<guillemotright>"
      by (metis assms corestr_def equalityD2 ide_dom ide_img image_subset_iff_funcset
          mkIde_set set_img mkArr_in_hom setp_set_ide)
    
    text\<open>
      Every arrow factors as a corestriction followed by an inclusion.
\<close>

    lemma img_fact:
    assumes "arr f"
    shows "S (incl_of (img f) (cod f)) (corestr f) = f"
    proof (intro arr_eqI\<^sub>S\<^sub>C)
      have 1: "\<guillemotleft>corestr f : dom f \<rightarrow> img f\<guillemotright>"
        using assms corestr_in_hom by blast
      moreover have 2: "\<guillemotleft>incl_of (img f) (cod f) : img f \<rightarrow> cod f\<guillemotright>"
        using assms incl_in_img_cod incl_incl_of by fast
      ultimately show P: "par (incl_of (img f) (cod f) \<cdot> corestr f) f"
        using assms in_homE by blast
      show "Fun (incl_of (img f) (cod f) \<cdot> corestr f) = Fun f"
        by (metis (no_types, lifting) 1 2 Fun_comp Fun_ide Fun_mkArr P comp_cod_arr
            corestr_def ide_img in_homE mkArr_Fun)
    qed

    lemma Fun_corestr:
    assumes "arr f"
    shows "Fun (corestr f) = Fun f"
      by (metis Fun_mkArr arrI assms corestr_def corestr_in_hom mkArr_Fun)
    
    subsection "Points and Terminal Objects"

    text\<open>
      To each element @{term t} of @{term "set a"} is associated a point
      @{term "mkPoint a t \<in> hom unity a"}.  The function induced by such
      a point is the constant-@{term t} function on the set @{term "{unity}"}.
\<close>

    definition mkPoint
    where "mkPoint a t \<equiv> mkArr {unity} (set a) (\<lambda>_. t)"

    lemma mkPoint_in_hom:
    assumes "ide a" and "t \<in> set a"
    shows "\<guillemotleft>mkPoint a t : unity \<rightarrow> a\<guillemotright>"
      using assms mkArr_in_hom
      by (metis Pi_I mkIde_set setp_set_ide terminal_char2 terminal_unity\<^sub>S\<^sub>C mkPoint_def)

    lemma Fun_mkPoint:
    assumes "ide a" and "t \<in> set a"
    shows "Fun (mkPoint a t) = (\<lambda>_ \<in> {unity}. t)"
      using assms mkPoint_def terminal_unity\<^sub>S\<^sub>C mkPoint_in_hom by fastforce

    text\<open>
      For each object @{term a} the function @{term "mkPoint a"} has as its inverse
      the restriction of the function @{term img} to @{term "hom unity a"}
\<close>

    lemma mkPoint_img:
    shows "img \<in> hom unity a \<rightarrow> set a"
    and "\<And>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<Longrightarrow> mkPoint a (img x) = x"
    proof -
      show "img \<in> hom unity a \<rightarrow> set a"
        using img_point_elem_set by simp
      show "\<And>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<Longrightarrow> mkPoint a (img x) = x"
      proof -
        fix x
        assume x: "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
        show "mkPoint a (img x) = x"
        proof (intro arr_eqI\<^sub>S\<^sub>C)
          have 0: "img x \<in> set a"
            using x img_point_elem_set by metis
          hence 1: "mkPoint a (img x) \<in> hom unity a"
            using x mkPoint_in_hom by force
          thus 2: "par (mkPoint a (img x)) x"
            using x by fastforce
          have "Fun (mkPoint a (img x)) = (\<lambda>_ \<in> {unity}. img x)"
            using 1 mkPoint_def by auto
          also have "... = Fun x"
            by (metis 0 Fun_corestr calculation elem_set_implies_set_eq_singleton
                ide_cod ide_unity in_homE mem_Collect_eq Fun_mkPoint corestr_in_hom
                img_point_in_Univ mkPoint_in_hom singletonI terminalE x)
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
        using assms(1) mkPoint_in_hom by simp
      show "\<And>t. t \<in> set a \<Longrightarrow> img (mkPoint a t) = t"
        proof -
        fix t
        assume t: "t \<in> set a"
        show "img (mkPoint a t) = t"
        proof -
          have 1: "arr (mkPoint a t)"
            using assms t mkPoint_in_hom by auto
          have "Fun (mkPoint a t) ` {unity} = {t}"
            using 1 mkPoint_def by simp
          thus ?thesis
            by (metis in_homE img_def mkIde_set mkPoint_in_hom elem_set_implies_incl_in
                elem_set_implies_set_eq_singleton incl_in_def t terminal_char2 terminal_unity\<^sub>S\<^sub>C)
        qed
      qed
    qed

    text\<open>
      For each object @{term a} the elements of @{term "hom unity a"} are therefore in
      bijective correspondence with @{term "set a"}.
\<close>

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

    lemma setp_img_points:
    assumes "ide a"
    shows "setp (img ` hom unity a)"
      using assms
      by (metis image_subset_iff_funcset mkPoint_img(1) setp_respects_subset setp_set_ide)

    text\<open>
      The function on the universe induced by an arrow @{term f} agrees, under the bijection
      between @{term "hom unity (dom f)"} and @{term "Dom f"}, with the action of @{term f}
      by composition on @{term "hom unity (dom f)"}.
\<close>

    lemma Fun_point:
    assumes "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
    shows "Fun x = (\<lambda>_ \<in> {unity}. img x)"
      using assms mkPoint_img img_mkPoint Fun_mkPoint [of a "img x"] img_point_elem_set
      by auto

    lemma comp_arr_mkPoint:
    assumes "arr f" and "t \<in> Dom f"
    shows "f \<cdot> mkPoint (dom f) t = mkPoint (cod f) (Fun f t)"
    proof (intro arr_eqI\<^sub>S\<^sub>C)
      have 0: "seq f (mkPoint (dom f) t)"
        using assms mkPoint_in_hom [of "dom f" t] by auto
      have 1: "\<guillemotleft>f \<cdot> mkPoint (dom f) t : unity \<rightarrow> cod f\<guillemotright>"
        using assms mkPoint_in_hom [of "dom f" t] by auto
      show "par (f \<cdot> mkPoint (dom f) t) (mkPoint (cod f) (Fun f t))"
      proof -
        have "\<guillemotleft>mkPoint (cod f) (Fun f t) : unity \<rightarrow> cod f\<guillemotright>"
          using assms Fun_mapsto mkPoint_in_hom [of "cod f" "Fun f t"] by auto
        thus ?thesis using 1 by fastforce
      qed
      show "Fun (f \<cdot> mkPoint (dom f) t) = Fun (mkPoint (cod f) (Fun f t))"
      proof -
        have "Fun (f \<cdot> mkPoint (dom f) t) = restrict (Fun f o Fun (mkPoint (dom f) t)) {unity}"
          using assms 0 1 Fun_comp terminal_char2 terminal_unity\<^sub>S\<^sub>C by auto
        also have "... = (\<lambda>_ \<in> {unity}. Fun f t)"
          using assms Fun_mkPoint by auto
        also have "... = Fun (mkPoint (cod f) (Fun f t))"
          using assms Fun_mkPoint [of "cod f" "Fun f t"] Fun_mapsto by fastforce
        finally show ?thesis by auto
      qed
    qed

    lemma comp_arr_point\<^sub>S\<^sub>S\<^sub>C:
    assumes "arr f" and "\<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright>"
    shows "f \<cdot> x = mkPoint (cod f) (Fun f (img x))"
      by (metis assms comp_arr_mkPoint img_point_elem_set mkPoint_img(2))

    text\<open>
      This agreement allows us to express @{term "Fun f"} in terms of composition.
\<close>

    lemma Fun_in_terms_of_comp:
    assumes "arr f"
    shows "Fun f = restrict (img o S f o mkPoint (dom f)) (Dom f)"
    proof
      fix t
      have "t \<notin> Dom f \<Longrightarrow> Fun f t = restrict (img o S f o mkPoint (dom f)) (Dom f) t"
        using assms by (simp add: Fun_def)
      moreover have "t \<in> Dom f \<Longrightarrow>
                     Fun f t = restrict (img o S f o mkPoint (dom f)) (Dom f) t"
      proof -
        assume t: "t \<in> Dom f"
        have 1: "f \<cdot> mkPoint (dom f) t = mkPoint (cod f) (Fun f t)"
          using assms t comp_arr_mkPoint by simp
        hence "img (f \<cdot> mkPoint (dom f) t) = img (mkPoint (cod f) (Fun f t))" by simp
        thus ?thesis
        proof -
          have "Fun f t \<in> Cod f" using assms t Fun_mapsto by auto
          thus ?thesis using assms t 1 img_mkPoint by auto
        qed
      qed
      ultimately show "Fun f t = restrict (img o S f o mkPoint (dom f)) (Dom f) t" by auto
    qed

    text\<open>
      We therefore obtain a rule for proving parallel arrows equal by showing
      that they have the same action by composition on points.
\<close>

    (*
     * TODO: Find out why attempts to use this as the main rule for a proof loop
     * unless the specific instance is given.
     *)
    lemma arr_eqI'\<^sub>S\<^sub>C:
    assumes "par f f'" and "\<And>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<Longrightarrow> f \<cdot> x = f' \<cdot> x"
    shows "f = f'"
      using assms Fun_in_terms_of_comp mkPoint_in_hom by (intro arr_eqI\<^sub>S\<^sub>C, auto)

    text\<open>
      An arrow can therefore be specified by giving its action by composition on points.
      In many situations, this is more natural than specifying it as a function on the universe.
\<close>

    definition mkArr'
    where "mkArr' a b F = mkArr (set a) (set b) (img o F o mkPoint a)"

    lemma mkArr'_in_hom:
    assumes "ide a" and "ide b" and "F \<in> hom unity a \<rightarrow> hom unity b"
    shows "\<guillemotleft>mkArr' a b F : a \<rightarrow> b\<guillemotright>"
    proof -
      have "img o F o mkPoint a \<in> set a \<rightarrow> set b"
        using assms(1,3) img_mkPoint(1) mkPoint_img(1) by fastforce
      thus ?thesis
        using assms mkArr'_def mkArr_in_hom [of "set a" "set b"] mkIde_set by simp
    qed

    lemma comp_point_mkArr':
    assumes "ide a" and "ide b" and "F \<in> hom unity a \<rightarrow> hom unity b"
    shows "\<And>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<Longrightarrow> mkArr' a b F \<cdot> x = F x"
    proof -
      fix x
      assume x: "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
      have "Fun (mkArr' a b F) (img x) = img (F x)"
        unfolding mkArr'_def
        using assms x Fun_mkArr img_point_elem_set mkPoint_img mkPoint_in_hom
        by (simp add: Pi_iff)
      hence "mkArr' a b F \<cdot> x = mkPoint b (img (F x))"
        using assms x mkArr'_in_hom [of a b F] comp_arr_point\<^sub>S\<^sub>S\<^sub>C by auto
      thus "mkArr' a b F \<cdot> x = F x"
        using assms x mkPoint_img(2) by auto
    qed

    text\<open>
      A third characterization of terminal objects is as those objects whose set of
      points is a singleton.
\<close>

    lemma terminal_char3:
    assumes "\<exists>!x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
    shows "terminal a"
    proof -
      have a: "ide a"
        using assms ide_cod mem_Collect_eq by blast
      hence "bij_betw img (hom unity a) (set a)"
        using assms bij_betw_points_and_set by auto
      hence "img ` (hom unity a) = set a"
        by (simp add: bij_betw_def)
      moreover have "hom unity a = {THE x. x \<in> hom unity a}"
        using assms theI' [of "\<lambda>x. x \<in> hom unity a"] by auto
      ultimately have "set a = {img (THE x. x \<in> hom unity a)}"
        by (metis image_empty image_insert)
      thus ?thesis using a terminal_char1 by simp
    qed

    text\<open>
      The following is an alternative formulation of functional completeness, which says that
      any function on points uniquely determines an arrow.
\<close>

    lemma fun_complete':
    assumes "ide a" and "ide b" and "F \<in> hom unity a \<rightarrow> hom unity b"
    shows "\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
    proof
      have 1: "\<guillemotleft>mkArr' a b F : a \<rightarrow> b\<guillemotright>" using assms mkArr'_in_hom by auto
      moreover have 2: "\<And>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<Longrightarrow> mkArr' a b F \<cdot> x = F x"
        using assms comp_point_mkArr' by auto
      ultimately show "\<guillemotleft>mkArr' a b F : a \<rightarrow> b\<guillemotright> \<and>
                       (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> mkArr' a b F \<cdot> x = F x)" by blast
      fix f
      assume f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
      show "f = mkArr' a b F"
        using f 1 2 by (intro arr_eqI'\<^sub>S\<^sub>C [of f "mkArr' a b F"], fastforce, auto)
    qed

    subsection "The `Determines Same Function' Relation on Arrows"

    text\<open>
      An important part of understanding the structure of a category of sets and functions
      is to characterize when it is that two arrows ``determine the same function''.
      The following result provides one answer to this: two arrows with a common domain
      determine the same function if and only if they can be rendered equal by composing with
      a cospan of inclusions.
\<close>

    lemma eq_Fun_iff_incl_joinable:
    assumes "span f f'"
    shows "Fun f = Fun f' \<longleftrightarrow>
           (\<exists>m m'. incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> m \<cdot> f = m' \<cdot> f')"
    proof
      assume ff': "Fun f = Fun f'"
      let ?b = "mkIde (Cod f \<union> Cod f')"
      let ?m = "incl_of (cod f) ?b"
      let ?m' = "incl_of (cod f') ?b"
      have incl_m: "incl ?m"
        using assms incl_incl_of [of "cod f" ?b] incl_in_def setp_respects_union by simp
      have incl_m': "incl ?m'"
        using assms incl_incl_of [of "cod f'" ?b] incl_in_def setp_respects_union by simp
      have m: "?m = mkArr (Cod f) (Cod f \<union> Cod f') (\<lambda>x. x)"
        using setp_respects_union by (simp add: assms)
      have m': "?m' = mkArr (Cod f') (Cod f \<union> Cod f') (\<lambda>x. x)"
        using setp_respects_union by (simp add: assms)
      have seq: "seq ?m f \<and> seq ?m' f'"
        using assms m m' using setp_respects_union by simp
      have "?m \<cdot> f = ?m' \<cdot> f'"
        by (metis assms comp_mkArr ff' incl_def incl_m incl_m' mkArr_Fun)
      hence "incl ?m \<and> incl ?m' \<and> seq ?m f \<and> seq ?m' f' \<and> ?m \<cdot> f = ?m' \<cdot> f'"
        using seq \<open>incl ?m\<close> \<open>incl ?m'\<close> by simp
      thus "\<exists>m m'. incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> m \<cdot> f = m' \<cdot> f'" by auto
      next
      assume ff': "\<exists>m m'. incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> m \<cdot> f = m' \<cdot> f'"
      show "Fun f = Fun f'"
        using ff'
        by (metis Fun_comp Fun_ide comp_cod_arr ide_cod seqE Fun_incl)
    qed

    text\<open>
      Another answer to the same question: two arrows with a common domain determine the
      same function if and only if their corestrictions are equal.
\<close>

    lemma eq_Fun_iff_eq_corestr:
    assumes "span f f'"
    shows "Fun f = Fun f' \<longleftrightarrow> corestr f = corestr f'"
      using assms corestr_def Fun_corestr by metis

    subsection "Retractions, Sections, and Isomorphisms"

    text\<open>
      An arrow is a retraction if and only if its image coincides with its codomain.
\<close>

    lemma retraction_if_Img_eq_Cod:
    assumes "arr g" and "Img g = Cod g"
    shows "retraction g"
    and "ide (g \<cdot> mkArr (Cod g) (Dom g) (inv_into (Dom g) (Fun g)))"
    proof -
      let ?F = "inv_into (Dom g) (Fun g)"
      let ?f = "mkArr (Cod g) (Dom g) ?F"
      have f: "arr ?f"
        by (simp add: assms inv_into_into)
      show "ide (g \<cdot> ?f)"
      proof -
        have "g = mkArr (Dom g) (Cod g) (Fun g)" using assms mkArr_Fun by auto
        hence "g \<cdot> ?f = mkArr (Cod g) (Cod g) (Fun g o ?F)"
          using assms(1) f comp_mkArr by metis
        moreover have "mkArr (Cod g) (Cod g) (\<lambda>y. y) = ..."
        proof (intro mkArr_eqI')
          show "arr (mkArr (Cod g) (Cod g) (\<lambda>y. y))"
            using assms arr_cod_iff_arr by auto
          show "\<And>y. y \<in> Cod g \<Longrightarrow> y = (Fun g o ?F) y"
            using assms by (simp add: f_inv_into_f)
        qed
        ultimately show ?thesis
          using assms f mkIde_as_mkArr by auto
      qed
      thus "retraction g" by auto
    qed

    lemma retraction_char:
    shows "retraction g \<longleftrightarrow> arr g \<and> Img g = Cod g"
    proof
      assume G: "retraction g"
      show "arr g \<and> Img g = Cod g"
      proof
        show "arr g" using G by blast
        show "Img g = Cod g"
        proof -
          from G obtain f where f: "ide (g \<cdot> f)" by blast
          have "Fun g ` Fun f ` Cod g = Cod g"
          proof -
            have "restrict (Fun g o Fun f) (Cod g) = restrict (\<lambda>x. x) (Cod g)"
              using f Fun_comp Fun_ide ide_compE by metis
            thus ?thesis
              by (metis image_comp image_ident image_restrict_eq)
          qed
          moreover have "Fun f ` Cod g \<subseteq> Dom g"
            using f Fun_mapsto arr_mkArr mkArr_Fun funcset_image
            by (metis seqE ide_compE ide_compE)
          moreover have "Img g \<subseteq> Cod g"
            using f Fun_mapsto by blast
          ultimately show ?thesis by blast
        qed
      qed
      next
      assume "arr g \<and> Img g = Cod g"
      thus "retraction g" using retraction_if_Img_eq_Cod by blast
    qed

    text\<open>
      Every corestriction is a retraction.
\<close>

    lemma retraction_corestr:
    assumes "arr f"
    shows "retraction (corestr f)"
      using assms retraction_char Fun_corestr corestr_in_hom in_homE set_img
      by metis

    text\<open>
      An arrow is a section if and only if it induces an injective function on its
      domain, except in the special case that it has an empty domain set and a
      nonempty codomain set.
\<close>

    lemma section_if_inj:
    assumes "arr f" and "inj_on (Fun f) (Dom f)" and "Dom f = {} \<longrightarrow> Cod f = {}"
    shows "section f"
    and "ide (mkArr (Cod f) (Dom f)
                    (\<lambda>y. if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                         else SOME x. x \<in> Dom f)
                \<cdot> f)"
    proof -
      let ?P= "\<lambda>y. \<lambda>x. x \<in> Dom f \<and> Fun f x = y"
      let ?G = "\<lambda>y. if y \<in> Img f then SOME x. ?P y x else SOME x. x \<in> Dom f"
      let ?g = "mkArr (Cod f) (Dom f) ?G"
      have g: "arr ?g"
      proof -
        have 1: "setp (Cod f)" using assms by simp
        have 2: "setp (Dom f)" using assms by simp
        have 3: "?G \<in> Cod f \<rightarrow> Dom f"
        proof
          fix y
          assume Y: "y \<in> Cod f"
          show "?G y \<in> Dom f"
          proof (cases "y \<in> Img f")
            assume "y \<in> Img f"
            hence "(\<exists>x. ?P y x) \<and> ?G y = (SOME x. ?P y x)" using Y by auto
            hence "?P y (?G y)" using someI_ex [of "?P y"] by argo
            thus "?G y \<in> Dom f" by auto
            next
            assume "y \<notin> Img f"
            hence "(\<exists>x. x \<in> Dom f) \<and> ?G y = (SOME x. x \<in> Dom f)" using assms Y by auto
            thus "?G y \<in> Dom f" using someI_ex [of "\<lambda>x. x \<in> Dom f"] by argo
          qed
        qed
        show ?thesis using 1 2 3 by simp
      qed
      show "ide (?g \<cdot> f)"
      proof -
        have "f = mkArr (Dom f) (Cod f) (Fun f)" using assms mkArr_Fun by auto
        hence "?g \<cdot> f = mkArr (Dom f) (Dom f) (?G o Fun f)"
          using assms(1) g comp_mkArr [of "Dom f" "Cod f" "Fun f" "Dom f" ?G] by argo
        moreover have "mkArr (Dom f) (Dom f) (\<lambda>x. x) = ..."
        proof (intro mkArr_eqI')
          show "arr (mkArr (Dom f) (Dom f) (\<lambda>x. x))"
            using assms by auto
          show "\<And>x. x \<in> Dom f \<Longrightarrow> x = (?G o Fun f) x"
          proof -
            fix x
            assume x: "x \<in> Dom f"
            have "Fun f x \<in> Img f" using x by blast
            hence *: "(\<exists>x'. ?P (Fun f x) x') \<and> ?G (Fun f x) = (SOME x'. ?P (Fun f x) x')"
              by auto
            then have "?P (Fun f x) (?G (Fun f x))"
              using someI_ex [of "?P (Fun f x)"] by argo
            with * have "x = ?G (Fun f x)"
              using assms x inj_on_def [of "Fun f" "Dom f"] by simp
            thus "x = (?G o Fun f) x" by simp
          qed
        qed
        ultimately show ?thesis
          using assms mkIde_as_mkArr mkIde_set by auto
      qed
      thus "section f" by auto
    qed

    lemma section_char:
    shows "section f \<longleftrightarrow> arr f \<and> (Dom f = {} \<longrightarrow> Cod f = {}) \<and> inj_on (Fun f) (Dom f)"
    proof
      assume f: "section f"
      from f obtain g where g: "ide (g \<cdot> f)" using section_def by blast
      show "arr f \<and> (Dom f = {} \<longrightarrow> Cod f = {}) \<and> inj_on (Fun f) (Dom f)"
      proof -
        have "arr f" using f by blast
        moreover have "Dom f = {} \<longrightarrow> Cod f = {}"
        proof -
          have "Cod f \<noteq> {} \<longrightarrow> Dom f \<noteq> {}"
          proof
            assume "Cod f \<noteq> {}"
            from this obtain y where "y \<in> Cod f" by blast
            hence "Fun g y \<in> Dom f"
              using g Fun_mapsto
              by (metis seqE ide_compE image_eqI retractionI retraction_char)
            thus "Dom f \<noteq> {}" by blast
          qed
          thus ?thesis by auto
        qed
        moreover have "inj_on (Fun f) (Dom f)"
          by (metis Fun_comp Fun_ide g ide_compE inj_on_id2 inj_on_imageI2 inj_on_restrict_eq)
        ultimately show ?thesis by auto
      qed
      next
      assume F: "arr f \<and> (Dom f = {} \<longrightarrow> Cod f = {}) \<and> inj_on (Fun f) (Dom f)"
      thus "section f" using section_if_inj by auto
    qed

    text\<open>
      Section-retraction pairs can also be characterized by an inverse relationship
      between the functions they induce.
\<close>

    lemma section_retraction_char:
    shows "ide (g \<cdot> f) \<longleftrightarrow> antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)"
      by (metis Fun_comp cod_comp compose_eq' dom_comp ide_char\<^sub>S\<^sub>C ide_compE seqE)

    text\<open>
      Antiparallel arrows @{term f} and @{term g} are inverses if the functions
      they induce are inverses.
\<close>

    lemma inverse_arrows_char:
    shows "inverse_arrows f g \<longleftrightarrow>
             antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)
                         \<and> compose (Dom g) (Fun f) (Fun g) = (\<lambda>y \<in> Dom g. y)"
      using section_retraction_char by blast

    text\<open>
      An arrow is an isomorphism if and only if the function it induces is a bijection.
\<close>

    lemma iso_char:
    shows "iso f \<longleftrightarrow> arr f \<and> bij_betw (Fun f) (Dom f) (Cod f)"
      by (metis bij_betw_def image_empty iso_iff_section_and_retraction retraction_char
          section_char)

    text\<open>
      The inverse of an isomorphism is constructed by inverting the induced function.
\<close>

    lemma inv_char:
    assumes "iso f"
    shows "inv f = mkArr (Cod f) (Dom f) (inv_into (Dom f) (Fun f))"
    proof -
      let ?g = "mkArr (Cod f) (Dom f) (inv_into (Dom f) (Fun f))"
      have "ide (f \<cdot> ?g)"
        using assms iso_is_retraction retraction_char retraction_if_Img_eq_Cod by simp
      moreover have "ide (?g \<cdot> f)"
      proof -
        let ?g' = "mkArr (Cod f) (Dom f)
                         (\<lambda>y. if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                              else SOME x. x \<in> Dom f)"
        have 1: "ide (?g' \<cdot> f)"
          using assms iso_is_section section_char section_if_inj by simp
        moreover have "?g' = ?g"
        proof
          show "arr ?g'" using 1 ide_compE by blast
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
      ultimately have "inverse_arrows f ?g" by auto
      thus ?thesis using inverse_unique by blast
    qed

    lemma Fun_inv:
    assumes "iso f"
    shows "Fun (inv f) = restrict (inv_into (Dom f) (Fun f)) (Cod f)"
      using assms inv_in_hom inv_char iso_inv_iso iso_is_arr Fun_mkArr by metis

    subsection "Monomorphisms and Epimorphisms"

    text\<open>
      An arrow is a monomorphism if and only if the function it induces is injective.
\<close>

    lemma mono_char:
    shows "mono f \<longleftrightarrow> arr f \<and> inj_on (Fun f) (Dom f)"
    proof
      assume f: "mono f"
      hence "arr f" using mono_def by auto
      moreover have "inj_on (Fun f) (Dom f)"
      proof (intro inj_onI)
        have 0: "inj_on (S f) (hom unity (dom f))"
        proof -
          have "hom unity (dom f) \<subseteq> {g. seq f g}"
            using f mono_def arrI by auto
          hence "\<exists>A. hom unity (dom f) \<subseteq> A \<and> inj_on (S f) A"
            using f mono_def by auto
          thus ?thesis
            by (meson subset_inj_on)
        qed
        fix x x'
        assume x: "x \<in> Dom f" and x': "x' \<in> Dom f" and xx': "Fun f x = Fun f x'"
        have "mkPoint (dom f) x \<in> hom unity (dom f) \<and>
              mkPoint (dom f) x' \<in> hom unity (dom f)"
          using x x' \<open>arr f\<close> mkPoint_in_hom by simp
        moreover have "f \<cdot> mkPoint (dom f) x = f \<cdot> mkPoint (dom f) x'"
          using \<open>arr f\<close> x x' xx' comp_arr_mkPoint by simp
        ultimately have "mkPoint (dom f) x = mkPoint (dom f) x'"
          using 0 inj_onD [of "S f" "hom unity (dom f)" "mkPoint (dom f) x"] by simp
        thus "x = x'"
          using \<open>arr f\<close> x x' img_mkPoint(2) img_mkPoint(2) ide_dom by metis
      qed
      ultimately show "arr f \<and> inj_on (Fun f) (Dom f)" by auto
      next
      assume f: "arr f \<and> inj_on (Fun f) (Dom f)"
      show "mono f"
      proof
        show "arr f" using f by auto
        show "\<And>g g'. \<lbrakk>seq f g; seq f g'; f \<cdot> g = f \<cdot> g'\<rbrakk> \<Longrightarrow> g = g'"
        proof -
          fix g g'
          assume fg: "seq f g" and fg': "seq f g'" and eq: "f \<cdot> g = f \<cdot> g'"
          show "g = g'"
          proof (intro arr_eqI\<^sub>S\<^sub>C)
            show par: "par g g'"
              using fg' eq dom_comp by (metis seqE)
            show "Fun g = Fun g'"
              by (metis empty_is_image eq f fg' ide_dom incl_in_def incl_in_img_cod
                  initial_arr_unique initial_empty empty_def monoE mkIde_set
                  section_if_inj(1) section_is_mono seqE set_img subset_empty)
          qed
        qed
      qed
    qed

    text\<open>
      Inclusions are monomorphisms.
\<close>

    lemma mono_imp_incl:
    assumes "incl f"
    shows "mono f"
      using assms incl_def Fun_incl mono_char by auto

    text\<open>
      A monomorphism is a section, except in case it has an empty domain set and
      a nonempty codomain set.
\<close>

    lemma mono_imp_section:
    assumes "mono f" and "Dom f = {} \<longrightarrow> Cod f = {}"
    shows "section f"
      using assms mono_char section_char by auto

    text\<open>
      An arrow is an epimorphism if and only if either its image coincides with its
      codomain, or else the universe has only a single element (in which case all arrows
      are epimorphisms).
\<close>

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
              have b: "ide ?b"
                by (metis B finite.emptyI finite_imp_setp finite_insert ide_mkIde
                    insert_subset setp_imp_subset_Univ setp_singleton mem_Collect_eq)
              have g: "\<guillemotleft>?g : cod f \<rightarrow> ?b\<guillemotright> \<and> Fun ?g = (\<lambda>y \<in> Cod f. tt)"
                using f B in_homI [of ?g "cod f" "mkIde {ff, tt}"] finite_imp_setp by simp
              have g': "?g' \<in> hom (cod f) ?b \<and>
                        Fun ?g' = (\<lambda>y \<in> Cod f. if \<exists>x. x \<in> Dom f \<and> Fun f x = y then tt else ff)"
                using f B in_homI [of ?g'] finite_imp_setp by simp
              have "?g \<cdot> f = ?g' \<cdot> f"
              proof (intro arr_eqI\<^sub>S\<^sub>C)
                show "par (?g \<cdot> f) (?g' \<cdot> f)"
                  using f g g' by auto
                show "Fun (?g \<cdot> f) = Fun (?g' \<cdot> f)"
                  using f g g' Fun_comp comp_mkArr by fastforce
              qed
              hence gg': "?g = ?g'"
                by (metis (no_types, lifting) epiE epi f g in_homE seqI)
              fix y
              assume y: "y \<in> Cod f"
              have "Fun ?g' y = tt" using gg' g y by simp
              hence "(if \<exists>x. x \<in> Dom f \<and> Fun f x = y then tt else ff) = tt"
                using g' y by simp
              hence "\<exists>x. x \<in> Dom f \<and> Fun f x = y"
                using B by argo
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
          using retraction_char retraction_is_epi by presburger
        moreover have "arr f \<and> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t') \<Longrightarrow> epi f"
        proof -
          assume f: "arr f \<and> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t')"
          have "\<And>f f'. par f f' \<Longrightarrow> f = f'"
          proof -
            fix f f'
            assume ff': "par f f'"
            show "f = f'"
            proof (intro arr_eqI\<^sub>S\<^sub>C)
              show "par f f'" using ff' by simp
              have "\<And>t t'. t \<in> Cod f \<and> t' \<in> Cod f \<Longrightarrow> t = t'"
                using f ff' setp_imp_subset_Univ setp_set_ide ide_cod subsetD by blast
              thus "Fun f = Fun f'"
                using ff' Fun_mapsto [of f] Fun_mapsto [of f']
                      extensional_arb [of "Fun f" "Dom f"] extensional_arb [of "Fun f'" "Dom f"]
                by fastforce
            qed
          qed
          moreover have "\<And>g g'. par (g \<cdot> f) (g' \<cdot> f) \<Longrightarrow> par g g'"
            by force
          ultimately show "epi f"
            using f by (intro epiI; metis)
        qed
        ultimately show "arr f \<and> (Img f = Cod f \<or>  (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t'))
                           \<Longrightarrow> epi f"
          by auto
      qed
    qed

    text\<open>
      An epimorphism is a retraction, except in the case of a degenerate universe with only
      a single element.
\<close>

    lemma epi_imp_retraction:
    assumes "epi f" and "\<exists>t t'. t \<in> Univ \<and> t' \<in> Univ \<and> t \<noteq> t'"
    shows "retraction f"
      using assms epi_char retraction_char by auto

    text\<open>
      Retraction/inclusion factorization is unique (not just up to isomorphism -- remember
      that the notion of inclusion is not categorical but depends on the arbitrarily chosen
      @{term img}).
\<close>

    lemma unique_retr_incl_fact:
    assumes "seq m e" and "seq m' e'" and "m \<cdot> e = m' \<cdot> e'"
    and "incl m" and "incl m'" and "retraction e" and "retraction e'"
    shows "m = m'" and "e = e'"
    proof -
      have 1: "cod m = cod m' \<and> dom e = dom e'"
        using assms(1-3) by (metis dom_comp cod_comp)
      hence 2: "span e e'" using assms(1-2) by blast
      hence 3: "Fun e = Fun e'"
        using assms eq_Fun_iff_incl_joinable by meson
      hence "img e = img e'" using assms 1 img_def by auto
      moreover have "img e = cod e \<and> img e' = cod e'"
        using assms(6-7) retraction_char img_def mkIde_set by simp
      ultimately have "par e e'" using 2 by simp
      thus "e = e'" using 3 arr_eqI\<^sub>S\<^sub>C by blast
      hence "par m m'" using assms(1) assms(2) 1 by fastforce
      thus "m = m'" using assms(4) assms(5) incls_coherent by blast
    qed

  end

  section "Concrete Set Categories"

  text\<open>
    The \<open>set_category\<close> locale is useful for stating results that depend on a
    category of @{typ 'a}-sets and functions, without having to commit to a particular
    element type @{typ 'a}.  However, in applications we often need to work with a
    category of sets and functions that is guaranteed to contain sets corresponding
    to the subsets of some extrinsically given type @{typ 'a}.
    A \emph{concrete set category} is a set category \<open>S\<close> that is equipped
    with an injective function @{term \<iota>} from type @{typ 'a} to \<open>S.Univ\<close>.
    The following locale serves to facilitate some of the technical aspects of passing
    back and forth between elements of type @{typ 'a} and the elements of \<open>S.Univ\<close>.
\<close>

  locale concrete_set_category = set_category S setp
    for S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
    and setp :: "'s set \<Rightarrow> bool"
    and U :: "'a set"
    and \<iota> :: "'a \<Rightarrow> 's" +
    assumes UP_mapsto: "\<iota> \<in> U \<rightarrow> Univ"
    and inj_UP: "inj_on \<iota> U"
  begin

    abbreviation UP
    where "UP \<equiv> \<iota>"

    abbreviation DN
    where "DN \<equiv> inv_into U UP"

    lemma DN_mapsto:
    shows "DN \<in> UP ` U \<rightarrow> U"
      by (simp add: inv_into_into)

    lemma DN_UP [simp]:
    assumes "x \<in> U"
    shows "DN (UP x) = x"
      using assms inj_UP inv_into_f_f by simp
      
    lemma UP_DN [simp]:
    assumes "t \<in> UP ` U"
    shows "UP (DN t) = t"
      using assms o_def inj_UP by auto

    lemma bij_UP:
    shows "bij_betw UP U (UP ` U)"
      using inj_UP inj_on_imp_bij_betw by blast

    lemma bij_DN:
    shows "bij_betw DN (UP ` U) U"
      using bij_UP bij_betw_inv_into by blast

  end

  locale replete_concrete_set_category =
    replete_set_category S +
    concrete_set_category S \<open>\<lambda>A. A \<subseteq> Univ\<close> U UP
    for S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
    and U :: "'a set"
    and UP :: "'a \<Rightarrow> 's"

  section "Sub-Set Categories"

  text\<open>
    In this section, we show that a full subcategory of a set category, obtained
    by imposing suitable further restrictions on the subsets of the universe
    that correspond to objects, is again a set category.
\<close>

  locale sub_set_category =
    S: set_category +
  fixes ssetp :: "'a set \<Rightarrow> bool"
  assumes ssetp_singleton: "\<And>t. t \<in> S.Univ \<Longrightarrow> ssetp {t}"
  and subset_closed: "\<And>B A. \<lbrakk>B \<subseteq> A; ssetp A\<rbrakk> \<Longrightarrow> ssetp B"
  and union_closed: "\<And>A B. \<lbrakk>ssetp A; ssetp B\<rbrakk> \<Longrightarrow> ssetp (A \<union> B)"
  and containment: "\<And>A. ssetp A \<Longrightarrow> setp A"
  begin

    sublocale full_subcategory S \<open>\<lambda>a. S.ide a \<and> ssetp (S.set a)\<close>
      by unfold_locales auto

    lemma is_full_subcategory:
    shows "full_subcategory S (\<lambda>a. S.ide a \<and> ssetp (S.set a))"
      ..

    lemma ide_char\<^sub>S\<^sub>S\<^sub>C:
    shows "ide a \<longleftrightarrow> S.ide a \<and> ssetp (S.set a)"
      using ide_char\<^sub>S\<^sub>b\<^sub>C arr_char\<^sub>S\<^sub>b\<^sub>C by fastforce

    lemma terminal_unity\<^sub>S\<^sub>S\<^sub>C:
    shows "terminal S.unity"
    proof
      show "ide S.unity"
        using S.terminal_unity\<^sub>S\<^sub>C S.terminal_def [of S.unity] S.terminal_char2 ide_char\<^sub>S\<^sub>S\<^sub>C
              ssetp_singleton
        by force
      thus "\<And>a. ide a \<Longrightarrow> \<exists>!f. in_hom f a S.unity"
        using S.terminal_unity\<^sub>S\<^sub>C S.terminal_def ide_char\<^sub>S\<^sub>b\<^sub>C ide_char' in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C
        by (metis (no_types, lifting))
    qed

    lemma terminal_char:
    shows "terminal t \<longleftrightarrow> S.terminal t"
    proof
      fix t
      assume t: "S.terminal t"
      have "ide t"
        using t ssetp_singleton ide_char\<^sub>S\<^sub>S\<^sub>C S.terminal_char2 by force
      thus "terminal t"
        using t in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C ide_char\<^sub>S\<^sub>S\<^sub>C arr_char\<^sub>S\<^sub>b\<^sub>C S.terminal_def terminalI by auto
      next
      assume t: "terminal t"
      have 1: "S.ide t"
        using t ide_char\<^sub>S\<^sub>b\<^sub>C terminal_def by simp
      moreover have "card (S.set t) = 1"
      proof -
        have "card (S.set t) = card (S.hom S.unity t)"
          using S.set_def S.inj_img
          by (metis 1 S.bij_betw_points_and_set bij_betw_same_card)
        also have "... = card (hom S.unity t)"
          using t in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C terminal_def terminal_unity\<^sub>S\<^sub>S\<^sub>C by auto
        also have "... = 1"
        proof -
          have "\<exists>!f. f \<in> hom S.unity t"
            using t terminal_def terminal_unity\<^sub>S\<^sub>S\<^sub>C by force
          moreover have "\<And>A. card A = 1 \<longleftrightarrow> (\<exists>!a. a \<in> A)"
            apply (intro iffI)
               apply (metis card_1_singletonE empty_iff insert_iff)
            using card_1_singleton_iff by auto
          ultimately show ?thesis by auto
        qed
        finally show ?thesis by blast
      qed
      ultimately show "S.terminal t"
        using 1 S.terminal_char1 card_1_singleton_iff
        by (metis One_nat_def singleton_iff)
    qed

    sublocale set_category comp ssetp
    proof
      text\<open>
        Here things are simpler if we define \<open>img\<close> appropriately so that we have
        \<open>set = T.set\<close> after accounting for the definition \<open>unity \<equiv> SOME t. terminal t\<close>,
        which is different from that of S.unity.
\<close>
      have 1: "terminal (SOME t. terminal t)"
        using terminal_unity\<^sub>S\<^sub>S\<^sub>C someI_ex [of terminal] by blast
      obtain i where i: "\<guillemotleft>i : S.unity \<rightarrow> SOME t. terminal t\<guillemotright>"
        using terminal_unity\<^sub>S\<^sub>S\<^sub>C someI_ex [of terminal] in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C terminal_def
        by auto
      obtain i' where i': "\<guillemotleft>i' : (SOME t. terminal t) \<rightarrow> S.unity\<guillemotright>"
        using terminal_unity\<^sub>S\<^sub>S\<^sub>C someI_ex [of S.terminal] S.terminal_def
        by (metis (no_types, lifting) 1 terminal_def)
      have ii': "inverse_arrows i i'"
      proof
        have "i' \<cdot> i = S.unity"
          using i i' terminal_unity\<^sub>S\<^sub>S\<^sub>C
          by (metis (no_types, lifting) S.comp_in_homI' S.ide_in_hom S.ide_unity S.in_homE
              S.terminalE S.terminal_unity\<^sub>S\<^sub>C in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C)
        thus 2: "ide (comp i' i)"
          by (metis (no_types, lifting) cod_comp comp_simp i i' ide_char' in_homE seqI')
        have "i \<cdot> i' = (SOME t. terminal t)"
          using 1
          by (metis (no_types, lifting) 2 comp_simp i' ide_compE in_homE inverse_arrowsE
              iso_iff_mono_and_retraction point_is_mono retractionI section_retraction_of_iso(2))
        thus "ide (comp i i')"
          using comp_char
          by (metis (no_types, lifting) 2 ide_char' dom_comp i' ide_compE in_homE seq_char\<^sub>S\<^sub>b\<^sub>C)
      qed
      interpret set_category_data comp \<open>\<lambda>x. S.some_img (x \<cdot> i)\<close> ..
      have i_in_hom: "\<guillemotleft>i : S.unity \<rightarrow> unity\<guillemotright>"
        using i unity_def by simp
      have i'_in_hom: "\<guillemotleft>i' : unity \<rightarrow> S.unity\<guillemotright>"
        using i' unity_def by simp
      have "\<And>a. ide a \<Longrightarrow> set a = S.set a"
      proof -
        fix a
        assume a: "ide a"
        have "set a = (\<lambda>x. S.some_img (x \<cdot> i)) ` hom unity a"
          using set_def by simp
        also have "... = S.some_img ` S.hom S.unity a"
        proof
          show "(\<lambda>x. S.some_img (x \<cdot> i)) ` hom unity a \<subseteq> S.some_img ` S.hom S.unity a"
            using i in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C i_in_hom by auto
          show "S.some_img ` S.hom S.unity a \<subseteq> (\<lambda>x. S.some_img (x \<cdot> i)) ` hom unity a"
          proof
            fix b
            assume b: "b \<in> S.some_img ` S.hom S.unity a"
            obtain x where x: "x \<in> S.hom S.unity a \<and> S.some_img x = b"
              using b by blast
            have "x \<cdot> i' \<in> hom unity a"
              using x in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C S.comp_in_homI a i' ideD(1) unity_def by force
            moreover have "S.some_img ((x \<cdot> i') \<cdot> i) = b"
              by (metis (no_types, lifting) i ii' x S.comp_assoc calculation comp_simp
                  ide_compE in_homE inverse_arrowsE mem_Collect_eq S.comp_arr_ide seqI'
                  seq_char\<^sub>S\<^sub>b\<^sub>C S.ide_unity unity_def)
            ultimately show "b \<in> (\<lambda>x. S.some_img (x \<cdot> i)) ` hom unity a" by blast
          qed
        qed
        also have "... = S.set a"
          using S.set_def by auto
        finally show "set a = S.set a" by blast
      qed
      interpret T: set_category_given_img comp \<open>\<lambda>x. S.some_img (x \<cdot> i)\<close> ssetp
      proof
        show "Collect terminal \<noteq> {}"
          using terminal_unity\<^sub>S\<^sub>S\<^sub>C by blast
        show "\<And>A' A. \<lbrakk>A' \<subseteq> A; ssetp A\<rbrakk> \<Longrightarrow> ssetp A'"
          using subset_closed by blast
        show "\<And>A B. \<lbrakk>ssetp A; ssetp B\<rbrakk> \<Longrightarrow> ssetp (A \<union> B)"
          using union_closed by simp
        show "\<And>A. ssetp A \<Longrightarrow> A \<subseteq> Univ"
          using S.setp_imp_subset_Univ containment terminal_char by presburger
        show "\<And>a b. \<lbrakk>ide a; ide b; set a = set b\<rbrakk> \<Longrightarrow> a = b"
          using ide_char\<^sub>S\<^sub>b\<^sub>C \<open>\<And>a. ide a \<Longrightarrow> set a = S.set a\<close> S.extensional_set by auto
        show "\<And>a. ide a \<Longrightarrow> ssetp (set a)"
          using \<open>\<And>a. ide a \<Longrightarrow> set a = S.set a\<close> ide_char\<^sub>S\<^sub>S\<^sub>C by force
        show "\<And>A. ssetp A \<Longrightarrow> \<exists>a. ide a \<and> set a = A"
          using S.set_complete \<open>\<And>a. ide a \<Longrightarrow> set a = S.set a\<close> containment ide_char\<^sub>S\<^sub>S\<^sub>C by blast
        show "\<And>t. terminal t \<Longrightarrow> t \<in> (\<lambda>x. S.some_img (x \<cdot> i)) ` hom unity t"
          using S.set_def S.stable_img \<open>\<And>a. ide a \<Longrightarrow> set a = S.set a\<close> set_def
                terminal_char terminal_def
          by force
        show "\<And>a. ide a \<Longrightarrow> inj_on (\<lambda>x. S.some_img (x \<cdot> i)) (hom unity a)"
        proof -
          fix a
          assume a: "ide a"
          show "inj_on (\<lambda>x. S.some_img (x \<cdot> i)) (hom unity a)"
          proof
            fix x y
            assume x: "x \<in> hom unity a" and y: "y \<in> hom unity a"
            and eq: "S.some_img (x \<cdot> i) = S.some_img (y \<cdot> i)"
            have "x \<cdot> i = y \<cdot> i"
            proof -
              have "x \<cdot> i \<in> S.hom S.unity a \<and> y \<cdot> i \<in> S.hom S.unity a"
                using in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C \<open>\<guillemotleft>i : S.unity \<rightarrow> unity\<guillemotright>\<close> x y by blast
              thus ?thesis
                using a eq ide_char\<^sub>S\<^sub>b\<^sub>C S.inj_img [of a] inj_on_def [of S.some_img] by simp
            qed
            have "x = (x \<cdot> i) \<cdot> i'"
              by (metis (no_types, lifting) S.comp_arr_ide S.comp_assoc S.inverse_arrowsE
                  S.match_4 i i' ii' inclusion_preserves_inverse mem_Collect_eq seqI'
                  seq_char\<^sub>S\<^sub>b\<^sub>C unity_def x)
            also have "... = (y \<cdot> i) \<cdot> i'"
              using \<open>x \<cdot> i = y \<cdot> i\<close> by simp
            also have "... = y"
              by (metis (no_types, lifting) S.comp_arr_ide S.comp_assoc S.inverse_arrowsE
                  S.match_4 i i' ii' inclusion_preserves_inverse mem_Collect_eq seqI'
                  seq_char\<^sub>S\<^sub>b\<^sub>C unity_def y)
            finally show "x = y" by simp
          qed
        qed
        show "\<And>f f'. \<lbrakk>par f f'; \<And>x. in_hom x unity (dom f) \<Longrightarrow> comp f x = comp f' x\<rbrakk>
                        \<Longrightarrow> f = f'"
        proof -
          fix f f'
          assume par: "par f f'"
          assume eq: "\<And>x. in_hom x unity (dom f) \<Longrightarrow> comp f x = comp f' x"
          have "S.par f f'"
            using par arr_char\<^sub>S\<^sub>b\<^sub>C dom_char\<^sub>S\<^sub>b\<^sub>C cod_char\<^sub>S\<^sub>b\<^sub>C by auto
          moreover have "\<And>x. S.in_hom x S.unity (S.dom f) \<Longrightarrow> f \<cdot> x = f' \<cdot> x"
          proof -
            fix x
            assume x: "S.in_hom x S.unity (S.dom f)"
            have "S.in_hom (x \<cdot> i') unity (S.dom f)"
              using i'_in_hom in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C x by blast
            hence 1: "in_hom (x \<cdot> i') unity (dom f)"
              using arr_dom dom_simp i in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C par unity_def by force
            hence "comp f (x \<cdot> i') = comp f' (x \<cdot> i')"
              using eq by blast
            hence "(f \<cdot> (x \<cdot> i')) \<cdot> i = (f' \<cdot> (x \<cdot> i')) \<cdot> i"
              using comp_char
              by (metis (no_types, lifting) 1 comp_simp in_homE seqI par)
            thus "f \<cdot> x = f' \<cdot> x"
              by (metis (no_types, lifting) S.comp_arr_dom S.comp_assoc S.comp_inv_arr
                  S.in_homE i_in_hom ii' in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C inclusion_preserves_inverse x)
          qed
          ultimately show "f = f'"
            using S.extensional_arr by blast
        qed
        show "\<And>a b F. \<lbrakk>ide a; ide b; F \<in> hom unity a \<rightarrow> hom unity b\<rbrakk>
                        \<Longrightarrow> \<exists>f. in_hom f a b \<and>
                                (\<forall>x. in_hom x unity (dom f) \<longrightarrow> comp f x = F x)"
        proof -
          fix a b F
          assume a: "ide a" and b: "ide b" and F: "F \<in> hom unity a \<rightarrow> hom unity b"
          have "S.ide a"
            using a ide_char\<^sub>S\<^sub>b\<^sub>C by blast
          have "S.ide b"
            using b ide_char\<^sub>S\<^sub>b\<^sub>C by blast
          have 1: "(\<lambda>x. F (x \<cdot> i') \<cdot> i) \<in> S.hom S.unity a \<rightarrow> S.hom S.unity b"
          proof
            fix x
            assume x: "x \<in> S.hom S.unity a"
            have "x \<cdot> i' \<in> S.hom unity a"
              using i'_in_hom in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C x by blast
            hence "x \<cdot> i' \<in> hom unity a"
              using a in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C
              by (metis (no_types, lifting) ideD(1) i'_in_hom in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C mem_Collect_eq)
            hence "F (x \<cdot> i') \<in> hom unity b"
              using a b F by blast
            hence "F (x \<cdot> i') \<in> S.hom unity b"
              using b in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C by blast
            thus "F (x \<cdot> i') \<cdot> i \<in> S.hom S.unity b"
              using i in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C unity_def by auto
          qed
          obtain f where f: "S.in_hom f a b \<and> (\<forall>x. S.in_hom x S.unity (S.dom f)
                               \<longrightarrow> f \<cdot> x = (\<lambda>x. F (x \<cdot> i') \<cdot> i) x)"
            using 1 S.fun_complete_ax \<open>S.ide a\<close> \<open>S.ide b\<close> by presburger
          show "\<exists>f. in_hom f a b \<and> (\<forall>x. in_hom x unity (dom f) \<longrightarrow> comp f x = F x)"
          proof -
            have "in_hom f a b"
              using f in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C ideD(1) a b by presburger
            moreover have "\<forall>x. in_hom x unity (dom f) \<longrightarrow> comp f x = F x"
            proof (intro allI impI)
              fix x
              assume x: "in_hom x unity (dom f)"
              have xi: "S.in_hom (x \<cdot> i) S.unity (S.dom f)"
                using f x i in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C dom_char\<^sub>S\<^sub>b\<^sub>C
                by (metis (no_types, lifting) in_homE unity_def calculation S.comp_in_homI)
              hence 1: "f \<cdot> (x \<cdot> i) = F ((x \<cdot> i) \<cdot> i') \<cdot> i"
                using f by blast
              hence "((f \<cdot> x) \<cdot> i) \<cdot> i' = (F x \<cdot> i) \<cdot> i'"
                by (metis (no_types, lifting) xi S.comp_assoc S.inverse_arrowsE
                    S.seqI' i' ii' in_hom_char\<^sub>F\<^sub>S\<^sub>b\<^sub>C inclusion_preserves_inverse S.comp_arr_ide)
              hence "f \<cdot> x = F x"
                by (metis (no_types, lifting) xi 1 S.invert_side_of_triangle(2) S.match_2 S.match_3
                    S.seqI arr_char\<^sub>S\<^sub>b\<^sub>C calculation S.in_homE S.inverse_unique S.isoI
                    ii' in_homE inclusion_preserves_inverse)
              thus "comp f x = F x"
                using comp_char
                by (metis (no_types, lifting) comp_simp in_homE seqI calculation x)
            qed
            ultimately show ?thesis by blast
          qed
        qed
      qed
      show "\<exists>img. set_category_given_img comp img ssetp"
        using T.set_category_given_img_axioms by blast
    qed

    lemma is_set_category:
    shows "set_category comp ssetp"
      ..

  end

end
