(*  Title:       Adjunction
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Adjunction

theory Adjunction
imports Yoneda
begin

  text\<open>
    This theory defines the notions of adjoint functor and adjunction in various
    ways and establishes their equivalence.
    The notions ``left adjoint functor'' and ``right adjoint functor'' are defined
    in terms of universal arrows.
    ``Meta-adjunctions'' are defined in terms of natural bijections between hom-sets,
    where the notion of naturality is axiomatized directly.
    ``Hom-adjunctions'' formalize the notion of adjunction in terms of natural
    isomorphisms of hom-functors.
    ``Unit-counit adjunctions'' define adjunctions in terms of functors equipped
    with unit and counit natural transformations that satisfy the usual
    ``triangle identities.''
    The \<open>adjunction\<close> locale is defined as the grand unification of all the
    definitions, and includes formulas that connect the data from each of them.
    It is shown that each of the definitions induces an interpretation of the
    \<open>adjunction\<close> locale, so that all the definitions are essentially equivalent.
    Finally, it is shown that right adjoint functors are unique up to natural
    isomorphism.

    The reference \<^cite>\<open>"Wikipedia-Adjoint-Functors"\<close> was useful in constructing this theory.
\<close>

  section "Left Adjoint Functor"

  text\<open>
    ``@{term e} is an arrow from @{term "F x"} to @{term y}.''
\<close>

  locale arrow_from_functor =
    C: category C +
    D: category D +
    F: "functor" D C F
    for D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and F :: "'d \<Rightarrow> 'c"
    and x :: 'd
    and y :: 'c
    and e :: 'c +
    assumes arrow: "D.ide x \<and> C.in_hom e (F x) y"
  begin

    notation C.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>\<close>)
    notation D.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>\<close>)

    text\<open>
      ``@{term g} is a @{term[source=true] D}-coextension of @{term f} along @{term e}.''
\<close>

    definition is_coext :: "'d \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
    where "is_coext x' f g \<equiv> \<guillemotleft>g : x' \<rightarrow>\<^sub>D x\<guillemotright> \<and> f = e \<cdot>\<^sub>C F g"

  end

  text\<open>
    ``@{term e} is a terminal arrow from @{term "F x"} to @{term y}.''
\<close>

  locale terminal_arrow_from_functor =
    arrow_from_functor D C F x y e
    for D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and F :: "'d \<Rightarrow> 'c"
    and x :: 'd
    and y :: 'c
    and e :: 'c +
    assumes is_terminal: "arrow_from_functor D C F x' y f \<Longrightarrow> (\<exists>!g. is_coext x' f g)"
  begin

    definition the_coext :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    where "the_coext x' f = (THE g. is_coext x' f g)"

    lemma the_coext_prop:
    assumes "arrow_from_functor D C F x' y f"
    shows "\<guillemotleft>the_coext x' f : x' \<rightarrow>\<^sub>D x\<guillemotright>" and "f = e \<cdot>\<^sub>C F (the_coext x' f)"
      by (metis assms is_coext_def is_terminal the_coext_def the_equality)+

    lemma the_coext_unique:
    assumes "arrow_from_functor D C F x' y f" and "is_coext x' f g"
    shows "g = the_coext x' f"
      using assms is_terminal the_coext_def the_equality by metis

  end

  text\<open>
    A left adjoint functor is a functor \<open>F: D \<rightarrow> C\<close>
    that enjoys the following universal coextension property: for each object
    @{term y} of @{term C} there exists an object @{term x} of @{term D} and an
    arrow \<open>e \<in> C.hom (F x) y\<close> such that for any arrow
    \<open>f \<in> C.hom (F x') y\<close> there exists a unique \<open>g \<in> D.hom x' x\<close>
    such that @{term "f = C e (F g)"}.
\<close>

  locale left_adjoint_functor =
    C: category C +
    D: category D +
    "functor" D C F
    for D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and F :: "'d \<Rightarrow> 'c" +
    assumes ex_terminal_arrow: "C.ide y \<Longrightarrow> (\<exists>x e. terminal_arrow_from_functor D C F x y e)"
  begin

    notation C.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>\<close>)
    notation D.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>\<close>)

  end

  section "Right Adjoint Functor"

  text\<open>
    ``@{term e} is an arrow from @{term x} to @{term "G y"}.''
\<close>

  locale arrow_to_functor =
    C: category C +
    D: category D +
    G: "functor" C D G
    for C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and G :: "'c \<Rightarrow> 'd"
    and x :: 'd
    and y :: 'c
    and e :: 'd +
    assumes arrow: "C.ide y \<and> D.in_hom e x (G y)"
  begin

    notation C.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>\<close>)
    notation D.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>\<close>)

    text\<open>
      ``@{term f} is a @{term[source=true] C}-extension of @{term g} along @{term e}.''
\<close>

    definition is_ext :: "'c \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> bool"
    where "is_ext y' g f \<equiv> \<guillemotleft>f : y \<rightarrow>\<^sub>C y'\<guillemotright> \<and> g = G f \<cdot>\<^sub>D e"

  end

  text\<open>
    ``@{term e} is an initial arrow from @{term x} to @{term "G y"}.''
\<close>

  locale initial_arrow_to_functor =
    arrow_to_functor C D G x y e
    for C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and G :: "'c \<Rightarrow> 'd"
    and x :: 'd
    and y :: 'c
    and e :: 'd +
    assumes is_initial: "arrow_to_functor C D G x y' g \<Longrightarrow> (\<exists>!f. is_ext y' g f)"
  begin

    definition the_ext :: "'c \<Rightarrow> 'd \<Rightarrow> 'c"
    where "the_ext y' g = (THE f. is_ext y' g f)"

    lemma the_ext_prop:
    assumes "arrow_to_functor C D G x y' g"
    shows "\<guillemotleft>the_ext y' g : y \<rightarrow>\<^sub>C y'\<guillemotright>" and "g = G (the_ext y' g) \<cdot>\<^sub>D e"
      by (metis assms is_initial is_ext_def the_equality the_ext_def)+

    lemma the_ext_unique:
    assumes "arrow_to_functor C D G x y' g" and "is_ext y' g f"
    shows "f = the_ext y' g"
      using assms is_initial the_ext_def the_equality by metis

  end

  text\<open>
    A right adjoint functor is a functor \<open>G: C \<rightarrow> D\<close>
    that enjoys the following universal extension property:
    for each object @{term x} of @{term D} there exists an object @{term y} of @{term C}
    and an arrow \<open>e \<in> D.hom x (G y)\<close> such that for any arrow
    \<open>g \<in> D.hom x (G y')\<close> there exists a unique \<open>f \<in> C.hom y y'\<close>
    such that @{term "h = D e (G f)"}.
\<close>

  locale right_adjoint_functor =
    C: category C +
    D: category D +
    "functor" C D G
    for C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and G :: "'c \<Rightarrow> 'd" +
    assumes ex_initial_arrow: "D.ide x \<Longrightarrow> (\<exists>y e. initial_arrow_to_functor C D G x y e)"
  begin

    notation C.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>\<close>)
    notation D.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>\<close>)

  end

  section "Various Definitions of Adjunction"

  subsection "Meta-Adjunction"

  text\<open>
    A ``meta-adjunction'' consists of a functor \<open>F: D \<rightarrow> C\<close>,
    a functor \<open>G: C \<rightarrow> D\<close>, and for each object @{term x}
    of @{term C} and @{term y} of @{term D} a bijection between
    \<open>C.hom (F y) x\<close> to \<open>D.hom y (G x)\<close> which is natural in @{term x}
    and @{term y}.  The naturality is easy to express at the meta-level without having
    to resort to the formal baggage of ``set category,'' ``hom-functor,''
    and ``natural isomorphism,'' hence the name.
\<close>

  locale meta_adjunction =
    C: category C +
    D: category D +
    F: "functor" D C F +
    G: "functor" C D G
    for C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and F :: "'d \<Rightarrow> 'c"
    and G :: "'c \<Rightarrow> 'd"
    and \<phi> :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    and \<psi> :: "'c \<Rightarrow> 'd \<Rightarrow> 'c" +
    assumes \<phi>_in_hom: "\<lbrakk> D.ide y; C.in_hom f (F y) x \<rbrakk> \<Longrightarrow> D.in_hom (\<phi> y f) y (G x)"
    and \<psi>_in_hom: "\<lbrakk> C.ide x; D.in_hom g y (G x) \<rbrakk> \<Longrightarrow> C.in_hom (\<psi> x g) (F y) x"
    and \<psi>_\<phi>: "\<lbrakk> D.ide y; C.in_hom f (F y) x \<rbrakk> \<Longrightarrow> \<psi> x (\<phi> y f) = f"
    and \<phi>_\<psi>: "\<lbrakk> C.ide x; D.in_hom g y (G x) \<rbrakk> \<Longrightarrow> \<phi> y (\<psi> x g) = g"
    and \<phi>_naturality: "\<lbrakk> C.in_hom f x x'; D.in_hom g y' y; C.in_hom h (F y) x \<rbrakk> \<Longrightarrow>
                         \<phi> y' (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) = G f \<cdot>\<^sub>D \<phi> y h \<cdot>\<^sub>D g"
  begin

    notation C.in_hom (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>\<close>)
    notation D.in_hom (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>\<close>)

    text\<open>
      The naturality of @{term \<psi>} is a consequence of the naturality of @{term \<phi>}
      and the other assumptions.
\<close>

    lemma \<psi>_naturality:
    assumes f: "\<guillemotleft>f : x \<rightarrow>\<^sub>C x'\<guillemotright>" and g: "\<guillemotleft>g : y' \<rightarrow>\<^sub>D y\<guillemotright>" and h: "\<guillemotleft>h : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "f \<cdot>\<^sub>C \<psi> x h \<cdot>\<^sub>C F g = \<psi> x' (G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g)"
      using f g h \<phi>_naturality \<psi>_in_hom C.ide_dom D.ide_dom D.in_homE \<phi>_\<psi> \<psi>_\<phi>
      by (metis C.comp_in_homI' F.preserves_hom C.in_homE D.in_homE)

    lemma respects_natural_isomorphism:
    assumes "natural_isomorphism D C F' F \<tau>" and "natural_isomorphism C D G G' \<mu>"
    shows "meta_adjunction C D F' G'
             (\<lambda>y f. \<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C inverse_transformation.map D C F \<tau> y))
             (\<lambda>x g. \<psi> x ((inverse_transformation.map C D G' \<mu> x) \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g))"
    proof -
      interpret \<tau>: natural_isomorphism D C F' F \<tau>
        using assms(1) by simp
      interpret \<tau>': inverse_transformation D C F' F \<tau>
        ..
      interpret \<mu>: natural_isomorphism C D G G' \<mu>
        using assms(2) by simp
      interpret \<mu>': inverse_transformation C D G G' \<mu>
        ..
      let ?\<phi>' = "\<lambda>y f. \<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y)"
      let ?\<psi>' = "\<lambda>x g. \<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g)"
      show "meta_adjunction C D F' G' ?\<phi>' ?\<psi>'"
      proof
        show "\<And>y f x. \<lbrakk>D.ide y; \<guillemotleft>f : F' y \<rightarrow>\<^sub>C x\<guillemotright>\<rbrakk>
                         \<Longrightarrow> \<guillemotleft>\<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y) : y \<rightarrow>\<^sub>D G' x\<guillemotright>"
        proof -
          fix x y f
          assume y: "D.ide y" and f: "\<guillemotleft>f : F' y \<rightarrow>\<^sub>C x\<guillemotright>"
          show "\<guillemotleft>\<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y) : y \<rightarrow>\<^sub>D G' x\<guillemotright>"
          proof (intro D.comp_in_homI)
            show "\<guillemotleft>\<mu> (C.cod f) : G x \<rightarrow>\<^sub>D G' x\<guillemotright>"
              using f by fastforce
            show "\<guillemotleft>\<phi> y (f \<cdot>\<^sub>C \<tau>'.map y) : y \<rightarrow>\<^sub>D G x\<guillemotright>"
              using f y \<phi>_in_hom by auto
          qed
        qed
        show "\<And>x g y. \<lbrakk>C.ide x; \<guillemotleft>g : y \<rightarrow>\<^sub>D G' x\<guillemotright>\<rbrakk>
                         \<Longrightarrow> \<guillemotleft>\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g) : F' y \<rightarrow>\<^sub>C x\<guillemotright>"
        proof -
          fix x y g
          assume x: "C.ide x" and g: "\<guillemotleft>g : y \<rightarrow>\<^sub>D G' x\<guillemotright>"
          show "\<guillemotleft>\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g) : F' y \<rightarrow>\<^sub>C x\<guillemotright>"
          proof (intro C.comp_in_homI)
            show "\<guillemotleft>\<tau> (D.dom g) : F' y \<rightarrow>\<^sub>C F y\<guillemotright>"
              using g by fastforce
            show "\<guillemotleft>\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) : F y \<rightarrow>\<^sub>C x\<guillemotright>"
              using x g \<psi>_in_hom by auto
          qed
        qed
        show "\<And>y f x. \<lbrakk>D.ide y; \<guillemotleft>f : F' y \<rightarrow>\<^sub>C x\<guillemotright>\<rbrakk>
                          \<Longrightarrow> \<psi> x (\<mu>'.map x \<cdot>\<^sub>D \<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y)) \<cdot>\<^sub>C
                                \<tau> (D.dom (\<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y))) =
                              f"
        proof -
          fix x y f
          assume y: "D.ide y" and f: "\<guillemotleft>f : F' y \<rightarrow>\<^sub>C x\<guillemotright>"
          have 1: "\<guillemotleft>\<phi> y (f \<cdot>\<^sub>C \<tau>'.map y) : y \<rightarrow>\<^sub>D G x\<guillemotright>"
            using f y \<phi>_in_hom by auto
          show "\<psi> x (\<mu>'.map x \<cdot>\<^sub>D \<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y)) \<cdot>\<^sub>C
                  \<tau> (D.dom (\<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y))) =
                f"
          proof -
            have "\<psi> x (\<mu>'.map x \<cdot>\<^sub>D \<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y)) \<cdot>\<^sub>C
                    \<tau> (D.dom (\<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y))) =
                  \<psi> x ((\<mu>'.map x \<cdot>\<^sub>D \<mu> (C.cod f)) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y)) \<cdot>\<^sub>C
                    \<tau> (D.dom (\<mu> (C.cod f) \<cdot>\<^sub>D \<phi> y (f \<cdot>\<^sub>C \<tau>'.map y)))"
              using D.comp_assoc by simp
            also have "... = \<psi> x (\<phi> y (f \<cdot>\<^sub>C \<tau>'.map y)) \<cdot>\<^sub>C \<tau> y"
              by (metis "1" C.arr_cod C.dom_cod C.ide_cod C.in_homE D.comp_ide_arr D.dom_comp
                  D.ide_compE D.in_homE D.inverse_arrowsE \<mu>'.inverts_components \<mu>.preserves_dom
                  \<mu>.preserves_reflects_arr category.seqI f meta_adjunction_axioms
                  meta_adjunction_def)
            also have "... = f"
              using f y \<psi>_\<phi> C.comp_assoc \<tau>'.inverts_components [of y] C.comp_arr_dom
              by fastforce
            finally show ?thesis by blast
          qed
        qed
        show "\<And>x g y. \<lbrakk>C.ide x; \<guillemotleft>g : y \<rightarrow>\<^sub>D G' x\<guillemotright>\<rbrakk>
                         \<Longrightarrow> \<mu> (C.cod (\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g))) \<cdot>\<^sub>D
                               \<phi> y ((\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g)) \<cdot>\<^sub>C \<tau>'.map y) =
                             g"
        proof -
          fix x y g
          assume x: "C.ide x" and g: "\<guillemotleft>g : y \<rightarrow>\<^sub>D G' x\<guillemotright>"
          have 1: "\<guillemotleft>\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) : F y \<rightarrow>\<^sub>C x\<guillemotright>"
            using x g \<psi>_in_hom by auto
          show "\<mu> (C.cod (\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g))) \<cdot>\<^sub>D
                  \<phi> y ((\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g)) \<cdot>\<^sub>C \<tau>'.map y) =
                g"
          proof -
            have "\<mu> (C.cod (\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g))) \<cdot>\<^sub>D
                    \<phi> y ((\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g)) \<cdot>\<^sub>C \<tau>'.map y) =
                  \<mu> (C.cod (\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g))) \<cdot>\<^sub>D
                    \<phi> y (\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g) \<cdot>\<^sub>C \<tau> (D.dom g) \<cdot>\<^sub>C \<tau>'.map y)"
              using C.comp_assoc by simp
            also have "... = \<mu> x \<cdot>\<^sub>D \<phi> y (\<psi> x (\<mu>'.map x \<cdot>\<^sub>D g))"
              using 1 C.comp_arr_dom C.comp_arr_inv' g by fastforce
            also have "... = (\<mu> x \<cdot>\<^sub>D \<mu>'.map x) \<cdot>\<^sub>D g"
              using x g \<phi>_\<psi> D.comp_assoc by auto
            also have "... = g"
              using x g \<mu>'.inverts_components [of x] D.comp_cod_arr by fastforce
            finally show ?thesis by blast
          qed
        qed
        show "\<And>f x x' g y' y h. \<lbrakk>\<guillemotleft>f : x \<rightarrow>\<^sub>C x'\<guillemotright>; \<guillemotleft>g : y' \<rightarrow>\<^sub>D y\<guillemotright>; \<guillemotleft>h : F' y \<rightarrow>\<^sub>C x\<guillemotright>\<rbrakk>
                  \<Longrightarrow> \<mu> (C.cod (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F' g)) \<cdot>\<^sub>D \<phi> y' ((f \<cdot>\<^sub>C h \<cdot>\<^sub>C F' g) \<cdot>\<^sub>C \<tau>'.map y') =
                      G' f \<cdot>\<^sub>D (\<mu> (C.cod h) \<cdot>\<^sub>D \<phi> y (h \<cdot>\<^sub>C \<tau>'.map y)) \<cdot>\<^sub>D g"
        proof -
          fix x y x' y' f g h
          assume f: "\<guillemotleft>f : x \<rightarrow>\<^sub>C x'\<guillemotright>" and g: "\<guillemotleft>g : y' \<rightarrow>\<^sub>D y\<guillemotright>" and h: "\<guillemotleft>h : F' y \<rightarrow>\<^sub>C x\<guillemotright>"
          show "\<mu> (C.cod (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F' g)) \<cdot>\<^sub>D \<phi> y' ((f \<cdot>\<^sub>C h \<cdot>\<^sub>C F' g) \<cdot>\<^sub>C \<tau>'.map y') =
                G' f \<cdot>\<^sub>D (\<mu> (C.cod h) \<cdot>\<^sub>D \<phi> y (h \<cdot>\<^sub>C \<tau>'.map y)) \<cdot>\<^sub>D g"
          proof -
            have "\<mu> (C.cod (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F' g)) \<cdot>\<^sub>D \<phi> y' ((f \<cdot>\<^sub>C h \<cdot>\<^sub>C F' g) \<cdot>\<^sub>C \<tau>'.map y') =
                  \<mu> x' \<cdot>\<^sub>D \<phi> y' ((f \<cdot>\<^sub>C h \<cdot>\<^sub>C F' g) \<cdot>\<^sub>C \<tau>'.map y')"
              using f g h by fastforce
            also have "... = \<mu> x' \<cdot>\<^sub>D \<phi> y' (f \<cdot>\<^sub>C (h \<cdot>\<^sub>C \<tau>'.map y) \<cdot>\<^sub>C F g)"
              using g \<tau>'.naturality C.comp_assoc by auto
            also have "... = (\<mu> x' \<cdot>\<^sub>D G f) \<cdot>\<^sub>D \<phi> y (h \<cdot>\<^sub>C \<tau>'.map y) \<cdot>\<^sub>D g"
              using f g h \<phi>_naturality [of f x x' g y' y "h \<cdot>\<^sub>C \<tau>'.map y"] D.comp_assoc
              by fastforce
            also have "... = (G' f \<cdot>\<^sub>D \<mu> x) \<cdot>\<^sub>D \<phi> y (h \<cdot>\<^sub>C \<tau>'.map y) \<cdot>\<^sub>D g"
              using f \<mu>.naturality by auto
            also have "... = G' f \<cdot>\<^sub>D (\<mu> (C.cod h) \<cdot>\<^sub>D \<phi> y (h \<cdot>\<^sub>C \<tau>'.map y)) \<cdot>\<^sub>D g"
              using h D.comp_assoc by auto
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

  end

  subsection "Hom-Adjunction"

  text\<open>
    The bijection between hom-sets that defines an adjunction can be represented
    formally as a natural isomorphism of hom-functors.  However, stating the definition
    this way is more complex than was the case for \<open>meta_adjunction\<close>.
    One reason is that we need to have a ``set category'' that is suitable as
    a target category for the hom-functors, and since the arrows of the categories
    @{term C} and @{term D} will in general have distinct types, we need a set category
    that simultaneously embeds both.  Another reason is that we simply have to formally
    construct the various categories and functors required to express the definition.

    This is a good place to point out that I have often included more sublocales
    in a locale than are strictly required.  The main reason for this is the fact that
    the locale system in Isabelle only gives one name to each entity introduced by
    a locale: the name that it has in the first locale in which it occurs.
    This means that entities that make their first appearance deeply nested in sublocales
    will have to be referred to by long qualified names that can be difficult to
    understand, or even to discover.  To counteract this, I have typically introduced
    sublocales before the superlocales that contain them to ensure that the entities
    in the sublocales can be referred to by short meaningful (and predictable) names.
    In my opinion, though, it would be better if the locale system would make entities
    that occur in multiple locales accessible by \emph{all} possible qualified names,
    so that the most perspicuous name could be used in any particular context.
\<close>

  locale hom_adjunction =
    C: category C +
    D: category D +
    S: set_category S setp +
    Cop: dual_category C +
    Dop: dual_category D +
    CopxC: product_category Cop.comp C +
    DopxD: product_category Dop.comp D +
    DopxC: product_category Dop.comp C +
    F: "functor" D C F +
    G: "functor" C D G +
    HomC: hom_functor C S setp \<phi>C +
    HomD: hom_functor D S setp \<phi>D +
    Fop: dual_functor Dop.comp Cop.comp F +
    FopxC: product_functor Dop.comp C Cop.comp C Fop.map C.map +
    DopxG: product_functor Dop.comp C Dop.comp D Dop.map G +
    Hom_FopxC: composite_functor DopxC.comp CopxC.comp S FopxC.map HomC.map +
    Hom_DopxG: composite_functor DopxC.comp DopxD.comp S DopxG.map HomD.map +
    Hom_FopxC: set_valued_functor DopxC.comp S setp Hom_FopxC.map +
    Hom_DopxG: set_valued_functor DopxC.comp S setp Hom_DopxG.map +
    \<Phi>: set_valued_transformation DopxC.comp S setp Hom_FopxC.map Hom_DopxG.map \<Phi> +
    \<Psi>: set_valued_transformation DopxC.comp S setp Hom_DopxG.map Hom_FopxC.map \<Psi> +
    \<Phi>\<Psi>: inverse_transformations DopxC.comp S Hom_FopxC.map Hom_DopxG.map \<Phi> \<Psi>
    for C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and S :: "'s comp"     (infixr \<open>\<cdot>\<^sub>S\<close> 55)
    and setp :: "'s set \<Rightarrow> bool"
    and \<phi>C :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and \<phi>D :: "'d * 'd \<Rightarrow> 'd \<Rightarrow> 's"
    and F :: "'d \<Rightarrow> 'c"
    and G :: "'c \<Rightarrow> 'd"
    and \<Phi> :: "'d * 'c \<Rightarrow> 's"
    and \<Psi> :: "'d * 'c \<Rightarrow> 's"
  begin

    notation C.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>\<close>)
    notation D.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>\<close>)

    abbreviation \<psi>C :: "'c * 'c \<Rightarrow> 's \<Rightarrow> 'c"
    where "\<psi>C \<equiv> HomC.\<psi>"

    abbreviation \<psi>D :: "'d * 'd \<Rightarrow> 's \<Rightarrow> 'd"
    where "\<psi>D \<equiv> HomD.\<psi>"

  end

  subsection "Unit/Counit Adjunction"

  text\<open>
    Expressed in unit/counit terms, an adjunction consists of functors
    \<open>F: D \<rightarrow> C\<close> and \<open>G: C \<rightarrow> D\<close>, equipped with natural transformations
    \<open>\<eta>: 1 \<rightarrow> GF\<close> and \<open>\<epsilon>: FG \<rightarrow> 1\<close> satisfying certain ``triangle identities''.
\<close>

  locale unit_counit_adjunction =
    C: category C +
    D: category D +
    F: "functor" D C F +
    G: "functor" C D G +
    GF: composite_functor D C D F G +
    FG: composite_functor C D C G F +
    FGF: composite_functor D C C F \<open>F o G\<close> +
    GFG: composite_functor C D D G \<open>G o F\<close> +
    \<eta>: natural_transformation D D D.map \<open>G o F\<close> \<eta> +
    \<epsilon>: natural_transformation C C \<open>F o G\<close> C.map \<epsilon> +
    F\<eta>: natural_transformation D C F \<open>F o G o F\<close> \<open>F o \<eta>\<close> +
    \<eta>G: natural_transformation C D G \<open>G o F o G\<close> \<open>\<eta> o G\<close> +
    \<epsilon>F: natural_transformation D C \<open>F o G o F\<close> F \<open>\<epsilon> o F\<close> +
    G\<epsilon>: natural_transformation C D \<open>G o F o G\<close> G \<open>G o \<epsilon>\<close> +
    \<epsilon>FoF\<eta>: vertical_composite D C F \<open>F o G o F\<close> F \<open>F o \<eta>\<close> \<open>\<epsilon> o F\<close> +
    G\<epsilon>o\<eta>G: vertical_composite C D G \<open>G o F o G\<close> G \<open>\<eta> o G\<close> \<open>G o \<epsilon>\<close>
    for C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and F :: "'d \<Rightarrow> 'c"
    and G :: "'c \<Rightarrow> 'd"
    and \<eta> :: "'d \<Rightarrow> 'd"
    and \<epsilon> :: "'c \<Rightarrow> 'c" +
    assumes triangle_F: "\<epsilon>FoF\<eta>.map = F"
    and triangle_G: "G\<epsilon>o\<eta>G.map = G"
  begin

    notation C.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>\<close>)
    notation D.in_hom      (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>\<close>)

  end

  lemma unit_determines_counit:
  assumes "unit_counit_adjunction C D F G \<eta> \<epsilon>"
  and "unit_counit_adjunction C D F G \<eta> \<epsilon>'"
  shows "\<epsilon> = \<epsilon>'"
  proof -
    (* IDEA:  \<epsilon>' = \<epsilon>'FG o (FG\<epsilon> o F\<eta>G) = \<epsilon>'\<epsilon> o F\<eta>G = \<epsilon>FG o (\<epsilon>'FG o F\<eta>G) = \<epsilon> *)
    interpret Adj: unit_counit_adjunction C D F G \<eta> \<epsilon> using assms(1) by auto
    interpret Adj': unit_counit_adjunction C D F G \<eta> \<epsilon>' using assms(2) by auto
    interpret FGFG: composite_functor C D C G \<open>F o G o F\<close> ..
    interpret FG\<epsilon>: natural_transformation C C \<open>(F o G) o (F o G)\<close> \<open>F o G\<close> \<open>(F o G) o \<epsilon>\<close>
      using Adj.\<epsilon>.natural_transformation_axioms Adj.FG.as_nat_trans.natural_transformation_axioms
            horizontal_composite
      by fastforce
    interpret F\<eta>G: natural_transformation C C \<open>F o G\<close> \<open>F o G o F o G\<close> \<open>F o \<eta> o G\<close>
      using Adj.\<eta>.natural_transformation_axioms Adj.F\<eta>.natural_transformation_axioms
            Adj.G.as_nat_trans.natural_transformation_axioms horizontal_composite
      by blast
    interpret \<epsilon>'\<epsilon>: natural_transformation C C \<open>F o G o F o G\<close> Adj.C.map \<open>\<epsilon>' o \<epsilon>\<close>
    proof -
      have "natural_transformation C C ((F o G) o (F o G)) Adj.C.map (\<epsilon>' o \<epsilon>)"
        using Adj.\<epsilon>.natural_transformation_axioms Adj'.\<epsilon>.natural_transformation_axioms
              horizontal_composite Adj.C.is_functor comp_functor_identity
        by (metis (no_types, lifting))
      thus "natural_transformation C C (F o G o F o G) Adj.C.map (\<epsilon>' o \<epsilon>)"
        using o_assoc by metis
    qed
    interpret \<epsilon>'\<epsilon>oF\<eta>G: vertical_composite
                         C C \<open>F o G\<close> \<open>F o G o F o G\<close> Adj.C.map \<open>F o \<eta> o G\<close> \<open>\<epsilon>' o \<epsilon>\<close> ..
    have "\<epsilon>' = vertical_composite.map C C (F o Adj.G\<epsilon>o\<eta>G.map) \<epsilon>'"
      using vcomp_ide_dom [of C C "F o G" Adj.C.map \<epsilon>'] Adj.triangle_G
      by (simp add: Adj'.\<epsilon>.natural_transformation_axioms)
    also have "... = vertical_composite.map C C
                       (vertical_composite.map C C (F o \<eta> o G) (F o G o \<epsilon>)) \<epsilon>'"
      using whisker_left Adj.F.functor_axioms Adj.G\<epsilon>.natural_transformation_axioms
            Adj.\<eta>G.natural_transformation_axioms o_assoc
      by (metis (no_types, lifting))
    also have "... = vertical_composite.map C C
                       (vertical_composite.map C C (F o \<eta> o G) (\<epsilon>' o F o G)) \<epsilon>"
    proof -
      have "vertical_composite.map C C
              (vertical_composite.map C C (F o \<eta> o G) (F o G o \<epsilon>)) \<epsilon>'
              = vertical_composite.map C C (F o \<eta> o G)
                  (vertical_composite.map C C (F o G o \<epsilon>) \<epsilon>')"
        using vcomp_assoc
        by (metis (no_types, lifting) Adj'.\<epsilon>.natural_transformation_axioms
            FG\<epsilon>.natural_transformation_axioms F\<eta>G.natural_transformation_axioms o_assoc)
      also have "... = vertical_composite.map C C (F o \<eta> o G)
                         (vertical_composite.map C C (\<epsilon>' o F o G) \<epsilon>)"
        using Adj'.\<epsilon>.natural_transformation_axioms Adj.\<epsilon>.natural_transformation_axioms
              interchange_spc [of C C "F o G" Adj.C.map \<epsilon> C "F o G" Adj.C.map \<epsilon>']
        by (metis hcomp_ide_cod hcomp_ide_dom o_assoc)
      also have "... = vertical_composite.map C C
                         (vertical_composite.map C C (F o \<eta> o G) (\<epsilon>' o F o G)) \<epsilon>"
        using vcomp_assoc
        by (metis Adj'.\<epsilon>F.natural_transformation_axioms
            Adj.G.as_nat_trans.natural_transformation_axioms
            Adj.\<epsilon>.natural_transformation_axioms F\<eta>G.natural_transformation_axioms
            horizontal_composite)
      finally show ?thesis by simp
    qed
    also have "... = vertical_composite.map C C
                       (vertical_composite.map D C (F o \<eta>) (\<epsilon>' o F) o G) \<epsilon>"
      using whisker_right Adj'.\<epsilon>F.natural_transformation_axioms
            Adj.F\<eta>.natural_transformation_axioms Adj.G.functor_axioms
      by metis
    also have "... = \<epsilon>"
      using Adj'.triangle_F vcomp_ide_cod Adj.\<epsilon>.natural_transformation_axioms by simp
    finally show ?thesis by simp
  qed

  lemma counit_determines_unit:
  assumes "unit_counit_adjunction C D F G \<eta> \<epsilon>"
  and "unit_counit_adjunction C D F G \<eta>' \<epsilon>"
  shows "\<eta> = \<eta>'"
  proof -
    interpret Adj: unit_counit_adjunction C D F G \<eta> \<epsilon> using assms(1) by auto
    interpret Adj': unit_counit_adjunction C D F G \<eta>' \<epsilon> using assms(2) by auto
    interpret GFGF: composite_functor D C D F \<open>G o F o G\<close> ..
    interpret GF\<eta>: natural_transformation D D \<open>G o F\<close> \<open>(G o F) o (G o F)\<close> \<open>(G o F) o \<eta>\<close>
      using Adj.\<eta>.natural_transformation_axioms Adj.GF.functor_axioms
            Adj.GF.as_nat_trans.natural_transformation_axioms comp_functor_identity
            horizontal_composite
      by (metis (no_types, lifting))
    interpret \<eta>'GF: natural_transformation D D \<open>G o F\<close> \<open>(G o F) o (G o F)\<close> \<open>\<eta>' o (G o F)\<close>
      using Adj'.\<eta>.natural_transformation_axioms Adj.GF.functor_axioms
            Adj.GF.as_nat_trans.natural_transformation_axioms comp_identity_functor
            horizontal_composite
      by (metis (no_types, lifting))
    interpret G\<epsilon>F: natural_transformation D D \<open>G o F o G o F\<close> \<open>G o F\<close> \<open>G o \<epsilon> o F\<close>
      using Adj.\<epsilon>.natural_transformation_axioms Adj.F.as_nat_trans.natural_transformation_axioms
            Adj.G\<epsilon>.natural_transformation_axioms horizontal_composite
      by blast
    interpret \<eta>'\<eta>: natural_transformation D D Adj.D.map \<open>G o F o G o F\<close> \<open>\<eta>' o \<eta>\<close>
    proof -
      have "natural_transformation D D Adj.D.map ((G o F) o (G o F)) (\<eta>' o \<eta>)"
        using Adj'.\<eta>.natural_transformation_axioms Adj.D.identity_functor_axioms
              Adj.\<eta>.natural_transformation_axioms horizontal_composite identity_functor.is_functor
        by fastforce
      thus "natural_transformation D D Adj.D.map (G o F o G o F) (\<eta>' o \<eta>)"
        using o_assoc by metis
    qed
    interpret G\<epsilon>Fo\<eta>'\<eta>: vertical_composite
                         D D Adj.D.map \<open>G o F o G o F\<close> \<open>G o F\<close> \<open>\<eta>' o \<eta>\<close> \<open>G o \<epsilon> o F\<close> ..
    have "\<eta>' = vertical_composite.map D D \<eta>' (G o Adj.\<epsilon>FoF\<eta>.map)"
      using vcomp_ide_cod [of D D  Adj.D.map "G o F" \<eta>'] Adj.triangle_F
      by (simp add: Adj'.\<eta>.natural_transformation_axioms)
    also have "... = vertical_composite.map D D \<eta>'
                       (vertical_composite.map D D (G o (F o \<eta>)) (G o (\<epsilon> o F)))"
      using whisker_left Adj.F\<eta>.natural_transformation_axioms Adj.G.functor_axioms
            Adj.\<epsilon>F.natural_transformation_axioms
      by fastforce
    also have "... = vertical_composite.map D D
                       (vertical_composite.map D D \<eta>' (G o (F o \<eta>))) (G o \<epsilon> o F)"
      using vcomp_assoc Adj'.\<eta>.natural_transformation_axioms
            GF\<eta>.natural_transformation_axioms G\<epsilon>F.natural_transformation_axioms o_assoc
      by (metis (no_types, lifting))
    also have "... = vertical_composite.map D D
                       (vertical_composite.map D D \<eta> (\<eta>' o G o F)) (G o \<epsilon> o F)"
        using interchange_spc [of D D Adj.D.map "G o F" \<eta> D Adj.D.map "G o F" \<eta>']
              Adj.\<eta>.natural_transformation_axioms Adj'.\<eta>.natural_transformation_axioms
        by (metis hcomp_ide_cod hcomp_ide_dom o_assoc)
    also have "... = vertical_composite.map D D \<eta>
                       (vertical_composite.map D D (\<eta>' o G o F) (G o \<epsilon> o F))"
      using vcomp_assoc
      by (metis (no_types, lifting) Adj.\<eta>.natural_transformation_axioms
          G\<epsilon>F.natural_transformation_axioms \<eta>'GF.natural_transformation_axioms o_assoc)
    also have "... = vertical_composite.map D D \<eta>
                       (vertical_composite.map C D (\<eta>' o G) (G o \<epsilon>) o F)"
      using whisker_right Adj'.\<eta>G.natural_transformation_axioms Adj.F.functor_axioms
            Adj.G\<epsilon>.natural_transformation_axioms
      by fastforce
    also have "... = \<eta>"
      using Adj'.triangle_G vcomp_ide_dom Adj.GF.functor_axioms
            Adj.\<eta>.natural_transformation_axioms
      by simp
    finally show ?thesis by simp
  qed

  subsection "Adjunction"

  text\<open>
    The grand unification of everything to do with an adjunction.
\<close>

  locale adjunction =
    C: category C +
    D: category D +
    S: set_category S setp +
    Cop: dual_category C +
    Dop: dual_category D +
    CopxC: product_category Cop.comp C +
    DopxD: product_category Dop.comp D +
    DopxC: product_category Dop.comp C +
    idDop: identity_functor Dop.comp +
    HomC: hom_functor C S setp \<phi>C +
    HomD: hom_functor D S setp \<phi>D +
    F: left_adjoint_functor D C F +
    G: right_adjoint_functor C D G +
    GF: composite_functor D C D F G +
    FG: composite_functor C D C G F +
    FGF: composite_functor D C C F FG.map +
    GFG: composite_functor C D D G GF.map +
    Fop: dual_functor Dop.comp Cop.comp F +
    FopxC: product_functor Dop.comp C Cop.comp C Fop.map C.map +
    DopxG: product_functor Dop.comp C Dop.comp D Dop.map G +
    Hom_FopxC: composite_functor DopxC.comp CopxC.comp S FopxC.map HomC.map +
    Hom_DopxG: composite_functor DopxC.comp DopxD.comp S DopxG.map HomD.map +
    Hom_FopxC: set_valued_functor DopxC.comp S setp Hom_FopxC.map +
    Hom_DopxG: set_valued_functor DopxC.comp S setp Hom_DopxG.map +
    \<eta>: natural_transformation D D D.map GF.map \<eta> +
    \<epsilon>: natural_transformation C C FG.map C.map \<epsilon> +
    F\<eta>: natural_transformation D C F \<open>F o G o F\<close> \<open>F o \<eta>\<close> +
    \<eta>G: natural_transformation C D G \<open>G o F o G\<close> \<open>\<eta> o G\<close> +
    \<epsilon>F: natural_transformation D C \<open>F o G o F\<close> F \<open>\<epsilon> o F\<close> +
    G\<epsilon>: natural_transformation C D \<open>G o F o G\<close> G \<open>G o \<epsilon>\<close> +
    \<epsilon>FoF\<eta>: vertical_composite D C F FGF.map F \<open>F o \<eta>\<close> \<open>\<epsilon> o F\<close> +
    G\<epsilon>o\<eta>G: vertical_composite C D G GFG.map G \<open>\<eta> o G\<close> \<open>G o \<epsilon>\<close> +
    \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi> +
    \<eta>\<epsilon>: unit_counit_adjunction C D F G \<eta> \<epsilon> +
    \<Phi>\<Psi>: hom_adjunction C D S setp \<phi>C \<phi>D F G \<Phi> \<Psi>
    for C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    and D :: "'d comp"     (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    and S :: "'s comp"     (infixr \<open>\<cdot>\<^sub>S\<close> 55)
    and setp :: "'s set \<Rightarrow> bool"
    and \<phi>C :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
    and \<phi>D :: "'d * 'd \<Rightarrow> 'd \<Rightarrow> 's"
    and F :: "'d \<Rightarrow> 'c"
    and G :: "'c \<Rightarrow> 'd"
    and \<phi> :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    and \<psi> :: "'c \<Rightarrow> 'd \<Rightarrow> 'c"
    and \<eta> :: "'d \<Rightarrow> 'd"
    and \<epsilon> :: "'c \<Rightarrow> 'c"
    and \<Phi> :: "'d * 'c \<Rightarrow> 's"
    and \<Psi> :: "'d * 'c \<Rightarrow> 's" +
    assumes \<phi>_in_terms_of_\<eta>: "\<lbrakk> D.ide y; \<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright> \<rbrakk> \<Longrightarrow> \<phi> y f = G f \<cdot>\<^sub>D \<eta> y"
    and \<psi>_in_terms_of_\<epsilon>: "\<lbrakk> C.ide x; \<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright> \<rbrakk> \<Longrightarrow> \<psi> x g = \<epsilon> x \<cdot>\<^sub>C F g"
    and \<eta>_in_terms_of_\<phi>: "D.ide y \<Longrightarrow> \<eta> y = \<phi> y (F y)"
    and \<epsilon>_in_terms_of_\<psi>: "C.ide x \<Longrightarrow> \<epsilon> x = \<psi> x (G x)"
    and \<phi>_in_terms_of_\<Phi>: "\<lbrakk> D.ide y; \<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright> \<rbrakk> \<Longrightarrow>
                              \<phi> y f = (\<Phi>\<Psi>.\<psi>D (y, G x) o S.Fun (\<Phi> (y, x)) o \<phi>C (F y, x)) f"
    and \<psi>_in_terms_of_\<Psi>: "\<lbrakk> C.ide x; \<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright> \<rbrakk> \<Longrightarrow>
                              \<psi> x g = (\<Phi>\<Psi>.\<psi>C (F y, x) o S.Fun (\<Psi> (y, x)) o \<phi>D (y, G x)) g"
    and \<Phi>_in_terms_of_\<phi>:
           "\<lbrakk> C.ide x; D.ide y \<rbrakk> \<Longrightarrow>
                \<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                    (\<phi>D (y, G x) o \<phi> y o \<Phi>\<Psi>.\<psi>C (F y, x))"
    and \<Psi>_in_terms_of_\<psi>:
           "\<lbrakk> C.ide x; D.ide y \<rbrakk> \<Longrightarrow>
                \<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                    (\<phi>C (F y, x) o \<psi> x o \<Phi>\<Psi>.\<psi>D (y, G x))"

  section "Meta-Adjunctions Induce Unit/Counit Adjunctions"

  context meta_adjunction
  begin

    interpretation GF: composite_functor D C D F G ..
    interpretation FG: composite_functor C D C G F ..
    interpretation FGF: composite_functor D C C F FG.map ..
    interpretation GFG: composite_functor C D D G GF.map ..

    definition \<eta>o :: "'d \<Rightarrow> 'd"
    where "\<eta>o y = \<phi> y (F y)"

    lemma \<eta>o_in_hom:
    assumes "D.ide y"
    shows "\<guillemotleft>\<eta>o y : y \<rightarrow>\<^sub>D G (F y)\<guillemotright>"
      using assms D.ide_in_hom \<eta>o_def \<phi>_in_hom by force

    lemma \<phi>_in_terms_of_\<eta>o:
    assumes "D.ide y" and "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<phi> y f = G f \<cdot>\<^sub>D \<eta>o y"
    proof (unfold \<eta>o_def)
      have 1: "\<guillemotleft>F y : F y \<rightarrow>\<^sub>C F y\<guillemotright>"
        using assms(1) D.ide_in_hom by blast
      hence "\<phi> y (F y) = \<phi> y (F y) \<cdot>\<^sub>D y"
        by (metis assms(1) D.in_homE \<phi>_in_hom D.comp_arr_dom)
      thus "\<phi> y f = G f \<cdot>\<^sub>D \<phi> y (F y)"
        using assms 1 D.ide_in_hom by (metis C.comp_arr_dom C.in_homE \<phi>_naturality)
    qed

    lemma \<phi>_F_char:
    assumes "\<guillemotleft>g : y' \<rightarrow>\<^sub>D y\<guillemotright>"
    shows "\<phi> y' (F g) = \<eta>o y \<cdot>\<^sub>D g"
      using assms \<eta>o_def \<phi>_in_hom [of y "F y" "F y"]
            D.comp_cod_arr [of "D (\<phi> y (F y)) g" "G (F y)"]
            \<phi>_naturality [of "F y" "F y" "F y" g y' y "F y"]
      by (metis C.ide_in_hom D.arr_cod_iff_arr D.arr_dom D.cod_cod D.cod_dom D.comp_ide_arr
          D.comp_ide_self D.ide_cod D.in_homE F.as_nat_trans.naturality2 F.functor_axioms
          F.preserves_section_retraction \<phi>_in_hom functor.preserves_hom)

    interpretation \<eta>: transformation_by_components D D D.map GF.map \<eta>o
    proof
      show "\<And>a. D.ide a \<Longrightarrow> \<guillemotleft>\<eta>o a : D.map a \<rightarrow>\<^sub>D GF.map a\<guillemotright>"
        using \<eta>o_def \<phi>_in_hom D.ide_in_hom by force
      fix f
      assume f: "D.arr f"
      show "\<eta>o (D.cod f) \<cdot>\<^sub>D D.map f = GF.map f \<cdot>\<^sub>D \<eta>o (D.dom f)"
        using f \<phi>_F_char [of "D.map f" "D.dom f" "D.cod f"]
              \<phi>_in_terms_of_\<eta>o [of "D.dom f" "F f" "F (D.cod f)"]
        by force
    qed

    lemma \<eta>_map_simp:
    assumes "D.ide y"
    shows "\<eta>.map y = \<phi> y (F y)"
      using assms \<eta>.map_simp_ide \<eta>o_def by simp

    definition \<epsilon>o :: "'c \<Rightarrow> 'c"
    where "\<epsilon>o x = \<psi> x (G x)"

    lemma \<epsilon>o_in_hom:
    assumes "C.ide x"
    shows "\<guillemotleft>\<epsilon>o x : F (G x) \<rightarrow>\<^sub>C x\<guillemotright>"
      using assms C.ide_in_hom \<epsilon>o_def \<psi>_in_hom by force

    lemma \<psi>_in_terms_of_\<epsilon>o:
    assumes "C.ide x" and "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "\<psi> x g = \<epsilon>o x \<cdot>\<^sub>C F g"
    proof -
      have "\<epsilon>o x \<cdot>\<^sub>C F g = x \<cdot>\<^sub>C \<psi> x (G x) \<cdot>\<^sub>C F g"
        using assms \<epsilon>o_def \<psi>_in_hom [of x "G x" "G x"]
              C.comp_cod_arr [of "\<psi> x (G x) \<cdot>\<^sub>C F g" x]
        by fastforce
      also have "... = \<psi> x (G x \<cdot>\<^sub>D G x \<cdot>\<^sub>D g)"
        using assms \<psi>_naturality [of x x x g y "G x" "G x"] by force
      also have "... = \<psi> x g"
        using assms D.comp_cod_arr by fastforce
      finally show ?thesis by simp
    qed

    lemma \<psi>_G_char:
    assumes "\<guillemotleft>f: x \<rightarrow>\<^sub>C x'\<guillemotright>"
    shows "\<psi> x' (G f) = f \<cdot>\<^sub>C \<epsilon>o x"
    proof (unfold \<epsilon>o_def)
      have 0: "C.ide x \<and> C.ide x'" using assms by auto
      thus "\<psi> x' (G f) = f \<cdot>\<^sub>C \<psi> x (G x)"
        using 0 assms \<psi>_naturality \<psi>_in_hom [of x "G x" "G x"] G.preserves_hom \<epsilon>o_def
              \<psi>_in_terms_of_\<epsilon>o G.as_nat_trans.naturality1 C.ide_in_hom
        by (metis C.arrI C.in_homE)
    qed

    interpretation \<epsilon>: transformation_by_components C C FG.map C.map \<epsilon>o
      apply unfold_locales
      using \<epsilon>o_in_hom
       apply simp
      using \<psi>_G_char \<psi>_in_terms_of_\<epsilon>o
      by (metis C.arr_iff_in_hom C.ide_cod C.map_simp G.preserves_hom comp_apply)

    lemma \<epsilon>_map_simp:
    assumes "C.ide x"
    shows "\<epsilon>.map x = \<psi> x (G x)"
      using assms \<epsilon>o_def by simp

    interpretation FD: composite_functor D D C D.map F ..
    interpretation CF: composite_functor D C C F C.map ..
    interpretation GC: composite_functor C C D C.map G ..
    interpretation DG: composite_functor C D D G D.map ..

    interpretation F\<eta>: natural_transformation D C F \<open>F o G o F\<close> \<open>F o \<eta>.map\<close>
      by (metis (no_types, lifting) F.as_nat_trans.natural_transformation_axioms
          F.functor_axioms \<eta>.natural_transformation_axioms comp_functor_identity
          horizontal_composite o_assoc)

    interpretation \<epsilon>F: natural_transformation D C \<open>F o G o F\<close> F \<open>\<epsilon>.map o F\<close>
      using \<epsilon>.natural_transformation_axioms F.as_nat_trans.natural_transformation_axioms
            horizontal_composite
      by fastforce

    interpretation \<eta>G: natural_transformation C D G \<open>G o F o G\<close> \<open>\<eta>.map o G\<close>
      using \<eta>.natural_transformation_axioms G.as_nat_trans.natural_transformation_axioms
            horizontal_composite
      by fastforce

    interpretation G\<epsilon>: natural_transformation C D \<open>G o F o G\<close> G \<open>G o \<epsilon>.map\<close>
      by (metis (no_types, lifting) G.as_nat_trans.natural_transformation_axioms
          G.functor_axioms \<epsilon>.natural_transformation_axioms comp_functor_identity
          horizontal_composite o_assoc)

    interpretation \<epsilon>FoF\<eta>: vertical_composite D C F \<open>F o G o F\<close> F \<open>F o \<eta>.map\<close> \<open>\<epsilon>.map o F\<close>
      ..
    interpretation G\<epsilon>o\<eta>G: vertical_composite C D G \<open>G o F o G\<close> G \<open>\<eta>.map o G\<close> \<open>G o \<epsilon>.map\<close>
      ..

    lemma unit_counit_F:
    assumes "D.ide y"
    shows "F y = \<epsilon>o (F y) \<cdot>\<^sub>C F (\<eta>o y)"
      using assms \<psi>_in_terms_of_\<epsilon>o \<eta>o_def \<psi>_\<phi> \<eta>o_in_hom F.preserves_ide C.ide_in_hom by metis

    lemma unit_counit_G:
    assumes "C.ide x"
    shows "G x = G (\<epsilon>o x) \<cdot>\<^sub>D \<eta>o (G x)"
      using assms \<phi>_in_terms_of_\<eta>o \<epsilon>o_def \<phi>_\<psi> \<epsilon>o_in_hom G.preserves_ide D.ide_in_hom by metis

    lemma induces_unit_counit_adjunction':
    shows "unit_counit_adjunction C D F G \<eta>.map \<epsilon>.map"
    proof
      show "\<epsilon>FoF\<eta>.map = F"
        using \<epsilon>FoF\<eta>.is_natural_transformation \<epsilon>FoF\<eta>.map_simp_ide unit_counit_F
              F.as_nat_trans.natural_transformation_axioms
        by (intro natural_transformation_eqI) auto
      show "G\<epsilon>o\<eta>G.map = G"
        using G\<epsilon>o\<eta>G.is_natural_transformation G\<epsilon>o\<eta>G.map_simp_ide unit_counit_G
              G.as_nat_trans.natural_transformation_axioms
        by (intro natural_transformation_eqI) auto
    qed

    definition \<eta> :: "'d \<Rightarrow> 'd" where "\<eta> \<equiv> \<eta>.map"
    definition \<epsilon> :: "'c \<Rightarrow> 'c" where "\<epsilon> \<equiv> \<epsilon>.map"

    theorem induces_unit_counit_adjunction:
    shows "unit_counit_adjunction C D F G \<eta> \<epsilon>"
      unfolding \<eta>_def \<epsilon>_def
      using induces_unit_counit_adjunction' by simp

    lemma \<eta>_naturalitytransformation:
    shows "natural_transformation D D D.map GF.map \<eta>"
      unfolding \<eta>_def ..

    lemma \<epsilon>_naturalitytransformation:
    shows "natural_transformation C C FG.map C.map \<epsilon>"
      unfolding \<epsilon>_def ..

    text\<open>
      From the defined @{term \<eta>} and @{term \<epsilon>} we can recover the original @{term \<phi>} and @{term \<psi>}.
\<close>

    lemma \<phi>_in_terms_of_\<eta>:
    assumes "D.ide y" and "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<phi> y f = G f \<cdot>\<^sub>D \<eta> y"
      using assms \<eta>_def by (simp add: \<phi>_in_terms_of_\<eta>o)

    lemma \<psi>_in_terms_of_\<epsilon>:
    assumes "C.ide x" and "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "\<psi> x g = \<epsilon> x \<cdot>\<^sub>C F g"
      using assms \<epsilon>_def by (simp add: \<psi>_in_terms_of_\<epsilon>o)

  end

  section "Meta-Adjunctions Induce Left and Right Adjoint Functors"

  context meta_adjunction
  begin

    interpretation unit_counit_adjunction C D F G \<eta> \<epsilon>
      using induces_unit_counit_adjunction \<eta>_def \<epsilon>_def by auto

    lemma has_terminal_arrows_from_functor:
    assumes x: "C.ide x"
    shows "terminal_arrow_from_functor D C F (G x) x (\<epsilon> x)"
    and "\<And>y' f. arrow_from_functor D C F y' x f
                   \<Longrightarrow> terminal_arrow_from_functor.the_coext D C F (G x) (\<epsilon> x) y' f = \<phi> y' f"
    proof -
      interpret \<epsilon>x: arrow_from_functor D C F \<open>G x\<close> x \<open>\<epsilon> x\<close>
        using x \<epsilon>.preserves_hom G.preserves_ide by unfold_locales auto
      have 1: "\<And>y' f. arrow_from_functor D C F y' x f \<Longrightarrow>
                      \<epsilon>x.is_coext y' f (\<phi> y' f) \<and> (\<forall>g'. \<epsilon>x.is_coext y' f g' \<longrightarrow> g' = \<phi> y' f)"
        using x
        by (metis (full_types) \<epsilon>x.is_coext_def \<phi>_\<psi> \<psi>_in_terms_of_\<epsilon> arrow_from_functor.arrow
            \<phi>_in_hom \<psi>_\<phi>)
      interpret \<epsilon>x: terminal_arrow_from_functor D C F \<open>G x\<close> x \<open>\<epsilon> x\<close>
        using 1 by unfold_locales blast
      show "terminal_arrow_from_functor D C F (G x) x (\<epsilon> x)" ..
      show "\<And>y' f. arrow_from_functor D C F y' x f \<Longrightarrow> \<epsilon>x.the_coext y' f = \<phi> y' f"
        using 1 \<epsilon>x.the_coext_def by auto
    qed

    lemma has_left_adjoint_functor:
    shows "left_adjoint_functor D C F"
      apply unfold_locales using has_terminal_arrows_from_functor by auto

    lemma has_initial_arrows_to_functor:
    assumes y: "D.ide y"
    shows "initial_arrow_to_functor C D G y (F y) (\<eta> y)"
    and "\<And>x' g. arrow_to_functor C D G y x' g \<Longrightarrow>
                  initial_arrow_to_functor.the_ext C D G (F y) (\<eta> y) x' g = \<psi> x' g"
    proof -
      interpret \<eta>y: arrow_to_functor C D G y \<open>F y\<close> \<open>\<eta> y\<close>
        using y by unfold_locales auto
      have 1: "\<And>x' g. arrow_to_functor C D G y x' g \<Longrightarrow>
                         \<eta>y.is_ext x' g (\<psi> x' g) \<and> (\<forall>f'. \<eta>y.is_ext x' g f' \<longrightarrow> f' = \<psi> x' g)"
        using y
        by (metis (full_types) \<eta>y.is_ext_def \<psi>_\<phi> \<phi>_in_terms_of_\<eta> arrow_to_functor.arrow
            \<psi>_in_hom \<phi>_\<psi>)
      interpret \<eta>y: initial_arrow_to_functor C D G y \<open>F y\<close> \<open>\<eta> y\<close>
        apply unfold_locales using 1 by blast
      show "initial_arrow_to_functor C D G y (F y) (\<eta> y)" ..
      show "\<And>x' g. arrow_to_functor C D G y x' g \<Longrightarrow> \<eta>y.the_ext x' g = \<psi> x' g"
        using 1 \<eta>y.the_ext_def by auto
    qed

    lemma has_right_adjoint_functor:
    shows "right_adjoint_functor C D G"
      apply unfold_locales using has_initial_arrows_to_functor by auto

  end

  section "Unit/Counit Adjunctions Induce Meta-Adjunctions"

  context unit_counit_adjunction
  begin

    definition \<phi> :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    where "\<phi> y h = G h \<cdot>\<^sub>D \<eta> y"

    definition \<psi> :: "'c \<Rightarrow> 'd \<Rightarrow> 'c"
    where "\<psi> x h = \<epsilon> x \<cdot>\<^sub>C F h"

    interpretation meta_adjunction C D F G \<phi> \<psi>
    proof
      fix x :: 'c and y :: 'd and f :: 'c
      assume y: "D.ide y" and f: "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
      show 0: "\<guillemotleft>\<phi> y f : y \<rightarrow>\<^sub>D G x\<guillemotright>"
        using f y G.preserves_hom \<eta>.preserves_hom \<phi>_def D.ide_in_hom by auto
      show "\<psi> x (\<phi> y f) = f"
      proof -
        have "\<psi> x (\<phi> y f) = (\<epsilon> x \<cdot>\<^sub>C F (G f)) \<cdot>\<^sub>C F (\<eta> y)"
          using y f \<phi>_def \<psi>_def C.comp_assoc by auto
        also have "... = (f \<cdot>\<^sub>C \<epsilon> (F y)) \<cdot>\<^sub>C F (\<eta> y)"
          using y f \<epsilon>.naturality by auto
        also have "... = f"
          using y f \<epsilon>FoF\<eta>.map_simp_2 triangle_F C.comp_arr_dom D.ide_in_hom C.comp_assoc
          by fastforce
        finally show ?thesis by auto
      qed
      next
      fix x :: 'c and y :: 'd and g :: 'd
      assume x: "C.ide x" and g: "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
      show "\<guillemotleft>\<psi> x g : F y \<rightarrow>\<^sub>C x\<guillemotright>" using g x \<psi>_def by fastforce
      show "\<phi> y (\<psi> x g) = g"
      proof -
        have "\<phi> y (\<psi> x g) = (G (\<epsilon> x) \<cdot>\<^sub>D \<eta> (G x)) \<cdot>\<^sub>D g"
          using g x \<phi>_def \<psi>_def \<eta>.naturality [of g] D.comp_assoc by auto
        also have "... = g"
          using x g triangle_G D.comp_ide_arr G\<epsilon>o\<eta>G.map_simp_ide by auto
        finally show ?thesis by auto
      qed
      next
      fix f :: 'c and g :: 'd and h :: 'c and x :: 'c and x' :: 'c and y :: 'd and y' :: 'd
      assume f: "\<guillemotleft>f : x \<rightarrow>\<^sub>C x'\<guillemotright>" and g: "\<guillemotleft>g : y' \<rightarrow>\<^sub>D y\<guillemotright>" and h: "\<guillemotleft>h : F y \<rightarrow>\<^sub>C x\<guillemotright>"
      show "\<phi> y' (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) = G f \<cdot>\<^sub>D \<phi> y h \<cdot>\<^sub>D g"
        using \<phi>_def f g h \<eta>.naturality D.comp_assoc by fastforce
    qed

    theorem induces_meta_adjunction:
    shows "meta_adjunction C D F G \<phi> \<psi>" ..

    text\<open>
      From the defined @{term \<phi>} and @{term \<psi>} we can recover the original @{term \<eta>} and @{term \<epsilon>}.
\<close>

    lemma \<eta>_in_terms_of_\<phi>:
    assumes "D.ide y"
    shows "\<eta> y = \<phi> y (F y)"
      using assms \<phi>_def D.comp_cod_arr by auto

    lemma \<epsilon>_in_terms_of_\<psi>:
    assumes "C.ide x"
    shows "\<epsilon> x = \<psi> x (G x)"
      using assms \<psi>_def C.comp_arr_dom by auto

  end

  section "Left and Right Adjoint Functors Induce Meta-Adjunctions"

  text\<open>
    A left adjoint functor induces a meta-adjunction, modulo the choice of a
    right adjoint and counit.
\<close>

  context left_adjoint_functor
  begin

    definition Go :: "'c \<Rightarrow> 'd"
    where "Go a = (SOME b. \<exists>e. terminal_arrow_from_functor D C F b a e)"

    definition \<epsilon>o :: "'c \<Rightarrow> 'c"
    where "\<epsilon>o a = (SOME e. terminal_arrow_from_functor D C F (Go a) a e)"

    lemma Go_\<epsilon>o_terminal:
    assumes "\<exists>b e. terminal_arrow_from_functor D C F b a e"
    shows "terminal_arrow_from_functor D C F (Go a) a (\<epsilon>o a)"
      using assms Go_def \<epsilon>o_def
            someI_ex [of "\<lambda>b. \<exists>e. terminal_arrow_from_functor D C F b a e"]
            someI_ex [of "\<lambda>e. terminal_arrow_from_functor D C F (Go a) a e"]
      by simp

    text\<open>
      The right adjoint @{term G} to @{term F} takes each arrow @{term f} of
      @{term[source=true] C} to the unique @{term[source=true] D}-coextension of
      @{term "C f (\<epsilon>o (C.dom f))"} along @{term "\<epsilon>o (C.cod f)"}.
\<close>

    definition G :: "'c \<Rightarrow> 'd"
    where "G f = (if C.arr f then
                     terminal_arrow_from_functor.the_coext D C F (Go (C.cod f)) (\<epsilon>o (C.cod f))
                                  (Go (C.dom f)) (f \<cdot>\<^sub>C \<epsilon>o (C.dom f))
                  else D.null)"

    lemma G_ide:
    assumes "C.ide x"
    shows "G x = Go x"
    proof -
      interpret terminal_arrow_from_functor D C F \<open>Go x\<close> x \<open>\<epsilon>o x\<close>
        using assms ex_terminal_arrow Go_\<epsilon>o_terminal by blast
      have 1: "arrow_from_functor D C F (Go x) x (\<epsilon>o x)" ..
      have "is_coext (Go x) (\<epsilon>o x) (Go x)"
        using arrow is_coext_def C.in_homE C.comp_arr_dom by auto
      hence "Go x = the_coext (Go x) (\<epsilon>o x)" using 1 the_coext_unique by blast
      moreover have "\<epsilon>o x = C x (\<epsilon>o (C.dom x))"
        using assms arrow C.comp_ide_arr C.seqI' C.ide_in_hom C.in_homE by metis
      ultimately show ?thesis using assms G_def C.cod_dom C.ide_in_hom C.in_homE by metis
    qed

    lemma G_is_functor:
    shows "functor C D G"
    proof
      fix f :: 'c
      assume "\<not>C.arr f"
      thus "G f = D.null" using G_def by auto
      next
      fix f :: 'c
      assume f: "C.arr f"
      let ?x = "C.dom f"
      let ?x' = "C.cod f"
      interpret x\<epsilon>: terminal_arrow_from_functor D C F \<open>Go ?x\<close> \<open>?x\<close> \<open>\<epsilon>o ?x\<close>
        using f ex_terminal_arrow Go_\<epsilon>o_terminal by simp
      interpret x'\<epsilon>: terminal_arrow_from_functor D C F \<open>Go ?x'\<close> \<open>?x'\<close> \<open>\<epsilon>o ?x'\<close>
        using f ex_terminal_arrow Go_\<epsilon>o_terminal by simp
      have 1: "arrow_from_functor D C F (Go ?x) ?x' (C f (\<epsilon>o ?x))"
        using f x\<epsilon>.arrow by (unfold_locales, auto)
      have "G f = x'\<epsilon>.the_coext (Go ?x) (C f (\<epsilon>o ?x))" using f G_def by simp
      hence Gf: "\<guillemotleft>G f : Go ?x \<rightarrow>\<^sub>D Go ?x'\<guillemotright> \<and> f \<cdot>\<^sub>C \<epsilon>o ?x = \<epsilon>o ?x' \<cdot>\<^sub>C F (G f)"
        using 1 x'\<epsilon>.the_coext_prop by simp
      show "D.arr (G f)" using Gf by auto
      show "D.dom (G f) = G ?x" using f Gf G_ide by auto
      show "D.cod (G f) = G ?x'" using f Gf G_ide by auto
      next
      fix f f' :: 'c
      assume ff': "C.arr (C f' f)"
      have f: "C.arr f" using ff' by auto
      let ?x = "C.dom f"
      let ?x' = "C.cod f"
      let ?x'' = "C.cod f'"
      interpret x\<epsilon>: terminal_arrow_from_functor D C F \<open>Go ?x\<close> \<open>?x\<close> \<open>\<epsilon>o ?x\<close>
        using f ex_terminal_arrow Go_\<epsilon>o_terminal by simp
      interpret x'\<epsilon>: terminal_arrow_from_functor D C F \<open>Go ?x'\<close> \<open>?x'\<close> \<open>\<epsilon>o ?x'\<close>
        using f ex_terminal_arrow Go_\<epsilon>o_terminal by simp
      interpret x''\<epsilon>: terminal_arrow_from_functor D C F \<open>Go ?x''\<close> \<open>?x''\<close> \<open>\<epsilon>o ?x''\<close>
        using ff' ex_terminal_arrow Go_\<epsilon>o_terminal by auto
      have 1: "arrow_from_functor D C F (Go ?x) ?x' (f \<cdot>\<^sub>C \<epsilon>o ?x)"
         using f x\<epsilon>.arrow by (unfold_locales, auto)
      have 2: "arrow_from_functor D C F (Go ?x') ?x'' (f' \<cdot>\<^sub>C \<epsilon>o ?x')"
         using ff' x'\<epsilon>.arrow by (unfold_locales, auto)
      have "G f = x'\<epsilon>.the_coext (Go ?x) (C f (\<epsilon>o ?x))"
        using f G_def by simp
      hence Gf: "D.in_hom (G f) (Go ?x) (Go ?x') \<and> f \<cdot>\<^sub>C \<epsilon>o ?x = \<epsilon>o ?x' \<cdot>\<^sub>C F (G f)"
        using 1 x'\<epsilon>.the_coext_prop by simp
      have "G f' = x''\<epsilon>.the_coext (Go ?x') (f' \<cdot>\<^sub>C \<epsilon>o ?x')"
        using ff' G_def by auto
      hence Gf': "\<guillemotleft>G f' : Go (C.cod f) \<rightarrow>\<^sub>D Go (C.cod f')\<guillemotright> \<and> f' \<cdot>\<^sub>C \<epsilon>o ?x' = \<epsilon>o ?x'' \<cdot>\<^sub>C F (G f')"
        using 2 x''\<epsilon>.the_coext_prop by simp
      show "G (f' \<cdot>\<^sub>C f) = G f' \<cdot>\<^sub>D G f"
      proof -
        have "x''\<epsilon>.is_coext (Go ?x) ((f' \<cdot>\<^sub>C f) \<cdot>\<^sub>C \<epsilon>o ?x) (G f' \<cdot>\<^sub>D G f)"
        proof -
          have 3: "\<guillemotleft>G f' \<cdot>\<^sub>D G f : Go (C.dom f) \<rightarrow>\<^sub>D Go (C.cod f')\<guillemotright>" using 1 2 Gf Gf' by auto
          moreover have "(f' \<cdot>\<^sub>C f) \<cdot>\<^sub>C \<epsilon>o ?x = \<epsilon>o ?x'' \<cdot>\<^sub>C F (G f' \<cdot>\<^sub>D G f)"
            by (metis 3 C.comp_assoc D.in_homE Gf Gf' preserves_comp)
          ultimately show ?thesis using x''\<epsilon>.is_coext_def by auto
        qed
        moreover have "arrow_from_functor D C F (Go ?x) ?x'' ((f' \<cdot>\<^sub>C f) \<cdot>\<^sub>C \<epsilon>o ?x)"
           using ff' x\<epsilon>.arrow by unfold_locales blast
        ultimately show ?thesis
          using ff' G_def x''\<epsilon>.the_coext_unique C.seqE C.cod_comp C.dom_comp by auto
      qed
    qed

    interpretation G: "functor" C D G using G_is_functor by auto

    lemma G_simp:
    assumes "C.arr f"
    shows "G f = terminal_arrow_from_functor.the_coext D C F (Go (C.cod f)) (\<epsilon>o (C.cod f))
                                                             (Go (C.dom f)) (f \<cdot>\<^sub>C \<epsilon>o (C.dom f))"
      using assms G_def by simp

    interpretation idC: identity_functor C ..
    interpretation GF: composite_functor C D C G F ..

    interpretation \<epsilon>: transformation_by_components C C GF.map C.map \<epsilon>o
    proof
      fix x :: 'c
      assume x: "C.ide x"
      show "\<guillemotleft>\<epsilon>o x : GF.map x \<rightarrow>\<^sub>C C.map x\<guillemotright>"
      proof -
        interpret terminal_arrow_from_functor D C F \<open>Go x\<close> x \<open>\<epsilon>o x\<close>
          using x Go_\<epsilon>o_terminal ex_terminal_arrow by simp
        show ?thesis using x G_ide arrow by auto
      qed
      next
      fix f :: 'c
      assume f: "C.arr f"
      show "\<epsilon>o (C.cod f) \<cdot>\<^sub>C GF.map f = C.map f \<cdot>\<^sub>C \<epsilon>o (C.dom f)"
      proof -
        let ?x = "C.dom f"
        let ?x' = "C.cod f"
        interpret x\<epsilon>: terminal_arrow_from_functor D C F \<open>Go ?x\<close> ?x \<open>\<epsilon>o ?x\<close>
          using f Go_\<epsilon>o_terminal ex_terminal_arrow by simp
        interpret x'\<epsilon>: terminal_arrow_from_functor D C F \<open>Go ?x'\<close> ?x' \<open>\<epsilon>o ?x'\<close>
          using f Go_\<epsilon>o_terminal ex_terminal_arrow by simp
        have 1: "arrow_from_functor D C F (Go ?x) ?x' (C f (\<epsilon>o ?x))"
           using f x\<epsilon>.arrow by unfold_locales auto
        have "G f = x'\<epsilon>.the_coext (Go ?x) (f \<cdot>\<^sub>C \<epsilon>o ?x)"
          using f G_simp by blast
        hence "x'\<epsilon>.is_coext (Go ?x) (f \<cdot>\<^sub>C \<epsilon>o ?x) (G f)"
          using 1 x'\<epsilon>.the_coext_prop x'\<epsilon>.is_coext_def by auto
        thus ?thesis
          using f x'\<epsilon>.is_coext_def by simp
      qed
    qed

    definition \<psi>
    where "\<psi> x h = C (\<epsilon>.map x) (F h)"

    lemma \<psi>_in_hom:
    assumes "C.ide x" and "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "\<guillemotleft>\<psi> x g : F y \<rightarrow>\<^sub>C x\<guillemotright>"
      unfolding \<psi>_def using assms \<epsilon>.maps_ide_in_hom by auto

    lemma \<psi>_natural:
    assumes f: "\<guillemotleft>f : x \<rightarrow>\<^sub>C x'\<guillemotright>" and g: "\<guillemotleft>g : y' \<rightarrow>\<^sub>D y\<guillemotright>" and h: "\<guillemotleft>h : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "f \<cdot>\<^sub>C \<psi> x h \<cdot>\<^sub>C F g = \<psi> x' ((G f \<cdot>\<^sub>D h) \<cdot>\<^sub>D g)"
    proof -
      have "f \<cdot>\<^sub>C \<psi> x h \<cdot>\<^sub>C F g = f \<cdot>\<^sub>C (\<epsilon>.map x \<cdot>\<^sub>C F h) \<cdot>\<^sub>C F g"
        unfolding \<psi>_def by auto
      also have "... = (f \<cdot>\<^sub>C \<epsilon>.map x) \<cdot>\<^sub>C F h \<cdot>\<^sub>C F g"
        using C.comp_assoc by fastforce
      also have "... = (f \<cdot>\<^sub>C \<epsilon>.map x) \<cdot>\<^sub>C F (h \<cdot>\<^sub>D g)"
        using g h by fastforce
      also have "... = (\<epsilon>.map x' \<cdot>\<^sub>C F (G f)) \<cdot>\<^sub>C F (h \<cdot>\<^sub>D g)"
        using f \<epsilon>.naturality by auto
      also have "... = \<epsilon>.map x' \<cdot>\<^sub>C F ((G f \<cdot>\<^sub>D h) \<cdot>\<^sub>D g)"
        using f g h C.comp_assoc by fastforce
      also have "... = \<psi> x' ((G f \<cdot>\<^sub>D h) \<cdot>\<^sub>D g)"
        unfolding \<psi>_def by auto
      finally show ?thesis by auto
    qed

    lemma \<psi>_inverts_coext:
    assumes x: "C.ide x" and g: "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "arrow_from_functor.is_coext D C F (G x) (\<epsilon>.map x) y (\<psi> x g) g"
    proof -
      interpret x\<epsilon>: arrow_from_functor D C F \<open>G x\<close> x \<open>\<epsilon>.map x\<close>
        using x \<epsilon>.maps_ide_in_hom by unfold_locales auto
      show "x\<epsilon>.is_coext y (\<psi> x g) g"
        using x g \<psi>_def x\<epsilon>.is_coext_def G_ide by blast
    qed

    lemma \<psi>_invertible:
    assumes y: "D.ide y" and f: "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<exists>!g. \<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright> \<and> \<psi> x g = f"
    proof
      have x: "C.ide x" using f by auto
      interpret x\<epsilon>: terminal_arrow_from_functor D C F \<open>Go x\<close> x \<open>\<epsilon>o x\<close>
        using x ex_terminal_arrow Go_\<epsilon>o_terminal by auto
      have 1: "arrow_from_functor D C F y x f"
        using y f by (unfold_locales, auto)
      let ?g = "x\<epsilon>.the_coext y f"
      have "\<psi> x ?g = f"
        using 1 x y \<psi>_def x\<epsilon>.the_coext_prop G_ide \<psi>_inverts_coext x\<epsilon>.is_coext_def by simp
      thus "\<guillemotleft>?g : y \<rightarrow>\<^sub>D G x\<guillemotright> \<and> \<psi> x ?g = f"
        using 1 x x\<epsilon>.the_coext_prop G_ide by simp
      show "\<And>g'. \<guillemotleft>g' : y \<rightarrow>\<^sub>D G x\<guillemotright> \<and> \<psi> x g' = f \<Longrightarrow> g' = ?g"
        using 1 x y \<psi>_inverts_coext G_ide x\<epsilon>.the_coext_unique by force
    qed

    definition \<phi>
    where "\<phi> y f = (THE g. \<guillemotleft>g : y \<rightarrow>\<^sub>D G (C.cod f)\<guillemotright> \<and> \<psi> (C.cod f) g = f)"

    lemma \<phi>_in_hom:
    assumes "D.ide y" and "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<guillemotleft>\<phi> y f : y \<rightarrow>\<^sub>D G x\<guillemotright>"
      using assms \<psi>_invertible \<phi>_def theI' [of "\<lambda>g. \<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright> \<and> \<psi> x g = f"]
      by auto

    lemma \<phi>_\<psi>:
    assumes "C.ide x" and "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "\<phi> y (\<psi> x g) = g"
    proof -
      have "\<phi> y (\<psi> x g) = (THE g'. \<guillemotleft>g' : y \<rightarrow>\<^sub>D G x\<guillemotright> \<and> \<psi> x g' = \<psi> x g)"
      proof -
        have "C.cod (\<psi> x g) = x"
          using assms \<psi>_in_hom by auto
        thus ?thesis
          using \<phi>_def by auto
      qed
      moreover have "\<exists>!g'. \<guillemotleft>g' : y \<rightarrow>\<^sub>D G x\<guillemotright> \<and> \<psi> x g' = \<psi> x g"
        using assms \<psi>_in_hom \<psi>_invertible D.ide_dom by blast
      ultimately show "\<phi> y (\<psi> x g) = g"
        using assms(2) by auto
    qed

    lemma \<psi>_\<phi>:
    assumes "D.ide y" and "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<psi> x (\<phi> y f) = f"
      using assms \<psi>_invertible \<phi>_def theI' [of "\<lambda>g. \<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright> \<and> \<psi> x g = f"]
      by auto

    lemma \<phi>_natural:
    assumes "\<guillemotleft>f : x \<rightarrow>\<^sub>C x'\<guillemotright>" and "\<guillemotleft>g : y' \<rightarrow>\<^sub>D y\<guillemotright>" and "\<guillemotleft>h : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<phi> y' (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) = (G f \<cdot>\<^sub>D \<phi> y h) \<cdot>\<^sub>D g"
    proof -
      have "C.ide x' \<and> D.ide y \<and> D.in_hom (\<phi> y h) y (G x)"
        using assms \<phi>_in_hom by auto
      thus ?thesis
        using assms D.comp_in_homI G.preserves_hom \<psi>_natural [of f x x' g y' y "\<phi> y h"] \<phi>_\<psi> \<psi>_\<phi>
        by auto
    qed

    theorem induces_meta_adjunction:
    shows "meta_adjunction C D F G \<phi> \<psi>"
      using \<phi>_in_hom \<psi>_in_hom \<phi>_\<psi> \<psi>_\<phi> \<phi>_natural D.comp_assoc
      by unfold_locales auto

  end

  text\<open>
    A right adjoint functor induces a meta-adjunction, modulo the choice of a
    left adjoint and unit.
\<close>

  context right_adjoint_functor
  begin

    definition Fo :: "'d \<Rightarrow> 'c"
    where "Fo y = (SOME x. \<exists>u. initial_arrow_to_functor C D G y x u)"

    definition \<eta>o :: "'d \<Rightarrow> 'd"
    where "\<eta>o y = (SOME u. initial_arrow_to_functor C D G y (Fo y) u)"

    lemma Fo_\<eta>o_initial:
    assumes "\<exists>x u. initial_arrow_to_functor C D G y x u"
    shows "initial_arrow_to_functor C D G y (Fo y) (\<eta>o y)"
      using assms Fo_def \<eta>o_def
            someI_ex [of "\<lambda>x. \<exists>u. initial_arrow_to_functor C D G y x u"]
            someI_ex [of "\<lambda>u. initial_arrow_to_functor C D G y (Fo y) u"]
      by simp

    text\<open>
      The left adjoint @{term F} to @{term g} takes each arrow @{term g} of
      @{term[source=true] D} to the unique @{term[source=true] C}-extension of
      @{term "D (\<eta>o (D.cod g)) g"} along @{term "\<eta>o (D.dom g)"}.
\<close>

    definition F :: "'d \<Rightarrow> 'c"
    where "F g = (if D.arr g then
                     initial_arrow_to_functor.the_ext C D G (Fo (D.dom g)) (\<eta>o (D.dom g))
                                  (Fo (D.cod g)) (\<eta>o (D.cod g) \<cdot>\<^sub>D g)
                  else C.null)"

    lemma F_ide:
    assumes "D.ide y"
    shows "F y = Fo y"
    proof -
      interpret initial_arrow_to_functor C D G y \<open>Fo y\<close> \<open>\<eta>o y\<close>
        using assms ex_initial_arrow Fo_\<eta>o_initial by blast
      have 1: "arrow_to_functor C D G y (Fo y) (\<eta>o y)" ..
      have "is_ext (Fo y) (\<eta>o y) (Fo y)"
        unfolding is_ext_def using arrow D.comp_ide_arr [of "G (Fo y)" "\<eta>o y"] by force
      hence "Fo y = the_ext (Fo y) (\<eta>o y)"
        using 1 the_ext_unique by blast
      moreover have "\<eta>o y = D (\<eta>o (D.cod y)) y"
        using assms arrow D.comp_arr_ide D.comp_arr_dom by auto
      ultimately show ?thesis
        using assms F_def D.dom_cod D.in_homE D.ide_in_hom by metis
    qed

    lemma F_is_functor:
    shows "functor D C F"
    proof
      fix g :: 'd
      assume "\<not>D.arr g"
      thus "F g = C.null" using F_def by auto
      next
      fix g :: 'd
      assume g: "D.arr g"
      let ?y = "D.dom g"
      let ?y' = "D.cod g"
      interpret y\<eta>: initial_arrow_to_functor C D G ?y \<open>Fo ?y\<close> \<open>\<eta>o ?y\<close>
        using g ex_initial_arrow Fo_\<eta>o_initial by simp
      interpret y'\<eta>: initial_arrow_to_functor C D G ?y' \<open>Fo ?y'\<close> \<open>\<eta>o ?y'\<close>
        using g ex_initial_arrow Fo_\<eta>o_initial by simp
      have 1: "arrow_to_functor C D G ?y (Fo ?y') (D (\<eta>o ?y') g)"
        using g y'\<eta>.arrow by unfold_locales auto
      have "F g = y\<eta>.the_ext (Fo ?y') (D (\<eta>o ?y') g)"
        using g F_def by simp
      hence Fg: "\<guillemotleft>F g : Fo ?y \<rightarrow>\<^sub>C Fo ?y'\<guillemotright> \<and> \<eta>o ?y' \<cdot>\<^sub>D g = G (F g) \<cdot>\<^sub>D \<eta>o ?y"
        using 1 y\<eta>.the_ext_prop by simp
      show "C.arr (F g)" using Fg by auto
      show "C.dom (F g) = F ?y" using Fg g F_ide by auto
      show "C.cod (F g) = F ?y'" using Fg g F_ide by auto
      next
      fix g :: 'd
      fix g' :: 'd
      assume g': "D.arr (D g' g)"
      have g: "D.arr g" using g' by auto
      let ?y = "D.dom g"
      let ?y' = "D.cod g"
      let ?y'' = "D.cod g'"
      interpret y\<eta>: initial_arrow_to_functor C D G ?y \<open>Fo ?y\<close> \<open>\<eta>o ?y\<close>
        using g ex_initial_arrow Fo_\<eta>o_initial by simp
      interpret y'\<eta>: initial_arrow_to_functor C D G ?y' \<open>Fo ?y'\<close> \<open>\<eta>o ?y'\<close>
        using g ex_initial_arrow Fo_\<eta>o_initial by simp
      interpret y''\<eta>: initial_arrow_to_functor C D G ?y'' \<open>Fo ?y''\<close> \<open>\<eta>o ?y''\<close>
        using g' ex_initial_arrow Fo_\<eta>o_initial by auto
      have 1: "arrow_to_functor C D G ?y (Fo ?y') (\<eta>o ?y' \<cdot>\<^sub>D g)"
        using g y'\<eta>.arrow by unfold_locales auto
      have "F g = y\<eta>.the_ext (Fo ?y') (\<eta>o ?y' \<cdot>\<^sub>D g)"
        using g F_def by simp
      hence Fg: "\<guillemotleft>F g : Fo ?y \<rightarrow>\<^sub>C Fo ?y'\<guillemotright> \<and> \<eta>o ?y' \<cdot>\<^sub>D g = G (F g) \<cdot>\<^sub>D \<eta>o ?y"
        using 1 y\<eta>.the_ext_prop by simp
      have 2: "arrow_to_functor C D G ?y' (Fo ?y'') (\<eta>o ?y'' \<cdot>\<^sub>D g')"
        using g' y''\<eta>.arrow by unfold_locales auto
      have "F g' = y'\<eta>.the_ext (Fo ?y'') (\<eta>o ?y'' \<cdot>\<^sub>D g')"
        using g' F_def by auto
      hence Fg': "\<guillemotleft>F g' : Fo ?y' \<rightarrow>\<^sub>C Fo ?y''\<guillemotright> \<and> \<eta>o ?y'' \<cdot>\<^sub>D g' = G (F g') \<cdot>\<^sub>D \<eta>o ?y'"
        using 2 y'\<eta>.the_ext_prop by simp
      show "F (g' \<cdot>\<^sub>D g) = F g' \<cdot>\<^sub>C F g"
      proof -
        have "y\<eta>.is_ext (Fo ?y'') (\<eta>o ?y'' \<cdot>\<^sub>D g' \<cdot>\<^sub>D g) (F g' \<cdot>\<^sub>C F g)"
        proof -
          have 3: "\<guillemotleft>F g' \<cdot>\<^sub>C F g : Fo ?y \<rightarrow>\<^sub>C Fo ?y''\<guillemotright>" using 1 2 Fg Fg' by auto
          moreover have "\<eta>o ?y'' \<cdot>\<^sub>D g' \<cdot>\<^sub>D g = G (F g' \<cdot>\<^sub>C F g) \<cdot>\<^sub>D \<eta>o ?y"
            using Fg Fg' g g' 3 y''\<eta>.arrow
            by (metis C.arrI D.comp_assoc preserves_comp)
          ultimately show ?thesis using y\<eta>.is_ext_def by auto
        qed
        moreover have "arrow_to_functor C D G ?y (Fo ?y'') (\<eta>o ?y'' \<cdot>\<^sub>D g' \<cdot>\<^sub>D g)"
          using g g' y''\<eta>.arrow by unfold_locales auto
        ultimately show ?thesis
          using g g' F_def y\<eta>.the_ext_unique D.dom_comp D.cod_comp by auto
      qed
    qed

    interpretation F: "functor" D C F using F_is_functor by auto

    lemma F_simp:
    assumes "D.arr g"
    shows "F g = initial_arrow_to_functor.the_ext C D G (Fo (D.dom g)) (\<eta>o (D.dom g))
                                                        (Fo (D.cod g)) (\<eta>o (D.cod g) \<cdot>\<^sub>D g)"
      using assms F_def by simp

    interpretation FG: composite_functor D C D F G ..

    interpretation \<eta>: transformation_by_components D D D.map FG.map \<eta>o
    proof
      fix y :: 'd
      assume y: "D.ide y"
      show "\<guillemotleft>\<eta>o y : D.map y \<rightarrow>\<^sub>D FG.map y\<guillemotright>"
      proof -
        interpret initial_arrow_to_functor C D G y \<open>Fo y\<close> \<open>\<eta>o y\<close>
          using y Fo_\<eta>o_initial ex_initial_arrow by simp
        show ?thesis using y F_ide arrow by auto
      qed
      next
      fix g :: 'd
      assume g: "D.arr g"
      show "\<eta>o (D.cod g) \<cdot>\<^sub>D D.map g = FG.map g \<cdot>\<^sub>D \<eta>o (D.dom g)"
      proof -
        let ?y = "D.dom g"
        let ?y' = "D.cod g"
        interpret y\<eta>: initial_arrow_to_functor C D G ?y \<open>Fo ?y\<close> \<open>\<eta>o ?y\<close>
          using g Fo_\<eta>o_initial ex_initial_arrow by simp
        interpret y'\<eta>: initial_arrow_to_functor C D G ?y' \<open>Fo ?y'\<close> \<open>\<eta>o ?y'\<close>
          using g Fo_\<eta>o_initial ex_initial_arrow by simp
        have "arrow_to_functor C D G ?y (Fo ?y') (\<eta>o ?y' \<cdot>\<^sub>D g)"
          using g y'\<eta>.arrow by unfold_locales auto
        moreover have "F g = y\<eta>.the_ext (Fo ?y') (\<eta>o ?y' \<cdot>\<^sub>D g)"
          using g F_simp by blast
        ultimately have "y\<eta>.is_ext (Fo ?y') (\<eta>o ?y' \<cdot>\<^sub>D g) (F g)"
          using y\<eta>.the_ext_prop y\<eta>.is_ext_def by auto
        thus ?thesis
          using g y\<eta>.is_ext_def by simp
      qed
    qed

    definition \<phi>
    where "\<phi> y h = D (G h) (\<eta>.map y)"

    lemma \<phi>_in_hom:
    assumes y: "D.ide y" and f: "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<guillemotleft>\<phi> y f : y \<rightarrow>\<^sub>D G x\<guillemotright>"
      unfolding \<phi>_def using assms \<eta>.maps_ide_in_hom by auto

    lemma \<phi>_natural:
    assumes f: "\<guillemotleft>f : x \<rightarrow>\<^sub>C x'\<guillemotright>" and g: "\<guillemotleft>g : y' \<rightarrow>\<^sub>D y\<guillemotright>" and h: "\<guillemotleft>h : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<phi> y' (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) = (G f \<cdot>\<^sub>D \<phi> y h) \<cdot>\<^sub>D g"
    proof -
      have "(G f \<cdot>\<^sub>D \<phi> y h) \<cdot>\<^sub>D g = (G f \<cdot>\<^sub>D G h \<cdot>\<^sub>D \<eta>.map y) \<cdot>\<^sub>D g"
        unfolding \<phi>_def by auto
      also have "... = (G f \<cdot>\<^sub>D G h) \<cdot>\<^sub>D \<eta>.map y \<cdot>\<^sub>D g"
        using D.comp_assoc by fastforce
      also have "... = G (f \<cdot>\<^sub>C h) \<cdot>\<^sub>D G (F g) \<cdot>\<^sub>D \<eta>.map y'"
        using f g h \<eta>.naturality by fastforce
      also have "... = (G (f \<cdot>\<^sub>C h) \<cdot>\<^sub>D G (F g)) \<cdot>\<^sub>D \<eta>.map y'"
        using D.comp_assoc by fastforce
      also have "... = G (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) \<cdot>\<^sub>D \<eta>.map y'"
        using f g h D.comp_assoc by fastforce
      also have "... = \<phi> y' (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g)"
        unfolding \<phi>_def by auto
      finally show ?thesis by auto
    qed

    lemma \<phi>_inverts_ext:
    assumes y: "D.ide y" and f: "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "arrow_to_functor.is_ext C D G (F y) (\<eta>.map y) x (\<phi> y f) f"
    proof -
      interpret y\<eta>: arrow_to_functor C D G y \<open>F y\<close> \<open>\<eta>.map y\<close>
        using y \<eta>.maps_ide_in_hom by unfold_locales auto
      show "y\<eta>.is_ext x (\<phi> y f) f"
        using f y \<phi>_def y\<eta>.is_ext_def F_ide by blast
    qed

    lemma \<phi>_invertible:
    assumes x: "C.ide x" and g: "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "\<exists>!f. \<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright> \<and> \<phi> y f = g"
    proof
      have y: "D.ide y" using g by auto
      interpret y\<eta>: initial_arrow_to_functor C D G y \<open>Fo y\<close> \<open>\<eta>o y\<close>
        using y ex_initial_arrow Fo_\<eta>o_initial by auto
      have 1: "arrow_to_functor C D G y x g"
        using x g by (unfold_locales, auto)
      let ?f = "y\<eta>.the_ext x g"
      have "\<phi> y ?f = g"
        using \<phi>_def y\<eta>.the_ext_prop 1 F_ide x y \<phi>_inverts_ext y\<eta>.is_ext_def by fastforce
      moreover have "\<guillemotleft>?f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
        using 1 y y\<eta>.the_ext_prop F_ide by simp
      ultimately show "\<guillemotleft>?f : F y \<rightarrow>\<^sub>C x\<guillemotright> \<and> \<phi> y ?f = g" by auto
      show "\<And>f'. \<guillemotleft>f' : F y \<rightarrow>\<^sub>C x\<guillemotright> \<and> \<phi> y f' = g \<Longrightarrow> f' = ?f"
        using 1 y \<phi>_inverts_ext y\<eta>.the_ext_unique F_ide by force
    qed

    definition \<psi>
    where "\<psi> x g = (THE f. \<guillemotleft>f : F (D.dom g) \<rightarrow>\<^sub>C x\<guillemotright> \<and> \<phi> (D.dom g) f = g)"

    lemma \<psi>_in_hom:
    assumes "C.ide x" and "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "C.in_hom (\<psi> x g) (F y) x"
      using assms \<phi>_invertible \<psi>_def theI' [of "\<lambda>f. \<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright> \<and> \<phi> y f = g"]
      by auto

    lemma \<psi>_\<phi>:
    assumes "D.ide y" and "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<psi> x (\<phi> y f) = f"
    proof -
      have "D.dom (\<phi> y f) = y" using assms \<phi>_in_hom by blast
      hence "\<psi> x (\<phi> y f) = (THE f'. \<guillemotleft>f' : F y \<rightarrow>\<^sub>C x\<guillemotright> \<and> \<phi> y f' = \<phi> y f)"
        using \<psi>_def by auto
      moreover have "\<exists>!f'. \<guillemotleft>f' : F y \<rightarrow>\<^sub>C x\<guillemotright> \<and> \<phi> y f' = \<phi> y f"
        using assms \<phi>_in_hom \<phi>_invertible C.ide_cod by blast
      ultimately show ?thesis using assms(2) by auto
    qed

    lemma \<phi>_\<psi>:
    assumes "C.ide x" and "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "\<phi> y (\<psi> x g) = g"
      using assms \<phi>_invertible \<psi>_def theI' [of "\<lambda>f. \<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright> \<and> \<phi> y f = g"]
      by auto

    theorem induces_meta_adjunction:
    shows "meta_adjunction C D F G \<phi> \<psi>"
      using \<phi>_in_hom \<psi>_in_hom \<phi>_\<psi> \<psi>_\<phi> \<phi>_natural D.comp_assoc
      by (unfold_locales, auto)

  end

  section "Meta-Adjunctions Induce Hom-Adjunctions"

  text\<open>
    To obtain a hom-adjunction from a meta-adjunction, we need to exhibit hom-functors
    from @{term C} and @{term D} to a common set category @{term S}, so it is necessary
    to apply an actual concrete construction of such a category.
    We use the replete set category generated by the disjoint sum
    @{typ "('c+'d)"} of the arrow types of @{term C} and @{term D}.
\<close>

  context meta_adjunction
  begin

    interpretation S: replete_setcat \<open>TYPE('c+'d)\<close> .

    definition inC :: "'c \<Rightarrow> ('c+'d) setcat.arr"
    where "inC \<equiv> S.UP o Inl"

    definition inD :: "'d \<Rightarrow> ('c+'d) setcat.arr"
    where "inD \<equiv> S.UP o Inr"

    interpretation S: replete_setcat \<open>TYPE('c+'d)\<close> .
    interpretation Cop: dual_category C ..
    interpretation Dop: dual_category D ..
    interpretation CopxC: product_category Cop.comp C ..
    interpretation DopxD: product_category Dop.comp D ..
    interpretation DopxC: product_category Dop.comp C ..
    interpretation HomC: hom_functor C S.comp S.setp \<open>\<lambda>_. inC\<close>
    proof
      show "\<And>f. C.arr f \<Longrightarrow> inC f \<in> S.Univ"
        unfolding inC_def using S.UP_mapsto by auto
      thus "\<And>b a. \<lbrakk>C.ide b; C.ide a\<rbrakk> \<Longrightarrow> inC ` C.hom b a \<subseteq> S.Univ"
        by blast
      show "\<And>b a. \<lbrakk>C.ide b; C.ide a\<rbrakk> \<Longrightarrow> inj_on inC (C.hom b a)"
        unfolding inC_def
        using S.inj_UP
        by (metis injD inj_Inl inj_compose inj_on_def)
    qed
    interpretation HomD: hom_functor D S.comp S.setp \<open>\<lambda>_. inD\<close>
    proof
      show "\<And>f. D.arr f \<Longrightarrow> inD f \<in> S.Univ"
        unfolding inD_def using S.UP_mapsto by auto
      thus "\<And>b a. \<lbrakk>D.ide b; D.ide a\<rbrakk> \<Longrightarrow> inD ` D.hom b a \<subseteq> S.Univ"
        by blast
      show "\<And>b a. \<lbrakk>D.ide b; D.ide a\<rbrakk> \<Longrightarrow> inj_on inD (D.hom b a)"
        unfolding inD_def
        using S.inj_UP
        by (metis injD inj_Inr inj_compose inj_on_def)
    qed
    interpretation Fop: dual_functor D C F ..
    interpretation FopxC: product_functor Dop.comp C Cop.comp C Fop.map C.map ..
    interpretation DopxG: product_functor Dop.comp C Dop.comp D Dop.map G ..
    interpretation Hom_FopxC: composite_functor DopxC.comp CopxC.comp S.comp
                                                FopxC.map HomC.map ..
    interpretation Hom_DopxG: composite_functor DopxC.comp DopxD.comp S.comp
                                                DopxG.map HomD.map ..

    lemma inC_\<psi> [simp]:
    assumes "C.ide b" and "C.ide a" and "x \<in> inC ` C.hom b a"
    shows "inC (HomC.\<psi> (b, a) x) = x"
      using assms by auto

    lemma \<psi>_inC [simp]:
    assumes "C.arr f"
    shows "HomC.\<psi> (C.dom f, C.cod f) (inC f) = f"
      using assms HomC.\<psi>_\<phi> by blast

    lemma inD_\<psi> [simp]:
    assumes "D.ide b" and "D.ide a" and "x \<in> inD ` D.hom b a"
    shows "inD (HomD.\<psi> (b, a) x) = x"
      using assms by auto

    lemma \<psi>_inD [simp]:
    assumes "D.arr f"
    shows "HomD.\<psi> (D.dom f, D.cod f) (inD f) = f"
      using assms HomD.\<psi>_\<phi> by blast

    lemma Hom_FopxC_simp:
    assumes "DopxC.arr gf"
    shows "Hom_FopxC.map gf =
              S.mkArr (HomC.set (F (D.cod (fst gf)), C.dom (snd gf)))
                      (HomC.set (F (D.dom (fst gf)), C.cod (snd gf)))
                      (inC \<circ> (\<lambda>h. snd gf \<cdot>\<^sub>C h \<cdot>\<^sub>C F (fst gf))
                           \<circ> HomC.\<psi> (F (D.cod (fst gf)), C.dom (snd gf)))"
      using assms HomC.map_def by simp

    lemma Hom_DopxG_simp:
    assumes "DopxC.arr gf"
    shows "Hom_DopxG.map gf =
              S.mkArr (HomD.set (D.cod (fst gf), G (C.dom (snd gf))))
                      (HomD.set (D.dom (fst gf), G (C.cod (snd gf))))
                      (inD \<circ> (\<lambda>h. G (snd gf) \<cdot>\<^sub>D h \<cdot>\<^sub>D fst gf)
                           \<circ> HomD.\<psi> (D.cod (fst gf), G (C.dom (snd gf))))"
      using assms HomD.map_def by simp
                      
    definition \<Phi>o
    where "\<Phi>o yx = S.mkArr (HomC.set (F (fst yx), snd yx))
                           (HomD.set (fst yx, G (snd yx)))
                           (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))"

    lemma \<Phi>o_in_hom:
    assumes yx: "DopxC.ide yx"
    shows "\<guillemotleft>\<Phi>o yx : Hom_FopxC.map yx \<rightarrow>\<^sub>S Hom_DopxG.map yx\<guillemotright>"
    proof -
      have "Hom_FopxC.map yx = S.mkIde (HomC.set (F (fst yx), snd yx))"
        using yx HomC.map_ide by auto
      moreover have "Hom_DopxG.map yx = S.mkIde (HomD.set (fst yx, G (snd yx)))"
        using yx HomD.map_ide by auto
      moreover have
          "\<guillemotleft>S.mkArr (HomC.set (F (fst yx), snd yx)) (HomD.set (fst yx, G (snd yx)))
                    (inD \<circ> \<phi> (fst yx) \<circ> HomC.\<psi> (F (fst yx), snd yx)) :
              S.mkIde (HomC.set (F (fst yx), snd yx))
                 \<rightarrow>\<^sub>S S.mkIde (HomD.set (fst yx, G (snd yx)))\<guillemotright>"
      proof (intro S.mkArr_in_hom)
        show "HomC.set (F (fst yx), snd yx) \<subseteq> S.Univ" using yx HomC.set_subset_Univ by simp
        show "HomD.set (fst yx, G (snd yx)) \<subseteq> S.Univ" using yx HomD.set_subset_Univ by simp
        show "inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx)
                 \<in> HomC.set (F (fst yx), snd yx) \<rightarrow> HomD.set (fst yx, G (snd yx))"
        proof
          fix x
          assume x: "x \<in> HomC.set (F (fst yx), snd yx)"
          show "(inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx)) x
                  \<in> HomD.set (fst yx, G (snd yx))"
            using x yx HomC.\<psi>_mapsto [of "F (fst yx)" "snd yx"]
                  \<phi>_in_hom [of "fst yx"] HomD.\<phi>_mapsto [of "fst yx" "G (snd yx)"]
            by auto
        qed
      qed
      ultimately show ?thesis using \<Phi>o_def by auto
    qed

    interpretation \<Phi>: transformation_by_components
                        DopxC.comp S.comp Hom_FopxC.map Hom_DopxG.map \<Phi>o
    proof
      fix yx
      assume yx: "DopxC.ide yx"
      show "\<guillemotleft>\<Phi>o yx : Hom_FopxC.map yx \<rightarrow>\<^sub>S Hom_DopxG.map yx\<guillemotright>"
        using yx \<Phi>o_in_hom by auto
      next
      fix gf
      assume gf: "DopxC.arr gf"
      show "S.comp (\<Phi>o (DopxC.cod gf)) (Hom_FopxC.map gf)
                = S.comp (Hom_DopxG.map gf) (\<Phi>o (DopxC.dom gf))"
      proof -
        let ?g = "fst gf"
        let ?f = "snd gf"
        let ?x = "C.dom ?f"
        let ?x' = "C.cod ?f"
        let ?y = "D.cod ?g"
        let ?y' = "D.dom ?g"
        let ?Fy = "F ?y"
        let ?Fy' = "F ?y'"
        let ?Fg = "F ?g"
        let ?Gx = "G ?x"
        let ?Gx' = "G ?x'"
        let ?Gf = "G ?f"
        have 1: "S.arr (Hom_FopxC.map gf) \<and>
                 Hom_FopxC.map gf = S.mkArr (HomC.set (?Fy, ?x)) (HomC.set (?Fy', ?x'))
                                            (inC o (\<lambda>h. ?f \<cdot>\<^sub>C h \<cdot>\<^sub>C ?Fg) o HomC.\<psi> (?Fy, ?x))"
          using gf Hom_FopxC.preserves_arr Hom_FopxC_simp by blast
        have 2: "S.arr (\<Phi>o (DopxC.cod gf)) \<and>
                 \<Phi>o (DopxC.cod gf) = S.mkArr (HomC.set (?Fy', ?x')) (HomD.set (?y', ?Gx'))
                                             (inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))"
          using gf \<Phi>o_in_hom [of "DopxC.cod gf"] \<Phi>o_def [of "DopxC.cod gf"] \<phi>_in_hom
          by auto
        have 3: "S.arr (\<Phi>o (DopxC.dom gf)) \<and>
                 \<Phi>o (DopxC.dom gf) = S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y, ?Gx))
                                             (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))"
          using gf \<Phi>o_in_hom [of "DopxC.dom gf"] \<Phi>o_def [of "DopxC.dom gf"] \<phi>_in_hom
          by auto
        have 4: "S.arr (Hom_DopxG.map gf) \<and>
                 Hom_DopxG.map gf = S.mkArr (HomD.set (?y, ?Gx)) (HomD.set (?y', ?Gx'))
                                            (inD o (\<lambda>h. ?Gf \<cdot>\<^sub>D h \<cdot>\<^sub>D ?g) o HomD.\<psi> (?y, ?Gx))"
          using gf Hom_DopxG.preserves_arr Hom_DopxG_simp by blast
        have 5: "S.seq (\<Phi>o (DopxC.cod gf)) (Hom_FopxC.map gf) \<and>
                 S.comp (\<Phi>o (DopxC.cod gf)) (Hom_FopxC.map gf)
                     = S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y', ?Gx'))
                               ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                                 o (inC o (\<lambda>h. ?f \<cdot>\<^sub>C h \<cdot>\<^sub>C ?Fg) o HomC.\<psi> (?Fy, ?x)))"
          by (metis gf 1 2 DopxC.arr_iff_in_hom DopxC.ide_cod Hom_FopxC.preserves_hom
                    S.comp_mkArr S.seqI' \<Phi>o_in_hom)
        have 6: "S.comp (Hom_DopxG.map gf) (\<Phi>o (DopxC.dom gf))
                  = S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y', ?Gx'))
                            ((inD o (\<lambda>h. ?Gf \<cdot>\<^sub>D h \<cdot>\<^sub>D ?g) o HomD.\<psi> (?y, ?Gx))
                              o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x)))"
          by (metis 3 4 S.comp_mkArr)
        have 7:
          "restrict ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                      o (inC o (\<lambda>h. ?f \<cdot>\<^sub>C h \<cdot>\<^sub>C ?Fg) o HomC.\<psi> (?Fy, ?x))) (HomC.set (?Fy, ?x))
             = restrict ((inD o (\<lambda>h. ?Gf \<cdot>\<^sub>D h \<cdot>\<^sub>D ?g) o HomD.\<psi> (?y, ?Gx))
                          o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))) (HomC.set (?Fy, ?x))"
        proof (intro restrict_ext)
          show "\<And>h. h \<in> HomC.set (?Fy, ?x) \<Longrightarrow>
                     ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                       o (inC o (\<lambda>h. ?f \<cdot>\<^sub>C h \<cdot>\<^sub>C ?Fg) o HomC.\<psi> (?Fy, ?x))) h
                       = ((inD o (\<lambda>h. ?Gf \<cdot>\<^sub>D h \<cdot>\<^sub>D ?g) o HomD.\<psi> (?y, ?Gx))
                           o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))) h"
          proof -
            fix h
            assume h: "h \<in> HomC.set (?Fy, ?x)"
            have \<psi>h: "\<guillemotleft>HomC.\<psi> (?Fy, ?x) h : ?Fy \<rightarrow>\<^sub>C ?x\<guillemotright>"
              using gf h HomC.\<psi>_mapsto [of ?Fy ?x] CopxC.ide_char by auto
            show "((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                       o (inC o (\<lambda>h. ?f \<cdot>\<^sub>C h \<cdot>\<^sub>C ?Fg) o HomC.\<psi> (?Fy, ?x))) h
                       = ((inD o (\<lambda>h. ?Gf \<cdot>\<^sub>D h \<cdot>\<^sub>D ?g) o HomD.\<psi> (?y, ?Gx))
                           o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))) h"
            proof -
              have
                "((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                   o (inC o (\<lambda>h. ?f \<cdot>\<^sub>C h \<cdot>\<^sub>C ?Fg) o HomC.\<psi> (?Fy, ?x))) h
                   = inD (\<phi> ?y' (?f \<cdot>\<^sub>C HomC.\<psi> (?Fy, ?x) h \<cdot>\<^sub>C ?Fg))"
                using gf \<psi>h HomC.\<phi>_mapsto HomC.\<psi>_mapsto \<phi>_in_hom
                      \<psi>_inC [of "?f \<cdot>\<^sub>C HomC.\<psi> (?Fy, ?x) h \<cdot>\<^sub>C ?Fg"]
                by auto
              also have "... = inD (D ?Gf (D (\<phi> ?y (HomC.\<psi> (?Fy, ?x) h)) ?g))"
                by (metis (no_types, lifting) C.arr_cod C.arr_dom_iff_arr C.arr_iff_in_hom
                    C.in_homE D.arr_cod_iff_arr D.arr_iff_in_hom F.preserves_reflects_arr
                    \<phi>_naturality \<psi>h)
              also have "... = ((inD o (\<lambda>h. ?Gf \<cdot>\<^sub>D h \<cdot>\<^sub>D ?g) o HomD.\<psi> (?y, ?Gx))
                                o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x))) h"
                using gf \<psi>h \<phi>_in_hom by simp
              finally show ?thesis by auto
            qed
          qed
        qed
        have 8: "S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y', ?Gx'))
                         ((inD o \<phi> ?y' o HomC.\<psi> (?Fy', ?x'))
                           o (inC o (\<lambda>h. ?f \<cdot>\<^sub>C h \<cdot>\<^sub>C ?Fg) o HomC.\<psi> (?Fy, ?x)))
                    = S.mkArr (HomC.set (?Fy, ?x)) (HomD.set (?y', ?Gx'))
                              ((inD o (\<lambda>h. ?Gf \<cdot>\<^sub>D h \<cdot>\<^sub>D ?g) o HomD.\<psi> (?y, ?Gx))
                                o (inD o \<phi> ?y o HomC.\<psi> (?Fy, ?x)))"
          using 5 7 by force
        show ?thesis using 5 6 8 by auto
      qed
    qed

    lemma \<Phi>_simp:
    assumes YX: "DopxC.ide yx"
    shows "\<Phi>.map yx =
           S.mkArr (HomC.set (F (fst yx), snd yx)) (HomD.set (fst yx, G (snd yx)))
                   (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))"
      using YX \<Phi>o_def by simp
      
    abbreviation \<Psi>o
    where "\<Psi>o yx \<equiv> S.mkArr (HomD.set (fst yx, G (snd yx))) (HomC.set (F (fst yx), snd yx))
                            (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))"

    lemma \<Psi>o_in_hom:
    assumes yx: "DopxC.ide yx"
    shows "\<guillemotleft>\<Psi>o yx : Hom_DopxG.map yx \<rightarrow>\<^sub>S Hom_FopxC.map yx\<guillemotright>"
    proof -
      have "Hom_FopxC.map yx = S.mkIde (HomC.set (F (fst yx), snd yx))"
        using yx HomC.map_ide by auto
      moreover have "Hom_DopxG.map yx = S.mkIde (HomD.set (fst yx, G (snd yx)))"
        using yx HomD.map_ide by auto
      moreover have "\<guillemotleft>\<Psi>o yx : S.mkIde (HomD.set (fst yx, G (snd yx)))
                                 \<rightarrow>\<^sub>S S.mkIde (HomC.set (F (fst yx), snd yx))\<guillemotright>"
      proof (intro S.mkArr_in_hom)
        show "HomC.set (F (fst yx), snd yx) \<subseteq> S.Univ" using yx HomC.set_subset_Univ by simp
        show "HomD.set (fst yx, G (snd yx)) \<subseteq> S.Univ" using yx HomD.set_subset_Univ by simp
        show "inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx))
                 \<in> HomD.set (fst yx, G (snd yx)) \<rightarrow> HomC.set (F (fst yx), snd yx)"
        proof
          fix x
          assume x: "x \<in> HomD.set (fst yx, G (snd yx))"
          show "(inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx))) x
                  \<in> HomC.set (F (fst yx), snd yx)"
            using x yx HomD.\<psi>_mapsto [of "fst yx" "G (snd yx)"] \<psi>_in_hom [of "snd yx"]
                  HomC.\<phi>_mapsto [of "F (fst yx)" "snd yx"]
            by auto
        qed
      qed
      ultimately show ?thesis by auto
    qed

    lemma \<Phi>_inv:
    assumes yx: "DopxC.ide yx"
    shows "S.inverse_arrows (\<Phi>.map yx) (\<Psi>o yx)"
    proof -
      have 1: "\<guillemotleft>\<Phi>.map yx : Hom_FopxC.map yx \<rightarrow>\<^sub>S Hom_DopxG.map yx\<guillemotright>"
        using yx \<Phi>.preserves_hom [of yx yx yx] DopxC.ide_in_hom by blast
      have 2: "\<guillemotleft>\<Psi>o yx : Hom_DopxG.map yx \<rightarrow>\<^sub>S Hom_FopxC.map yx\<guillemotright>"
        using yx \<Psi>o_in_hom by simp
      have 3: "\<Phi>.map yx = S.mkArr (HomC.set (F (fst yx), snd yx))
                                   (HomD.set (fst yx, G (snd yx)))
                                   (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))"
        using yx \<Phi>_simp by blast
      have antipar: "S.antipar (\<Phi>.map yx) (\<Psi>o yx)"
        using 1 2 by blast
      moreover have "S.ide (S.comp (\<Psi>o yx) (\<Phi>.map yx))"
      proof -
        have "S.comp (\<Psi>o yx) (\<Phi>.map yx) =
                  S.mkArr (HomC.set (F (fst yx), snd yx)) (HomC.set (F (fst yx), snd yx))
                          ((inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))
                            o (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx)))"
          using 1 2 3 antipar S.comp_mkArr by auto
        also have
          "... = S.mkArr (HomC.set (F (fst yx), snd yx)) (HomC.set (F (fst yx), snd yx))
                         (\<lambda>x. x)"
        proof -
          have
            "S.mkArr (HomC.set (F (fst yx), snd yx)) (HomC.set (F (fst yx), snd yx)) (\<lambda>x. x)
               = ..."
          proof
            show
              "S.arr (S.mkArr (HomC.set (F (fst yx), snd yx)) (HomC.set (F (fst yx), snd yx))
                     (\<lambda>x. x))"
              using yx HomC.set_subset_Univ by simp
            show "\<And>x. x \<in> HomC.set (F (fst yx), snd yx) \<Longrightarrow>
                        x = ((inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))
                             o (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))) x"
            proof -
              fix x
              assume x: "x \<in> HomC.set (F (fst yx), snd yx)"
              have "((inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))
                             o (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))) x
                      = inC (\<psi> (snd yx) (HomD.\<psi> (fst yx, G (snd yx))
                              (inD (\<phi> (fst yx) (HomC.\<psi> (F (fst yx), snd yx) x)))))"
                by simp
              also have "... = inC (\<psi> (snd yx) (\<phi> (fst yx) (HomC.\<psi> (F (fst yx), snd yx) x)))"
                using x yx HomC.\<psi>_mapsto [of "F (fst yx)" "snd yx"] \<phi>_in_hom by force
              also have "... = inC (HomC.\<psi> (F (fst yx), snd yx) x)"
                using x yx HomC.\<psi>_mapsto [of "F (fst yx)" "snd yx"] \<psi>_\<phi> by force
              also have "... = x" using x yx inC_\<psi> by simp
              finally show "x = ((inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))
                                   o (inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))) x"
                by auto
            qed
          qed
          thus ?thesis by auto
        qed
        also have "... = S.mkIde (HomC.set (F (fst yx), snd yx))"
          using yx S.mkIde_as_mkArr HomC.set_subset_Univ by force
        finally have
            "S.comp (\<Psi>o yx) (\<Phi>.map yx) = S.mkIde (HomC.set (F (fst yx), snd yx))"
          by auto
        thus ?thesis using yx HomC.set_subset_Univ S.ide_mkIde by simp
      qed
      moreover have "S.ide (S.comp (\<Phi>.map yx) (\<Psi>o yx))"
      proof -
        have "S.comp (\<Phi>.map yx) (\<Psi>o yx) =
                  S.mkArr (HomD.set (fst yx, G (snd yx))) (HomD.set (fst yx, G (snd yx)))
                          ((inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))
                            o (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx))))"
          using 1 2 3 S.comp_mkArr antipar by fastforce
        also
          have "... = S.mkArr (HomD.set (fst yx, G (snd yx))) (HomD.set (fst yx, G (snd yx)))
                              (\<lambda>x. x)"
        proof -
          have
            "S.mkArr (HomD.set (fst yx, G (snd yx))) (HomD.set (fst yx, G (snd yx))) (\<lambda>x. x)
                = ..."
          proof
            show
              "S.arr (S.mkArr (HomD.set (fst yx, G (snd yx))) (HomD.set (fst yx, G (snd yx)))
                     (\<lambda>x. x))"
              using yx HomD.set_subset_Univ by simp
            show "\<And>x. x \<in> (HomD.set (fst yx, G (snd yx))) \<Longrightarrow>
                        x = ((inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))
                            o (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))) x"
            proof -
              fix x
              assume x: "x \<in> HomD.set (fst yx, G (snd yx))"
              have "((inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))
                          o (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))) x
                       = inD (\<phi> (fst yx) (HomC.\<psi> (F (fst yx), snd yx)
                            (inC (\<psi> (snd yx) (HomD.\<psi> (fst yx, G (snd yx)) x)))))"
                by simp
              also have "... = inD (\<phi> (fst yx) (\<psi> (snd yx) (HomD.\<psi> (fst yx, G (snd yx)) x)))"
              proof -
                have "\<guillemotleft>\<psi> (snd yx) (HomD.\<psi> (fst yx, G (snd yx)) x) : F (fst yx) \<rightarrow> snd yx\<guillemotright>"
                  using x yx HomD.\<psi>_mapsto [of "fst yx" "G (snd yx)"] \<psi>_in_hom by auto
                thus ?thesis by simp
              qed
              also have "... = inD (HomD.\<psi> (fst yx, G (snd yx)) x)"
                using x yx HomD.\<psi>_mapsto [of "fst yx" "G (snd yx)"] \<phi>_\<psi> by force
              also have "... = x" using x yx inD_\<psi> by simp
              finally show "x = ((inD o \<phi> (fst yx) o HomC.\<psi> (F (fst yx), snd yx))
                                   o (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))) x"
                by auto
            qed
          qed
          thus ?thesis by auto
        qed
        also have "... = S.mkIde (HomD.set (fst yx, G (snd yx)))"
          using yx S.mkIde_as_mkArr HomD.set_subset_Univ by force
        finally have
            "S.comp (\<Phi>.map yx) (\<Psi>o yx) = S.mkIde (HomD.set (fst yx, G (snd yx)))"
          by auto
        thus ?thesis using yx HomD.set_subset_Univ S.ide_mkIde by simp
      qed
      ultimately show ?thesis by auto
    qed

    interpretation \<Phi>: natural_isomorphism DopxC.comp S.comp
                                          Hom_FopxC.map Hom_DopxG.map \<Phi>.map
      using \<Phi>_inv by unfold_locales blast

    interpretation \<Psi>: inverse_transformation DopxC.comp S.comp
                           Hom_FopxC.map Hom_DopxG.map \<Phi>.map ..

    interpretation \<Phi>\<Psi>: inverse_transformations DopxC.comp S.comp
                           Hom_FopxC.map Hom_DopxG.map \<Phi>.map \<Psi>.map
      using \<Psi>.inverts_components by unfold_locales simp

    abbreviation \<Phi> where "\<Phi> \<equiv> \<Phi>.map"
    abbreviation \<Psi> where "\<Psi> \<equiv> \<Psi>.map"

    abbreviation HomC where "HomC \<equiv> HomC.map"
    abbreviation \<phi>C where "\<phi>C \<equiv> \<lambda>_. inC"
    abbreviation HomD where "HomD \<equiv> HomD.map"
    abbreviation \<phi>D where "\<phi>D \<equiv> \<lambda>_. inD"

    theorem induces_hom_adjunction: "hom_adjunction C D S.comp S.setp \<phi>C \<phi>D F G \<Phi> \<Psi>" ..

    lemma \<Psi>_simp:
    assumes yx: "DopxC.ide yx"
    shows "\<Psi> yx = S.mkArr (HomD.set (fst yx, G (snd yx))) (HomC.set (F (fst yx), snd yx))
                          (inC o \<psi> (snd yx) o HomD.\<psi> (fst yx, G (snd yx)))"
      using assms \<Phi>o_def \<Phi>_inv S.inverse_unique by simp

    text\<open>
      The original @{term \<phi>} and @{term \<psi>} can be recovered from @{term \<Phi>} and @{term \<Psi>}.
\<close>

    interpretation \<Phi>: set_valued_transformation DopxC.comp S.comp S.setp
                                                Hom_FopxC.map Hom_DopxG.map \<Phi>.map ..
     
    interpretation \<Psi>: set_valued_transformation DopxC.comp S.comp S.setp
                                                Hom_DopxG.map Hom_FopxC.map \<Psi>.map ..

    lemma \<phi>_in_terms_of_\<Phi>':
    assumes y: "D.ide y" and f: "\<guillemotleft>f: F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<phi> y f = (HomD.\<psi> (y, G x) o \<Phi>.FUN (y, x) o inC) f"
    proof -
      have x: "C.ide x" using f by auto
      have "(HomD.\<psi> (y, G x) o \<Phi>.FUN (y, x) o inC) f =
              HomD.\<psi> (y, G x)
                     (restrict (inD o \<phi> y o HomC.\<psi> (F y, x)) (HomC.set (F y, x)) (inC f))"
      proof -
        have "S.arr (\<Phi> (y, x))" using x y by fastforce
        thus ?thesis
          using x y \<Phi>o_def by simp
      qed
      also have "... = \<phi> y f"
        using x y f HomC.\<phi>_mapsto \<phi>_in_hom HomC.\<psi>_mapsto C.ide_in_hom D.ide_in_hom
        by auto
      finally show ?thesis by auto
    qed

    lemma \<psi>_in_terms_of_\<Psi>':
    assumes x: "C.ide x" and g: "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "\<psi> x g = (HomC.\<psi> (F y, x) o \<Psi>.FUN (y, x) o inD) g"
    proof -
      have y: "D.ide y" using g by auto
      have "(HomC.\<psi> (F y, x) o \<Psi>.FUN (y, x) o inD) g =
              HomC.\<psi> (F y, x)
                     (restrict (inC o \<psi> x o HomD.\<psi> (y, G x)) (HomD.set (y, G x)) (inD g))"
      proof -
        have "S.arr (\<Psi> (y, x))"
          using x y \<Psi>.preserves_reflects_arr [of "(y, x)"] by simp
        thus ?thesis
          using x y \<Psi>_simp by simp
      qed
      also have "... = \<psi> x g"
        using x y g HomD.\<phi>_mapsto \<psi>_in_hom HomD.\<psi>_mapsto C.ide_in_hom D.ide_in_hom
        by auto
      finally show ?thesis by auto
    qed

  end

  section "Hom-Adjunctions Induce Meta-Adjunctions"

  context hom_adjunction
  begin

    definition \<phi> :: "'d \<Rightarrow> 'c \<Rightarrow> 'd"
    where
      "\<phi> y h = (HomD.\<psi> (y, G (C.cod h)) o \<Phi>.FUN (y, C.cod h) o \<phi>C (F y, C.cod h)) h"
    
    definition \<psi> :: "'c \<Rightarrow> 'd \<Rightarrow> 'c"
    where
      "\<psi> x h = (HomC.\<psi> (F (D.dom h), x) o \<Psi>.FUN (D.dom h, x) o \<phi>D (D.dom h, G x)) h"

    lemma Hom_FopxC_map_simp:
    assumes "DopxC.arr gf"
    shows "Hom_FopxC.map gf =
              S.mkArr (HomC.set (F (D.cod (fst gf)), C.dom (snd gf)))
                      (HomC.set (F (D.dom (fst gf)), C.cod (snd gf)))            
                      (\<phi>C (F (D.dom (fst gf)), C.cod (snd gf))
                           o (\<lambda>h. snd gf \<cdot>\<^sub>C h \<cdot>\<^sub>C F (fst gf))
                           o HomC.\<psi> (F (D.cod (fst gf)), C.dom (snd gf)))"
      using assms HomC.map_def by simp

    lemma Hom_DopxG_map_simp:
    assumes "DopxC.arr gf"
    shows "Hom_DopxG.map gf =
              S.mkArr (HomD.set (D.cod (fst gf), G (C.dom (snd gf))))
                      (HomD.set (D.dom (fst gf), G (C.cod (snd gf))))           
                      (\<phi>D (D.dom (fst gf), G (C.cod (snd gf)))
                           o (\<lambda>h. G (snd gf) \<cdot>\<^sub>D h \<cdot>\<^sub>D fst gf)
                           o HomD.\<psi> (D.cod (fst gf), G (C.dom (snd gf))))"
      using assms HomD.map_def by simp
                      
    lemma \<Phi>_Fun_mapsto:
    assumes "D.ide y" and "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
    shows "\<Phi>.FUN (y, x) \<in> HomC.set (F y, x) \<rightarrow> HomD.set (y, G x)"
    proof -
      have "S.arr (\<Phi> (y, x)) \<and> \<Phi>.DOM (y, x) = HomC.set (F y, x) \<and>
                                \<Phi>.COD (y, x) = HomD.set (y, G x)"
        using assms HomC.set_map HomD.set_map by auto
      thus ?thesis using S.Fun_mapsto by blast
    qed

    lemma \<phi>_mapsto:
    assumes y: "D.ide y"
    shows "\<phi> y \<in> C.hom (F y) x \<rightarrow> D.hom y (G x)"
    proof
      fix h
      assume h: "h \<in> C.hom (F y) x"
      hence 1: " \<guillemotleft>h : F y \<rightarrow>\<^sub>C x\<guillemotright>" by simp
      show "\<phi> y h \<in> D.hom y (G x)"
      proof -
        have "\<phi>C (F y, x) h \<in> HomC.set (F y, x)"
          using y h 1 HomC.\<phi>_mapsto [of "F y" x] by fastforce
        hence "\<Phi>.FUN (y, x) (\<phi>C (F y, x) h) \<in> HomD.set (y, G x)"
          using h y \<Phi>_Fun_mapsto by auto
        thus ?thesis
          using y h 1 \<phi>_def HomC.\<phi>_mapsto HomD.\<psi>_mapsto [of y "G x"] by fastforce
      qed
    qed

    lemma \<Phi>_simp:
    assumes "D.ide y" and "C.ide x"
    shows "S.arr (\<Phi> (y, x))"
    and "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                            (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
    proof -
      show 1: "S.arr (\<Phi> (y, x))" using assms by auto
      hence "\<Phi> (y, x) = S.mkArr (\<Phi>.DOM (y, x)) (\<Phi>.COD (y, x)) (\<Phi>.FUN (y, x))"
        using S.mkArr_Fun by metis
      also have "... = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x)) (\<Phi>.FUN (y, x))"
        using assms HomC.set_map HomD.set_map by fastforce
      also have "... = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                               (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
      proof (intro S.mkArr_eqI')
        show 2: "S.arr (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x)) (\<Phi>.FUN (y, x)))"
          using 1 calculation by argo
        show "\<And>h. h \<in> HomC.set (F y, x) \<Longrightarrow>
                    \<Phi>.FUN (y, x) h = (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)) h"
        proof -
          fix h
          assume h: "h \<in> HomC.set (F y, x)"
          have "(\<phi>D (y, G x) o \<phi> y o HomC.\<psi> (F y, x)) h =
                   \<phi>D (y, G x) (\<psi>D (y, G x) (\<Phi>.FUN (y, x) (\<phi>C (F y, x) (\<psi>C (F y, x) h))))"
          proof -
            have "\<guillemotleft>\<psi>C (F y, x) h : F y \<rightarrow>\<^sub>C x\<guillemotright>"
              using assms h HomC.\<psi>_mapsto [of "F y" x] by auto
            thus ?thesis
              using h \<phi>_def by auto
          qed
          also have "... = \<phi>D (y, G x) (\<psi>D (y, G x) (\<Phi>.FUN (y, x) h))"
            using assms h HomC.\<phi>_\<psi> \<Phi>_Fun_mapsto by simp
          also have "... = \<Phi>.FUN (y, x) h"
            using assms h \<Phi>_Fun_mapsto [of y "\<psi>C (F y, x) h"] HomC.\<psi>_mapsto
                  HomD.\<phi>_\<psi> [of y "G x"] C.ide_in_hom D.ide_in_hom
            by blast
          finally show "\<Phi>.FUN (y, x) h = (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)) h" by auto
        qed
      qed
      finally show "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                       (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
        by force
    qed

    lemma \<Psi>_Fun_mapsto:
    assumes "C.ide x" and "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
    shows "\<Psi>.FUN (y, x) \<in> HomD.set (y, G x) \<rightarrow> HomC.set (F y, x)"
    proof -
      have "S.arr (\<Psi> (y, x)) \<and> \<Psi>.COD (y, x) = HomC.set (F y, x) \<and>
                                \<Psi>.DOM (y, x) = HomD.set (y, G x)"
        using assms HomC.set_map HomD.set_map by auto
      thus ?thesis using S.Fun_mapsto by fast
    qed

    lemma \<psi>_mapsto:
    assumes x: "C.ide x"
    shows "\<psi> x \<in> D.hom y (G x) \<rightarrow> C.hom (F y) x"
    proof
      fix h
      assume h: "h \<in> D.hom y (G x)"
      hence 1: "\<guillemotleft>h : y \<rightarrow>\<^sub>D G x\<guillemotright>" by auto
      show "\<psi> x h \<in> C.hom (F y) x"
      proof -
        have "\<Psi>.FUN (y, x) (\<phi>D (y, G x) h) \<in> HomC.set (F y, x)"
        proof -
          have "\<phi>D (y, G x) h \<in> HomD.set (y, G x)"
            using x h 1 HomD.\<phi>_mapsto [of y "G x"] by fastforce
          thus ?thesis
            using h x \<Psi>_Fun_mapsto by auto
        qed
        thus ?thesis
          using x h 1 \<psi>_def HomD.\<phi>_mapsto HomC.\<psi>_mapsto [of "F y" x] by fastforce
      qed
    qed

    lemma \<Psi>_simp:
    assumes "D.ide y" and "C.ide x"
    shows "S.arr (\<Psi> (y, x))"
    and "\<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                            (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
    proof -
      show 1: "S.arr (\<Psi> (y, x))" using assms by auto
      hence "\<Psi> (y, x) = S.mkArr (\<Psi>.DOM (y, x)) (\<Psi>.COD (y, x)) (\<Psi>.FUN (y, x))"
        using S.mkArr_Fun by metis
      also have "... = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x)) (\<Psi>.FUN (y, x))"
        using assms HomC.set_map HomD.set_map by auto
      also have "... = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                               (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
      proof (intro S.mkArr_eqI')
        show "S.arr (S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x)) (\<Psi>.FUN (y, x)))"
          using 1 calculation by argo
        show "\<And>h. h \<in> HomD.set (y, G x) \<Longrightarrow>
                    \<Psi>.FUN (y, x) h = (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x)) h"
        proof -
          fix h
          assume h: "h \<in> HomD.set (y, G x)"
          have "(\<phi>C (F y, x) o \<psi> x o HomD.\<psi> (y, G x)) h =
                   \<phi>C (F y, x) (\<psi>C (F y, x) (\<Psi>.FUN (y, x) (\<phi>D (y, G x) (\<psi>D (y, G x) h))))"
          proof -
            have "\<guillemotleft>\<psi>D (y, G x) h : y \<rightarrow>\<^sub>D G x\<guillemotright>"
              using assms h HomD.\<psi>_mapsto [of y "G x"] by auto
            thus ?thesis
              using h \<psi>_def by auto
          qed
          also have "... = \<phi>C (F y, x) (\<psi>C (F y, x) (\<Psi>.FUN (y, x) h))"
            using assms h HomD.\<phi>_\<psi> \<Psi>_Fun_mapsto by simp
          also have "... = \<Psi>.FUN (y, x) h"
            using assms h \<Psi>_Fun_mapsto HomD.\<psi>_mapsto [of y "G x"] HomC.\<phi>_\<psi> [of "F y" x]
                  C.ide_in_hom D.ide_in_hom
            by blast
          finally show "\<Psi>.FUN (y, x) h = (\<phi>C (F y, x) o \<psi> x o HomD.\<psi> (y, G x)) h" by auto
        qed
      qed
      finally show "\<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                       (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
        by force
    qed

    text\<open>
      The length of the next proof stems from having to use properties of composition
      of arrows in @{term[source=true] S} to infer properties of the composition of the
      corresponding functions.
\<close>

    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi>
    proof
      fix y :: 'd and x :: 'c and h :: 'c
      assume y: "D.ide y" and h: "\<guillemotleft>h : F y \<rightarrow>\<^sub>C x\<guillemotright>"
      have x: "C.ide x" using h by auto
      show "\<guillemotleft>\<phi> y h : y \<rightarrow>\<^sub>D G x\<guillemotright>"
      proof -
        have "\<Phi>.FUN (y, x) \<in> HomC.set (F y, x) \<rightarrow> HomD.set (y, G x)"
          using y h \<Phi>_Fun_mapsto by blast
        thus ?thesis
          using x y h \<phi>_def HomD.\<psi>_mapsto [of y "G x"] HomC.\<phi>_mapsto [of "F y" x] by auto
      qed
      show "\<psi> x (\<phi> y h) = h"
      proof -
        have 0: "restrict (\<lambda>h. h) (HomC.set (F y, x))
                   = restrict (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) (HomC.set (F y, x))"
        proof -
          have 1: "S.ide (\<Psi> (y, x) \<cdot>\<^sub>S \<Phi> (y, x))"
            using x y \<Phi>\<Psi>.inv [of "(y, x)"] by auto
          hence 6: "S.seq (\<Psi> (y, x)) (\<Phi> (y, x))" by auto
          have 2: "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                      (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)) \<and>
                   \<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                      (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
            using x y \<Phi>_simp \<Psi>_simp by force
          have 3: "S (\<Psi> (y, x)) (\<Phi> (y, x))
                    = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                              (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x))"
          proof -
            have 4: "S.arr (\<Psi> (y, x) \<cdot>\<^sub>S \<Phi> (y, x))" using 1 by auto
            hence "S (\<Psi> (y, x)) (\<Phi> (y, x))
                     = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                               ((\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))
                                  o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))"
              using 1 2 S.ide_in_hom S.comp_mkArr by fastforce
            also have "... = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                                     (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x))"
            proof (intro S.mkArr_eqI')
              show "S.arr (S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                                   ((\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))
                                     o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))))"
                using 4 calculation by simp
              show "\<And>h. h \<in> HomC.set (F y, x) \<Longrightarrow>
                          ((\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))
                            o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))) h =
                          (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) h"
              proof -
                fix h
                assume h: "h \<in> HomC.set (F y, x)"
                hence "\<guillemotleft>\<phi> y (\<psi>C (F y, x) h) : y \<rightarrow>\<^sub>D G x\<guillemotright>"
                  using x y h HomC.\<psi>_mapsto [of "F y" x] \<phi>_mapsto by auto
                thus "((\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))
                            o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))) h =
                      (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) h"
                  using x y 1 \<phi>_mapsto HomD.\<psi>_\<phi> by simp
              qed
            qed
            finally show ?thesis by simp
          qed
          moreover have "\<Psi> (y, x) \<cdot>\<^sub>S \<Phi> (y, x)
                             = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x)) (\<lambda>h. h)"
            using 1 2 6 calculation S.mkIde_as_mkArr S.arr_mkArr S.dom_mkArr S.ideD(2)
            by metis
          ultimately have 4: "S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                                      (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x))
                                = S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x)) (\<lambda>h. h)"
            by auto
          have 5: "S.arr (S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                                  (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)))"
            using 1 3 6 by presburger
          hence "restrict (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) (HomC.set (F y, x))
                  = S.Fun (S.mkArr (HomC.set (F y, x)) (HomC.set (F y, x))
                         (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)))"
            by auto
          also have "... = restrict (\<lambda>h. h) (HomC.set (F y, x))"
            using 4 5 by auto
          finally show ?thesis by auto
        qed
        moreover have "\<phi>C (F y, x) h \<in> HomC.set (F y, x)"
          using x y h HomC.\<phi>_mapsto [of "F y" x] by auto
        ultimately have
            "\<phi>C (F y, x) h = (\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) (\<phi>C (F y, x) h)"
          using x y h HomC.\<phi>_mapsto [of "F y" x] by fast
        hence "\<psi>C (F y, x) (\<phi>C (F y, x) h) =
                 \<psi>C (F y, x) ((\<phi>C (F y, x) o (\<psi> x o \<phi> y) o \<psi>C (F y, x)) (\<phi>C (F y, x) h))"
          by simp
        hence "h = \<psi>C (F y, x) (\<phi>C (F y, x) (\<psi> x (\<phi> y (\<psi>C (F y, x) (\<phi>C (F y, x) h)))))"
          using x y h HomC.\<psi>_\<phi> [of "F y" x] by simp
        also have "... = \<psi> x (\<phi> y h)"
          using x y h HomC.\<psi>_\<phi> HomC.\<psi>_\<phi> \<phi>_mapsto \<psi>_mapsto
          by (metis PiE mem_Collect_eq)
        finally show ?thesis by auto
      qed
      next
      fix x :: 'c and h :: 'd and y :: 'd
      assume x: "C.ide x" and h: "\<guillemotleft>h : y \<rightarrow>\<^sub>D G x\<guillemotright>"
      have y: "D.ide y" using h by auto
      show "\<guillemotleft>\<psi> x h : F y \<rightarrow>\<^sub>C x\<guillemotright>" using x y h \<psi>_mapsto [of x y] by auto
      show "\<phi> y (\<psi> x h) = h"
      proof -
        have 0: "restrict (\<lambda>h. h) (HomD.set (y, G x))
                   = restrict (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) (HomD.set (y, G x))"
        proof -
          have 1: "S.ide (S (\<Phi> (y, x)) (\<Psi> (y, x)))"
            using x y \<Phi>\<Psi>.inv by force
          hence 6: "S.seq (\<Phi> (y, x)) (\<Psi> (y, x))" by auto
          have 2: "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                      (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)) \<and>
                   \<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                       (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
            using x h \<Phi>_simp \<Psi>_simp by auto
          have 3: "S (\<Phi> (y, x)) (\<Psi> (y, x))
                     = S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                               (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x))"
          proof -
            have 4: "S.seq (\<Phi> (y, x)) (\<Psi> (y, x))" using 1 by auto
            hence "S (\<Phi> (y, x)) (\<Psi> (y, x))
                     = S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                               ((\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))
                                 o (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x)))"
              using 1 2 6 S.ide_in_hom S.comp_mkArr by fastforce
            also have "... = S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                                     (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x))"
            proof
              show "S.arr (S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                                   ((\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))
                                     o (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))))"
                using 4 calculation by simp
              show "\<And>h. h \<in> HomD.set (y, G x) \<Longrightarrow>
                          ((\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))
                            o (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))) h =
                          (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) h"
              proof -
                fix h
                assume h: "h \<in> HomD.set (y, G x)"
                hence "\<guillemotleft>\<psi> x (\<psi>D (y, G x) h) : F y \<rightarrow>\<^sub>C x\<guillemotright>"
                  using x y HomD.\<psi>_mapsto [of y "G x"] \<psi>_mapsto by auto
                thus "((\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))
                            o (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))) h =
                      (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) h"
                  using x y HomC.\<psi>_\<phi> by simp
              qed
            qed
            finally show ?thesis by auto
          qed
          moreover have "\<Phi> (y, x) \<cdot>\<^sub>S \<Psi> (y, x) =
                           S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x)) (\<lambda>h. h)"
            using 1 2 6 calculation
            by (metis S.arr_mkArr S.cod_mkArr S.ide_in_hom S.mkIde_as_mkArr S.in_homE)
          ultimately have 4: "S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                                      (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x))
                                = S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x)) (\<lambda>h. h)"
            by auto
          have 5: "S.arr (S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                                  (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)))"
            using 1 3 by fastforce
          hence "restrict (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) (HomD.set (y, G x))
                  = S.Fun (S.mkArr (HomD.set (y, G x)) (HomD.set (y, G x))
                         (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)))"
            by auto
          also have "... = restrict (\<lambda>h. h) (HomD.set (y, G x))"
            using 4 5 by auto
          finally show ?thesis by auto
        qed
        moreover have "\<phi>D (y, G x) h \<in> HomD.set (y, G x)"
          using x y h HomD.\<phi>_mapsto [of y "G x"] by auto
        ultimately have
            "\<phi>D (y, G x) h = (\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) (\<phi>D (y, G x) h)"
          by fast
        hence "\<psi>D (y, G x) (\<phi>D (y, G x) h) =
                \<psi>D (y, G x) ((\<phi>D (y, G x) o (\<phi> y o \<psi> x) o \<psi>D (y, G x)) (\<phi>D (y, G x) h))"
          by simp
        hence "h = \<psi>D (y, G x) (\<phi>D (y, G x) (\<phi> y (\<psi> x (\<psi>D (y, G x) (\<phi>D (y, G x) h)))))"
          using x y h HomD.\<psi>_\<phi> by simp
        also have "... = \<phi> y (\<psi> x h)"
          using x y h HomD.\<psi>_\<phi> HomD.\<psi>_\<phi> [of "\<phi> y (\<psi> x h)" y "G x"] \<phi>_mapsto \<psi>_mapsto
          by fastforce
        finally show ?thesis by auto
      qed
      next
      fix x :: 'c and x' :: 'c and y :: 'd and y' :: 'd
      and f :: 'c and g :: 'd and h :: 'c
      assume f: "\<guillemotleft>f : x \<rightarrow>\<^sub>C x'\<guillemotright>" and g: "\<guillemotleft>g : y' \<rightarrow>\<^sub>D y\<guillemotright>" and h: "\<guillemotleft>h : F y \<rightarrow>\<^sub>C x\<guillemotright>"
      have x: "C.ide x" using f by auto
      have y: "D.ide y" using g by auto
      have x': "C.ide x'" using f by auto
      have y': "D.ide y'" using g by auto
      show "\<phi> y' (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) = G f \<cdot>\<^sub>D \<phi> y h \<cdot>\<^sub>D g"
      proof -
        have 0: "restrict ((\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x))
                           o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                       (HomC.set (F y, x))
                = restrict ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                             o (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g)) o \<psi>C (F y, x))
                           (HomC.set (F y, x))"
        proof -
          have 1: "S.arr (\<Phi> (y, x)) \<and>
                   \<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                      (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
                using x y \<Phi>_simp [of y x] by auto
          have 2: "S.arr (\<Phi> (y', x')) \<and>
                   \<Phi> (y', x') = S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x'))
                                        (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))"
                using x' y' \<Phi>_simp [of y' x'] by auto
          have 3: "S.arr (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                  ((\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x))
                                    o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))))
                   \<and> S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                             ((\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x))
                               o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                     = S (S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                  (\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x)))
                         (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                  (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))"
          proof -
            have 1: "S.seq (S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                  (\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x)))
                           (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                  (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))"
            proof -
              have "S.arr (Hom_DopxG.map (g, f)) \<and>
                    Hom_DopxG.map (g, f)
                        = S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                  (\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x))"
                using f g Hom_DopxG.preserves_arr Hom_DopxG_map_simp by fastforce
              thus ?thesis
                using 1 S.cod_mkArr S.dom_mkArr S.seqI by metis
            qed
            have "S.seq (S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                 (\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x)))
                        (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                 (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))"
              using 1 by (intro S.seqI', auto)
            moreover have "S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                             ((\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x))
                               o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                             = S (S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                          (\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x)))
                                 (S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                                          (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))"
              using 1 S.comp_mkArr by fastforce
            ultimately show ?thesis by auto
          qed
          moreover have
             4: "S.arr (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                                  o (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x))))
                 \<and> S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                           ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                             o (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x)))
                     = S (S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x')) 
                                  (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x')))
                         (S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                  (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x)))"
          proof -
            have 5: "S.seq (S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x'))
                                    (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x')))
                           (S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                    (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x)))"
            proof -
              have "S.arr (Hom_FopxC.map (g, f)) \<and>
                    Hom_FopxC.map (g, f)
                          = S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                    (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x))"
                using f g Hom_FopxC.preserves_arr Hom_FopxC_map_simp by fastforce
              thus ?thesis using 2 S.cod_mkArr S.dom_mkArr S.seqI by metis
            qed
            have "S.seq (S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x'))
                                 (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x')))
                        (S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                 (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x)))"
              using 5 by (intro S.seqI', auto)
            moreover have "S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                   ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                                     o (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x)))
                             = S (S.mkArr (HomC.set (F y', x')) (HomD.set (y', G x'))
                                          (\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x')))
                                 (S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                          (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x)))"
              using 5 S.comp_mkArr by fastforce
            ultimately show ?thesis by argo
          qed
          moreover have 2:
              "S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                       ((\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x))
                         o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                  = S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                            ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                              o (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x)))"
          proof -
            have
              "S (Hom_DopxG.map (g, f)) (\<Phi> (y, x)) = S (\<Phi> (y', x')) (Hom_FopxC.map (g, f))"
              using f g \<Phi>.naturality1 \<Phi>.naturality2 by fastforce
            moreover have "Hom_DopxG.map (g, f)
                             = S.mkArr (HomD.set (y, G x)) (HomD.set (y', G x'))
                                       (\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x))"
              using f g Hom_DopxG_map_simp [of "(g, f)"] by fastforce
            moreover have "Hom_FopxC.map (g, f)
                             = S.mkArr (HomC.set (F y, x)) (HomC.set (F y', x'))
                                       (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x))"
              using f g Hom_FopxC_map_simp [of "(g, f)"] by fastforce
            ultimately show ?thesis using 1 2 3 4 by simp
          qed
          ultimately have 6: "S.arr (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                             ((\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x))
                                               o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))))"
            by fast
          hence "restrict ((\<phi>D (y', G x') o (\<lambda>h. D (G f) (D h g)) o \<psi>D (y, G x))
                            o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x)))
                          (HomC.set (F y, x))
                  = S.Fun (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                  ((\<phi>D (y', G x') o (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) o \<psi>D (y, G x))
                                    o (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))))"
            by simp
          also have "... = S.Fun (S.mkArr (HomC.set (F y, x)) (HomD.set (y', G x'))
                                       ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                                         o (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x))))"
            using 2 by argo
          also have "... = restrict ((\<phi>D (y', G x') o \<phi> y' o \<psi>C (F y', x'))
                                      o (\<phi>C (F y', x') o (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x)))
                                    (HomC.set (F y, x))"
            using 4 S.Fun_mkArr by meson
          finally show ?thesis by auto
        qed
        hence 5: "((\<phi>D (y', G x') \<circ> (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) \<circ> \<psi>D (y, G x))
                    \<circ> (\<phi>D (y, G x) \<circ> \<phi> y \<circ> \<psi>C (F y, x))) (\<phi>C (F y, x) h) =
                   (\<phi>D (y', G x') \<circ> \<phi> y' \<circ> \<psi>C (F y', x')
                     \<circ> (\<phi>C (F y', x') \<circ> (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g)) \<circ> \<psi>C (F y, x)) (\<phi>C (F y, x) h)"
        proof -
          have "\<phi>C (F y, x) h \<in> HomC.set (F y, x)"
            using x y h HomC.\<phi>_mapsto [of "F y" x] by auto
          thus ?thesis
            using 0 h restr_eqE [of "(\<phi>D (y', G x') \<circ> (\<lambda>h. G f \<cdot>\<^sub>D h \<cdot>\<^sub>D g) \<circ> \<psi>D (y, G x))
                                      \<circ> (\<phi>D (y, G x) \<circ> \<phi> y \<circ> \<psi>C (F y, x))"
                                    "HomC.set (F y, x)"
                                    "(\<phi>D (y', G x') \<circ> \<phi> y' \<circ> \<psi>C (F y', x'))
                                       \<circ> (\<phi>C (F y', x') \<circ> (\<lambda>h. f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) o \<psi>C (F y, x))"]
            by fast
        qed
        show ?thesis
        proof -
          have "\<phi> y' (C f (C h (F g))) =
                  \<psi>D (y', G x') (\<phi>D (y', G x') (\<phi> y' (\<psi>C (F y', x') (\<phi>C (F y', x')
                     (C f (C (\<psi>C (F y, x) (\<phi>C (F y, x) h)) (F g)))))))"
          proof -
            have "\<psi>D (y', G x') (\<phi>D (y', G x') (\<phi> y' (\<psi>C (F y', x') (\<phi>C (F y', x')
                     (C f (C (\<psi>C (F y, x) (\<phi>C (F y, x) h)) (F g)))))))
                    = \<psi>D (y', G x') (\<phi>D (y', G x') (\<phi> y' (\<psi>C (F y', x') (\<phi>C (F y', x')
                         (C f (C h (F g)))))))"
              using x y h HomC.\<psi>_\<phi> by simp
            also have "... = \<psi>D (y', G x') (\<phi>D (y', G x') (\<phi> y' (C f (C h (F g)))))"
              using f g h HomC.\<psi>_\<phi> [of "C f (C h (F g))"] by fastforce
            also have "... = \<phi> y' (C f (C h (F g)))"
            proof -
              have "\<guillemotleft>\<phi> y' (f \<cdot>\<^sub>C h \<cdot>\<^sub>C F g) : y' \<rightarrow>\<^sub>D G x'\<guillemotright>"
                using f g h y' x' \<phi>_mapsto [of y' x'] by auto
              thus ?thesis by simp
            qed
            finally show ?thesis by auto
          qed
          also have
             "... = \<psi>D (y', G x')
                       (\<phi>D (y', G x')
                           (G f \<cdot>\<^sub>D \<psi>D (y, G x) (\<phi>D (y, G x) (\<phi> y (\<psi>C (F y, x) (\<phi>C (F y, x) h))))
                                \<cdot>\<^sub>D g))"
            using 5 by force
          also have "... = D (G f) (D (\<phi> y h) g)"
          proof -
            have \<phi>yh: "\<guillemotleft>\<phi> y h : y \<rightarrow>\<^sub>D G x\<guillemotright>"
              using x y h \<phi>_mapsto by auto
            have "\<psi>D (y', G x')
                     (\<phi>D (y', G x')
                         (G f \<cdot>\<^sub>D \<psi>D (y, G x) (\<phi>D (y, G x) (\<phi> y (\<psi>C (F y, x) (\<phi>C (F y, x) h))))
                              \<cdot>\<^sub>D g)) =
                  \<psi>D (y', G x') (\<phi>D (y', G x') (G f \<cdot>\<^sub>D \<psi>D (y, G x) (\<phi>D (y, G x) (\<phi> y h)) \<cdot>\<^sub>D g))"
              using x y f g h by auto
            also have "... = \<psi>D (y', G x') (\<phi>D (y', G x') (G f \<cdot>\<^sub>D \<phi> y h \<cdot>\<^sub>D g))"
              using \<phi>yh x' y' f g by simp
            also have "... = G f \<cdot>\<^sub>D \<phi> y h \<cdot>\<^sub>D g"
              using \<phi>yh f g by fastforce
            finally show ?thesis by auto
          qed
          finally show ?thesis by auto
        qed
      qed
    qed

    theorem induces_meta_adjunction:
    shows "meta_adjunction C D F G \<phi> \<psi>" ..

  end

  section "Putting it All Together"

  text\<open>
    Combining the above results, an interpretation of any one of the locales:
    \<open>left_adjoint_functor\<close>, \<open>right_adjoint_functor\<close>, \<open>meta_adjunction\<close>,
    \<open>hom_adjunction\<close>, and \<open>unit_counit_adjunction\<close> extends to an interpretation
    of \<open>adjunction\<close>.
\<close>

  context meta_adjunction
  begin

    interpretation S: replete_setcat .
    interpretation F: left_adjoint_functor D C F using has_left_adjoint_functor by auto
    interpretation G: right_adjoint_functor C D G using has_right_adjoint_functor by auto

    interpretation \<eta>\<epsilon>: unit_counit_adjunction C D F G \<eta> \<epsilon>
      using induces_unit_counit_adjunction \<eta>_def \<epsilon>_def by auto
    interpretation \<Phi>\<Psi>: hom_adjunction C D S.comp S.setp \<phi>C \<phi>D F G \<Phi> \<Psi>
      using induces_hom_adjunction by auto

    theorem induces_adjunction:
    shows "adjunction C D S.comp S.setp \<phi>C \<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<Phi> \<Psi>"
      using \<epsilon>_map_simp \<eta>_map_simp \<phi>_in_terms_of_\<eta> \<phi>_in_terms_of_\<Phi>' \<psi>_in_terms_of_\<epsilon>
            \<psi>_in_terms_of_\<Psi>' \<Phi>_simp \<Psi>_simp \<eta>_def \<epsilon>_def
      by unfold_locales auto

  end

  context unit_counit_adjunction
  begin

    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi> using induces_meta_adjunction by auto

    interpretation S: replete_setcat .
    interpretation F: left_adjoint_functor D C F using \<phi>\<psi>.has_left_adjoint_functor by auto
    interpretation G: right_adjoint_functor C D G using \<phi>\<psi>.has_right_adjoint_functor by auto

    interpretation \<Phi>\<Psi>: hom_adjunction C D S.comp S.setp
                          \<phi>\<psi>.\<phi>C \<phi>\<psi>.\<phi>D F G \<phi>\<psi>.\<Phi> \<phi>\<psi>.\<Psi>
      using \<phi>\<psi>.induces_hom_adjunction by auto

    theorem induces_adjunction:
    shows "adjunction C D S.comp S.setp \<phi>\<psi>.\<phi>C \<phi>\<psi>.\<phi>D F G \<phi> \<psi> \<eta> \<epsilon> \<phi>\<psi>.\<Phi> \<phi>\<psi>.\<Psi>"
      using \<epsilon>_in_terms_of_\<psi> \<eta>_in_terms_of_\<phi> \<phi>\<psi>.\<phi>_in_terms_of_\<Phi>' \<psi>_def \<phi>\<psi>.\<psi>_in_terms_of_\<Psi>'
            \<phi>\<psi>.\<Phi>_simp \<phi>\<psi>.\<Psi>_simp \<phi>_def
      by unfold_locales auto

  end

  context hom_adjunction
  begin
   
    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi>
      using induces_meta_adjunction by auto
    interpretation F: left_adjoint_functor D C F using \<phi>\<psi>.has_left_adjoint_functor by auto
    interpretation G: right_adjoint_functor C D G using \<phi>\<psi>.has_right_adjoint_functor by auto
    interpretation \<eta>\<epsilon>: unit_counit_adjunction C D F G \<phi>\<psi>.\<eta> \<phi>\<psi>.\<epsilon>
      using \<phi>\<psi>.induces_unit_counit_adjunction \<phi>\<psi>.\<eta>_def \<phi>\<psi>.\<epsilon>_def by auto

    theorem induces_adjunction:
    shows "adjunction C D S setp \<phi>C \<phi>D F G \<phi> \<psi> \<phi>\<psi>.\<eta> \<phi>\<psi>.\<epsilon> \<Phi> \<Psi>"
    proof
      fix x
      assume "C.ide x"
      thus "\<phi>\<psi>.\<epsilon> x = \<psi> x (G x)"
        using \<phi>\<psi>.\<epsilon>_map_simp \<phi>\<psi>.\<epsilon>_def by simp
      next
      fix y
      assume "D.ide y"
      thus "\<phi>\<psi>.\<eta> y = \<phi> y (F y)"
        using \<phi>\<psi>.\<eta>_map_simp \<phi>\<psi>.\<eta>_def by simp
      fix x y f
      assume y: "D.ide y" and f: "\<guillemotleft>f : F y \<rightarrow>\<^sub>C x\<guillemotright>"
      show "\<phi> y f = G f \<cdot>\<^sub>D \<phi>\<psi>.\<eta> y"
        using y f \<phi>\<psi>.\<phi>_in_terms_of_\<eta> \<phi>\<psi>.\<eta>_def by simp
      show "\<phi> y f = (\<psi>D (y, G x) \<circ> \<Phi>.FUN (y, x) \<circ> \<phi>C (F y, x)) f"
        using y f \<phi>_def by auto
      next
      fix x y g
      assume x: "C.ide x" and g: "\<guillemotleft>g : y \<rightarrow>\<^sub>D G x\<guillemotright>"
      show "\<psi> x g = \<phi>\<psi>.\<epsilon> x \<cdot>\<^sub>C F g"
        using x g \<phi>\<psi>.\<psi>_in_terms_of_\<epsilon> \<phi>\<psi>.\<epsilon>_def by simp
      show "\<psi> x g = (\<psi>C (F y, x) \<circ> \<Psi>.FUN (y, x) \<circ> \<phi>D (y, G x)) g"
        using x g \<psi>_def by fast
      next
      fix x y
      assume x: "C.ide x" and y: "D.ide y"
      show "\<Phi> (y, x) = S.mkArr (HomC.set (F y, x)) (HomD.set (y, G x))
                               (\<phi>D (y, G x) o \<phi> y o \<psi>C (F y, x))"
        using x y \<Phi>_simp by simp
      show "\<Psi> (y, x) = S.mkArr (HomD.set (y, G x)) (HomC.set (F y, x))
                                (\<phi>C (F y, x) o \<psi> x o \<psi>D (y, G x))"
        using x y \<Psi>_simp by simp
    qed

  end

  context left_adjoint_functor
  begin

    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi>
      using induces_meta_adjunction by auto
    interpretation S: replete_setcat .

    theorem induces_adjunction:
    shows "adjunction C D S.comp S.setp \<phi>\<psi>.\<phi>C \<phi>\<psi>.\<phi>D F G \<phi> \<psi> \<phi>\<psi>.\<eta> \<phi>\<psi>.\<epsilon> \<phi>\<psi>.\<Phi> \<phi>\<psi>.\<Psi>"
      using \<phi>\<psi>.induces_adjunction by auto

  end

  context right_adjoint_functor
  begin

    interpretation \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi>
      using induces_meta_adjunction by auto
    interpretation S: replete_setcat .

    theorem induces_adjunction:
    shows "adjunction C D S.comp S.setp \<phi>\<psi>.\<phi>C \<phi>\<psi>.\<phi>D F G \<phi> \<psi> \<phi>\<psi>.\<eta> \<phi>\<psi>.\<epsilon> \<phi>\<psi>.\<Phi> \<phi>\<psi>.\<Psi>"
      using \<phi>\<psi>.induces_adjunction by auto

  end

  definition adjoint_functors
  where "adjoint_functors C D F G = (\<exists>\<phi> \<psi>. meta_adjunction C D F G \<phi> \<psi>)"

  lemma adjoint_functors_respects_naturally_isomorphic:
  assumes "adjoint_functors C D F G"
  and "naturally_isomorphic D C F' F" and "naturally_isomorphic C D G G'"
  shows "adjoint_functors C D F' G'"
  proof -
    obtain \<phi> \<psi> where \<phi>\<psi>: "meta_adjunction C D F G \<phi> \<psi>"
      using assms(1) adjoint_functors_def by blast
    interpret \<phi>\<psi>: meta_adjunction C D F G \<phi> \<psi>
      using \<phi>\<psi> by simp
    obtain \<tau> where \<tau>: "natural_isomorphism D C F' F \<tau>"
      using assms(2) naturally_isomorphic_def by blast
    obtain \<mu> where \<mu>: "natural_isomorphism C D G G' \<mu>"
      using assms(3) naturally_isomorphic_def by blast
    show ?thesis
      using adjoint_functors_def \<tau> \<mu> \<phi>\<psi>.respects_natural_isomorphism by blast
  qed

  lemma left_adjoint_functor_respects_naturally_isomorphic:
  assumes "left_adjoint_functor D C F"
  and "naturally_isomorphic D C F F'"
  shows "left_adjoint_functor D C F'"
  proof -
    interpret F: left_adjoint_functor D C F
      using assms(1) by simp
    have 1: "meta_adjunction C D F F.G F.\<phi> F.\<psi>"
      using F.induces_meta_adjunction by simp
    interpret \<phi>\<psi>: meta_adjunction C D F F.G F.\<phi> F.\<psi>
      using 1 by simp
    have "adjoint_functors C D F F.G"
      using 1 adjoint_functors_def by blast
    hence 2: "adjoint_functors C D F' F.G"
      using assms(2) adjoint_functors_respects_naturally_isomorphic [of C D F F.G F' F.G]
            naturally_isomorphic_reflexive naturally_isomorphic_symmetric
            \<phi>\<psi>.G.functor_axioms
      by blast
    obtain \<phi>' \<psi>' where \<phi>'\<psi>': "meta_adjunction C D F' F.G \<phi>' \<psi>'"
      using 2 adjoint_functors_def by blast
    interpret \<phi>'\<psi>': meta_adjunction C D F' F.G \<phi>' \<psi>'
      using \<phi>'\<psi>' by simp
    show ?thesis
      using \<phi>'\<psi>'.has_left_adjoint_functor by simp
  qed

  lemma right_adjoint_functor_respects_naturally_isomorphic:
  assumes "right_adjoint_functor C D G"
  and "naturally_isomorphic C D G G'"
  shows "right_adjoint_functor C D G'"
  proof -
    interpret G: right_adjoint_functor C D G
      using assms(1) by simp
    have 1: "meta_adjunction C D G.F G G.\<phi> G.\<psi>"
      using G.induces_meta_adjunction by simp
    interpret \<phi>\<psi>: meta_adjunction C D G.F G G.\<phi> G.\<psi>
      using 1 by simp
    have "adjoint_functors C D G.F G"
      using 1 adjoint_functors_def by blast
    hence 2: "adjoint_functors C D G.F G'"
      using assms(2) adjoint_functors_respects_naturally_isomorphic
            naturally_isomorphic_reflexive naturally_isomorphic_symmetric
            \<phi>\<psi>.F.functor_axioms
      by blast
    obtain \<phi>' \<psi>' where \<phi>'\<psi>': "meta_adjunction C D G.F G' \<phi>' \<psi>'"
      using 2 adjoint_functors_def by blast
    interpret \<phi>'\<psi>': meta_adjunction C D G.F G' \<phi>' \<psi>'
      using \<phi>'\<psi>' by simp
    show ?thesis
      using \<phi>'\<psi>'.has_right_adjoint_functor by simp
  qed

  section "Inverse Functors are Adjoints"

  (* TODO: This really should show that inverse functors induce an adjoint equivalence. *)

  lemma inverse_functors_induce_meta_adjunction:
  assumes "inverse_functors C D F G"
  shows "meta_adjunction C D F G (\<lambda>x. G) (\<lambda>y. F)"
  proof -
    interpret inverse_functors C D F G using assms by auto
    interpret meta_adjunction C D F G \<open>\<lambda>x. G\<close> \<open>\<lambda>y. F\<close>
    proof -
      have 1: "\<And>y. B.arr y \<Longrightarrow> G (F y) = y"
        by (metis B.map_simp comp_apply inv)
      have 2: "\<And>x. A.arr x \<Longrightarrow> F (G x) = x"
        by (metis A.map_simp comp_apply inv')
      show "meta_adjunction C D F G (\<lambda>x. G) (\<lambda>y. F)"
      proof
        fix y f x
        assume y: "B.ide y" and f: "\<guillemotleft>f : F y \<rightarrow>\<^sub>A x\<guillemotright>"
        show "\<guillemotleft>G f : y \<rightarrow>\<^sub>B G x\<guillemotright>"
          using y f 1 G.preserves_hom by (elim A.in_homE, auto)
        show "F (G f) = f"
          using f 2 by auto
        next
        fix x g y
        assume x: "A.ide x" and g: "\<guillemotleft>g : y \<rightarrow>\<^sub>B G x\<guillemotright>"
        show "\<guillemotleft>F g : F y \<rightarrow>\<^sub>A x\<guillemotright>"
          using x g 2 F.preserves_hom by (elim B.in_homE, auto)
        show "G (F g) = g" using g 1 A.map_def by blast
        next
        fix f x x' g y' y h
        assume f: "\<guillemotleft>f : x \<rightarrow>\<^sub>A x'\<guillemotright>" and g: "\<guillemotleft>g : y' \<rightarrow>\<^sub>B y\<guillemotright>" and h: "\<guillemotleft>h : F y \<rightarrow>\<^sub>A x\<guillemotright>"
        show "G (C f (C h (F g))) = D (G f) (D (G h) g)"
          using f g h 1 2 inv inv' A.map_def B.map_def by (elim A.in_homE B.in_homE, auto)
      qed
    qed
    show ?thesis ..
  qed

  lemma inverse_functors_are_adjoints:
  assumes "inverse_functors A B F G"
  shows "adjoint_functors A B F G"
    using assms inverse_functors_induce_meta_adjunction adjoint_functors_def by fast

  context inverse_functors
  begin

    lemma \<eta>_char:
    shows "meta_adjunction.\<eta> B F (\<lambda>x. G) = identity_functor.map B"
    proof (intro natural_transformation_eqI)
      interpret meta_adjunction A B F G \<open>\<lambda>y. G\<close> \<open>\<lambda>x. F\<close>
        using inverse_functors_induce_meta_adjunction inverse_functors_axioms by auto
      interpret S: replete_setcat .
      interpret adjunction A B S.comp S.setp \<phi>C \<phi>D F G \<open>\<lambda>y. G\<close> \<open>\<lambda>x. F\<close> \<eta> \<epsilon> \<Phi> \<Psi>
        using induces_adjunction by force
      show "natural_transformation B B B.map GF.map \<eta>"
        using \<eta>.natural_transformation_axioms by auto
      show "natural_transformation B B B.map GF.map B.map"
        by (simp add: B.as_nat_trans.natural_transformation_axioms inv)
      show "\<And>b. B.ide b \<Longrightarrow> \<eta> b = B.map b"
        using \<eta>_in_terms_of_\<phi> \<eta>o_def \<eta>o_in_hom by fastforce
    qed

    lemma \<epsilon>_char:
    shows "meta_adjunction.\<epsilon> A F G (\<lambda>y. F) = identity_functor.map A"
    proof (intro natural_transformation_eqI)
      interpret meta_adjunction A B F G \<open>\<lambda>y. G\<close> \<open>\<lambda>x. F\<close>
        using inverse_functors_induce_meta_adjunction inverse_functors_axioms by auto
      interpret S: replete_setcat .
      interpret adjunction A B S.comp S.setp \<phi>C \<phi>D F G \<open>\<lambda>y. G\<close> \<open>\<lambda>x. F\<close> \<eta> \<epsilon> \<Phi> \<Psi>
        using induces_adjunction by force
      show "natural_transformation A A FG.map A.map \<epsilon>"
        using \<epsilon>.natural_transformation_axioms by auto
      show "natural_transformation A A FG.map A.map A.map"
        by (simp add: A.as_nat_trans.natural_transformation_axioms inv')
      show "\<And>a. A.ide a \<Longrightarrow> \<epsilon> a = A.map a"
        using \<epsilon>_in_terms_of_\<psi> \<epsilon>o_def \<epsilon>o_in_hom by fastforce
    qed

  end

  section "Composition of Adjunctions"

  locale composite_adjunction =
    A: category A +
    B: category B +
    C: category C +
    F: "functor" B A F +
    G: "functor" A B G +
    F': "functor" C B F' +
    G': "functor" B C G' +
    FG: meta_adjunction A B F G \<phi> \<psi> +
    F'G': meta_adjunction B C F' G' \<phi>' \<psi>'
  for A :: "'a comp"     (infixr \<open>\<cdot>\<^sub>A\<close> 55)
  and B :: "'b comp"     (infixr \<open>\<cdot>\<^sub>B\<close> 55)
  and C :: "'c comp"     (infixr \<open>\<cdot>\<^sub>C\<close> 55)
  and F :: "'b \<Rightarrow> 'a"
  and G :: "'a \<Rightarrow> 'b"
  and F' :: "'c \<Rightarrow> 'b"
  and G' :: "'b \<Rightarrow> 'c"
  and \<phi> :: "'b \<Rightarrow> 'a \<Rightarrow> 'b"
  and \<psi> :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"
  and \<phi>' :: "'c \<Rightarrow> 'b \<Rightarrow> 'c"
  and \<psi>' :: "'b \<Rightarrow> 'c \<Rightarrow> 'b"
  begin

    interpretation S: replete_setcat .
    interpretation FG: adjunction A B S.comp S.setp
                           FG.\<phi>C FG.\<phi>D F G \<phi> \<psi> FG.\<eta> FG.\<epsilon> FG.\<Phi> FG.\<Psi>
      using FG.induces_adjunction by simp
    interpretation F'G': adjunction B C S.comp S.setp F'G'.\<phi>C F'G'.\<phi>D F' G' \<phi>' \<psi>'
                           F'G'.\<eta> F'G'.\<epsilon> F'G'.\<Phi> F'G'.\<Psi>
      using F'G'.induces_adjunction by simp

    (* Notation for C.in_hom is inherited here somehow, but I don't know from where. *)

    lemma is_meta_adjunction:
    shows "meta_adjunction A C (F o F') (G' o G) (\<lambda>z. \<phi>' z o \<phi> (F' z)) (\<lambda>x. \<psi> x o \<psi>' (G x))"
    proof -
      interpret G'oG: composite_functor A B C G G' ..
      interpret FoF': composite_functor C B A F' F ..
      show ?thesis
      proof
        fix y f x
        assume y: "C.ide y" and f: "\<guillemotleft>f : FoF'.map y \<rightarrow>\<^sub>A x\<guillemotright>"
        show "\<guillemotleft>(\<phi>' y \<circ> \<phi> (F' y)) f : y \<rightarrow>\<^sub>C G'oG.map x\<guillemotright>"
          using y f FG.\<phi>_in_hom F'G'.\<phi>_in_hom by simp
        show "(\<psi> x \<circ> \<psi>' (G x)) ((\<phi>' y \<circ> \<phi> (F' y)) f) = f"
          using y f FG.\<phi>_in_hom F'G'.\<phi>_in_hom FG.\<psi>_\<phi> F'G'.\<psi>_\<phi> by simp
        next
        fix x g y
        assume x: "A.ide x" and g: "\<guillemotleft>g : y \<rightarrow>\<^sub>C G'oG.map x\<guillemotright>"
        show "\<guillemotleft>(\<psi> x \<circ> \<psi>' (G x)) g : FoF'.map y \<rightarrow>\<^sub>A x\<guillemotright>"
          using x g FG.\<psi>_in_hom F'G'.\<psi>_in_hom by auto
        show "(\<phi>' y \<circ> \<phi> (F' y)) ((\<psi> x \<circ> \<psi>' (G x)) g) = g"
          using x g FG.\<psi>_in_hom F'G'.\<psi>_in_hom FG.\<phi>_\<psi> F'G'.\<phi>_\<psi> by simp
        next
        fix f x x' g y' y h
        assume f: "\<guillemotleft>f : x \<rightarrow>\<^sub>A x'\<guillemotright>" and g: "\<guillemotleft>g : y' \<rightarrow>\<^sub>C y\<guillemotright>" and h: "\<guillemotleft>h : FoF'.map y \<rightarrow>\<^sub>A x\<guillemotright>"
        show "(\<phi>' y' \<circ> \<phi> (F' y')) (f \<cdot>\<^sub>A h \<cdot>\<^sub>A FoF'.map g) =
              G'oG.map f \<cdot>\<^sub>C (\<phi>' y \<circ> \<phi> (F' y)) h \<cdot>\<^sub>C g"
          using f g h FG.\<phi>_naturality [of f x x' "F' g" "F' y'" "F' y" h]
                F'G'.\<phi>_naturality [of "G f" "G x" "G x'" g y' y "\<phi> (F' y) h"]
                FG.\<phi>_in_hom
          by fastforce
      qed
    qed

    interpretation K\<eta>H: natural_transformation C C \<open>G' o F'\<close> \<open>G' o G o F o F'\<close>
                          \<open>G' o FG.\<eta> o F'\<close>
    proof -
      interpret \<eta>F': natural_transformation C B F' \<open>(G o F) o F'\<close> \<open>FG.\<eta> o F'\<close>
        using FG.\<eta>_naturalitytransformation F'.as_nat_trans.natural_transformation_axioms
              horizontal_composite
        by fastforce
      interpret G'\<eta>F': natural_transformation C C \<open>G' o F'\<close> \<open>G' o (G o F o F')\<close>
                         \<open>G' o (FG.\<eta> o F')\<close>
        using \<eta>F'.natural_transformation_axioms G'.as_nat_trans.natural_transformation_axioms
              horizontal_composite
        by blast
      show "natural_transformation C C (G' o F') (G' o G o F o F') (G' o FG.\<eta> o F')"
        using G'\<eta>F'.natural_transformation_axioms o_assoc by metis
    qed
    interpretation G'\<eta>F'o\<eta>': vertical_composite C C C.map \<open>G' o F'\<close> \<open>G' o G o F o F'\<close>
                             F'G'.\<eta> \<open>G' o FG.\<eta> o F'\<close> ..

    interpretation F\<epsilon>G: natural_transformation A A \<open>F o F' o G' o G\<close> \<open>F o G\<close>
                          \<open>F o F'G'.\<epsilon> o G\<close>
    proof -
      interpret F\<epsilon>': natural_transformation B A \<open>F o (F' o G')\<close> F \<open>F o F'G'.\<epsilon>\<close>
        using F'G'.\<epsilon>.natural_transformation_axioms F.as_nat_trans.natural_transformation_axioms
              horizontal_composite
        by fastforce
      interpret F\<epsilon>'G: natural_transformation A A \<open>F o (F' o G') o G\<close> \<open>F o G\<close> \<open>F o F'G'.\<epsilon> o G\<close>
        using F\<epsilon>'.natural_transformation_axioms G.as_nat_trans.natural_transformation_axioms
              horizontal_composite
        by blast
      show "natural_transformation A A (F o F' o G' o G) (F o G) (F o F'G'.\<epsilon> o G)"
        using F\<epsilon>'G.natural_transformation_axioms o_assoc by metis
    qed
    interpretation \<epsilon>oF\<epsilon>'G: vertical_composite A A \<open>F \<circ> F' \<circ> G' \<circ> G\<close> \<open>F o G\<close> A.map
                             \<open>F o F'G'.\<epsilon> o G\<close> FG.\<epsilon> ..

    interpretation meta_adjunction A C \<open>F o F'\<close> \<open>G' o G\<close>
                                   \<open>\<lambda>z. \<phi>' z o \<phi> (F' z)\<close> \<open>\<lambda>x. \<psi> x o \<psi>' (G x)\<close>
      using is_meta_adjunction by auto
    interpretation S: replete_setcat .
    interpretation adjunction A C S.comp S.setp \<phi>C \<phi>D \<open>F \<circ> F'\<close> \<open>G' \<circ> G\<close>
                     \<open>\<lambda>z. \<phi>' z \<circ> \<phi> (F' z)\<close> \<open>\<lambda>x. \<psi> x \<circ> \<psi>' (G x)\<close> \<eta> \<epsilon> \<Phi> \<Psi>
      using induces_adjunction by simp

    lemma \<eta>_char:
    shows "\<eta> = G'\<eta>F'o\<eta>'.map"
    proof (intro natural_transformation_eqI)
      show "natural_transformation C C C.map (G' o G o F o F') G'\<eta>F'o\<eta>'.map" ..
      show "natural_transformation C C C.map (G' o G o F o F') \<eta>"
        by (metis (no_types, lifting) \<eta>_naturalitytransformation o_assoc)
      fix a
      assume a: "C.ide a"
      show "\<eta> a = G'\<eta>F'o\<eta>'.map a"
        unfolding \<eta>_def
        using a G'\<eta>F'o\<eta>'.map_def FG.\<eta>.preserves_hom [of "F' a" "F' a" "F' a"]
              F'G'.\<phi>_in_terms_of_\<eta> FG.\<eta>_map_simp \<eta>_map_simp [of a] C.ide_in_hom
              F'G'.\<eta>_def FG.\<eta>_def
        by auto
    qed

    lemma \<epsilon>_char:
    shows "\<epsilon> = \<epsilon>oF\<epsilon>'G.map"
    proof (intro natural_transformation_eqI)
      show "natural_transformation A A (F o F' o G' o G) A.map \<epsilon>"
        by (metis (no_types, lifting) \<epsilon>_naturalitytransformation o_assoc)
      show "natural_transformation A A (F \<circ> F' \<circ> G' \<circ> G) A.map \<epsilon>oF\<epsilon>'G.map" ..
      fix a
      assume a: "A.ide a"
      show "\<epsilon> a = \<epsilon>oF\<epsilon>'G.map a"
      proof -
        have "\<epsilon> a = \<psi> a (\<psi>' (G a) (G' (G a)))"
          using a \<epsilon>_in_terms_of_\<psi> by simp
        also have "... = FG.\<epsilon> a \<cdot>\<^sub>A F (F'G'.\<epsilon> (G a) \<cdot>\<^sub>B F' (G' (G a)))"
          by (metis F'G'.\<epsilon>_in_terms_of_\<psi> F'G'.\<epsilon>o_def F'G'.\<epsilon>o_in_hom F'G'.\<eta>\<epsilon>.\<epsilon>_in_terms_of_\<psi>
              F'G'.\<eta>\<epsilon>.\<psi>_def FG.G\<epsilon>.natural_transformation_axioms FG.\<psi>_in_terms_of_\<epsilon> a
              functor.preserves_ide natural_transformation_def)
        also have "... = \<epsilon>oF\<epsilon>'G.map a"
          using a B.comp_arr_dom \<epsilon>oF\<epsilon>'G.map_def by simp
        finally show ?thesis by blast
      qed
    qed

  end

  section "Right Adjoints are Unique up to Natural Isomorphism"

  text\<open>
    As an example of the use of the of the foregoing development, we show that two right adjoints
    to the same functor are naturally isomorphic.
\<close>

  theorem two_right_adjoints_naturally_isomorphic:
  assumes "adjoint_functors C D F G" and "adjoint_functors C D F G'"
  shows "naturally_isomorphic C D G G'"
  proof -
    text\<open>
      For any object @{term x} of @{term C}, we have that \<open>\<epsilon> x \<in> C.hom (F (G x)) x\<close>
      is a terminal arrow from @{term F} to @{term x}, and similarly for \<open>\<epsilon>' x\<close>.
      We may therefore obtain the unique coextension \<open>\<tau> x \<in> D.hom (G x) (G' x)\<close>
      of \<open>\<epsilon> x\<close> along \<open>\<epsilon>' x\<close>.
      An explicit formula for \<open>\<tau> x\<close> is \<open>D (G' (\<epsilon> x)) (\<eta>' (G x))\<close>.
      Similarly, we obtain \<open>\<tau>' x = D (G (\<epsilon>' x)) (\<eta> (G' x)) \<in> D.hom (G' x) (G x)\<close>.
      We show these are the components of inverse natural transformations between
      @{term G} and @{term G'}.
\<close>
    obtain \<phi> \<psi> where \<phi>\<psi>: "meta_adjunction C D F G \<phi> \<psi>"
      using assms adjoint_functors_def by blast
    obtain \<phi>' \<psi>' where \<phi>'\<psi>': "meta_adjunction C D F G' \<phi>' \<psi>'"
      using assms adjoint_functors_def by blast
    interpret Adj: meta_adjunction C D F G \<phi> \<psi> using \<phi>\<psi> by auto
    interpret S: replete_setcat .
    interpret Adj: adjunction C D S.comp S.setp Adj.\<phi>C Adj.\<phi>D
                              F G \<phi> \<psi> Adj.\<eta> Adj.\<epsilon> Adj.\<Phi> Adj.\<Psi>
      using Adj.induces_adjunction by auto
    interpret Adj': meta_adjunction C D F G' \<phi>' \<psi>' using \<phi>'\<psi>' by auto
    interpret Adj': adjunction C D S.comp S.setp Adj'.\<phi>C Adj'.\<phi>D
                               F G' \<phi>' \<psi>' Adj'.\<eta> Adj'.\<epsilon> Adj'.\<Phi> Adj'.\<Psi>
      using Adj'.induces_adjunction by auto
    write C (infixr \<open>\<cdot>\<^sub>C\<close> 55)
    write D (infixr \<open>\<cdot>\<^sub>D\<close> 55)
    write Adj.C.in_hom (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>\<close>)
    write Adj.D.in_hom (\<open>\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>\<close>)
    let ?\<tau>o = "\<lambda>a. G' (Adj.\<epsilon> a) \<cdot>\<^sub>D Adj'.\<eta> (G a)"
    interpret \<tau>: transformation_by_components C D G G' ?\<tau>o
    proof
      show "\<And>a. Adj.C.ide a \<Longrightarrow> \<guillemotleft>G' (Adj.\<epsilon> a) \<cdot>\<^sub>D Adj'.\<eta> (G a) : G a \<rightarrow>\<^sub>D G' a\<guillemotright>"
        by fastforce
      show "\<And>f. Adj.C.arr f \<Longrightarrow>
                   (G' (Adj.\<epsilon> (Adj.C.cod f)) \<cdot>\<^sub>D Adj'.\<eta> (G (Adj.C.cod f))) \<cdot>\<^sub>D G f =
                   G' f \<cdot>\<^sub>D G' (Adj.\<epsilon> (Adj.C.dom f)) \<cdot>\<^sub>D Adj'.\<eta> (G (Adj.C.dom f))"
      proof -
        fix f
        assume f: "Adj.C.arr f"
        let ?x = "Adj.C.dom f"
        let ?x' = "Adj.C.cod f"
        have "(G' (Adj.\<epsilon> (Adj.C.cod f)) \<cdot>\<^sub>D Adj'.\<eta> (G (Adj.C.cod f))) \<cdot>\<^sub>D G f =
              G' (Adj.\<epsilon> (Adj.C.cod f) \<cdot>\<^sub>C F (G f)) \<cdot>\<^sub>D Adj'.\<eta> (G (Adj.C.dom f))"
          using f Adj'.\<eta>.naturality [of "G f"] Adj.D.comp_assoc by simp
        also have "... = G' (f \<cdot>\<^sub>C Adj.\<epsilon> (Adj.C.dom f)) \<cdot>\<^sub>D Adj'.\<eta> (G (Adj.C.dom f))"
          using f Adj.\<epsilon>.naturality by simp
        also have "... = G' f \<cdot>\<^sub>D G' (Adj.\<epsilon> (Adj.C.dom f)) \<cdot>\<^sub>D Adj'.\<eta> (G (Adj.C.dom f))"
          using f Adj.D.comp_assoc by simp
        finally show "(G' (Adj.\<epsilon> (Adj.C.cod f)) \<cdot>\<^sub>D Adj'.\<eta> (G (Adj.C.cod f))) \<cdot>\<^sub>D G f =
                      G' f \<cdot>\<^sub>D G' (Adj.\<epsilon> (Adj.C.dom f)) \<cdot>\<^sub>D Adj'.\<eta> (G (Adj.C.dom f))"
          by auto
      qed
    qed
    interpret natural_isomorphism C D G G' \<tau>.map
    proof
      fix a
      assume a: "Adj.C.ide a"
      show "Adj.D.iso (\<tau>.map a)"
      proof
        show "Adj.D.inverse_arrows (\<tau>.map a) (\<phi> (G' a) (Adj'.\<epsilon> a))"
        proof
          text\<open>
            The proof that the two composites are identities is a modest diagram chase.
            This is a good example of the inference rules for the \<open>category\<close>,
            \<open>functor\<close>, and \<open>natural_transformation\<close> locales in action.
            Isabelle is able to use the single hypothesis that \<open>a\<close> is an identity to
            implicitly fill in all the details that the various quantities are in fact arrows
            and that the indicated composites are all well-defined, as well as to apply
            associativity of composition.  In most cases, this is done by auto or simp without
            even mentioning any of the rules that are used.
$$\xymatrix{
        {G' a} \ar[dd]_{\eta'(G'a)} \ar[rr]^{\tau' a} \ar[dr]_{\eta(G'a)}
           && {G a} \ar[rr]^{\tau a} \ar[dr]_{\eta'(Ga)} && {G' a}                     \\
        & {GFG'a} \rrtwocell\omit{\omit(2)} \ar[ur]_{G(\epsilon' a)} \ar[dr]_{\eta'(GFG'a)}
           && {G'FGa} \drtwocell\omit{\omit(3)} \ar[ur]_{G'(\epsilon a)} &            \\
        {G'FG'a} \urtwocell\omit{\omit(1)} \ar[rr]_{G'F\eta(G'a)} \ar@/_8ex/[rrrr]_{G'FG'a}
           && {G'FGFG'a} \dtwocell\omit{\omit(4)} \ar[ru]_{G'FG(\epsilon' a)} \ar[rr]_{G'(\epsilon(FG'a))}
           && {G'FG'a} \ar[uu]_{G'(\epsilon' a)}                                       \\
           &&&&
}$$
\<close>
          show "Adj.D.ide (\<tau>.map a \<cdot>\<^sub>D \<phi> (G' a) (Adj'.\<epsilon> a))"
          proof -
            have "\<tau>.map a \<cdot>\<^sub>D \<phi> (G' a) (Adj'.\<epsilon> a) = G' a"
            proof -
              have "\<tau>.map a \<cdot>\<^sub>D \<phi> (G' a) (Adj'.\<epsilon> a) =
                    G' (Adj.\<epsilon> a) \<cdot>\<^sub>D (Adj'.\<eta> (G a) \<cdot>\<^sub>D G (Adj'.\<epsilon> a)) \<cdot>\<^sub>D Adj.\<eta> (G' a)"
                using a \<tau>.map_simp_ide Adj.\<phi>_in_terms_of_\<eta> Adj'.\<phi>_in_terms_of_\<eta>
                      Adj'.\<epsilon>.preserves_hom [of a a a] Adj.C.ide_in_hom Adj.D.comp_assoc
                      Adj.\<epsilon>_def Adj.\<eta>_def
                by simp
              also have "... = G' (Adj.\<epsilon> a) \<cdot>\<^sub>D (G' (F (G (Adj'.\<epsilon> a))) \<cdot>\<^sub>D Adj'.\<eta> (G (F (G' a)))) \<cdot>\<^sub>D
                               Adj.\<eta> (G' a)"
                using a Adj'.\<eta>.naturality [of "G (Adj'.\<epsilon> a)"] by auto
              also have "... = (G' (Adj.\<epsilon> a) \<cdot>\<^sub>D G' (F (G (Adj'.\<epsilon> a)))) \<cdot>\<^sub>D G' (F (Adj.\<eta> (G' a))) \<cdot>\<^sub>D
                               Adj'.\<eta> (G' a)"
                using a Adj'.\<eta>.naturality [of "Adj.\<eta> (G' a)"] Adj.D.comp_assoc by auto
              also have
                  "... = G' (Adj'.\<epsilon> a) \<cdot>\<^sub>D (G' (Adj.\<epsilon> (F (G' a))) \<cdot>\<^sub>D G' (F (Adj.\<eta> (G' a)))) \<cdot>\<^sub>D
                         Adj'.\<eta> (G' a)"
              proof -
                have
                   "G' (Adj.\<epsilon> a) \<cdot>\<^sub>D G' (F (G (Adj'.\<epsilon> a))) = G' (Adj'.\<epsilon> a) \<cdot>\<^sub>D G' (Adj.\<epsilon> (F (G' a)))"
                proof -
                  have "G' (Adj.\<epsilon> a \<cdot>\<^sub>C F (G (Adj'.\<epsilon> a))) = G' (Adj'.\<epsilon> a \<cdot>\<^sub>C Adj.\<epsilon> (F (G' a)))"
                    using a Adj.\<epsilon>.naturality [of "Adj'.\<epsilon> a"] by auto
                  thus ?thesis using a by force
                qed
                thus ?thesis using Adj.D.comp_assoc by auto
              qed
              also have "... = G' (Adj'.\<epsilon> a) \<cdot>\<^sub>D Adj'.\<eta> (G' a)"
              proof -
                have "G' (Adj.\<epsilon> (F (G' a))) \<cdot>\<^sub>D G' (F (Adj.\<eta> (G' a))) = G' (F (G' a))"
                proof -
                  have
                      "G' (Adj.\<epsilon> (F (G' a))) \<cdot>\<^sub>D G' (F (Adj.\<eta> (G' a))) = G' (Adj.\<epsilon>FoF\<eta>.map (G' a))"
                    using a Adj.\<epsilon>FoF\<eta>.map_simp_1 by auto
                  moreover have "Adj.\<epsilon>FoF\<eta>.map (G' a) = F (G' a)"
                    using a by (simp add: Adj.\<eta>\<epsilon>.triangle_F)
                  ultimately show ?thesis by auto
                qed
                thus ?thesis
                  using a Adj.D.comp_cod_arr [of "Adj'.\<eta> (G' a)"] by auto
              qed
              also have "... = G' a"
                using a Adj'.\<eta>\<epsilon>.triangle_G Adj'.G\<epsilon>o\<eta>G.map_simp_1 [of a] by auto
              finally show ?thesis by auto
            qed
            thus ?thesis using a by simp
          qed
          show "Adj.D.ide (\<phi> (G' a) (Adj'.\<epsilon> a) \<cdot>\<^sub>D \<tau>.map a)"
          proof -
            have "\<phi> (G' a) (Adj'.\<epsilon> a) \<cdot>\<^sub>D \<tau>.map a = G a"
            proof -
              have "\<phi> (G' a) (Adj'.\<epsilon> a) \<cdot>\<^sub>D \<tau>.map a =
                    G (Adj'.\<epsilon> a) \<cdot>\<^sub>D (Adj.\<eta> (G' a) \<cdot>\<^sub>D G' (Adj.\<epsilon> a)) \<cdot>\<^sub>D Adj'.\<eta> (G a)"
                using a \<tau>.map_simp_ide Adj.\<phi>_in_terms_of_\<eta> Adj'.\<epsilon>.preserves_hom [of a a a]
                      Adj.C.ide_in_hom Adj.D.comp_assoc Adj.\<eta>_def
                by auto
              also have
                "... = G (Adj'.\<epsilon> a) \<cdot>\<^sub>D (G (F (G' (Adj.\<epsilon> a))) \<cdot>\<^sub>D Adj.\<eta> (G' (F (G a)))) \<cdot>\<^sub>D
                       Adj'.\<eta> (G a)"
                using a Adj.\<eta>.naturality [of "G' (Adj.\<epsilon> a)"] by auto
              also have
                "... = (G (Adj'.\<epsilon> a) \<cdot>\<^sub>D G (F (G' (Adj.\<epsilon> a)))) \<cdot>\<^sub>D G (F (Adj'.\<eta> (G a))) \<cdot>\<^sub>D
                       Adj.\<eta> (G a)"
                using a Adj.\<eta>.naturality [of "Adj'.\<eta> (G a)"] Adj.D.comp_assoc by auto
              also have
                "... = G (Adj.\<epsilon> a) \<cdot>\<^sub>D (G (Adj'.\<epsilon> (F (G a))) \<cdot>\<^sub>D G (F (Adj'.\<eta> (G a)))) \<cdot>\<^sub>D
                       Adj.\<eta> (G a)"
              proof -
                have "G (Adj'.\<epsilon> a) \<cdot>\<^sub>D G (F (G' (Adj.\<epsilon> a))) = G (Adj.\<epsilon> a) \<cdot>\<^sub>D G (Adj'.\<epsilon> (F (G a)))"
                proof -
                  have "G (Adj'.\<epsilon> a \<cdot>\<^sub>C F (G' (Adj.\<epsilon> a))) = G (Adj.\<epsilon> a \<cdot>\<^sub>C Adj'.\<epsilon> (F (G a)))"
                    using a Adj'.\<epsilon>.naturality [of "Adj.\<epsilon> a"] by auto
                  thus ?thesis using a by force
                qed
                thus ?thesis using Adj.D.comp_assoc by auto
              qed
              also have "... = G (Adj.\<epsilon> a) \<cdot>\<^sub>D Adj.\<eta> (G a)"
              proof -
                have "G (Adj'.\<epsilon> (F (G a))) \<cdot>\<^sub>D G (F (Adj'.\<eta> (G a))) = G (F (G a))"
                proof -
                  have
                    "G (Adj'.\<epsilon> (F (G a))) \<cdot>\<^sub>D G (F (Adj'.\<eta> (G a))) = G (Adj'.\<epsilon>FoF\<eta>.map (G a))"
                    using a Adj'.\<epsilon>FoF\<eta>.map_simp_1 [of "G a"] by auto
                  moreover have "Adj'.\<epsilon>FoF\<eta>.map (G a) = F (G a)"
                    using a by (simp add: Adj'.\<eta>\<epsilon>.triangle_F)
                  ultimately show ?thesis by auto
                qed
                thus ?thesis
                  using a Adj.D.comp_cod_arr by auto
              qed
              also have "... = G a"
                using a Adj.\<eta>\<epsilon>.triangle_G Adj.G\<epsilon>o\<eta>G.map_simp_1 [of a] by auto
              finally show ?thesis by auto
            qed
            thus ?thesis using a by auto
          qed
        qed
      qed
    qed
    have "natural_isomorphism C D G G' \<tau>.map" ..
    thus "naturally_isomorphic C D G G'"
      using naturally_isomorphic_def by blast
  qed

end
