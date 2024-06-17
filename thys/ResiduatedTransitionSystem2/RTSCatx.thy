(*  Title:       RTSCatx
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "The RTS-Category of RTS's and Transformations"

theory RTSCatx
imports Main ConcreteRTSCategory
begin

  text\<open>
    In this section we apply the @{locale concrete_rts_category} construction to create an
    RTS-category, taking the set of all small extensional RTS's at a given arrow type as
    the objects and the exponential RTS's formed from these as the hom's, so that the
    arrows correspond to transformations and the arrows that are identities with respect to
    the residuation correspond to simulations.  We prove that the resulting category,
    which we will refer to in informal text as \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close>, is cartesian closed.
    For that to hold, we need to start with the assumption that the underlying arrow type
    is a universe.
  \<close>

  locale rtscatx =
    universe arr_type
  for arr_type :: "'A itself"
  begin

    sublocale concrete_rts_category
                \<open>TYPE('A resid)\<close> \<open>TYPE(('A, 'A) exponential_rts.arr)\<close>
                \<open>Collect extensional_rts \<inter> Collect small_rts\<close>
                \<open>\<lambda>A B. exponential_rts.resid A B\<close>
                \<open>\<lambda>A. exponential_rts.MkArr (I A) (I A) (I A)\<close>
                \<open>\<lambda>A B C f g. COMP.map A B C (f, g)\<close>
    proof (intro concrete_rts_category.intro)
      show "\<And>A B. \<lbrakk>A \<in> Collect extensional_rts \<inter> Collect small_rts;
                   B \<in> Collect extensional_rts \<inter> Collect small_rts\<rbrakk>
                      \<Longrightarrow> extensional_rts (exponential_rts.resid A B)"
        by (metis CollectD Int_Collect exponential_rts.intro
            exponential_rts.is_extensional_rts extensional_rts.extensional
            small_rts.axioms(1) weakly_extensional_rts.intro
            weakly_extensional_rts_axioms.intro)
      show "\<And>A. A \<in> Collect extensional_rts \<inter> Collect small_rts \<Longrightarrow>
                       residuation.ide (exponential_rts.resid A A)
                         (exponential_rts.MkArr (I A) (I A) (I A))"
      proof -
        fix A :: "'a resid"
        assume A: "A \<in> Collect extensional_rts \<inter> Collect small_rts"
        show "residuation.ide (exponential_rts.resid A A)
                (exponential_rts.MkIde (I A))"
        proof -
          interpret A: extensional_rts A using A by blast
          interpret I: identity_simulation A ..
          interpret AA: exponential_rts A A ..
          show "AA.ide (AA.MkIde (I A))"
            using AA.ide_MkIde I.simulation_axioms by blast
        qed
      qed
      fix A :: "'a resid" and B :: "'a resid"
      assume A: "A \<in> Collect extensional_rts \<inter> Collect small_rts"
      and B: "B \<in> Collect extensional_rts \<inter> Collect small_rts"
      interpret A: extensional_rts A using A by blast
      interpret B: extensional_rts B using B by blast
      interpret IA: identity_simulation A ..
      interpret IA: simulation_as_transformation A A \<open>I A\<close> ..
      interpret IB: identity_simulation B ..
      interpret IB: simulation_as_transformation B B \<open>I B\<close> ..
      interpret AA: exponential_rts A A ..
      interpret BB: exponential_rts B B ..
      interpret AB: exponential_rts A B ..
      interpret Cmp_AAB: COMP A A B ..
      interpret Cmp_ABB: COMP A B B ..
      show "\<And>t. AB.arr t \<Longrightarrow> Cmp_AAB.map (t, AA.MkIde (I A)) = t"
      proof -
        fix t
        assume t: "AB.arr t"
        interpret t: transformation A B \<open>AB.Dom t\<close> \<open>AB.Cod t\<close> \<open>AB.Map t\<close>
          using t AB.arr_char by blast
        show "Cmp_AAB.map (t, AA.MkIde (I A)) = t"
        proof -
          have "AB.Dom t \<circ> AA.Dom (AA.MkIde (I A)) = AB.Dom t"
            using t.F.simulation_axioms comp_simulation_identity by auto
          moreover have "AB.Cod t \<circ> AA.Cod (AA.MkIde (I A)) = AB.Cod t"
            using t.G.simulation_axioms comp_simulation_identity by auto
          moreover have "AB.Map t \<circ> AA.Map (AA.MkIde (I A)) = AB.Map t"
            using t.extensional by auto
          ultimately show ?thesis
            using t Cmp_AAB.map_eq AB.MkArr_Map AB.arr_char
                  IA.transformation_axioms
            by auto
        qed
      qed
      show "\<And>u. AB.arr u \<Longrightarrow> Cmp_ABB.map (BB.MkIde (I B), u) = u"
      proof -
        fix u
        assume u: "AB.arr u"
        interpret u: transformation A B \<open>AB.Dom u\<close> \<open>AB.Cod u\<close> \<open>AB.Map u\<close>
          using u AB.arr_char by blast
        show "Cmp_ABB.map (BB.MkIde (I B), u) = u"
        proof -
          have "BB.Dom (BB.MkIde (I B)) \<circ> AB.Dom u = AB.Dom u"
            using u.F.simulation_axioms comp_identity_simulation by auto
          moreover have "BB.Cod (BB.MkIde (I B)) \<circ> AB.Cod u = AB.Cod u"
            using u.G.simulation_axioms comp_identity_simulation by auto
          moreover have "BB.Map (BB.MkIde (I B)) \<circ> AB.Map u = AB.Map u"
          proof
            fix x
            show "(BB.Map (BB.MkIde (I B)) \<circ> AB.Map u) x = AB.Map u x"
              using u.extensional u.preserves_arr by auto metis
          qed
          ultimately show ?thesis
            using u Cmp_ABB.map_eq AB.MkArr_Map AB.arr_char
                  IB.transformation_axioms
            by auto
        qed
      qed
      fix C :: "'a resid"
      assume C: "C \<in> Collect extensional_rts \<inter> Collect small_rts"
      interpret C: extensional_rts C using C by blast
      interpret BC: exponential_rts B C ..
      interpret AC: exponential_rts A C ..
      interpret BCxAB: product_rts BC.resid AB.resid ..
      interpret Cmp_ABC: COMP A B C ..
      show "binary_simulation BC.resid AB.resid AC.resid
              (\<lambda>(t, u). Cmp_ABC.map (t, u))"
        using Cmp_ABC.simulation_axioms BCxAB.product_rts_axioms
              BC.rts_axioms AB.rts_axioms AC.rts_axioms binary_simulation.intro
        by auto
      fix D :: "'a resid"
      assume D: "D \<in> Collect extensional_rts \<inter> Collect small_rts"
      interpret D: extensional_rts D using D by blast
      interpret BD: exponential_rts B D ..
      interpret CD: exponential_rts C D ..
      interpret Cmp_ABD: COMP A B D ..
      interpret Cmp_BCD: COMP B C D ..
      interpret Cmp_ACD: COMP A C D ..
      show "\<And>t u v. \<lbrakk>CD.arr t; BC.arr u; AB.arr v\<rbrakk> \<Longrightarrow> 
                       COMP.map A B D (COMP.map B C D (t, u), v) =
                       COMP.map A C D (t, COMP.map A B C (u, v))"
      proof -
        fix t u v
        assume t: "CD.arr t" and u: "BC.arr u" and v: "AB.arr v"
        have "transformation A C
                (AC.Dom u \<circ> AC.Dom v) (AC.Cod u \<circ> AC.Cod v)
                (AC.Map u \<circ> AC.Map v)"
          using t u v Preliminaries.horizontal_composite
          by (metis A.extensional_rts_axioms AB.arrE B.extensional_rts_axioms
              BC.arrE C.extensional_rts_axioms)
        moreover
        have "transformation B D
                (BD.Dom t \<circ> BD.Dom u) (BD.Cod t \<circ> BD.Cod u)
                (BD.Map t \<circ> BD.Map u)"
          using t u v Preliminaries.horizontal_composite
          by (metis B.extensional_rts_axioms BC.arrE C.extensional_rts_axioms
              CD.arrE D.extensional_rts_axioms)
        ultimately
        show "COMP.map A B D (COMP.map B C D (t, u), v) =
              COMP.map A C D (t, COMP.map A B C (u, v))"
          using t u v Cmp_ABD.map_eq Cmp_BCD.map_eq Cmp_ACD.map_eq
                Cmp_ABC.map_eq
          by auto
      qed
    qed

    type_synonym 'a arr =
      "('a resid, ('a, 'a) exponential_rts.arr) concrete_rts_category.arr"

    notation resid  (infix "\\" 70)
    notation hcomp  (infixr "\<star>" 53)

    text\<open>
      The mapping @{term Trn} that takes arrow \<open>t \<in> H.hom a b\<close> to the underlying transition of the
      exponential RTS \<open>[Dom a, Dom b]\<close>, is injective.
    \<close>

    lemma inj_Trn:
    assumes "obj a" and "obj b"
    shows "Trn \<in> H.hom a b \<rightarrow>
                   Collect (residuation.arr (exponential_rts.resid (Dom a) (Dom b)))"
    and "inj_on Trn (H.hom a b)"
    proof
      interpret A: extensional_rts \<open>Dom a\<close>
        using assms obj_char arr_char by blast
      interpret B: extensional_rts \<open>Dom b\<close>
        using assms obj_char arr_char by blast
      interpret AB: exponential_rts \<open>Dom a\<close> \<open>Dom b\<close> ..
      show "\<And>x. x \<in> H.hom a b \<Longrightarrow> Trn x \<in> Collect AB.arr"
        using assms arr_char H.in_homE by auto
      show "inj_on Trn (H.hom a b)"
      proof
        fix t u
        assume t: "t \<in> H.hom a b" and u: "u \<in> H.hom a b"
        assume tu: "Trn t = Trn u"
        show "t = u"
          using t u tu AB.arr_eqI
          apply auto[1]
          by (metis H.comp_arr_dom H.comp_cod_arr H.in_homE H_seq_char
              MkArr_Trn)
      qed
    qed

    sublocale locally_small_rts_category resid hcomp
    proof
      fix a b
      assume a: "obj a" and b: "obj b"
      interpret A: extensional_rts \<open>Dom a\<close>
        using a obj_char arr_char by blast
      interpret A: small_rts \<open>Dom a\<close>
        using a obj_char arr_char by blast
      interpret B: extensional_rts \<open>Dom b\<close>
        using b obj_char arr_char by blast
      interpret B: small_rts \<open>Dom b\<close>
        using b obj_char arr_char by blast
      interpret AB: exponential_of_small_rts \<open>Dom a\<close> \<open>Dom b\<close> ..
      have "Trn ` H.hom a b \<subseteq> Collect AB.arr"
        using H_arr_char image_subset_iff by auto
      moreover have "inj_on Trn (H.hom a b)"
        using a b inj_Trn by blast
      ultimately show "small (H.hom a b)"
        using a b AB.small smaller_than_small small_image_iff inj_Trn by metis
    qed

    abbreviation sta_in_hom   ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>s\<^sub>t\<^sub>a _\<guillemotright>")
    where "sta_in_hom f a b \<equiv> H.in_hom f a b \<and> sta f"

    abbreviation trn_to   ("\<guillemotleft>_ : _ \<Rightarrow> _\<guillemotright>")
    where "trn_to t f g \<equiv> arr t \<and> src t = f \<and> trg t = g"

    definition mkarr :: "'A resid \<Rightarrow> 'A resid \<Rightarrow>
                              ('A \<Rightarrow> 'A) \<Rightarrow> ('A \<Rightarrow> 'A) \<Rightarrow> ('A \<Rightarrow> 'A) \<Rightarrow>
                                 'A arr"
    where "mkarr A B F G \<tau> \<equiv>
           MkArr A B (exponential_rts.MkArr F G \<tau>)"

    abbreviation mksta
    where "mksta A B F \<equiv> mkarr A B F F F"

    lemma Dom_mkarr [simp]:
    shows "Dom (mkarr A B F G \<tau>) = A"
      unfolding mkarr_def by simp

    lemma Cod_mkarr [simp]:
    shows "Cod (mkarr A B F G \<tau>) = B"
      unfolding mkarr_def by simp

    lemma arr_mkarr [intro]:
    assumes "small_rts A" and "extensional_rts A"
    and "small_rts B" and "extensional_rts B"
    and "transformation A B F G \<tau>"
    shows "arr (mkarr A B F G \<tau>)"
    and "src (mkarr A B F G \<tau>) = mksta A B F"
    and "trg (mkarr A B F G \<tau>) = mksta A B G"
    and "dom (mkarr A B F G \<tau>) = mkobj A"
    and "cod (mkarr A B F G \<tau>) = mkobj B"
    proof -
      interpret A: extensional_rts A
        using assms by simp
      interpret B: extensional_rts B
        using assms by simp
      interpret AB: exponential_rts A B ..
      interpret \<tau>: transformation A B F G \<tau>
        using assms(5) by blast
      show 1: "arr (mkarr A B F G \<tau>)"
        unfolding mkarr_def
        using assms arr_char by auto
      show "src (mkarr A B F G \<tau>) = mksta A B F"
      and "trg (mkarr A B F G \<tau>) = mksta A B G"
      and "dom (mkarr A B F G \<tau>) = mkobj A"
      and "cod (mkarr A B F G \<tau>) = mkobj B"
        unfolding mkarr_def
        using assms 1 src_char trg_char AB.src_char AB.trg_char
              dom_char cod_char
        by auto
    qed

    lemma mkarr_simps [simp]:
    assumes "arr (mkarr A B F G \<sigma>)"
    shows "dom (mkarr A B F G \<sigma>) = mkobj A"
    and "cod (mkarr A B F G \<sigma>) = mkobj B"
    and "src (mkarr A B F G \<sigma>) = mksta A B F"
    and "trg (mkarr A B F G \<sigma>) = mksta A B G"
      using assms arr_mkarr dom_char cod_char apply auto[4]
      by (metis (no_types, lifting) Cod_mkarr CollectD Dom_mkarr Int_Collect
          Trn.simps(1) arrE exponential_rts.arr_MkArr exponential_rts.intro
          extensional_rts.axioms(1) extensional_rts.extensional mkarr_def
          weakly_extensional_rts.intro weakly_extensional_rts_axioms.intro)+

    lemma sta_mksta [intro]:
    assumes "small_rts A" and "extensional_rts A"
    and "small_rts B" and "extensional_rts B"
    and "simulation A B F"
    shows "sta (mksta A B F)"
    and "dom (mksta A B F) = mkobj A" and "cod (mksta A B F) = mkobj B"
    proof -
      interpret A: extensional_rts A
        using assms by blast
      interpret B: extensional_rts B
        using assms by blast
      interpret F: simulation A B F
        using assms by blast
      interpret F: simulation_as_transformation A B F ..
      show "sta (mksta A B F)"
        using assms F.transformation_axioms arr_mkarr V.ide_iff_src_self
        by presburger
      show "dom (mksta A B F) = mkobj A"
        using assms F.transformation_axioms arr_mkarr(4) by blast
      show "cod (mksta A B F) = mkobj B"
        using assms F.transformation_axioms arr_mkarr(5) by blast
    qed

    abbreviation Src
    where "Src \<equiv> exponential_rts.Dom \<circ> Trn"

    abbreviation Trg
    where "Trg \<equiv> exponential_rts.Cod \<circ> Trn"

    abbreviation Map
    where "Map \<equiv> exponential_rts.Map \<circ> Trn"

    lemma Src_mkarr [simp]:
    assumes "arr (mkarr A B F G \<sigma>)"
    shows "Src (mkarr A B F G \<sigma>) = F"
      using assms
      by (metis (mono_tags, lifting) Int_Collect Trn.simps(1) arrE comp_apply
          exponential_rts.Dom.simps(1) exponential_rts.intro
          extensional_rts.axioms(1) extensional_rts.extensional mem_Collect_eq
          mkarr_def weakly_extensional_rts.intro
          weakly_extensional_rts_axioms.intro)

    lemma Trg_mkarr [simp]:
    assumes "arr (mkarr A B F G \<sigma>)"
    shows "Trg (mkarr A B F G \<sigma>) = G"
      using assms
      by (metis (mono_tags, lifting) Int_Collect Trn.simps(1) arrE comp_apply
          exponential_rts.Cod.simps(1) exponential_rts.intro
          extensional_rts.axioms(1) extensional_rts.extensional mem_Collect_eq
          mkarr_def weakly_extensional_rts.intro
          weakly_extensional_rts_axioms.intro)

    lemma Map_simps [simp]:
    assumes "arr t"
    shows "Map (dom t) = I (Dom t)"
    and "Map (cod t) = I (Cod t)"
    and "Map (src t) = Src t"
    and "Map (trg t) = Trg t"
    proof -
      interpret A: extensional_rts \<open>Dom t\<close>
        using assms arr_char by blast
      interpret B: extensional_rts \<open>Cod t\<close>
        using assms arr_char by blast
      interpret AB: exponential_rts \<open>Dom t\<close> \<open>Cod t\<close> ..
      show "Map (dom t) = I (Dom t)"
        using assms dom_char by simp
      show "Map (cod t) = I (Cod t)"
        using assms cod_char by simp
      show "Map (src t) = Src t"
        using assms arr_char src_char by simp
      show "Map (trg t) = Trg t"
        using assms arr_char trg_char by simp
    qed

    lemma src_simp:
    assumes "arr t"
    shows "src t = mksta (Dom t) (Cod t) (Src t)"
    proof -
      interpret A: extensional_rts \<open>Dom t\<close>
        using assms arr_char by blast
      interpret B: extensional_rts \<open>Cod t\<close>
        using assms arr_char by blast
      interpret AB: exponential_rts \<open>Dom t\<close> \<open>Cod t\<close> ..
      show ?thesis
        using assms mkarr_def src_char AB.src_char by auto
    qed

    lemma trg_simp:
    assumes "arr t"
    shows "trg t = mksta (Dom t) (Cod t) (Trg t)"
    proof -
      interpret A: extensional_rts \<open>Dom t\<close>
        using assms arr_char by blast
      interpret B: extensional_rts \<open>Cod t\<close>
        using assms arr_char by blast
      interpret AB: exponential_rts \<open>Dom t\<close> \<open>Cod t\<close> ..
      show ?thesis
        using assms mkarr_def trg_char AB.trg_char by auto
    qed

    text\<open>
      The mapping @{term Map} that takes a transition to its underlying transformation,
      is a bijection, which cuts down to a bijection between states and simulations.
    \<close>

    lemma bij_mkarr:
    assumes "small_rts A" and "extensional_rts A"
    and "small_rts B" and "extensional_rts B"
    and "simulation A B F" and "simulation A B G"
    shows "mkarr A B F G \<in> Collect (transformation A B F G)
                              \<rightarrow> {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}"
    and "Map \<in> {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}
                   \<rightarrow> Collect (transformation A B F G)"
    and [simp]: "Map (mkarr A B F G \<tau>) = \<tau>"
    and [simp]: "t \<in> {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}
                    \<Longrightarrow> mkarr A B F G (Map t) = t"
    and "bij_betw (mkarr A B F G) (Collect (transformation A B F G))
           {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}"
    and "bij_betw Map {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}
           (Collect (transformation A B F G))"
    proof -
      interpret A: extensional_rts A
        using assms by simp
      interpret B: extensional_rts B
        using assms by simp
      interpret AB: exponential_rts A B ..
      show 1: "mkarr A B F G \<in>
                 Collect (transformation A B F G)
                    \<rightarrow> {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}"
        using assms(1,3) src_char A.extensional_rts_axioms
              B.extensional_rts_axioms arr_mkarr(1-3)
        by auto
      show 2: "Map \<in> {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}
                         \<rightarrow> Collect (transformation A B F G)"
        using assms arr_char src_char trg_char mkarr_def
        apply auto[1]
        by (metis AB.Map.simps(1) AB.Map_src AB.Map_trg AB.arr_char)
      show 3: "\<And>\<tau>. Map (mkarr A B F G \<tau>) = \<tau>"
        using mkarr_def by simp
      show 4: "\<And>t. t \<in> {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}
                      \<Longrightarrow> mkarr A B F G (Map t) = t"
        using AB.MkArr_Map AB.arr_char MkArr_Trn arr_char src_char trg_char
              mkarr_def
        apply auto[1]
        by (metis AB.Map.simps(1) AB.Map_src AB.Map_trg)
      show "bij_betw (mkarr A B F G) (Collect (transformation A B F G))
              {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}"
        using 1 2 3 4 by (intro bij_betwI)
      show "bij_betw Map {t. \<guillemotleft>t : mksta A B F \<Rightarrow> mksta A B G\<guillemotright>}
               (Collect (transformation A B F G))"
        using 1 2 3 4 by (intro bij_betwI)
    qed

    lemma bij_mksta:
    assumes "small_rts A" and "extensional_rts A"
    and "small_rts B" and "extensional_rts B"
    shows "mksta A B \<in> Collect (simulation A B)
                          \<rightarrow> {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}"
    and "Map \<in> {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}
                   \<rightarrow> Collect (simulation A B)"
    and [simp]: "Map (mksta A B F) = F"
    and [simp]: "t \<in> {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}
                    \<Longrightarrow> mksta A B (Map t) = t"
    and "bij_betw (mksta A B) (Collect (simulation A B))
           {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}"
    and "bij_betw Map {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}
           (Collect (simulation A B))"
    proof -
      interpret A: extensional_rts A
        using assms by simp
      interpret A: small_rts A
        using assms by simp
      interpret B: extensional_rts B
        using assms by simp
      interpret B: small_rts B
        using assms by simp
      interpret AB: exponential_rts A B ..
      show 1: " mksta A B \<in> Collect (simulation A B)
                               \<rightarrow> {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}"
      proof
        fix F
        assume F: "F \<in> Collect (simulation A B)"
        interpret F: simulation A B F
          using F by blast
        interpret F: simulation_as_transformation A B F ..
        show "mksta A B F \<in> {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}"
          using assms F sta_mksta A.small_rts_axioms F.transformation_axioms
          by auto
      qed
      show 2: "Map \<in> {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}
                         \<rightarrow> Collect (simulation A B)"
        using AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S cod_char dom_char mkobj_def sta_char by auto
      show 3: "\<And>F. Map (mksta A B F) = F"
        using mkarr_def by auto
      show 4: "\<And>t. t \<in> {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}
                           \<Longrightarrow> mksta A B (Map t) = t"
        using AB.Map.simps(1) Trn.simps(1) AB.MkArr_Map AB.arr_char mkarr_def
        apply auto[1]
        by (metis (no_types, lifting) AB.MkIde_Map Dom_cod Dom_dom H.in_homE
            MkArr_Trn V.ide_implies_arr mkobj_simps(1) sta_char)
      show "bij_betw (mksta A B) (Collect (simulation A B))
              {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}"
        using assms 1 2 3 4 sta_mksta
        apply (intro bij_betwI)
        by (auto simp add: dom_char cod_char)
      show "bij_betw Map {t. \<guillemotleft>t : mkobj A \<rightarrow>\<^sub>s\<^sub>t\<^sub>a mkobj B\<guillemotright>}
              (Collect (simulation A B))"
        using assms 1 2 3 4 sta_mksta
        apply (intro bij_betwI)
        by (auto simp add: dom_char cod_char)
    qed

    lemma mkarr_comp:
    assumes "small_rts A" and "extensional_rts A"
    and "small_rts B" and "extensional_rts B"
    and "small_rts C" and "extensional_rts C"
    and "transformation A B F G \<sigma>"
    and "transformation B C H K \<tau>"
    shows "mkarr A C (H \<circ> F) (K \<circ> G) (\<tau> \<circ> \<sigma>) =
           mkarr B C H K \<tau> \<star> mkarr A B F G \<sigma>"
    proof -
      interpret COMP: COMP A B C
        using assms COMP.intro by blast
      interpret \<sigma>: transformation A B F G \<sigma>
        using assms by simp
      interpret \<tau>: transformation B C H K \<tau>
        using assms by simp
      show ?thesis
        unfolding hcomp_def mkarr_def
        using assms sta_mksta COMP.map_eq by auto
    qed

    lemma mkarr_resid:
    assumes "small_rts A \<and> extensional_rts A"
    and "small_rts B \<and> extensional_rts B"
    and "consistent_transformations A B F G H \<sigma> \<tau>"
    shows "mkarr A B F G \<sigma> \<frown> mkarr A B F H \<tau>"
    and "mkarr A B H (consistent_transformations.apex A B H \<sigma> \<tau>)
           (consistent_transformations.resid A B H \<sigma> \<tau>) =
         mkarr A B F G \<sigma> \\ mkarr A B F H \<tau>"
    proof -
      interpret A: extensional_rts A
        using assms by simp
      interpret B: extensional_rts B
        using assms by simp
      interpret AB: exponential_rts A B ..
      interpret \<sigma>\<tau>: consistent_transformations A B F G H \<sigma> \<tau>
        using assms by blast
      show 1: "mkarr A B F G \<sigma> \<frown> mkarr A B F H \<tau>"
        using assms \<sigma>\<tau>.con con_char AB.con_char mkarr_def
        by (simp add: \<sigma>\<tau>.\<sigma>.transformation_axioms \<sigma>\<tau>.\<tau>.transformation_axioms)
      show "mkarr A B H \<sigma>\<tau>.apex \<sigma>\<tau>.resid =
            mkarr A B F G \<sigma> \\ mkarr A B F H \<tau>"
        unfolding mkarr_def
        using assms Trn_resid AB.resid_def AB.Apex_def AB.con_char
              \<sigma>\<tau>.\<sigma>.transformation_axioms \<sigma>\<tau>.\<tau>.transformation_axioms
              \<sigma>\<tau>.con
        by (intro arr_eqI) auto
    qed

    lemma Map_hcomp:
    assumes "H.seq t u"
    shows "Map (t \<star> u) = Map t \<circ> Map u"
    proof -
      interpret COMP \<open>Dom u\<close> \<open>Cod u\<close> \<open>Cod t\<close>
        using assms arr_char COMP.intro H_seq_char by auto
      have t: "arr t" and u: "arr u"
        using assms by fastforce+
      have tu: "Dom t = Cod u"
        using assms H_seq_char by blast
      show ?thesis
        unfolding hcomp_def
        using assms tu t u map_eq H.ext arr_char by auto
    qed

    lemma Map_resid:
    assumes "V.con t u"
    shows "consistent_transformations (Dom t) (Cod t)
             (Src t) (Trg t) (Trg u) (Map t) (Map u)"
    and "Map (t \\ u) =
           consistent_transformations.resid (Dom t) (Cod t) (Trg u)
             (Map t) (Map u)"
    proof -
      interpret A: extensional_rts \<open>Dom t\<close>
        using assms arr_char V.con_implies_arr by blast
      interpret B: extensional_rts \<open>Cod t\<close>
        using assms arr_char V.con_implies_arr by blast
      interpret AB: exponential_rts \<open>Dom t\<close> \<open>Cod t\<close> ..
      have 1: "Dom t = Dom u" and "Cod t = Cod u"
        using assms con_implies_Par(1-2) by auto
      have 2: "Src t = Src u"
        using assms con_char AB.con_char by simp
      interpret T: transformation \<open>Dom t\<close> \<open>Cod t\<close>
                     \<open>Src t\<close> \<open>Trg t\<close> \<open>Map t\<close>
        using assms arr_char AB.arr_char [of "Trn t"] V.con_implies_arr
        by simp
      interpret U: transformation \<open>Dom t\<close> \<open>Cod t\<close>
                     \<open>Src t\<close> \<open>Trg u\<close> \<open>Map u\<close>
        using assms 1 2 con_char arr_char [of u] AB.arr_char V.con_implies_arr
        by simp
      interpret TU: consistent_transformations \<open>Dom t\<close> \<open>Cod t\<close>
                      \<open>Src t\<close> \<open>Trg t\<close> \<open>Trg u\<close>
                      \<open>Map t\<close> \<open>Map u\<close>
        using assms con_char AB.con_char
        by unfold_locales auto
      show "consistent_transformations (Dom t) (Cod t)
              (Src t) (Trg t) (Trg u)
              (Map t) (Map u)"
        ..
      show "Map (t \\ u) =
            consistent_transformations.resid (Dom t) (Cod t) (Trg u)
              (Map t) (Map u)"
        using assms con_char AB.con_char  AB.Map_resid by auto
    qed

    lemma simulation_Map_sta:
    assumes "sta f"
    shows "simulation (Dom f) (Cod f) (Map f)"
      by (metis Map_resid(1) Map_simps(3) V.ideE V.ide_implies_arr
          V.src_ide assms consistent_transformations.axioms(6)
          transformation.axioms(3))

    lemma transformation_Map_arr:
    assumes "arr t"
    shows "transformation (Dom t) (Cod t) (Src t) (Trg t) (Map t)"
      by (meson Map_resid(1) V.arrE assms
          consistent_transformations.axioms(6))

    lemma iso_char:
    shows "H.iso t \<longleftrightarrow> arr t \<and> Src t = Map t \<and> Trg t = Map t \<and>
                       invertible_simulation (Dom t) (Cod t) (Map t)"
    proof
      assume t: "H.iso t"
      have 1: "arr t"
        using t H.iso_is_arr by simp
      interpret A: extensional_rts \<open>Dom t\<close>
        using 1 arr_char by blast
      interpret B: extensional_rts \<open>Cod t\<close>
        using 1 arr_char by blast
      interpret AB: exponential_rts \<open>Dom t\<close> \<open>Cod t\<close> ..
      interpret BA: exponential_rts \<open>Cod t\<close> \<open>Dom t\<close> ..
      show "arr t \<and> Src t = Map t \<and> Trg t = Map t \<and>
            invertible_simulation (Dom t) (Cod t) (Map t)"
      proof (intro conjI)
        show "arr t" by fact
        obtain u where tu: "H.inverse_arrows t u"
          using t H.iso_def by blast
        have 2: "V.ide t \<and> V.ide u"
          using tu iso_implies_sta by auto
        have 3: "Dom u = Cod t \<and> Cod u = Dom t"
          using tu
          by (metis (no_types, lifting) H.inverse_arrowsE H_composable_char
              V.not_ide_null obj_is_sta)
        show "Src t = Map t" and "Trg t = Map t"
          using 2 sta_char AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S by auto
        let ?T = "Map t" and ?U = "Map u"
        interpret T: simulation \<open>Dom t\<close> \<open>Cod t\<close> ?T
          using 2 sta_char AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S by simp
        interpret U: simulation \<open>Cod t\<close> \<open>Dom t\<close> ?U
          using 2 3 sta_char BA.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S by simp
        have "inverse_simulations (Dom t) (Cod t) ?U ?T"
        proof
          show "?T \<circ> ?U = I (Cod t)"
            by (metis (no_types, lifting) 2 H.ide_compE H.inverse_arrowsE
                Map_hcomp Map_simps(2) V.ide_implies_arr tu)
          show "?U \<circ> ?T = I (Dom t)"
            by (metis (no_types, lifting) 2 H.ide_compE H.inverse_arrowsE
                Map_hcomp Map_simps(1) V.ide_implies_arr tu)
        qed
        thus "invertible_simulation (Dom t) (Cod t) (Map t)"
          using invertible_simulation_def' by blast
      qed
      next
      assume t: "arr t \<and> Src t = Map t \<and> Trg t = Map t \<and>
                 invertible_simulation (Dom t) (Cod t) (Map t)"
      interpret A: extensional_rts \<open>Dom t\<close>
        using t arr_char by blast
      interpret A: small_rts \<open>Dom t\<close>
        using t arr_char by blast
      interpret B: extensional_rts \<open>Cod t\<close>
        using t arr_char by blast
      interpret B: small_rts \<open>Cod t\<close>
        using t arr_char by blast
      interpret AB: exponential_rts \<open>Dom t\<close> \<open>Cod t\<close> ..
      interpret BA: exponential_rts \<open>Cod t\<close> \<open>Dom t\<close> ..
      interpret AA: exponential_rts \<open>Dom t\<close> \<open>Dom t\<close> ..
      interpret BB: exponential_rts \<open>Cod t\<close> \<open>Cod t\<close> ..
      interpret C: COMP \<open>Dom t\<close> \<open>Cod t\<close> \<open>Dom t\<close> ..
      interpret C': COMP \<open>Cod t\<close> \<open>Dom t\<close> \<open>Cod t\<close> ..
      interpret T: invertible_simulation \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
        using t by auto
      show "H.iso t"
      proof -
        obtain U where U: "inverse_simulations (Dom t) (Cod t) U (Map t)"
          using T.invertible by blast
        interpret U: simulation \<open>Cod t\<close> \<open>Dom t\<close> U
          using U inverse_simulations_def by blast
        interpret U: simulation_as_transformation \<open>Cod t\<close> \<open>Dom t\<close> U ..
        interpret TU: inverse_simulations \<open>Dom t\<close> \<open>Cod t\<close> U \<open>Map t\<close>
          using U by blast
        let ?u = "mksta (Cod t) (Dom t) U"
        have u: "V.ide ?u \<and> \<guillemotleft>?u : cod t \<rightarrow> dom t\<guillemotright>"
          using t sta_mksta U.simulation_axioms A.small_rts_axioms
                A.extensional_rts_axioms B.small_rts_axioms
                B.extensional_rts_axioms dom_char cod_char
          by auto
        have seq: "H.seq ?u t \<and> H.seq t ?u"
          using t u H.seqI by auto
        have "H.inverse_arrows t ?u"
        proof
          show "obj (hcomp ?u t)"
          proof -
            have "hcomp ?u t = dom t"
            proof (intro arr_eqI)
              show "mksta (Cod t) (Dom t) U \<star> t \<noteq> Null"
                using t U.transformation_axioms sta_mksta V.not_arr_null
                      null_char seq
                by force
              show "dom t \<noteq> Null"
                using t arr_char by blast
              show "Dom (mksta (Cod t) (Dom t) U \<star> t) = Dom (dom t)"
                using t u sta_mksta mkarr_def by simp
              show "Cod (mksta (Cod t) (Dom t) U \<star> t) = Cod (dom t)"
                using t u sta_mksta mkarr_def by simp
              show "Trn (mksta (Cod t) (Dom t) U \<star> t) = Trn (dom t)"
              proof -
                have "Trn (mksta (Cod t) (Dom t) U \<star> t) =
                      C.map (BA.MkIde U, Trn t)"
                  using t u Trn_hcomp mkarr_def by auto
                also have "... = C'.Currying.A_BC.MkArr
                                      (U \<circ> Src t) (U \<circ> Trg t) (U \<circ> Map t)"
                  unfolding C.map_eq
                  using t U.transformation_axioms arr_char by auto
                also have "... = Trn (dom t)"
                  using t U inverse_simulations.inv' dom_char mkobj_simps(3)
                  by auto
                finally show ?thesis by blast
              qed
            qed
            thus ?thesis
              using t H.ide_dom by auto
          qed
          show "obj (hcomp t ?u)"
          proof -
            have "hcomp t ?u = cod t"
            proof (intro arr_eqI)
              show "t \<star> mksta (Cod t) (Dom t) U \<noteq> Null"
                using t U.transformation_axioms sta_mksta V.not_arr_null  
                      null_char seq
                by force
              show "cod t \<noteq> Null"
                using t arr_char by blast
              show "Dom (t \<star> mksta (Cod t) (Dom t) U) = Dom (cod t)"
                using t u sta_mksta mkarr_def by simp
              show "Cod (t \<star> mksta (Cod t) (Dom t) U) = Cod (cod t)"
                using t u sta_mksta mkarr_def by simp
              show "Trn (t \<star> mksta (Cod t) (Dom t) U) = Trn (cod t)"
              proof -
                have "Trn (t \<star> mksta (Cod t) (Dom t) U) =
                      C'.map (Trn t, BA.MkIde U)"
                  using t u Trn_hcomp mkarr_def by auto
                also have "... = C.Currying.A_BC.MkArr
                                      (Src t \<circ> U) (Trg t \<circ> U) (Map t \<circ> U)"
                  unfolding C'.map_eq
                  using t U.transformation_axioms arr_char by auto
                also have "... = Trn (cod t)"
                  using t U inverse_simulations.inv cod_char mkobj_simps(3)
                  by auto
                finally show ?thesis by blast
              qed
            qed
            thus ?thesis
              using t H.ide_cod by auto
          qed
        qed
        thus "H.iso t" by blast
      qed
    qed

  end

  subsection "Terminal Object"

  text\<open>
    The object corresponding to the one-arrow RTS is a terminal object.
    We don't want too much clutter in @{locale rtscatx}, so we prove everything
    in a separate locale and then transfer only what we want to @{locale rtscatx}.
  \<close>

  locale terminal_object_in_rtscat =
    rtscatx arr_type
  for arr_type :: "'A itself"
  begin

    sublocale One: one_arr_rts arr_type ..
    interpretation I\<^sub>1: identity_simulation One.resid ..

    abbreviation one  ("\<^bold>\<one>")
    where "one \<equiv> mkobj One.resid"

    lemma obj_one:
    shows "obj \<^bold>\<one>"
      using obj_mkobj One.is_extensional_rts One.small_rts_axioms by blast

    definition trm
    where "trm a \<equiv> MkArr (Dom a) One.resid
                     (exponential_rts.MkIde
                       (constant_simulation.map (Dom a) One.resid One.the_arr))"

    lemma one_universality:
    assumes "obj a"
    shows "\<guillemotleft>trm a : a \<rightarrow> \<^bold>\<one>\<guillemotright>"
    and "\<And>t. \<guillemotleft>t : a \<rightarrow> \<^bold>\<one>\<guillemotright> \<Longrightarrow> t = trm a"
    and "\<exists>!t. \<guillemotleft>t : a \<rightarrow> \<^bold>\<one>\<guillemotright>"
    proof -
      interpret A: extensional_rts \<open>Dom a\<close>
        using assms obj_char arr_char by blast
      interpret A: small_rts \<open>Dom a\<close>
        using assms obj_char arr_char by blast
      interpret A_One: exponential_rts \<open>Dom a\<close> One.resid ..
      interpret Trm: constant_simulation \<open>Dom a\<close> One.resid One.the_arr
        using One.ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S
        by unfold_locales auto
      interpret Trm: simulation_as_transformation \<open>Dom a\<close> One.resid Trm.map ..
      have Dom_trm: "Dom (trm a) = Dom a"
        using trm_def by simp
      have Cod_trm: "Cod (trm a) = One.resid"
        using trm_def by auto
      show 1: "\<guillemotleft>trm a : a \<rightarrow> \<^bold>\<one>\<guillemotright>"
      proof -
        have a: "mksta (Dom a) (Dom a) (I (Dom a)) = a"
          using assms bij_mkobj(4) [of a] mkobj_def mkarr_def by auto
        have t: "arr (trm a)"
          using assms obj_char arr_char One.is_extensional_rts One.small_rts_axioms
                A_One.ide_MkIde A_One.ide_implies_arr Trm.transformation_axioms
          by (unfold trm_def, intro arr_MkArr) auto
        show ?thesis
          using a t dom_char cod_char Dom_trm Cod_trm mkobj_def mkarr_def
          by (intro H.in_homI) auto
      qed
      show "\<And>t. \<guillemotleft>t : a \<rightarrow> \<^bold>\<one>\<guillemotright> \<Longrightarrow> t = trm a"
      proof (intro arr_eqI)
        fix t
        assume t: "\<guillemotleft>t : a \<rightarrow> \<^bold>\<one>\<guillemotright>"
        show "t \<noteq> Null"
          using t arr_char [of t] by auto
        show "trm a \<noteq> Null"
          using 1 arr_char [of "trm a"] by auto
        show "Dom t = Dom (trm a)"
          using t 1 trm_def dom_char by auto
        show "Cod t = Cod (trm a)"
          using t 1 cod_char mkobj_def
          by (metis (no_types, lifting) Cod.simps(1) H.in_homE)
        show "Trn t = Trn (trm a)"
        proof (intro A_One.arr_eqI)
          have 2: "\<And>F G. \<lbrakk>simulation (Dom a) One.resid F;
                          simulation (Dom a) One.resid G\<rbrakk>
                            \<Longrightarrow> F = G"
            using A.rts_axioms One.universality by blast
          show 3: "A_One.arr (Trn t)"
            using assms t arr_char mkobj_def
            by (metis (no_types, lifting) H.ideD(1-2) H.in_homE
                H_arr_char cod_char dom_char arr.simps(1))
          show 4: "A_One.arr (Trn (trm a))"
            using 1 trm_def H.in_homE H_arr_char by auto
          show "A_One.Dom (Trn t) = A_One.Dom (Trn (trm a))"
            using 2 3 4 trm_def A_One.ide_MkIde A_One.ide_src A_One.src_simp
            by metis
          show "A_One.Cod (Trn t) = A_One.Cod (Trn (trm a))"
            using 2 3 4 trm_def A_One.arr_char transformation.axioms(4)
            by metis
          show "\<And>x. A.ide x \<Longrightarrow>
                       A_One.Map (Trn t) x = A_One.Map (Trn (trm a)) x"
            using 3 trm_def A_One.con_char One.arr_char One.con_char by force
        qed
      qed
      thus "\<exists>!t. \<guillemotleft>t : a \<rightarrow> \<^bold>\<one>\<guillemotright>"
        using 1 by blast
    qed

    lemma terminal_one:
    shows "H.terminal \<^bold>\<one>"
      using one_universality H.terminal_def obj_one by blast

    lemma trm_in_hom [intro, simp]:
    assumes "obj a"
    shows "\<guillemotleft>trm a : a \<rightarrow> \<^bold>\<one>\<guillemotright>"
      using assms one_universality by simp

    lemma terminal_arrow_is_sta:
    assumes "\<guillemotleft>t : a \<rightarrow> \<^bold>\<one>\<guillemotright>"
    shows "sta t"
    proof -
      have "src t = t"
        using assms H.ide_dom one_universality(3)
        by (metis (no_types, lifting) H.in_homE H.terminal_arr_unique
            cod_src dom_src src.preserves_arr terminal_one)
      thus ?thesis
        using assms
        by (metis (no_types, lifting) H.arrI V.ide_iff_src_self arr_coincidence)
    qed

    text\<open>
      For any object \<open>a\<close> we have an RTS isomorphism \<open>Dom a \<cong> HOM \<^bold>\<one> a\<close>.
      Note that these are \emph{not} at the same type.
    \<close>

    abbreviation UP ::  "'A arr \<Rightarrow> 'A \<Rightarrow> 'A arr"
    where "UP a \<equiv> MkArr\<^sub>e\<^sub>x\<^sub>t (\\\<^sub>1) (Dom a) \<circ> exponential_by_One.Up (Dom a)"

    abbreviation DN :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A"
    where "DN a \<equiv> exponential_by_One.Dn (Dom a) \<circ> Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> a"

    lemma inverse_simulations_DN_UP:
    assumes "obj a"
    shows "inverse_simulations (Dom a) (HOM \<^bold>\<one> a) (DN a) (UP a)"
    and "isomorphic_rts (Dom a) (HOM \<^bold>\<one> a)"
    proof -
      interpret A: extensional_rts \<open>Dom a\<close>
        using assms obj_char arr_char by blast
      interpret A: small_rts \<open>Dom a\<close>
        using assms obj_char arr_char by blast
      interpret Exp: exponential_rts One.resid \<open>Dom a\<close> ..
      interpret HOM: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright>\<close>
        using assms sub_rts_HOM by blast
      interpret exponential_by_One arr_type \<open>Dom a\<close> ..
      interpret Dom_Exp: inverse_simulations \<open>Dom a\<close> Exp.resid Dn Up
        using inverse_simulations_Dn_Up by blast
      interpret Trn_MkArr: inverse_simulations Exp.resid HOM.resid
                             \<open>Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> a\<close> \<open>MkArr\<^sub>e\<^sub>x\<^sub>t One.resid (Dom a)\<close>
        using assms inverse_simulations_Trn_MkArr [of One.resid "Dom a"]
              bij_mkobj(4) [of a] A.extensional_rts_axioms A.small_rts_axioms
              One.extensional_rts_axioms One.small_rts_axioms mkobj_def
        apply auto[1]
        by metis
      show "inverse_simulations (Dom a) HOM.resid
              (Dn \<circ> Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> a) (MkArr\<^sub>e\<^sub>x\<^sub>t One.resid (Dom a) \<circ> Up)"
        using inverse_simulations_compose Dom_Exp.inverse_simulations_axioms
              Trn_MkArr.inverse_simulations_axioms
        by blast
      thus "isomorphic_rts (Dom a) (HOM \<^bold>\<one> a)"
        using isomorphic_rts_def by blast
    qed

    lemma terminal_char:
    shows "H.terminal x \<longleftrightarrow> obj x \<and> (\<exists>!t. residuation.arr (Dom x) t)"
    proof (intro iffI conjI)
      (*
       * TODO: I would love to be able to figure out how to make reasoning like
       * this about Ex1 and bij_betw easier to carry out.
       *)
      assume x: "H.terminal x"
      show obj_x: "obj x"
        using x H.terminal_def by fastforce
      interpret X: extensional_rts \<open>Dom x\<close>
        using obj_x obj_char arr_char by blast
      have 1: "H.isomorphic x \<^bold>\<one>"
        using x obj_char terminal_one H.terminal_objs_isomorphic by force
      obtain f where f: "\<guillemotleft>f : x \<rightarrow> \<^bold>\<one>\<guillemotright> \<and> H.iso f"
        using 1 H.isomorphic_def by auto
      have ide_f: "sta f"
        using f iso_implies_sta by blast
      show "\<exists>!t. residuation.arr (Dom x) t"
      proof -
        have "card (Collect (residuation.arr (Dom x))) = 1"
        proof -
          have "bij_betw (Map f) (Collect X.arr) (Collect One.arr)"
          proof -
            have "Dom f = Dom x" and "Cod f = One.resid"
              using f dom_char cod_char mkobj_def by auto
            thus ?thesis
              by (metis (no_types, lifting) f
                  invertible_simulation.is_bijection_betw_arr_sets iso_char)
          qed
          moreover have "card (Collect One.arr) = 1"
            by (simp add: Collect_cong One.arr_char)
          ultimately show ?thesis
            by (simp add: bij_betw_same_card)
        qed
        thus ?thesis
          by (metis CollectI Collect_empty_eq One_nat_def card_1_singleton_iff
              card_eq_0_iff singleton_iff zero_neq_one)
      qed
      next
      assume x: "obj x \<and> (\<exists>!t. residuation.arr (Dom x) t)"
      interpret X: extensional_rts \<open>Dom x\<close>
        using x obj_char arr_char by blast
      interpret T: simulation \<open>Dom x\<close> One.resid \<open>One.terminator (Dom x)\<close>
        using x One.terminator_is_simulation obj_char arr_char small_rts_def
        by blast
      have "bij_betw (One.terminator (Dom x)) (Collect X.arr) (Collect One.arr)"
      proof (unfold bij_betw_def, intro conjI)
        show "inj_on (One.terminator (Dom x)) (Collect X.arr)"
          using x T.simulation_axioms
          by (intro inj_onI) auto
        show "One.terminator (Dom x) ` Collect X.arr = Collect One.arr"
        proof
          show "One.terminator (Dom x) ` Collect X.arr \<subseteq> Collect One.arr"
            by auto
          show "Collect One.arr \<subseteq> One.terminator (Dom x) ` Collect X.arr"
            using x T.simulation_axioms One.arr_char T.preserves_reflects_arr
            by (metis (no_types, lifting) CollectD CollectI image_iff subsetI)
        qed
      qed
      hence 2: "invertible_simulation (Dom x) One.resid (One.terminator (Dom x))"
        using invertible_simulation_iff
                [of "Dom x" One.resid "One.terminator (Dom x)"]
              One.con_implies_arr
        by (metis T.simulation_axioms X.arrE T.preserves_reflects_arr x)
      have 3: "sta (mksta (Dom x) One.resid (One.terminator (Dom x)))"
        using x T.simulation_axioms obj_char iso_char sta_mksta(1)
              arr_char One.small_rts_axioms One.extensional_rts_axioms
              invertible_simulation_def
        by blast
      have 4: "H.iso (mksta (Dom x) One.resid (One.terminator (Dom x)))"
        unfolding iso_char
        using 2 3 bij_mksta(3) sta_char mkarr_def
        by (metis Cod_mkarr Dom_mkarr Map_simps(4) Src_mkarr Trg_mkarr
            V.ide_implies_arr V.trg_ide)
      interpret T: simulation_as_transformation
                     \<open>Dom x\<close> One.resid \<open>One.terminator (Dom x)\<close>
        ..
      have "H.isomorphic x \<^bold>\<one>"
        using x 4 obj_char arr_char mkarr_simps(1-2) One.small_rts_axioms
              One.extensional_rts_axioms T.transformation_axioms
              H.isomorphicI [of "mksta (Dom x) (\\\<^sub>1) (One.terminator (Dom x))"]
        by (simp add: arr_mkarr(4-5))
      thus "H.terminal x"
        using H.isomorphic_symmetric H.isomorphic_to_terminal_is_terminal
              terminal_one
        by blast
    qed

  end

  text\<open>
    The above was all carried out in a separate locale.  Here we transfer to
    @{locale rtscatx} just the final definitions and facts that we want.
  \<close>

  context rtscatx
  begin

    sublocale One: one_arr_rts arr_type ..

    definition one  ("\<^bold>\<one>")
    where "one \<equiv> terminal_object_in_rtscat.one"

    definition trm
    where "trm = terminal_object_in_rtscat.trm"

    interpretation Trm: terminal_object_in_rtscat ..
    no_notation Trm.one  ("\<^bold>\<one>")

    lemma obj_one [intro, simp]:
    shows "obj one"
      unfolding one_def
      using Trm.obj_one by blast

    lemma trm_simps' [simp]:
    assumes "obj a"
    shows "arr (trm a)" and "dom (trm a) = a" and "cod (trm a) = \<^bold>\<one>"
    and "src (trm a) = trm a" and "trg (trm a) = trm a"
    and "sta (trm a)"
    proof -
      show "arr (trm a)" and "dom (trm a) = a" and "cod (trm a) = \<^bold>\<one>"
        unfolding trm_def one_def
        using assms Trm.terminal_arrow_is_sta H.in_homE
          by auto blast+
      show "src (trm a) = trm a" and "trg (trm a) = trm a" and "sta (trm a)"
        using Trm.terminal_arrow_is_sta Trm.trm_in_hom V.src_ide
              V.trg_ide assms trm_def
        by (metis (no_types, lifting))+
    qed

    sublocale category_with_terminal_object hcomp
      using Trm.terminal_one H.terminal_def Trm.obj_one
      by unfold_locales auto

    sublocale elementary_category_with_terminal_object hcomp one trm
      using Trm.obj_one Trm.trm_in_hom
      by unfold_locales
         (auto simp add: Trm.one_universality(2) one_def trm_def)

    lemma is_elementary_category_with_terminal_object:
    shows "elementary_category_with_terminal_object hcomp one trm"
      ..

    lemma terminal_char:
    shows "H.terminal x \<longleftrightarrow> obj x \<and> (\<exists>!t. residuation.arr (Dom x) t)"
      using Trm.terminal_char by simp

    lemma Map_trm:
    assumes "obj a"
    shows "Map (trm a) =
           constant_simulation.map (Dom a) One.resid One.the_arr"
    proof -
      interpret A: extensional_rts \<open>Dom a\<close>
        using assms obj_char arr_char by blast
      interpret A1: exponential_rts \<open>Dom a\<close> One.resid ..
      show ?thesis
        using assms trm_def Trm.trm_def
        by (metis A1.Map.simps(1) Trn.simps(1) comp_apply)
    qed

    lemma inverse_simulations_DN_UP:
    assumes "obj a"
    shows "inverse_simulations (Dom a) (HOM \<^bold>\<one> a) (Trm.DN a) (Trm.UP a)"
    and "isomorphic_rts (Dom a) (HOM \<^bold>\<one> a)"
      unfolding one_def
      using assms Trm.inverse_simulations_DN_UP by auto

    abbreviation UP\<^sub>r\<^sub>t\<^sub>s :: "'A arr \<Rightarrow> 'A \<Rightarrow> 'A arr"
    where "UP\<^sub>r\<^sub>t\<^sub>s a \<equiv> MkArr\<^sub>e\<^sub>x\<^sub>t (\\\<^sub>1) (Dom a) \<circ> exponential_by_One.Up (Dom a)"

    abbreviation DN\<^sub>r\<^sub>t\<^sub>s :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A"
    where "DN\<^sub>r\<^sub>t\<^sub>s a \<equiv> exponential_by_One.Dn (Dom a) \<circ> Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> a"

    lemma UP_DN_naturality:
    assumes "arr t"
    shows "DN\<^sub>r\<^sub>t\<^sub>s (cod t) \<circ> cov_HOM \<^bold>\<one> t = Map t \<circ> DN\<^sub>r\<^sub>t\<^sub>s (dom t)"
    and "UP\<^sub>r\<^sub>t\<^sub>s (cod t) \<circ> Map t = cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s (dom t)"
    and "cov_HOM \<^bold>\<one> t = UP\<^sub>r\<^sub>t\<^sub>s (cod t) \<circ> Map t \<circ> DN\<^sub>r\<^sub>t\<^sub>s (dom t)"
    and "Map t = DN\<^sub>r\<^sub>t\<^sub>s (cod t) \<circ> cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s (dom t)"
    proof -
      let ?a = "dom t" and ?b = "cod t"
      let ?A = "Dom t" and ?B = "Cod t"
      have a: "obj ?a" and b: "obj ?b"
        using assms by auto
      have t: "\<guillemotleft>t : ?a \<rightarrow> ?b\<guillemotright>"
        using assms by auto
      have a_simp: "mksta ?A ?A (I ?A) = ?a"
        using assms a bij_mkobj(4) dom_char mkobj_def mkarr_def by simp
      have b_simp: "mksta ?B ?B (I ?B) = ?b"
        using assms b bij_mkobj(4) cod_char mkobj_def mkarr_def by simp
      have one_simp: "mksta One.resid One.resid (I One.resid) = one"
        unfolding one_def mkarr_def
        by (simp add: mkobj_def)
      interpret A: extensional_rts ?A
        using assms by blast
      interpret A: small_rts ?A
        using assms by blast
      interpret B: extensional_rts ?B
        using assms by blast
      interpret B: small_rts ?B
        using assms by blast
      interpret OneA: exponential_by_One arr_type ?A ..
      interpret OneB: exponential_by_One arr_type ?B ..
      interpret HOM_1a: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> ?a\<guillemotright>\<close>
        using a sub_rts_HOM by blast
      interpret HOM_1a: sub_rts_of_extensional_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> ?a\<guillemotright>\<close> ..
      interpret HOM_1b: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> ?b\<guillemotright>\<close>
        using b sub_rts_HOM by blast
      interpret HOM_1b: sub_rts_of_extensional_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> ?b\<guillemotright>\<close> ..
      interpret Trn_MkArr_a: inverse_simulations OneA.resid \<open>HOM \<^bold>\<one> ?a\<close>
                               \<open>Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> ?a\<close> \<open>MkArr\<^sub>e\<^sub>x\<^sub>t One.resid ?A\<close>
      proof -
        show "inverse_simulations OneA.resid (HOM \<^bold>\<one> ?a)
                (Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> ?a) (MkArr\<^sub>e\<^sub>x\<^sub>t One.resid ?A)"
          using assms inverse_simulations_Trn_MkArr(1) [of One.resid ?A]
          unfolding one_def mkobj_def
          apply simp
          by (metis A.extensional_rts_axioms A.small_rts_axioms
              One.is_extensional_rts One.small_rts_axioms a_simp mkarr_def)
      qed
      interpret Trn_MkArr_b: inverse_simulations OneB.resid \<open>HOM \<^bold>\<one> ?b\<close>
                               \<open>Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> ?b\<close> \<open>MkArr\<^sub>e\<^sub>x\<^sub>t One.resid ?B\<close>
      proof -
        show "inverse_simulations OneB.resid (HOM \<^bold>\<one> ?b)
                (Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> ?b) (MkArr\<^sub>e\<^sub>x\<^sub>t One.resid ?B)"
          using assms inverse_simulations_Trn_MkArr(1) [of One.resid ?B]
          unfolding one_def mkobj_def
          apply simp
          by (metis B.extensional_rts_axioms B.small_rts_axioms
              One.is_extensional_rts One.small_rts_axioms b_simp mkarr_def)
      qed
      have UP_a: "UP\<^sub>r\<^sub>t\<^sub>s ?a = MkArr\<^sub>e\<^sub>x\<^sub>t (\\\<^sub>1) ?A \<circ> OneA.Up"
        using assms t Dom_dom by presburger
      have UP_b: "UP\<^sub>r\<^sub>t\<^sub>s ?b = MkArr\<^sub>e\<^sub>x\<^sub>t (\\\<^sub>1) ?B \<circ> OneB.Up"
        using assms t Dom_cod by presburger
      have DN_a: "DN\<^sub>r\<^sub>t\<^sub>s ?a = OneA.Dn \<circ> Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> ?a"
        using assms t Dom_dom by presburger
      have DN_b: "DN\<^sub>r\<^sub>t\<^sub>s ?b = OneB.Dn \<circ> Trn\<^sub>e\<^sub>x\<^sub>t \<^bold>\<one> ?b"
        using assms t Dom_cod by presburger
      interpret UP_DN_a: inverse_simulations ?A HOM_1a.resid
                           \<open>DN\<^sub>r\<^sub>t\<^sub>s ?a\<close> \<open>UP\<^sub>r\<^sub>t\<^sub>s ?a\<close>
        using a t DN_a UP_a OneA.inverse_simulations_Dn_Up
              Trn_MkArr_a.inverse_simulations_axioms
              inverse_simulations_compose
        by fastforce
      interpret UP_DN_b: inverse_simulations ?B HOM_1b.resid
                           \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b\<close> \<open>UP\<^sub>r\<^sub>t\<^sub>s ?b\<close>
        using b t DN_b UP_b OneB.inverse_simulations_Dn_Up
              Trn_MkArr_b.inverse_simulations_axioms
              inverse_simulations_compose
        by fastforce
      interpret T: transformation ?A ?B \<open>Src t\<close> \<open>Trg t\<close> \<open>Map t\<close>
        using assms(1) arr_char [of t]
        by (simp add: A.rts_axioms A.weak_extensionality B.extensional_rts_axioms
            exponential_rts.arr_char exponential_rts.intro
            weakly_extensional_rts.intro weakly_extensional_rts_axioms.intro)
      interpret T': transformation \<open>HOM \<^bold>\<one> ?a\<close> \<open>HOM \<^bold>\<one> ?b\<close>
                      \<open>cov_HOM \<^bold>\<one> (src t)\<close> \<open>cov_HOM \<^bold>\<one> (trg t)\<close> \<open>cov_HOM \<^bold>\<one> t\<close>
        using assms(1) transformation_cov_HOM_arr [of "\<^bold>\<one>" t] obj_one by blast

      interpret LHS: transformation \<open>HOM \<^bold>\<one> ?a\<close> ?B
                       \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> (src t)\<close>
                       \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> (trg t)\<close>
                       \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> t\<close>
        using assms transformation_whisker_left UP_DN_b.F.simulation_axioms
              T'.F.simulation_axioms T'.G.simulation_axioms T'.transformation_axioms
              B.weakly_extensional_rts_axioms DN_b
        by fastforce
      interpret RHS: transformation \<open>HOM \<^bold>\<one> ?a\<close> ?B
                       \<open>Src t \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a\<close> \<open>Trg t \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a\<close> \<open>Map t \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a\<close>
        using assms
              transformation_whisker_right
                [of ?A ?B "Src t" "Trg t" "Map t" HOM_1a.resid "DN\<^sub>r\<^sub>t\<^sub>s ?a"]
              UP_DN_a.F.simulation_axioms T.transformation_axioms
              HOM_1a.weakly_extensional_rts_axioms DN_a
        by auto
      show 1: "DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> t = Map t \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a"
      proof
        fix x
        show "(DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> t) x = (Map t \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a) x"
        proof (cases "HOM_1a.arr x")
          show "\<not> HOM_1a.arr x \<Longrightarrow> ?thesis"
            using LHS.extensional RHS.extensional by auto
          assume x: "HOM_1a.arr x"
          have Trn_x: "OneA.arr (Trn x)"
            using Trn_MkArr_a.F.preserves_reflects_arr x by presburger
          have Trn_tx: "OneB.arr (Trn (t \<star> x))"
            using x t T'.preserves_arr Trn_MkArr_b.F.preserves_reflects_arr
            by presburger
          show ?thesis
            using assms x Map_hcomp Trn_tx Dom_cod T'.preserves_arr
                  HOM_1b.arr_char HOM_1b.inclusion T'.preserves_arr Trn_x
            by (auto simp add: one_def)
        qed
      qed
      show "cov_HOM \<^bold>\<one> t = UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> Map t \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a"
      proof -
        have "cov_HOM \<^bold>\<one> t = (UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?b) \<circ> cov_HOM \<^bold>\<one> t"
          using b t comp_identity_transformation [of HOM_1a.resid HOM_1b.resid]
                T'.transformation_axioms UP_DN_b.inv UP_b DN_b
          by force
        also have "... = UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> t)"
          by auto
        also have "... = UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> (Map t \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a)"
          using 1 by simp
        also have "... = UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> Map t \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a"
          by auto
        finally show ?thesis by blast
      qed
      show 2: "UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> Map t = cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a"
      (* TODO: I don't have a clue why this doesn't go through easily. *)
      proof -
        have "UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> Map t = UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> (Map t \<circ> (DN\<^sub>r\<^sub>t\<^sub>s ?a \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a))"
          using a t T.transformation_axioms UP_a DN_a
                UP_DN_a.inverse_simulations_axioms
          by (simp add: comp_transformation_identity inverse_simulations.inv')
        also have "... = UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)"
          using 1 by auto
        also have "... = UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> (cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a))"
          using Fun.comp_assoc [of "DN\<^sub>r\<^sub>t\<^sub>s ?b" "cov_HOM \<^bold>\<one> t" "UP\<^sub>r\<^sub>t\<^sub>s ?a"] by force
        also have "... = (UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?b) \<circ> (cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)"
          using Fun.comp_assoc [of "UP\<^sub>r\<^sub>t\<^sub>s ?b" "DN\<^sub>r\<^sub>t\<^sub>s ?b" "cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a"]
          by force
        also have "... = I HOM_1b.resid \<circ> (cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)"
          using UP_DN_b.inv by force
        also have "... = I HOM_1b.resid \<circ> cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a"
          using Fun.comp_assoc [of "I HOM_1b.resid" "cov_HOM \<^bold>\<one> t" "UP\<^sub>r\<^sub>t\<^sub>s ?a"]
          by force
        also have "... = cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a"
          using comp_identity_transformation
                  [of HOM_1a.resid HOM_1b.resid "cov_HOM \<^bold>\<one> (src t)"
                      "cov_HOM \<^bold>\<one> (trg t)" "cov_HOM \<^bold>\<one> t"]
                T'.transformation_axioms
          by fastforce
        finally show ?thesis by blast
      qed
      show "Map t = DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a"
      proof -
        have "Map t = DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> Map t"
        proof -
          have "Map t = I (Cod t) \<circ> Map t"
            using T.transformation_axioms
                  comp_identity_transformation [of "Dom t" "Cod t"]
            by auto
          also have "... = DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> Map t"
            using b UP_b DN_b UP_DN_b.inverse_simulations_axioms
                  inverse_simulations.inv'
            by (metis (no_types, lifting))
          finally show ?thesis by blast
        qed
        also have "... = DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> (UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> Map t)"
          by auto
        also have "... = DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> (cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)"
          using 2 by simp
        also have "... = DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> t \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a"
          using comp_assoc [of "DN\<^sub>r\<^sub>t\<^sub>s ?b" "cov_HOM \<^bold>\<one> t" "UP\<^sub>r\<^sub>t\<^sub>s ?a"] by metis
        finally show ?thesis by blast
      qed
    qed

    text\<open>
      Equality of parallel arrows \<open>\<guillemotleft>u : a \<rightarrow> b\<guillemotright>\<close> and \<open>\<guillemotleft>v : a \<rightarrow> b\<guillemotright>\<close> is determined by
      their compositions with global transitions \<open>\<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright>\<close>.
    \<close>

    lemma arr_extensionality:
    assumes "\<guillemotleft>u : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>v : a \<rightarrow> b\<guillemotright>" and "src u = src v" and "trg u = trg v"
    shows "u = v \<longleftrightarrow> (\<forall>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright> \<longrightarrow> u \<star> t = v \<star> t)"
    proof
      have a: "obj a" and b: "obj b"
        using assms(1) by auto
      have A: "small_rts (Dom a) \<and> extensional_rts (Dom a)"
      and B: "small_rts (Dom b) \<and> extensional_rts (Dom b)"
        using a b obj_char arr_char by blast+
      interpret A: extensional_rts \<open>Dom a\<close>
        using A by blast
      interpret B: extensional_rts \<open>Dom b\<close>
        using B by blast
      interpret AB: exponential_rts \<open>Dom a\<close> \<open>Dom b\<close> ..
      have "Dom u = Dom a" and "Cod u = Dom b"
        using assms(1) Dom_dom Dom_cod by auto
      have "Dom v = Dom a" and "Cod v = Dom b"
        using assms(2) Dom_dom Dom_cod by auto
      have "Map (src u) = Src u" and "Map (trg u) = Trg u"
        using assms(1) Map_simps(3-4) by fastforce+
      have "Map (src v) = Src v" and "Map (trg v) = Trg v"
        using assms(2) Map_simps(3-4) by fastforce+
      interpret U: transformation \<open>Dom a\<close> \<open>Dom b\<close>
                     \<open>Map (src u)\<close> \<open>Map (trg u)\<close> \<open>Map u\<close>
        using assms(1) arr_char [of u] AB.arr_char [of "Trn u"]
              \<open>Dom u = Dom a\<close> \<open>Cod u = Dom b\<close>
              \<open>Map (src u) = Src u\<close> \<open>Map (trg u) = Trg u\<close>
        by auto
      interpret V: transformation \<open>Dom a\<close> \<open>Dom b\<close>
                     \<open>Map (src v)\<close> \<open>Map (trg v)\<close> \<open>Map v\<close>
        using assms(2) arr_char [of v] AB.arr_char [of "Trn v"]
              \<open>Dom v = Dom a\<close> \<open>Cod v = Dom b\<close>
              \<open>Map (src v) = Src v\<close> \<open>Map (trg v) = Trg v\<close>
        by auto
      show "u = v \<Longrightarrow> \<forall>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright> \<longrightarrow> u \<star> t = v \<star> t"
        by blast
      show "\<forall>t. \<guillemotleft>t : one \<rightarrow> a\<guillemotright> \<longrightarrow> u \<star> t = v \<star> t \<Longrightarrow> u = v"
      proof (intro arr_eqI)
        assume 1: "\<forall>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright> \<longrightarrow> u \<star> t = v \<star> t"
        show "u \<noteq> Null"
          using assms(1) arr_char by fastforce
        show "v \<noteq> Null"
          using assms(2) arr_char by fastforce
        show "Dom u = Dom v"
          using \<open>Dom u = Dom a\<close> \<open>Dom v = Dom a\<close> by auto
        show "Cod u = Cod v"
          using \<open>Cod u = Dom b\<close> \<open>Cod v = Dom b\<close> by presburger
        show "Trn u = Trn v"
        proof (intro AB.arr_eqI)
          show "AB.arr (Trn u)"
            using assms(1) arr_char [of u] \<open>Dom u = Dom a\<close> \<open>Cod u = Dom b\<close>
            by auto
          show "AB.arr (Trn v)"
            using assms(2) arr_char [of v] \<open>Dom v = Dom a\<close> \<open>Cod v = Dom b\<close>
            by auto
          show "AB.Dom (Trn u) = AB.Dom (Trn v)"
            using assms(3) arr_char arr_char \<open>Map (src u) = Src u\<close>
                  \<open>Map (src v) = Src v\<close>
            by auto
          show "AB.Cod (Trn u) = AB.Cod (Trn v)"
            using assms(4) arr_char arr_char \<open>Map (trg u) = Trg u\<close>
                  \<open>Map (trg v) = Trg v\<close>
            by auto
          have "Map u = Map v"
          proof -
            have "\<And>Q R T. transformation One.resid (Dom a) Q R T
                             \<Longrightarrow> Map u \<circ> T = Map v \<circ> T"
            proof -
              fix Q R T
              assume 2: "transformation One.resid (Dom a) Q R T"
              interpret T: transformation One.resid \<open>Dom a\<close> Q R T
                using 2 by blast
              let ?t = "mkarr One.resid (Dom a) Q R T"
              have t: "\<guillemotleft>?t : \<^bold>\<one> \<rightarrow> a\<guillemotright>"
                by (metis (no_types, lifting) "2" A H.ideD(2) H.ideD(3) H.ide_in_hom
                    H.in_homI One.is_extensional_rts One.small_rts_axioms Trm.obj_one
                    Trm.one_universality(2) a arr_coincidence arr_mkarr(1) arr_mkarr(5)
                    mkarr_simps(1) mkobj_Dom trm_def trm_simps(3))
              show "Map u \<circ> T = Map v \<circ> T"
                by (metis (no_types, lifting) "1" AB.Map.simps(1) H.seqI' mkarr_def
                    Map_hcomp Trn.simps(1) assms(1) comp_def t)
            qed
            thus "Map u = Map v"
              using assms(3-4)
                    One.eq_transformation_iff U.transformation_axioms V.transformation_axioms
                    A.weakly_extensional_rts_axioms B.weakly_extensional_rts_axioms
                    \<open>Map (src u) = Src u\<close> \<open>Map (trg u) = Trg u\<close>
                    \<open>Map (src v) = Src v\<close> \<open>Map (trg v) = Trg v\<close>
              by metis
          qed
          thus "\<And>a. A.ide a \<Longrightarrow> AB.Map (Trn u) a = AB.Map (Trn v) a" by simp
        qed
      qed
    qed

    lemma sta_extensionality:
    assumes "\<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>" and "\<guillemotleft>g : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>"
    shows "f = g \<longleftrightarrow> (\<forall>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright> \<longrightarrow> f \<star> t = g \<star> t)"
    proof
      have a: "obj a" and b: "obj b"
        using assms(1) by auto
      have A: "small_rts (Dom a) \<and> extensional_rts (Dom a)"
      and B: "small_rts (Dom b) \<and> extensional_rts (Dom b)"
        using a b obj_char arr_char by blast+
      interpret A: extensional_rts \<open>Dom a\<close>
        using A by blast
      interpret B: extensional_rts \<open>Dom b\<close>
        using B by blast
      interpret AB: exponential_rts \<open>Dom a\<close> \<open>Dom b\<close> ..
      have "Dom f = Dom a" and "Cod f = Dom b"
        using assms(1) Dom_dom Dom_cod by auto
      have "Dom g = Dom a" and "Cod g = Dom b"
        using assms(2) Dom_dom Dom_cod by auto
      interpret F: simulation \<open>Dom a\<close> \<open>Dom b\<close> \<open>Map f\<close>
        using assms(1) sta_char [of f] AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S [of "Trn f"]
              \<open>Dom f = Dom a\<close> \<open>Cod f = Dom b\<close>
        by simp
      interpret G: simulation \<open>Dom a\<close> \<open>Dom b\<close> \<open>Map g\<close>
        using assms(2) sta_char [of g] AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S [of "Trn g"]
              \<open>Dom g = Dom a\<close> \<open>Cod g = Dom b\<close>
        by simp
      show "f = g \<Longrightarrow> \<forall>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright> \<longrightarrow> f \<star> t = g \<star> t"
        by blast
      show "\<forall>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright> \<longrightarrow> f \<star> t = g \<star> t \<Longrightarrow> f = g"
      proof -
        assume 1: "\<forall>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright> \<longrightarrow> f \<star> t = g \<star> t"
        have "\<And>Q R T. transformation One.resid (Dom a) Q R T
                         \<Longrightarrow> Map f \<circ> T = Map g \<circ> T"
        proof -
          fix Q R T
          assume 2: "transformation One.resid (Dom a) Q R T"
          interpret T: transformation One.resid \<open>Dom a\<close> Q R T
            using 2 by blast
          let ?t = "mkarr One.resid (Dom a) Q R T"
          have t: "\<guillemotleft>?t : \<^bold>\<one> \<rightarrow> a\<guillemotright>"
            by (metis (no_types, lifting) "2" A H.ideD(2) H.ideD(3) H.ide_in_hom
                H.in_homI One.is_extensional_rts One.small_rts_axioms Trm.obj_one
                Trm.one_universality(2) a arr_coincidence arr_mkarr(1) arr_mkarr(5)
                mkarr_simps(1) mkobj_Dom trm_def trm_simps(3))
          show "Map f \<circ> T = Map g \<circ> T"
            by (metis (no_types, lifting) "1" AB.Map.simps(1) H.seqI' mkarr_def
                Map_hcomp Trn.simps(1) assms(1) comp_apply t)
        qed
        hence 2: "Map f = Map g"
          using One.eq_simulation_iff F.simulation_axioms G.simulation_axioms
                A.weakly_extensional_rts_axioms B.weakly_extensional_rts_axioms
          by blast
        have "f = mksta (Dom a) (Dom b) (Map f)"
          using assms(1) a b A B obj_char arr_char bij_mksta(4) by fastforce
        also have "... = mksta (Dom a) (Dom b) (Map g)"
          using 2 by simp
        also have "... = g"
          using assms(2) a b A B obj_char arr_char bij_mksta(4) by fastforce
        finally show "f = g" by auto
      qed
    qed

    text\<open>
      The mapping @{term "HOM \<^bold>\<one>"}, like @{term Dom}, takes each object to a corresponding RTS,
      but unlike @{term Dom} it stays at type \<open>'A arr\<close>, rather than decreasing
      the type from @{typ "'A arr"} to @{typ 'A}.
    \<close>

    lemma HOM1_mapsto:
    shows "HOM \<^bold>\<one> \<in> Collect obj \<rightarrow> Collect extensional_rts \<inter> Collect small_rts"
    proof
      fix a
      assume a: "a \<in> Collect obj"
      have A: "extensional_rts (HOM \<^bold>\<one> a)"
        using a extensional_rts_HOM by blast
      interpret HOM_1A: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright>\<close>
        using a sub_rts_HOM by simp
      have "small_rts HOM_1A.resid"
      proof -
        have "Collect HOM_1A.arr \<subseteq> H.hom \<^bold>\<one> a"
          using HOM_1A.arr_char by blast
        moreover have "small (H.hom \<^bold>\<one> a)"
          using a small_homs by blast
        ultimately show ?thesis
          using smaller_than_small small_rts_def HOM_1A.rts_axioms
                small_rts_axioms_def
          by blast
      qed
      moreover have "extensional_rts HOM_1A.resid"
        using A by blast
      ultimately show "HOM \<^bold>\<one> a \<in> Collect extensional_rts \<inter> Collect small_rts"
        by blast
    qed

    text\<open>
      The mapping @{term "HOM \<^bold>\<one>"} is not necessarily injective, but it is essentially so.
    \<close>

    lemma HOM1_reflects_isomorphic:
    assumes "obj a" and "obj b" and "isomorphic_rts (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b)"
    shows "H.isomorphic a b"
    proof -
      have 1: "isomorphic_rts (Dom a) (Dom b)"
      proof -
        have "isomorphic_rts (Dom a) (HOM \<^bold>\<one> a)"
          using assms(1) inverse_simulations_DN_UP(2) by blast
        also have "isomorphic_rts ... (HOM \<^bold>\<one> b)"
          using assms(3) by blast
        also have "isomorphic_rts ... (Dom b)"
          using assms(2) inverse_simulations_DN_UP(2) isomorphic_rts_symmetric
          by blast
        finally show ?thesis by blast
      qed
      obtain F G where FG: "inverse_simulations (Dom b) (Dom a) F G"
        using 1 isomorphic_rts_def isomorphic_rts_symmetric by blast
      interpret FG: inverse_simulations \<open>Dom b\<close> \<open>Dom a\<close> F G
        using FG by blast
      let ?f = "mksta (Dom a) (Dom b) F"
      let ?g = "mksta (Dom b) (Dom a) G"
      have f: "\<guillemotleft>?f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>" and g: "\<guillemotleft>?g : b \<rightarrow>\<^sub>s\<^sub>t\<^sub>a a\<guillemotright> \<and> sta ?g"
        using assms(1-2) FG.F.simulation_axioms FG.G.simulation_axioms
              bij_mksta(1) obj_char [of a] obj_char [of b]
              obj_is_sta sta_char sta_mksta(1-3)
        by auto
      have "H.inverse_arrows ?f ?g"
      proof
        show "obj (?g \<star> ?f)"
        proof -
          have "?g \<star> ?f = a"
          proof -
            have gf: "\<guillemotleft>?g \<star> ?f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a a\<guillemotright>"
              using f g Cod.simps(1) Dom.simps(1) H.cod_comp H.dom_comp H_seqI
                    V.ide_implies_arr sta_hcomp
              by blast
            have "?g \<star> ?f = mksta (Dom a) (Dom a) (Map (?g \<star> ?f))"
              using f g gf
              by (metis (no_types, lifting) Cod_mkarr Dom_mkarr Int_Collect
                  Src_mkarr Trg_mkarr V.ide_implies_arr assms(1-2) bij_mksta(3)
                  inf_idem mkarr_comp objE transformation_Map_arr)
            also have "... = mksta (Dom a) (Dom a) (Map ?g \<circ> Map ?f)"
              using gf H.arrI Map_hcomp by force
            also have "... = mksta (Dom a) (Dom a) (G \<circ> F)"
              using assms obj_char arr_char FG.F.simulation_axioms
                    FG.G.simulation_axioms bij_mksta(3)
              by auto
            also have "... = mksta (Dom a) (Dom a) (I (Dom a))"
              using FG.inv by simp
            also have "... = a"
              using assms obj_char mkobj_def mkarr_def by simp
            finally show ?thesis by blast
          qed
          thus "obj (?g \<star> ?f)"
            using assms by simp
        qed
        show "obj (?f \<star> ?g)"
        proof -
          have "?f \<star> ?g = b"
          proof -
            have fg: "\<guillemotleft>?f \<star> ?g : b \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>"
              using f g Cod.simps(1) Dom.simps(1) H.cod_comp H.dom_comp H_seqI
                    V.ide_implies_arr sta_hcomp
              by blast
            have "?f \<star> ?g = mksta (Dom b) (Dom b) (Map (?f \<star> ?g))"
              using f g fg
              by (metis (no_types, lifting) Cod_mkarr Dom_mkarr Int_Collect
                  Src_mkarr Trg_mkarr V.ide_implies_arr assms(1-2) bij_mksta(3)
                  inf_idem mkarr_comp objE transformation_Map_arr)
            also have "... = mksta (Dom b) (Dom b) (Map ?f \<circ> Map ?g)"
              using fg H.arrI Map_hcomp by force
            also have "... = mksta (Dom b) (Dom b) (F \<circ> G)"
              using assms obj_char arr_char FG.F.simulation_axioms
                    FG.G.simulation_axioms bij_mksta(3)
              by auto
            also have "... = mksta (Dom b) (Dom b) (I (Dom b))"
              using FG.inv' by simp
            also have "... = b"
              using assms obj_char mkobj_def mkarr_def by simp
            finally show ?thesis by blast
          qed
          thus "obj (?f \<star> ?g)"
            using assms by simp
        qed
      qed
      hence "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright> \<and> H.iso ?f"
        using f by blast
      thus ?thesis
        using H.isomorphic_def by blast
    qed

  end

  subsection "Products"

  text\<open>
    In this section we show that the category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> has products.
    A product of objects \<open>a\<close> and \<open>b\<close> is obtained by constructing the product
    \<open>Dom a \<times> Dom b\<close> of their underlying RTS's and then showing that there exists an
    object \<open>a \<otimes> b\<close> such that \<open>Dom (a \<otimes> b)\<close> is isomorphic to \<open>Dom a \<times> Dom b\<close>.
    Since \<open>Dom (a \<otimes> b)\<close> will have arrow type @{typ 'A}, but \<open>Dom a \<otimes> Dom b\<close> has arrow type
    @{typ "'A * 'A"}, we need a way to reduce the arrow type of \<open>Dom a \<otimes> Dom b\<close> from
    @{typ "'A * 'A"} to @{typ 'A}.  This is done by using the assumption that the type @{typ 'A}
    admits pairing to obtain an injective map from @{typ "'A * 'A"} to @{typ 'A}, and then
    applying the injective image construction to obtain an RTS with arrow type @{typ 'A}
    that is isomorphic to \<open>Dom a \<otimes> Dom b\<close>.
  \<close>

  locale product_in_rtscat =
    rtscatx arr_type
  for arr_type :: "'A itself"
  and a
  and b +
  assumes obj_a: "obj a"
  and obj_b: "obj b"
  begin

    notation hcomp  (infixr "\<star>" 53)

    interpretation A: extensional_rts \<open>Dom a\<close>
      using obj_a bij_mkobj obj_char by blast
    interpretation A: small_rts \<open>Dom a\<close>
      using obj_a bij_mkobj obj_char by blast
    interpretation B: extensional_rts \<open>Dom b\<close>
      using obj_b bij_mkobj obj_char by blast
    interpretation B: small_rts \<open>Dom b\<close>
      using obj_b bij_mkobj obj_char by blast
    interpretation AB: exponential_rts \<open>Dom a\<close> \<open>Dom b\<close> ..

    sublocale PROD: product_rts \<open>Dom a\<close> \<open>Dom b\<close> ..
    sublocale PROD: product_of_extensional_rts \<open>Dom a\<close> \<open>Dom b\<close> ..
    sublocale PROD: product_of_small_rts \<open>Dom a\<close> \<open>Dom b\<close> ..

    sublocale Prod: inj_image_rts pairing.some_pair PROD.resid
      by (metis (no_types, opaque_lifting) PROD.rts_axioms
          inj_image_rts_axioms_def inj_image_rts_def inj_on_subset
          inj_some_pair top_greatest)
    sublocale Prod: small_rts Prod.resid
      using PROD.small_rts_axioms Prod.preserves_reflects_small_rts
      by unfold_locales (simp add: small_rts.small)
    sublocale Prod: extensional_rts Prod.resid
      using PROD.extensional_rts_axioms Prod.preserves_extensional_rts
      by unfold_locales (simp add: extensional_rts.extensional)

    text\<open>
      The injective image construction on RTS's gives us invertible simulations between
      \<open>Prod.resid\<close> and \<open>PROD.resid\<close>.
    \<close>

    abbreviation Pack :: "'A \<times> 'A \<Rightarrow> 'A"
    where "Pack \<equiv> Prod.map\<^sub>e\<^sub>x\<^sub>t"

    abbreviation Unpack :: "'A \<Rightarrow> 'A \<times> 'A"
    where "Unpack \<equiv> Prod.map'\<^sub>e\<^sub>x\<^sub>t"

    interpretation P\<^sub>1: composite_simulation Prod.resid PROD.resid \<open>Dom a\<close>
                         Unpack PROD.P\<^sub>1
      ..
    interpretation P\<^sub>0: composite_simulation Prod.resid PROD.resid \<open>Dom b\<close>
                         Unpack PROD.P\<^sub>0
      ..

    abbreviation prod :: "'A arr"
    where "prod \<equiv> mkobj Prod.resid"

    lemma obj_prod:
    shows "obj prod"
      using obj_mkobj Prod.extensional_rts_axioms Prod.small_rts_axioms by blast

    lemma Dom_prod [simp]:
    shows "Dom prod = Prod.resid"
      by (simp add: Prod.extensional_rts_axioms Prod.small_rts_axioms)

    definition p\<^sub>0 :: "'A arr"
    where "p\<^sub>0 \<equiv> mksta Prod.resid (Dom b) P\<^sub>0.map"

    definition p\<^sub>1 :: "'A arr"
    where "p\<^sub>1 \<equiv> mksta Prod.resid (Dom a) P\<^sub>1.map"

    lemma p\<^sub>0_simps [simp]:
    shows "sta p\<^sub>0" and "dom p\<^sub>0 = prod" and "cod p\<^sub>0 = b"
    and "Dom p\<^sub>0 = Prod.resid" and "Cod p\<^sub>0 = Dom b"
    and "Trn p\<^sub>0 = exponential_rts.MkIde P\<^sub>0.map"
      using p\<^sub>0_def obj_b B.extensional_rts_axioms B.small_rts_axioms
            P\<^sub>0.simulation_axioms Prod.extensional_rts_axioms
            Prod.small_rts_axioms sta_mksta(1) H.dom_eqI H.cod_eqI
            H_seqI obj_char obj_prod mkarr_def
      by auto

    lemma p\<^sub>1_simps [simp]:
    shows "sta p\<^sub>1" and "dom p\<^sub>1 = prod" and "cod p\<^sub>1 = a"
    and "Dom p\<^sub>1 = Prod.resid" and "Cod p\<^sub>1 = Dom a"
    and "Trn p\<^sub>1 = exponential_rts.MkIde P\<^sub>1.map"
      using p\<^sub>1_def obj_a A.extensional_rts_axioms A.small_rts_axioms
            P\<^sub>1.simulation_axioms Prod.extensional_rts_axioms
            Prod.small_rts_axioms sta_mksta(1) H.dom_eqI H.cod_eqI
            H_seqI obj_char obj_prod mkarr_def
      by auto

    lemma p\<^sub>0_in_hom [intro]:
    shows "\<guillemotleft>p\<^sub>0 : prod \<rightarrow> b\<guillemotright>"
      by auto

    lemma p\<^sub>1_in_hom [intro]:
    shows "\<guillemotleft>p\<^sub>1 : prod \<rightarrow> a\<guillemotright>"
      by auto

    text\<open>
      It should be noted that the length of the proof of the following result is partly
      due to the fact that it is proving something rather stronger than one might
      expect at first blush.  The category we are working with here is analogous to a
      2-category in the sense that there are essentially two classes of arrows:
      \emph{states}, which correspond to simulations between RTS's, and \emph{transitions},
      which correspond to transformations.  The class of states is included
      in the class of transitions.  The universality result below shows the universality
      of the product for the full class of arrows, so it is in that sense analogous to
      showing that the category has 2-products, rather than just ordinary products.
    \<close>

    lemma universality:
    assumes "\<guillemotleft>h : x \<rightarrow> a\<guillemotright>" and "\<guillemotleft>k : x \<rightarrow> b\<guillemotright>"
    shows "\<exists>!m. p\<^sub>1 \<star> m = h \<and> p\<^sub>0 \<star> m = k"
    proof
      interpret X: extensional_rts \<open>Dom x\<close>
        using assms(1) H.in_homE H_arr_char dom_char by auto
      interpret X: small_rts \<open>Dom x\<close>
        using assms(1) H.in_homE H_arr_char dom_char by auto
      interpret A: extensional_rts \<open>Dom a\<close>
        using assms(1) H.in_homE H_arr_char cod_char by auto
      interpret A: small_rts \<open>Dom a\<close>
        using assms(1) H.in_homE H_arr_char cod_char by auto
      interpret B: extensional_rts \<open>Dom b\<close>
        using assms(2) H.in_homE H_arr_char cod_char by auto
      interpret B: small_rts \<open>Dom b\<close>
        using assms(2) H.in_homE H_arr_char cod_char by auto
      interpret XA: exponential_rts \<open>Dom x\<close> \<open>Dom a\<close> ..
      interpret XB: exponential_rts \<open>Dom x\<close> \<open>Dom b\<close> ..
      have *: "Dom h = Dom x \<and> Cod h = Dom a \<and>
               Dom k = Dom x \<and> Cod k = Dom b"
        using assms(1-2) dom_char cod_char by auto
      interpret H\<^sub>0: simulation \<open>Dom x\<close> \<open>Dom a\<close> \<open>Map (src h)\<close>
        by (metis (mono_tags, lifting) * H.arrI H_arr_char Trn.simps(1)
            XA.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S XA.ide_src arr_char assms(1) comp_apply src_char)
      interpret H\<^sub>1: simulation \<open>Dom x\<close> \<open>Dom a\<close> \<open>Map (trg h)\<close>
        by (metis (mono_tags, lifting) * H.arrI H_arr_char Trn.simps(1)
            XA.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S XA.ide_trg arr_char assms(1) comp_apply trg_char)
      interpret K\<^sub>0: simulation \<open>Dom x\<close> \<open>Dom b\<close> \<open>Map (src k)\<close>
        by (metis (mono_tags, lifting) "*" H.arrI H_arr_char Map_simps(3)
            XB.arrE arr_char assms(2) comp_apply transformation_def)
      interpret K\<^sub>1: simulation \<open>Dom x\<close> \<open>Dom b\<close> \<open>Map (trg k)\<close>
        by (metis (mono_tags, lifting) "*" H.arrI H_arr_char Map_simps(4)
            XB.arrE arr_char assms(2) comp_apply transformation_def)
      interpret H: transformation \<open>Dom x\<close> \<open>Dom a\<close>
                     \<open>Map (src h)\<close> \<open>Map (trg h)\<close> \<open>Map h\<close>
        using "*" Map_simps(3) Map_simps(4) XA.arr_char arr_char assms(1)
        by (metis H.arrI H_arr_char transformation_Map_arr)
      interpret K: transformation \<open>Dom x\<close> \<open>Dom b\<close>
                     \<open>Map (src k)\<close> \<open>Map (trg k)\<close> \<open>Map k\<close>
        using "*" Map_simps(3) Map_simps(4) XB.arr_char arr_char assms(2)
              H.arrI
        by force

      interpret HK\<^sub>0: simulation \<open>Dom x\<close> PROD.resid
                       \<open>\<langle>\<langle>Map (src h), Map (src k)\<rangle>\<rangle>\<close>
        using assms PROD.universality(1) [of "Dom h" "Map (src h)" "Map (src k)"]
              H\<^sub>0.simulation_axioms K\<^sub>0.simulation_axioms
        by blast
      interpret HK\<^sub>1: simulation \<open>Dom x\<close> PROD.resid
                       \<open>\<langle>\<langle>Map (trg h), Map (trg k)\<rangle>\<rangle>\<close>
        using assms PROD.universality(1) [of "Dom h" "Map (trg h)" "Map (trg k)"]
              H\<^sub>1.simulation_axioms K\<^sub>1.simulation_axioms
        by blast

      interpret PROD.P\<^sub>1: simulation_as_transformation PROD.resid \<open>Dom a\<close>
                           PROD.P\<^sub>1
        ..
      interpret PROD.P\<^sub>0: simulation_as_transformation PROD.resid \<open>Dom b\<close>
                           PROD.P\<^sub>0
        ..
      interpret P\<^sub>1: simulation_as_transformation Prod.resid \<open>Dom a\<close> P\<^sub>1.map ..
      interpret P\<^sub>0: simulation_as_transformation Prod.resid \<open>Dom b\<close> P\<^sub>0.map ..

      interpret P\<^sub>0oHK\<^sub>0: composite_simulation \<open>Dom x\<close> PROD.resid \<open>Dom b\<close>
                          \<open>\<langle>\<langle>Map (src h), Map (src k)\<rangle>\<rangle>\<close> PROD.P\<^sub>0
        .. 
      interpret P\<^sub>0oHK\<^sub>1: composite_simulation \<open>Dom x\<close> PROD.resid \<open>Dom b\<close>
                          \<open>\<langle>\<langle>Map (trg h), Map (trg k)\<rangle>\<rangle>\<close> PROD.P\<^sub>0
        .. 
      interpret P\<^sub>1oHK\<^sub>0: composite_simulation \<open>Dom x\<close> PROD.resid \<open>Dom a\<close>
                          \<open>\<langle>\<langle>Map (src h), Map (src k)\<rangle>\<rangle>\<close> PROD.P\<^sub>1
        .. 
      interpret P\<^sub>1oHK\<^sub>1: composite_simulation \<open>Dom x\<close> PROD.resid \<open>Dom a\<close>
                          \<open>\<langle>\<langle>Map (trg h), Map (trg k)\<rangle>\<rangle>\<close> PROD.P\<^sub>1
        .. 
      interpret HK: transformation \<open>Dom x\<close> PROD.resid
                      \<open>\<langle>\<langle>Map (src h), Map (src k)\<rangle>\<rangle>\<close>
                      \<open>\<langle>\<langle>Map (trg h), Map (trg k)\<rangle>\<rangle>\<close>
                      \<open>\<langle>\<langle>Map h, Map k\<rangle>\<rangle>\<close>
        using assms HK\<^sub>0.simulation_axioms HK\<^sub>1.simulation_axioms
              H.transformation_axioms K.transformation_axioms
        by (metis H\<^sub>0.simulation_axioms H\<^sub>1.simulation_axioms
            K\<^sub>0.simulation_axioms K\<^sub>1.simulation_axioms PROD.proj_tuple(1)
            PROD.universality2(1) PROD.universality(3))
      interpret Pack_o_HK: transformation \<open>Dom h\<close> Prod.resid
                             \<open>Pack \<circ> \<langle>\<langle>Map (src h), Map (src k)\<rangle>\<rangle>\<close>
                             \<open>Pack \<circ> \<langle>\<langle>Map (trg h), Map (trg k)\<rangle>\<rangle>\<close>
                             \<open>Pack \<circ> \<langle>\<langle>Map h, Map k\<rangle>\<rangle>\<close>
        using assms transformation_whisker_left
              Prod.weakly_extensional_rts_axioms HK.transformation_axioms
              Prod.Map.simulation_axioms dom_char
        by fastforce

      let ?hk = "mkarr (Dom h) Prod.resid
                   (Pack \<circ> \<langle>\<langle>Map (src h), Map (src k)\<rangle>\<rangle>)
                   (Pack \<circ> \<langle>\<langle>Map (trg h), Map (trg k)\<rangle>\<rangle>)
                   (Pack \<circ> \<langle>\<langle>Map h, Map k\<rangle>\<rangle>)"
      have hk: "\<guillemotleft>?hk : dom h \<rightarrow> prod\<guillemotright>"
        using assms arr_mkarr arr_char Pack_o_HK.transformation_axioms
              X.extensional_rts_axioms X.small_rts_axioms
              Prod.extensional_rts_axioms Prod.small_rts_axioms
              dom_char cod_char
        by auto
      show "p\<^sub>1 \<star> ?hk = h \<and> p\<^sub>0 \<star> ?hk = k"
      proof
        have seq0: "H.seq p\<^sub>0 ?hk"
          using hk by blast
        have seq1: "H.seq p\<^sub>1 ?hk"
          using hk by blast
        show "p\<^sub>1 \<star> ?hk = h"
        proof (intro arr_eqI)
          show "p\<^sub>1 \<star> ?hk \<noteq> Null"
            using seq1 arr_char by auto
          show "h \<noteq> Null"
            using assms arr_char [of h] by auto
          show Dom: "Dom (p\<^sub>1 \<star> ?hk) = Dom h"
            using seq1 H_seq_char mkarr_def by fastforce
          show Cod: "Cod (p\<^sub>1 \<star> ?hk) = Cod h"
            using "*" H.arrI hk mkarr_def by auto
          show "Trn (p\<^sub>1 \<star> ?hk) = Trn h"
          proof -
            interpret C: COMP \<open>Dom x\<close> Prod.resid \<open>Dom a\<close> ..
            have "Trn (p\<^sub>1 \<star> ?hk) =
                  COMP.map (Dom ?hk) (Cod ?hk) (Cod p\<^sub>1) (Trn p\<^sub>1, Trn ?hk)"
              using assms seq1 Trn_hcomp hk H.seqE mkarr_def by auto
            also have "... =
                       COMP.map (Dom x) Prod.resid (Dom a) (Trn p\<^sub>1, Trn ?hk)"
              using assms hk dom_char mkarr_def by auto
            also have "... =
                       C.BC.MkArr
                         ((P\<^sub>1.map \<circ> Pack) \<circ>
                            \<langle>\<langle>C.BC.Map (Trn (src h)), C.BC.Map (Trn (src k))\<rangle>\<rangle>)
                         ((P\<^sub>1.map \<circ> Pack) \<circ>
                            \<langle>\<langle>C.BC.Map (Trn (trg h)), C.BC.Map (Trn (trg k))\<rangle>\<rangle>)
                         ((P\<^sub>1.map \<circ> Pack) \<circ>
                            \<langle>\<langle>C.BC.Map (Trn h), C.BC.Map (Trn k)\<rangle>\<rangle>)"
              unfolding p\<^sub>1_def C.map_eq
              using assms hk C.map_eq P\<^sub>1.transformation_axioms
                    Pack_o_HK.transformation_axioms dom_char cod_char mkarr_def
              by auto
            also have "... =
                       C.BC.MkArr
                         (PROD.P\<^sub>1 \<circ>
                            \<langle>\<langle>C.BC.Map (Trn (src h)), C.BC.Map (Trn (src k))\<rangle>\<rangle>)
                         (PROD.P\<^sub>1 \<circ>
                            \<langle>\<langle>C.BC.Map (Trn (trg h)), C.BC.Map (Trn (trg k))\<rangle>\<rangle>)
                         (PROD.P\<^sub>1 \<circ>
                            \<langle>\<langle>C.BC.Map (Trn h), C.BC.Map (Trn k)\<rangle>\<rangle>)"
            proof -
              have "P\<^sub>1.map \<circ> Pack = PROD.P\<^sub>1"
                using PROD.P\<^sub>1.extensional Prod.map_null Prod.null_char by auto
              thus ?thesis by simp
            qed
            also have "... = C.BC.MkArr
                               (C.BC.Map (Trn (src h))) (C.BC.Map (Trn (trg h)))
                               (C.BC.Map (Trn h))"
              using PROD.proj_tuple2(1-2) PROD.proj_tuple(1-2)
                    H.transformation_axioms K.transformation_axioms
                    H\<^sub>0.simulation_axioms H\<^sub>1.simulation_axioms
                    K\<^sub>0.simulation_axioms K\<^sub>1.simulation_axioms
              by auto
            also have "... = Trn h"
              using assms C.BC.MkArr_Map "*" Map_simps(3-4) XA.arr_char arr_char
              by (metis (no_types, lifting) H.arrI H_arr_char comp_def)
            finally show ?thesis by blast
          qed
        qed
        show "p\<^sub>0 \<star> ?hk = k"
        proof (intro arr_eqI)
          show "p\<^sub>0 \<star> ?hk \<noteq> Null"
            using seq0 arr_char by auto
          show "k \<noteq> Null"
            using assms arr_char [of k] by auto
          show Dom: "Dom (p\<^sub>0 \<star> ?hk) = Dom k"
            using "*" H_seq_char seq1 mkarr_def by auto
          show Cod: "Cod (p\<^sub>0 \<star> ?hk) = Cod k"
            using "*" H_seq_char seq0 by auto
          show "Trn (p\<^sub>0 \<star> ?hk) = Trn k"
          proof -
            interpret C: COMP \<open>Dom x\<close> Prod.resid \<open>Dom b\<close> ..
            have "Trn (p\<^sub>0 \<star> ?hk) =
                  COMP.map (Dom ?hk) (Cod ?hk) (Cod p\<^sub>0) (Trn p\<^sub>0, Trn ?hk)"
              using assms seq0 Trn_hcomp [of p\<^sub>0 ?hk] hk H.seqE mkarr_def by auto
            also have "... =
                       COMP.map (Dom x) Prod.resid (Dom b) (Trn p\<^sub>0, Trn ?hk)"
              using assms hk dom_char mkarr_def by auto
            also have "... =
                       C.BC.MkArr
                         ((P\<^sub>0.map \<circ> Pack) \<circ>
                             \<langle>\<langle>C.BC.Map (Trn (src h)), C.BC.Map (Trn (src k))\<rangle>\<rangle>)
                         ((P\<^sub>0.map \<circ> Pack) \<circ>
                             \<langle>\<langle>C.BC.Map (Trn (trg h)), C.BC.Map (Trn (trg k))\<rangle>\<rangle>)
                         ((P\<^sub>0.map \<circ> Pack) \<circ>
                             \<langle>\<langle>C.BC.Map (Trn h), C.BC.Map (Trn k)\<rangle>\<rangle>)"
              unfolding p\<^sub>0_def C.map_eq
              using assms hk C.map_eq P\<^sub>0.transformation_axioms
                    Pack_o_HK.transformation_axioms dom_char cod_char mkarr_def
              by auto
            also have "... =
                       C.BC.MkArr
                         (PROD.P\<^sub>0 \<circ>
                            \<langle>\<langle>C.BC.Map (Trn (src h)), C.BC.Map (Trn (src k))\<rangle>\<rangle>)
                         (PROD.P\<^sub>0 \<circ>
                            \<langle>\<langle>C.BC.Map (Trn (trg h)), C.BC.Map (Trn (trg k))\<rangle>\<rangle>)
                         (PROD.P\<^sub>0 \<circ>
                            \<langle>\<langle>C.BC.Map (Trn h), C.BC.Map (Trn k)\<rangle>\<rangle>)"
            proof -
              have "P\<^sub>0.map \<circ> Pack = PROD.P\<^sub>0"
                using PROD.P\<^sub>0.extensional Prod.map_null Prod.null_char by auto
              thus ?thesis by simp
            qed
            also have "... = C.BC.MkArr
                               (C.BC.Map (Trn (src k))) (C.BC.Map (Trn (trg k)))
                               (C.BC.Map (Trn k))"
              using PROD.proj_tuple2(1-2) PROD.proj_tuple(1-2)
                    H.transformation_axioms K.transformation_axioms
                    H\<^sub>0.simulation_axioms H\<^sub>1.simulation_axioms
                    K\<^sub>0.simulation_axioms K\<^sub>1.simulation_axioms
              by auto
            also have "... = Trn k"
              using assms C.BC.MkArr_Map [of "Trn k"] "*" Map_simps(3-4)
                    XB.arr_char arr_char
              by (metis (no_types, lifting) H.arrI H_arr_char comp_apply)
            finally show ?thesis by blast
          qed
        qed
      qed
      fix m
      assume m: "p\<^sub>1 \<star> m = h \<and> p\<^sub>0 \<star> m = k"
      have arr_m: "arr m"
        using assms m by fastforce
      have Dom_m: "Dom m = Dom x"
        using assms m dom_char by fastforce
      have Cod_m: "Cod m = Prod.resid"
        using assms m cod_char
        using H_seq_char by auto
      interpret X_Prod: exponential_rts \<open>Dom x\<close> Prod.resid ..
      interpret M: transformation \<open>Dom x\<close> Prod.resid
                     \<open>Map (src m)\<close> \<open>Map (trg m)\<close> \<open>Map m\<close>
        using Cod_m Dom_m Map_simps(3) Map_simps(4) arr_char arr_m by auto
      interpret UnpackoM: transformation \<open>Dom h\<close> PROD.resid
                            \<open>Unpack \<circ> Map (src m)\<close>
                            \<open>Unpack \<circ> Map (trg m)\<close>
                            \<open>Unpack \<circ> Map m\<close>
        using "*" M.transformation_axioms PROD.weakly_extensional_rts_axioms
              Prod.Map'.simulation_axioms transformation_whisker_left
        by fastforce
      show "m = ?hk"
      proof (intro arr_eqI)
        show "m \<noteq> Null"
          using assms m null_char by fastforce
        show "?hk \<noteq> Null"
          using hk mkarr_def by auto
        show 2: "Dom m = Dom ?hk"
          using assms m hk cod_char "*" Dom.simps(1) Dom_m mkarr_def
          by presburger
        show 3: "Cod m = Cod ?hk"
          using assms m hk cod_char mkarr_def
          by (simp add: Cod_m)
        show "Trn m = Trn ?hk"
        proof (intro X_Prod.arr_eqI)
          interpret COMPa: COMP \<open>Dom x\<close> Prod.resid \<open>Dom a\<close> ..
          interpret COMPb: COMP \<open>Dom x\<close> Prod.resid \<open>Dom b\<close> ..
          show 4: "X_Prod.arr (Trn m)"
            using assms arr_m Dom_m Cod_m arr_char by simp
          show 5: "X_Prod.arr (Trn ?hk)"
            using "2" Dom_m H_arr_char hk mkarr_def by force
          show 6: "X_Prod.Dom (Trn m) = X_Prod.Dom (Trn ?hk)"
          proof -
            have "PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Dom (Trn ?hk)) =
                  PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Dom (Trn m))"
            proof -
              have "PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Dom (Trn ?hk)) =
                    PROD.P\<^sub>1 \<circ> (Unpack \<circ> Pack) \<circ>
                      \<langle>\<langle>COMPa.BC.Map (Trn (src h)),
                        COMPa.BC.Map (Trn (src k))\<rangle>\<rangle>"
                using mkarr_def by auto
              also have "... = COMPa.BC.Map (Trn (src h))"
              proof
                fix x
                show "(PROD.P\<^sub>1 \<circ> (Unpack \<circ> Pack) \<circ>
                         \<langle>\<langle>COMPa.BC.Map (Trn (src h)),
                           COMPa.BC.Map (Trn (src k))\<rangle>\<rangle>) x =
                      COMPa.BC.Map (Trn (src h)) x"
                  using PROD.P\<^sub>1_def
                  apply (auto simp add: pointwise_tuple_def)[1]
                     apply (metis A.not_arr_null PROD.null_char
                      Prod.null_char first_conv)
                    apply (metis (no_types, opaque_lifting) H\<^sub>0.extensional
                      H\<^sub>0.simulation_axioms comp_apply
                      simulation.preserves_reflects_arr)
                   apply (metis B.not_arr_null PROD.null_char Prod.null_char
                      second_conv)
                 by (metis (no_types, opaque_lifting) A.not_arr_null
                     H\<^sub>0.extensional P\<^sub>1oHK\<^sub>0.preserves_reflects_arr comp_def
                     pointwise_tuple_def)
              qed
              also have "... = COMPa.BC.Map (Trn (src (p\<^sub>1 \<star> m)))"
                using m by blast
              also have "... = COMPa.BC.Map (Trn (p\<^sub>1 \<star> src m))"
                using assms m by auto
              also have "... =
                         COMPa.BC.Map (COMPa.map (Trn p\<^sub>1, Trn (src m)))"
                using arr_m Dom_m Cod_m Trn_hcomp by simp
              also have "... =
                         COMPa.BC.Map (Trn p\<^sub>1) \<circ> COMPa.BC.Map (Trn (src m))"
              proof -
                have "COMPa.BCxAB.arr (COMPa.BC.MkIde P\<^sub>1.map, Trn m)"
                  using assms arr_m Dom_m Cod_m arr_char arr_char p\<^sub>1_simps(1)
                        P\<^sub>1.transformation_axioms
                  by auto
                thus ?thesis
                  unfolding COMPa.map_eq
                  using assms m arr_m Dom_m Cod_m arr_char [of "src m"] by simp
              qed
              also have "... =
                         (PROD.P\<^sub>1 \<circ> Unpack) \<circ> COMPa.BC.Map (Trn (src m))"
                by simp
              also have "... = PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Dom (Trn m))"
                by (auto simp add: 4 Cod_m Dom_m arr_m src_char)
              finally show ?thesis by blast
            qed
            moreover have "PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Dom (Trn ?hk)) =
                           PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Dom (Trn m))"
            proof -
              have "PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Dom (Trn ?hk)) =
                    PROD.P\<^sub>0 \<circ> (Unpack \<circ> Pack) \<circ>
                    \<langle>\<langle>COMPb.BC.Map (Trn (src h)),
                      COMPb.BC.Map (Trn (src k))\<rangle>\<rangle>"
                using mkarr_def by auto
              also have "... = COMPb.BC.Map (Trn (src k))"
              proof
                fix x
                show "(PROD.P\<^sub>0 \<circ> (Unpack \<circ> Pack) \<circ>
                         \<langle>\<langle>COMPb.BC.Map (Trn (src h)),
                           COMPb.BC.Map (Trn (src k))\<rangle>\<rangle>) x =
                      COMPb.BC.Map (Trn (src k)) x"
                  using PROD.P\<^sub>0_def H\<^sub>0.preserves_reflects_arr K\<^sub>0.extensional
                        PROD.null_char Prod.null_char
                  apply (auto simp add: pointwise_tuple_def)[1]
                    apply (metis second_conv)
                   apply (metis A.not_arr_null PROD.null_char first_conv)
                 by (metis (no_types, opaque_lifting) B.not_arr_null
                     P\<^sub>0oHK\<^sub>0.preserves_reflects_arr comp_def pointwise_tuple_def)
              qed
              also have "... = COMPb.BC.Map (Trn (src (p\<^sub>0 \<star> m)))"
                using m by blast
              also have "... = COMPb.BC.Map (Trn (p\<^sub>0 \<star> src m))"
                using assms m by auto
              also have "... = COMPb.BC.Map (COMPb.map (Trn p\<^sub>0, Trn (src m)))"
                using arr_m Dom_m Cod_m Trn_hcomp by simp
              also have "... = COMPb.BC.Map (Trn p\<^sub>0) \<circ>
                                 COMPb.BC.Map (Trn (src m))"
              proof -
                have "COMPb.BCxAB.arr (COMPb.BC.MkIde P\<^sub>0.map, Trn m)"
                  using assms arr_m Dom_m Cod_m arr_char arr_char p\<^sub>0_simps(1)
                        P\<^sub>0.transformation_axioms
                  by auto
                thus ?thesis
                  unfolding COMPb.map_eq
                  using assms m arr_m Dom_m Cod_m arr_char [of "src m"]
                  by simp
              qed
              also have "... =
                         (PROD.P\<^sub>0 \<circ> Unpack) \<circ> COMPb.BC.Map (Trn (src m))"
                by simp
              also have "... = PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Dom (Trn m))"
                by (auto simp add: 4 Cod_m Dom_m arr_m src_char)
              finally show ?thesis by blast
            qed
            moreover have "simulation (Dom x) PROD.resid
                             (Unpack \<circ> X_Prod.Dom (Trn ?hk))"
              using hk arr_char 2 Pack_o_HK.F.simulation_axioms Dom_m
                    Prod.Map'.simulation_axioms simulation_comp mkarr_def
              by auto
            moreover have "simulation (Dom x) PROD.resid
                             (Unpack \<circ> X_Prod.Dom (Trn m))"
              using 4 X_Prod.ide_src Prod.Map'.simulation_axioms
                    simulation_comp
              by auto
            ultimately have "Unpack \<circ> X_Prod.Dom (Trn ?hk) =
                             Unpack \<circ> X_Prod.Dom (Trn m)"
              using PROD.proj_joint_monic by blast
            moreover have "simulation (Dom x) Prod.resid (X_Prod.Dom (Trn ?hk))"
              using hk arr_char X_Prod.ide_src "2" Pack_o_HK.F.simulation_axioms
                    Dom_m mkarr_def
              by fastforce
            moreover have "simulation (Dom x) Prod.resid (X_Prod.Dom (Trn m))"
              using 4 X_Prod.ide_src by auto
            ultimately show ?thesis
              using invertible_simulation_cancel_left
              by (metis (no_types, lifting) Prod.invertible_simulation_map')
          qed
          show 7: "X_Prod.Cod (Trn m) = X_Prod.Cod (Trn ?hk)"
          proof -
            have "PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Cod (Trn ?hk)) =
                  PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Cod (Trn m))"
            proof -
              have "PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Cod (Trn ?hk)) =
                    PROD.P\<^sub>1 \<circ> (Unpack \<circ> Pack) \<circ>
                      \<langle>\<langle>COMPa.BC.Map (Trn (trg h)),
                        COMPa.BC.Map (Trn (trg k))\<rangle>\<rangle>"
                using mkarr_def by auto
              also have "... = COMPa.BC.Map (Trn (trg h))"
              proof
                fix x
                show "(PROD.P\<^sub>1 \<circ> (Unpack \<circ> Pack) \<circ>
                         \<langle>\<langle>COMPa.BC.Map (Trn (trg h)),
                           COMPa.BC.Map (Trn (trg k))\<rangle>\<rangle>) x =
                      COMPa.BC.Map (Trn (trg h)) x"
                  using PROD.P\<^sub>1_def
                  apply (auto simp add: pointwise_tuple_def)[1]
                  subgoal by (metis A.not_arr_null PROD.null_char Prod.null_char
                      first_conv)
                  subgoal using H\<^sub>1.extensional H\<^sub>1.preserves_reflects_arr by auto
                  subgoal by (metis B.not_arr_null PROD.null_char Prod.null_char
                      second_conv)
                  subgoal by (metis (mono_tags, lifting) H\<^sub>1.simulation_axioms
                      K\<^sub>1.simulation_axioms comp_def simulation.extensional
                      simulation.preserves_reflects_arr)
                  done
              qed
              also have "... = COMPa.BC.Map (Trn (trg (p\<^sub>1 \<star> m)))"
                using m by blast
              also have "... = COMPa.BC.Map (Trn (p\<^sub>1 \<star> trg m))"
                using assms m by auto
              also have "... = COMPa.BC.Map (COMPa.map (Trn p\<^sub>1, Trn (trg m)))"
                using arr_m Dom_m Cod_m by simp
              also have "... =
                         COMPa.BC.Map (Trn p\<^sub>1) \<circ> COMPa.BC.Map (Trn (trg m))"
              proof -
                have "COMPa.BCxAB.arr (COMPa.BC.MkIde P\<^sub>1.map, Trn m)"
                  using assms arr_m Dom_m Cod_m arr_char arr_char p\<^sub>1_simps(1)
                        P\<^sub>1.transformation_axioms
                  by auto
                thus ?thesis
                  unfolding COMPa.map_eq
                  using assms m arr_m Dom_m Cod_m arr_char [of "trg m"] by simp
              qed
              also have "... =
                         (PROD.P\<^sub>1 \<circ> Unpack) \<circ> COMPa.BC.Map (Trn (trg m))"
                by simp
              also have "... = PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Cod (Trn m))"
                by (auto simp add: 4 Cod_m Dom_m arr_m trg_char)
              finally show ?thesis by blast
            qed
            moreover have "PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Cod (Trn ?hk)) =
                           PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Cod (Trn m))"
            proof -
              have "PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Cod (Trn ?hk)) =
                    PROD.P\<^sub>0 \<circ> (Unpack \<circ> Pack) \<circ>
                      \<langle>\<langle>COMPb.BC.Map (Trn (trg h)),
                        COMPb.BC.Map (Trn (trg k))\<rangle>\<rangle>"
                using mkarr_def by auto
              also have "... = COMPb.BC.Map (Trn (trg k))"
              proof
                fix x
                show "(PROD.P\<^sub>0 \<circ> (Unpack \<circ> Pack) \<circ>
                         \<langle>\<langle>COMPb.BC.Map (Trn (trg h)),
                          COMPb.BC.Map (Trn (trg k))\<rangle>\<rangle>) x =
                      COMPb.BC.Map (Trn (trg k)) x"
                  using PROD.P\<^sub>0_def H\<^sub>0.preserves_reflects_arr K\<^sub>0.extensional
                         K\<^sub>1.extensional PROD.null_char Prod.null_char
                         H\<^sub>1.preserves_reflects_arr second_conv
                  apply (auto simp add: pointwise_tuple_def)[1]
                     apply metis
                   apply (metis B.not_arr_null)
                  using K\<^sub>1.extensional K\<^sub>1.preserves_reflects_arr by fastforce
              qed
              also have "... = COMPb.BC.Map (Trn (trg (p\<^sub>0 \<star> m)))"
                using m by blast
              also have "... = COMPb.BC.Map (Trn (p\<^sub>0 \<star> trg m))"
                using assms m by auto
              also have "... =
                         COMPb.BC.Map (COMPb.map (Trn p\<^sub>0, Trn (trg m)))"
                using arr_m Dom_m Cod_m by simp
              also have "... =
                         COMPb.BC.Map (Trn p\<^sub>0) \<circ> COMPb.BC.Map (Trn (trg m))"
              proof -
                have "COMPb.BCxAB.arr (COMPb.BC.MkIde P\<^sub>0.map, Trn m)"
                  using assms arr_m Dom_m Cod_m arr_char arr_char p\<^sub>0_simps(1)
                        P\<^sub>0.transformation_axioms
                  by auto
                thus ?thesis
                  unfolding COMPb.map_eq
                  using assms m arr_m Dom_m Cod_m arr_char [of "trg m"]
                  by simp
              qed
              also have "... = (PROD.P\<^sub>0 \<circ> Unpack) \<circ> COMPb.BC.Map (Trn (trg m))"
                by simp
              also have "... = PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Cod (Trn m))"
                by (auto simp add: 4 Cod_m Dom_m arr_m trg_char)
              finally show ?thesis by blast
            qed
            moreover have "simulation (Dom x) PROD.resid
                             (Unpack \<circ> X_Prod.Cod (Trn ?hk))"
              using hk arr_char 2 Pack_o_HK.G.simulation_axioms Dom_m
                    Prod.Map'.simulation_axioms simulation_comp
              using mkarr_def by auto
            moreover have "simulation (Dom x) PROD.resid
                             (Unpack \<circ> X_Prod.Cod (Trn m))"
              using X_Prod.ide_trg \<open>X_Prod.arr (Trn m)\<close>
                    Prod.Map'.simulation_axioms simulation_comp
              by auto
            ultimately have "Unpack \<circ> X_Prod.Cod (Trn ?hk) =
                             Unpack \<circ> X_Prod.Cod (Trn m)"
              using PROD.proj_joint_monic by blast
            moreover have "simulation (Dom x) Prod.resid
                             (X_Prod.Cod (Trn ?hk))"
              using hk 2 arr_char X_Prod.ide_trg Dom_m mkarr_def
                    Pack_o_HK.F.simulation_axioms Pack_o_HK.G.simulation_axioms
              by force
            moreover have "simulation (Dom x) Prod.resid
                             (X_Prod.Cod (Trn m))"
              using 4 X_Prod.ide_trg by auto
            ultimately show ?thesis
              using invertible_simulation_cancel_left
              by (metis (no_types, lifting) Prod.invertible_simulation_map')
          qed
          show "\<And>x. X.ide x \<Longrightarrow> X_Prod.Map (Trn m) x = X_Prod.Map (Trn ?hk) x"
          proof -
            have "PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Map (Trn ?hk)) =
                  PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Map (Trn m))"
            proof -
              have "PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Map (Trn ?hk)) =
                    PROD.P\<^sub>1 \<circ> (Unpack \<circ> Pack) \<circ>
                      \<langle>\<langle>COMPa.BC.Map (Trn h), COMPa.BC.Map (Trn k)\<rangle>\<rangle>"
                using mkarr_def by auto
              also have "... = COMPa.BC.Map (Trn h)"
              proof
                fix x
                show "(PROD.P\<^sub>1 \<circ> (Unpack \<circ> Pack) \<circ> 
                        \<langle>\<langle>COMPa.BC.Map (Trn h),
                          COMPa.BC.Map (Trn k)\<rangle>\<rangle>) x =
                      COMPa.BC.Map (Trn h) x"
                  using PROD.P\<^sub>1_def
                  apply (auto simp add: pointwise_tuple_def)[1]
                     apply (metis A.not_arr_null PROD.null_char Prod.null_char
                      first_conv)
                    apply (metis (mono_tags, lifting) H.transformation_axioms
                      K.transformation_axioms PROD.P\<^sub>1.extensional
                      PROD.P\<^sub>1.preserves_arr PROD.proj_tuple2(1) comp_apply)
                   apply (metis B.not_arr_null PROD.null_char Prod.null_char
                      second_conv)
                  by (metis H.extensional K.preserves_arr comp_apply)
              qed
              also have "... = COMPa.BC.Map (Trn (p\<^sub>1 \<star> m))"
                using m by blast
              also have "... = COMPa.BC.Map (COMPa.map (Trn p\<^sub>1, Trn m))"
                using arr_m Dom_m Cod_m Trn_hcomp by simp
              also have "... = COMPa.BC.Map (Trn p\<^sub>1) \<circ> COMPa.BC.Map (Trn m)"
              proof -
                have "COMPa.BCxAB.arr (COMPa.BC.MkIde P\<^sub>1.map, Trn m)"
                  using assms arr_m Dom_m Cod_m arr_char arr_char p\<^sub>1_simps(1)
                        P\<^sub>1.transformation_axioms
                  by auto
                thus ?thesis
                  unfolding COMPa.map_eq
                  using assms m arr_m Dom_m Cod_m by simp
              qed
              also have "... = (PROD.P\<^sub>1 \<circ> Unpack) \<circ> COMPa.BC.Map (Trn m)"
                by simp
              also have "... = PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_Prod.Map (Trn m))"
                by (auto simp add: 4 Cod_m Dom_m arr_m src_char)
              finally show ?thesis by blast
            qed
            moreover have "PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Map (Trn ?hk)) =
                           PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Map (Trn m))"
            proof -
              have "PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Map (Trn ?hk)) =
                    PROD.P\<^sub>0 \<circ> (Unpack \<circ> Pack) \<circ>
                      \<langle>\<langle>COMPb.BC.Map (Trn h),
                        COMPb.BC.Map (Trn k)\<rangle>\<rangle>"
                using mkarr_def by auto
              also have "... = COMPb.BC.Map (Trn k)"
              proof
                fix x
                show "(PROD.P\<^sub>0 \<circ> (Unpack \<circ> Pack) \<circ>
                         \<langle>\<langle>COMPb.BC.Map (Trn h), COMPb.BC.Map (Trn k)\<rangle>\<rangle>) x =
                      COMPb.BC.Map (Trn k) x"
                  using PROD.P\<^sub>0_def H\<^sub>0.preserves_reflects_arr K\<^sub>0.extensional
                        PROD.null_char Prod.null_char
                  apply (auto simp add: pointwise_tuple_def)[1]
                     apply (metis B.not_arr_null second_conv)
                    apply (metis H.preserves_arr K.extensional comp_apply)
                   apply (metis A.not_arr_null PROD.null_char first_conv)
                  by (metis K.extensional K.preserves_arr comp_apply)
              qed
              also have "... = COMPb.BC.Map (Trn (p\<^sub>0 \<star> m))"
                using m by blast
              also have "... = COMPb.BC.Map (COMPb.map (Trn p\<^sub>0, Trn m))"
                using arr_m Dom_m Cod_m Trn_hcomp by simp
              also have "... =
                         COMPb.BC.Map (Trn p\<^sub>0) \<circ> COMPb.BC.Map (Trn m)"
              proof -
                have "COMPb.BCxAB.arr (COMPb.BC.MkIde P\<^sub>0.map, Trn m)"
                  using assms arr_m Dom_m Cod_m arr_char p\<^sub>0_simps(1)
                        P\<^sub>0.transformation_axioms
                  by auto
                thus ?thesis
                  unfolding COMPb.map_eq
                  using assms m arr_m Dom_m Cod_m by simp
              qed
              also have "... =
                         (PROD.P\<^sub>0 \<circ> Unpack) \<circ> COMPb.BC.Map (Trn m)"
                by simp
              also have "... = PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_Prod.Map (Trn m))"
                by (auto simp add: 4 Cod_m Dom_m arr_m src_char)
              finally show ?thesis by blast
            qed
            moreover have "transformation (Dom x) PROD.resid
                             (Unpack \<circ> Map (src m)) (Unpack \<circ> Map (trg m))
                             (Unpack \<circ> X_Prod.Map (Trn m))"
              by (metis "*" UnpackoM.transformation_axioms comp_def)
            moreover have "transformation (Dom x) PROD.resid
                             (Unpack \<circ> Map (src m)) (Unpack \<circ> Map (trg m))
                             (Unpack \<circ> X_Prod.Map (Trn ?hk))"
            proof -
              have "Map (src m) = X_Prod.Dom (Trn m) \<and> Map (trg m) = X_Prod.Cod (Trn m)"
                by (metis Map_simps(3-4) arr_m comp_def)
              hence "Map (src m) = X_Prod.Dom (Trn ?hk) \<and> Map (trg m) = X_Prod.Cod (Trn ?hk)"
                using 6 7 by simp
              thus ?thesis
                using 5 Prod.Map'.simulation_axioms X_Prod.arr_char [of "Trn ?hk"]
                      PROD.weakly_extensional_rts_axioms
                      transformation_whisker_left
                        [of "Dom x" Prod.resid "Map (src m)" "Map (trg m)"
                            "X_Prod.Map (Trn ?hk)" PROD.resid Unpack]
                by metis
            qed
            ultimately have "Unpack \<circ> X_Prod.Map (Trn ?hk) =
                             Unpack \<circ> X_Prod.Map (Trn m)"
              using 4 5 X_Prod.arr_char
                    PROD.proj_joint_monic2
                      [of "Dom x" "Unpack \<circ> Map (src m)" "Unpack \<circ> Map (trg m)"
                          "Unpack \<circ> X_Prod.Map (Trn ?hk)" "Unpack \<circ> X_Prod.Map (Trn m)"]
              by metis
            moreover have "Pack \<circ> \<langle>\<langle>Map (src h), Map (src k)\<rangle>\<rangle> = Map (src m)"
              by (simp add: 4 Cod_m Dom_m
                  \<open>COMPb.BC.Dom (Trn m) = COMPb.BC.Dom (Trn ?hk)\<close>
                  arr_m src_char mkarr_def)
            moreover have "Pack \<circ> \<langle>\<langle>Map (trg h), Map (trg k)\<rangle>\<rangle> = Map (trg m)"
              by (simp add: 4 Cod_m Dom_m
                  \<open>COMPb.BC.Cod (Trn m) = COMPb.BC.Cod (Trn ?hk)\<close>
                  arr_m trg_char mkarr_def)
            ultimately have "X_Prod.Map (Trn ?hk) = X_Prod.Map (Trn m)"
              using assms 2 Dom_m Prod.invertible_simulation_map'
                    invertible_simulation_cancel_left'
                    M.transformation_axioms Pack_o_HK.transformation_axioms
                    mkarr_def
              by simp
            thus "\<And>x. X.ide x \<Longrightarrow>
                         X_Prod.Map (Trn m) x = X_Prod.Map (Trn ?hk) x"
              by simp
          qed
        qed
      qed
    qed

    lemma has_as_binary_product:
    shows "H.has_as_binary_product a b p\<^sub>1 p\<^sub>0"
    proof
      show "H.span p\<^sub>1 p\<^sub>0" and "cod p\<^sub>1 = a" and"cod p\<^sub>0 = b"
        by auto
      fix x f g
      assume f: "\<guillemotleft>f : x \<rightarrow> a\<guillemotright>" and g: "\<guillemotleft>g : x \<rightarrow> b\<guillemotright>"
      have 1: "\<exists>!h. p\<^sub>1 \<star> h = f \<and> p\<^sub>0 \<star> h = g"
        using f g universality by blast
      show "\<exists>!h. \<guillemotleft>h : x \<rightarrow> dom p\<^sub>1\<guillemotright> \<and> p\<^sub>1 \<star> h = f \<and> p\<^sub>0 \<star> h = g"
        using 1 f by blast
    qed

    sublocale binary_product hcomp a b p\<^sub>1 p\<^sub>0
      using has_as_binary_product
      by unfold_locales blast

    lemma preserves_extensional_rts:
    assumes "extensional_rts (Dom a)" and "extensional_rts (Dom b)"
    shows "extensional_rts Prod.resid"
      using PROD.preserves_extensional_rts
            Prod.preserves_extensional_rts assms(1-2)
      by fastforce

    lemma preserves_small_rts:
    assumes "small_rts (Dom a)" and "small_rts (Dom b)"
    shows "small_rts Prod.resid"
      using PROD.preserves_small_rts
            Prod.preserves_reflects_small_rts assms(1-2)
      by fastforce

    lemma sta_tuple:
    assumes "H.span t u" and "cod t = a" and "cod u = b" and "sta t" and "sta u"
    shows "sta (tuple t u)"
    proof -
      have 0: "\<guillemotleft>tuple t u : dom t \<rightarrow> prod\<guillemotright>"
        using assms tuple_props(1)
        by (simp add: product_def)
      have "src (tuple t u) = tuple t u"
        by (metis (no_types, lifting) H.arr_iff_in_hom V.src_ide assms(1-5)
            p\<^sub>0_simps(1) p\<^sub>1_simps(1) src_hcomp tuple_props(6) universality)
      thus ?thesis
        using 0 V.ide_iff_src_self by auto
    qed

    lemma Map_p\<^sub>0:
    shows "Map p\<^sub>0 = PROD.P\<^sub>0 \<circ> Unpack"
      by simp

    lemma Map_p\<^sub>1:
    shows "Map p\<^sub>1 = PROD.P\<^sub>1 \<circ> Unpack"
      by simp

    lemma Map_tuple:
    assumes "\<guillemotleft>t : x \<rightarrow> a\<guillemotright>" and "\<guillemotleft>u : x \<rightarrow> b\<guillemotright>"
    shows "Map (tuple t u) = Pack \<circ> \<langle>\<langle>Map t, Map u\<rangle>\<rangle>"
    proof -
      have *: "Dom t = Dom x \<and> Cod t = Dom a \<and>
               Dom u = Dom x \<and> Cod u = Dom b"
        using assms dom_char cod_char by auto
      interpret X: extensional_rts \<open>Dom x\<close>
        using assms(1) arr_char [of t] dom_char by auto
      interpret XA: exponential_rts \<open>Dom x\<close> \<open>Dom a\<close> ..
      interpret XB: exponential_rts \<open>Dom x\<close> \<open>Dom b\<close> ..
      interpret AB: exponential_rts \<open>Dom a\<close> \<open>Dom b\<close> ..
      interpret aXb: extensional_rts \<open>Dom prod\<close>
        using obj_prod obj_char arr_char [of prod] by blast
      interpret X_aXb: exponential_rts \<open>Dom x\<close> Prod.resid ..
      interpret aXb_A: exponential_rts Prod.resid \<open>Dom a\<close> ..
      interpret aXb_B: exponential_rts Prod.resid \<open>Dom b\<close> ..
      interpret COMP\<^sub>1: COMP \<open>Dom x\<close> Prod.resid \<open>Dom a\<close> ..
      interpret COMP\<^sub>0: COMP \<open>Dom x\<close> Prod.resid \<open>Dom b\<close> ..
      have span: "H.span t u"
        using assms by blast
      have 1: "arr (tuple t u)"
        using assms span tuple_props [of t u]
        by (elim H.in_homE) auto
      have 2: "Dom (tuple t u) = Dom x"
        by (metis (no_types, lifting) "1" Dom_dom H.in_homE
            assms(1-2) tuple_props(2))
      have 3: "Cod (tuple t u) = Prod.resid"
        by (metis (no_types, lifting) H.in_homE H_seq_char
            assms(1-2) p\<^sub>1_simps(4) tuple_props(4))
      have 4: "COMP\<^sub>1.BCxAB.arr (Trn p\<^sub>1, Trn (tuple t u))"
        by (metis (no_types, lifting) "*" "1" "2" "3"
            COMP\<^sub>1.extensional H.in_homE H_arr_char Trn_hcomp
            V.ide_implies_arr XA.not_arr_null assms(1-2)
            p\<^sub>1_simps(1) p\<^sub>1_simps(4) p\<^sub>1_simps(5) tuple_props(4))
      interpret P\<^sub>1: simulation_as_transformation Prod.resid \<open>Dom a\<close> P\<^sub>1.map ..
      interpret P\<^sub>0: simulation_as_transformation Prod.resid \<open>Dom b\<close> P\<^sub>0.map ..

      interpret T: transformation \<open>Dom x\<close> \<open>Dom a\<close>
                     \<open>XA.Dom (Trn t)\<close> \<open>XA.Cod (Trn t)\<close> \<open>XA.Map (Trn t)\<close>
        using assms(1) * arr_char [of t] XA.arr_char [of "Trn t"] by auto
      interpret U: transformation \<open>Dom x\<close> \<open>Dom b\<close>
                     \<open>XB.Dom (Trn u)\<close> \<open>XB.Cod (Trn u)\<close> \<open>XB.Map (Trn u)\<close>
        using assms(2) * arr_char [of u] XB.arr_char [of "Trn u"] H.arrI
        by auto
      have "Map t = PROD.P\<^sub>1 \<circ> (Unpack \<circ> X_aXb.Map (Trn (tuple t u)))"
        by (metis (no_types, lifting) H.in_homE Map_hcomp Map_p\<^sub>1 assms(1-2)
            comp_assoc o_apply tuple_props(4))
      moreover
      have "Map u = PROD.P\<^sub>0 \<circ> (Unpack \<circ> X_aXb.Map (Trn (tuple t u)))"
        by (metis (no_types, lifting) H.in_homE Map_hcomp Map_p\<^sub>0 assms(1-2)
            comp_assoc comp_def tuple_props(5))
      moreover have "Map t = PROD.P\<^sub>1 \<circ> \<langle>\<langle>Map t, Map u\<rangle>\<rangle>"
        using T.transformation_axioms U.transformation_axioms
              PROD.proj_tuple2 [of "Dom x"]
        by simp
      moreover have "Map u = PROD.P\<^sub>0 \<circ> \<langle>\<langle>Map t, Map u\<rangle>\<rangle>"
        using T.transformation_axioms U.transformation_axioms
              PROD.proj_tuple2 [of "Dom x"]
        by simp
      ultimately
      have 5: "Unpack \<circ> X_aXb.Map (Trn (tuple t u)) = \<langle>\<langle>Map t, Map u\<rangle>\<rangle>"
        by (metis (no_types, lifting) PROD.tuple_proj
            Prod.Map'.simulation_axioms comp_assoc comp_pointwise_tuple)
      show ?thesis
      proof -
        have "X_aXb.Map (Trn (tuple t u)) =
              Pack \<circ> Unpack \<circ> X_aXb.Map (Trn (tuple t u))"
          using 1 2 3 arr_char [of "tuple t u"]
                X_aXb.arr_char [of "Trn (tuple t u)"]
                Prod.inv' comp_identity_transformation
          by fastforce
        also have "... = Pack \<circ> (Unpack \<circ> X_aXb.Map (Trn (tuple t u)))"
          by auto
        also have "... = Pack \<circ> \<langle>\<langle>Map t, Map u\<rangle>\<rangle>"
          using 5 by simp
        finally show ?thesis by simp
      qed
    qed

  end

  text\<open>
    Now we transfer to @{locale rtscatx} just the definitions and facts we want from
    @{locale product_in_rtscat}, generalized to all pairs of objects rather than a fixed pair.
  \<close>

  context rtscatx
  begin

    definition p\<^sub>0
    where "p\<^sub>0 \<equiv> product_in_rtscat.p\<^sub>0"

    definition p\<^sub>1
    where "p\<^sub>1 \<equiv> product_in_rtscat.p\<^sub>1"

    lemma sta_p\<^sub>0:
    assumes "obj a" and "obj b"
    shows "sta (p\<^sub>0 a b)"
      by (simp add: assms(1-2) p\<^sub>0_def product_in_rtscat.p\<^sub>0_simps(1)
          product_in_rtscat_axioms.intro product_in_rtscat_def
          rtscatx.intro universe_axioms)
      
    lemma sta_p\<^sub>1:
    assumes "obj a" and "obj b"
    shows "sta (p\<^sub>1 a b)"
      by (simp add: assms(1-2) p\<^sub>1_def product_in_rtscat.p\<^sub>1_simps(1)
          product_in_rtscat_axioms.intro product_in_rtscat_def
          rtscatx.intro universe_axioms)

    lemma has_binary_products:
    assumes "obj a" and "obj b"
    shows "H.has_as_binary_product a b (p\<^sub>1 a b) (p\<^sub>0 a b)"
      by (simp add: assms(1-2) p\<^sub>0_def p\<^sub>1_def
          product_in_rtscat.has_as_binary_product product_in_rtscat_axioms_def
          product_in_rtscat_def rtscatx.intro universe_axioms)

    interpretation category_with_binary_products hcomp
      using H.has_binary_products_def has_binary_products
      by unfold_locales auto

    proposition is_category_with_binary_products:
    shows "category_with_binary_products hcomp"
      ..

    lemma extends_to_elementary_category_with_binary_products:
    shows "elementary_category_with_binary_products hcomp p\<^sub>0 p\<^sub>1"
    proof
      fix a b
      assume a: "obj a" and b: "obj b"
      interpret axb: product_in_rtscat arr_type a b
        using a b by unfold_locales
      show "H.span (p\<^sub>1 a b) (p\<^sub>0 a b)" and "cod (p\<^sub>1 a b) = a" and "cod (p\<^sub>0 a b) = b"
        unfolding p\<^sub>0_def p\<^sub>1_def
        using a b by auto
      next
      fix t u
      assume tu: "H.span t u"
      interpret axb: product_in_rtscat arr_type \<open>cod t\<close> \<open>cod u\<close>
        using tu H.ide_cod
        by unfold_locales auto
      show "\<exists>!l. p\<^sub>1 (cod t) (cod u) \<star> l = t \<and>
                 p\<^sub>0 (cod t) (cod u) \<star> l = u"
        unfolding p\<^sub>0_def p\<^sub>1_def
        using tu axb.universality by blast
    qed

    interpretation elementary_category_with_binary_products hcomp p\<^sub>0 p\<^sub>1
      using extends_to_elementary_category_with_binary_products by blast

    (* TODO: Why don't these get pulled in automatically? *)
    notation p\<^sub>0      ("\<pp>\<^sub>0[_, _]")
    notation p\<^sub>1      ("\<pp>\<^sub>1[_, _]")
    notation tuple   ("\<langle>_, _\<rangle>")
    notation prod    (infixr "\<otimes>" 51)

    (* TODO: I don't really want to have to bother with this. *)
    lemma prod_eq:
    assumes "obj a" and "obj b"
    shows "a \<otimes> b = product_in_rtscat.prod a b"
    proof -
      interpret axb: product_in_rtscat arr_type a b
        using assms by unfold_locales auto
      show "a \<otimes> b = axb.prod"
        using assms
        by (metis (no_types, lifting) axb.p\<^sub>1_simps(2) p\<^sub>1_def pr_simps(5))
    qed

    lemma sta_tuple [simp]:
    assumes "H.span t u" and "sta t" and "sta u"
    shows "sta \<langle>t, u\<rangle>"
    proof -
      let ?a = "cod t" and ?b = "cod u"
      have a: "obj ?a" and b: "obj ?b"
        using assms by auto
      interpret axb: product_in_rtscat arr_type ?a ?b
        using assms
        by unfold_locales auto
      have "\<langle>t, u\<rangle> = axb.tuple t u"
        using assms(1-2) a b H.in_homE axb.tuple_props(4-5)
              tuple_pr_arr p\<^sub>0_def p\<^sub>1_def
        by (metis (no_types, lifting))
      thus ?thesis
        using assms axb.sta_tuple by auto
    qed

    lemma sta_prod:
    assumes "sta t" and "sta u"
    shows "sta (t \<otimes> u)"
    proof -
      have "H.span (t \<star> p\<^sub>1 (dom t) (dom u)) (u \<star> p\<^sub>0 (dom t) (dom u))"
        using H.seqI assms(1-2) pr_simps(1,4) by force
      moreover have "V.ide (t \<star> p\<^sub>1 (dom t) (dom u))"
        using assms pr_in_hom sta_p\<^sub>1 H_seq_char calculation by auto
      moreover have "V.ide (u \<star> p\<^sub>0 (dom t) (dom u))"
        using assms pr_in_hom sta_p\<^sub>0 H_seq_char calculation by auto
      ultimately show ?thesis
        unfolding prod_def
        using assms sta_tuple by blast
    qed

    definition Pack :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A \<times> 'A \<Rightarrow> 'A"
    where "Pack \<equiv> product_in_rtscat.Pack"

    definition Unpack :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A \<Rightarrow> 'A \<times> 'A"
    where "Unpack \<equiv> product_in_rtscat.Unpack"

    lemma inverse_simulations_Pack_Unpack:
    assumes "obj a" and "obj b"
    shows "inverse_simulations (Dom (a \<otimes> b)) (product_rts.resid (Dom a) (Dom b))
             (Pack a b) (Unpack a b)"
    proof -
      interpret axb: product_in_rtscat arr_type a b
        using assms by unfold_locales auto
      show ?thesis
        unfolding Pack_def Unpack_def
        using p\<^sub>0_def p\<^sub>1_def
        by (metis (no_types, lifting) axb.Dom_prod
            axb.Prod.inverse_simulations_axioms axb.obj_a axb.obj_b
            axb.p\<^sub>0_simps(2) pr_simps(2))
    qed

    lemma simulation_Pack:
    assumes "obj a" and "obj b"
    shows "simulation (product_rts.resid (Dom a) (Dom b)) (Dom (a \<otimes> b)) 
             (Pack a b)"
      using assms inverse_simulations_Pack_Unpack [of a b]
            inverse_simulations_def
      by fast

    lemma simulation_Unpack:
    assumes "obj a" and "obj b"
    shows "simulation (Dom (a \<otimes> b)) (product_rts.resid (Dom a) (Dom b))
             (Unpack a b)"
      using assms inverse_simulations_Pack_Unpack [of a b]
            inverse_simulations_def
      by fast

    lemma Pack_o_Unpack:
    assumes "obj a" and "obj b"
    shows "Pack a b \<circ> Unpack a b = I (Dom (a \<otimes> b))"
    proof -
      interpret PU: inverse_simulations
                      \<open>Dom (a \<otimes> b)\<close> \<open>product_rts.resid (Dom a) (Dom b)\<close>
                      \<open>Pack a b\<close> \<open>Unpack a b\<close>
        using assms inverse_simulations_Pack_Unpack by blast
      show ?thesis
        using assms PU.inv' by simp
    qed

    lemma Unpack_o_Pack:
    assumes "obj a" and "obj b"
    shows "Unpack a b \<circ> Pack a b = I (product_rts.resid (Dom a) (Dom b))"
    proof -
      interpret PU: inverse_simulations
                      \<open>Dom (a \<otimes> b)\<close> \<open>product_rts.resid (Dom a) (Dom b)\<close>
                      \<open>Pack a b\<close> \<open>Unpack a b\<close>
        using assms inverse_simulations_Pack_Unpack by blast
      show ?thesis
        using assms PU.inv by simp
    qed

    lemma Pack_Unpack [simp]:
    assumes "obj a" and "obj b"
    and "residuation.arr (Dom (a \<otimes> b)) t"
    shows "Pack a b (Unpack a b t) = t"
      by (meson assms(1-3) inverse_simulations.inv'_simp
          inverse_simulations_Pack_Unpack)

    lemma Unpack_Pack [simp]:
    assumes "obj a" and "obj b"
    and "residuation.arr (product_rts.resid (Dom a) (Dom b)) t"
    shows "Unpack a b (Pack a b t) = t"
      by (metis (no_types, lifting) Unpack_o_Pack assms(1-3) o_apply)

    lemma src_tuple [simp]:
    assumes "H.span t u"
    shows "src \<langle>t, u\<rangle> = \<langle>src t, src u\<rangle>"
      using assms sta_p\<^sub>0 sta_p\<^sub>1 tuple_simps(1) src_hcomp H.seqI
            src_hcomp [of "p\<^sub>0 (cod t) (cod u)" "tuple t u"]
            src_hcomp [of "p\<^sub>1 (cod t) (cod u)" "tuple t u"]
      by (intro tuple_eqI) auto

    lemma trg_tuple [simp]:
    assumes "H.span t u"
    shows "trg \<langle>t, u\<rangle> = \<langle>trg t, trg u\<rangle>"
      using assms sta_p\<^sub>0 sta_p\<^sub>1 tuple_simps(1) src_hcomp H.seqI
            trg_hcomp [of "p\<^sub>0 (cod t) (cod u)" "tuple t u"]
            trg_hcomp [of "p\<^sub>1 (cod t) (cod u)" "tuple t u"]
      by (intro tuple_eqI) auto

    lemma Map_p\<^sub>0:
    assumes "obj a" and "obj b"
    shows "Map \<pp>\<^sub>0[a, b] = product_rts.P\<^sub>0 (Dom a) (Dom b) \<circ> Unpack a b"
    proof -
      interpret axb: product_in_rtscat arr_type a b
        using assms by unfold_locales auto
      show ?thesis
        unfolding Unpack_def p\<^sub>0_def
        using axb.Map_p\<^sub>0 by blast
    qed

    lemma Map_p\<^sub>1:
    assumes "obj a" and "obj b"
    shows "Map \<pp>\<^sub>1[a, b] = product_rts.P\<^sub>1 (Dom a) (Dom b) \<circ> Unpack a b"
    proof -
      interpret axb: product_in_rtscat arr_type a b
        using assms by unfold_locales auto
      show ?thesis
        unfolding Unpack_def p\<^sub>1_def
        using axb.Map_p\<^sub>1 by blast
    qed

    lemma Map_tuple:
    assumes "\<guillemotleft>t : x \<rightarrow> a\<guillemotright>" and "\<guillemotleft>u : x \<rightarrow> b\<guillemotright>"
    shows "Map \<langle>t, u\<rangle> = Pack a b \<circ> \<langle>\<langle>Map t, Map u\<rangle>\<rangle>"
    proof -
      interpret axb: product_in_rtscat arr_type a b
        using assms by unfold_locales auto
      show ?thesis
        unfolding Pack_def
        using assms axb.Map_tuple [of t x u] p\<^sub>0_def p\<^sub>1_def
        by (metis (no_types, lifting) H.in_homE axb.tuple_props(6) pr_tuple(1-2))
    qed

    lemma assoc_expansion:
    assumes "obj a" and "obj b" and "obj c"
    shows "assoc a b c =
           \<langle>\<pp>\<^sub>1[a, b] \<star> \<pp>\<^sub>1[a \<otimes> b, c], \<langle>\<pp>\<^sub>0[a, b] \<star> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle> \<rangle>"
      using assms assoc_def by blast

  end

  subsection "Exponentials"

  text\<open>
    In this section we show that the category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> has exponentials.
    The strategy is the same as for products: given objects \<open>b\<close> and \<open>c\<close>, construct the
    exponential RTS \<open>[Dom b, Dom c]\<close>, apply an injective map on the arrows to obtain an
    isomorphic RTS with arrow type @{typ 'A}, then let \<open>exp b c\<close> be the object corresponding
    to this RTS.  In order for the type-reducing injection to exist, we use the assumption
    that the type @{typ 'A} admits exponentiation, but this is also where we use the
    assumption that the RTS's \<open>Dom b\<close> and \<open>Dom c\<close> are small, so that the exponential RTS
    \<open>[Dom b, Dom c]\<close> is also small.
  \<close>

  context rtscatx
  begin

    definition inj_exp :: "('A, 'A) exponential_rts.arr \<Rightarrow> 'A"
    where "inj_exp \<equiv> \<lambda> exponential_rts.MkArr F G T \<Rightarrow>
                              lifting.some_lift
                                (Some (pairing.some_pair
                                         (exponentiation.some_inj F,
                                          pairing.some_pair
                                            (exponentiation.some_inj G,
                                             exponentiation.some_inj T))))
                          | exponential_rts.Null \<Rightarrow> lifting.some_lift None"

    lemma inj_inj_exp:
    assumes "small_rts A" and "extensional_rts A"
    and "small_rts B" and "extensional_rts B"
    shows "inj_on inj_exp
             (Collect (residuation.arr (exponential_rts.resid A B)) \<union> {exponential_rts.Null})"
    proof
      interpret A: small_rts A
        using assms by blast
      interpret A: extensional_rts A
        using assms by blast
      interpret B: small_rts B
        using assms by blast
      interpret B: extensional_rts B
        using assms by blast
      interpret AB: exponential_rts A B ..
      fix x y
      assume x: "x \<in> Collect AB.arr \<union> {AB.Null}"
      and y: "y \<in> Collect AB.arr \<union> {AB.Null}"
      assume eq: "inj_exp x = inj_exp y"
      show "x = y"
      proof (cases x; cases y)
        show "\<lbrakk>x = AB.Null; y = AB.Null\<rbrakk> \<Longrightarrow> x = y"
          by blast
        show "\<And>F' G' T'. \<lbrakk>x = AB.Null; y = AB.MkArr F' G' T'\<rbrakk> \<Longrightarrow> x = y"
          using x y eq inj_some_lift
          unfolding inj_exp_def inj_def
          by simp blast
        show "\<And>F G T. \<lbrakk>x = AB.MkArr F G T; y = AB.Null\<rbrakk> \<Longrightarrow> x = y"
          using x y eq inj_some_lift
          unfolding inj_exp_def inj_def
          by simp blast
        fix F G T F' G' T'
        show "\<lbrakk>x = AB.MkArr F G T; y = AB.MkArr F' G' T'\<rbrakk> \<Longrightarrow> x = y"
        proof -
          assume x_eq: "x = AB.MkArr F G T" and y_eq: "y = AB.MkArr F' G' T'"
          have "some_lift
                  (Some
                     (some_pair
                        (some_inj F, some_pair (some_inj G, some_inj T)))) =
                some_lift
                  (Some
                     (some_pair
                        (some_inj F', some_pair (some_inj G', some_inj T'))))"
            using eq x_eq y_eq
            unfolding inj_exp_def
            by simp
          hence "Some
                   (some_pair
                      (some_inj F, some_pair (some_inj G, some_inj T))) =
                 Some
                   (some_pair
                      (some_inj F', some_pair (some_inj G', some_inj T')))"
            using inj_some_lift inj_def by metis
          hence "some_pair (some_inj F, some_pair (some_inj G, some_inj T)) =
                 some_pair (some_inj F', some_pair (some_inj G', some_inj T'))"
            by simp
          hence "some_inj F = some_inj F' \<and>
                 some_pair (some_inj G, some_inj T) =
                 some_pair (some_inj G', some_inj T')"
            using inj_some_pair inj_def [of some_pair] by blast
          hence 1: "some_inj F = some_inj F' \<and> some_inj G = some_inj G' \<and>
                    some_inj T = some_inj T'"
            using inj_some_pair inj_def [of some_pair] by blast
          have "F = F' \<and> G = G' \<and> T = T'"
          proof -
            have "small_function F \<and> small_function F' \<and>
                  small_function G \<and> small_function G'"
              using x_eq x y_eq y AB.arr_char small_function_simulation
                    transformation_def
              by (metis A.small_rts_axioms AB.arr.simps(2)
                  AB.arr_MkArr B.small_rts_axioms UnE mem_Collect_eq singletonD)
            moreover have "small_function T \<and> small_function T'"
              using assms x_eq x y_eq y AB.arr_char small_function_transformation
              by fast
            ultimately show ?thesis
              using 1 inj_some_inj inj_on_def [of some_inj] by auto
          qed
          thus "x = y"
            using x_eq y_eq by auto
        qed
      qed
    qed

  end

  locale exponential_in_rtscat =
    rtscatx arr_type
  for arr_type :: "'A itself"
  and b :: "'A rtscatx.arr"
  and c :: "'A rtscatx.arr" +
  assumes obj_b: "obj b"
  and obj_c: "obj c"
  begin

    sublocale elementary_category_with_binary_products hcomp p\<^sub>0 p\<^sub>1
      using extends_to_elementary_category_with_binary_products by blast

    notation hcomp  (infixr "\<star>" 53)
    notation p\<^sub>0      ("\<pp>\<^sub>0[_, _]")
    notation p\<^sub>1      ("\<pp>\<^sub>1[_, _]")
    notation tuple   ("\<langle>_, _\<rangle>")
    notation prod    (infixr "\<otimes>" 51)

    sublocale B: extensional_rts \<open>Dom b\<close>
      using obj_b bij_mkobj obj_char by blast
    sublocale B: small_rts \<open>Dom b\<close>
      using obj_b bij_mkobj obj_char by blast
    sublocale C: extensional_rts \<open>Dom c\<close>
      using obj_c bij_mkobj obj_char by blast
    sublocale C: small_rts \<open>Dom c\<close>
      using obj_c bij_mkobj obj_char by blast

    sublocale EXP: exponential_rts \<open>Dom b\<close> \<open>Dom c\<close> ..
    sublocale EXP: exponential_of_small_rts \<open>Dom b\<close> \<open>Dom c\<close> ..

    lemma small_function_Map:
    assumes "EXP.arr t"
    shows "small_function (EXP.Dom t)" and "small_function (EXP.Cod t)"
    and "small_function (EXP.Map t)"
      using assms small_function_simulation small_function_transformation
            transformation_def B.small_rts_axioms C.small_rts_axioms
            EXP.con_arr_src(2) EXP.con_char
      by metis+

    text \<open>
      Sublocale \<open>Exp\<close> refers to the isomorphic image of the RTS \<open>EXP\<close> under the type-reducing
      injective map \<open>inj_exp\<close>.  These are connected by simulation \<open>Func\<close>, which maps \<open>Exp\<close>
      to \<open>EXP\<close>, and its inverse \<open>Unfunc\<close>, which maps \<open>EXP\<close> to \<open>Exp\<close>.
    \<close>

    sublocale Exp: inj_image_rts inj_exp EXP.resid
      using inj_inj_exp [of "Dom b" "Dom c"] EXP.null_char
            B.small_rts_axioms B.extensional_rts_axioms
            C.small_rts_axioms C.extensional_rts_axioms
      by unfold_locales argo
    sublocale Exp: extensional_rts Exp.resid
      using EXP.is_extensional_rts Exp.preserves_extensional_rts by blast
    sublocale Exp: small_rts Exp.resid
      using EXP.small_rts_axioms Exp.preserves_reflects_small_rts by blast

    lemma is_extensional_rts:
    shows "extensional_rts Exp.resid"
      ..

    lemma is_small_rts:
    shows "small_rts Exp.resid"
      ..

    abbreviation Func :: "'A \<Rightarrow> ('A, 'A) EXP.arr"
    where "Func \<equiv> Exp.map'\<^sub>e\<^sub>x\<^sub>t"

    abbreviation Unfunc :: "('A, 'A) EXP.arr \<Rightarrow> 'A"
    where "Unfunc \<equiv> Exp.map\<^sub>e\<^sub>x\<^sub>t"

    text \<open>
      We define \<open>exp\<close> to be the object of the category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> having \<open>Exp\<close> as its
      underlying RTS.
    \<close>

    definition exp
    where "exp \<equiv> mkobj Exp.resid"

    lemma obj_exp:
    shows "obj exp"
      using exp_def Exp.rts_axioms is_small_rts is_extensional_rts bij_mkobj by auto

    text\<open>
       The fact that @{term "Dom exp"} and @{term Exp.resid} are equal, but not identical,
       poses a minor inconvenience for the moment.
    \<close>

    lemma Dom_exp [simp]:
    shows "Dom exp = Exp.resid"
      unfolding exp_def by fastforce

    sublocale EXPxB: product_rts EXP.resid \<open>Dom b\<close> ..
    sublocale ExpxB: product_rts Exp.resid \<open>Dom b\<close> ..

    sublocale B: identity_simulation \<open>Dom b\<close> ..
    sublocale B: simulation_as_transformation \<open>Dom b\<close> \<open>Dom b\<close> B.map ..
    sublocale B: transformation_to_extensional_rts
                   \<open>Dom b\<close> \<open>Dom b\<close> B.map B.map B.map ..
    sublocale UnfuncxB: product_simulation
                   EXP.resid \<open>Dom b\<close> Exp.resid \<open>Dom b\<close> Unfunc B.map ..
    sublocale FuncxB: product_simulation
                   Exp.resid \<open>Dom b\<close> EXP.resid \<open>Dom b\<close> Func B.map ..

    sublocale inverse_simulations EXPxB.resid ExpxB.resid
                FuncxB.map UnfuncxB.map
      using UnfuncxB.map_def FuncxB.map_def Exp.arr_char Exp.not_arr_null
      by unfold_locales force+

    lemma obj_expxb:
    shows "obj (exp \<otimes> b)"
      using obj_exp obj_b by blast

    text \<open>
      We now have a simulation \<open>FuncxB_o_Unpack\<close>, which refers to the result of composing
      the isomorphism \<open>Unpack exp b\<close> from \<open>Dom expxb\<close> to \<open>ExpxB\<close>, with the isomorphism
      \<open>FuncxB\<close> from \<open>ExpxB\<close> to \<open>EXPxB\<close>.  This composite essentially ``unpacks''
      the RTS \<open>Dom expxb\<close>, which underlies the product object \<open>expxb\<close>,
      to expose its construction as an application of the exponential RTS construction,
      followed by an application of the product RTS construction.
    \<close>

    sublocale FuncxB_o_Unpack: composite_simulation
                                 \<open>Dom (exp \<otimes> b)\<close> ExpxB.resid EXPxB.resid
                                 \<open>Unpack exp b\<close> FuncxB.map
    proof -
      have "product_rts.resid (Dom exp) (Dom b) = ExpxB.resid"
        by simp
      thus "composite_simulation (Dom (exp \<otimes> b)) ExpxB.resid EXPxB.resid
              (Unpack exp b) FuncxB.map"
        using FuncxB.simulation_axioms simulation_Unpack [of exp b]
              simulation_comp
        by (simp add: composite_simulation_def obj_b obj_exp)
    qed

    text \<open>
      We construct the evaluation map associated with \<open>ExpxB\<close> by composing the evaluation
      map \<open>Eval.map\<close> from \<open>EXPxB\<close> to \<open>C\<close>, derived from the exponential RTS construction,
      with the isomorphism \<open>FuncxB_o_Unpack\<close> from \<open>Dom expxb.prod\<close> to \<open>EXPxB\<close>
      and then obtain the corresponding arrow of the category.
    \<close>

    sublocale Eval: evaluation_map \<open>Dom b\<close> \<open>Dom c\<close> ..
    sublocale Eval: evaluation_map_between_extensional_rts \<open>Dom b\<close> \<open>Dom c\<close> ..
    sublocale Eval_o_FuncxB_o_Unpack:
                 composite_simulation
                   \<open>Dom (exp \<otimes> b)\<close> EXPxB.resid \<open>Dom c\<close>
                   FuncxB_o_Unpack.map Eval.map
      using Eval.simulation_axioms FuncxB_o_Unpack.simulation_axioms
            composite_simulation_def
      by fastforce

    lemma EvaloFuncxB_o_Unpack_is_simulation:
    shows "simulation (Dom (exp \<otimes> b)) (Dom c) Eval_o_FuncxB_o_Unpack.map"
      using Eval_o_FuncxB_o_Unpack.simulation_axioms by blast

    definition eval
    where "eval \<equiv> mksta (Dom (exp \<otimes> b)) (Dom c) Eval_o_FuncxB_o_Unpack.map"

    lemma eval_simps [simp]:
    shows "sta eval" and "dom eval = exp \<otimes> b" and "cod eval = c"
    and "Dom eval = Dom (exp \<otimes> b)" and "Cod eval = Dom c"
    and "Trn eval = exponential_rts.MkIde Eval_o_FuncxB_o_Unpack.map"
    proof -
      show 1: "sta eval"
        unfolding eval_def
        using sta_mksta [of "Dom (exp \<otimes> b)" "Dom c" Eval_o_FuncxB_o_Unpack.map]
               obj_b obj_c obj_exp obj_char arr_char Eval_o_FuncxB_o_Unpack.is_simulation
        by blast
      show 2: "Dom eval = Dom (exp \<otimes> b)" and 3: "Cod eval = Dom c"
        unfolding eval_def mkarr_def by auto
      show "Trn eval = exponential_rts.MkIde Eval_o_FuncxB_o_Unpack.map"
        unfolding eval_def mkarr_def by auto
      have 4: "(\<lambda>a. if FuncxB_o_Unpack.F.A.arr a then a
                    else ResiduatedTransitionSystem.partial_magma.null
                           (Dom eval)) =
               I (Dom (exp \<otimes> b))"
        using "2" by presburger
      have 5: "(\<lambda>t. if C.arr t then t
                    else ResiduatedTransitionSystem.partial_magma.null
                           (Cod eval)) =
               I (Dom c)"
        using 3 by presburger
      show "dom eval = exp \<otimes> b"
        using 1 2 4 dom_char obj_char obj_expxb by auto
      show "cod eval = c"
        using 1 3 5 cod_char obj_char obj_c by auto
    qed

    lemma eval_in_hom [intro]:
    shows "\<guillemotleft>eval : exp \<otimes> b \<rightarrow> c\<guillemotright>"
      using eval_simps by auto

    lemma Map_eval:
    shows "Map eval = Eval.map \<circ> (FuncxB.map \<circ> Unpack exp b)"
      unfolding eval_def mkarr_def by simp

  end

  text\<open>
    Now we transfer the definitions and facts we want to @{locale rtscatx}.
  \<close>

  context rtscatx
  begin

    interpretation elementary_category_with_binary_products hcomp p\<^sub>0 p\<^sub>1
      using extends_to_elementary_category_with_binary_products by blast

    notation prod    (infixr "\<otimes>" 51)

    definition exp
    where "exp b c \<equiv> exponential_in_rtscat.exp b c"

    lemma obj_exp:
    assumes "obj b" and "obj c"
    shows "obj (exp b c)"
    proof -
      interpret bc: exponential_in_rtscat arr_type b c
        using assms by unfold_locales auto
      show ?thesis
        unfolding exp_def
        using bc.obj_exp by blast
    qed

    definition eval
    where "eval b c \<equiv> exponential_in_rtscat.eval b c"

    lemma eval_simps [simp]:
    assumes "obj b" and "obj c"
    shows "sta (eval b c)"
    and "dom (eval b c) = exp b c \<otimes> b"
    and "cod (eval b c) = c"
    proof -
      interpret bc: exponential_in_rtscat arr_type b c
        using assms by unfold_locales auto
      show "sta (eval b c)"
      and "dom (eval b c) = exp b c \<otimes> b"
      and "cod (eval b c) = c"
        unfolding eval_def exp_def
        using bc.eval_simps by auto 
    qed

    lemma eval_in_hom\<^sub>R\<^sub>C\<^sub>R [intro]:
    assumes "obj b" and "obj c"
    shows "\<guillemotleft>eval b c : exp b c \<otimes> b \<rightarrow> c\<guillemotright>"
      using assms eval_simps by auto

    (*
     * TODO: I wanted 'A here instead of 'a (for documentation reasons), but if I do that,
     * it triggers a multiply defined error below when processing \<open>currying_in_rtscat\<close>.
     *)
    definition Func :: "'a arr \<Rightarrow> 'a arr \<Rightarrow> 'a \<Rightarrow> ('a, 'a) exponential_rts.arr"
    where "Func \<equiv> exponential_in_rtscat.Func"

    definition Unfunc :: "'a arr \<Rightarrow> 'a arr \<Rightarrow> ('a, 'a) exponential_rts.arr \<Rightarrow> 'a"
    where "Unfunc \<equiv> exponential_in_rtscat.Unfunc"

    lemma inverse_simulations_Func_Unfunc:
    assumes "obj b" and "obj c"
    shows "inverse_simulations
             (exponential_rts.resid (Dom b) (Dom c)) (Dom (exp b c))
             (Func b c) (Unfunc b c)"
    proof -
      interpret bc: exponential_in_rtscat arr_type b c
        using assms by unfold_locales blast
      have "bc.Exp.resid = Dom (exp b c)"
        using assms exp_def bc.Dom_exp by metis
      thus ?thesis
        unfolding Func_def Unfunc_def
        using bc.Exp.inverse_simulations_axioms inverse_simulations_sym by auto
    qed

    lemma simulation_Func:
    assumes "obj b" and "obj c"
    shows "simulation (Dom (exp b c)) (exponential_rts.resid (Dom b) (Dom c))
             (Func b c)"
      using assms inverse_simulations_Func_Unfunc [of b c]
            inverse_simulations_def
      by fast

    lemma simulation_Unfunc:
    assumes "obj b" and "obj c"
    shows "simulation (exponential_rts.resid (Dom b) (Dom c)) (Dom (exp b c))
             (Unfunc b c)"
      using assms inverse_simulations_Func_Unfunc [of b c]
            inverse_simulations_def
      by fast

    lemma Func_o_Unfunc:
    assumes "obj b" and "obj c"
    shows "Func b c \<circ> Unfunc b c = I (exponential_rts.resid (Dom b) (Dom c))"
    proof -
      interpret FU: inverse_simulations
                      \<open>exponential_rts.resid (Dom b) (Dom c)\<close> \<open>Dom (exp b c)\<close>
                      \<open>Func b c\<close> \<open>Unfunc b c\<close>
        using assms inverse_simulations_Func_Unfunc by blast
      show ?thesis
        using assms FU.inv' by simp
    qed

    lemma Unfunc_o_Func:
    assumes "obj b" and "obj c"
    shows "Unfunc b c \<circ> Func b c = I (Dom (exp b c))"
    proof -
      interpret FU: inverse_simulations
                      \<open>exponential_rts.resid (Dom b) (Dom c)\<close> \<open>Dom (exp b c)\<close>
                      \<open>Func b c\<close> \<open>Unfunc b c\<close>
        using assms inverse_simulations_Func_Unfunc by blast
      show ?thesis
        using assms FU.inv by simp
    qed

    lemma Func_Unfunc [simp]:
    assumes "obj b" and "obj c"
    and "residuation.arr (exponential_rts.resid (Dom b) (Dom c)) t"
    shows "Func b c (Unfunc b c t) = t"
      by (meson assms(1-3) inverse_simulations.inv'_simp
          inverse_simulations_Func_Unfunc)

    lemma Unfunc_Func [simp]:
    assumes "obj b" and "obj c"
    and "residuation.arr (Dom (exp b c)) t"
    shows "Unfunc b c (Func b c t) = t"
    proof -
      have "Unfunc b c (Func b c t) = (Unfunc b c \<circ> Func b c) t"
        using assms by simp
      also have "... = t"
        using assms Unfunc_o_Func [of b c] by auto
      finally show ?thesis by auto
    qed

    lemma Map_eval:
    assumes "obj b" and "obj c"
    shows "Map (eval b c) =
           evaluation_map.map (Dom b) (Dom c) \<circ>
             (product_simulation.map
                (Dom (exp b c)) (Dom b) (Func b c) (I (Dom b)) \<circ>
                Unpack (exp b c) b)"
    proof -
      interpret bc: exponential_in_rtscat arr_type b c
        using assms by unfold_locales blast
      have "Map (eval b c) = bc.Eval.map \<circ> (bc.FuncxB.map \<circ> Unpack (exp b c) b)"
        using assms bc.Map_eval comp_assoc exp_def local.eval_def
        by (simp add: exp_def eval_def)
      thus ?thesis
        unfolding Func_def
        by (simp add: exp_def)
    qed

  end

  locale currying_in_rtscat =
    exponential_in_rtscat arr_type b c
  for arr_type :: "'A itself"
  and a :: "'A rtscatx.arr"
  and b :: "'A rtscatx.arr"
  and c :: "'A rtscatx.arr" +
  assumes obj_a: "obj a"
  begin

    sublocale A: extensional_rts \<open>Dom a\<close>
      using obj_a obj_char arr_char by blast
    sublocale A: small_rts \<open>Dom a\<close>
      using obj_a obj_char arr_char by blast
    sublocale B: extensional_rts \<open>Dom b\<close>
      using obj_b obj_char arr_char by blast
    sublocale B: small_rts \<open>Dom b\<close>
      using obj_b obj_char arr_char by blast

    sublocale AxB: product_of_extensional_rts \<open>Dom a\<close> \<open>Dom b\<close> ..
    sublocale A_Exp: exponential_rts \<open>Dom a\<close> Exp.resid ..

    sublocale aXb: extensional_rts \<open>Dom (a \<otimes> b)\<close>
      using obj_a obj_b obj_char arr_char by blast
    sublocale aXb: small_rts \<open>Dom (a \<otimes> b)\<close>
      using obj_a obj_b obj_char arr_char by blast
    sublocale expXb: exponential_rts Exp.resid \<open>Dom b\<close> ..
    sublocale aXb_C: exponential_rts \<open>Dom (a \<otimes> b)\<close> \<open>Dom c\<close> ..

    sublocale Currying \<open>Dom a\<close> \<open>Dom b\<close> \<open>Dom c\<close> ..

    (*
     * TODO: Notationally distinguish curry as a function on arrows,
     * rather than just a single arrow.
     *)
    definition curry :: "'A arr \<Rightarrow> 'A arr"
    where "curry f = mkarr (Dom a) Exp.resid
                       (Unfunc \<circ> Curry3 (aXb_C.Dom (Trn f) \<circ> Pack a b))
                       (Unfunc \<circ> Curry3 (aXb_C.Cod (Trn f) \<circ> Pack a b))
                       (Unfunc \<circ> Curry (aXb_C.Dom (Trn f) \<circ> Pack a b)
                                       (aXb_C.Cod (Trn f) \<circ> Pack a b)
                                       (aXb_C.Map (Trn f) \<circ> Pack a b))"

    lemma curry_in_hom [intro]:
    assumes "\<guillemotleft>f : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>curry f : a \<rightarrow> exp\<guillemotright>"
    proof -
      have Dom: "Dom f = Dom (a \<otimes> b)" and Cod: "Cod f = Dom c"
        using assms
         apply (metis (no_types, lifting) Dom_dom H.in_homE H_arr_char arr_char)
        using cod_char assms by fastforce
      interpret F: transformation \<open>Dom (a \<otimes> b)\<close> \<open>Dom c\<close>
                     \<open>aXb_C.Dom (Trn f)\<close> \<open>aXb_C.Cod (Trn f)\<close> \<open>aXb_C.Map (Trn f)\<close>
        using assms arr_char aXb_C.arr_char dom_char cod_char H.in_homE Dom
        by auto

      let ?Src = "Unfunc \<circ> Curry3 (aXb_C.Dom (Trn f) \<circ> Pack a b)"
      let ?Trg = "Unfunc \<circ> Curry3 (aXb_C.Cod (Trn f) \<circ> Pack a b)"
      let ?Map = "Unfunc \<circ> Curry (aXb_C.Dom (Trn f) \<circ> Pack a b)
                                 (aXb_C.Cod (Trn f) \<circ> Pack a b)
                                 (aXb_C.Map (Trn f) \<circ> Pack a b)"

      interpret Src: simulation \<open>Dom a\<close> Exp.resid ?Src
        using obj_a obj_b simulation_Pack F.F.simulation_axioms
              Exp.Map.simulation_axioms
        by (intro simulation_comp) auto
      interpret Trg: simulation \<open>Dom a\<close> Exp.resid ?Trg
        using obj_a obj_b simulation_Pack F.G.simulation_axioms
              Exp.Map.simulation_axioms
        by (intro simulation_comp) auto
      interpret Map: transformation \<open>Dom a\<close> Exp.resid ?Src ?Trg ?Map
      proof -
        interpret FoMap: transformation AxB.resid \<open>Dom c\<close>
                           \<open>aXb_C.Dom (Trn f) \<circ> Pack a b\<close>
                           \<open>aXb_C.Cod (Trn f) \<circ> Pack a b\<close>
                           \<open>aXb_C.Map (Trn f) \<circ> Pack a b\<close>
          using obj_a obj_b F.transformation_axioms simulation_Pack
                transformation_whisker_right
                  [of "Dom (a \<otimes> b)" "Dom c"
                      "aXb_C.Dom (Trn f)" "aXb_C.Cod (Trn f)"
                      "aXb_C.Map (Trn f)" AxB.resid "Pack a b"]
                AxB.weakly_extensional_rts_axioms
          by blast
        have "transformation (Dom a) EXP.resid
                (Eval.coext (Dom a) (aXb_C.Dom (Trn f) \<circ> Pack a b))
                (Eval.coext (Dom a) (aXb_C.Cod (Trn f) \<circ> Pack a b))
                (Curry (aXb_C.Dom (Trn f) \<circ> Pack a b)
                       (aXb_C.Cod (Trn f) \<circ> Pack a b)
                       (aXb_C.Map (Trn f) \<circ> Pack a b))"
          using Curry_preserves_transformations FoMap.transformation_axioms
          by blast
        thus "transformation (Dom a) Exp.resid ?Src ?Trg ?Map"
          using Exp.Map.simulation_axioms Exp.weakly_extensional_rts_axioms
                transformation_whisker_left
          by fastforce
      qed
      show ?thesis
        unfolding curry_def exp_def
        using obj_a obj_exp obj_char arr_char Map.transformation_axioms arr_mkarr
        by (intro H.in_homI) auto
    qed

    lemma curry_simps [simp]:
    assumes "\<guillemotleft>t : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "arr (curry t)" and "dom (curry t) = a" and "cod (curry t) = exp"
    and "Dom (curry t) = Dom a" and "Cod (curry t) = Exp.resid"
    and "src (curry t) = curry (src t)" and "trg (curry t) = curry (trg t)"
    and "Map (curry t) =
         (Unfunc \<circ> Curry (aXb_C.Dom (Trn t) \<circ> Pack a b)
                         (aXb_C.Cod (Trn t) \<circ> Pack a b)
                         (aXb_C.Map (Trn t) \<circ> Pack a b))"
    proof -
      let ?Src = "Unfunc \<circ> Curry3 (aXb_C.Dom (Trn t) \<circ> Pack a b)"
      let ?Trg = "Unfunc \<circ> Curry3 (aXb_C.Cod (Trn t) \<circ> Pack a b)"
      let ?Map = "Unfunc \<circ> Curry (aXb_C.Dom (Trn t) \<circ> Pack a b)
                                 (aXb_C.Cod (Trn t) \<circ> Pack a b)
                                 (aXb_C.Map (Trn t) \<circ> Pack a b)"
      show "arr (curry t)" and "dom (curry t) = a" and "cod (curry t) = exp"
      and "Dom (curry t) = Dom a" and "Cod (curry t) = Exp.resid"
      and "Map (curry t) = ?Map"
        using assms obj_a curry_in_hom sta_mksta H.in_homE H_arr_char arr_char
              A.extensional_rts_axioms A.small_rts_axioms
              Exp.extensional_rts_axioms Exp.small_rts_axioms
        apply (auto simp add: curry_def mkarr_def)[6]
        by (metis (no_types, lifting) A_Exp.arr_MkArr
            Cod.simps(1) Dom.simps(1) Trn.simps(1))
      have 1: "transformation (Dom a) Exp.resid ?Src ?Trg ?Map"
        using \<open>arr (curry t)\<close> A_Exp.src_char curry_def curry_in_hom
              arr_char mkarr_def
        by simp
      show "src (curry t) = curry (src t)"
      proof -
        have "src (curry t) =
              MkArr (Dom a) (Exp.resid) (A_Exp.src (Trn (curry t)))"
          unfolding src_char
          using assms \<open>arr (curry t)\<close> \<open>Dom (curry t) = Dom a\<close>
                \<open>Cod (curry t) = Exp.resid\<close>
          by simp
        also have "... = mksta (Dom a) Exp.resid ?Src"
          using 1 A_Exp.src_char curry_def curry_in_hom arr_char
                aXb_C.arr_char mkarr_def
          by auto
        also have "... = curry (src t)"
          unfolding src_char curry_def mkarr_def
          using assms
          apply auto[1]
            apply (metis (no_types, lifting) Dom_cod Dom_dom H.in_homE
              H_arr_char aXb_C.Dom.simps(1) aXb_C.src_simp)
           apply (metis (no_types, lifting) Cod_cod Cod_dom H.ide_char
              H.in_homE H_arr_char aXb_C.MkIde_Dom expXb.Cod.simps(1)
              ide_prod obj_a obj_b obj_c obj_char)
          by (metis (no_types, lifting) Cod_cod Cod_dom H.ide_char
              H.in_homE H_arr_char aXb_C.Map_src aXb_C.src_simp
              expXb.Cod.simps(1) expXb.Dom.simps(1) ide_prod
              obj_a obj_b obj_c obj_char)
        finally show ?thesis by blast
      qed
      show "trg (curry t) = curry (trg t)"
      proof -
        have "trg (curry t) =
              MkArr (Dom a) (Exp.resid) (A_Exp.trg (Trn (curry t)))"
          unfolding trg_char
          using assms \<open>arr (curry t)\<close> \<open>Dom (curry t) = Dom a\<close>
                \<open>Cod (curry t) = Exp.resid\<close>
          by simp
        also have "... = mksta (Dom a) Exp.resid ?Trg"
          using 1 A_Exp.trg_char curry_def curry_in_hom arr_char
                aXb_C.arr_char mkarr_def
          by auto
        also have "... = curry (trg t)"
        proof -
          have "arr t"
            using assms by auto
          moreover have "aXb_C.Dom (Trn (trg t)) = aXb_C.Map (Trn (trg t)) \<and>
                         aXb_C.Cod (Trn (trg t)) = aXb_C.Map (Trn (trg t))"
            by (metis (no_types, lifting) Cod_trg Dom_cod Dom_dom Dom_trg
                H.in_homE aXb_C.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S assms calculation ide_trg staE)
          moreover have "aXb_C.Cod (Trn t) =
                         aXb_C.Map
                           (residuation.trg
                              (exponential_rts.resid (Dom t) (Cod t)) (Trn t))"
            by (metis (no_types, lifting) Dom_cod Dom_dom H.in_homE H_arr_char
                aXb_C.Map_trg arr_char assms)
          ultimately show ?thesis
            unfolding curry_def
            using assms trg_char by simp
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma sta_curry:
    assumes "\<guillemotleft>f : a \<otimes> b \<rightarrow> c\<guillemotright>" and "sta f"
    shows "sta (curry f)"
      using assms V.ide_iff_src_self [of "curry f"] by auto

    definition uncurry :: "'A arr \<Rightarrow> 'A arr"
    where "uncurry g = mkarr (Dom (a \<otimes> b)) (Dom c)
                         (Uncurry (Func \<circ> exponential_rts.Dom (Trn g)) \<circ> Unpack a b)
                         (Uncurry (Func \<circ> exponential_rts.Cod (Trn g)) \<circ> Unpack a b)
                         (Uncurry (Func \<circ> exponential_rts.Map (Trn g)) \<circ> Unpack a b)"

    lemma uncurry_in_hom [intro]:
    assumes "\<guillemotleft>g : a \<rightarrow> exp\<guillemotright>"
    shows "\<guillemotleft>uncurry g : a \<otimes> b \<rightarrow> c\<guillemotright>"
    proof -
      interpret G: transformation \<open>Dom a\<close> Exp.resid
                     \<open>A_Exp.Dom (Trn g)\<close> \<open>A_Exp.Cod (Trn g)\<close> \<open>A_Exp.Map (Trn g)\<close>
        using assms arr_char exp_def A_Exp.arr_char dom_char cod_char
        by (metis (no_types, lifting) H.in_homE H_arr_char
            mkobj_simps(2) obj_a obj_char)
      interpret Cmp'oG: transformation \<open>Dom a\<close> EXP.resid
                          \<open>Func \<circ> A_Exp.Dom (Trn g)\<close>
                          \<open>Func \<circ> A_Exp.Cod (Trn g)\<close>
                          \<open>Func \<circ> A_Exp.Map (Trn g)\<close>
        using Exp.Map'.simulation_axioms G.transformation_axioms
              EXP.weakly_extensional_rts_axioms transformation_whisker_left
        by simp
      have "transformation AxB.resid (Dom c)
              (Uncurry (Func \<circ> A_Exp.Dom (Trn g)))
              (Uncurry (Func \<circ> A_Exp.Cod (Trn g)))
              (Uncurry (Func \<circ> A_Exp.Map (Trn g)))"
        using Cmp'oG.transformation_axioms Uncurry_preserves_transformations
        by blast
      hence "transformation (Dom (a \<otimes> b)) (Dom c)
               (Uncurry (Func \<circ> A_Exp.Dom (Trn g)) \<circ> Unpack a b)
               (Uncurry (Func \<circ> A_Exp.Cod (Trn g)) \<circ> Unpack a b)
               (Uncurry (Func \<circ> A_Exp.Map (Trn g)) \<circ> Unpack a b)"
        using obj_a obj_b simulation_Unpack [of a b]
              aXb.weakly_extensional_rts_axioms transformation_whisker_right
        by auto
      thus ?thesis
        unfolding uncurry_def
        using obj_c obj_char arr_char aXb.extensional_rts_axioms
              aXb.small_rts_axioms arr_mkarr
        apply (intro H.in_homI)
          apply auto[3]
        using obj_a obj_b by blast
    qed

    lemma uncurry_simps [simp]:
    assumes "\<guillemotleft>u : a \<rightarrow> exp\<guillemotright>"
    shows "arr (uncurry u)"
    and "dom (uncurry u) = a \<otimes> b" and "cod (uncurry u) = c"
    and "Dom (uncurry u) = Dom (a \<otimes> b)" and "Cod (uncurry u) = Dom c"
    and "Map (uncurry u) =
         Uncurry (Func \<circ> exponential_rts.Map (Trn u)) \<circ> Unpack a b"
    and "src (uncurry u) = uncurry (src u)"
    and "trg (uncurry u) = uncurry (trg u)"         
    proof -
      show 0: "arr (uncurry u)"
      and "dom (uncurry u) = a \<otimes> b" and "cod (uncurry u) = c"
        using assms uncurry_in_hom [of u] by auto
      show "Dom (uncurry u) = Dom (a \<otimes> b)" and "Cod (uncurry u) = Dom c"
        using 0 \<open>dom (uncurry u) = a \<otimes> b\<close> \<open>cod (uncurry u) = c\<close>
        by (metis Dom_dom Dom_cod)+
      show "Map (uncurry u) =
            Uncurry (Func \<circ> exponential_rts.Map (Trn u)) \<circ> Unpack a b"
        unfolding uncurry_def mkarr_def by simp
      have 1: "transformation (Dom (a \<otimes> b)) (Dom c)
                 (Uncurry (Func \<circ> aXb_C.Dom (Trn u)) \<circ> Unpack a b)
                 (Uncurry (Func \<circ> aXb_C.Cod (Trn u)) \<circ> Unpack a b)
                 (Uncurry (Func \<circ> aXb_C.Map (Trn u)) \<circ> Unpack a b)"
        using 0 A_Exp.src_char uncurry_def uncurry_in_hom arr_char mkarr_def
        by simp
      show "src (uncurry u) = uncurry (src u)"
      proof -
        have "src (uncurry u) =
              MkArr (Dom (a \<otimes> b)) (Dom c) (aXb_C.src (Trn (uncurry u)))"
          unfolding src_char
          using assms 0 \<open>Dom (uncurry u) = Dom (a \<otimes> b)\<close>
                \<open>Cod (uncurry u) = Dom c\<close>
          by simp
        also have "... = uncurry (src u)"
          unfolding uncurry_def mkarr_def
          using assms 1 src_char aXb_C.src_char
          apply auto[1]
            apply (metis (no_types, lifting) A_Exp.src_simp Dom_cod Dom_dom
              Dom_exp H.in_homE arrE expXb.Dom.simps(1))
           apply (metis (no_types, lifting) A_Exp.src_simp Dom_cod Dom_dom
              Dom_exp H.in_homE arrE expXb.Cod.simps(1))
          by (metis (no_types, lifting) A_Exp.Map_src Dom_cod Dom_dom
              Dom_exp H.in_homE arrE)
        finally show ?thesis by blast
      qed
      show "trg (uncurry u) = uncurry (trg u)"
      proof -
        have "trg (uncurry u) =
              MkArr (Dom (a \<otimes> b)) (Dom c) (aXb_C.trg (Trn (uncurry u)))"
          unfolding trg_char
          using assms \<open>arr (uncurry u)\<close> \<open>Dom (uncurry u) = Dom (a \<otimes> b)\<close>
                \<open>Cod (uncurry u) = Dom c\<close>
          by simp
        also have "... = uncurry (trg u)"
          unfolding uncurry_def mkarr_def trg_char
          using assms 1 trg_char aXb_C.trg_char
          apply auto[1]
            apply (metis (no_types, lifting) A_Exp.trg_char Dom_cod Dom_dom
              Dom_exp H.in_homE arrE expXb.Dom.simps(1))
           apply (metis (no_types, lifting) A_Exp.trg_char Dom_cod Dom_dom
              Dom_exp H.in_homE arrE expXb.Cod.simps(1))
          by (metis (no_types, lifting) A_Exp.Map_trg Dom_cod Dom_dom
              Dom_exp H.in_homE arrE)
        finally show ?thesis by blast
      qed
    qed

    lemma sta_uncurry:
    assumes "\<guillemotleft>g : a \<rightarrow> exp\<guillemotright>" and "sta g"
    shows "sta (uncurry g)"
      using assms V.ide_iff_src_self [of "uncurry g"] by auto

    lemma uncurry_curry:
    assumes "obj a" and "obj b"
    and "\<guillemotleft>t : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "uncurry (curry t) = t"
    proof -
      have "mkarr (Dom (a \<otimes> b)) (Dom c)
              (Uncurry
                 (Func \<circ>
                    (Unfunc \<circ>
                       Curry3 (aXb_C.Dom (Trn t) \<circ> Pack a b))) \<circ>
                    Unpack a b)
              (Uncurry
                 (Func \<circ>
                    (Unfunc \<circ>
                        Curry3 (aXb_C.Cod (Trn t) \<circ> Pack a b))) \<circ>
                   Unpack a b)
              (Uncurry
                 (Func \<circ>
                    (Unfunc \<circ>
                       Curry (aXb_C.Dom (Trn t) \<circ> Pack a b)
                             (aXb_C.Cod (Trn t) \<circ> Pack a b)
                             (aXb_C.Map (Trn t) \<circ> Pack a b))) \<circ>
                   Unpack a b) =
           t"
        (is "mkarr (Dom (a \<otimes> b)) (Dom c) ?Src ?Trg ?Map = t")
      proof -
        interpret Dom: simulation \<open>Dom (a \<otimes> b)\<close> \<open>Dom c\<close> \<open>aXb_C.Dom (Trn t)\<close>
          using assms(3) arr_char aXb_C.arr_char Dom_dom Dom_cod
                transformation_def
          by (metis (no_types, lifting) H.in_homE arr_coincidence)
        interpret Cod: simulation \<open>Dom (a \<otimes> b)\<close> \<open>Dom c\<close> \<open>aXb_C.Cod (Trn t)\<close>
          using assms(3) arr_char aXb_C.arr_char Dom_dom Dom_cod
                transformation_def
          by (metis (no_types, lifting) H.in_homE arr_coincidence)
        interpret T: transformation \<open>Dom (a \<otimes> b)\<close> \<open>Dom c\<close>
                       \<open>aXb_C.Dom (Trn t)\<close> \<open>aXb_C.Cod (Trn t)\<close>
                       \<open>aXb_C.Map (Trn t)\<close>
          using assms(3) arr_char aXb_C.arr_char Dom_dom Dom_cod
          by (metis (no_types, lifting) H.in_homE arr_coincidence)
        interpret Dom_o_Pack: composite_simulation
                                AxB.resid \<open>Dom (a \<otimes> b)\<close> \<open>Dom c\<close>
                                \<open>Pack a b\<close> \<open>aXb_C.Dom (Trn t)\<close>
          by intro_locales
             (simp add: obj_a obj_b simulation.axioms(3) simulation_Pack)
        interpret Dom_o_Pack: simulation_as_transformation
                                AxB.resid \<open>Dom c\<close> Dom_o_Pack.map
          ..
        interpret Cod_o_Pack: composite_simulation
                               AxB.resid \<open>Dom (a \<otimes> b)\<close> \<open>Dom c\<close>
                               \<open>Pack a b\<close> \<open>aXb_C.Cod (Trn t)\<close>
          ..
        interpret Cod_o_Pack: simulation_as_transformation
                                AxB.resid \<open>Dom c\<close> Cod_o_Pack.map
          ..
        interpret T_o_Pack: transformation AxB.resid \<open>Dom c\<close>
                              Dom_o_Pack.map Cod_o_Pack.map
                              \<open>aXb_C.Map (Trn t) \<circ> Pack a b\<close>
          using obj_a obj_b T.transformation_axioms simulation_Pack
               AxB.weakly_extensional_rts_axioms
                transformation_whisker_right
                  [of "Dom (a \<otimes> b)" "Dom c" "aXb_C.Dom (Trn t)"
                      "aXb_C.Cod (Trn t)" "aXb_C.Map (Trn t)"
                      AxB.resid "Pack a b"]
          by auto
        interpret Curry_T_o_Pack: transformation \<open>Dom a\<close> EXP.resid
                                    \<open>Curry3 Dom_o_Pack.map\<close>
                                    \<open>Curry3 Cod_o_Pack.map\<close>
                                    \<open>Curry
                                       Dom_o_Pack.map
                                       Cod_o_Pack.map
                                       (aXb_C.Map (Trn t) \<circ> Pack a b)\<close>
          using T_o_Pack.transformation_axioms Curry_preserves_transformations
          by blast
        have "?Src = aXb_C.Dom (Trn t)"
        proof -
          have "?Src =
                Uncurry
                  ((Func \<circ> Unfunc) \<circ>
                        Curry3 (aXb_C.Dom (Trn t) \<circ> Pack a b)) \<circ>
                     Unpack a b"
            using comp_assoc by metis
          also have "... =
                     Uncurry
                       (Curry3 (aXb_C.Dom (Trn t) \<circ> Pack a b)) \<circ>
                          Unpack a b"
            using Exp.inv Curry_T_o_Pack.transformation_axioms
                  comp_identity_simulation
                    [of "Dom a" EXP.resid "Curry3 Dom_o_Pack.map"]
            by (auto simp add: transformation_def)
          also have "... = aXb_C.Dom (Trn t) \<circ> (Pack a b \<circ> Unpack a b)"
            using Dom_o_Pack.transformation_axioms Uncurry_Curry by auto
          also have "... = aXb_C.Dom (Trn t) \<circ> I (Dom (a \<otimes> b))"
            using assms Pack_o_Unpack by simp
          also have "... = aXb_C.Dom (Trn t)"
            using assms Dom.simulation_axioms comp_simulation_identity
            by auto
          finally show ?thesis by auto
        qed
        moreover
        have "?Trg = aXb_C.Cod (Trn t)"
        proof -
          have "?Trg =
                Uncurry
                  ((Func \<circ> Exp.map\<^sub>e\<^sub>x\<^sub>t) \<circ>
                        Curry3 (aXb_C.Cod (Trn t) \<circ> Pack a b)) \<circ>
                     Unpack a b"
            using comp_assoc by metis
          also have "... =
                Uncurry
                  (Curry3 (aXb_C.Cod (Trn t) \<circ> Pack a b)) \<circ>
                     Unpack a b"
            using Exp.inv Curry_T_o_Pack.transformation_axioms
                  comp_identity_simulation
                    [of "Dom a" EXP.resid "Curry Cod_o_Pack.map
                        Cod_o_Pack.map Cod_o_Pack.map"]
            by (auto simp add: transformation_def)
          also have "... = aXb_C.Cod (Trn t) \<circ> (Pack a b \<circ> Unpack a b)"
            using Cod_o_Pack.transformation_axioms Uncurry_Curry by auto
          also have "... = aXb_C.Cod (Trn t) \<circ> I (Dom (a \<otimes> b))"
            using assms Pack_o_Unpack by simp
          also have "... = aXb_C.Cod (Trn t)"
            using assms Cod.simulation_axioms comp_simulation_identity
            by auto
          finally show ?thesis by auto
        qed
        moreover
        have "?Map = aXb_C.Map (Trn t)"
        proof -
          have "?Map =
                Uncurry
                  ((Func \<circ> Unfunc) \<circ>
                        Curry (aXb_C.Dom (Trn t) \<circ> Pack a b)
                              (aXb_C.Cod (Trn t) \<circ> Pack a b)
                              (aXb_C.Map (Trn t) \<circ> Pack a b)) \<circ>
                     Unpack a b"
            using comp_assoc by metis
          also have "... =
                Uncurry
                  (Curry (aXb_C.Dom (Trn t) \<circ> Pack a b)
                         (aXb_C.Cod (Trn t) \<circ> Pack a b)
                         (aXb_C.Map (Trn t) \<circ> Pack a b)) \<circ>
                     Unpack a b"
            using Exp.inv Curry_T_o_Pack.transformation_axioms
                  comp_identity_transformation [of "Dom a" EXP.resid]
            by (auto simp add: transformation_def)
          also have "... = aXb_C.Map (Trn t) \<circ> (Pack a b \<circ> Unpack a b)"
            using T_o_Pack.transformation_axioms Uncurry_Curry by auto
          also have "... = aXb_C.Map (Trn t) \<circ> I (Dom (a \<otimes> b))"
            using assms Pack_o_Unpack by simp
          also have "... = aXb_C.Map (Trn t)"
            using assms T.transformation_axioms comp_transformation_identity
            by blast
          finally show ?thesis by auto
        qed
        ultimately have "mkarr (Dom (a \<otimes> b)) (Dom c) ?Src ?Trg ?Map =
                         mkarr (Dom (a \<otimes> b)) (Dom c)
                           (aXb_C.Dom (Trn t)) (aXb_C.Cod (Trn t))
                           (aXb_C.Map (Trn t))"
          by simp
        also have "... = t"
          by (metis (no_types, lifting) Dom_cod Dom_dom H.in_homE
              H_arr_char mkarr_def MkArr_Trn aXb_C.arrE aXb_C.null_char
              arr_char assms(3) expXb.MkArr_Map)
        finally show ?thesis
          using curry_def uncurry_def by simp
      qed
      thus ?thesis
        using assms curry_def uncurry_def mkarr_def by simp
    qed

    lemma curry_uncurry:
    assumes "\<guillemotleft>u : a \<rightarrow> exp\<guillemotright>"
    shows "curry (uncurry u) = u"
    proof -
      have "mkarr (Dom a) Exp.resid
              (Exp.map\<^sub>e\<^sub>x\<^sub>t \<circ>
                 Curry3
                   ((Uncurry (Func \<circ> A_Exp.Dom (Trn u)) \<circ> Unpack a b) \<circ> Pack a b))
              (Exp.map\<^sub>e\<^sub>x\<^sub>t \<circ>
                 Curry3
                   ((Uncurry (Func \<circ> A_Exp.Cod (Trn u)) \<circ> Unpack a b) \<circ> Pack a b))
              (Exp.map\<^sub>e\<^sub>x\<^sub>t \<circ>
                 Curry
                   ((Uncurry (Func \<circ> A_Exp.Dom (Trn u)) \<circ> Unpack a b) \<circ> Pack a b)
                   ((Uncurry (Func \<circ> A_Exp.Cod (Trn u)) \<circ> Unpack a b) \<circ> Pack a b)
                   ((Uncurry (Func \<circ> A_Exp.Map (Trn u)) \<circ> Unpack a b) \<circ> Pack a b))
               = u"
        (is "?LHS = u")
      proof -
        interpret Dom: simulation \<open>Dom a\<close> Exp.resid \<open>A_Exp.Dom (Trn u)\<close>
          using assms(1) arr_char A_Exp.arr_char transformation_def
          by (metis Dom_cod Dom_dom Dom_exp H.in_homE arr_coincidence)
        interpret Cod: simulation \<open>Dom a\<close> Exp.resid \<open>A_Exp.Cod (Trn u)\<close>
          using assms(1) arr_char A_Exp.arr_char transformation_def
          by (metis (mono_tags, lifting) Dom_cod Dom_dom Dom_exp
              H.in_homE arr_coincidence)
        interpret U: transformation \<open>Dom a\<close> Exp.resid
                       \<open>A_Exp.Dom (Trn u)\<close> \<open>A_Exp.Cod (Trn u)\<close>
                       \<open>A_Exp.Map (Trn u)\<close>
          using assms(1) arr_char A_Exp.arr_char H.in_homE dom_char cod_char
          by (metis (no_types, lifting) Dom_cod Dom_dom Dom_exp arr_coincidence)
        interpret FuncoDom: composite_simulation
                              \<open>Dom a\<close> Exp.resid EXP.resid
                              \<open>A_Exp.Dom (Trn u)\<close> Func
          ..
        interpret FuncoDom: simulation_as_transformation
                              \<open>Dom a\<close> EXP.resid \<open>Func \<circ> A_Exp.Dom (Trn u)\<close>
          ..
        interpret FuncoCod: composite_simulation
                              \<open>Dom a\<close> Exp.resid EXP.resid
                              \<open>A_Exp.Cod (Trn u)\<close> Func
          ..
        interpret FuncoCod: simulation_as_transformation
                              \<open>Dom a\<close> EXP.resid \<open>Func \<circ> A_Exp.Cod (Trn u)\<close>
          ..
        interpret FuncoU: transformation \<open>Dom a\<close> EXP.resid
                            FuncoDom.map FuncoCod.map
                            \<open>Func \<circ> A_Exp.Map (Trn u)\<close>
          using U.transformation_axioms Exp.Map'.simulation_axioms
                EXP.weakly_extensional_rts_axioms transformation_whisker_left
          by blast
        have 1: "transformation AxB.resid (Dom c)
                   (Uncurry FuncoDom.map) (Uncurry FuncoCod.map)
                   (Uncurry (Func \<circ> aXb_C.Map (Trn u)))"
          using Uncurry_preserves_transformations FuncoU.transformation_axioms
          by simp
        have 2: "(Uncurry (Func \<circ> A_Exp.Dom (Trn u)) \<circ> Unpack a b) \<circ>
                    Pack a b =
                 Uncurry (Func \<circ> A_Exp.Dom (Trn u))"
        proof -
          have "(Uncurry (Func \<circ> A_Exp.Dom (Trn u)) \<circ> Unpack a b) \<circ> Pack a b =
                Uncurry (Func \<circ> A_Exp.Dom (Trn u)) \<circ> (Unpack a b \<circ> Pack a b)"
            using comp_assoc by metis
          also have "... = Uncurry (Func \<circ> A_Exp.Dom (Trn u)) \<circ> I AxB.resid"
            using obj_a obj_b Unpack_o_Pack by auto
          also have "... = Uncurry (Func \<circ> A_Exp.Dom (Trn u))"
            using 1 transformation_def comp_simulation_identity by blast
          finally show ?thesis by simp
        qed
        have 3: "(Uncurry (Func \<circ> A_Exp.Cod (Trn u)) \<circ> Unpack a b) \<circ> Pack a b =
                 Uncurry (Func \<circ> A_Exp.Cod (Trn u))"
        proof -
          have "(Uncurry (Func \<circ> A_Exp.Cod (Trn u)) \<circ> Unpack a b) \<circ> Pack a b =
                Uncurry (Func \<circ> A_Exp.Cod (Trn u)) \<circ> (Unpack a b \<circ> Pack a b)"
            using comp_assoc by metis
          also have "... = Uncurry (Func \<circ> A_Exp.Cod (Trn u)) \<circ> I AxB.resid"
            using obj_a obj_b Unpack_o_Pack by auto
          also have "... = Uncurry (Func \<circ> A_Exp.Cod (Trn u))"
            using 1 transformation_def comp_simulation_identity by blast
          finally show ?thesis by simp
        qed
        have 4: "(Uncurry (Func \<circ> A_Exp.Map (Trn u)) \<circ> Unpack a b) \<circ> Pack a b =
                 Uncurry (Func \<circ> A_Exp.Map (Trn u))"
        proof -
          have "(Uncurry (Func \<circ> A_Exp.Map (Trn u)) \<circ> Unpack a b) \<circ> Pack a b =
                Uncurry (Func \<circ> A_Exp.Map (Trn u)) \<circ> (Unpack a b \<circ> Pack a b)"
            using comp_assoc by metis
          also have "... = Uncurry (Func \<circ> A_Exp.Map (Trn u)) \<circ> I AxB.resid"
            using obj_a obj_b Unpack_o_Pack by auto
          also have "... = Uncurry (Func \<circ> A_Exp.Map (Trn u))"
            using 1 transformation_def comp_transformation_identity by blast
          finally show ?thesis by simp
        qed
        have "?LHS = mkarr (Dom a) Exp.resid
                       (Exp.map\<^sub>e\<^sub>x\<^sub>t \<circ> Exp.map'\<^sub>e\<^sub>x\<^sub>t \<circ> A_Exp.Dom (Trn u))
                       (Exp.map\<^sub>e\<^sub>x\<^sub>t \<circ> Exp.map'\<^sub>e\<^sub>x\<^sub>t \<circ> A_Exp.Cod (Trn u))
                       (Exp.map\<^sub>e\<^sub>x\<^sub>t \<circ> Exp.map'\<^sub>e\<^sub>x\<^sub>t \<circ> A_Exp.Map (Trn u))"
          using 2 3 4 FuncoDom.transformation_axioms
                FuncoCod.transformation_axioms FuncoU.transformation_axioms
                Curry_Uncurry mkarr_def
          by auto
        also have "... = mkarr (Dom a) Exp.resid
                           (A_Exp.Dom (Trn u)) (A_Exp.Cod (Trn u))
                           (A_Exp.Map (Trn u))"
          using Dom.simulation_axioms Cod.simulation_axioms
                U.transformation_axioms comp_identity_transformation
                comp_identity_simulation [of "Dom a" Exp.resid]
                Exp.inv' mkarr_def
          by simp
        also have "... = u"
        proof -
          have "Exp.resid = Cod u"
            using assms Dom_exp cod_char
            by (metis (no_types, lifting) Dom_cod H.in_homE
                H_arr_char arr_char)
          moreover have "Trn u =
                         A_Exp.MkArr
                           (A_Exp.Dom (Trn u)) (A_Exp.Cod (Trn u))
                           (A_Exp.Map (Trn u))"
            using assms arr_char [of u] A_Exp.MkArr_Map
            apply auto[1]
            by (metis (no_types, lifting) A.weakly_extensional_rts_axioms
                Dom_dom H.in_homE exponential_rts.arr_char
                exponential_rts.intro)
          ultimately show ?thesis
            using assms U.transformation_axioms null_char arr_char
                  A_Exp.arr_char A_Exp.null_char dom_char
                  cod_char mkarr_def
            by (intro arr_eqI) auto
        qed
        finally show ?thesis by auto
      qed
      thus ?thesis
        unfolding curry_def uncurry_def mkarr_def
        by simp
    qed

    text\<open>
      We are not yet quite where we want to go, because to establish the naturality
      of the curry/uncurry bijection we have to show how uncurry relates to evaluation.
    \<close>

    (* TODO: Restate this, factoring out the projections on the right. *)
    lemma uncurry_expansion:
    assumes "\<guillemotleft>u : a \<rightarrow> exp\<guillemotright>"
    shows "uncurry u = eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"
    proof (intro arr_eqI)
      interpret AxB: identity_simulation AxB.resid ..
      interpret P\<^sub>0: simulation_as_transformation AxB.resid \<open>Dom b\<close> AxB.P\<^sub>0 ..
      interpret P\<^sub>1: simulation_as_transformation AxB.resid \<open>Dom a\<close> AxB.P\<^sub>1 ..
      interpret U: transformation \<open>Dom a\<close> \<open>Dom exp\<close>
                     \<open>A_Exp.Dom (Trn u)\<close> \<open>A_Exp.Cod (Trn u)\<close> \<open>A_Exp.Map (Trn u)\<close>
        using assms Dom_dom Dom_cod [of u] arr_char A_Exp.arr_char
        by (metis (no_types, lifting) Dom_exp H.in_homE arr_coincidence)
      have a: "obj a"
        using assms H.ide_dom by blast
      have src_u: "\<guillemotleft>src u : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a exp\<guillemotright>"
        using assms by fastforce
      have 0: "\<guillemotleft>eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle> : a \<otimes> b \<rightarrow> c\<guillemotright>"
        using assms obj_a obj_b by auto
      have 00: "\<guillemotleft>eval \<star> \<langle>src u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle> : a \<otimes> b \<rightarrow> c\<guillemotright>"
        using src_u obj_a obj_b by auto
      have Dom: "Dom (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>) = Dom (a \<otimes> b)"
        using 0 Dom_dom [of "eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"] by auto
      have Cod: "Cod (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>) = Dom c"
        using 0 Cod_dom [of "eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"]
        by (metis (no_types, lifting) Dom_cod H.in_homE H_arr_char arr_char)
      show "uncurry u \<noteq> Null"
        using assms uncurry_simps(1) V.not_arr_null null_char by metis
      show "eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle> \<noteq> Null"
        using assms eval_in_hom null_char tuple_in_hom pr_in_hom
        by (metis (no_types, lifting) H.comp_in_homI H.seqI' V.not_arr_null
            arr_coincidence obj_a obj_b)
      show 1: "Dom (uncurry u) = Dom (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)"
        by (simp add: Dom assms)
      show 2: "Cod (uncurry u) = Cod (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)"
        by (simp add: Cod assms)
      show "Trn (uncurry u) = Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)"
      proof (intro aXb_C.arr_eqI)
        show "aXb_C.arr (Trn (uncurry u))"
          using assms arr_char [of "uncurry u"] by auto
        show "aXb_C.arr (Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>))"
          using assms(1) 0 1 2 arr_char [of "eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"]
                Dom_dom Dom_cod
          by auto
        show "aXb_C.Dom (Trn (uncurry u)) =
              aXb_C.Dom (Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>))"
        proof -
          have 4: "arr (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)"
            using 0 by blast
          have 5: "sta \<langle>src u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"
            using assms 00 sta_tuple sta_p\<^sub>0 sta_p\<^sub>1
            by (metis (no_types, lifting) H.dom_comp H.in_homE
                H.seqI cod_pr1 obj_a obj_b pr_simps(1-2,4-5)
                src_u sta_hcomp)
          have "aXb_C.Dom (Trn (uncurry u)) =
                Eval.map \<circ>
                  product_simulation.map (Dom a) (Dom b)
                    (Func \<circ> Map (src u)) B.map \<circ>
                  Unpack a b"
          proof -
            have "aXb_C.Dom (Trn (uncurry u)) =
                  aXb_C.Map (aXb_C.src (Trn (uncurry u)))"
              by (simp add: \<open>aXb_C.arr (Trn (uncurry u))\<close>)
            also have "... = Map (src (uncurry u))"
              using assms(1) src_char by force
            also have "... = Map (uncurry (src u))"
              using assms(1) uncurry_simps by simp
            also have "... = Uncurry (Func \<circ> Map (src u)) \<circ> Unpack a b"
              unfolding uncurry_def mkarr_def by simp
            also have "... = Eval.map \<circ>
                               product_simulation.map (Dom a) (Dom b)
                                 (Func \<circ> Map (src u)) B.map \<circ>
                                 Unpack a b"
            proof -
              have "simulation (Dom a) EXP.resid (Func \<circ> A_Exp.Map (Trn (src u)))"
                using assms Exp.Map'.simulation_axioms sta_char
                      A_Exp.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S simulation_comp
                by (metis (no_types, lifting) Cod_src Dom_cod Dom_dom
                    Dom_exp Dom_src H.in_homE V.ide_src arr_coincidence)
              thus ?thesis
                using Eval.Uncurry_simulation_expansion
                        [of "Dom a" "Exp.map'\<^sub>e\<^sub>x\<^sub>t \<circ> A_Exp.Map (Trn (src u))"]
                      A.weakly_extensional_rts_axioms
                by auto
            qed
            finally show ?thesis by simp
          qed
          moreover
          have "aXb_C.Dom (Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)) =
                Eval.map \<circ>
                   product_simulation.map (Dom a) (Dom b)
                     (Func \<circ> Map (src u)) B.map \<circ>
                   Unpack a b"
          proof -
            have "aXb_C.Dom (Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)) =
                  aXb_C.Map (aXb_C.src (Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)))"
              using assms(1) 0 4 Dom Cod arr_char by auto
            also have "... = aXb_C.Map (Trn (src (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)))"
              using 4 src_char Cod Dom Trn.simps(1) by presburger
            also have "... = Map (eval \<star> \<langle>src u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)"
            proof -
              have "H.seq eval \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"
                by (simp add: 4)
              moreover have "H.span (u \<star> \<pp>\<^sub>1[a, b]) \<pp>\<^sub>0[a, b]"
                by (metis (no_types, lifting) H.not_arr_null H_seq_char
                    arr_coincidence calculation tuple_ext)
              ultimately show ?thesis
                using obj_a obj_b sta_p\<^sub>0 sta_p\<^sub>1 by auto
            qed
            also have "... = Map eval \<circ> Map \<langle>src u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"
              using "00" Map_hcomp by blast
            also have "... = Map eval \<circ>
                               (Pack exp b \<circ>
                                  \<langle>\<langle>Map (src u \<star> \<pp>\<^sub>1[a, b]), AxB.P\<^sub>0 \<circ> Unpack a b\<rangle>\<rangle>)"
              using assms(1) obj_a obj_b Map_p\<^sub>0
                    Map_tuple [of "src u \<star> \<pp>\<^sub>1[a, b]" "a \<otimes> b" exp "\<pp>\<^sub>0[a, b]" b]
              by (metis (no_types, lifting) H.comp_in_homI pr_in_hom(1-2) src_u)
            also have "... = Map eval \<circ>
                               (Pack exp b \<circ>
                                  \<langle>\<langle>Map (src u) \<circ> (AxB.P\<^sub>1 \<circ> Unpack a b),
                                    AxB.P\<^sub>0 \<circ> Unpack a b\<rangle>\<rangle>)"
              using H.seqI Map_hcomp Map_p\<^sub>1 assms obj_b pr_simps(4) by auto
            also have "... = Map eval \<circ>
                               Pack exp b \<circ>
                                 \<langle>\<langle>Map (src u) \<circ> (AxB.P\<^sub>1 \<circ> Unpack a b),
                                   AxB.P\<^sub>0 \<circ> Unpack a b\<rangle>\<rangle>"
              using comp_assoc by metis
            also have "... = (Eval.map \<circ>
                                (FuncxB.map \<circ>
                                   (Unpack exp b \<circ> Pack exp b)) \<circ>
                                     \<langle>\<langle>Map (src u) \<circ> AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                     Unpack a b"
              using Map_eval
                    comp_pointwise_tuple
                      [of "Map (src u) \<circ> AxB.P\<^sub>1" AxB.P\<^sub>0 "Unpack a b"]
              by (simp add: comp_assoc)
            also have "... = (Eval.map \<circ>
                                FuncxB.map \<circ>
                                  \<langle>\<langle>Map (src u) \<circ> AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                  Unpack a b"
              using obj_b obj_exp Unpack_o_Pack Dom_exp
                    FuncxB.simulation_axioms comp_simulation_identity
                      [of ExpxB.resid EXPxB.resid FuncxB.map]
              by presburger
            also have "... = Eval.map \<circ>
                                (FuncxB.map \<circ>
                                   \<langle>\<langle>Map (src u) \<circ> AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                 Unpack a b"
              by auto
            also have "... = Eval.map \<circ>
                               \<langle>\<langle>Func \<circ> Map (src u) \<circ> AxB.P\<^sub>1,
                                 B.map \<circ> AxB.P\<^sub>0\<rangle>\<rangle> \<circ>
                                 Unpack a b"
            proof -
              have 1: "Src u = Map (src u)"
                using assms Map_simps(3) by fastforce
              interpret src_uoP\<^sub>1: simulation AxB.resid Exp.resid
                                    \<open>Map (src u) \<circ> AxB.P\<^sub>1\<close>
                using 1 AxB.P\<^sub>1.simulation_axioms U.F.simulation_axioms
                      simulation_comp
                by auto
              interpret src_uoP\<^sub>1: simulation_as_transformation
                                    AxB.resid Exp.resid
                                    \<open>Map (src u) \<circ> AxB.P\<^sub>1\<close>
                ..
              show ?thesis
                using src_uoP\<^sub>1.transformation_axioms B.simulation_axioms
                      Exp.Map'.simulation_axioms P\<^sub>0.transformation_axioms
                      comp_product_simulation_tuple2
                        [of Exp.resid EXP.resid Func "Dom b" "Dom b" B.map
                            AxB.resid _ _ "Map (src u) \<circ> AxB.P\<^sub>1" _ _ AxB.P\<^sub>0]
                by (simp add: comp_assoc)
            qed
            also have "... = Eval.map \<circ>
                               (product_simulation.map (Dom a) (Dom b)
                                  (Func \<circ> Map (src u)) B.map \<circ>
                                     \<langle>\<langle>AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                  Unpack a b"
            proof -
              have "simulation (Dom a) EXP.resid (Func \<circ> Map (src u))"
                using Exp.Map'.simulation_axioms U.F.simulation_axioms
                      simulation_comp Dom_exp H.arrI Map_simps(3) assms
                by auto
              thus ?thesis
                using B.simulation_axioms P\<^sub>0.transformation_axioms
                      P\<^sub>1.transformation_axioms
                      comp_product_simulation_tuple2
                        [of "Dom a" EXP.resid "Func \<circ> Map (src u)"
                            "Dom b" "Dom b" B.map AxB.resid
                            AxB.P\<^sub>1 AxB.P\<^sub>1 AxB.P\<^sub>1 AxB.P\<^sub>0 AxB.P\<^sub>0 AxB.P\<^sub>0]
                      simulation_as_transformation.intro
                      AxB.weakly_extensional_rts_axioms
                      A.weakly_extensional_rts_axioms
                      B.weakly_extensional_rts_axioms
                by simp
            qed
            also have "... = Eval.map \<circ>
                               product_simulation.map (Dom a) (Dom b)
                                 (Func \<circ> Map (src u)) B.map \<circ>
                                 (\<langle>\<langle>AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle> \<circ> Unpack a b)"
              by auto
            also have "... = Eval.map \<circ>
                               (product_simulation.map (Dom a) (Dom b)
                                  (Func \<circ> Map (src u)) B.map) \<circ>
                               Unpack a b"
            proof -
              interpret AxB: identity_simulation AxB.resid ..
              have "\<langle>\<langle>AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle> = I AxB.resid"
                using AxB.tuple_proj [of AxB.resid "I AxB.resid"]
                      AxB.simulation_axioms
                      comp_simulation_identity [of AxB.resid "Dom b" AxB.P\<^sub>0]
                      comp_simulation_identity [of AxB.resid "Dom a" AxB.P\<^sub>1]
                      AxB.P\<^sub>0.simulation_axioms AxB.P\<^sub>1.simulation_axioms
                by simp
              thus ?thesis
                using obj_a obj_b simulation_Unpack
                      comp_identity_simulation
                        [of "Dom (a \<otimes> b)" AxB.resid "Unpack a b"]
                by auto
            qed
            finally show ?thesis by blast
          qed
          ultimately show ?thesis by simp
        qed
        show "aXb_C.Cod (Trn (uncurry u)) =
              aXb_C.Cod (Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>))"
        proof -
          have "aXb_C.Cod (Trn (uncurry u)) =
                aXb_C.Map (aXb_C.trg (Trn (uncurry u)))"
            by (simp add: \<open>aXb_C.arr (Trn (uncurry u))\<close>)
          also have "... = Map (trg (uncurry u))"
            using assms(1) trg_char by force
          also have "... = Map (uncurry (trg u))"
            using assms(1) uncurry_simps by simp
          also have "... = Uncurry (Func \<circ> Map (trg u)) \<circ> Unpack a b"
            unfolding uncurry_def mkarr_def by simp
          also have "... = Eval.map \<circ>
                             product_simulation.map (Dom a) (Dom b)
                               (Func \<circ> Map (trg u)) B.map \<circ>
                               Unpack a b"
          proof -
            have "simulation (Dom a) EXP.resid (Func \<circ> A_Exp.Map (Trn (trg u)))"
              using assms Exp.Map'.simulation_axioms sta_char A_Exp.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S
                    simulation_comp
                      [of "Dom a" Exp.resid "A_Exp.Map (Trn (trg u))"
                          EXP.resid Func]
              by (metis (no_types, lifting) Cod_trg Dom_cod Dom_exp Dom_trg
                  H.in_homE H.seqI H_seq_char cod_pr1 ide_trg obj_a pr_simps(4))
            thus ?thesis
              using Eval.Uncurry_simulation_expansion
                      [of "Dom a" "Exp.map'\<^sub>e\<^sub>x\<^sub>t \<circ> A_Exp.Map (Trn (trg u))"]
                    A.weakly_extensional_rts_axioms
              by auto
          qed
          also have "... = Eval.map \<circ>
                             product_simulation.map (Dom a) (Dom b)
                               (Func \<circ> Map (trg u)) B.map \<circ>
                                 (\<langle>\<langle>AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle> \<circ> Unpack a b)"
            by (metis (no_types, lifting) AxB.tuple_proj
                comp_pointwise_tuple obj_a obj_b simulation_Unpack)
          also have "... = Eval.map \<circ>
                             (product_simulation.map (Dom a) (Dom b)
                                (Func \<circ> Map (trg u)) B.map \<circ>
                                   \<langle>\<langle>AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                Unpack a b"
            by auto
          also have "... = Eval.map \<circ>
                             \<langle>\<langle>Func \<circ> Map (trg u) \<circ> AxB.P\<^sub>1, B.map \<circ> AxB.P\<^sub>0\<rangle>\<rangle> \<circ>
                               Unpack a b"
          proof -
            have "simulation (Dom a) EXP.resid (Func \<circ> Map (trg u))"
              using Exp.Map'.simulation_axioms U.G.simulation_axioms
                    simulation_comp Dom_exp H.arrI Map_simps(4) assms
              by auto
            thus ?thesis
              using B.simulation_axioms P\<^sub>0.transformation_axioms
                    P\<^sub>1.transformation_axioms
                    comp_product_simulation_tuple2
                      [of "Dom a" EXP.resid "Func \<circ> Map (trg u)"
                           "Dom b" "Dom b" B.map
                           AxB.resid AxB.P\<^sub>1 AxB.P\<^sub>1 AxB.P\<^sub>1 AxB.P\<^sub>0 AxB.P\<^sub>0 AxB.P\<^sub>0]
              by (simp add: comp_assoc)
          qed
          also have "... = Eval.map \<circ>
                              (FuncxB.map \<circ>
                                 \<langle>\<langle>Map (trg u) \<circ> AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                               Unpack a b"
          proof -
            have 1: "Trg u = Map (trg u)"
              using assms Map_simps(4) by fastforce
            interpret trg_uoP\<^sub>1: simulation AxB.resid Exp.resid
                                  \<open>Map (trg u) \<circ> AxB.P\<^sub>1\<close>
              using 1 AxB.P\<^sub>1.simulation_axioms U.G.simulation_axioms
                    simulation_comp
              by auto
            interpret src_uoP\<^sub>1: simulation_as_transformation AxB.resid Exp.resid
                                  \<open>Map (trg u) \<circ> AxB.P\<^sub>1\<close>
              ..
            interpret P\<^sub>0: simulation_as_transformation AxB.resid \<open>Dom b\<close> AxB.P\<^sub>0
              ..
            show ?thesis
              using src_uoP\<^sub>1.transformation_axioms B.simulation_axioms
                    Exp.Map'.simulation_axioms P\<^sub>0.transformation_axioms
                    comp_product_simulation_tuple2
                      [of Exp.resid EXP.resid Func "Dom b" "Dom b" B.map
                          AxB.resid _ _ "Map (trg u) \<circ> AxB.P\<^sub>1" _ _ AxB.P\<^sub>0]
              by (simp add: comp_assoc)
          qed
          also have "... = (Eval.map \<circ>
                              FuncxB.map \<circ>
                                \<langle>\<langle>Map (trg u) \<circ> AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                Unpack a b"
            by auto
          also have "... = (Eval.map \<circ>
                              (FuncxB.map \<circ>
                                 (Unpack exp b \<circ> Pack exp b)) \<circ>
                                   \<langle>\<langle>Map (trg u) \<circ> AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                   Unpack a b"
            using obj_b obj_exp Unpack_o_Pack Dom_exp FuncxB.simulation_axioms
                  comp_simulation_identity [of ExpxB.resid EXPxB.resid FuncxB.map]
            by presburger
          also have "... = Map eval \<circ>
                             Pack exp b \<circ>
                               \<langle>\<langle>Map (trg u) \<circ> AxB.P\<^sub>1 \<circ> Unpack a b,
                                 AxB.P\<^sub>0 \<circ> Unpack a b\<rangle>\<rangle>"
            using Map_eval
                  comp_pointwise_tuple
                    [of "Map (trg u) \<circ> AxB.P\<^sub>1" AxB.P\<^sub>0 "Unpack a b"]
            by (simp add: comp_assoc)
          also have "... = Map eval \<circ>
                             (Pack exp b \<circ>
                                \<langle>\<langle>Map (trg u) \<circ> AxB.P\<^sub>1 \<circ> Unpack a b,
                                  AxB.P\<^sub>0 \<circ> Unpack a b\<rangle>\<rangle>)"
            using comp_assoc by metis
          also have "... = Map eval \<circ>
                             (Pack exp b \<circ>
                                \<langle>\<langle>Map (trg u \<star> p\<^sub>1 a b),
                                  AxB.P\<^sub>0 \<circ> Unpack a b\<rangle>\<rangle>)"
            by (metis (no_types, lifting) H.in_homE H.seqI Map_hcomp
                Map_p\<^sub>1 assms cod_pr1 comp_assoc dom_trg obj_a obj_b
                pr_simps(4) trg.preserves_arr)
          also have "... = Map eval \<circ> Map \<langle>trg u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"
          proof -
            have "\<guillemotleft>trg u \<star> \<pp>\<^sub>1[a, b] : a \<otimes> b \<rightarrow> exp\<guillemotright>"
              using assms(1) obj_a obj_b sta_p\<^sub>0 [of a b] sta_p\<^sub>1 [of a b] H.seqI
              by auto
            moreover have "\<guillemotleft>\<pp>\<^sub>0[a, b] : a \<otimes> b \<rightarrow> b\<guillemotright>"
              using obj_a obj_b by blast
            ultimately show ?thesis
              using assms(1) obj_a obj_b Map_p\<^sub>0
                    Map_tuple [of "trg u \<star> \<pp>\<^sub>1[a, b]" "a \<otimes> b" exp "\<pp>\<^sub>0[a, b]" b]
              by auto
          qed
          also have "... = Map (eval \<star> \<langle>trg u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)"
            using assms 0 Map_eval Map_hcomp H.cod_comp H.dom_comp H.seqI
                  cod_pr0 cod_pr1 cod_trg cod_tuple dom_trg eval_in_hom
                  obj_a obj_b pr_simps(1-2,4-5) trg.preserves_arr tuple_simps(1)
              by (elim H.in_homE) presburger
          also have "... = Map (trg (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>))"
          proof -
            have "H.seq eval \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"
              using 0 by blast
            moreover have "H.span (u \<star> \<pp>\<^sub>1[a, b]) \<pp>\<^sub>0[a, b]"
              by (metis (no_types, lifting) H.not_arr_null H_seq_char
                  arr_coincidence calculation tuple_ext)
            ultimately show ?thesis
              using obj_a obj_b sta_p\<^sub>0 sta_p\<^sub>1 by auto
          qed
          also have "... = Trg (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)"
            using 0 trg_char Cod Dom Trn.simps(1) H.arrI Map_simps(4) by blast
          also have "... = aXb_C.Cod (Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>))"
            by simp
          finally show ?thesis by simp
        qed
        fix x
        assume x: "aXb.ide x"
        show "aXb_C.Map (Trn (uncurry u)) x =
              aXb_C.Map (Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>)) x"
        proof -
          have "aXb_C.Map (Trn (uncurry u)) x =
                (Uncurry (Func \<circ> Map u) \<circ> Unpack a b) x"
            unfolding uncurry_def mkarr_def by simp
          also have "... = (Eval.map \<circ>
                              product_transformation.map (Dom a) (Dom b)
                                EXP.resid (Dom b)
                                (Func \<circ> A_Exp.Dom (Trn u)) B.map
                                (Func \<circ> A_Exp.Map (Trn u)) B.map \<circ>
                                Unpack a b) x"
          proof -
            have "transformation (Dom a) EXP.resid
                     (Func \<circ> A_Exp.Dom (Trn u)) (Func \<circ> A_Exp.Cod (Trn u))
                     (Func \<circ> A_Exp.Map (Trn u))"
              using assms Exp.Map'.simulation_axioms arr_char A_Exp.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S
                    EXP.weakly_extensional_rts_axioms Dom_exp
                    U.transformation_axioms transformation_whisker_left
              by simp
            thus ?thesis
              using Eval.Uncurry_transformation_expansion
                      [of "Dom a" "Func \<circ> A_Exp.Dom (Trn u)"
                          "Func \<circ> A_Exp.Cod (Trn u)" "Func \<circ> A_Exp.Map (Trn u)"]
                    A.weakly_extensional_rts_axioms
              by auto
          qed
          also have "... = (Eval.map \<circ>
                              product_transformation.map (Dom a) (Dom b)
                                EXP.resid (Dom b)
                                (Func \<circ> A_Exp.Dom (Trn u)) B.map
                                (Func \<circ> Map u) B.map \<circ>
                                (\<langle>\<langle>AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle> \<circ> Unpack a b)) x"
          proof -
            have "pointwise_tuple AxB.P\<^sub>1 AxB.P\<^sub>0 = I AxB.resid"
              using AxB.tuple_proj [of AxB.resid "I AxB.resid"]
                    comp_simulation_identity [of AxB.resid "Dom b" AxB.P\<^sub>0]
                    comp_simulation_identity [of AxB.resid "Dom a" AxB.P\<^sub>1]
                    AxB.P\<^sub>0.simulation_axioms AxB.P\<^sub>1.simulation_axioms
                    AxB.simulation_axioms
              by simp
            thus ?thesis
              using obj_a obj_b simulation_Unpack
                    comp_identity_simulation
                      [of "Dom (a \<otimes> b)" AxB.resid "Unpack a b"]
              by auto
          qed
          also have "... = (Eval.map \<circ>
                              ((product_transformation.map (Dom a) (Dom b)
                                 EXP.resid (Dom b)
                                 (Func \<circ> Src u) B.map
                                 (Func \<circ> Map u) B.map \<circ>
                                    \<langle>\<langle>AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                 Unpack a b)) x"
            by auto
          also have "... = (Eval.map \<circ>
                              (\<langle>\<langle>Func \<circ> (Map u \<circ> AxB.P\<^sub>1), B.map \<circ> AxB.P\<^sub>0\<rangle>\<rangle> \<circ>
                                Unpack a b)) x"
          proof -
            have "transformation (Dom a) EXP.resid
                    (Func \<circ> Src u) (Func \<circ> Trg u) (Func \<circ> Map u)"
              using assms Exp.Map'.simulation_axioms U.transformation_axioms
                    EXP.weakly_extensional_rts_axioms Dom_exp H.arrI
                    Map_simps(4) transformation_whisker_left
              by auto
            hence "transformation_to_extensional_rts (Dom a) EXP.resid
                    (Func \<circ> Src u) (Func \<circ> Trg u) (Func \<circ> Map u)"
              using EXP.extensional_rts_axioms
                    transformation_to_extensional_rts.intro
              by blast
            thus ?thesis
              using B.simulation_axioms AxB.P\<^sub>0_is_simulation
                    AxB.P\<^sub>1_is_simulation
                    B.transformation_to_extensional_rts_axioms
                    comp_product_transformation_tuple
                      [of "Dom a" EXP.resid
                          "Func \<circ> Src u" "Func \<circ> Trg u" "Func \<circ> Map u"
                          "Dom b" "Dom b" B.map B.map B.map
                          AxB.resid AxB.P\<^sub>1 AxB.P\<^sub>0]
              by (simp add: comp_assoc)
          qed
          also have "... = (Eval.map \<circ>
                              (FuncxB.map \<circ>
                                 \<langle>\<langle>Map u \<circ> AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                               Unpack a b) x"
          proof -
            have "transformation (\\\<^sub>A\<^sub>x\<^sub>B) Exp.resid
                    (Src u \<circ> AxB.P\<^sub>1) (Trg u \<circ> AxB.P\<^sub>1) (Map u \<circ> AxB.P\<^sub>1)"
              using transformation_whisker_right AxB.P\<^sub>1.simulation_axioms
                    U.transformation_axioms Dom_exp
                    AxB.weakly_extensional_rts_axioms
              by auto
            thus ?thesis
              using B.simulation_axioms Exp.Map'.simulation_axioms
                    P\<^sub>0.transformation_axioms P\<^sub>1.transformation_axioms
                    comp_product_simulation_tuple2
                      [of Exp.resid EXP.resid Func "Dom b" "Dom b" B.map
                          AxB.resid _ _ "Map u \<circ> AxB.P\<^sub>1" _ _ AxB.P\<^sub>0]
              by simp
          qed
          also have "... = ((Eval.map \<circ>
                               FuncxB.map \<circ>
                                 \<langle>\<langle>Map u \<circ> AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                 Unpack a b) x"
            by auto
          also have "... = ((Eval.map \<circ>
                               (FuncxB.map \<circ>
                                  (Unpack exp b \<circ> Pack exp b)) \<circ>
                                    \<langle>\<langle>Map u \<circ> AxB.P\<^sub>1, AxB.P\<^sub>0\<rangle>\<rangle>) \<circ>
                                    Unpack a b) x"
            using obj_b obj_exp Unpack_o_Pack Dom_exp FuncxB.simulation_axioms
                  comp_simulation_identity
                    [of ExpxB.resid EXPxB.resid FuncxB.map]
            by presburger
          also have "... = (Map eval \<circ>
                              Pack exp b \<circ>
                                \<langle>\<langle>Map u \<circ> AxB.P\<^sub>1 \<circ> Unpack a b,
                                  AxB.P\<^sub>0 \<circ> Unpack a b\<rangle>\<rangle>) x"
            using Map_eval
                  comp_pointwise_tuple [of "Map u \<circ> AxB.P\<^sub>1" AxB.P\<^sub>0 "Unpack a b"]
            by (simp add: comp_assoc)
          also have "... = (Map eval \<circ>
                              (Pack exp b \<circ>
                                 \<langle>\<langle>Map u \<circ> (AxB.P\<^sub>1 \<circ> Unpack a b),
                                   AxB.P\<^sub>0 \<circ> Unpack a b\<rangle>\<rangle>)) x"
            using comp_assoc by metis
          also have "... = (Map eval \<circ>
                              (Pack exp b \<circ>
                                 \<langle>\<langle>Map (u \<star> p\<^sub>1 a b),
                                   AxB.P\<^sub>0 \<circ> Unpack a b\<rangle>\<rangle>)) x"
            by (metis (no_types, lifting) H.seqI' Map_p\<^sub>1
                Map_hcomp arr_coincidence assms obj_a obj_b pr_in_hom(2))
          also have "... = (Map eval \<circ> Map \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>) x"
            by (metis (mono_tags, lifting) H.comp_in_homI Map_p\<^sub>0 Map_tuple
                assms obj_a obj_b pr_in_hom(1) pr_in_hom(2))
          also have "... = (aXb_C.Map (Trn (eval \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>))) x"
            using 0 Map_eval Map_hcomp by auto
          finally show ?thesis by simp
        qed
      qed
    qed

  end

  text\<open>
    Once again, we transfer the things we want to @{locale rtscatx}.
  \<close>

  context rtscatx
  begin

    interpretation elementary_category_with_binary_products hcomp p\<^sub>0 p\<^sub>1
      using extends_to_elementary_category_with_binary_products by blast

    notation hcomp  (infixr "\<star>" 53)
    notation p\<^sub>0      ("\<pp>\<^sub>0[_, _]")
    notation p\<^sub>1      ("\<pp>\<^sub>1[_, _]")
    notation tuple   ("\<langle>_, _\<rangle>")
    notation prod    (infixr "\<otimes>" 51)

    definition curry :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr"
    where "curry \<equiv> currying_in_rtscat.curry"

    definition uncurry :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr"
    where "uncurry \<equiv> currying_in_rtscat.uncurry"

    lemma curry_in_hom [intro, simp]:
    assumes "obj a" and "obj b"
    and "\<guillemotleft>f : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>curry a b c f : a \<rightarrow> exp b c\<guillemotright>"
    proof -
      interpret Currying: currying_in_rtscat arr_type a b c
        using assms by unfold_locales auto
      show ?thesis
        unfolding curry_def exp_def
        using assms Currying.curry_in_hom by blast
    qed

    lemma curry_simps [simp]:
    assumes "obj a" and "obj b"
    and "\<guillemotleft>f : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "arr (curry a b c f)"
    and "dom (curry a b c f) = a" and "cod (curry a b c f) = exp b c"
    and "src (curry a b c f) = curry a b c (src f)"
    and "trg (curry a b c f) = curry a b c (trg f)"
    proof -
      interpret Currying: currying_in_rtscat arr_type a b c
        using assms by unfold_locales auto
      show "arr (curry a b c f)"
      and "dom (curry a b c f) = a" and "cod (curry a b c f) = exp b c"
        using assms curry_in_hom H.in_homE H_arr_char arr_char
          apply (metis (no_types, lifting))
        by (metis (no_types, lifting) H.in_homE assms curry_in_hom)+
      show "src (curry a b c f) = curry a b c (src f)"
      and "trg (curry a b c f) = curry a b c (trg f)"
        unfolding curry_def
        using assms by auto
    qed

    lemma sta_curry:
    assumes "obj a" and "obj b"
    and "\<guillemotleft>f : a \<otimes> b \<rightarrow> c\<guillemotright>" and "sta f"
    shows "sta (curry a b c f)"
      using assms V.ide_iff_src_self [of "curry a b c f"] by auto

    lemma uncurry_in_hom [intro, simp]:
    assumes "obj b" and "obj c"
    and "\<guillemotleft>g : a \<rightarrow> exp b c\<guillemotright>"
    shows "\<guillemotleft>uncurry a b c g : a \<otimes> b \<rightarrow> c\<guillemotright>"
    proof -
      interpret Currying: currying_in_rtscat arr_type a b c
        using assms by unfold_locales auto
      show ?thesis
        using assms
        unfolding uncurry_def exp_def
        using Currying.uncurry_in_hom by blast
    qed

    lemma uncurry_simps [simp]:
    assumes "obj b" and "obj c"
    and "\<guillemotleft>g : a \<rightarrow> exp b c\<guillemotright>"
    shows "arr (uncurry a b c g)"
    and "dom (uncurry a b c g) = a \<otimes> b" and "cod (uncurry a b c g) = c"
    and "src (uncurry a b c g) = uncurry a b c (src g)"
    and "trg (uncurry a b c g) = uncurry a b c (trg g)"
    proof -
      interpret Currying: currying_in_rtscat arr_type a b c
        using assms by unfold_locales auto
      show "arr (uncurry a b c g)"
      and "dom (uncurry a b c g) = a \<otimes> b" and "cod (uncurry a b c g) = c"
        using assms uncurry_in_hom H.in_homE H_arr_char arr_char
          apply (metis (no_types, lifting))
        by (metis (no_types, lifting) H.in_homE assms uncurry_in_hom)+
      show "src (uncurry a b c g) = uncurry a b c (src g)"
      and "trg (uncurry a b c g) = uncurry a b c (trg g)"
        using assms
        by (auto simp add: uncurry_def exp_def)
    qed

    lemma sta_uncurry:
    assumes "obj b" and "obj c"
    and "\<guillemotleft>g : a \<rightarrow> exp b c\<guillemotright>" and "sta g"
    shows "sta (uncurry a b c g)"
      using assms V.ide_iff_src_self [of "uncurry a b c g"] by auto

    lemma uncurry_curry:
    assumes "obj a" and "obj b"
    and "\<guillemotleft>t : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "uncurry a b c (curry a b c t) = t"
    proof -
      interpret Currying: currying_in_rtscat arr_type a b c
        using assms by unfold_locales auto
      show ?thesis
        unfolding curry_def uncurry_def
        using assms Currying.uncurry_curry by blast
    qed

    lemma curry_uncurry:
    assumes "obj b" and "obj c"
    and "\<guillemotleft>u : a \<rightarrow> exp b c\<guillemotright>"
    shows "curry a b c (uncurry a b c u) = u"
    proof -
      interpret Currying: currying_in_rtscat arr_type a b c
        using assms by unfold_locales auto
      show ?thesis
        using assms
        unfolding curry_def uncurry_def exp_def
        using Currying.curry_uncurry by blast
    qed

    lemma uncurry_expansion:
    assumes "obj b" and "obj c"
    and "\<guillemotleft>u : a \<rightarrow> exp b c\<guillemotright>"
    shows "uncurry a b c u = eval b c \<star> (u \<otimes> b)"
    proof -
      have a: "obj a"
        using assms(3) by auto
      interpret Currying: currying_in_rtscat arr_type a b c
        using assms by unfold_locales auto
      have "uncurry a b c u = eval b c \<star> \<langle>u \<star> \<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"
        using assms
        unfolding curry_def uncurry_def exp_def eval_def
        using Currying.uncurry_expansion by blast
      also have "... = eval b c \<star> (u \<otimes> b) \<star> \<langle>\<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>"
      proof -
        have "b \<star> \<pp>\<^sub>0[a, b] = \<pp>\<^sub>0[a, b]"
          using assms a sta_p\<^sub>0
          by (simp add: H.comp_cod_arr)
        moreover have "H.seq u \<pp>\<^sub>1[a, b]"
          using assms sta_p\<^sub>1 [of a b]
          by (intro H.seqI) auto
        ultimately show ?thesis
          using assms prod_tuple [of "\<pp>\<^sub>1[a, b]" "\<pp>\<^sub>0[a, b]" u b]
                sta_p\<^sub>0 [of a b] sta_p\<^sub>1 [of a b]
          by auto
      qed
      also have "... = eval b c \<star> (u \<otimes> b)"
        using assms a tuple_pr [of a b] H.comp_arr_ide
        by (metis (no_types, lifting) H.comp_arr_dom H.comp_ide_self H.ideD(1)
            H.in_homE interchange)
      finally show ?thesis by blast
    qed

    lemma Map_curry:
    assumes "obj a" and "obj b" and "obj c"
    shows "Map (curry a b c f) =
           Unfunc b c \<circ>
             Currying.Curry (Dom a) (Dom b) (Dom c)
                (Src f \<circ> Pack a b) (Trg f \<circ> Pack a b) (Map f \<circ> Pack a b)"
    proof -
      interpret Currying: currying_in_rtscat arr_type a b c
        using assms by unfold_locales auto
      show ?thesis
        unfolding curry_def Currying.curry_def Unfunc_def mkarr_def by simp
    qed

    lemma Map_uncurry:
    assumes "obj a" and "obj b" and "obj c"
    shows "Map (uncurry a b c g) =
           Currying.Uncurry (Dom a) (Dom b) (Dom c)
             (Func b c \<circ> exponential_rts.Map (Trn g)) \<circ> Unpack a b"
    proof -
      interpret Currying: currying_in_rtscat arr_type a b c
        using assms by unfold_locales auto
      show ?thesis
        unfolding uncurry_def Currying.uncurry_def Func_def mkarr_def by simp
    qed

  end

  subsection "Cartesian Closure"

  text\<open>
    We can now show that the category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> is cartesian closed.
  \<close>

  context rtscatx
  begin

    interpretation elementary_category_with_binary_products hcomp p\<^sub>0 p\<^sub>1
      using extends_to_elementary_category_with_binary_products by blast

    notation prod    (infixr "\<otimes>" 51)

    interpretation elementary_cartesian_closed_category
                     hcomp p\<^sub>0 p\<^sub>1 one trm exp eval curry
    proof
      fix b c
      assume b: "obj b" and c: "obj c"
      show "\<guillemotleft>eval b c : exp b c \<otimes> b \<rightarrow> c\<guillemotright>"
        using b c eval_in_hom\<^sub>R\<^sub>C\<^sub>R by blast
      show "obj (exp b c)"
        using b c obj_exp by blast
      fix a
      assume a: "obj a"
      show "\<And>t. \<guillemotleft>t : a \<otimes> b \<rightarrow> c\<guillemotright> \<Longrightarrow> \<guillemotleft>curry a b c t : a \<rightarrow> exp b c\<guillemotright>"
        using a b c curry_in_hom by blast
      show "\<And>t. \<guillemotleft>t : a \<otimes> b \<rightarrow> c\<guillemotright> \<Longrightarrow> eval b c \<star> (curry a b c t \<otimes> b) = t"
        by (metis \<open>\<And>t. \<guillemotleft>t : a \<otimes> b \<rightarrow> c\<guillemotright> \<Longrightarrow> \<guillemotleft>curry a b c t : a \<rightarrow> exp b c\<guillemotright>\<close>
            a b c uncurry_curry uncurry_expansion)
      show "\<And>u. \<guillemotleft>u : a \<rightarrow> exp b c\<guillemotright> \<Longrightarrow> curry a b c (eval b c \<star> (u \<otimes> b)) = u"
        using b c curry_uncurry uncurry_expansion by force
    qed

    lemma is_elementary_cartesian_closed_category:
    shows "elementary_cartesian_closed_category
             hcomp p\<^sub>0 p\<^sub>1 one trm exp eval curry"
      ..

    theorem is_cartesian_closed_category:
    shows "cartesian_closed_category hcomp"
      ..

  end

  subsection "Repleteness"

  context rtscatx
  begin

  text\<open>
    We have shown that the RTS-category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> has objects that
    are in bijective correspondence with small extensional RTS's, states (identities for
    the vertical residuation) that are in bijective correspondence with simulations,
    and arrows that are in bijective correspondence with transformations.  These results
    allow us to pass back and forth between external constructions on RTS's and internal
    structure of the RTS-category, as was demonstrated in the proof of cartesian closure.
    However, these results make use of extra structure beyond that of an RTS-category;
    namely the mapping @{term Dom} that takes an object to its underlying RTS.
    We would like to have a characterization of \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> in terms that make sense
    for an abstract RTS-category without additional structure.  It seems that it should
    be possible to do this, because as we have shown, for any object \<open>a\<close> the RTS \<open>Dom a\<close>
    is isomorphic to \<open>Hom \<^bold>\<one> a\<close>.  So we ought to be able to dispense with the extrinsic
    mapping @{term Dom} and work instead with the intrinsic mapping @{term "Hom \<^bold>\<one>"}.
    However, there is an issue here to do with types.  The mapping @{term Dom} takes an object
    \<open>a\<close> to a small extensional RTS \<open>Dom a\<close> having arrow type @{typ 'A}.  On the other hand,
    the RTS \<open>Hom \<^bold>\<one> a\<close> has arrow type @{typ "'A rtscatx.arr"}.  So one thing that needs to be
    done in order to carry out this program is to express the ``object repleteness''
    of \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> in terms of small extensional RTS's with arrow type
    @{typ "'A rtscatx.arr"}, as opposed to small extensional RTS's with arrow type @{typ 'A}.
    However, the type @{typ "'A rtscatx.arr"} is larger than the type @{typ 'A},
    and consequently it could admit a larger class of small extensional RTS's than
    type @{typ 'A} does.  It is possible, though, to define a mapping from
    @{typ "'A rtscatx.arr"} to @{typ 'A} whose restriction to the set of arrows (and null)
    of @{locale rtscatx} is injective.  This will allow us to take any small extensional
    RTS \<open>A\<close> with arrow type @{typ "'A rtscatx.arr"}, as long as its arrows
    and null are drawn from the set of arrows and null of @{locale rtscatx} as a whole,
    and obtain an isomorphic image of it with arrow type @{typ 'A}.
  \<close>

    text\<open>
      We first define the required mapping from @{typ "'A arr"} to @{typ 'A}.
    \<close>

    fun inj_arr :: "'A arr \<Rightarrow> 'A"
    where "inj_arr (MkArr A B F) =
           lifting.some_lift
             (Some (pairing.some_pair
                      (some_inj_resid A,
                       pairing.some_pair
                         (some_inj_resid B, inj_exp F))))"
        | "inj_arr Null = lifting.some_lift None"

    text\<open>
      The mapping @{term inj_arr} has the required injectiveness property.
    \<close>

    lemma inj_inj_arr:
    fixes A :: "'A arr resid"
    assumes "small_rts A" and "extensional_rts A"
    and "Collect (residuation.arr A) \<union>
                    {ResiduatedTransitionSystem.partial_magma.null A} \<subseteq>
         Collect arr \<union> {Null}"
    shows "inj_on inj_arr
             (Collect (residuation.arr A) \<union>
                {ResiduatedTransitionSystem.partial_magma.null A})"
    proof
      interpret A: small_rts A
        using assms(1) by blast
      interpret A: extensional_rts A
        using assms(2) by blast
      fix x y :: "'A arr"
      assume x: "x \<in> Collect A.arr \<union> {A.null}"
      assume y: "y \<in> Collect A.arr \<union> {A.null}"
      assume eq: "inj_arr x = inj_arr y"
      show "x = y"
      proof -
        have "\<lbrakk>x = Null; y \<noteq> Null\<rbrakk> \<Longrightarrow> ?thesis"
          using eq
          apply (cases x; cases y)
          by (auto simp add: inj_eq inj_some_lift)
        moreover have "\<lbrakk>x \<noteq> Null; y = Null\<rbrakk> \<Longrightarrow> ?thesis"
          using eq
          apply (cases x; cases y)
          by (auto simp add: inj_eq inj_some_lift)
        moreover have "\<lbrakk>x \<noteq> Null; y \<noteq> Null\<rbrakk> \<Longrightarrow> x = y"
        proof -
          assume x': "x \<noteq> Null" and y': "y \<noteq> Null"
          have "lifting.some_lift
                  (Some (pairing.some_pair
                           (some_inj_resid (Dom x),
                            pairing.some_pair
                              (some_inj_resid (Cod x), inj_exp (Trn x))))) =
                lifting.some_lift
                  (Some (pairing.some_pair
                           (some_inj_resid (Dom y),
                            pairing.some_pair
                              (some_inj_resid (Cod y), inj_exp (Trn y)))))"
            using eq x' y'
            by (cases x; cases y) auto
          hence "Some (pairing.some_pair
                           (some_inj_resid (Dom x),
                            pairing.some_pair
                              (some_inj_resid (Cod x), inj_exp (Trn x)))) =
                 Some (pairing.some_pair
                           (some_inj_resid (Dom y),
                            pairing.some_pair
                              (some_inj_resid (Cod y), inj_exp (Trn y))))"
            using inj_some_lift injD by metis
          hence "pairing.some_pair
                           (some_inj_resid (Dom x),
                            pairing.some_pair
                              (some_inj_resid (Cod x), inj_exp (Trn x))) =
                 pairing.some_pair
                           (some_inj_resid (Dom x),
                            pairing.some_pair
                              (some_inj_resid (Cod x), inj_exp (Trn x)))"
            by auto
          hence "some_inj_resid (Dom x) = some_inj_resid (Dom y) \<and>
                 pairing.some_pair (some_inj_resid (Cod x), inj_exp (Trn x)) =
                 pairing.some_pair (some_inj_resid (Cod x), inj_exp (Trn y))"
            using inj_some_pair
            by (metis \<open>Some (some_pair
                               (some_inj_resid (Dom x),
                                some_pair (some_inj_resid (Cod x), inj_exp (Trn x)))) =
                       Some (some_pair
                               (some_inj_resid (Dom y),
                                some_pair (some_inj_resid (Cod y), inj_exp (Trn y))))\<close>
                first_conv option.inject second_conv)
          hence 1: "some_inj_resid (Dom x) = some_inj_resid (Dom y) \<and>
                    some_inj_resid (Cod x) = some_inj_resid (Cod y) \<and>
                    inj_exp (Trn x) = inj_exp (Trn y)"
            using inj_some_pair
            by (metis Pair_inject
                \<open>Some (some_pair (some_inj_resid (Dom x),
                 some_pair (some_inj_resid (Cod x), inj_exp (Trn x)))) =
                 Some (some_pair (some_inj_resid (Dom y),
                 some_pair (some_inj_resid (Cod y), inj_exp (Trn y))))\<close>
                 injD option.inject)
          have "Dom x = Dom y \<and> Cod x = Cod y \<and> Trn x = Trn y"
          proof -
            have 2: "small_rts (Dom x) \<and> small_rts (Dom y) \<and>
                     small_rts (Cod x) \<and> small_rts (Cod y)"
              using assms x y x' y' 1 arr_char inj_on_some_inj_resid small_function_resid
              by blast
            have 3: "Dom x = Dom y \<and> Cod x = Cod y"
              using 1 2 inj_on_some_inj_resid inj_on_def
              by (metis mem_Collect_eq)
            moreover have "Trn x = Trn y"
            proof -
              have "residuation.arr (exponential_rts.resid (Dom x) (Cod x)) (Trn x) \<and>
                    residuation.arr (exponential_rts.resid (Dom x) (Cod x)) (Trn y)"
                by (metis (no_types, lifting) Un_insert_right arrE assms(3) calculation
                    insertE mem_Collect_eq subsetD sup_bot.right_neutral x x' y y')
              thus ?thesis
                using 1 2 inj_inj_exp inj_on_def [of inj_exp]
                      arr_char assms(3) x x'
                by auto
            qed
            ultimately show ?thesis by blast
          qed
          thus "x = y"
            apply (cases x; cases y)
               apply auto[4]
            using x' y' by blast+ 
        qed
        ultimately show ?thesis by blast
      qed
    qed

    text\<open>
      The following result says that, for any small extensional RTS \<open>A\<close> whose arrows
      inhabit type @{typ "'A arr resid"} and are drawn from among the arrows and null
      of @{locale rtscatx}, there is an object \<open>a\<close> of @{locale rtscatx} such that the
      RTS \<open>HOM \<^bold>\<one> a\<close> is isomorphic to \<open>A\<close>.  It is expressed in terms that are intrinsic
      to \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> as an abstract RTS-category, as opposed to the fact \<open>bij_mkobj\<close>,
      which uses the extrinsically given mapping @{term Dom}.
      The result is proved by taking an isomorphic image of the given RTS \<open>A\<close> under the
      injective mapping \<open>inj_arr :: 'A arr \<Rightarrow> 'A\<close>, then applying \<open>bij_mkobj\<close>
      to obtain the corresponding object \<open>a\<close>, and finally using the isomorphism
      \<open>Dom a \<cong> HOM \<^bold>\<one> a\<close> to conclude that \<open>HOM \<^bold>\<one> a \<cong> A\<close>.
    \<close>

    lemma obj_replete:
    fixes A :: "'A arr resid"
    assumes "small_rts A \<and> extensional_rts A"
    and "Collect (residuation.arr A) \<union>
                    {ResiduatedTransitionSystem.partial_magma.null A}
           \<subseteq> Collect arr \<union> {null}"
    shows "\<exists>a. obj a \<and> isomorphic_rts A (HOM \<^bold>\<one> a)"
    proof -
      interpret A: small_rts A
        using assms by blast
      interpret A: extensional_rts A
        using assms by blast
      obtain \<iota> :: "'A arr \<Rightarrow> 'A"
      where \<iota>: "inj_on \<iota> (Collect A.arr \<union> {A.null})"
        using assms inj_inj_arr [of A] null_char by auto
      interpret \<iota>A: inj_image_rts \<iota> A
        using \<iota> by unfold_locales blast
      have "small_rts \<iota>A.resid \<and> extensional_rts \<iota>A.resid"
        using assms \<iota>A.preserves_reflects_small_rts \<iota>A.preserves_extensional_rts
        by blast
      have \<iota>A: "isomorphic_rts A \<iota>A.resid"
        using \<iota>A.F.invertible isomorphic_rts_def by blast

      let ?a = "mkobj \<iota>A.resid"
      have a: "obj ?a \<and> Dom ?a = \<iota>A.resid"
        using \<open>small_rts \<iota>A.resid \<and> extensional_rts \<iota>A.resid\<close> bij_mkobj by auto
      hence "obj ?a \<and> isomorphic_rts \<iota>A.resid (HOM \<^bold>\<one> ?a)"
        using inverse_simulations_DN_UP [of ?a] isomorphic_rts_def by auto
      hence "obj ?a \<and> isomorphic_rts A (HOM \<^bold>\<one> ?a)"
        using \<iota>A isomorphic_rts_transitive by blast
      thus ?thesis by blast
    qed

    text\<open>
      We now turn our attention to showing that, for any given objects \<open>a\<close> and \<open>b\<close>,
      the states from \<open>a\<close> to \<open>b\<close> correspond bijectively (via the ``covariant hom''
      mapping @{term cov_HOM}) to simulations from \<open>HOM \<^bold>\<one> a\<close> to \<open>HOM \<^bold>\<one> b\<close> and the arrows
      from \<open>a\<close> to \<open>b\<close> correspond bijectively to the transformations between such simulations. 
    \<close>

    lemma HOM1_faithful_for_sta:
    assumes "\<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>" and "\<guillemotleft>g : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>"
    and "cov_HOM \<^bold>\<one> f = cov_HOM \<^bold>\<one> g"
    shows "f = g"
    proof -
      interpret A: extensional_rts \<open>Dom a\<close>
        using assms(1) obj_char arr_char
        by (metis (no_types, lifting) H.ide_dom H.in_homE Int_Collect mem_Collect_eq)
      interpret A: small_rts \<open>Dom a\<close>
        using assms(1) obj_char arr_char
        by (metis (no_types, lifting) H.ide_dom H.in_homE Int_Collect)
      interpret B: extensional_rts \<open>Dom b\<close>
        using assms(1) obj_char arr_char
        by (metis (no_types, lifting) H.ide_cod H.in_homE Int_Collect mem_Collect_eq)
      interpret AB: exponential_rts \<open>Dom a\<close> \<open>Dom b\<close> ..
      interpret HOM_1a: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright>\<close>
        using sub_rts_HOM by simp
      interpret F: simulation \<open>Dom a\<close> \<open>Dom b\<close> \<open>AB.Map (Trn f)\<close>
        using assms(1) sta_char
        by (metis (no_types, lifting) AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S Dom_cod Dom_dom
            H.in_homE V.residuation_axioms residuation.ide_implies_arr)
      interpret G: simulation \<open>Dom a\<close> \<open>Dom b\<close> \<open>AB.Map (Trn g)\<close>
        using assms(2) sta_char
        by (metis (no_types, lifting) AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S Dom_cod Dom_dom
            H.in_homE V.residuation_axioms residuation.ide_implies_arr)
      have "\<And>Q R T. transformation (\\\<^sub>1) (Dom a) Q R T
                       \<Longrightarrow> AB.Map (Trn f) \<circ> T = AB.Map (Trn g) \<circ> T"
      proof -
        fix Q R T
        assume T: "transformation (\\\<^sub>1) (Dom a) Q R T"
        interpret T: transformation \<open>(\\<^sub>1)\<close> \<open>Dom a\<close> Q R T
          using T by blast
        let ?t = "mkarr One.resid (Dom a) Q R T"
        have t: "\<guillemotleft>?t : \<^bold>\<one> \<rightarrow> a\<guillemotright>"
        proof
          show "H.arr ?t"
            using A.extensional_rts_axioms A.small_rts_axioms One.is_extensional_rts
                  One.small_rts_axioms T
            by auto
          show "dom ?t = \<^bold>\<one>"
            by (simp add: A.extensional_rts_axioms A.small_rts_axioms
                One.is_extensional_rts One.small_rts_axioms T arr_mkarr(4) one_def)
          show "cod ?t = a"
            using One.is_extensional_rts One.small_rts_axioms T assms(1) dom_char
            by fastforce
        qed
        hence "HOM_1a.arr ?t"
          using assms HOM_1a.arr_char by blast
        moreover have "dom f = a" and "dom g = a"
          using assms by blast+
        ultimately have 1: "f \<star> ?t = g \<star> ?t"
          using assms
          by auto meson
        have "AB.Map (Trn f) \<circ> T = Map f \<circ> T"
          by simp
        also have "... = Map (f \<star> ?t)"
          by (metis (no_types, lifting) A.extensional_rts_axioms
              A.small_rts_axioms H.seqI' Map_hcomp One.is_extensional_rts
              One.small_rts_axioms T assms(1) bij_mkarr(3) t transformation_def)
        also have "... = Map (g \<star> ?t)"
          using 1 by simp
        also have "... = Map g \<circ> T"
          using assms t Map_hcomp [of g ?t] mkarr_def by auto
        also have "... = AB.Map (Trn g) \<circ> T"
          by simp
        finally show "AB.Map (Trn f) \<circ> T = AB.Map (Trn g) \<circ> T" by blast
      qed
      thus ?thesis
        using One.eq_simulation_iff A.weakly_extensional_rts_axioms
              B.weakly_extensional_rts_axioms F.simulation_axioms
              G.simulation_axioms
        by (metis (no_types, lifting) AB.MkIde_Map Dom_cod Dom_dom H.in_homE
            MkArr_Trn V.ide_implies_arr assms(1-2) sta_char)
    qed

    lemma HOM1_faithful_for_arr:
    assumes "arr t" and "arr u" and "src t = src u" and "trg t = trg u"
    and "cov_HOM \<^bold>\<one> t = cov_HOM \<^bold>\<one> u"
    shows "t = u"
    proof (intro arr_eqI)
      let ?a = "dom t" and ?b = "cod t"
      have a: "dom t = ?a \<and> dom u = ?a"
        using assms dom_src [of t] by auto
      have b: "cod t = ?b \<and> cod u = ?b"
        using assms cod_src [of t] by auto
      let ?A = "Dom t" and ?B = "Cod t"
      have A: "Dom t = ?A \<and> Dom u = ?A"
        using assms Dom_src [of t] by auto
      have B: "Cod t = ?B \<and> Cod u = ?B"
        using assms Cod_src [of t] by auto
      interpret A: extensional_rts ?A
        using assms(1) arr_char by blast
      interpret A: small_rts ?A
        using assms(1) arr_char by auto
      interpret B: extensional_rts ?B
        using assms(1) arr_char by auto
      interpret AB: exponential_rts ?A ?B ..
      interpret HOM_1a: sub_rts resid \<open>\<lambda>x. \<guillemotleft>x : \<^bold>\<one> \<rightarrow> dom t\<guillemotright>\<close>
        using sub_rts_HOM by blast
      interpret HOM_1b: sub_rts resid \<open>\<lambda>x. \<guillemotleft>x : \<^bold>\<one> \<rightarrow> cod t\<guillemotright>\<close>
        using sub_rts_HOM by blast
      have *: "\<And>Q R X. transformation (\\\<^sub>1) ?A Q R X
                          \<Longrightarrow> AB.Map (Trn t) \<circ> X = AB.Map (Trn u) \<circ> X"
      proof -
        fix Q R X
        assume X: "transformation (\\\<^sub>1) ?A Q R X"
        interpret X: transformation \<open>(\\<^sub>1)\<close> ?A Q R X
          using X by blast
        let ?x = "mkarr One.resid ?A Q R X"
        have x: "\<guillemotleft>?x : \<^bold>\<one> \<rightarrow> ?a\<guillemotright>"
        proof
          show 1: "H.arr (mkarr (\\\<^sub>1) (Dom t) Q R X)"
            using X arr_mkarr(1) [of One.resid ?A Q R X]
                  One.small_rts_axioms One.extensional_rts_axioms
                  A.small_rts_axioms A.extensional_rts_axioms
            by simp
          show "dom (mkarr (\\\<^sub>1) (Dom t) Q R X) = \<^bold>\<one>"
            using X arr_mkarr(4) [of One.resid ?A Q R X] one_def
                  One.small_rts_axioms One.extensional_rts_axioms
                  A.small_rts_axioms A.extensional_rts_axioms
            by metis
          show "cod (mkarr (\\\<^sub>1) (Dom t) Q R X) = ?a"
          proof -
            have "(\<lambda>ta. if A.arr ta then ta
                        else ResiduatedTransitionSystem.partial_magma.null
                               (Dom (dom t))) =
                  I (Dom t)"
              using assms(1) Dom_dom by presburger
            thus ?thesis
              using assms(1) X arr_mkarr(5) obj_char [of ?a] Dom_dom
                    One.small_rts_axioms One.extensional_rts_axioms
                    A.small_rts_axioms A.extensional_rts_axioms
              by simp
          qed
        qed
        have 1: "t \<star> ?x = u \<star> ?x"
        proof -
          have "HOM_1a.arr ?x"
            using assms x HOM_1a.arr_char by blast
          moreover have "dom t = ?a" and "dom u = ?a"
            using a by blast+
          ultimately show ?thesis
            using assms
            by auto meson
        qed
        have "AB.Map (Trn t) \<circ> X = Map t \<circ> X"
          by simp
        also have "... = Map (t \<star> ?x)"
        proof -
          have "H.seq t ?x"
            using assms x H.seqI by auto
          thus ?thesis
            using assms x Map_hcomp mkarr_def by simp
        qed
        also have "... = Map (u \<star> ?x)"
          using 1 by simp
        also have "... = Map u \<circ> X"
        proof -
          have "H.seq u ?x"
            by (metis (no_types, lifting) "1" H.arr_cod_iff_arr H.dom_null
                H.ext H.in_homE H.seqI dom_char x)
          thus ?thesis
            using assms x Map_hcomp mkarr_def by simp
        qed
        also have "... = AB.Map (Trn u) \<circ> X"
          by simp
        finally show "AB.Map (Trn t) \<circ> X = AB.Map (Trn u) \<circ> X" by blast
      qed
      show "t \<noteq> Null" and "u \<noteq> Null"
        using assms(1-2) arr_char by blast+
      show "Dom t = Dom u" and "Cod t = Cod u"
        using A B by auto
      show "Trn t = Trn u"
      proof (intro AB.arr_eqI)
        show "AB.arr (Trn t)" and "AB.arr (Trn u)"
          using assms(1-2) A B arr_char by auto
        show Dom: "AB.Dom (Trn t) = AB.Dom (Trn u)"
          using assms(1-3) arr_char Map_simps
          apply auto[1]
          by (metis (no_types, lifting))
        show Cod: "AB.Cod (Trn t) = AB.Cod (Trn u)"
          using assms(1-2,4) arr_char Map_simps
          apply auto[1]
          by (metis (no_types, lifting))
        have "AB.Map (Trn t) = AB.Map (Trn u)"
          using assms(1-2) * Dom Cod A B arr_char arr_char
                AB.arr_char AB.arr_char
                One.eq_transformation_iff
                  [of ?A ?B "AB.Dom (Trn t)" "AB.Cod (Trn t)"
                      "AB.Map (Trn t)" "AB.Map (Trn u)"]
                A.weakly_extensional_rts_axioms
                B.weakly_extensional_rts_axioms
          by simp
        thus "\<And>a. A.ide a \<Longrightarrow> AB.Map (Trn t) a = AB.Map (Trn u) a" by simp
      qed
    qed

    lemma HOM1_full_for_sta:
    assumes "obj a" and "obj b" and "simulation (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b) F"
    shows "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> sta f \<and> cov_HOM \<^bold>\<one> f = F"
    proof -
      interpret A: extensional_rts \<open>Dom a\<close>
        using assms obj_char arr_char by blast
      interpret A: small_rts \<open>Dom a\<close>
        using assms obj_char arr_char by blast
      interpret B: extensional_rts \<open>Dom b\<close>
        using assms obj_char arr_char by blast
      interpret B: small_rts \<open>Dom b\<close>
        using assms obj_char arr_char by blast
      interpret A1: exponential_by_One arr_type \<open>Dom a\<close> ..
      interpret B1: exponential_by_One arr_type \<open>Dom b\<close> ..
      interpret HOM_1a: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> a\<guillemotright>\<close>
        using assms sub_rts_HOM by blast
      interpret HOM_1b: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> b\<guillemotright>\<close>
        using assms sub_rts_HOM by blast
      interpret UP_DN_a: inverse_simulations
                           \<open>Dom a\<close> HOM_1a.resid \<open>DN\<^sub>r\<^sub>t\<^sub>s a\<close> \<open>UP\<^sub>r\<^sub>t\<^sub>s a\<close>
        using assms inverse_simulations_DN_UP [of a] dom_char
        by (metis one_def)
      interpret UP_DN_b: inverse_simulations
                           \<open>Dom b\<close> HOM_1b.resid \<open>DN\<^sub>r\<^sub>t\<^sub>s b\<close> \<open>UP\<^sub>r\<^sub>t\<^sub>s b\<close>
        using assms inverse_simulations_DN_UP [of b] dom_char
        by (metis one_def)
      interpret F: simulation \<open>HOM \<^bold>\<one> a\<close> \<open>HOM \<^bold>\<one> b\<close> F
        using assms by blast
      interpret F': simulation \<open>Dom a\<close> \<open>Dom b\<close> \<open>DN\<^sub>r\<^sub>t\<^sub>s b \<circ> F \<circ> UP\<^sub>r\<^sub>t\<^sub>s a\<close>
        using simulation_comp UP_DN_a.G.simulation_axioms
              UP_DN_b.F.simulation_axioms F.simulation_axioms
        by blast
      interpret F': simulation_as_transformation
                      \<open>Dom a\<close> \<open>Dom b\<close> \<open>DN\<^sub>r\<^sub>t\<^sub>s b \<circ> F \<circ> UP\<^sub>r\<^sub>t\<^sub>s a\<close> ..
      show "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> sta f \<and> cov_HOM \<^bold>\<one> f = F"
      proof -
        define f
        where f_def: "f = mksta (Dom a) (Dom b) (DN\<^sub>r\<^sub>t\<^sub>s b \<circ> F \<circ> UP\<^sub>r\<^sub>t\<^sub>s a)"
        have sta_f: "sta f"
          unfolding f_def
          using sta_mksta(1) F'.simulation_axioms
                A.small_rts_axioms A.extensional_rts_axioms
                B.small_rts_axioms B.extensional_rts_axioms
          by blast
        moreover have f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
          using assms sta_f f_def
          by (intro H.in_homI) auto
        moreover have "cov_HOM \<^bold>\<one> f = F"
        proof -
          have "cov_HOM \<^bold>\<one> f = UP\<^sub>r\<^sub>t\<^sub>s b \<circ> Map f \<circ> DN\<^sub>r\<^sub>t\<^sub>s a"
            using f sta_f dom_char cod_char UP_DN_naturality(3) [of f]
            by auto
          also have "... = (UP\<^sub>r\<^sub>t\<^sub>s b \<circ> DN\<^sub>r\<^sub>t\<^sub>s b) \<circ> F \<circ> (UP\<^sub>r\<^sub>t\<^sub>s a \<circ> DN\<^sub>r\<^sub>t\<^sub>s a)"
          proof -
            have "... = UP\<^sub>r\<^sub>t\<^sub>s b \<circ> (DN\<^sub>r\<^sub>t\<^sub>s b \<circ> F \<circ> UP\<^sub>r\<^sub>t\<^sub>s a) \<circ> DN\<^sub>r\<^sub>t\<^sub>s a"
              using f_def mkarr_def by auto
            thus ?thesis
              using comp_assoc by (metis (no_types, lifting))
          qed
          also have "... = F \<circ> (UP\<^sub>r\<^sub>t\<^sub>s a \<circ> DN\<^sub>r\<^sub>t\<^sub>s a)"
            using comp_identity_simulation [of HOM_1a.resid HOM_1b.resid F]
                  F.simulation_axioms UP_DN_b.inv
            by auto
          also have "... = F"
            using comp_simulation_identity [of HOM_1a.resid HOM_1b.resid F]
                  F.simulation_axioms UP_DN_a.inv
            by auto
          finally show ?thesis by blast
        qed
        ultimately show ?thesis by blast
      qed
    qed

    lemma HOM1_full_for_arr:
    assumes "sta f" and "sta g" and "H.par f g"
    and "transformation (HOM \<^bold>\<one> (dom f)) (HOM \<^bold>\<one> (cod f))
            (cov_HOM \<^bold>\<one> f) (cov_HOM \<^bold>\<one> g) T"
    shows "\<exists>t. arr t \<and> src t = f \<and> trg t = g \<and> cov_HOM \<^bold>\<one> t = T"
    proof -
      let ?a = "dom f" and ?b = "cod f"
      have a: "obj ?a" and b: "obj ?b"
        using assms by auto
      have f: "\<guillemotleft>f : ?a \<rightarrow> ?b\<guillemotright>" and g: "\<guillemotleft>g : ?a \<rightarrow> ?b\<guillemotright>"
        using assms by auto
      let ?A = "Dom ?a" and ?B = "Dom ?b"
      have 0: "Dom f = ?A \<and> Cod f = ?B \<and> Dom g = ?A \<and> Cod g = ?B"
        using assms f dom_char cod_char
        by (metis (no_types, lifting) Dom_cod Dom_dom arr_coincidence)
      have A: "small_rts ?A \<and> extensional_rts ?A"
        using assms arr_char by auto
      have B: "small_rts ?B \<and> extensional_rts ?B"
        using assms arr_char by auto
      interpret A: extensional_rts ?A using A by blast
      interpret A: small_rts ?A using A by blast
      interpret B: extensional_rts ?B using B by blast
      interpret B: small_rts ?B using B by blast
      interpret AB: exponential_rts ?A ?B ..
      interpret HOM_1a: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> ?a\<guillemotright>\<close>
        using a sub_rts_HOM by blast
      interpret HOM_1a: sub_rts_of_extensional_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> ?a\<guillemotright>\<close> ..
      interpret HOM_1a: small_rts \<open>HOM \<^bold>\<one> ?a\<close>
      proof -
        have "Collect HOM_1a.arr \<subseteq> H.hom \<^bold>\<one> ?a"
          using HOM_1a.arr_char by blast
        thus "small_rts (HOM \<^bold>\<one> ?a)"
          using assms obj_one H.terminal_def small_homs [of "\<^bold>\<one>" ?a]
                smaller_than_small
          by unfold_locales auto
      qed
      interpret HOM_1b: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> ?b\<guillemotright>\<close>
        using b sub_rts_HOM by blast
      interpret HOM_1b: sub_rts_of_extensional_rts resid \<open>\<lambda>t. \<guillemotleft>t: \<^bold>\<one> \<rightarrow> ?b\<guillemotright>\<close> ..
      interpret HOM_1b: small_rts \<open>HOM \<^bold>\<one> ?b\<close>
      proof -
        have "Collect HOM_1b.arr \<subseteq> H.hom \<^bold>\<one> ?b"
          using HOM_1b.arr_char by blast
        thus "small_rts (HOM \<^bold>\<one> ?b)"
          using assms obj_one H.terminal_def small_homs [of "\<^bold>\<one>" ?b]
                smaller_than_small
          by unfold_locales auto
      qed
      interpret UP_DN_a: inverse_simulations
                           ?A HOM_1a.resid \<open>DN\<^sub>r\<^sub>t\<^sub>s ?a\<close> \<open>UP\<^sub>r\<^sub>t\<^sub>s ?a\<close>
        using assms a inverse_simulations_DN_UP [of ?a] dom_char one_def
        by metis
      interpret UP_DN_b: inverse_simulations
                           ?B HOM_1b.resid \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b\<close> \<open>UP\<^sub>r\<^sub>t\<^sub>s ?b\<close>
        using assms b inverse_simulations_DN_UP [of ?b] dom_char one_def
        by metis
      interpret T: transformation
                     \<open>HOM \<^bold>\<one> ?a\<close> \<open>HOM \<^bold>\<one> ?b\<close> \<open>cov_HOM \<^bold>\<one> f\<close> \<open>cov_HOM \<^bold>\<one> g\<close> T
        using assms(4) by blast
      interpret F': simulation ?A ?B \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a\<close>
        using simulation_comp UP_DN_a.G.simulation_axioms
              UP_DN_b.F.simulation_axioms T.F.simulation_axioms
        by blast
      interpret G': simulation ?A ?B \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a\<close>
        using simulation_comp UP_DN_a.G.simulation_axioms
              UP_DN_b.F.simulation_axioms T.G.simulation_axioms
        by blast
      interpret DN_T: transformation HOM_1a.resid ?B
                        \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f\<close> \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g\<close>
                        \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> T\<close>
        using UP_DN_a.G.simulation_axioms UP_DN_b.F.simulation_axioms
              T.transformation_axioms F'.simulation_axioms G'.simulation_axioms
              transformation_whisker_left B.weakly_extensional_rts_axioms
        by fastforce
      interpret T': transformation ?A ?B
                      \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a\<close>
                      \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a\<close>
                      \<open>DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> T \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a\<close>
        using UP_DN_a.G.simulation_axioms UP_DN_b.F.simulation_axioms
              T.transformation_axioms DN_T.transformation_axioms
              DN_T.F.simulation_axioms DN_T.G.simulation_axioms
              transformation_whisker_right A.weakly_extensional_rts_axioms
        by fastforce
      define t
        where t_def: "t = mkarr ?A ?B
                            (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)
                            (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)
                            (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> T \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)"
      have t: "\<guillemotleft>t : ?a \<rightarrow> ?b\<guillemotright>"
      proof
        show t: "H.arr t"
        proof -
          have "V.arr t"
            unfolding t_def
            using arr_mkarr(1) T'.transformation_axioms
                  F'.simulation_axioms G'.simulation_axioms
                  A.small_rts_axioms A.extensional_rts_axioms
                  B.small_rts_axioms B.extensional_rts_axioms
            by blast
          thus ?thesis by auto
        qed
        show "dom t = ?a"
          using assms(3) a t f dom_char t_def by auto
        show "cod t = ?b"
          using assms(3) b t f cod_char t_def by auto
      qed
      have 1: "arr t"
        using t by auto
      moreover have "src t = f"
      proof -
        have 2: "src t = mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)"
          using t t_def mkarr_simps(3) A.small_rts_axioms A.extensional_rts_axioms
                B.small_rts_axioms B.extensional_rts_axioms T'.transformation_axioms
          by blast
        also have "... = f"
        proof (intro arr_eqI)
          show "mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a) \<noteq> Null"
            unfolding mkarr_def by blast
          show "f \<noteq> Null"
            using f H_arr_char by blast
          show "Dom (mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                Dom f"
            using f dom_char mkarr_def by auto
          show "Cod (mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                Cod f"
            using f cod_char mkarr_def by auto
          show "Trn (mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                Trn f"
          proof -
            have "Trn (mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                  AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)"
              using mkarr_def by simp
            also have "... = Trn f"
            proof (intro AB.arr_eqI)
              show "AB.arr (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a))"
              proof -
                have "arr (src t)"
                  using 1 V.arr_src_iff_arr by blast
                thus ?thesis
                  using 2 arr_char mkarr_def by auto
              qed
              show "AB.arr (Trn f)"
                using f arr_char [of f] dom_char cod_char by auto
              show "AB.Dom (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                    AB.Dom (Trn f)"
              proof -
                have "AB.Dom (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                      DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a"
                  by simp
                also have "... = AB.Map (Trn f)"
                  using assms f 0 UP_DN_naturality(4) by simp
                also have "... = AB.Dom (Trn f)"
                  using assms sta_char dom_char cod_char AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S
                  by fastforce
                finally show ?thesis by blast
              qed
              show "AB.Cod (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                    AB.Cod (Trn f)"
              proof -
                have "AB.Cod (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                      DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a"
                  by simp
                also have "... = AB.Map (Trn f)"
                  using assms f 0 UP_DN_naturality(4) by simp
                also have "... = AB.Cod (Trn f)"
                  using assms sta_char dom_char cod_char AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S
                  by fastforce
                finally show ?thesis by blast
              qed
              show "\<And>x. A.ide x \<Longrightarrow>
                          AB.Map
                            (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) x =
                          AB.Map (Trn f) x"
              proof -
                fix x
                assume x: "A.ide x"
                have "AB.Map
                        (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) x =
                      (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a) x"
                  by simp
                also have "... = AB.Map (Trn f) x"
                  using assms f 0 UP_DN_naturality(4) [of f] by simp
                finally
                show "AB.Map
                        (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> f \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) x =
                      AB.Map (Trn f) x"
                  by blast
              qed
            qed
            finally show ?thesis by blast
          qed
        qed
        finally show ?thesis by blast
      qed
      moreover have "trg t = g"
      proof -
        have 2: "trg t = mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)"
          using t t_def mkarr_simps(4) A.small_rts_axioms A.extensional_rts_axioms
                B.small_rts_axioms B.extensional_rts_axioms T'.transformation_axioms
          by blast
        also have "... = g"
        proof (intro arr_eqI)
          show "mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a) \<noteq> Null"
            unfolding mkarr_def by blast
          show "g \<noteq> Null"
            using g H_arr_char by blast
          show "Dom (mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                Dom g"
            using assms g dom_char mkarr_def by auto
          show "Cod (mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) = Cod g"
            using assms g cod_char mkarr_def by auto
          show "Trn (mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) = Trn g"
          proof -
            have 3: "DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a = AB.Map (Trn g)"
              using assms g 0 UP_DN_naturality(4)
              apply simp
              by presburger
            have "Trn (mksta ?A ?B (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                  AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)"
             using mkarr_def by simp
            also have "... = Trn g"
            proof (intro AB.arr_eqI)
              show "AB.arr (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a))"
                using AB.ide_implies_arr G'.simulation_axioms by blast
              show "AB.arr (Trn g)"
                using assms g arr_char [of g] dom_char cod_char by auto
              show "AB.Dom (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                    AB.Dom (Trn g)"
                using assms 3 sta_char AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S by simp
              show "AB.Cod (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) =
                    AB.Cod (Trn g)"
                 using assms 3 sta_char AB.ide_char\<^sub>E\<^sub>R\<^sub>T\<^sub>S by simp
              show "\<And>x. A.ide x \<Longrightarrow>
                          AB.Map
                            (AB.MkIde (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> cov_HOM \<^bold>\<one> g \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a)) x =
                          AB.Map (Trn g) x"
                using 3 by simp
            qed
            finally show ?thesis by blast
          qed
        qed
        finally show ?thesis by blast
      qed
      moreover have "cov_HOM \<^bold>\<one> t = T"
      proof -
        have "cov_HOM \<^bold>\<one> t = UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> Map t \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a"
        proof -
          have "arr t \<and> dom f = dom t \<and> cod f = cod t"
            using f t by auto
          thus ?thesis
            using UP_DN_naturality(3) [of t] by presburger
        qed
        also have "... = UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> (DN\<^sub>r\<^sub>t\<^sub>s ?b \<circ> T \<circ> UP\<^sub>r\<^sub>t\<^sub>s ?a) \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a"
          unfolding t_def mkarr_def by simp
        also have "... = (UP\<^sub>r\<^sub>t\<^sub>s ?b \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?b) \<circ> T \<circ> (UP\<^sub>r\<^sub>t\<^sub>s ?a \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a)"
          (* using comp_assoc by (metis (no_types, lifting)) (* 7 sec *) *)
          using comp_assoc by smt
        also have "... = T \<circ> (UP\<^sub>r\<^sub>t\<^sub>s ?a \<circ> DN\<^sub>r\<^sub>t\<^sub>s ?a)"
          using comp_identity_transformation
                  [of HOM_1a.resid HOM_1b.resid _ _ T]
                T.transformation_axioms UP_DN_b.inv
          by auto
        also have "... = T"
          using comp_transformation_identity
                  [of HOM_1a.resid HOM_1b.resid _ _ T]
                T.transformation_axioms UP_DN_a.inv
          by auto
        finally show ?thesis by blast
      qed
      ultimately show ?thesis by blast
    qed

    lemma bij_HOM1_sta:
    assumes "obj a" and "obj b"
    shows "bij_betw (cov_HOM \<^bold>\<one>) {f. \<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>}
             (Collect (simulation (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b)))"
    proof -
      interpret HOM_1a: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright>\<close>
        using assms(1) sub_rts_HOM by blast
      interpret HOM_1b: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> b\<guillemotright>\<close>
        using assms(2) sub_rts_HOM by blast
      have 1: "cov_HOM \<^bold>\<one> \<in> {f. \<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>}
                              \<rightarrow> Collect (simulation (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b))"
      proof
        fix f
        assume f: "f \<in> {f. \<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>}"
        have "sta f \<and> dom f = a \<and> cod f = b"
          using f by auto
        thus "cov_HOM \<^bold>\<one> f \<in> Collect (simulation (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b))"
          using simulation_cov_HOM_sta [of "\<^bold>\<one>" f] by blast
      qed
      show "bij_betw (cov_HOM \<^bold>\<one>) {f. \<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>}
              (Collect (simulation (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b)))"
      proof (unfold bij_betw_def, intro conjI)
        show "inj_on (cov_HOM \<^bold>\<one>) {f. \<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>}"
          using assms HOM1_faithful_for_sta [of _ a b]
          unfolding inj_on_def
          by auto
        show "cov_HOM \<^bold>\<one> ` {f. \<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>} =
              Collect (simulation (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b))"
        proof
          show "cov_HOM \<^bold>\<one> ` {f. \<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>}
                   \<subseteq> Collect (simulation HOM_1a.resid HOM_1b.resid)"
            using 1 by blast
          show "Collect (simulation HOM_1a.resid HOM_1b.resid)
                   \<subseteq> cov_HOM \<^bold>\<one> ` {f. \<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>}"
          proof
            fix F
            assume F: "F \<in> Collect (simulation HOM_1a.resid HOM_1b.resid)"
            obtain f where f: "\<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright> \<and> cov_HOM \<^bold>\<one> f = F"
              using assms F HOM1_full_for_sta [of a b F]
                    HOM_1a.arr_char HOM_1b.arr_char
              by auto
            show "F \<in> cov_HOM \<^bold>\<one> ` {f. \<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>}"
              using f by blast
          qed
        qed
      qed
    qed

    lemma bij_HOM1_arr:
    assumes "\<guillemotleft>f : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>" and "\<guillemotleft>g : a \<rightarrow>\<^sub>s\<^sub>t\<^sub>a b\<guillemotright>"
    shows "bij_betw (cov_HOM \<^bold>\<one>) {t. \<guillemotleft>t : f \<Rightarrow> g\<guillemotright>}
             (Collect (transformation (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b)
                (cov_HOM \<^bold>\<one> f) (cov_HOM \<^bold>\<one> g)))"
    proof -
      interpret HOM_1a: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> a\<guillemotright>\<close>
        using assms(1) sub_rts_HOM by blast
      interpret HOM_1b: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : \<^bold>\<one> \<rightarrow> b\<guillemotright>\<close>
        using assms(2) sub_rts_HOM by blast
      have 1: "cov_HOM \<^bold>\<one> \<in>
                 {t. \<guillemotleft>t : f \<Rightarrow> g\<guillemotright>}
                    \<rightarrow> Collect (transformation
                                  (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b) (cov_HOM \<^bold>\<one> f) (cov_HOM \<^bold>\<one> g))"
      proof
        fix t
        assume t: "t \<in> {t. \<guillemotleft>t : f \<Rightarrow> g\<guillemotright>}"
        thus "cov_HOM \<^bold>\<one> t \<in> Collect (transformation (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b)
                                       (cov_HOM \<^bold>\<one> f) (cov_HOM \<^bold>\<one> g))"
          using assms(1) t transformation_cov_HOM_arr [of "\<^bold>\<one>" t] obj_one by auto
      qed
      show "bij_betw (cov_HOM \<^bold>\<one>) {t. \<guillemotleft>t : f \<Rightarrow> g\<guillemotright>}
             (Collect (transformation (HOM \<^bold>\<one> a) (HOM \<^bold>\<one> b)
                         (cov_HOM \<^bold>\<one> f) (cov_HOM \<^bold>\<one> g)))"
      proof (unfold bij_betw_def, intro conjI)
        show "inj_on (cov_HOM \<^bold>\<one>) {t. \<guillemotleft>t : f \<Rightarrow> g\<guillemotright>}"
          using assms HOM1_faithful_for_arr
          unfolding inj_on_def
          by auto
        show "cov_HOM \<^bold>\<one> ` {t. \<guillemotleft>t : f \<Rightarrow> g\<guillemotright>} =
              Collect (transformation HOM_1a.resid HOM_1b.resid
                         (cov_HOM \<^bold>\<one> f) (cov_HOM \<^bold>\<one> g))"
        proof
          show "cov_HOM \<^bold>\<one> ` {t. \<guillemotleft>t : f \<Rightarrow> g\<guillemotright>} \<subseteq>
                Collect (transformation HOM_1a.resid HOM_1b.resid
                           (cov_HOM \<^bold>\<one> f) (cov_HOM \<^bold>\<one> g))"
            using 1 by blast
          show "Collect (transformation HOM_1a.resid HOM_1b.resid
                           (cov_HOM \<^bold>\<one> f) (cov_HOM \<^bold>\<one> g)) \<subseteq>
                cov_HOM \<^bold>\<one> ` {t. \<guillemotleft>t : f \<Rightarrow> g\<guillemotright>}"
          proof
            fix T
            assume T: "T \<in> Collect (transformation HOM_1a.resid HOM_1b.resid
                                      (cov_HOM \<^bold>\<one> f) (cov_HOM \<^bold>\<one> g))"
            obtain t where t: "\<guillemotleft>t : f \<Rightarrow> g\<guillemotright> \<and> cov_HOM \<^bold>\<one> t = T"
              using assms T HOM1_full_for_arr [of f g T] arr_char
                    HOM_1a.arr_char HOM_1b.arr_char
              by blast
            show "T \<in> cov_HOM \<^bold>\<one> ` {t. arr t \<and> src t = f \<and> trg t = g}"
              using t by blast
          qed
        qed
      qed
    qed

    text\<open>
      My original objective for the results in this section was to obtain a characterization
      up to equivalence of the RTS-category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> in terms of intrinsic notions that make
      sense for any RTS-category, and to carry out the proof of cartesian closure using
      @{term "HOM \<^bold>\<one>"} in place of @{term Dom}.  This can probably be done, and I did push the
      idea through the construction of products, but for exponentials there were some
      technicalities that started to get messy and become distractions from the main things
      that I was trying to do.  So I decided to leave this program for future work.
    \<close>

  end

end

