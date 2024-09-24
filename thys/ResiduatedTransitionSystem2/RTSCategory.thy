(*  Title:       RTSCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "RTS-Categories"

text\<open>
  In this section, we develop the notion of an \emph{RTS-category}, which is analogous
  to a 2-category, except that the ``vertical'' structure is that of an RTS,
  rather than a category.  So an RTS-category is a category with respect to
  a ``horizontal'' composition, which also has a vertical structure as an RTS.
\<close>

theory RTSCategory
imports Main RTSConstructions Category3.ConcreteCategory
        Category3.CartesianClosedCategory Category3.EquivalenceOfCategories
begin

  subsection "Definition and Basic Properties"

  locale rts_category =
    V: extensional_rts resid +
    H: category hcomp +
    VV: fibered_product_rts resid resid resid H.dom H.cod +
    H: simulation VV.resid resid
          \<open>\<lambda>t. if VV.arr t then hcomp (fst t) (snd t) else V.null\<close>
  for resid :: "'a resid"  (infix \<open>\\<close> 70)
  and hcomp :: "'a comp"   (infixr \<open>\<star>\<close> 53) +
  assumes null_coincidence [simp]: "H.null = V.null"
  and arr_coincidence [simp]: "H.arr = V.arr"
  and src_dom [simp]: "V.src (H.dom t) = H.dom t"
  begin

    notation H.in_hom     (\<open>\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>\<close>)

    abbreviation null
    where "null \<equiv> V.null"

    abbreviation arr
    where "arr \<equiv> V.arr"

    abbreviation src
    where "src \<equiv> V.src"

    abbreviation trg
    where "trg \<equiv> V.trg"

    abbreviation dom
    where "dom \<equiv> H.dom"

    abbreviation cod
    where "cod \<equiv> H.cod"

    text\<open>
      We refer to the identities for the horizontal composition as \emph{objects}.
    \<close>
    abbreviation obj
    where "obj \<equiv> H.ide"

    text\<open>
      We refer to the identities for the vertical residuation as \emph{states}.
    \<close>

    abbreviation sta
    where "sta \<equiv> V.ide"

    interpretation VV: fibered_product_of_extensional_rts resid resid resid dom cod
      ..
    interpretation H: simulation_between_extensional_rts VV.resid resid
                   \<open>\<lambda>t. if VV.arr t then fst t \<star> snd t else null\<close>
      ..

    (* TODO: The following fact belongs all the way back in partial_composition. *)
    lemma obj_is_isolated:
    assumes "obj a" and "obj a'" and "a \<star> a' \<noteq> null"
    shows "a = a'"
      using assms H.ide_def by fastforce

    lemma obj_implies_sta:
    assumes "obj a"
    shows "sta a"
      using assms H.ide_char arr_coincidence V.ide_src src_dom by metis

    lemma trg_dom [simp]:
    shows "trg (dom t) = dom t"
      by (metis src_dom V.trg_src)

    lemma src_cod [simp]:
    shows "src (cod t) = cod t"
      by (metis H.dom_cod src_dom)

    lemma trg_cod [simp]:
    shows "trg (cod t) = cod t"
      by (metis H.dom_cod src_dom V.trg_src)

    lemma dom_src [simp]:
    shows "dom (src t) = dom t"
      using H.preserves_src
      by (metis VV.F.preserves_con VV.F.preserves_reflects_arr V.con_arr_src(1)
          V.con_imp_eq_src V.src_def src_dom)

    lemma dom_trg [simp]:
    shows "dom (trg t) = dom t"
      using H.preserves_trg
      by (metis VV.F.extensional VV.F.preserves_trg V.arr_trg_iff_arr trg_dom)

    lemma cod_src [simp]:
    shows "cod (src t) = cod t"
      using H.preserves_src
      by (metis VV.G.preserves_con VV.G.preserves_reflects_arr V.con_arr_src(1)
          V.con_imp_eq_src src_cod V.src_def)

    lemma cod_trg [simp]:
    shows "cod (trg t) = cod t"
      using H.preserves_trg
      by (metis VV.G.extensional VV.G.preserves_trg V.arr_trg_iff_arr trg_cod)

    lemma arr_hcomp [intro]:
    assumes "H.seq t u"
    shows "arr (t \<star> u)"
      using assms VV.arr_char H.preserves_reflects_arr by auto

    lemma sta_hcomp [intro]:
    assumes "H.seq t u" and "sta t" and "sta u"
    shows "sta (t \<star> u)"
      using assms VV.ide_char\<^sub>F\<^sub>P H.preserves_ide
      by (elim H.seqE) auto

    lemma src_hcomp [simp]:
    assumes "H.seq t u"
    shows "src (t \<star> u) = src t \<star> src u"
      using assms VV.arr_char H.preserves_src [of "(t, u)"] VV.src_char VV.arr_src_iff_arr
      by (elim H.seqE) auto

    lemma trg_hcomp [simp]:
    assumes "H.seq t u"
    shows "trg (t \<star> u) = trg t \<star> trg u"
      using assms VV.arr_char H.preserves_trg [of "(t, u)"] VV.trg_char VV.arr_trg_iff_arr
      by (elim H.seqE) auto

    lemma con_implies_hpar:
    assumes "t \<frown> u"
    shows "H.par t u"
      using assms V.con_implies_arr arr_coincidence cod_src V.con_imp_eq_src
            dom_src
      by metis

    lemma hpar_arr_resid:
    assumes "t \<frown> u"
    shows "H.par t (t \\ u)"
      using assms con_implies_hpar V.con_implies_arr arr_coincidence V.arr_resid
            cod_src dom_src V.resid_arr_self
      by auto

    lemma dom_resid [simp]:
    assumes "t \<frown> u"
    shows "dom (t \\ u) = dom t"
      using assms hpar_arr_resid by simp

    lemma cod_resid [simp]:
    assumes "t \<frown> u"
    shows "cod (t \\ u) = cod t"
      using assms hpar_arr_resid by simp

    text\<open>
      RTS-categories enjoy an ``interchange law'' between residuation and composition.
    \<close>

    lemma resid_hcomp:
    assumes "r \<frown> t" and "s \<frown> u" and "H.seq r s"
    shows "r \<star> s \<frown> t \<star> u"
    and "(r \<star> s) \\ (t \<star> u) = r \\ t \<star> s \\ u"
    proof -
      have tu: "H.seq t u"
        using assms con_implies_hpar
        by (elim H.seqE, intro H.seqI) auto
      have 1: "VV.con (r, s) (t, u)"
        using assms tu VV.con_char
        by (elim H.seqE) auto
      have 2: "H.dom r = H.cod s \<and> H.dom t = H.cod u"
        using assms tu by blast
      show "r \<star> s \<frown> t \<star> u"
        using assms 1 2 VV.con_char VV.arr_char V.con_implies_arr
              H.preserves_con [of "(r, s)" "(t, u)"]
        by simp
      show "(r \<star> s) \\ (t \<star> u) = r \\ t \<star> s \\ u"
        using assms 1 2 VV.resid_def VV.arr_char V.con_implies_arr
              H.preserves_resid [of "(r, s)" "(t, u)"]
        by auto
    qed

    lemma dom_vcomp [simp]:
    assumes "V.composable t u"
    shows "dom (t \<cdot> u) = dom t"
      using assms arr_coincidence
      by (metis dom_src V.src_comp)

    lemma cod_vcomp [simp]:
    assumes "V.composable t u"
    shows "cod (t \<cdot> u) = cod t"
      using assms arr_coincidence
      by (metis cod_src V.src_comp)

    text\<open>
      If the vertical structure is that of an RTS with composites, then the usual
      middle-four interchange law holds, as for 2-categories, between the horizontal
      and vertical compositions.
    \<close>
    lemma interchange:
    assumes "V.composable t r" and "V.composable u s" and "H.seq t u"
    shows "V.composable (t \<star> u) (r \<star> s)"
    and "(t \<star> u) \<cdot> (r \<star> s) = (t \<cdot> r) \<star> (u \<cdot> s)"
    proof -
      have r: "arr r" and s: "arr s" and rs: "dom r = cod s"
        using assms H.seqE
          apply auto[3]
        by (metis cod_src cod_trg V.composable_imp_seq dom_src dom_trg V.seqE\<^sub>W\<^sub>E)
      have 1: "V.composite_of (t \<star> u) (r \<star> s) ((t \<cdot> r) \<star> (u \<cdot> s))"
      proof
        have 2: "t \<cdot> r \<frown> t"
          using assms(1) V.con_comp_iff [of t t r] V.con_sym by force
        have 3: "u \<cdot> s \<frown> u"
          using assms(2) V.con_comp_iff [of u u s] V.con_sym by force
        show "t \<star> u \<lesssim> t \<cdot> r \<star> u \<cdot> s"
          by (metis 2 3 V.arr_comp V.arr_resid V.con_sym V.prfx_comp
              arr_coincidence assms(1-3) resid_hcomp(1) resid_hcomp(2)
              sta_hcomp)
        show "(t \<cdot> r \<star> u \<cdot> s) \\ (t \<star> u) \<sim> r \<star> s"
          by (metis 2 3 H.seqI V.comp_resid_prfx V.prfx_reflexive
              arr_coincidence hpar_arr_resid resid_hcomp(2) rs)
      qed
      show "V.composable (t \<star> u) (r \<star> s)"
        using assms 1 V.composable_def by auto
      show "(t \<star> u) \<cdot> (r \<star> s) = t \<cdot> r \<star> u \<cdot> s"
        using 1 V.comp_is_composite_of by blast
    qed

    lemma hcomp_monotone:
    assumes "r \<lesssim> t" and "s \<lesssim> u" and "H.seq r s"
    shows "r \<star> s \<lesssim> t \<star> u"
      by (metis V.prfx_implies_con assms(1-3) hpar_arr_resid
          resid_hcomp(1-2) sta_hcomp)

    lemma dom_join [simp]:
    assumes "V.joinable t u"
    shows "H.dom (t \<squnion> u) = H.dom t"
      using assms con_implies_hpar V.joinable_implies_con
      by (metis dom_trg hpar_arr_resid V.trg_join)

    lemma cod_join [simp]:
    assumes "V.joinable t u"
    shows "H.cod (t \<squnion> u) = H.cod t"
      using assms con_implies_hpar V.joinable_implies_con
      by (metis cod_trg hpar_arr_resid V.trg_join)

    lemma join_hcomp:
    assumes "V.joinable r t" and "V.joinable s u" and "H.seq r s"
    shows "(r \<star> s) \<squnion> (t \<star> u) = (r \<squnion> t) \<star> (s \<squnion> u)"
    proof (intro V.join_eqI)
      show "r \<star> s \<lesssim> (r \<squnion> t) \<star> (s \<squnion> u)"
        using assms hcomp_monotone V.arr_prfx_join_self by presburger
      show 0: "t \<star> u \<lesssim> (r \<squnion> t) \<star> (s \<squnion> u)"
        using assms hcomp_monotone V.arr_prfx_join_self V.join_sym H.seqE H.seqI
              con_implies_hpar V.joinable_iff_join_not_null V.joinable_implies_con
        by metis
      have 1: "H.seq (r \<squnion> t) (s \<squnion> u)"
        using assms H.seqE H.seqI arr_coincidence cod_join dom_join V.joinable_iff_arr_join
        by metis
      have 2: "r \<squnion> t \<frown> t \<and> r \<squnion> t \<frown> r"
        using assms V.arr_prfx_join_self V.con_sym V.join_sym V.joinable_iff_arr_join
              V.prfx_implies_con
        by metis
      have 3: "s \<squnion> u \<frown> u \<and> s \<squnion> u \<frown> s"
        using assms V.arr_prfx_join_self V.con_sym V.join_sym V.joinable_iff_arr_join
              V.prfx_implies_con
        by metis
      have 4: "(r \<squnion> t) \\ t = r \\ t \<and> (r \<squnion> t) \\ r = t \\ r"
        by (metis (no_types, lifting) 2 V.arr_resid_iff_con V.con_sym
            V.join_src V.join_sym V.joinable_implies_con V.resid_join\<^sub>E(3)
            V.src_resid V.trg_def assms(1))
      have 5: "(s \<squnion> u) \\ u = s \\ u \<and> (s \<squnion> u) \\ s = u \\ s"
        by (metis (no_types, lifting) 3 V.arr_resid_iff_con V.con_sym
            V.join_src V.join_sym V.joinable_implies_con V.resid_join\<^sub>E(3)
            V.src_resid V.trg_def assms(2))
      show "((r \<squnion> t) \<star> (s \<squnion> u)) \\ (t \<star> u) = (r \<star> s) \\ (t \<star> u)"
        using assms 1 2 3 4 5 V.joinable_implies_con resid_hcomp by auto
      show "((r \<squnion> t) \<star> (s \<squnion> u)) \\ (r \<star> s) = (t \<star> u) \\ (r \<star> s)"
        using assms 1 2 3 4 5 V.joinable_implies_con resid_hcomp
        apply auto[1]
        by (metis 0 V.arr_resid_iff_con V.prfx_implies_con hpar_arr_resid resid_hcomp(2))
    qed

    text\<open>
      The source and target maps given by the vertical structure are functorial
      with respect to the horizontal structure.
    \<close>

    sublocale src: "functor" hcomp hcomp src
      apply unfold_locales
      subgoal using V.src_def by auto
      by auto

    sublocale trg: "functor" hcomp hcomp trg
      apply unfold_locales
      subgoal using V.trg_def by auto
      by auto

    text\<open>
      An isomorphism with respect to the horizontal composition is an identity
      with respect to the vertical residuation.
    \<close>

    lemma iso_implies_sta:
    assumes "H.iso f"
    shows "sta f"
    proof -
      obtain g where inv_fg: "H.inverse_arrows f g"
        using assms by blast
      have f: "arr f" and g: "arr g" and fg: "H.dom f = H.cod g"
        using inv_fg arr_coincidence
        by auto fastforce+
      (* TODO: There has to be a shorter proof than this. *)
      have "sta (cod f \<star> f)"
      proof -
        have "sta ((trg f \<star> trg g) \<star> f)"
        proof -
          have 1: "sta (trg g \<star> f)"
          proof -
            have 2: "sta ((g \<star> src f) \<cdot> (trg g \<star> f))"
            proof -
              have "sta (g \<star> f)"
                using inv_fg obj_implies_sta by blast
              moreover have "V.composable g (trg g)"
                using V.composable_iff_comp_not_null g by auto
              moreover have "V.composable (src f) f"
                using V.composable_iff_comp_not_null f by auto
              moreover have "H.seq g (src f)"
                by (metis H.dom_null H.ext H.ide_compE
                    H.inverse_arrowsE H.seqI cod_src dom_trg
                    inv_fg src.preserves_arr trg.is_extensional)
              ultimately show ?thesis
                using g interchange by auto
            qed
            moreover have "V.composable (g \<star> src f) (trg g \<star> f)"
              using 2 V.composable_iff_arr_comp by blast
            ultimately show "sta (trg g \<star> f)"
              using g V.comp_is_composite_of
                    V.divisors_of_ide
                      [of "g \<star> src f" "trg g \<star> f" "(g \<star> src f) \<cdot> (trg g \<star> f)"]
              by blast
          qed
          moreover have "H.seq (trg f) (trg g \<star> f)"
            using f g inv_fg 1
            by (intro H.seqI) auto
          moreover have "sta (trg f)"
            using assms arr_coincidence by fastforce
          ultimately show ?thesis
            using g H.comp_assoc by auto
        qed
        moreover have "H.inverse_arrows (trg f) (trg g)"
          using inv_fg trg.preserves_inverse_arrows by auto
        ultimately show ?thesis
          by fastforce
      qed
      thus "sta f"
        using assms H.comp_cod_arr by force
    qed

  subsection "Hom-RTS's"

    text\<open>
      We have defined the vertical structure of an RTS-category as a ``global'' residuation,
      but in fact a pair of arrows can only be consistent if they have the same domain and
      codomain with respect to the horizontal composition.  If we restrict the global
      residuation to sets of arrows having the same domain and codomain, then we obtain
      hom-RTS's, analogous to the hom-categories in the case of a 2-category.
    \<close>

    abbreviation HOM
    where "HOM a b \<equiv> sub_rts.resid resid (\<lambda>t. \<guillemotleft>t : a \<rightarrow> b\<guillemotright>)"

    lemma sub_rts_HOM:
    shows "sub_rts resid (\<lambda>t. \<guillemotleft>t : a \<rightarrow> b\<guillemotright>)"
    proof
      show "\<And>t. \<guillemotleft>t : a \<rightarrow> b\<guillemotright> \<Longrightarrow> arr t"
        by auto
      show "\<And>t u. \<lbrakk>\<guillemotleft>t : a \<rightarrow> b\<guillemotright>; \<guillemotleft>u : a \<rightarrow> b\<guillemotright>; t \<frown> u\<rbrakk> \<Longrightarrow> \<guillemotleft>t \\ u : a \<rightarrow> b\<guillemotright>"
        using H.in_homE H.in_homI hpar_arr_resid by metis
      show "\<And>t u. \<lbrakk>\<guillemotleft>t : a \<rightarrow> b\<guillemotright>; \<guillemotleft>u : a \<rightarrow> b\<guillemotright>; t \<frown> u\<rbrakk> \<Longrightarrow>
                     \<exists>X. \<guillemotleft>X : a \<rightarrow> b\<guillemotright> \<and> X \<in> V.sources t \<and> X \<in> V.sources u"
        using arr_coincidence
        by (metis (mono_tags, lifting) H.arr_iff_in_hom H.in_homE cod_src
            V.con_imp_coinitial_ax V.con_implies_arr(1) dom_src V.src_eqI
            V.src_in_sources)
    qed

    lemma extensional_rts_HOM:
    assumes "obj a" and "obj b"
    shows "HOM a b \<in> Collect extensional_rts"
    proof -
      interpret HOM: sub_rts resid \<open>\<lambda>t. t \<in> H.hom a b\<close>
        using assms sub_rts_HOM by fastforce
      show ?thesis
        using HOM.preserves_extensional_rts V.extensional_rts_axioms by auto
    qed

    text\<open>
      Given an object \<open>a\<close> and an arrow \<open>t\<close>, horizontal composition with \<open>t\<close> determines
      a transformation \<open>HOM\<^sup>\<rightarrow> a t\<close> from \<open>HOM a (H.dom t)\<close> to \<open>HOM a (H.cod t)\<close>.
    \<close>

    abbreviation cov_HOM  (\<open>HOM\<^sup>\<rightarrow>\<close>)
    where "HOM\<^sup>\<rightarrow> a t \<equiv>
           (\<lambda>x. if residuation.arr (HOM a (dom t)) x then t \<star> x else null)"

    lemma simulation_cov_HOM_sta:
    assumes "obj a" and "sta f"
    shows "simulation (HOM a (dom f)) (HOM a (cod f)) (HOM\<^sup>\<rightarrow> a f)"
    proof -
      interpret HOM_a: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : a \<rightarrow> dom f\<guillemotright>\<close>
        using sub_rts_HOM by blast
      interpret HOM_b: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : a \<rightarrow> cod f\<guillemotright>\<close>
        using sub_rts_HOM by blast
      show "simulation HOM_a.resid HOM_b.resid (HOM\<^sup>\<rightarrow> a f)"
      proof
        show "\<And>x. \<not> HOM_a.arr x \<Longrightarrow> HOM\<^sup>\<rightarrow> a f x = HOM_b.null"
          using assms HOM_b.null_char by auto
        fix t u
        assume tu: "HOM_a.con t u"
        have 1: "\<guillemotleft>f \<star> t : a \<rightarrow> cod f\<guillemotright> \<and> \<guillemotleft>f \<star> u : a \<rightarrow> cod f\<guillemotright>"
        proof -
          have "f \<frown> f"
            using assms(2) by auto
          thus ?thesis
            using assms tu HOM_a.con_implies_arr HOM_a.con_char [of t u]
            by auto
        qed
        have 2: "\<guillemotleft>f \<star> t : a \<rightarrow> cod f\<guillemotright> \<and> \<guillemotleft>f \<star> u : a \<rightarrow> cod f\<guillemotright> \<and> f \<star> t \<frown> f \<star> u"
          using assms tu 1 HOM_a.con_char resid_hcomp(1) [of f f t u]
          by blast
        show "HOM_b.con (HOM\<^sup>\<rightarrow> a f t) (HOM\<^sup>\<rightarrow> a f u)"
          using assms(2) tu 2 HOM_a.con_implies_arr [of t u]
                HOM_a.con_char HOM_b.con_char
          by auto
        show "HOM\<^sup>\<rightarrow> a f (HOM_a.resid t u) =
              HOM_b.resid (HOM\<^sup>\<rightarrow> a f t) (HOM\<^sup>\<rightarrow> a f u)"
        proof -
          have "HOM_a.arr (t \\ u)"
            using tu HOM_a.con_char [of t u] HOM_a.arr_char [of "t \\ u"]
                  dom_resid [of t u] cod_resid [of t u]
            by fastforce
          moreover have "arr (f \<star> t)"
            using 2 by auto
          moreover have "f \<frown> f"
            using assms(2) by auto
          ultimately show ?thesis
            using assms(1-2) tu 1 2 HOM_b.resid_def HOM_a.resid_def
                  HOM_a.con_implies_arr HOM_a.con_char resid_hcomp(2)
            by auto
        qed
      qed
    qed

    lemma transformation_cov_HOM_arr:
    assumes "obj a" and "arr t"
    shows "transformation (HOM a (dom t)) (HOM a (cod t))
             (HOM\<^sup>\<rightarrow> a (src t)) (HOM\<^sup>\<rightarrow> a (trg t)) (HOM\<^sup>\<rightarrow> a t)"
    proof -
      interpret Dom': sub_rts resid \<open>\<lambda>x. x \<in> H.hom a (dom t)\<close>
        using assms sub_rts_HOM by auto
      interpret Dom': sub_rts_of_extensional_rts resid \<open>\<lambda>x. x \<in> H.hom a (dom t)\<close> ..
      interpret Cod': sub_rts resid \<open>\<lambda>x. x \<in> H.hom a (cod t)\<close>
        using assms  sub_rts_HOM by auto
      interpret Cod': sub_rts_of_extensional_rts resid \<open>\<lambda>x. x \<in> H.hom a (cod t)\<close> ..
      have Dom'_eq: "Dom'.resid = HOM a (dom t)"
        using assms Cod'.null_char by auto
      have Cod'_eq: "Cod'.resid = HOM a (cod t)"
        using assms Cod'.null_char by auto
      interpret Dom: extensional_rts \<open>HOM a (dom t)\<close>
        using Dom'_eq Dom'.extensional_rts_axioms by simp
      interpret Cod: extensional_rts \<open>HOM a (cod t)\<close>
        using Cod'_eq Cod'.extensional_rts_axioms by simp
      interpret Src: simulation
                       \<open>HOM a (dom t)\<close> \<open>HOM a (cod t)\<close> \<open>HOM\<^sup>\<rightarrow> a (src t)\<close>
        using assms simulation_cov_HOM_sta [of a "src t"] by auto
      interpret Trg: simulation
                       \<open>HOM a (H.dom t)\<close> \<open>HOM a (cod t)\<close> \<open>HOM\<^sup>\<rightarrow> a (trg t)\<close>
        using assms simulation_cov_HOM_sta [of a "trg t"] by auto
      show ?thesis
      proof
        show "\<And>f. \<not> Dom.arr f \<Longrightarrow> HOM\<^sup>\<rightarrow> a t f = Cod.null"
          using Dom'_eq Cod'_eq Cod'.null_char by simp
        fix f
        assume f: "Dom.ide f"
        have 1: "H.seq t f"
          using assms f Dom'.ide_char Dom'.arr_char
          by (intro H.seqI) auto
        have 2: "\<guillemotleft>t \<star> f : a \<rightarrow> cod t\<guillemotright>"
            using f 1 Dom'.ide_char Dom'.arr_char H.cod_comp
            by (intro H.in_homI) auto
        show "Cod.src (HOM\<^sup>\<rightarrow> a t f) = HOM\<^sup>\<rightarrow> a (src t) f"
          using f 1 2 Cod'.src_char Dom'.ide_char Cod'.arr_char by simp
        show "Cod.trg (HOM\<^sup>\<rightarrow> a t f) = HOM\<^sup>\<rightarrow> a (trg t) f"
          using f 1 2 Cod'.trg_char Dom'.ide_char Cod'.arr_char by simp
        next
        fix f
        assume f: "Dom.arr f"
        have arr_f: "arr f"
          using f Dom'.arr_char by auto
        have 3: "H.cod f = H.dom t"
          using f Dom'.arr_char by auto
        have 4: "Dom.src f = src f"
          using f Dom'_eq Dom'.src_char by auto
        have 5: "VV.con (t, Dom.src f) (src t, f)"
          unfolding VV.con_char
          using assms f 3 4 Dom'_eq Dom'.arr_char
          by (intro conjI) auto
        have 6: "VV.con (src t, f) (t, Dom.src f)"
          using assms arr_f 3 4 VV.con_char by auto
        have 7: "VV.resid (t, Dom.src f) (src t, f) = (t, trg f)"
          using f 5 VV.resid_def VV.con_char Dom'.src_char V.con_implies_arr
          by auto
        show "HOM a (cod t) (HOM\<^sup>\<rightarrow> a t (Dom.src f)) (HOM\<^sup>\<rightarrow> a (src t) f) =
              HOM\<^sup>\<rightarrow> a t (Dom.trg f)"
        proof -
          have "HOM a (cod t) (HOM\<^sup>\<rightarrow> a t (Dom.src f)) (HOM\<^sup>\<rightarrow> a (src t) f) =
                Cod'.resid (t \<star> src f) (src t \<star> f)"
            using f 4 Dom.arr_src_iff_arr [of f] by simp
          also have "... = (t \<star> src f) \\ (src t \<star> f)"
            using assms f 4 5 Cod'.resid_def Dom'_eq Dom'.arr_char H.preserves_con
                  VV.con_implies_arr
            by auto
          also have "... = t \\ src t \<star> src f \\ f"
            using assms f 4 5 7 VV.arr_char Dom'.arr_char
                  H.preserves_resid [of "(t, src f)" "(src t, f)"]
            by auto
          also have "... = HOM\<^sup>\<rightarrow> a t (Dom.trg f)"
            using assms f Dom'.arr_char Dom'.trg_char H.in_homI by auto
          finally show ?thesis by blast
        qed
        show "HOM a (cod t) (HOM\<^sup>\<rightarrow> a (src t) f) (HOM\<^sup>\<rightarrow> a t (Dom.src f)) =
              HOM\<^sup>\<rightarrow> a (trg t) f"
        proof -
          have "HOM a (cod t) (HOM\<^sup>\<rightarrow> a (src t) f) (HOM\<^sup>\<rightarrow> a t (Dom.src f)) =
                Cod'.resid (src t \<star> f) (t \<star> Dom.src f)"
            using f by simp
          also have "... = (src t \<star> f) \\ (t \<star> src f)"
            using assms f 4 Cod'.resid_def Dom'.arr_char by auto
          also have "... = src t \\ t \<star> f \\ src f"
            using assms f arr_f 4 6 VV.arr_char Dom'.arr_char VV.resid_def
                  H.preserves_resid [of "(src t, f)" "(t, src f)"]
            by auto
          also have "... = cov_HOM a (trg t) f"
            using assms f arr_f by simp
          finally show ?thesis by blast
        qed
        show "Cod.join_of (HOM\<^sup>\<rightarrow> a t (Dom.src f)) (HOM\<^sup>\<rightarrow> a (src t) f)
                (HOM\<^sup>\<rightarrow> a t f)"
        proof -
          have 8: "t \<star> src f \<squnion> src t \<star> f = t \<star> f"
            using assms f arr_f V.join_src V.join_sym V.joinable_iff_arr_join
                  join_hcomp Dom'.arr_char H.seqI
            by auto
          moreover have "\<guillemotleft>f : a \<rightarrow> dom t\<guillemotright>"
            using f Dom'.arr_char by auto
          moreover have "\<guillemotleft>src f : a \<rightarrow> dom t\<guillemotright>"
            using f Dom'.arr_char H.in_homI by auto
          moreover have "V.joinable (t \<star> src f) (src t \<star> f)"
          proof -
            have "t \<star> f \<in> H.hom a (cod t)"
              using assms f Dom'.arr_char by auto
            thus ?thesis
              using 8 V.joinable_iff_arr_join by auto
          qed
          ultimately show ?thesis
            using assms 4 Dom'.arr_char Cod'.join_of_char
                  V.join_is_join_of [of "t \<star> src f" "src t \<star> f"]
            by auto
        qed
      qed
    qed

    text\<open>
      For fixed \<open>a\<close>, the mapping \<open>HOM\<^sup>\<rightarrow> a\<close> takes horizontal composite of arrows
      to function composition.
    \<close>
    lemma cov_HOM_hcomp:
    assumes "obj a" and "H.seq t u"
    shows "HOM\<^sup>\<rightarrow> a (t \<star> u) = HOM\<^sup>\<rightarrow> a t \<circ> HOM\<^sup>\<rightarrow> a u"
    proof
      interpret au: transformation \<open>HOM a (dom u)\<close> \<open>HOM a (cod u)\<close>
                      \<open>HOM\<^sup>\<rightarrow> a (src u)\<close> \<open>HOM\<^sup>\<rightarrow> a (trg u)\<close> \<open>HOM\<^sup>\<rightarrow> a u\<close>
        using assms transformation_cov_HOM_arr [of a u] by fastforce
      interpret at: transformation \<open>HOM a (dom t)\<close> \<open>HOM a (cod t)\<close>
                      \<open>HOM\<^sup>\<rightarrow> a (src t)\<close> \<open>HOM\<^sup>\<rightarrow> a (trg t)\<close> \<open>HOM\<^sup>\<rightarrow> a t\<close>
        using assms transformation_cov_HOM_arr [of a t] by fastforce
      fix x
      have "(HOM\<^sup>\<rightarrow> a t \<circ> HOM\<^sup>\<rightarrow> a u) x =
            (if au.A.arr x then (t \<star> u) \<star> x else null)"
        using assms(2) H.comp_assoc au.preserves_arr H.seqE H.null_is_zero
        apply (cases "au.A.arr x")
         apply auto[2]
        by metis
      thus "HOM\<^sup>\<rightarrow> a (t \<star> u) x = (HOM\<^sup>\<rightarrow> a t \<circ> HOM\<^sup>\<rightarrow> a u) x"
        using assms(2) by auto
    qed

    text\<open>
      The mapping \<open>HOM\<^sup>\<rightarrow> a\<close> preserves consistency and residuation.
    \<close>

    lemma cov_HOM_resid:
    assumes "obj a" and "V.con t u"
    shows "cov_HOM a (t \\ u) =
           consistent_transformations.resid
             (HOM a (dom t)) (HOM a (cod t)) (HOM\<^sup>\<rightarrow> a (trg u))
             (HOM\<^sup>\<rightarrow> a t) (HOM\<^sup>\<rightarrow> a u)"
    proof -
      have 1: "HOM a (dom u) = HOM a (dom t)"
        using assms V.con_imp_eq_src dom_src by metis
      have 2: "HOM a (cod u) = HOM a (cod t)"
        using assms V.con_imp_eq_src cod_src by metis
      interpret A: sub_rts resid \<open>\<lambda>x. \<guillemotleft>x : a \<rightarrow> dom t\<guillemotright>\<close>
        using sub_rts_HOM by blast
      interpret A: extensional_rts A.resid
        using assms V.con_implies_arr extensional_rts_HOM by simp
      interpret B: sub_rts resid \<open>\<lambda>x. \<guillemotleft>x : a \<rightarrow> cod t\<guillemotright>\<close>
        using sub_rts_HOM by blast
      interpret B: extensional_rts B.resid
        using assms V.con_implies_arr extensional_rts_HOM by simp
      interpret at: transformation A.resid B.resid
                      \<open>HOM\<^sup>\<rightarrow> a (src t)\<close> \<open>HOM\<^sup>\<rightarrow> a (trg t)\<close> \<open>HOM\<^sup>\<rightarrow> a t\<close>
        using assms transformation_cov_HOM_arr [of a t] V.con_implies_arr
        by fastforce
      interpret au: transformation A.resid B.resid
                      \<open>HOM\<^sup>\<rightarrow> a (src t)\<close> \<open>HOM\<^sup>\<rightarrow> a (trg u)\<close> \<open>HOM\<^sup>\<rightarrow> a u\<close>
        using assms 1 2 V.con_imp_eq_src transformation_cov_HOM_arr [of a u]
              V.con_implies_arr
        by presburger
      interpret at_au: consistent_transformations A.resid B.resid
                         \<open>HOM\<^sup>\<rightarrow> a (src t)\<close> \<open>HOM\<^sup>\<rightarrow> a (trg t)\<close> \<open>HOM\<^sup>\<rightarrow> a (trg u)\<close>
                         \<open>HOM\<^sup>\<rightarrow> a t\<close> \<open>HOM\<^sup>\<rightarrow> a u\<close>
      proof
        show "\<And>x. A.ide x \<longrightarrow> HOM\<^sup>\<rightarrow> a t x \<frown>\<^sub>B HOM\<^sup>\<rightarrow> a u x"
        proof (intro impI)
          fix x
          assume x: "A.ide x"
          show "HOM\<^sup>\<rightarrow> a t x \<frown>\<^sub>B HOM\<^sup>\<rightarrow> a u x"
            using assms x resid_hcomp B.con_char B.arr_char at.preserves_arr
                  au.preserves_arr
            apply auto[1]
             apply (metis (no_types, lifting) B.inclusion V.arrE arr_coincidence
                A.ide_implies_arr H.seqE)
            by (metis (full_types) B.not_arr_null B.null_char A.ide_implies_arr
                rts_category.sub_rts_HOM)
        qed
      qed
      show "HOM\<^sup>\<rightarrow> a (t \\ u) = at_au.resid"
      proof (intro transformation_eqI)
        show "extensional_rts (HOM a (cod t))" ..
        show "transformation (HOM a (dom t)) B.resid 
                (cov_HOM a (trg u)) at_au.apex at_au.resid"
          using at_au.transformation_resid by blast
        show "transformation (HOM a (dom t)) B.resid
                (HOM\<^sup>\<rightarrow> a (trg u)) at_au.apex (HOM\<^sup>\<rightarrow> a (t \\ u))"
        proof -
          have "dom (t \\ u) = dom t"
            using assms dom_resid by blast
          moreover have "cod (t \\ u) = cod t"
            using assms cod_resid by blast
          moreover have "(\<lambda>x. if residuation.arr (HOM a (dom u)) x
                              then src (t \\ u) \<star> x else null) =
                         (\<lambda>x. if residuation.arr (HOM a (dom u)) x
                              then trg u \<star> x else null)"
            using assms by auto
          moreover have "(\<lambda>x. if A.arr x then trg (t \\ u) \<star> x else null) = at_au.apex"
          proof
            fix x
            show "(if A.arr x then trg (t \\ u) \<star> x else null) = at_au.apex x"
            proof (cases "A.arr x")
              case False
              show ?thesis
                using False B.null_char by auto
              next
              case True
              show ?thesis
              proof -
                have 3: "residuation.arr (HOM a (dom u)) (A.src x)"
                  using True 1 by auto
                have "\<guillemotleft>t \<star> A.src x : a \<rightarrow> cod t\<guillemotright>"
                  using True B.arr_char at.preserves_arr by force
                moreover have "\<guillemotleft>u \<star> A.src x : a \<rightarrow> cod t\<guillemotright>"
                  using True 1 A.arr_char A.arr_src_if_arr B.arr_char au.preserves_arr
                  by force
                moreover have "\<guillemotleft>trg u \<star> x : a \<rightarrow> cod t\<guillemotright>"
                  using assms True A.arr_char con_implies_hpar by fastforce
                moreover have 4: " \<guillemotleft>(t \<star> A.src x) \\ (u \<star> A.src x) : a \<rightarrow> cod t\<guillemotright>"
                  using 1 3 A.ide_iff_src_self A.src_src B.con_char B.resid_closed
                        at_au.con
                  by presburger
                moreover have "t \<star> A.src x \<frown> u \<star> A.src x"
                  using 4 B.inclusion V.arr_resid_iff_con by blast
                moreover have "trg (t \\ u) \<star> x =
                               (trg u \<star> x) \\ ((t \<star> A.src x) \\ (u \<star> A.src x))"
                proof -
                  have "(trg u \<star> x) \\ ((t \<star> A.src x) \\ (u \<star> A.src x)) =
                        (trg u \<star> x) \\ ((t \\ u) \<star> A.src x)"
                    by (metis (no_types, lifting) 1 3 A.con_arr_self A.con_char
                        A.trg_char A.trg_src H.arrI V.trg_def assms(2)
                        calculation(1) resid_hcomp(2))
                  also have "... = trg (t \\ u) \<star> x"
                  proof -
                    have "\<guillemotleft>trg u \<star> x : a \<rightarrow> cod t\<guillemotright>"
                      using assms True A.arr_char con_implies_hpar by fastforce
                    thus ?thesis
                      using assms True resid_hcomp [of "trg u" "t \\ u" x "A.src x"]
                      by (metis (no_types, lifting) A.con_arr_src(1) A.con_char
                          A.resid_arr_src A.resid_def H.arrI V.arr_resid V.con_def
                          V.con_imp_arr_resid V.resid_src_arr V.src_resid V.trg_def)
                  qed
                  finally show ?thesis by simp
                qed
                ultimately show ?thesis
                  using True 1 B.resid_def by auto
              qed
            qed
          qed
          ultimately show ?thesis
            using assms transformation_cov_HOM_arr [of a "t \\ u"] by auto
        qed
        show "\<And>x. A.ide x \<Longrightarrow> HOM\<^sup>\<rightarrow> a (t \\ u) x = at_au.resid x"
        proof -
          fix x
          assume x: "A.ide x"
          have "at_au.resid x = B.resid (HOM\<^sup>\<rightarrow> a t x) (HOM\<^sup>\<rightarrow> a u x)"
            using x at_au.resid_ide by blast
          also have "... = HOM\<^sup>\<rightarrow> a (t \\ u) x"
            using assms x 1 A.ide_char A.arr_char resid_hcomp [of t u x x]
                  B.resid_def
            apply clarsimp
            apply (intro conjI impI)
            subgoal by (metis B.inclusion V.ideE)
            subgoal using V.trg_def con_implies_hpar trg_dom by force
            subgoal using B.arr_char au.preserves_arr at.preserves_arr
              by auto (metis arr_coincidence category.in_homE 
                  rts_category_axioms rts_category_def)
            done
          finally show "HOM\<^sup>\<rightarrow> a (t \\ u) x = at_au.resid x" by simp
        qed
      qed
    qed

    text\<open>
      We can dualize the above, to define, given an object \<open>c\<close> and an arrow \<open>t\<close>,
      a contravariant mapping \<open>HOM\<^sup>\<leftarrow> c t\<close> from \<open>HOM (H.cod t) c\<close> to \<open>HOM (H.dom t) c\<close>.
      I have not carried out a full development parallel to the covariant case,
      because the contravariant version is not used in an essential way in this article.
    \<close>

    abbreviation cnt_HOM  (\<open>HOM\<^sup>\<leftarrow>\<close>)
    where "HOM\<^sup>\<leftarrow> c t \<equiv>
           (\<lambda>x. if residuation.arr (HOM (cod t) c) x then x \<star> t else null)"

    lemma simulation_cnt_HOM_sta:
    assumes "sta f" and "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "obj c"
    shows "simulation (HOM b c) (HOM a c) (HOM\<^sup>\<leftarrow> c f)"
    proof -
      interpret HOM_a: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : a \<rightarrow> c\<guillemotright>\<close>
        using sub_rts_HOM by blast
      interpret HOM_b: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : b \<rightarrow> c\<guillemotright>\<close>
        using sub_rts_HOM by blast
      show "simulation HOM_b.resid HOM_a.resid (HOM\<^sup>\<leftarrow> c f)"
      proof
        show "\<And>x. \<not> HOM_b.arr x \<Longrightarrow> HOM\<^sup>\<leftarrow> c f x = HOM_a.null"
          using assms(2) HOM_a.null_char by auto
        fix t u
        assume tu: "HOM_b.con t u"
        show "HOM_a.con (HOM\<^sup>\<leftarrow> c f t) (HOM\<^sup>\<leftarrow> c f u)"
        proof -
          have "f \<frown> f"
            using assms(1) by auto
          hence "\<guillemotleft>t \<star> f : a \<rightarrow> c\<guillemotright> \<and> \<guillemotleft>u \<star> f : a \<rightarrow> c\<guillemotright> \<and> t \<star> f \<frown> u \<star> f"
            using assms tu HOM_b.con_implies_arr HOM_b.con_char [of t u]
                  resid_hcomp(1) [of t u f f]
            by (intro conjI) blast+
          thus ?thesis
            using assms(2) tu HOM_b.con_implies_arr [of t u]
                  HOM_a.con_char HOM_b.con_char
            by auto
        qed
        show "HOM\<^sup>\<leftarrow> c f (HOM_b.resid t u) =
              HOM_a.resid (HOM\<^sup>\<leftarrow> c f t) (HOM\<^sup>\<leftarrow> c f u)"
        proof -
          have "HOM_b.arr (t \\ u)"
            using tu HOM_b.con_char [of t u] HOM_b.arr_char [of "t \\ u"]
                  dom_resid [of t u] cod_resid [of t u]
            by fastforce
          moreover have "arr (t \<star> f)"
            using assms(2) tu HOM_b.con_char HOM_b.con_implies_arr
            by blast
          moreover
          have "\<guillemotleft>t \<star> f : a \<rightarrow> c\<guillemotright> \<and> \<guillemotleft>u \<star> f : a \<rightarrow> c\<guillemotright> \<and> t \<star> f \<frown> u \<star> f"
            using assms tu HOM_b.con_char [of t u] resid_hcomp(1)
            by (intro conjI) blast+
          moreover have "f \<frown> f"
            using assms(2) by auto
          ultimately show ?thesis
            using assms(1-2) tu HOM_a.resid_def HOM_b.resid_def
                  HOM_b.con_implies_arr HOM_b.con_char resid_hcomp(2)
            by auto
        qed
      qed
    qed

    lemma HOM_preserves_isomorphic_left:
    assumes "H.isomorphic a b" and "obj c"
    shows "isomorphic_rts (HOM a c) (HOM b c)"
    proof -
      interpret HOM_a: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : a \<rightarrow> c\<guillemotright>\<close>
        using sub_rts_HOM by blast
      interpret HOM_b: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : b \<rightarrow> c\<guillemotright>\<close>
        using sub_rts_HOM by blast
      obtain f g where fg: "H.inverse_arrows f g \<and> dom f = a \<and> cod f = b"
        using assms(1) by blast
      have 1: "sta f \<and> sta g"
        using fg iso_implies_sta by blast
      have f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
        using fg H.inverse_arrows_def
        by (intro H.in_homI) auto
      have g: "\<guillemotleft>g : b \<rightarrow> a\<guillemotright>"
        using fg H.inverse_arrows_def
        by (intro H.in_homI) auto
      let ?F = "\<lambda>t. if HOM_b.arr t then t \<star> f else null"
      let ?G = "\<lambda>t. if HOM_a.arr t then t \<star> g else null"
      interpret F: simulation HOM_b.resid HOM_a.resid ?F
        using assms(2) f 1 simulation_cnt_HOM_sta by blast
      interpret G: simulation HOM_a.resid HOM_b.resid ?G
        using assms(2) g 1 simulation_cnt_HOM_sta by blast
      interpret FG: inverse_simulations HOM_a.resid HOM_b.resid ?F ?G
      proof
        show "?F \<circ> ?G = I HOM_a.resid"
        proof
          fix x
          show "(?F \<circ> ?G) x = I HOM_a.resid x"
            using G.preserves_reflects_arr H.comp_arr_dom H.comp_assoc
                  H.comp_inv_arr HOM_a.arr_char HOM_a.null_char fg
            by auto
        qed
        show "?G \<circ> ?F = I HOM_b.resid"
        proof
          fix x
          show "(?G \<circ> ?F) x = I HOM_b.resid x"
          proof (cases "HOM_b.arr x")
            show "\<not> HOM_b.arr x \<Longrightarrow> ?thesis"
              using HOM_b.null_char H.null_is_zero by auto
            assume x: "HOM_b.arr x"
            show ?thesis
            proof -
              have "obj (f \<star> g)"
                using fg by blast
              moreover have "arr (x \<star> f \<star> g)"
                using f g x HOM_b.arr_char by blast
              moreover have "\<guillemotleft>x \<star> f : dom f \<rightarrow> c\<guillemotright>"
                using f x HOM_b.arr_char H.dom_comp by blast
              ultimately show ?thesis
                using fg x H.comp_assoc H.comp_arr_ide HOM_a.arr_char
                by auto
            qed
          qed
        qed
      qed
      show ?thesis
        using FG.inverse_simulations_axioms isomorphic_rts_def by blast
    qed

  end

  subsection "Additional Notions"

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

  text\<open>
    An \emph{RTS-functor} is a mapping between RTS-categories that is functor with
    respect to the horizontal composition and a simulation with respect to the
    vertical residuation.  An \emph{RTS-category isomorphism} is an RTS-functor
    that is invertible as a simulation, from which it follows that it is also
    invertible as a functor.
  \<close>

  locale rts_functor =
    A: rts_category resid\<^sub>A comp\<^sub>A +
    B: rts_category resid\<^sub>B comp\<^sub>B +
    "functor" comp\<^sub>A comp\<^sub>B F +
    simulation resid\<^sub>A resid\<^sub>B F
  for resid\<^sub>A :: "'a resid"  (infix \<open>\\<^sub>A\<close> 70)
  and comp\<^sub>A :: "'a comp"    (infixr \<open>\<star>\<^sub>A\<close> 53)
  and resid\<^sub>B :: "'b resid"  (infix \<open>\\<^sub>B\<close> 70)
  and comp\<^sub>B :: "'b comp"    (infixr \<open>\<star>\<^sub>B\<close> 53)
  and F :: "'a \<Rightarrow> 'b"
  begin

    notation A.V.con  (infix \<open>\<frown>\<^sub>A\<close> 50)
    notation B.V.con  (infix \<open>\<frown>\<^sub>B\<close> 50)

    lemma is_invertible_simulation_if:
    assumes "invertible_functor comp\<^sub>A comp\<^sub>B F"
    and "\<And>t u. F t \<frown>\<^sub>B F u \<Longrightarrow> t \<frown>\<^sub>A u"
    shows "invertible_simulation resid\<^sub>A resid\<^sub>B F"
    proof -
      obtain G where G: "inverse_functors comp\<^sub>A comp\<^sub>B G F"
        using assms(1) invertible_functor.invertible by blast
      interpret FG: inverse_functors comp\<^sub>A comp\<^sub>B G F
        using G by blast
      interpret FG: inverse_simulations resid\<^sub>A resid\<^sub>B G F
      proof
        show "\<And>t. \<not> B.arr t \<Longrightarrow> G t = A.null"
          using FG.F.is_extensional by simp
        show inv: "F \<circ> G = I resid\<^sub>B" and inv': "G \<circ> F = I resid\<^sub>A"
          using FG.inv FG.inv' A.H.map_def B.H.map_def by auto
        fix t u
        assume tu: "t \<frown>\<^sub>B u"
        have "F (G t) \<frown>\<^sub>B F (G u)"
          using tu inv
          by (metis B.V.con_implies_arr(1-2) comp_apply)
        thus "G t \<frown>\<^sub>A G u"
          using assms(2) by blast
        show "G (t \\\<^sub>B u) = G t \\\<^sub>A G u"
          by (metis A.V.arr_resid B.V.con_implies_arr(1-2)
              \<open>G t \<frown>\<^sub>A G u\<close> comp_apply inv inv' preserves_resid tu)
      qed
      show ?thesis
        using invertible_simulation_def' FG.inverse_simulations_axioms by auto
    qed

    lemma is_invertible_if:
    assumes "invertible_simulation resid\<^sub>A resid\<^sub>B F"
    shows "invertible_functor comp\<^sub>A comp\<^sub>B F"
    proof -
      obtain G where G: "inverse_simulations resid\<^sub>A resid\<^sub>B G F"
        using assms(1) invertible_simulation_def' by blast
      interpret FG: inverse_simulations resid\<^sub>A resid\<^sub>B G F
        using G by blast
      interpret FG: inverse_functors comp\<^sub>A comp\<^sub>B G F
      proof
        show "\<And>f. \<not> B.H.arr f \<Longrightarrow> G f = A.H.null"
          using FG.F.extensional by auto
        show 1: "\<And>f. B.H.arr f \<Longrightarrow> A.H.arr (G f)"
          by auto
        show 2: "\<And>f. B.H.arr f \<Longrightarrow> A.H.dom (G f) = G (B.H.dom f)"
          by (metis 1 A.H.arr_dom_iff_arr A.arr_coincidence B.arr_coincidence
              FG.inv FG.inv' o_apply preserves_dom)
        show 3: "\<And>f. B.H.arr f \<Longrightarrow> A.H.cod (G f) = G (B.H.cod f)"
          by (metis 1 A.H.arr_cod_iff_arr A.arr_coincidence B.arr_coincidence
              FG.inv FG.inv' o_apply preserves_cod)
        show "F \<circ> G = B.H.map"
          using B.H.map_def FG.inv by auto
        show "G \<circ> F = A.H.map"
          using A.H.map_def FG.inv' by auto
        show "\<And>g f. B.H.seq g f \<Longrightarrow> G (g \<star>\<^sub>B f) = G g \<star>\<^sub>A G f"
          by (metis (full_types) 1 2 3 A.arr_coincidence B.H.seqE B.arr_coincidence
              FG.inv_simp FG.inv'_simp as_nat_trans.preserves_comp_2 A.H.seqI)
      qed
      show ?thesis
        using FG.inverse_functors_axioms
        by unfold_locales blast
    qed

  end

  locale rts_category_isomorphism =
    rts_functor +
    invertible_simulation resid\<^sub>A resid\<^sub>B F
  begin

    sublocale invertible_functor comp\<^sub>A comp\<^sub>B F
      using invertible_simulation_axioms is_invertible_if by simp

  end

end

