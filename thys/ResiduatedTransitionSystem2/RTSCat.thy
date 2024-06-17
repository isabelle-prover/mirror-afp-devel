(*  Title:       RTSCat
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "The Category of RTS's and Simulations"

text\<open>
  In this section, we show that the subcategory of \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close>, comprised of the arrows that are
  identities with respect to the residuation, is also cartesian closed.  In informal text,
  we will refer to this category as \<open>\<^bold>R\<^bold>T\<^bold>S\<close>.  In a later section, we will show that the entire
  structure of the RTS-category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> is already determined by the ordinary subcategory \<open>\<^bold>R\<^bold>T\<^bold>S\<close>.
\<close>

theory RTSCat
imports Main RTSCatx EnrichedCategoryBasics.CartesianClosedMonoidalCategory
begin

  locale rtscat =
    universe arr_type
  for arr_type :: "'A itself"
  begin

    sublocale One: one_arr_rts arr_type ..

    interpretation RTSx: rtscatx arr_type ..
    interpretation RTSx: elementary_category_with_binary_products
                          RTSx.hcomp RTSx.p\<^sub>0 RTSx.p\<^sub>1
      using RTSx.extends_to_elementary_category_with_binary_products by blast
    interpretation RTS\<^sub>S: subcategory RTSx.hcomp RTSx.sta
      using RTSx.dom.preserves_ide RTSx.cod.preserves_ide RTSx.sta_hcomp
            RTSx.arr_hcomp RTSx.H.seqI
      by unfold_locales auto

    type_synonym 'a arr = "'a rtscatx.arr"

    definition comp :: "'A arr comp"  (infixr "\<cdot>" 53)
    where "comp \<equiv> subcategory.comp RTSx.hcomp RTSx.sta"

    sublocale category comp
      unfolding comp_def
      using RTS\<^sub>S.is_category by blast

    notation in_hom           ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma ide_iff_RTS_obj:
    shows "ide a \<longleftrightarrow> RTSx.obj a"
      using RTSx.obj_is_sta RTS\<^sub>S.ideI\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.ide_char\<^sub>S\<^sub>b\<^sub>C comp_def by auto

    lemma arr_iff_RTS_sta:
    shows "arr f \<longleftrightarrow> RTSx.sta f"
      by (simp add: RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C comp_def)

    text\<open>
      We want @{locale rtscat} to stand on its own, so here we embark on an
      extended development designed to bootstrap away from dependence on the
      supporting locale @{locale rtscatx}.
    \<close>

    abbreviation Obj
    where "Obj A \<equiv> extensional_rts A \<and> small_rts A"

    definition mkide :: "'A resid \<Rightarrow> 'A arr"
    where "mkide \<equiv> RTSx.mkobj"

    definition mkarr :: "'A resid \<Rightarrow> 'A resid \<Rightarrow> ('A \<Rightarrow> 'A) \<Rightarrow> 'A arr"
    where "mkarr \<equiv> RTSx.mksta"

    definition Rts :: "'A arr \<Rightarrow> 'A resid"
    where "Rts \<equiv> RTSx.Dom"

    abbreviation Dom :: "'A arr \<Rightarrow> 'A resid"
    where "Dom t \<equiv> Rts (dom t)"

    abbreviation Cod :: "'A arr \<Rightarrow> 'A resid"
    where "Cod t \<equiv> Rts (cod t)"

    definition Map :: "'A arr \<Rightarrow> 'A \<Rightarrow> 'A"
    where "Map \<equiv> RTSx.Map"

    lemma ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C [intro, simp]:
    assumes "ide a"
    shows "Obj (Rts a)"
      using assms Rts_def RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C ideD(1) comp_def by auto

    lemma ide_mkide [intro, simp]:
    assumes "Obj A"
    shows "ide (mkide A)"
      using assms comp_def mkide_def RTSx.obj_implies_sta RTSx.obj_mkobj
            RTS\<^sub>S.ideI\<^sub>S\<^sub>b\<^sub>C
      by simp

    lemma Rts_mkide [simp]:
    shows "Rts (mkide A) = A"
      by (simp add: Rts_def mkide_def)

    lemma mkide_Rts [simp]:
    assumes "ide a"
    shows "mkide (Rts a) = a"
      using assms RTSx.bij_mkobj(4) Rts_def ide_iff_RTS_obj mkide_def
      by force

    lemma Dom_mkide [simp]:
    assumes "ide (mkide A)"
    shows "Dom (mkide A) = A"
      using assms by force

    lemma Cod_mkide [simp]:
    assumes "ide (mkide A)"
    shows "Cod (mkide A) = A"
      using assms by force

    lemma Map_mkide [simp]:
    assumes "ide (mkide A)"
    shows "Map (mkide A) = I A"
      using assms mkide_def RTSx.mkobj_def Map_def RTSx.bij_mksta(3)
            RTSx.mkarr_def Rts_def ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C
      by fastforce

    lemma bij_mkide:
    shows "mkide \<in> Collect Obj \<rightarrow> Collect ide"
    and "Rts \<in> Collect ide \<rightarrow> Collect Obj"
    and "Rts (mkide A) = A"
    and "ide a \<Longrightarrow> mkide (Rts a) = a"
    and "bij_betw mkide (Collect Obj) (Collect ide)"
    and "bij_betw Rts (Collect ide) (Collect Obj)"
    proof -
      show "mkide \<in> Collect Obj \<rightarrow> Collect ide" by simp
      show "Rts \<in> Collect ide \<rightarrow> Collect Obj" by simp
      show "Rts (mkide A) = A" by simp
      show "ide a \<Longrightarrow> mkide (Rts a) = a" by simp
      show "bij_betw mkide (Collect Obj) (Collect ide)"
        unfolding bij_betw_def
        apply auto[1]
         apply (metis RTSx.mkobj_simps(1) inj_on_inverseI mkide_def)
        by (metis (no_types, lifting) CollectI ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C image_eqI mkide_Rts)
      show "bij_betw Rts (Collect ide) (Collect Obj)"
        unfolding bij_betw_def
        apply auto[1]
         apply (metis CollectD inj_onI mkide_Rts)
        using image_iff by fastforce
    qed

    lemma arrD:
    assumes "arr f"
    shows "Obj (Rts (dom f))" and "Obj (Rts (cod f))"
    and "simulation (Rts (dom f)) (Rts (cod f)) (Map f)"
    proof -
      interpret A: extensional_rts \<open>Rts (dom f)\<close>
        by (simp add: assms)
      interpret A: small_rts \<open>Rts (dom f)\<close>
        by (simp add: assms)
      interpret B: extensional_rts \<open>Rts (cod f)\<close>
        by (simp add: assms)
      interpret B: small_rts \<open>Rts (cod f)\<close>
        by (simp add: assms)
      interpret AB: exponential_rts \<open>Rts (dom f)\<close> \<open>Rts (cod f)\<close> ..
      have 1: "mkarr (Rts (dom f)) (Rts (cod f)) (Map f) = f"
        using assms comp_def mkarr_def Rts_def RTSx.mkarr_def
        by (metis (no_types, lifting) Map_def RTSx.Dom_cod RTSx.Dom_dom
            RTSx.Map_simps(4) RTSx.V.ide_implies_arr RTSx.V.trg_ide
            RTSx.trg_simp RTS\<^sub>S.cod_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.dom_char\<^sub>S\<^sub>b\<^sub>C arr_iff_RTS_sta)
      show "Obj (Rts (dom f))"
        using A.extensional_rts_axioms A.small_rts_axioms by simp
      show "Obj (Rts (cod f))"
        using B.extensional_rts_axioms B.small_rts_axioms by simp
      show "simulation (Rts (dom f)) (Rts (cod f)) (Map f)"
        using assms 1 RTSx.sta_char RTSx.simulation_Map_sta
              RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.cod_simp RTS\<^sub>S.dom_simp comp_def
        by (simp add: Map_def Rts_def)
    qed

    lemma arr_mkarr [intro, simp]:
    assumes "Obj A" and "Obj B" and "simulation A B F"
    shows "arr (mkarr A B F)"
      unfolding mkarr_def comp_def
      using assms RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C by blast

    lemma arrI\<^sub>R\<^sub>T\<^sub>S\<^sub>C:
    assumes "f \<in> mkarr A B ` Collect (simulation A B)"
    and "Obj A" and "Obj B"
    shows "arr f"
      using assms arr_mkarr by blast

    lemma Dom_mkarr [simp]:
    assumes "arr (mkarr A B F)"
    shows "Dom (mkarr A B F) = A"
      using assms
      by (simp add: RTS\<^sub>S.arrE RTS\<^sub>S.dom_simp Rts_def comp_def mkarr_def)

    lemma Cod_mkarr [simp]:
    assumes "arr (mkarr A B F)"
    shows "Cod (mkarr A B F) = B"
      using assms
      by (simp add: RTS\<^sub>S.arrE RTS\<^sub>S.cod_simp Rts_def comp_def mkarr_def)

    lemma Map_mkarr [simp]:
    assumes "arr (mkarr A B F)"
    shows "Map (mkarr A B F) = F"
      using assms mkarr_def RTSx.mkarr_def
      by (metis Cod_mkarr Dom_mkarr Map_def RTSx.bij_mksta(3) arrD(1-2))

    lemma mkarr_Map [simp]:
    assumes "Obj A" and "Obj B" and "t \<in> {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>}"
    shows "mkarr A B (Map t) = t"
      using assms mkarr_def Map_def comp_def mkide_def
      by (metis (no_types, lifting) RTS\<^sub>S.arrE RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C
          RTSx.bij_mksta(4) mem_Collect_eq)

    lemma dom_mkarr [simp]:
    assumes "arr (mkarr A B F)"
    shows "dom (mkarr A B F) = mkide A"
      using assms
      by (metis Dom_mkarr ide_dom mkide_Rts)

    lemma cod_mkarr [simp]:
    assumes "arr (mkarr A B F)"
    shows "cod (mkarr A B F) = mkide B"
      using assms
      by (metis Cod_mkarr ide_cod mkide_Rts)

    lemma mkarr_in_hom [intro]:
    assumes "simulation A B F" and "Rts a = A" and "Rts b = B"
    and "ide a" and "ide b"
    shows "\<guillemotleft>mkarr A B F : a \<rightarrow> b\<guillemotright>"
      using assms by auto

    lemma bij_mkarr:
    assumes "Obj A" and "Obj B"
    shows "mkarr A B \<in> Collect (simulation A B)
                          \<rightarrow> {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>}"
    and "Map \<in> {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>} \<rightarrow> Collect (simulation A B)"
    and "Map (mkarr A B F) = F"
    and "t \<in> {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>} \<Longrightarrow> mkarr A B (Map t) = t"
    and "bij_betw (mkarr A B) (Collect (simulation A B))
           {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>}"
    and "bij_betw Map {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>}
           (Collect (simulation A B))"
    proof -
      show 1: "mkarr A B \<in> Collect (simulation A B) \<rightarrow> hom (mkide A) (mkide B)"
        by (simp add: assms in_homI)
      show 2: "Map \<in> {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>} \<rightarrow> Collect (simulation A B)"
        using arrD(3) by fastforce
      show 3: "Map (mkarr A B F) = F"
        using assms
        by (metis Map_def RTSx.bij_mksta(3) mkarr_def)
      show 4: "t \<in> {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>} \<Longrightarrow> mkarr A B (Map t) = t"
        using assms by auto
      show "bij_betw (mkarr A B) (Collect (simulation A B))
              {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>}"
        using assms 1 2 3 4 by (intro bij_betwI) auto
      show "bij_betw Map {t. \<guillemotleft>t : mkide A \<rightarrow> mkide B\<guillemotright>} (Collect (simulation A B))"
        using assms 1 2 3 4 by (intro bij_betwI) auto
    qed

    lemma arr_eqI:
    assumes "par f g" and "Map f = Map g"
    shows "f = g"
    proof (intro RTSx.arr_eqI)
      show "f \<noteq> RTSx.Null"
        using assms RTS\<^sub>S.null_char RTSx.null_char not_arr_null comp_def by force
      show "g \<noteq> RTSx.Null"
        using assms RTS\<^sub>S.null_char RTSx.null_char not_arr_null comp_def by force
      show 1: "RTSx.Dom f = RTSx.Dom g"
        using assms comp_def
        by (metis RTSx.Dom_dom RTSx.V.ide_implies_arr RTS\<^sub>S.arrE RTS\<^sub>S.dom_simp)
      show 2: "RTSx.Cod f = RTSx.Cod g"
        using assms comp_def
        by (metis RTSx.Dom_cod RTSx.V.ide_implies_arr RTS\<^sub>S.arrE RTS\<^sub>S.cod_char\<^sub>S\<^sub>b\<^sub>C)
      interpret A: extensional_rts \<open>RTSx.Dom f\<close>
        using assms RTS\<^sub>S.arrE comp_def by auto
      interpret B: extensional_rts \<open>RTSx.Cod f\<close>
        using assms RTS\<^sub>S.arrE comp_def by auto
      interpret AB: exponential_rts \<open>RTSx.Dom f\<close> \<open>RTSx.Cod f\<close> ..
      show "RTSx.Trn f = RTSx.Trn g"
        using assms 1 2 comp_def Map_def
        by (metis (no_types, lifting) AB.ide_implies_arr RTSx.Map_simps(4)
            RTSx.V.trg_ide RTSx.arr_char RTSx.sta_char RTSx.trg_simp
            RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C)
    qed

    lemma Map_ide:
    assumes "ide a"
    shows "Map a = I (Rts a)"
      using assms Map_mkide [of "Rts a"] by simp

    lemma Map_comp:
    assumes "seq g f"
    shows "Map (g \<cdot> f) = Map g \<circ> Map f"
      using assms Map_def comp_def RTSx.Map_hcomp RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.comp_def
      by auto

    lemma comp_mkarr:
    assumes "arr (mkarr A B F)" and "arr (mkarr B C G)"
    shows "mkarr B C G \<cdot> mkarr A B F = mkarr A C (G \<circ> F)"
    proof (intro arr_eqI)
      have 1: "arr (mkarr A C (G \<circ> F))"
        using assms arrD simulation_comp bij_mkarr(3) Cod_mkarr Dom_mkarr
              arr_mkarr
        by metis
      show "par (mkarr B C G \<cdot> mkarr A B F) (mkarr A C (G \<circ> F))"
        using assms 1 by auto
      show "Map (mkarr B C G \<cdot> mkarr A B F) = Map (mkarr A C (G \<circ> F))"
        using assms 1 Map_comp Map_mkarr by auto
    qed

    lemma iso_char:
    shows "iso t \<longleftrightarrow> arr t \<and> invertible_simulation (Dom t) (Cod t) (Map t)"
      using Map_def comp_def Rts_def RTSx.iso_char RTSx.iso_implies_sta
      by (metis (no_types, lifting) RTSx.Dom_cod RTSx.Dom_dom
          RTSx.H.iso_inv_iso RTSx.Map_simps(3-4)
          RTSx.V.ide_iff_src_self RTSx.V.ide_implies_arr RTSx.V.trg_ide
          RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.cod_simp RTS\<^sub>S.dom_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.iso_char\<^sub>S\<^sub>b\<^sub>C)

    lemma isomorphic_char:
    shows "isomorphic a b \<longleftrightarrow>
           ide a \<and> ide b \<and> (\<exists>F. invertible_simulation (Rts a) (Rts b) F)"
    proof
      show "isomorphic a b \<Longrightarrow>
              ide a \<and> ide b \<and> (\<exists>F. invertible_simulation (Rts a) (Rts b) F)"
        by (metis (no_types, lifting) ide_cod ide_dom in_homE iso_char
            isomorphicE)
      show "ide a \<and> ide b \<and> (\<exists>F. invertible_simulation (Rts a) (Rts b) F)
               \<Longrightarrow> isomorphic a b"
        by (metis arr_mkarr cod_mkarr dom_mkarr ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C isomorphic_def
            iso_char invertible_simulation.axioms(1) mkarr_in_hom mkide_Rts
            Map_mkarr)
    qed

    subsection "Terminal Object"

    definition one          ("\<^bold>\<one>")
    where "one \<equiv> RTSx.one"
    no_notation RTSx.one     ("\<^bold>\<one>")

    definition trm
    where "trm \<equiv> RTSx.trm"

    lemma Rts_one [simp]:
    shows "Rts \<^bold>\<one> = One.resid"
      unfolding one_def Rts_def RTSx.one_def by simp

    lemma mkide_One [simp]:
    shows "mkide One.resid = \<^bold>\<one>"
      unfolding one_def mkide_def RTSx.one_def by simp

    sublocale elementary_category_with_terminal_object comp one trm
    proof
      show "ide \<^bold>\<one>"
        unfolding one_def
        using RTSx.obj_one RTSx.obj_is_sta RTS\<^sub>S.ideI\<^sub>S\<^sub>b\<^sub>C comp_def by force
      show "\<And>a. ide a \<Longrightarrow> \<guillemotleft>trm a : a \<rightarrow> \<^bold>\<one>\<guillemotright>"
        using RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.ide_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C comp_def
        by (metis (no_types, lifting) RTSx.trm_in_hom RTSx.trm_simps'(6)
            \<open>ide \<^bold>\<one>\<close> one_def trm_def)
      show "\<And>a f. \<lbrakk>ide a; \<guillemotleft>f : a \<rightarrow> \<^bold>\<one>\<guillemotright>\<rbrakk> \<Longrightarrow> f = trm a"
        by (metis RTSx.trm_eqI RTS\<^sub>S.ide_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C comp_def
            one_def trm_def)
    qed

    lemma Map_trm:
    assumes "ide a"
    shows "Map (trm a) = constant_simulation.map (Rts a) One.resid One.the_arr"
      unfolding Map_def trm_def Rts_def
      using assms RTSx.Map_trm RTS\<^sub>S.ide_char\<^sub>S\<^sub>b\<^sub>C comp_def by fastforce

    lemma terminal_char:
    shows "terminal x \<longleftrightarrow> ide x \<and> (\<exists>!t. residuation.arr (Rts x) t)"
    proof -
      have "\<And>x. terminal x \<longleftrightarrow> RTSx.H.terminal x"
      proof -
        fix x
        have 1: "terminal x \<longleftrightarrow> isomorphic x one"
          using terminal_one terminal_objs_isomorphic
          by (meson isomorphic_symmetric isomorphic_to_terminal_is_terminal)
        also have "... \<longleftrightarrow> RTSx.obj x \<and> isomorphic_rts (RTSx.Dom x) One.resid"
          using Rts_one ide_one isomorphic_char Rts_def ide_iff_RTS_obj
                isomorphic_rts_def [of "Rts x" One.resid]
                invertible_simulation_def' [of "Rts x" "Rts \<^bold>\<one>"]
          by auto
        also have "... \<longleftrightarrow> RTSx.H.terminal x"
          by (metis (mono_tags, lifting) 1 RTS\<^sub>S.arrI\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C
              RTS\<^sub>S.iso_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.isomorphic_def RTSx.H.iso_inv_iso
              RTSx.H.isomorphic_def RTSx.H.isomorphic_symmetric
              RTSx.H.isomorphic_to_terminal_is_terminal RTSx.H.terminal_def
              RTSx.iso_implies_sta RTSx.obj_implies_sta RTSx.terminal_one
              calculation comp_def one_def RTSx.H.terminal_objs_isomorphic)
        finally show "terminal x \<longleftrightarrow> RTSx.H.terminal x" by blast
      qed
      thus ?thesis
        using RTSx.terminal_char Rts_def ide_iff_RTS_obj by presburger
    qed

    subsection "Products"

    definition p\<^sub>0 :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr"
    where "p\<^sub>0 \<equiv> RTSx.p\<^sub>0"

    definition p\<^sub>1 :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr"
    where "p\<^sub>1 \<equiv> RTSx.p\<^sub>1"

    no_notation RTSx.p\<^sub>0  ("\<pp>\<^sub>0[_, _]")
    no_notation RTSx.p\<^sub>1  ("\<pp>\<^sub>1[_, _]")
    notation p\<^sub>0  ("\<pp>\<^sub>0[_, _]")
    notation p\<^sub>1  ("\<pp>\<^sub>1[_, _]")

    sublocale elementary_cartesian_category comp p\<^sub>0 p\<^sub>1 one trm
    proof
      fix a b
      assume a: "ide a" and b: "ide b"
      show 1: "span \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]"
        using a b RTSx.sta_p\<^sub>0 RTSx.sta_p\<^sub>1 RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.dom_simp
              RTS\<^sub>S.ide_char\<^sub>S\<^sub>b\<^sub>C
        by (simp add: comp_def p\<^sub>0_def p\<^sub>1_def)
      show "cod \<pp>\<^sub>0[a, b] = b"
        using a b 1 RTS\<^sub>S.cod_simp RTSx.cod_pr0 ide_iff_RTS_obj comp_def
              p\<^sub>0_def
        by metis
      show "cod \<pp>\<^sub>1[a, b] = a"
        using a b 1 RTS\<^sub>S.cod_simp RTSx.cod_pr1 ide_iff_RTS_obj comp_def
              p\<^sub>1_def
        by metis
      next
      fix f g
      assume fg: "span f g"
      have a: "ide (cod f)" and b: "ide (cod g)"
        using fg by auto
      have 1: "RTSx.H.span f g"
        using fg RTS\<^sub>S.arrE RTS\<^sub>S.dom_simp comp_def by force
      have 2: "RTSx.cod f = cod f \<and> RTSx.cod g = cod g"
        using fg by (simp add: RTS\<^sub>S.cod_char\<^sub>S\<^sub>b\<^sub>C comp_def)
      show "\<exists>!l. \<pp>\<^sub>1[cod f, cod g] \<cdot> l = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> l = g"
      proof -
        have "\<exists>l. \<pp>\<^sub>1[cod f, cod g] \<cdot> l = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> l = g"
        proof -
          let ?l = "RTSx.tuple f g"
          have "\<pp>\<^sub>1[cod f, cod g] \<cdot> ?l = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> ?l = g"
            using a b fg 1 2 RTSx.sta_p\<^sub>0 RTSx.sta_p\<^sub>1 arr_iff_RTS_sta
                  ide_iff_RTS_obj
            by (simp add: comp_def RTS\<^sub>S.comp_def p\<^sub>0_def p\<^sub>1_def)
          thus "\<exists>l. \<pp>\<^sub>1[cod f, cod g] \<cdot> l = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> l = g"
            by blast
        qed
        moreover
        have "\<And>l l'. \<lbrakk>\<pp>\<^sub>1[cod f, cod g] \<cdot> l = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> l = g;
                      \<pp>\<^sub>1[cod f, cod g] \<cdot> l' = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> l' = g\<rbrakk>
                         \<Longrightarrow> l' = l"
          by (metis (no_types, lifting) 1 RTSx.tuple_eqI RTS\<^sub>S.comp_simp
              a b fg ide_iff_RTS_obj comp_def p\<^sub>0_def p\<^sub>1_def)
        ultimately show ?thesis by blast
      qed
    qed

    notation prod   (infixr "\<otimes>" 51)
    notation tuple  ("\<langle>_, _\<rangle>")
    notation dup    ("\<d>[_]")
    notation assoc  ("\<a>[_, _, _]")
    notation assoc' ("\<a>\<^sup>-\<^sup>1[_, _, _]")
    notation lunit  ("\<l>[_]")
    notation lunit' ("\<l>\<^sup>-\<^sup>1[_]")
    notation runit  ("\<r>[_]")
    notation runit' ("\<r>\<^sup>-\<^sup>1[_]")

    lemma tuple_char:
    shows "tuple = (\<lambda>f g. if span f g then RTSx.tuple f g else null)"
    proof -
      have "\<And>f g. \<langle>f, g\<rangle> = (if span f g then RTSx.tuple f g else null)"
      proof -
        fix f g
        show "\<langle>f, g\<rangle> = (if span f g then RTSx.tuple f g else null)"
        proof (cases "span f g")
          case True
          have "RTSx.tuple f g = \<langle>f, g\<rangle>"
            by (metis (no_types, lifting) RTSx.tuple_pr_arr RTS\<^sub>S.comp_simp
                RTS\<^sub>S.seq_char\<^sub>S\<^sub>b\<^sub>C True ide_cod ide_iff_RTS_obj comp_def
                p\<^sub>0_def p\<^sub>1_def tuple_eqI universal)
          thus "\<langle>f, g\<rangle> = (if span f g then RTSx.tuple f g else null)"
            using True by auto
          next
          case False
          show "\<langle>f, g\<rangle> = (if span f g then RTSx.tuple f g else null)"
            using False tuple_ext by auto
        qed
      qed
      thus ?thesis by blast
    qed

    lemma prod_char:
    shows "(\<otimes>) = (\<lambda>f g. if arr f \<and> arr g then RTSx.prod f g else null)"
    proof -
      have "\<And>f g. f \<otimes> g = (if arr f \<and> arr g then RTSx.prod f g else null)"
      proof -
        fix f g
        have "\<not> arr f \<Longrightarrow> f \<otimes> g = (if arr f \<and> arr g then RTSx.prod f g else null)"
          using prod_def tuple_def by auto
        moreover
        have "\<not> arr g \<Longrightarrow> f \<otimes> g = (if arr f \<and> arr g then RTSx.prod f g else null)"
          using prod_def tuple_def by auto
        moreover have "\<lbrakk>arr f; arr g\<rbrakk>
                          \<Longrightarrow> f \<otimes> g = (if arr f \<and> arr g then RTSx.prod f g else null)"
        proof -
          assume f: "arr f" and g: "arr g"
          have "f \<otimes> g = \<langle>f \<cdot> \<pp>\<^sub>1[dom f, dom g], g \<cdot> \<pp>\<^sub>0[dom f, dom g]\<rangle>"
            unfolding prod_def by simp
          also have "... = \<langle>f \<cdot> \<pp>\<^sub>1[RTSx.dom f, RTSx.dom g],
                            g \<cdot> \<pp>\<^sub>0[RTSx.dom f, RTSx.dom g]\<rangle>"
            using f g RTS\<^sub>S.dom_char\<^sub>S\<^sub>b\<^sub>C comp_def by force
          also have "... = \<langle>RTSx.hcomp f \<pp>\<^sub>1[RTSx.dom f, RTSx.dom g],
                            RTSx.hcomp g \<pp>\<^sub>0[RTSx.dom f, RTSx.dom g]\<rangle>"
            using f g RTS\<^sub>S.comp_char RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C
            by (metis (no_types, lifting) RTS\<^sub>S.null_char calculation
                comp_def not_arr_null prod_simps(1) tuple_ext)
          also have "... = RTSx.tuple
                             (RTSx.hcomp f \<pp>\<^sub>1[RTSx.dom f, RTSx.dom g])
                             (RTSx.hcomp g \<pp>\<^sub>0[RTSx.dom f, RTSx.dom g])"
            by (metis (no_types, lifting) calculation f g not_arr_null
                prod_simps(1) tuple_char)
          also have "... = RTSx.prod f g"
            using RTSx.prod_def by (simp add: p\<^sub>0_def p\<^sub>1_def)
          finally show ?thesis
            using f g by auto
        qed
        ultimately show "f \<otimes> g = (if arr f \<and> arr g then RTSx.prod f g else null)"
          by blast
      qed
      thus ?thesis by blast
    qed

    definition Pack :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A \<times> 'A \<Rightarrow> 'A"
    where "Pack \<equiv> RTSx.Pack"

    definition Unpack :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A \<Rightarrow> 'A \<times> 'A"
    where "Unpack \<equiv> RTSx.Unpack"

    lemma inverse_simulations_Pack_Unpack:
    assumes "ide a" and "ide b"
    shows "inverse_simulations (Rts (a \<otimes> b)) (product_rts.resid (Rts a) (Rts b))
             (Pack a b) (Unpack a b)"
      using Pack_def RTSx.inverse_simulations_Pack_Unpack Rts_def Unpack_def
            assms(1-2) ide_iff_RTS_obj prod_char
      by force

    lemma simulation_Pack:
    assumes "ide a" and "ide b"
    shows "simulation
             (product_rts.resid (Rts a) (Rts b)) (Rts (a \<otimes> b)) (Pack a b)"
      using assms inverse_simulations_Pack_Unpack inverse_simulations_def
      by fast

    lemma simulation_Unpack:
    assumes "ide a" and "ide b"
    shows "simulation
             (Rts (a \<otimes> b)) (product_rts.resid (Rts a) (Rts b)) (Unpack a b)"
      using assms inverse_simulations_Pack_Unpack inverse_simulations_def
      by fast

    lemma Pack_o_Unpack:
    assumes "ide a" and "ide b"
    shows "Pack a b \<circ> Unpack a b = I (Rts (a \<otimes> b))"
      unfolding Pack_def Unpack_def Rts_def
      using assms RTSx.Pack_o_Unpack ide_iff_RTS_obj prod_char by auto

    lemma Unpack_o_Pack:
    assumes "ide a" and "ide b"
    shows "Unpack a b \<circ> Pack a b = I (product_rts.resid (Rts a) (Rts b))"
      unfolding Pack_def Unpack_def Rts_def
      using assms RTSx.Unpack_o_Pack ide_iff_RTS_obj prod_char by auto

    lemma Pack_Unpack [simp]:
    assumes "ide a" and "ide b"
    and "residuation.arr (Rts (a \<otimes> b)) t"
    shows "Pack a b (Unpack a b t) = t"
      using assms by (metis Pack_o_Unpack comp_apply)

    lemma Unpack_Pack [simp]:
    assumes "ide a" and "ide b"
    and "residuation.arr (product_rts.resid (Rts a) (Rts b)) t"
    shows "Unpack a b (Pack a b t) = t"
      using assms by (metis Unpack_o_Pack comp_apply)

    lemma Map_p\<^sub>0:
    assumes "ide a" and "ide b"
    shows "Map \<pp>\<^sub>0[a, b] = product_rts.P\<^sub>0 (Rts a) (Rts b) \<circ> Unpack a b"
      unfolding Map_def p\<^sub>0_def Unpack_def
      using assms RTSx.Map_p\<^sub>0 Rts_def ide_iff_RTS_obj by auto

    lemma Map_p\<^sub>1:
    assumes "ide a" and "ide b"
    shows "Map \<pp>\<^sub>1[a, b] = product_rts.P\<^sub>1 (Rts a) (Rts b) \<circ> Unpack a b"
      unfolding Map_def p\<^sub>1_def Unpack_def
      using assms RTSx.Map_p\<^sub>1 Rts_def ide_iff_RTS_obj by auto

    lemma Map_tuple:
    assumes "\<guillemotleft>f : x \<rightarrow> a\<guillemotright>" and "\<guillemotleft>g : x \<rightarrow> b\<guillemotright>"
    shows "Map \<langle>f, g\<rangle> = Pack a b \<circ> \<langle>\<langle>Map f, Map g\<rangle>\<rangle>"
      unfolding Map_def Pack_def comp_def
      using assms RTSx.Map_tuple
      by (metis (no_types, lifting) RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C in_homE comp_def
          tuple_char)

    corollary Map_dup:
    assumes "ide a"
    shows "Map \<d>[a] = Pack a a \<circ> \<langle>\<langle>Map a, Map a\<rangle>\<rangle>"
      using assms Map_tuple ide_in_hom by blast

    proposition Map_lunit:
    assumes "ide a"
    shows "Map \<l>[a] = product_rts.P\<^sub>0 (Rts \<^bold>\<one>) (Rts a) \<circ> Unpack \<^bold>\<one> a"
      using assms Map_p\<^sub>0 ide_one by auto

    proposition Map_runit:
    assumes "ide a"
    shows "Map \<r>[a] = product_rts.P\<^sub>1 (Rts a) (Rts \<^bold>\<one>) \<circ> Unpack a \<^bold>\<one>"
      using assms Map_p\<^sub>1 ide_one by auto

    lemma assoc_expansion:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<a>[a, b, c] =
           \<langle>\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle> \<rangle>"
      using assms RTSx.assoc_expansion assoc_def p\<^sub>0_def p\<^sub>1_def by simp

    lemma Unpack_naturality:
    assumes "arr f" and "arr g"
    shows "Unpack (cod f) (cod g) \<circ> Map (f \<otimes> g) =
           product_simulation.map (Rts (dom f)) (Rts (dom g)) (Map f) (Map g) \<circ>
             Unpack (dom f) (dom g)"
    proof -
      interpret Dom_f: extensional_rts \<open>Rts (dom f)\<close>
        by (simp add: assms(1))
      interpret Dom_g: extensional_rts \<open>Rts (dom g)\<close>
        by (simp add: assms(2))
      interpret Cod_f: extensional_rts \<open>Rts (cod f)\<close>
        by (simp add: assms(1))
      interpret Cod_g: extensional_rts \<open>Rts (cod g)\<close>
        by (simp add: assms(2))
      interpret Dom: product_rts \<open>Rts (dom f)\<close> \<open>Rts (dom g)\<close> ..
      interpret Cod: product_rts \<open>Rts (cod f)\<close> \<open>Rts (cod g)\<close> ..
      interpret Dom: extensional_rts Dom.resid
        using Dom.preserves_extensional_rts Dom_f.extensional_rts_axioms
              Dom_g.extensional_rts_axioms
        by simp
      interpret Unpack: simulation
                          \<open>Rts (dom f \<otimes> dom g)\<close> Dom.resid \<open>Unpack (dom f) (dom g)\<close>
        using assms simulation_Unpack [of "dom f" "dom g"] by simp
      interpret Unpack.A: extensional_rts \<open>Rts (dom f \<otimes> dom g)\<close>
        by (simp add: assms)
      interpret Unpack: simulation_as_transformation
                          \<open>Rts (dom f \<otimes> dom g)\<close> Dom.resid \<open>Unpack (dom f) (dom g)\<close>
        ..
      have "Unpack (cod f) (cod g) \<circ> Map (f \<otimes> g) =
            Unpack (cod f) (cod g) \<circ>
              Map \<langle>f \<cdot> \<pp>\<^sub>1[dom f, dom g], g \<cdot> \<pp>\<^sub>0[dom f, dom g]\<rangle>"
        using assms prod_def by force
      also have "... = Unpack (cod f) (cod g) \<circ> 
                         Pack (cod f) (cod g) \<circ>
                           (Cod.tuple (Map (f \<cdot> \<pp>\<^sub>1[dom f, dom g]))
                                      (Map (g \<cdot> \<pp>\<^sub>0[dom f, dom g])))"
        using assms Map_tuple
        by (metis (no_types, lifting) Fun.comp_assoc cod_pr0 cod_pr1
            comp_in_homI' ide_dom pr_simps(1-2,4-5))
      also have "... = I (Cod.resid) \<circ>
                         Cod.tuple (Map (f \<cdot> \<pp>\<^sub>1[dom f, dom g]))
                                   (Map (g \<cdot> \<pp>\<^sub>0[dom f, dom g]))"
        using assms Unpack_o_Pack by auto
      also have "... = Cod.tuple (Map (f \<cdot> \<pp>\<^sub>1[dom f, dom g]))
                                 (Map (g \<cdot> \<pp>\<^sub>0[dom f, dom g]))"
      proof -
        have "simulation (Rts (dom f \<otimes> dom g)) Cod.resid
                (Cod.tuple
                   (Map (f \<cdot> \<pp>\<^sub>1[dom f, dom g]))
                   (Map (g \<cdot> \<pp>\<^sub>0[dom f, dom g])))"
          by (metis arrD(3) assms(1-2) cod_comp cod_pr0 cod_pr1 dom_comp
              ide_dom pr_simps(1-2,4-5) seqI simulation_tuple)
        thus ?thesis
          using assms comp_identity_simulation by blast
      qed
      also have "... = Cod.tuple
                         (Map f \<circ> (Dom.P\<^sub>1 \<circ> Unpack (dom f) (dom g)))
                         (Map g \<circ> (Dom.P\<^sub>0 \<circ> Unpack (dom f) (dom g)))"
        using assms Map_comp Map_p\<^sub>1 Map_p\<^sub>0 by auto
      also have "... = product_simulation.map (Rts f) (Rts g) (Map f) (Map g) \<circ>
                         Dom.tuple
                           (Dom.P\<^sub>1 \<circ> Unpack (dom f) (dom g))
                           (Dom.P\<^sub>0 \<circ> Unpack (dom f) (dom g))"
      proof -
        interpret P\<^sub>1oUnpack: simulation \<open>Rts (dom f \<otimes> dom g)\<close> \<open>Rts (dom f)\<close>
                               \<open>Dom.P\<^sub>1 \<circ> Unpack (dom f) (dom g)\<close>
          using assms Dom.P\<^sub>1_is_simulation simulation_comp
                simulation_Unpack [of "dom f" "dom g"]
          by auto
        interpret P\<^sub>1oUnpack: simulation_as_transformation
                               \<open>Rts (dom f \<otimes> dom g)\<close> \<open>Rts (dom f)\<close>
                               \<open>Dom.P\<^sub>1 \<circ> Unpack (dom f) (dom g)\<close>
          ..
        interpret P\<^sub>0oUnpack: simulation \<open>Rts (dom f \<otimes> dom g)\<close> \<open>Rts (dom g)\<close>
                               \<open>Dom.P\<^sub>0 \<circ> Unpack (dom f) (dom g)\<close>
          using assms Dom.P\<^sub>0_is_simulation simulation_comp
                simulation_Unpack [of "dom f" "dom g"]
          by auto
        interpret P\<^sub>0oUnpack: simulation_as_transformation
                               \<open>Rts (dom f \<otimes> dom g)\<close> \<open>Rts (dom g)\<close>
                               \<open>Dom.P\<^sub>0 \<circ> Unpack (dom f) (dom g)\<close>
          ..
        show ?thesis
          by (metis (no_types, lifting) P\<^sub>0oUnpack.transformation_axioms
              P\<^sub>1oUnpack.transformation_axioms RTSx.Dom_dom RTSx.V.ide_implies_arr
              RTS\<^sub>S.dom_char\<^sub>S\<^sub>b\<^sub>C Rts_def arrD(3) arr_iff_RTS_sta assms(1-2)
              comp_product_simulation_tuple2 comp_def)
      qed
      also have "... = product_simulation.map
                         (Rts (dom f)) (Rts (dom g)) (Map f) (Map g) \<circ>
                            Unpack (dom f) (dom g)"
        using assms Unpack.simulation_axioms Dom.tuple_proj RTSx.arr_char
        by (metis (no_types, lifting) RTSx.Dom_dom RTSx.V.ide_implies_arr
            RTS\<^sub>S.arrE RTS\<^sub>S.dom_char\<^sub>S\<^sub>b\<^sub>C Rts_def comp_def)
      finally show ?thesis by blast
    qed

    lemma Map_prod:
    assumes "arr f" and "arr g"
    shows "Map (f \<otimes> g) =
           Pack (cod f) (cod g) \<circ>
             product_simulation.map (Rts (dom f)) (Rts (dom g)) (Map f) (Map g) \<circ>
               Unpack (dom f) (dom g)"
    proof -
      have "Map (f \<otimes> g) =
            Pack (cod f) (cod g) \<circ> (Unpack (cod f) (cod g) \<circ> Map (f \<otimes> g))"
      proof -
        have "Map (f \<otimes> g) =
              (Pack (cod f) (cod g) \<circ> (Unpack (cod f) (cod g)) \<circ> Map (f \<otimes> g))"
          using assms Pack_o_Unpack [of "cod f" "cod g"] arrD(3) [of "f \<otimes> g"]
          by (simp add: comp_identity_simulation)
        thus ?thesis
          using Fun.comp_assoc by metis
      qed
      also have "... =
                 Pack (cod f) (cod g) \<circ>
                   (product_simulation.map
                      (Rts (dom f)) (Rts (dom g)) (Map f) (Map g) \<circ>
                      Unpack (dom f) (dom g))"
        using assms Unpack_naturality [of f g] by auto
      also have "... = Pack (cod f) (cod g) \<circ>
                         product_simulation.map
                           (Rts (dom f)) (Rts (dom g)) (Map f) (Map g) \<circ>
                           Unpack (dom f) (dom g)"
        by auto
      finally show ?thesis by blast
    qed

    subsection "Exponentials"

    definition exp :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr"
    where "exp \<equiv> RTSx.exp"

    definition eval :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr"
    where "eval \<equiv> RTSx.eval"

    definition curry :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr"
    where "curry \<equiv> RTSx.curry"

    definition uncurry :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A arr"
    where "uncurry \<equiv> RTSx.uncurry"

    definition Func :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> 'A \<Rightarrow> ('A, 'A) exponential_rts.arr"
    where "Func \<equiv> RTSx.Func"

    definition Unfunc :: "'A arr \<Rightarrow> 'A arr \<Rightarrow> ('A, 'A) exponential_rts.arr \<Rightarrow> 'A"
    where "Unfunc \<equiv> RTSx.Unfunc"

    lemma inverse_simulations_Func_Unfunc:
    assumes "ide b" and "ide c"
    shows "inverse_simulations
             (exponential_rts.resid (Rts b) (Rts c)) (Rts (exp b c))
             (Func b c) (Unfunc b c)"
      unfolding Func_def Unfunc_def Rts_def exp_def
      using assms RTSx.inverse_simulations_Func_Unfunc ide_iff_RTS_obj by blast

    lemma simulation_Func:
    assumes "ide b" and "ide c"
    shows "simulation
             (Rts (exp b c)) (exponential_rts.resid (Rts b) (Rts c)) (Func b c)"
      using assms inverse_simulations_Func_Unfunc inverse_simulations_def
      by fast

    lemma simulation_Unfunc:
    assumes "ide b" and "ide c"
    shows "simulation
             (exponential_rts.resid (Rts b) (Rts c)) (Rts (exp b c)) (Unfunc b c)"
      using assms inverse_simulations_Func_Unfunc inverse_simulations_def
      by fast

    lemma Func_o_Unfunc:
    assumes "ide b" and "ide c"
    shows "Func b c \<circ> Unfunc b c = I (exponential_rts.resid (Rts b) (Rts c))"
      using assms
      by (meson inverse_simulations.inv' inverse_simulations_Func_Unfunc)

    lemma Unfunc_o_Func:
    assumes "ide b" and "ide c"
    shows "Unfunc b c \<circ> Func b c = I (Rts (exp b c))"
      using assms
      by (meson inverse_simulations.inv inverse_simulations_Func_Unfunc)

    lemma Func_Unfunc [simp]:
    assumes "ide b" and "ide c"
    and "residuation.arr (exponential_rts.resid (Rts b) (Rts c)) t"
    shows "Func b c (Unfunc b c t) = t"
      using assms
      by (meson inverse_simulations.inv'_simp inverse_simulations_Func_Unfunc)

    lemma Unfunc_Func [simp]:
    assumes "ide b" and "ide c"
    and "residuation.arr (Rts (exp b c)) t"
    shows "Unfunc b c (Func b c t) = t"
      using assms
      by (meson inverse_simulations.inv_simp inverse_simulations_Func_Unfunc)

    lemma Map_eval:
    assumes "ide b" and "ide c"
    shows "Map (eval b c) =
           evaluation_map.map (Rts b) (Rts c) \<circ>
             product_simulation.map (Rts (exp b c)) (Rts b) (Func b c) (I (Rts b)) \<circ>
               Unpack (exp b c) b"
      unfolding Map_def eval_def Rts_def exp_def Func_def Unpack_def
      using assms RTSx.Map_eval [of b c] ide_iff_RTS_obj by force

    lemma Map_curry:
    assumes "ide a" and "ide b" and "\<guillemotleft>f : a \<otimes> b \<rightarrow> c\<guillemotright>"
    shows "Map (curry a b c f) =
           Unfunc b c \<circ>
             Currying.Curry3 (Rts a) (Rts b) (Rts c) (Map f \<circ> Pack a b)"
      unfolding Map_def curry_def Unfunc_def Rts_def Pack_def
      using assms RTSx.Map_curry [of a b c f] ide_iff_RTS_obj arr_iff_RTS_sta
      by (metis (no_types, lifting) RTSx.H.category_axioms RTSx.Map_simps(3-4)
          RTSx.V.ide_iff_src_self RTSx.V.trg_ide RTSx.arr_coincidence\<^sub>C\<^sub>R\<^sub>C
          RTS\<^sub>S.ide_cod RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C category.in_homE category_axioms
          comp_def)

    lemma Map_uncurry:
    assumes "ide b" and "ide c" and "\<guillemotleft>g : a \<rightarrow> exp b c\<guillemotright>"
    shows "Map (uncurry a b c g) =
           Currying.Uncurry (Rts a) (Rts b) (Rts c) (Func b c \<circ> Map g) \<circ>
             Unpack a b"
      unfolding Map_def uncurry_def Func_def Rts_def Unpack_def
      using assms RTSx.Map_uncurry ide_iff_RTS_obj arr_iff_RTS_sta ide_dom
      by auto

    subsection "Cartesian Closure"

    sublocale elementary_cartesian_closed_category
                comp p\<^sub>0 p\<^sub>1 one trm exp eval curry
    proof
      fix b c
      assume b: "ide b" and c: "ide c"
      show "\<guillemotleft>eval b c : exp b c \<otimes> b \<rightarrow> c\<guillemotright>"
        unfolding eval_def exp_def
        using b c RTSx.eval_in_hom\<^sub>R\<^sub>C\<^sub>R prod_char ide_iff_RTS_obj
              arr_iff_RTS_sta RTSx.obj_is_sta
        by (simp add: RTSx.obj_exp RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C comp_def)
      show "ide (exp b c)"
        unfolding exp_def
        using b c ide_iff_RTS_obj RTSx.obj_exp by simp
      fix a
      assume a: "ide a"
      fix g
      assume g: "\<guillemotleft>g : a \<otimes> b \<rightarrow> c\<guillemotright>"
      show 1: "\<guillemotleft>curry a b c g : a \<rightarrow> exp b c\<guillemotright>"
        unfolding curry_def
        using a b c g ide_char prod_char ide_iff_RTS_obj
              RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C \<open>ide (exp b c)\<close>
              exp_def comp_def RTSx.curry_in_hom RTSx.sta_curry
        by (metis (no_types, lifting))
      show "eval b c \<cdot> (curry a b c g \<otimes> b) = g"
        using a b c g 1 RTSx.uncurry_curry RTSx.uncurry_expansion
              arr_iff_RTS_sta ide_iff_RTS_obj RTS\<^sub>S.comp_char
              RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C ideD(1)
        apply (auto simp add: exp_def comp_def curry_def eval_def)[1]
          apply (metis (no_types, lifting) comp_def prod_char)
         apply (metis comp_def prod_simps(1))
        by (metis (no_types, lifting) RTSx.H.ext RTSx.arr_coincidence\<^sub>C\<^sub>R\<^sub>C
            RTSx.null_coincidence\<^sub>C\<^sub>R\<^sub>C comp_def prod_char)
      next
      fix a b c h
      assume a: "ide a" and b: "ide b" and c: "ide c"
      and h: "\<guillemotleft>h : a \<rightarrow> exp b c\<guillemotright>"
      show "curry a b c (eval b c \<cdot> (h \<otimes> b)) = h"
        using a b c h prod_char RTSx.curry_uncurry ide_iff_RTS_obj
              RTSx.uncurry_expansion RTS\<^sub>S.comp_char RTS\<^sub>S.in_hom_char\<^sub>S\<^sub>b\<^sub>C
              RTSx.obj_is_sta RTSx.sta_prod RTS\<^sub>S.arr_char\<^sub>S\<^sub>b\<^sub>C
        apply (auto simp add: eval_def curry_def comp_def exp_def)[1]
        by (metis (no_types, lifting) RTSx.H.ext RTSx.arr_coincidence\<^sub>C\<^sub>R\<^sub>C
            RTSx.null_coincidence\<^sub>C\<^sub>R\<^sub>C)
    qed

    theorem is_elementary_cartesian_closed_category:
    shows "elementary_cartesian_closed_category
                comp p\<^sub>0 p\<^sub>1 one trm exp eval curry"
      ..

  end

subsection "Associators"

  text \<open>
    Here we expose the relationship between the associators internal to \<open>\<^bold>R\<^bold>T\<^bold>S\<close> and those
    external to it.
  \<close>

  locale Association =
    rtscat arr_type
  for arr_type :: "'A itself"
  and a :: "'A rtscat.arr"
  and b :: "'A rtscat.arr"
  and c :: "'A rtscat.arr" +
  assumes a: "ide a"
  and b: "ide b"
  and c: "ide c"
  begin

    interpretation A: extensional_rts \<open>Rts a\<close>
      using a by simp
    interpretation B: extensional_rts \<open>Rts b\<close>
      using b by simp
    interpretation C: extensional_rts \<open>Rts c\<close>
      using c by simp

    interpretation A: identity_simulation \<open>Rts a\<close> ..
    interpretation B: identity_simulation \<open>Rts b\<close> ..
    interpretation C: identity_simulation \<open>Rts c\<close> ..

    interpretation AxB: product_rts \<open>Rts a\<close> \<open>Rts b\<close> ..
    interpretation AxB_xC: product_rts AxB.resid \<open>Rts c\<close> ..
    interpretation BxC: product_rts \<open>Rts b\<close> \<open>Rts c\<close> ..
    interpretation Ax_BxC: product_rts \<open>Rts a\<close> BxC.resid ..

    interpretation AxB: extensional_rts AxB.resid
      using A.extensional_rts_axioms B.extensional_rts_axioms
            AxB.preserves_extensional_rts
      by blast
    interpretation BxC: extensional_rts BxC.resid
      using B.extensional_rts_axioms C.extensional_rts_axioms
            BxC.preserves_extensional_rts
      by blast
    interpretation AxB_xC: extensional_rts AxB_xC.resid
      using AxB.extensional_rts_axioms C.extensional_rts_axioms
            AxB_xC.preserves_extensional_rts
      by blast
    interpretation Ax_BxC: extensional_rts Ax_BxC.resid
      using A.extensional_rts_axioms BxC.extensional_rts_axioms
            Ax_BxC.preserves_extensional_rts
      by blast

    sublocale ASSOC: ASSOC \<open>Rts a\<close> \<open>Rts b\<close> \<open>Rts c\<close> ..

    interpretation axb: extensional_rts \<open>Rts (a \<otimes> b)\<close>
      using a b by simp
    interpretation bxc: extensional_rts \<open>Rts (b \<otimes> c)\<close>
      using b c by simp
    interpretation axb_xc: extensional_rts \<open>Rts ((a \<otimes> b) \<otimes> c)\<close>
      using a b c by simp
    interpretation ax_bxc: extensional_rts \<open>Rts (a \<otimes> (b \<otimes> c))\<close>
      using a b c by simp

    interpretation PU_ab: inverse_simulations
                            \<open>Rts (a \<otimes> b)\<close> AxB.resid \<open>Pack a b\<close> \<open>Unpack a b\<close>
      using a b inverse_simulations_Pack_Unpack [of a b] by fastforce
    interpretation PU_bc: inverse_simulations
                            \<open>Rts (b \<otimes> c)\<close> BxC.resid \<open>Pack b c\<close> \<open>Unpack b c\<close>
      using b c inverse_simulations_Pack_Unpack [of b c] by fastforce

    interpretation Axbc: product_rts \<open>Rts a\<close> \<open>Rts (b \<otimes> c)\<close> ..
    interpretation Axbc: identity_simulation Axbc.resid ..
    interpretation abxC: product_rts \<open>Rts (a \<otimes> b)\<close> \<open>Rts c\<close> ..
    interpretation abxC: identity_simulation abxC.resid ..

    interpretation AxPack_bc:
      product_simulation \<open>Rts a\<close> BxC.resid \<open>Rts a\<close> \<open>Rts (b \<otimes> c)\<close>
        \<open>I (Rts a)\<close> \<open>Pack b c\<close> ..
    interpretation AxUnpack_bc:
      product_simulation \<open>Rts a\<close> \<open>Rts (b \<otimes> c)\<close> \<open>Rts a\<close> BxC.resid
        \<open>I (Rts a)\<close> \<open>Unpack b c\<close> ..
    interpretation Unpack_abxC:
      product_simulation \<open>Rts (a \<otimes> b)\<close> \<open>Rts c\<close> AxB.resid \<open>Rts c\<close>
        \<open>Unpack a b\<close> \<open>I (Rts c)\<close> ..

    sublocale PU_Axbc: inverse_simulations Axbc.resid Ax_BxC.resid
                         AxPack_bc.map AxUnpack_bc.map
    proof
      show "AxPack_bc.map \<circ> AxUnpack_bc.map = Axbc.map"
      proof -
        have "AxPack_bc.map \<circ> AxUnpack_bc.map =
              product_simulation.map (Rts a) (Rts (b \<otimes> c))
                (A.map \<circ> A.map) (Pack b c \<circ> Unpack b c)"
          using A.simulation_axioms PU_bc.F.simulation_axioms
                PU_bc.G.simulation_axioms PU_bc.inv'
                simulation_interchange
                  [of "Rts a" "Rts a" A.map "Rts (b \<otimes> c)"
                       BxC.resid "Unpack b c" "Rts a"
                       A.map "Rts (b \<otimes> c)" "Pack b c"]
          by simp
        also have "... =
                   product_simulation.map (Rts a) (Rts (b \<otimes> c))
                     A.map (I (Rts (b \<otimes> c)))"
          using PU_bc.inv' A.simulation_axioms
                comp_identity_simulation [of "Rts a" "Rts a" A.map]
          by simp
        also have "... = Axbc.map"
          using product_identity_simulation A.rts_axioms bxc.rts_axioms
          by blast
        finally show ?thesis by blast
      qed
      show "AxUnpack_bc.map \<circ> AxPack_bc.map = I Ax_BxC.resid"
      proof -
        have "AxUnpack_bc.map \<circ> AxPack_bc.map =
              product_simulation.map (Rts a) BxC.resid
                (A.map \<circ> A.map) (Unpack b c \<circ> Pack b c)"
          using A.simulation_axioms PU_bc.F.simulation_axioms
                PU_bc.G.simulation_axioms PU_bc.inv
                simulation_interchange
                  [of "Rts a" "Rts a" "A.map" BxC.resid "Rts (b \<otimes> c)"
                      "Pack b c" "Rts a" A.map BxC.resid "Unpack b c"]
          by simp
        also have "... =
                   product_simulation.map (Rts a) BxC.resid
                     A.map (I BxC.resid)"
          using PU_bc.inv A.simulation_axioms
                comp_identity_simulation [of "Rts a" "Rts a" A.map]
          by simp
        also have "... = I Ax_BxC.resid"
          using product_identity_simulation A.rts_axioms BxC.rts_axioms
          by blast
        finally show ?thesis by blast
      qed
    qed

    text \<open>
      The following shows that the simulation \<open>Map \<a>[a, b, c]\<close> underlying an internal associator
      \<open>\<a>[a, b, c]\<close> is transformed into a corresponding external associator \<open>ASSOC.map\<close> via
      invertible simulations that ``unpack'' product objects in \<open>\<^bold>R\<^bold>T\<^bold>S\<close> into corresponding
      product RTS's.
    \<close>

    lemma Unpack_o_Map_assoc:
    shows "(AxUnpack_bc.map \<circ> Unpack a (b \<otimes> c)) \<circ> Map \<a>[a, b, c] =
           ASSOC.map \<circ> (Unpack_abxC.map \<circ> Unpack (a \<otimes> b) c)"
    proof -
      have "(AxUnpack_bc.map \<circ> Unpack a (b \<otimes> c)) \<circ> Map \<a>[a, b, c] =
            (AxUnpack_bc.map \<circ> Unpack a (b \<otimes> c)) \<circ> 
               Pack a (b \<otimes> c) \<circ>
                 (Axbc.tuple
                    (Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                    (Map \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>))"
        using a b c
              Map_tuple
                [of "\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]" "(a \<otimes> b) \<otimes> c" a
                    "\<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>" "b \<otimes> c"]
              assoc_expansion [of a b c]
        by auto
      also have "... = AxUnpack_bc.map \<circ>
                         (Unpack a (b \<otimes> c) \<circ> Pack a (b \<otimes> c)) \<circ>
                           (Axbc.tuple
                              (Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                              (Map \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>))"
        by force
      also have "... = AxUnpack_bc.map \<circ>
                         I Axbc.resid \<circ>
                           (Axbc.tuple
                              (Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                              (Map \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>))"
        using a b c Unpack_o_Pack [of a "b \<otimes> c"] by fastforce
      also have "... = AxUnpack_bc.map \<circ>
                         (Axbc.tuple
                           (Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                           (Map \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>))"
        using comp_simulation_identity
                [of Axbc.resid Ax_BxC.resid AxUnpack_bc.map]
              AxUnpack_bc.simulation_axioms
        by simp
      also have "... = Ax_BxC.tuple
                         (I (Rts a) \<circ> Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                         (Unpack b c \<circ> Map \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>)"
      proof -
        have "simulation (Rts ((a \<otimes> b) \<otimes> c)) (Rts a) (Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))"
          using a b c
          by (metis (no_types, lifting) arrD(3) cod_comp cod_pr1 dom_comp ide_prod
              pr_simps(4) pr_simps(5) seqI)
        moreover have "simulation (Rts ((a \<otimes> b) \<otimes> c)) (Rts (b \<otimes> c))
                         (Map \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>)"
        proof -
          have "\<guillemotleft>\<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle> : (a \<otimes> b) \<otimes> c \<rightarrow> b \<otimes> c\<guillemotright>"
            using a b c by blast
          thus ?thesis
            using arrD(3) by fastforce
        qed
        ultimately show ?thesis
          using PU_bc.G.simulation_axioms A.simulation_axioms
                simulation_as_transformation.intro
                comp_product_simulation_tuple
                  [of "Rts a" "Rts a" A.map "Rts (b \<otimes> c)" BxC.resid "Unpack b c"
                      "Rts ((a \<otimes> b) \<otimes> c)" "Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c])"
                      "Map \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>"]
          by blast
      qed
      also have "... = Ax_BxC.tuple
                         (Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                         (Unpack b c \<circ> Map \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>)"
      proof -
        have "\<guillemotleft>p\<^sub>1 a b \<cdot> p\<^sub>1 (a \<otimes> b) c : (a \<otimes> b) \<otimes> c \<rightarrow> a\<guillemotright>"
          using a b c by blast
        hence "simulation (Rts ((a \<otimes> b) \<otimes> c)) (Rts a)
                 (Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))"
          using arrD(3) by (metis (no_types, lifting) in_homE)
        thus ?thesis
          using comp_identity_simulation
                  [of "Rts ((a \<otimes> b) \<otimes> c)" "Rts a" "Map (\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c])"]
          by fastforce
      qed
      also have "... = Ax_BxC.tuple
                         (Map \<pp>\<^sub>1[a, b] \<circ> Map \<pp>\<^sub>1[a \<otimes> b, c])
                         (Unpack b c \<circ> Map \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>)"
        using a b c Map_comp by auto
      also have "... = Ax_BxC.tuple
                         (Map \<pp>\<^sub>1[a, b] \<circ> Map \<pp>\<^sub>1[a \<otimes> b, c])
                         (Unpack b c \<circ>
                            (Pack b c \<circ>
                               abxC.tuple
                                 (Map (\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                                 (Map \<pp>\<^sub>0[a \<otimes> b, c])))"
        using a b c Map_tuple
        by (metis (no_types, lifting) comp_in_homI ide_prod pr_in_hom(1-2))
      also have "... = Ax_BxC.tuple
                         (Map \<pp>\<^sub>1[a, b] \<circ> Map \<pp>\<^sub>1[a \<otimes> b, c])
                         ((Unpack b c \<circ> Pack b c) \<circ>
                               abxC.tuple
                                 (Map (\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                                 (Map \<pp>\<^sub>0[a \<otimes> b, c]))"
        using fun.map_comp by metis
      also have "... = Ax_BxC.tuple
                         (Map \<pp>\<^sub>1[a, b] \<circ> Map \<pp>\<^sub>1[a \<otimes> b, c])
                         (I BxC.resid \<circ>
                            BxC.tuple
                              (Map (\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                              (Map \<pp>\<^sub>0[a \<otimes> b, c]))"
        using PU_bc.inv by simp
      also have "... = Ax_BxC.tuple
                         (Map \<pp>\<^sub>1[a, b] \<circ> Map \<pp>\<^sub>1[a \<otimes> b, c])
                         (BxC.tuple
                            (Map \<pp>\<^sub>0[a, b] \<circ> Map \<pp>\<^sub>1[a \<otimes> b, c])
                            (Map \<pp>\<^sub>0[a \<otimes> b, c]))"
      proof -
        have "\<guillemotleft>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c] : (a \<otimes> b) \<otimes> c \<rightarrow> b\<guillemotright> \<and>
              \<guillemotleft>\<pp>\<^sub>0[a \<otimes> b, c] : (a \<otimes> b) \<otimes> c \<rightarrow> c\<guillemotright>"
          using a b c by blast
        hence "simulation (Rts ((a \<otimes> b) \<otimes> c)) BxC.resid
                 (pointwise_tuple (Map (\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c])) (Map \<pp>\<^sub>0[a \<otimes> b, c]))"
          using a b c arrD(3) simulation_tuple in_homE by metis
        thus ?thesis
          using a b c Map_comp
                comp_identity_simulation
                  [of "Rts ((a \<otimes> b) \<otimes> c)" BxC.resid
                      "BxC.tuple
                          (Map (\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c]))
                          (Map \<pp>\<^sub>0[a \<otimes> b, c])"]
          by auto
      qed
      also have "... = Ax_BxC.tuple
                         ((AxB.P\<^sub>1 \<circ> Unpack a b) \<circ>
                            (abxC.P\<^sub>1 \<circ> Unpack (a \<otimes> b) c))
                         (BxC.tuple
                            ((AxB.P\<^sub>0 \<circ> Unpack a b) \<circ>
                               (abxC.P\<^sub>1 \<circ> Unpack (a \<otimes> b) c))
                            (abxC.P\<^sub>0 \<circ> Unpack (a \<otimes> b) c))"
        using a b c Map_p\<^sub>1 Map_p\<^sub>0 by auto
      also have "... = Ax_BxC.tuple
                         (AxB.P\<^sub>1 \<circ> (Unpack a b \<circ> abxC.P\<^sub>1) \<circ> Unpack (a \<otimes> b) c)
                         (BxC.tuple
                            (AxB.P\<^sub>0 \<circ> (Unpack a b \<circ> abxC.P\<^sub>1) \<circ> Unpack (a \<otimes> b) c)
                            (abxC.P\<^sub>0 \<circ> Unpack (a \<otimes> b) c))"
        using fun.map_comp by metis
      also have "... = Ax_BxC.tuple
                         (AxB.P\<^sub>1 \<circ> (AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map) \<circ>
                            Unpack (a \<otimes> b) c)
                         (BxC.tuple
                            (AxB.P\<^sub>0 \<circ> (AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map) \<circ>
                            Unpack (a \<otimes> b) c)
                              (abxC.P\<^sub>0 \<circ> Unpack (a \<otimes> b) c))"
      proof -
        (* TODO: Probably wants to be a lemma. *)
        have "Unpack a b \<circ> abxC.P\<^sub>1 = AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map"
        proof
          fix x
          show "(Unpack a b \<circ> abxC.P\<^sub>1) x =
                (AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map) x"
          proof (cases "abxC.arr x")
            show "\<not> abxC.arr x \<Longrightarrow> ?thesis"
              using Unpack_abxC.extensional AxB_xC.P\<^sub>1.extensional
                    abxC.P\<^sub>1.extensional PU_ab.G.extensional
              by auto
            assume x: "abxC.arr x"
            show ?thesis
              using x a b c abxC.P\<^sub>1_def Unpack_abxC.map_def AxB_xC.P\<^sub>1_def
              apply auto[1]
              using AxB.arr_char by blast+
          qed
        qed
        thus ?thesis by simp
      qed
      also have "... = Ax_BxC.tuple
                         (AxB.P\<^sub>1 \<circ> AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map \<circ>
                            Unpack (a \<otimes> b) c)
                         (BxC.tuple
                            (AxB.P\<^sub>0 \<circ> AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map \<circ>
                               Unpack (a \<otimes> b) c)
                            (abxC.P\<^sub>0 \<circ> Unpack (a \<otimes> b) c))"
      proof -
        have "AxB.P\<^sub>1 \<circ> (AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map) \<circ> Unpack (a \<otimes> b) c =
              AxB.P\<^sub>1 \<circ> AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map \<circ> Unpack (a \<otimes> b) c"
          by auto
        moreover have "AxB.P\<^sub>0 \<circ> (AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map) \<circ>
                         Unpack (a \<otimes> b) c =
                       AxB.P\<^sub>0 \<circ> AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map \<circ>
                         Unpack (a \<otimes> b) c"
          by auto
        ultimately show ?thesis by simp
      qed
      also have "... = Ax_BxC.tuple
                         (AxB.P\<^sub>1 \<circ> AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map)
                         (BxC.tuple
                            (AxB.P\<^sub>0 \<circ> AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map)
                            abxC.P\<^sub>0) \<circ>
                         Unpack (a \<otimes> b) c"
        by (simp add: comp_pointwise_tuple)
      also have "... = Ax_BxC.tuple
                         (AxB.P\<^sub>1 \<circ> AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map)
                         (BxC.tuple
                            (AxB.P\<^sub>0 \<circ> AxB_xC.P\<^sub>1 \<circ> Unpack_abxC.map)
                            (AxB_xC.P\<^sub>0 \<circ> Unpack_abxC.map)) \<circ>
                         Unpack (a \<otimes> b) c"
      proof -
        (* TODO: Also probably wants to be a lemma. *)
        have "AxB_xC.P\<^sub>0 \<circ> Unpack_abxC.map = abxC.P\<^sub>0"
        proof
          fix x
          show "(AxB_xC.P\<^sub>0 \<circ> Unpack_abxC.map) x = abxC.P\<^sub>0 x"
            using a b c abxC.P\<^sub>0_def Unpack_abxC.map_def AxB_xC.P\<^sub>0_def
                  PU_ab.G.preserves_reflects_arr abxC.arr_char PU_ab.G.extensional
                  abxC.P\<^sub>1.extensional axb.not_arr_null AxB_xC.P\<^sub>1.extensional
                  AxB_xC.not_arr_null
            by auto
        qed
        thus ?thesis by simp
      qed
      also have "... = Ax_BxC.tuple
                         (AxB.P\<^sub>1 \<circ> AxB_xC.P\<^sub>1)
                         (BxC.tuple (AxB.P\<^sub>0 \<circ> AxB_xC.P\<^sub>1) AxB_xC.P\<^sub>0) \<circ>
                         Unpack_abxC.map \<circ> Unpack (a \<otimes> b) c"
        by (simp add: comp_pointwise_tuple)
      also have "... = ASSOC.map \<circ> (Unpack_abxC.map \<circ> Unpack (a \<otimes> b) c)"
        unfolding ASSOC.map_def by auto
      finally show ?thesis by blast
    qed

    text \<open>
      As a corollary, we obtain an explicit formula for \<open>Map \<a>[a, b, c]\<close> in terms of
      the external associator \<open>ASSOC.map\<close> and packing and unpacking isomorphisms.
    \<close>

    corollary Map_assoc:
    shows "Map \<a>[a, b, c] =
           (Pack a (b \<otimes> c) \<circ> AxPack_bc.map) \<circ>
              ASSOC.map \<circ>
                (Unpack_abxC.map \<circ> Unpack (a \<otimes> b) c)"
    proof -
      interpret PU_axbc: inverse_simulations
                           \<open>Rts (a \<otimes> (b \<otimes> c))\<close> Axbc.resid
                           \<open>Pack a (b \<otimes> c)\<close> \<open>Unpack a (b \<otimes> c)\<close>
        using a b c
              inverse_simulations_Pack_Unpack [of a "b \<otimes> c"]
        by force
      interpret PU_abxc: inverse_simulations
                           \<open>Rts ((a \<otimes> b) \<otimes> c)\<close> abxC.resid
                           \<open>Pack (a \<otimes> b) c\<close> \<open>Unpack (a \<otimes> b) c\<close>
        using a b c
              inverse_simulations_Pack_Unpack [of "a \<otimes> b" c]
        by force
      interpret PoAxP: composite_simulation
                         Ax_BxC.resid Axbc.resid \<open>Rts (a \<otimes> b \<otimes> c)\<close>
                         AxPack_bc.map \<open>Pack a (b \<otimes> c)\<close> ..
      interpret UxCoU: composite_simulation
                         \<open>Rts  ((a \<otimes> b) \<otimes> c)\<close> abxC.resid AxB_xC.resid
                         \<open>Unpack (a \<otimes> b) c\<close> Unpack_abxC.map ..
      interpret AxUoU: composite_simulation
                         \<open>Rts (a \<otimes> b \<otimes> c)\<close> Axbc.resid Ax_BxC.resid
                         \<open>Unpack a (b \<otimes> c)\<close> AxUnpack_bc.map ..

      have *: "inverse_simulations (Rts (a \<otimes> b \<otimes> c)) Ax_BxC.resid
                 (Pack a (b \<otimes> c) \<circ> AxPack_bc.map)
                 (AxUnpack_bc.map \<circ> Unpack a (b \<otimes> c))"
      proof
        show "AxUoU.map \<circ> PoAxP.map = I Ax_BxC.resid"
        proof -
          have "AxUoU.map \<circ> PoAxP.map =
                AxUnpack_bc.map \<circ> (Unpack a (b \<otimes> c) \<circ> Pack a (b \<otimes> c)) \<circ>
                  AxPack_bc.map"
            using fun.map_comp by force
          also have "... = AxUnpack_bc.map \<circ> I Axbc.resid \<circ> AxPack_bc.map"
            using PU_axbc.inv by simp
          also have "... = AxUnpack_bc.map \<circ> AxPack_bc.map"
            using comp_simulation_identity AxUnpack_bc.simulation_axioms
            by fastforce
          also have "... = I Ax_BxC.resid"
            using PU_Axbc.inv by blast
          finally show ?thesis by blast
        qed
        show "PoAxP.map \<circ> AxUoU.map = I (Rts (a \<otimes> b \<otimes> c))"
        proof -
          have "PoAxP.map \<circ> AxUoU.map =
                Pack a (b \<otimes> c) \<circ> (AxPack_bc.map \<circ> AxUnpack_bc.map) \<circ>
                  Unpack a (b \<otimes> c)"
            using fun.map_comp by auto
          also have "... = Pack a (b \<otimes> c) \<circ> I Axbc.resid \<circ> Unpack a (b \<otimes> c)"
            using PU_Axbc.inv' by simp
          also have "... = Pack a (b \<otimes> c) \<circ> Unpack a (b \<otimes> c)"
            using comp_simulation_identity PU_axbc.F.simulation_axioms
            by fastforce
          also have "... = I (Rts  (a \<otimes> b \<otimes> c))"
            using PU_axbc.inv' by blast
          finally show ?thesis by blast
        qed
      qed
      have "simulation (Rts ((a \<otimes> b) \<otimes> c)) (Rts (a \<otimes> b \<otimes> c)) (Map \<a>[a, b, c]) "
        using a b c arrD(3)
        by (metis (no_types, lifting) assoc_simps(1-3))
      hence "Map \<a>[a, b, c] = I (Rts (a \<otimes> b \<otimes> c)) \<circ> Map \<a>[a, b, c]"
         using a b c
               comp_identity_simulation
                  [of "Rts ((a \<otimes> b) \<otimes> c)" "Rts (a \<otimes> b \<otimes> c)" "Map \<a>[a, b, c]"]
         by auto
      also have  "... = PoAxP.map \<circ> AxUoU.map \<circ> Map \<a>[a, b, c]"
        using a b c * inverse_simulations.inv' by fastforce
      also have "... = PoAxP.map \<circ> (AxUoU.map \<circ> Map \<a>[a, b, c])"
        using fun.map_comp by fastforce
      also have "... = PoAxP.map \<circ> (ASSOC.map \<circ> UxCoU.map)"
        using Unpack_o_Map_assoc by simp
      also have "... = PoAxP.map \<circ> ASSOC.map \<circ> UxCoU.map"
        using fun.map_comp by fastforce
      finally show ?thesis by blast
    qed

  end

  context rtscat
  begin

    proposition Map_assoc:
    assumes "ide a" and "ide b" and "ide c"
    shows "Map \<a>[a, b, c] =
           Pack a (b \<otimes> c) \<circ>
             product_simulation.map (Rts a) (product_rts.resid (Rts b) (Rts c))
                 (I (Rts a)) (Pack b c) \<circ>
               ASSOC.map (Rts a) (Rts b) (Rts c) \<circ>
                 (product_simulation.map
                      (Rts (a \<otimes> b)) (Rts c) (Unpack a b) (I (Rts c)) \<circ>
                    Unpack (a \<otimes> b) c)"
    proof -
      interpret A: Association arr_type a b c
        using assms by unfold_locales auto
      show ?thesis
        using assms A.Map_assoc by force
    qed

  end

subsection "Compositors"

  text \<open>
    Here we expose the relationship between the compositors internal to \<open>\<^bold>R\<^bold>T\<^bold>S\<close>
    (inherited from @{locale closed_monoidal_category}) and those external to it
    (given by horizontal composition of simulations).
  \<close>

  context rtscat
  begin

    sublocale CMC: cartesian_monoidal_category comp Prod \<alpha> \<iota>
      using extends_to_cartesian_monoidal_category\<^sub>E\<^sub>C\<^sub>C by blast

    sublocale ECMC: elementary_closed_monoidal_category comp Prod \<alpha> \<iota>
                      exp eval curry
      using extends_to_elementary_closed_monoidal_category\<^sub>E\<^sub>C\<^sub>C\<^sub>C by blast

  end

  locale Composition =
    rtscat arr_type
  for arr_type :: "'A itself"
  and a :: "'A rtscat.arr"
  and b :: "'A rtscat.arr"
  and c :: "'A rtscat.arr" +
  assumes a: "ide a"
  and b: "ide b"
  and c: "ide c"
  begin

    abbreviation EXP
    where "EXP \<equiv> \<lambda>a b. Rts (exp a b)"

    interpretation A: extensional_rts \<open>Rts a\<close>
      using a by simp
    interpretation B: extensional_rts \<open>Rts b\<close>
      using b by simp
    interpretation C: extensional_rts \<open>Rts c\<close>
      using c by simp
    interpretation AxB: product_rts \<open>Rts a\<close> \<open>Rts b\<close> ..
    interpretation BxC: product_rts \<open>Rts b\<close> \<open>Rts c\<close> ..
    interpretation AB: exponential_rts \<open>Rts a\<close> \<open>Rts b\<close> ..
    interpretation BC: exponential_rts \<open>Rts b\<close> \<open>Rts c\<close> ..
    interpretation AC: exponential_rts \<open>Rts a\<close> \<open>Rts c\<close> ..
    interpretation ABxA: product_rts AB.resid \<open>Rts a\<close> ..
    interpretation BCxAB: product_rts BC.resid AB.resid ..
    interpretation BCxAB: extensional_rts BCxAB.resid
      using AB.is_extensional_rts BC.is_extensional_rts
        BCxAB.preserves_extensional_rts
      by fastforce
    interpretation BCxAB_x_A: product_rts BCxAB.resid \<open>Rts a\<close> ..

    interpretation ab: extensional_rts \<open>EXP a b\<close>
      using a b ide_exp_ax by simp
    interpretation bc: extensional_rts \<open>EXP b c\<close>
      using b c ide_exp_ax by simp
    interpretation bcxab: product_of_extensional_rts \<open>EXP b c\<close> \<open>EXP a b\<close> ..
    interpretation abxA: product_rts \<open>EXP a b\<close> \<open>Rts a\<close> ..
    interpretation bcxB: product_rts \<open>EXP b c\<close> \<open>Rts b\<close> ..
    interpretation bc_x_abxA: product_rts \<open>EXP b c\<close> abxA.resid ..
    interpretation bcxab_x_A: product_rts bcxab.resid \<open>Rts a\<close> ..

    interpretation ASSOC: ASSOC BC.resid AB.resid \<open>Rts a\<close> ..
    interpretation COMP: COMP \<open>Rts a\<close> \<open>Rts b\<close> \<open>Rts c\<close> ..

    interpretation Assoc_abc: Association arr_type a b c
      using a b c by unfold_locales
    interpretation Assoc_bc_ab_a: Association arr_type \<open>exp b c\<close> \<open>exp a b\<close> a
      using a b c ide_exp_ax by unfold_locales

    interpretation Func_Unfunc_ab: inverse_simulations AB.resid \<open>EXP a b\<close>
                                     \<open>Func a b\<close> \<open>Unfunc a b\<close>
      using a b inverse_simulations_Func_Unfunc [of a b] by blast
    interpretation Func_Unfunc_bc: inverse_simulations BC.resid \<open>EXP b c\<close>
                                    \<open>Func b c\<close> \<open>Unfunc b c\<close>
      using a b c inverse_simulations_Func_Unfunc [of b c] by blast
    interpretation Func_bcxFunc_ab: product_simulation
                                      \<open>EXP b c\<close> \<open>EXP a b\<close> BC.resid AB.resid
                                      \<open>Func b c\<close> \<open>Func a b\<close> ..

    text \<open>
      The following shows that the simulation \<open>Map (Comp a b c)\<close> underlying an internal
      compositor \<open>Comp a b c\<close> is transformed into a corresponding external compositor \<open>COMP.map\<close>
      by invertible simulations that ``unpack'' product and exponential objects in \<open>RTS\<^sub>S\<close> into
      corresponding RTS products and exponentials.
    \<close>

    lemma Func_o_Map_Comp:
    shows "Func a c \<circ> Map (ECMC.Comp a b c) =
           COMP.map \<circ> (Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b))"
    proof -
      interpret A: identity_simulation \<open>Rts a\<close> ..
      interpret B: identity_simulation \<open>Rts b\<close> ..
      interpret BC: identity_simulation BC.resid ..
      interpret ABxA: identity_simulation ABxA.resid ..
      interpret BCxB: product_rts BC.resid \<open>Rts b\<close> ..
      interpret abxa: extensional_rts \<open>Rts (exp a b \<otimes> a)\<close>
        using a b ide_exp_ax by simp
      interpret eval_ab: simulation \<open>Rts (exp a b \<otimes> a)\<close> \<open>Rts b\<close> \<open>Map (eval a b)\<close>
        using a b ide_exp_ax arrD eval_in_hom_ax [of a b] by force
      interpret bc: identity_simulation \<open>EXP b c\<close> ..
      interpret bcxeval: product_simulation
                           \<open>EXP b c\<close> \<open>Rts (exp a b \<otimes> a)\<close> \<open>EXP b c\<close> \<open>Rts b\<close>
                           bc.map \<open>Map (eval a b)\<close> ..
      interpret bcxab': extensional_rts \<open>Rts (exp b c \<otimes> exp a b)\<close>
        using a b c ide_exp_ax by simp
      interpret bcxab'_x_A: product_rts \<open>Rts (exp b c \<otimes> exp a b)\<close> \<open>Rts a\<close> ..
      interpret bcxab: identity_simulation bcxab.resid ..
      interpret bcxab_x_A: product_simulation bcxab.resid \<open>Rts a\<close>
                             bcxab.resid \<open>Rts a\<close> bcxab.map A.map ..
      interpret bcxab: extensional_rts \<open>Rts (exp b c \<otimes> exp a b)\<close>
        using a b c ide_exp_ax by simp
      interpret PU_abxa: inverse_simulations \<open>Rts (exp a b \<otimes> a)\<close> abxA.resid
                           \<open>Pack (exp a b) a\<close> \<open>Unpack (exp a b) a\<close>
        using a b c inverse_simulations_Pack_Unpack [of "exp a b" a] by blast
      interpret PU_bcxab_xa: inverse_simulations
                               \<open>Rts ((exp b c \<otimes> exp a b) \<otimes> a)\<close> bcxab'_x_A.resid
                               \<open>Pack (exp b c \<otimes> exp a b) a\<close>
                               \<open>Unpack (exp b c \<otimes> exp a b) a\<close>
        using a b c ide_exp_ax inverse_simulations_Pack_Unpack by simp
      interpret PU_bcxab: inverse_simulations \<open>Rts (exp b c \<otimes> exp a b)\<close> bcxab.resid
                            \<open>Pack (exp b c) (exp a b)\<close>
                            \<open>Unpack (exp b c) (exp a b)\<close>
        using a b c inverse_simulations_Pack_Unpack [of "exp b c" "exp a b"] by blast
      interpret FU_ac: inverse_simulations AC.resid \<open>EXP a c\<close>
                         \<open>Func a c\<close> \<open>Unfunc a c\<close>
        using a c inverse_simulations_Func_Unfunc [of a c] by blast
      interpret Func_bcxB: product_simulation
                             \<open>EXP b c\<close> \<open>Rts b\<close> BC.resid \<open>Rts b\<close>
                             \<open>Func b c\<close> \<open>I (Rts b)\<close>
        ..
      interpret UnpackxA: product_simulation
                            \<open>Rts (exp b c \<otimes> exp a b)\<close> \<open>Rts a\<close> bcxab.resid \<open>Rts a\<close>
                            \<open>Unpack (exp b c) (exp a b)\<close> A.map ..
      interpret Func_abxA: product_simulation
                             \<open>EXP a b\<close> \<open>Rts a\<close> AB.resid \<open>Rts a\<close>
                             \<open>Func a b\<close> \<open>I (Rts a)\<close>
        ..
      interpret Func_bcxFunc_ab_x_A: product_simulation
                                       bcxab.resid \<open>Rts a\<close> BCxAB.resid \<open>Rts a\<close>
                                       Func_bcxFunc_ab.map A.map ..
      interpret Func_bc_x_Func_abxA: product_simulation
                                       \<open>EXP b c\<close> abxA.resid BC.resid ABxA.resid
                                       \<open>Func b c\<close> Func_abxA.map ..
      interpret E_AB: RTSConstructions.evaluation_map \<open>Rts a\<close> \<open>Rts b\<close> ..
      interpret E_BC: RTSConstructions.evaluation_map \<open>Rts b\<close> \<open>Rts c\<close> ..
      interpret BCxE_AB: product_simulation BC.resid ABxA.resid
                           BC.resid \<open>Rts b\<close> BC.map E_AB.map ..
      interpret E_ABoFunc_abxA: composite_simulation
                                  abxA.resid ABxA.resid \<open>Rts b\<close>
                                  Func_abxA.map E_AB.map ..
      interpret bc_x_E_ABoFunc_abxA: product_simulation
                                       \<open>EXP b c\<close> abxA.resid \<open>EXP b c\<close> \<open>Rts b\<close>
                                       bc.map \<open>E_AB.map \<circ> Func_abxA.map\<close> ..

      have bc_map: "bc.map \<circ> bc.map = bc.map"
        by auto  (* TODO: Comes up frequently and is annoying. *)
      have 1: "\<guillemotleft>eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot> \<a>[exp b c, exp a b, a] :
                  (exp b c \<otimes> exp a b) \<otimes> a \<rightarrow> c\<guillemotright>"
        using a b c eval_in_hom_ax [of b c] eval_in_hom_ax [of a b] ide_exp_ax
        by fastforce
      have "Func a c \<circ> Map (ECMC.Comp a b c) =
            Func a c \<circ> Map (curry (exp b c \<otimes> exp a b) a c
                              (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot>
                                 \<a>[exp b c, exp a b, a]))"
        unfolding ECMC.Comp_def
        using Assoc_bc_ab_a.a Assoc_bc_ab_a.b a assoc_agreement by auto
      also have "... = Func a c \<circ>
                         Unfunc a c \<circ>
                           COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                             (Map (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot>
                                     \<a>[exp b c, exp a b, a]) \<circ>
                                Pack (exp b c \<otimes> exp a b) a)"
      proof -
        have "ide (exp b c \<otimes> exp a b)"
          using a b c ide_exp_ax by blast
        moreover have "\<guillemotleft>eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot>
                          \<a>[exp b c, exp a b, a] :
                           (exp b c \<otimes> exp a b) \<otimes> a \<rightarrow> c\<guillemotright>"
          using a b c eval_in_hom_ax eval_in_hom_ax ide_exp_ax
          by fastforce
        ultimately show ?thesis
          using a Map_curry fun.map_comp by auto
      qed
      also have "... = I AC.resid \<circ>
                         COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                           (Map (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot>
                                   \<a>[exp b c, exp a b, a]) \<circ>
                              Pack (exp b c \<otimes> exp a b) a)"
        using FU_ac.inv' by simp
      also have "... = I AC.resid \<circ>
                         COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                           (Map (eval b c) \<circ>
                              Map (exp b c \<otimes> eval a b) \<circ>
                                Map \<a>[exp b c, exp a b, a] \<circ>
                                  Pack (exp b c \<otimes> exp a b) a)"
      proof -
        have "Map (eval b c \<cdot> (exp b c \<otimes> eval a b) \<cdot> \<a>[exp b c, exp a b, a]) =
              Map (eval b c) \<circ> Map (exp b c \<otimes> eval a b) \<circ> Map \<a>[exp b c, exp a b, a]"
          using 1 Map_comp by fastforce
        thus ?thesis by auto
      qed
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> Func_bcxB.map \<circ> Unpack (exp b c) b \<circ>
                            Map (exp b c \<otimes> eval a b) \<circ>
                              Map \<a>[exp b c, exp a b, a] \<circ>
                                 Pack (exp b c \<otimes> exp a b) a)"
      proof -
        have "simulation bcxab'_x_A.resid (Rts c)
                (Map (eval b c) \<circ>
                   Map (exp b c \<otimes> eval a b) \<circ>
                     Map \<a>[exp b c, exp a b, a] \<circ>
                       Pack (exp b c \<otimes> exp a b) a)"
        proof (intro simulation_comp)
          show "simulation (Rts (exp b c \<otimes> b)) (Rts c) (Map (eval b c))"
            using a b c eval_in_hom_ax [of b c] arrD(3) by force
          show "simulation (Rts (exp b c \<otimes> exp a b \<otimes> a)) (Rts (exp b c \<otimes> b))
                  (Map (exp b c \<otimes> eval a b))"
          proof -
            have "\<guillemotleft>exp b c \<otimes> eval a b : exp b c \<otimes> exp a b \<otimes> a \<rightarrow> exp b c \<otimes> b\<guillemotright>"
              using a b c Assoc_bc_ab_a.a eval_in_hom_ax eval_in_hom_ax
              by auto
            thus ?thesis
              using arrD(3) by fastforce
          qed
          show "simulation bcxab'_x_A.resid (Rts ((exp b c \<otimes> exp a b) \<otimes> a))
                  (Pack (exp b c \<otimes> exp a b) a)"
            using a b c PU_bcxab_xa.F.simulation_axioms by blast
          show "simulation (Rts ((exp b c \<otimes> exp a b) \<otimes> a))
                           (Rts (exp b c \<otimes> exp a b \<otimes> a))
                           (Map \<a>[exp b c, exp a b, a])"
            using a b c ide_exp_ax arrD(3) [of "\<a>[exp b c, exp a b, a]"] by auto
        qed
        moreover have "Currying (Rts (exp b c \<otimes> exp a b)) (Rts a) (Rts c)" ..
        ultimately have "simulation (Rts (exp b c \<otimes> exp a b)) AC.resid
                           (COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                              (Map (eval b c) \<circ>
                                 Map (exp b c \<otimes> eval a b) \<circ>
                                   Map \<a>[exp b c, exp a b, a] \<circ>
                                     Pack (exp b c \<otimes> exp a b) a))"
          using Currying.Curry_preserves_simulations by fastforce
        thus ?thesis
          using b c Assoc_abc.Map_assoc Map_eval comp_identity_simulation
          by auto
      qed
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> Func_bcxB.map \<circ> Unpack (exp b c) b \<circ>
                            (Pack (exp b c) b \<circ>
                               bcxeval.map \<circ>
                                 Unpack (dom (exp b c)) (dom (eval a b))) \<circ>
                               Map \<a>[exp b c, exp a b, a] \<circ>
                                 Pack (exp b c \<otimes> exp a b) a)"
      proof -
        have "bcxeval.map = product_simulation.map
                              (Dom (exp b c)) (Dom (eval a b))
                              (Map (exp b c)) (Map (eval a b))"
        proof -
          have "Dom (eval a b) = Rts (exp a b \<otimes> a)"
            using a b eval_in_hom_ax by fastforce
          thus ?thesis
            using a b c Map_ide ide_exp_ax by auto
        qed
        hence "Map (exp b c \<otimes> eval a b) =
               Pack (exp b c) b \<circ>
                 bcxeval.map \<circ>
                   Unpack (dom (exp b c)) (dom (eval a b))"
          using a b c Map_prod ide_exp_ax eval_in_hom_ax by fastforce
        thus ?thesis by simp
      qed
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> Func_bcxB.map \<circ> Unpack (exp b c) b \<circ>
                            (Pack (exp b c) b \<circ>
                               bcxeval.map \<circ>
                                 Unpack (exp b c) (exp a b \<otimes> a)) \<circ>
                               Map \<a>[exp b c, exp a b, a] \<circ>
                                 Pack (exp b c \<otimes> exp a b) a)"
        using a b c ide_exp_ax eval_in_hom_ax by auto
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> (Func_bcxB.map \<circ>
                            (Unpack (exp b c) b \<circ> Pack (exp b c) b)) \<circ>
                              bcxeval.map \<circ>
                                Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                                  Map \<a>[exp b c, exp a b, a] \<circ>
                                    Pack (exp b c \<otimes> exp a b) a)"
        using fun.map_comp by metis
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> (Func_bcxB.map \<circ> I bcxB.resid) \<circ>
                            bcxeval.map \<circ>
                              Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                                Map \<a>[exp b c, exp a b, a] \<circ>
                                  Pack (exp b c \<otimes> exp a b) a)"
        using b c Unpack_o_Pack ide_exp_ax by auto
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> Func_bcxB.map \<circ>
                            bcxeval.map \<circ>
                              Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                                Map \<a>[exp b c, exp a b, a] \<circ>
                                  Pack (exp b c \<otimes> exp a b) a)"
        using comp_simulation_identity [of bcxB.resid BCxB.resid Func_bcxB.map]
              Func_bcxB.simulation_axioms
        by auto
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> Func_bcxB.map \<circ>
                            product_simulation.map (EXP b c) (Rts (exp a b \<otimes> a))
                              bc.map
                                (E_AB.map \<circ> Func_abxA.map \<circ> Unpack (exp a b) a) \<circ>
                              Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                                Map \<a>[exp b c, exp a b, a] \<circ>
                                  Pack (exp b c \<otimes> exp a b) a)"
         using a b c Map_eval eval_in_hom_ax by auto
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> Func_bcxB.map \<circ>
                            ((product_simulation.map
                                (EXP b c) ABxA.resid bc.map E_AB.map \<circ>
                               product_simulation.map
                                 (EXP b c) abxA.resid bc.map Func_abxA.map) \<circ>
                                 product_simulation.map
                                   (EXP b c) (Rts (exp a b \<otimes> a))
                                   bc.map (Unpack (exp a b) a)) \<circ>
                                  Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                                    Map \<a>[exp b c, exp a b, a] \<circ>
                                      Pack (exp b c \<otimes> exp a b) a)"
      proof -
        have "product_simulation.map (EXP b c) (Rts (exp a b \<otimes> a))
                 bc.map (E_AB.map \<circ> Func_abxA.map \<circ> Unpack (exp a b) a) =
              product_simulation.map
                (EXP b c) abxA.resid bc.map (E_AB.map \<circ> Func_abxA.map) \<circ>
                product_simulation.map
                  (EXP b c) (Rts (exp a b \<otimes> a)) bc.map (Unpack (exp a b) a)"
          using bc_map Func_abxA.simulation_axioms E_AB.simulation_axioms
                bc.simulation_axioms E_ABoFunc_abxA.simulation_axioms
                PU_abxa.G.simulation_axioms
                simulation_interchange
                  [of "EXP b c" "EXP b c" bc.map
                      "Rts (exp a b \<otimes> a)" abxA.resid "Unpack (exp a b) a"
                      "EXP b c" bc.map "Rts b" "E_AB.map \<circ> Func_abxA.map"]
          by simp
        also have "... = product_simulation.map
                          (EXP b c) ABxA.resid bc.map E_AB.map \<circ>
                           product_simulation.map
                             (EXP b c) abxA.resid bc.map Func_abxA.map \<circ>
                             product_simulation.map (EXP b c) (Rts (exp a b \<otimes> a))
                               bc.map (Unpack (exp a b) a)"
          using a b c bc_map Func_abxA.simulation_axioms E_AB.simulation_axioms
                bc.simulation_axioms
                simulation_interchange
                  [of "EXP b c" "EXP b c" bc.map
                      abxA.resid ABxA.resid Func_abxA.map
                      "EXP b c" bc.map "Rts b" E_AB.map]
          by simp
        finally show ?thesis by simp
      qed
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> Func_bcxB.map \<circ>
                            (bc_x_E_ABoFunc_abxA.map \<circ>
                               product_simulation.map (EXP b c) (Rts (exp a b \<otimes> a))
                                 bc.map (Unpack (exp a b) a)) \<circ>
                                 Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                                   Map \<a>[exp b c, exp a b, a] \<circ>
                                     Pack (exp b c \<otimes> exp a b) a)"
        using a b c E_AB.simulation_axioms Func_abxA.simulation_axioms
              bc.simulation_axioms bc_map
              simulation_interchange
                [of "EXP b c" "EXP b c" bc.map
                    abxA.resid ABxA.resid Func_abxA.map
                    "EXP b c" bc.map "Rts b" E_AB.map]
        by simp
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         ((E_BC.map \<circ> Func_bcxB.map \<circ>
                            product_simulation.map
                              (EXP b c) abxA.resid
                              bc.map (E_AB.map \<circ> Func_abxA.map)) \<circ>
                                 (product_simulation.map
                                   (EXP b c) (Rts (exp a b \<otimes> a))
                                   bc.map (Unpack (exp a b) a) \<circ>
                                  Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                                    Map \<a>[exp b c, exp a b, a] \<circ>
                                      Pack (exp b c \<otimes> exp a b) a))"
      proof -
        have "E_BC.map \<circ> Func_bcxB.map \<circ>
                (product_simulation.map
                   (EXP b c) abxA.resid bc.map (E_AB.map \<circ> Func_abxA.map) \<circ>
                     product_simulation.map
                       (EXP b c) (Rts (exp a b \<otimes> a))
                       bc.map (Unpack (exp a b) a)) \<circ>
                         Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                           Map \<a>[exp b c, exp a b, a] \<circ>
                             Pack (exp b c \<otimes> exp a b) a =
              (E_BC.map \<circ> Func_bcxB.map \<circ>
                 product_simulation.map
                   (EXP b c) abxA.resid bc.map (E_AB.map \<circ> Func_abxA.map)) \<circ>
                   (product_simulation.map
                     (EXP b c) (Rts (exp a b \<otimes> a)) bc.map (Unpack (exp a b) a) \<circ>
                          Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                            Map \<a>[exp b c, exp a b, a] \<circ>
                              Pack (exp b c \<otimes> exp a b) a)"
          using fun.map_comp by auto
        thus ?thesis by simp
      qed
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         ((E_BC.map \<circ> Func_bcxB.map \<circ> bc_x_E_ABoFunc_abxA.map) \<circ>
                             (Assoc_bc_ab_a.ASSOC.map \<circ> UnpackxA.map))"
      proof -
        have "product_simulation.map
                (EXP b c) (Rts (exp a b \<otimes> a)) bc.map (Unpack (exp a b) a) \<circ>
                Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                  Map \<a>[exp b c, exp a b, a] \<circ>
                    Pack (exp b c \<otimes> exp a b) a =
              product_simulation.map
                (EXP b c) (Rts (exp a b \<otimes> a)) bc.map (Unpack (exp a b) a) \<circ>
                Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                  (Pack (exp b c) (exp a b \<otimes> a) \<circ>
                     product_simulation.map
                       (EXP b c) abxA.resid bc.map (Pack (exp a b) a) \<circ>
                       Assoc_bc_ab_a.ASSOC.map \<circ>
                         (UnpackxA.map \<circ>
                            Unpack (exp b c \<otimes> exp a b) a)) \<circ>
                              Pack (exp b c \<otimes> exp a b) a"
          using Assoc_bc_ab_a.Map_assoc by simp
        also have "... =
              product_simulation.map
                (EXP b c) (Rts (exp a b \<otimes> a))
                bc.map (Unpack (exp a b) a) \<circ>
                (Unpack (exp b c) (exp a b \<otimes> a) \<circ> Pack (exp b c) (exp a b \<otimes> a)) \<circ>
                   product_simulation.map
                      (EXP b c) abxA.resid bc.map (Pack (exp a b) a) \<circ>
                       Assoc_bc_ab_a.ASSOC.map \<circ>
                         (UnpackxA.map \<circ>
                            (Unpack (exp b c \<otimes> exp a b) a \<circ>
                               Pack (exp b c \<otimes> exp a b) a))"
          using fun.map_comp by auto
        also have "... = I bc_x_abxA.resid \<circ>
                           Assoc_bc_ab_a.ASSOC.map \<circ>
                             (UnpackxA.map \<circ> I bcxab'_x_A.resid)"
        proof -
          have "product_simulation.map
                  (EXP b c) (Rts (exp a b \<otimes> a))
                  bc.map (Unpack (exp a b) a) \<circ>
                  (Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                     Pack (exp b c) (exp a b \<otimes> a)) \<circ>
                   product_simulation.map
                      (EXP b c) abxA.resid bc.map (Pack (exp a b) a) =
                product_simulation.map
                  (EXP b c) (Rts (exp a b \<otimes> a)) bc.map (Unpack (exp a b) a) \<circ>
                (I bcxeval.A1xA0.resid) \<circ>
                   product_simulation.map
                      (EXP b c) abxA.resid bc.map (Pack (exp a b) a)"
            using a b c Unpack_o_Pack [of "exp b c" "exp a b \<otimes> a"] by force
          also have "... = product_simulation.map
                             (EXP b c) (Rts (exp a b \<otimes> a))
                             bc.map (Unpack (exp a b) a) \<circ>
                               product_simulation.map (EXP b c) abxA.resid
                                 bc.map (Pack (exp a b) a)"
            using comp_simulation_identity
                    [of bcxeval.A1xA0.resid bc_x_abxA.resid
                        "product_simulation.map (EXP b c) (Rts (exp a b \<otimes> a))
                           bc.map (Unpack (exp a b) a)"]
                  Assoc_bc_ab_a.PU_Axbc.G.simulation_axioms
            by fastforce
          also have "... =
                product_simulation.map
                  (EXP b c) abxA.resid (bc.map \<circ> bc.map)
                  (Unpack (exp a b) a \<circ> Pack (exp a b) a)"
            using simulation_interchange
                  PU_abxa.F.simulation_axioms PU_abxa.G.simulation_axioms
                  bc.simulation_axioms
            by fastforce
          also have "... = product_simulation.map (EXP b c) abxA.resid
                             bc.map (I abxA.resid)"
            using a b bc_map Unpack_o_Pack ide_exp_ax by simp
          also have "... = I bc_x_abxA.resid"
            using product_identity_simulation abxA.rts_axioms bc.rts_axioms
            by fastforce
          finally have "product_simulation.map
                          (EXP b c) (Rts (exp a b \<otimes> a))
                          bc.map (Unpack (exp a b) a) \<circ>
                          (Unpack (exp b c) (exp a b \<otimes> a) \<circ>
                             Pack (exp b c) (exp a b \<otimes> a)) \<circ>
                             product_simulation.map
                               (EXP b c) abxA.resid bc.map (Pack (exp a b) a) =
                        I bc_x_abxA.resid"
            by blast
          moreover have "Unpack (exp b c \<otimes> exp a b) a \<circ>
                           Pack (exp b c \<otimes> exp a b) a =
                         I bcxab'_x_A.resid"
            using a b c Unpack_o_Pack [of "exp b c \<otimes> exp a b" a] by blast
          ultimately show ?thesis by simp
        qed
        also have "... = Assoc_bc_ab_a.ASSOC.map \<circ> UnpackxA.map"
          using comp_identity_simulation [of _ bc_x_abxA.resid Assoc_bc_ab_a.ASSOC.map]
                comp_simulation_identity [of bcxab'_x_A.resid _ UnpackxA.map]
                Assoc_bc_ab_a.ASSOC.simulation_axioms UnpackxA.simulation_axioms
          by simp
        finally show ?thesis by simp
      qed
      also have "... =
                 COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> BCxE_AB.map \<circ>
                            (Func_bc_x_Func_abxA.map \<circ> Assoc_bc_ab_a.ASSOC.map \<circ>
                               UnpackxA.map))"
      proof -
        have "E_BC.map \<circ> Func_bcxB.map \<circ> bc_x_E_ABoFunc_abxA.map =
              E_BC.map \<circ> Func_bcxB.map \<circ> 
                (product_simulation.map (EXP b c) ABxA.resid bc.map E_AB.map \<circ>
                   product_simulation.map (EXP b c) abxA.resid bc.map Func_abxA.map)"
          using bc_map Func_abxA.simulation_axioms E_AB.simulation_axioms
                bc.simulation_axioms
                simulation_interchange
                  [of "EXP b c" "EXP b c" bc.map abxA.resid ABxA.resid Func_abxA.map
                      "EXP b c" bc.map "Rts b" E_AB.map]
          by simp
        also have "... = E_BC.map \<circ>
                           (Func_bcxB.map \<circ>
                              product_simulation.map (EXP b c) ABxA.resid
                                bc.map E_AB.map) \<circ>
                             product_simulation.map
                                (EXP b c) abxA.resid bc.map Func_abxA.map"
          using fun.map_comp by auto
        also have "... = E_BC.map \<circ>
                           (product_simulation.map
                              BC.resid ABxA.resid BC.map E_AB.map \<circ>
                              product_simulation.map
                                (EXP b c) ABxA.resid (Func b c) ABxA.map) \<circ>
                                product_simulation.map
                                  (EXP b c) abxA.resid bc.map Func_abxA.map"
        proof -
          have "Func_bcxB.map \<circ>
                  product_simulation.map (EXP b c) ABxA.resid
                  bc.map E_AB.map =
                product_simulation.map (EXP b c) ABxA.resid (Func b c) E_AB.map"
            using simulation_interchange
                    [of "EXP b c" "EXP b c" bc.map ABxA.resid "Rts b" E_AB.map
                         BC.resid"Func b c" "Rts b" B.map]
                  E_AB.simulation_axioms Func_Unfunc_bc.G.simulation_axioms
                  B.simulation_axioms bc.simulation_axioms
                  comp_simulation_identity [of "EXP b c" BC.resid "Func b c"]
                  comp_identity_simulation [of ABxA.resid "Rts b" E_AB.map]
                  Func_Unfunc_bc.F.simulation_axioms
            by auto
          also have "... = product_simulation.map
                             BC.resid ABxA.resid BC.map E_AB.map \<circ>
                           product_simulation.map
                              (EXP b c) ABxA.resid (Func b c) ABxA.map"
            using ABxA.simulation_axioms BC.simulation_axioms
                  E_AB.simulation_axioms Func_Unfunc_bc.G.simulation_axioms
                  comp_simulation_identity [of ABxA.resid "Rts b" E_AB.map]
                  comp_identity_simulation [of "EXP b c" BC.resid "Func b c"]
                  simulation_interchange
                    [of "EXP b c" BC.resid "Func b c"
                        ABxA.resid ABxA.resid ABxA.map
                        BC.resid BC.map "Rts b" E_AB.map]
                  Func_Unfunc_bc.F.simulation_axioms
            by auto
          finally have "Func_bcxB.map \<circ>
                          product_simulation.map (EXP b c) ABxA.resid
                            bc.map E_AB.map =
                        BCxE_AB.map \<circ>
                          product_simulation.map (EXP b c) ABxA.resid
                            (Func b c) ABxA.map"
            by blast
          thus ?thesis by simp
        qed
        also have "... = E_BC.map \<circ>
                           (product_simulation.map BC.resid ABxA.resid
                              BC.map E_AB.map) \<circ>
                              (product_simulation.map
                                 (EXP b c) ABxA.resid (Func b c) ABxA.map \<circ>
                               product_simulation.map
                                 (EXP b c) abxA.resid bc.map Func_abxA.map)"
          using fun.map_comp by auto
        also have "... = E_BC.map \<circ> BCxE_AB.map \<circ> Func_bc_x_Func_abxA.map"
          using simulation_interchange
                  [of "EXP b c" "EXP b c" bc.map abxA.resid ABxA.resid Func_abxA.map
                      BC.resid "Func b c" ABxA.resid ABxA.map]
                bc.simulation_axioms Func_abxA.simulation_axioms ABxA.simulation_axioms
                Func_Unfunc_bc.G.simulation_axioms
                comp_simulation_identity [of _ _ "Func b c"]
                comp_identity_simulation [of _ ABxA.resid Func_abxA.map]
                  Func_Unfunc_bc.F.simulation_axioms
          by auto
        finally have "E_BC.map \<circ> Func_bcxB.map \<circ> bc_x_E_ABoFunc_abxA.map =
                      E_BC.map \<circ> BCxE_AB.map \<circ> Func_bc_x_Func_abxA.map"
          by blast
        thus ?thesis
          using fun.map_comp by metis
      qed
      also have "... = COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                         (E_BC.map \<circ> BCxE_AB.map \<circ> ASSOC.map \<circ>
                            (Func_bcxFunc_ab_x_A.map \<circ> UnpackxA.map))"
      proof -
        have 1: "Func_bc_x_Func_abxA.map \<circ> Assoc_bc_ab_a.ASSOC.map =
                 ASSOC.map \<circ> Func_bcxFunc_ab_x_A.map"
        proof -
          have "Func_bc_x_Func_abxA.map \<circ> Assoc_bc_ab_a.ASSOC.map =
                Func_bc_x_Func_abxA.map \<circ>
                  \<langle>\<langle>bcxab.P\<^sub>1 \<circ> bcxab_x_A.P\<^sub>1,
                    AxB.tuple (bcxab.P\<^sub>0 \<circ> bcxab_x_A.P\<^sub>1) bcxab_x_A.P\<^sub>0\<rangle>\<rangle>"
            unfolding Assoc_bc_ab_a.ASSOC.map_def by blast
          also have "... = \<langle>\<langle>Func b c \<circ> (bcxab.P\<^sub>1 \<circ> bcxab_x_A.P\<^sub>1),
                             Func_abxA.map \<circ>
                               (AxB.tuple (bcxab.P\<^sub>0 \<circ> bcxab_x_A.P\<^sub>1) bcxab_x_A.P\<^sub>0)\<rangle>\<rangle>"
            using comp_product_simulation_tuple
                    [of "EXP b c" BC.resid "Func b c" abxA.resid ABxA.resid
                        Func_abxA.map bcxab_x_A.resid "bcxab.P\<^sub>1 \<circ> bcxab_x_A.P\<^sub>1"
                        "AxB.tuple (bcxab.P\<^sub>0 \<circ> bcxab_x_A.P\<^sub>1) bcxab_x_A.P\<^sub>0"]
                  Func_Unfunc_bc.F.simulation_axioms Func_abxA.simulation_axioms
                  bcxab_x_A.P\<^sub>1.simulation_axioms bcxab_x_A.P\<^sub>0.simulation_axioms
                  bcxab.P\<^sub>1.simulation_axioms bcxab.P\<^sub>0.simulation_axioms
                  simulation_comp simulation_tuple
            by auto
          also have "... = \<langle>\<langle>Func b c \<circ> (bcxab.P\<^sub>1 \<circ> bcxab_x_A.P\<^sub>1),
                             \<langle>\<langle>Func a b \<circ> (bcxab.P\<^sub>0 \<circ> bcxab_x_A.P\<^sub>1),
                                bcxab_x_A.P\<^sub>0\<rangle>\<rangle> \<rangle>\<rangle>"
            using comp_product_simulation_tuple
                    [of "EXP a b" AB.resid "Func a b" "Rts a" "Rts a" A.map
                        bcxab_x_A.resid "bcxab.P\<^sub>0 \<circ> bcxab_x_A.P\<^sub>1" bcxab_x_A.P\<^sub>0]
                  comp_identity_simulation [of bcxab_x_A.resid "Rts a" bcxab_x_A.P\<^sub>0]
                  A.simulation_axioms Func_Unfunc_ab.F.simulation_axioms
                  bcxab.P\<^sub>0.simulation_axioms bcxab_x_A.P\<^sub>0.simulation_axioms
                  bcxab_x_A.P\<^sub>1.simulation_axioms
                  simulation_comp [of _ _ bcxab_x_A.P\<^sub>1 _ bcxab.P\<^sub>0]
            by simp
          also have "... = \<langle>\<langle>BCxAB.P\<^sub>1 \<circ> BCxAB_x_A.P\<^sub>1 \<circ> Func_bcxFunc_ab_x_A.map,
                             \<langle>\<langle>BCxAB.P\<^sub>0 \<circ> BCxAB_x_A.P\<^sub>1 \<circ> Func_bcxFunc_ab_x_A.map,
                               BCxAB_x_A.P\<^sub>0 \<circ> Func_bcxFunc_ab_x_A.map\<rangle>\<rangle> \<rangle>\<rangle>"
          proof -
            have "Func b c \<circ> (bcxab.P\<^sub>1 \<circ> bcxab_x_A.P\<^sub>1) =
                  BCxAB.P\<^sub>1 \<circ> BCxAB_x_A.P\<^sub>1 \<circ> Func_bcxFunc_ab_x_A.map"
              using Func_Unfunc_bc.F.extensional BCxAB_x_A.P\<^sub>1.extensional
                    bcxab_x_A.map_def bcxab_x_A.P\<^sub>1_def bcxab.P\<^sub>1_def
                    Func_bcxFunc_ab_x_A.map_def Func_bcxFunc_ab.map_def
                    BCxAB_x_A.P\<^sub>1_def BCxAB.P\<^sub>1_def
              by auto
            moreover have "Func a b \<circ> (bcxab.P\<^sub>0 \<circ> bcxab_x_A.P\<^sub>1) =
                           (BCxAB.P\<^sub>0 \<circ> BCxAB_x_A.P\<^sub>1) \<circ> Func_bcxFunc_ab_x_A.map"
              using BCxAB.P\<^sub>0_def BCxAB_x_A.P\<^sub>1_def bcxab.P\<^sub>0_def bcxab_x_A.P\<^sub>1_def
                    Func_bcxFunc_ab_x_A.map_def Func_bcxFunc_ab.map_def
                    Func_bcxFunc_ab_x_A.extensional Func_Unfunc_ab.F.extensional
              by auto
            moreover have "bcxab_x_A.P\<^sub>0 =
                           BCxAB_x_A.P\<^sub>0 \<circ> Func_bcxFunc_ab_x_A.map"
              using BCxAB.P\<^sub>0_def BCxAB_x_A.P\<^sub>0_def bcxab_x_A.P\<^sub>0_def
                    Func_bcxFunc_ab_x_A.map_def Func_bcxFunc_ab.map_def
                    Func_bcxFunc_ab_x_A.extensional
              by auto
            ultimately show ?thesis by simp
          qed
          also have "... = \<langle>\<langle>BCxAB.P\<^sub>1 \<circ> BCxAB_x_A.P\<^sub>1,
                             \<langle>\<langle>BCxAB.P\<^sub>0 \<circ> BCxAB_x_A.P\<^sub>1, BCxAB_x_A.P\<^sub>0\<rangle>\<rangle> \<rangle>\<rangle> \<circ>
                             Func_bcxFunc_ab_x_A.map"
            by (simp add: comp_pointwise_tuple)
          also have "... = ASSOC.map \<circ> Func_bcxFunc_ab_x_A.map"
            unfolding ASSOC.map_def by simp
          finally show ?thesis by blast
        qed
        have "COMP.E_BC_o_BCxE_AB.map \<circ>
                (Func_bc_x_Func_abxA.map \<circ> Assoc_bc_ab_a.ASSOC.map \<circ>
                   UnpackxA.map) =
              COMP.E_BC_o_BCxE_AB.map \<circ>
                (ASSOC.map \<circ> Func_bcxFunc_ab_x_A.map \<circ> UnpackxA.map)"
          using 1 by simp
        also have "... = COMP.E_BC_o_BCxE_AB.map \<circ> ASSOC.map \<circ>
                           (Func_bcxFunc_ab_x_A.map \<circ> UnpackxA.map)"
          by auto
        finally show ?thesis by simp
      qed
      also have "... = COMP.Currying.E.coext BCxAB.resid
                         (E_BC.map \<circ> BCxE_AB.map \<circ> ASSOC.map) \<circ>
                         (Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b))"
      proof -
        have "COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                (COMP.E_BC_o_BCxE_AB.map \<circ> ASSOC.map \<circ>
                  (Func_bcxFunc_ab_x_A.map \<circ> UnpackxA.map)) =
              COMP.Currying.E.coext (Rts (exp b c \<otimes> exp a b))
                (COMP.E_BC_o_BCxE_AB.map \<circ> ASSOC.map \<circ>
                   (product_simulation.map (Rts (exp b c \<otimes> exp a b)) (Rts a)
                 (Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b)) A.map))"
        proof -
          have "A.map \<circ> A.map = A.map"
            using comp_identity_simulation [of "Rts a" "Rts a" A.map]
                  A.simulation_axioms
            by simp
          hence "Func_bcxFunc_ab_x_A.map \<circ> UnpackxA.map =
                 product_simulation.map (Rts (exp b c \<otimes> exp a b)) (Rts a)
                   (Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b)) A.map"
            using simulation_interchange
                    [of "Rts (exp b c \<otimes> exp a b)" bcxab.resid
                        "Unpack (exp b c) (exp a b)"
                        "Rts a" "Rts a" A.map BCxAB.resid Func_bcxFunc_ab.map
                        "Rts a" A.map]
                  Func_bcxFunc_ab.simulation_axioms PU_bcxab.G.simulation_axioms
                  A.simulation_axioms
            by simp
          thus ?thesis by simp
        qed
        also have "... = COMP.Currying.E.coext BCxAB.resid
                           (E_BC.map \<circ> BCxE_AB.map \<circ> ASSOC.map) \<circ>
                           (Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b))"
        proof -
          have "simulation (Rts (exp b c \<otimes> exp a b)) BCxAB.resid
                           (Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b))"
            using simulation_comp Func_bcxFunc_ab.simulation_axioms
                  PU_bcxab.G.simulation_axioms
            by auto
          moreover have "simulation BCxAB_x_A.resid (Rts c)
                           (COMP.E_BC_o_BCxE_AB.map \<circ> ASSOC.map)"
            using simulation_comp COMP.E_BC_o_BCxE_AB.simulation_axioms
                  ASSOC.simulation_axioms
            by auto
          ultimately show ?thesis
            using COMP.Currying.E.comp_coext_simulation
                    [of "Rts (exp b c \<otimes> exp a b)" BCxAB.resid
                        "Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b)"
                        "E_BC.map \<circ> BCxE_AB.map \<circ> ASSOC.map"]
                  BCxAB.weakly_extensional_rts_axioms
                  bcxab'.weakly_extensional_rts_axioms
            by fastforce
        qed
        finally show ?thesis by blast
      qed
      also have "... = COMP.map \<circ>
                         (Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b))"
        unfolding COMP.map_def by simp
      finally show ?thesis by simp
    qed

    text \<open>
      We obtain as a corollary an explicit formula for \<open>Map (Comp a b c)\<close> in terms of
      the external compositor \<open>COMP.map\<close> and packing and unpacking isomorphisms.
    \<close>

    corollary Map_Comp:
    shows "Map (ECMC.Comp a b c) =
           Unfunc a c \<circ> COMP.map \<circ>
             (Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b))"
    proof -
      have "Map (ECMC.Comp a b c) =
            I (EXP a c) \<circ> Map (ECMC.Comp a b c)"
        using a b c ECMC.Comp_in_hom arrD(3) [of "ECMC.Comp a b c"]
              comp_identity_simulation
                [of "Rts (exp b c \<otimes> exp a b)" "EXP a c" "Map (ECMC.Comp a b c)"]
        by simp
      also have "... = Unfunc a c \<circ> Func a c \<circ> Map (ECMC.Comp a b c)"
        using a c Unfunc_o_Func by simp
      also have "... = Unfunc a c \<circ> (Func a c \<circ> Map (ECMC.Comp a b c))"
        by auto
      also have "... = Unfunc a c \<circ>
                         COMP.map \<circ>
                           (Func_bcxFunc_ab.map \<circ> Unpack (exp b c) (exp a b))"
        using Func_o_Map_Comp by auto
      finally show ?thesis by blast
    qed

  end

  context rtscat
  begin

    abbreviation EXP
    where "EXP \<equiv> \<lambda>a b. Rts (exp a b)"

    proposition Map_Comp:
    assumes "ide a" and "ide b" and "ide c"
    shows "Map (ECMC.Comp a b c) =
           Unfunc a c \<circ> COMP.map (Rts a) (Rts b) (Rts c) \<circ>
             (product_simulation.map (EXP b c) (EXP a b)
                (Func b c) (Func a b) \<circ>
                Unpack (exp b c) (exp a b))"
    proof -
      interpret Comp: Composition
        using assms by unfold_locales
      show ?thesis
        using Comp.Map_Comp by blast
    qed

  end

end

